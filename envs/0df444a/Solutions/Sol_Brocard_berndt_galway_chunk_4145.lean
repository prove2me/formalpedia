-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4145
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:41:36.134784+00:00
-- url     : https://prove2.me/submissions/487d4e93-5767-42a5-9bec-e70e2e0a1689

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 745323741 ≤ n < 745503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 745324991 1250 745323741 745323823
    0xb030c0a030f06050303130f0e06030a030e040603060501172a012609060f01060e012f030d060303020105060904030e100306090c05070302240c070203030408071502 72
    0x1a01c80100b0401d118a42d0800405010010180c0f500c2d4034104420f000c25210358410341d0315940460360002104050160b020b07006100240190a01d4a078949003655920002001a03130004ea40751400400701d5907920920b4080d1442e5103007c40d007041c00d449240e281442d417605500110300d00014410042c0480030a4481040081c2040c2c903ca4100801c0090301042c0c00312140030804e5180c00704000383c0004510b051041100d0080403140341d8032140102ca15030800a5074902182180c690798140d041174611070310740151521481e002c120100e09841d4215081a80242e1000e80c44020600c101902802404d90066050304c00c00450b14103500d004160780c01c210300840c0a10082540c4120051003904100090302c0540001e0100360482000140303240d002c1c101c10350050095030030f15034420203000c043c1c1440791003011080b403031038580380700700070565108040499040c4001c00000800f02d800713000300b44c02416011100c3e08150301081c0b0103814034544c0c00034142d100c402c80038402c84021190380109802 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 745326241 1250 745324991 745324997
    0x105010e0409020609120a0c0807060203041a0705072c0f0a0b060d0203162d1b0b0c04060315031e15050f07120e030919030b010315060b030c0a 63
    0x7400443c008112584282c400503030300201071720a14040340f02c0010300f8000c1e161041c18508003095840748070795180e00c940d0080b0700060f01304010412000e420780c154420200719a085041c5802103e03603a841c5070040940c00140c120030080845034920905075214126510020042d0f01c01c0d250001e40702002040081c180e00703680d5682c20b040d10443d25801c06403610200e141000315520300f490044000d80c40c10403400c4400280e241d200d4600c0300d1581c0c982c2e2903500d603803411000050542c1c0c6c5400381c6000d06034000f580c0c0e05401001418020078560101c1e42c3c05203070182e035071070f039074a082c00001001d68a109100130141e040f040020800980c2c1411583c0b440711101c83c0e00c85900a451418258034030240011940701800c142c03c4c00508081030002c140a40116107850440c401031155280581d08455101025034000b40703c02105400c02a11119900340703070080407410740d500c0b40d8410700180c600781c2007610440c0440f04680381d400740c3d5228a0f0060800c00c0402819403602c000014003920800e0b12070020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 745327491 1250 745326241 745326251
    0x90f0603080f0705030412080d0516020c0d050c180609010b0403020a2903012309060109061b08120a060f15050702041103010603141501141b010603060c03140105010e04 74
    0xd2040c1070041c1c0307000e40740c90961065480502d0402843d1070300700c182750821707981c5400f0100f110540217601e4804d1504540c0c015200e00880c81d020400800200303201999540030301c0c41c201c01d4541c2c400d03020707240200000e13400300c1c4942000c80c00d01405460580000300404c204200030700c007696400c10080111044d44501041e0031014030503c50a40004c00904645050040008a401e2200c031040140d0103d02920030642806a0420410b45c008146c03402d5010030202c14040c4680e5118082d00310050249024501c1c81c10420341d10000243d20070801c64600100300400e02c446014680030700b03c0105180d80441034042d060020323901510696807045c0c02071100001d20b85085455940158101030303001d84100d83c0769a03650a02030041c203100c69110001c2c030201c01c00101c5070070030585c0d0b025003000181c1d04c000491840c040018000c0d446824292014069400c1c80209031b83d09002d0343c0f000c0c510441d0b02045404c109000941035a952a50a04d810703844100180b0981e603016610604003c821117011030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 745328741 1250 745327491 745327493
    0x50a1502090d0c06080a150b0a180303022407020c01032307201b1018030c17060610030b1305040602031510140711061201090f0603080f07 61
    0x1009214500340c080d000001c0c18034400c20b000c0d41d0100c1c4001c131680c0f0340f02c803503896880003681000c654800c0c1f0462900c42080406104410004000c0e006803089030800c9162400100b00c1050901026482100141d101032401002d44a000a88459129030812160042e041c0301c580692245080c60400e410144d40341c100040c60002c454601040d03072184050b1114601705040c004101000c110410380c1e0940310f68010040110001503440f4402030000021001000c4440810090a9008450380300300300514180b419084140318104000b14400c1c0303e03050321945010b01c0305504541032041d100d00e513000070301005000d848100d0a12113842c5a49800030710250784500007601c04401005806040f8601000c020400c640340d4001c60041c508030144100c0a69004108140d060145841c00300190000108483c000c02980252860a202d0030002c22400d070b5050100750345821480403c60326140803401042038040ca44685228410520024452142940c6684016109144180904d0078000880300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 745329991 1250 745328741 745328783
    0x309010c021f2a08040510050403020915030c181b0421060b03010e0a0b1302120d08090c0319060b03060c0a0314040f020d060b04021b19050a 62
    0x1128604101c40e6450a0321140d64018a40100c080b203400495044a2092000c143e0003004903c059610542061070141044140b0106d01150182902848400c0c400440103a90300100030344580e41c202c080031420104e04007054030b0b1a40440e2080e004603090341c200c40c40640d80000003588086102145441581058071040651107a80d0042e10030141c0c94200c1607521202c1c3c104e081d18a2b00816081c80301d101d403002010b00301e68180310410720039800b141103c0009100500c0255110f00140310000744402e00f030300442c480c940705501c40c40c0141c020308610120280c10040e01134015002c4401061aa4603400100e50b0f5005041e018010703505505012008019a13a0032070f01040e0300113010349038903082c4140030304561780082d042100400d082824807108000a07940b110311564208098003492011390302404410105900305440b00e503124442140300380c03a903000510000d690f041660064500c840d54903070070302600708048441c01c000031001c0400f24000180b0403810641103001401c1d188421034501d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 745331241 1250 745329991 745330009
    0x1050f1c11041506020601081b0d0c0305070b040314010504050d03020c030d0e06180d050703031d0114060307060804050a020108061207062f0a080a02100608060106200309010c02 78
    0x507690043c200354407944258043c000c08000c440641d005c83d003003640ca60707056684403800f004e080e5010f020a80b1225140d460311652102c901070060041900b140d880391600350070020142c0101c9245c0074000740400820040070502580c511040008001c181070a517500c9442703204158802c000c06402003a0b04001c0f040a004803014800f2401080007074240381120079444110868601c00010b1559048464892012030707682c10300c0100c0d40d82c162400c0d040d43c1e0143d0090070740944000400001d90344c00201d070402481080d03080200046008810319007034003003501e009816007003801004003c03800d11002840000b80040c6255090910701060b54801c0041040380c0ea850030144024811903000203a15501311262407002880030990300c0401d0302c44032001080702040b203008a11603201c0c1e00c1d07181c04241d1410140406003c6441a01c0c0170307452042c0341c00280d40722504025400c0d00103000401c01d41d50050b85040030415018582001d0341d091000484d160700407510b200b814022104107140444d601c50b049 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 745332491 1250 745331241 745331273
    0x1051b120f180f07080105070915080a140702072c01091a09010603090b2508070302160809030f07051305040507170a031409130e1903080f01050f1c 65
    0x3c83d007501c2d4000319003035a5a020341c8030796180303135117030001151407103200304a26821381e078041550710021141c40d103080700c2e0158024944517003a991082120f1240c134161170494001c400580c001d1a03040c5c100b2440364180b01c2510741c85000840845c8800e21612901c85545044a5564100152003c40a00503804085078012020703445011500003080ca0b42c2c06501c021b444038010f900c4c0c1c404503a60188102d448000c02c00000c0d107007109198160714914800c1e010590711145910740942060761010100d01c0315a04028100c0e02664003240c4507c03142010884030020030030100003080c502d86000f0207d242071800d401c1660b0032503250000182444400c107d1100242201112180c0c4800c20112094540e40e8141080700020424041700b25182d113a0000e2702d09130346000305031000b590404400540207050503401c2c501e03e07015005000540000c00350000c09070f14025150b211b1945412007001d80e0030801604902d2140d0300c0c860440c80c5c603890f80202c40c01d60384510a440340d01410070b07080c549103c64554007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 745333741 1250 745332491 745332493
    0xf020d090804061b08040b030405010b0a06050705010f020f0313080c0d05071101020105090c01030c0e150a0801080303040f0201050c0c042a110d03090201090308030901051b120f18 79
    0x40e0410898090010300880e159a035490343c2c1d025142400f4840c11064100203000d1305801c0c403050040300d10110045402600c610f0000a10009171b03408600160500c3d800740001c5100400d240702030283c01c1c0280c0c00f1070f8103080802c61500d103110707070715401e207000180444c4580494014443c04106240c011620040220b1089444590350749400078025403106a0456018000352030214455005014190141c559940940103010702500118018401c2050243c1004030304002040355403a4408881503501108015035500c0240c3c881c0076010050683c0001a0307540100100404941c9800070004181d0b42460500c1da502a140141031800c5e01010125034000d02e40103417110801110401c2c04002416801d241482318200c0c1d1068451482c9030402c0b000d190000c804401c04580710b5813110311094814100075002c151203031603030300854108072211843c0d690744000707205041c11064000034618201c000c0e194070b004005e5072058071500003d0079190315240a08046021707003c03c40074802c583c4500c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 745334991 1250 745333741 745333751
    0x60d1410180204060b03040b0c0f091806040b09070e0607080c3a09090b040908071b150f03050a061a1903060e0708060d0b011d010605031501030f020d 66
    0x4054401d20301c10401c0384a1072034440d000482c0d810315019280304a0704002c1c00e0301143c0e01d240c55200c3c6680f000300041d00b200d50801c960000350713803000352150f08040460200c01c550b14001c010302080311005240e0034410300c0088200202542d00a02d50441d504041e14495102d5040d40782c0309146014483c011300c99030081e0000b50042d41844000408094080c10346172288180403652800c00315841e540d408005007543d5400d00c05001c0035001200c00c0301c0e011f040000c1d03801e00b54a40490a40004030111100a4020300e0303030030341300840754000001d003800c540300c0610b400003240090000310304032132034405140e02c650000380d40b03000e43c0e48003c0040100b116001f00f8900c200081a007254071105187c40c0c6614140f00001d902e500c20301c1104281c401d40004401709803500f030f2041c0d81d1584028003c942c0107040304071078030010341403045550007040d0801c121015109070002426410005810903010440c1c18020408804040141050410381c2801c0c0058100200912200030703110b507020b880b064500380 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 745336241 1250 745334991 745335011
    0x112080d0b0a034107030212030c060f01031202060c070605060109050303040f09060f053a0c182c12030106050301150309170d0f0f0506041103060d1410 67
    0x4060241024001141c086444510b154009501c0103c4c2a0038800d59a204110030310060803c0600c2d15050701c80c600840307040c00e40036081c062500900300e0b4944010860300d40104200080e2079041162866203001030000c070724141d1802e01c0701c0e0040380300281c01c0c641c442020908130b9004031002806080c001e0b050301d582c0d60f154519098011140d00c61061400d00e08040040c0401220841c8410390344002e200c50b0107145401d0070507a00443c0c400f0360f00c0c1e40c4200381198200042d00c4006007200c25101c0d160b0096003501d820502c9001c0d15913409011000b40c00e06190103203015510740880320801c4031041e16662491014a030ba03181c40d40702201044031110000011030011340010241d4100e0b440045074420008900c2c03c110140c510300b06004001c820f030754042c80d100a041d140500042004410000b61041d409918801904e0400a2410707001c0d903209c060010504041c06202402e5500500c00c03491400c018000c60892000701c0009030500202c0142203200802c1401602d6a00581c4102481300c45c41d5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 745337491 1250 745336241 745336283
    0x5070f112d09040206070201141c0b0132031b07080903010c02070803030a0209061c090606090608030f0c030909070f1206030506130201051c02120112080d0b0a03 71
    0x7403103400140102841481c40681d1401d5141144103070343c00351400c1e0a01109a00548140356601c94030300c07074980309100002c4030328085413200c0b990804e0302c1c402080c00441c46001410750000180d0042c02c03500910455466141c000c1580321007158015117459881c1d54090200c600060040f000714000d040c00980f0310b091090410141040c3c5408900030040344802c1c00099944409912828905410600004048001e03d0b400380c0300c42e52016013074902d4500311010482c05001c4c40300d072401c00c082d0b8416405003403000621860000c0e04017004d080004a0404141b269203004280740c0b0021000000f030440d058800c1841a40e1b08004007800d025287d040903500a45075140c1c00401c10000b07010200c0e0740c00c1c055071a002d002c0450381c1220250a4607260308100890380004944d040e418840c04101c103480c034440c0261000d40703003c101e41005840d61040d0300c005030318180c180d005e03c01303184001d185100800c800300225030811241c024001803200c1c3d1580494140c00d5640d001034507290700c40e840c950019003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 745338741 1250 745337491 745337539
    0xe1212040503070b070b070c05120309010906062304150f0806011802120601200f03041a0a0f1d100509010e04090b010501110a1403040305070806010605070f11 70
    0x8040301034900d15900c840c400007131402913040c0606059404404030b05514021001e15034601d00481c01d5613040b10060010b071103298000c3d00c00e020943e542e00c5261090081e244540d030b01802000002e081c84402c0680035242c0c13405400e6180b881150741c0c541030280345164100907001801c5060300580e50941d54095180c48042c24482d00001500c0313490080302d810032a10849991000a031050a0b454071000e004485445000c06401c8035120108924440c4813010065180f020740b01d00c00444c1d807541805c172480d610311203244d9034001c1c8402c244042d0907020340100c0f0b4000141101e1512800e030403548400b00c1c00c1448003584468010b4401c2941d078101950000090008030020f880b0b4403804c0d10b14400788004c881c0c01c0d24010308140203500c01401035600c030f003070803400340000c0c24211040e13038101e17403144040c400d000424540150700028080003005030900a40e00100280e0015140079031500c170303010700b2611030360700002d0100081405607001c200f6644a01c0d038a0f5000581400d84808100c03107000f241c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 745339991 1250 745338741 745338749
    0x90a020a08070228113f1b0a0b0a030605010f083d170706020d170a0e0f010c14130504050601020102190e13020c0a030e121204 56
    0x1c54070400900d04500010381040301c0301400c003600d03d01c013007400c000010780c0c40307407843c01c68141080c02d1100141e0755440740041c16140510703c081031000c020b4114a140031360604c171540c06c045a00040840305603804a501d005400382c60780c40c000400c090400040f01461a50400d0300c4103200440c20013104c55141e80004251102030300c50303900805c1500ca09546641d0708a071006080800d4000c140107030420790280e4250456801c091103045480071200072503101c00d070340104655241108014140240400c0100e00520311400600110042084000d20594028030300249a000305004100c0c024900c1d80024485c180c43c8042e0760310f003034001c42c115001e8007802c1c4e22280000e4840c0f10646406113132404940e4030130003640e00c25400a103404107000141c5001001941595401e00001d030705204070703150a81400041ea603a034241030303014408111808189500d5090300c81e1041c8285c5a0102000620724000750f05818116004500d0b0000103030003807050091900c1c103018034400e0710150030000010388261 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 745341241 1250 745339991 745339997
    0x3180114040b071b23010b0a120210030b0901060c1b1d160203071b0f1205120406080118110d0b03010b0f01140f0d020a0e130b09160e090a020a 63
    0x340210344c14030084c0d01004d003024154915030300041220b00c40d04820110b4009140002080150000000070b0030305070380754042c22441d0304401e40b01d01146452400000d9003189410104007001150000c01c8050070140104c40600407808030100510a0034007004030342e800c5e40c0c1248400d954503580904d00e03482001d17804055049402000c40c0700b05002e01841d00b0320341120b500450810509407545110443c0c0d02c0001480424001d4002c94507288040c00303040580034103031a800140c501450701703e1522007452405040010b085c0403c0c040d40707030b10050840c11103980b403010341c4070001100d54450003080b0f070b200c0031654a0701c002030074140040140c00a1510240440080000203680340130311100400c92000d440c006400c140d0103180e450300c20009444d030464402e00d0f15040c0300020784084100c1e40800038050100302c003100c860402d07191062442101341c44164003402441242c501007058070f50040d018201606a0041001e0801d110300c00c90340c46840c0007411201d040c14034004a2000794407880100c800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 745342491 1250 745341241 745341257
    0x120a1b08040e51040608030714060c1204021315033e01050c100c05030406050a1b081f0b03010302010f09120219030b040c0f050d0803180114040b07 65
    0xb088504400c40042c0440b0070002c01c0d807030120341d0800c540c003528043c0e01070344681d0703501e808500d500701080501031561060720038559144400f80c40300c0c0b0b4140020041003081000300405c2c0c1c00140d0006501d500302c0ea05483c4964401c01c1414407102030201d0000c000100d0f415030038004140000140ca48207c082030b90b6111002d01c65905001e45d000030807040e00c0d895030003242d61010407540302d000203000c050300b43c0c41540c00c404080d224507003d48446040701400140b02000b031006000c26403048a030018080c140c00c0020801c000300d1000b03c000619848024030010b02c000482000009203410000101d03441c81d812001e0301c0f1300c1c18a09680084c04140d00141100060328081409000200d041c0c40400e06c00100024041d13003003102d0300d4484d41c8009906603003408004001200542841d0045105004544455040034800c001c0780c12181d01040c425814034038004c0116860104481c0c0001e81802000b200c0b4180f041c89a02406001c0210380402005d08100014000c03c40803882c0601e03000d59030402 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 745343741 1250 745342491 745342561
    0x4030b130303060b0c0318010e03031201411314010e0703270c0b0a030b0f0603190b03010621060e120d1508030a020c03120a1b08040e 59
    0x2003401040c4000d40181d02c20082000a140c1d400011004418140340442000c00909c0100f400c0d6040a542a01d580840e5030040c4000e001c00080340c40010301c003800c1542000c0c0c1c050043e070049003070f06941c440c14180740070340810f00ea15000503000c0c60b202c8000d42840040092106c115040303070240300b4032916050308408100024072a0003603446a1a44800132805102681c51031084098000c804541f003030102d040024400500c0005403078001001c0d200090103010725400c0c0301100c110000b08501c01c040c01c00800c442001190100c03141c550391000d00150440460002c00d004000c0c42e0000c9911590103e10340403a84040c00d00ca840b15407003210140144608130030240ea540c0d80d01211b1240d07000051002e89404a0598040c2501c590382880024441340d41d1281641581c0c40000000c0058011803440303070780e5080c204003500215102d61052440c08001e264018900001420f50f01e03410540065a0404d006103001607501600101d00c0113001c9090030100162600c0e10f038041403070240f5840440310 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 745344991 1250 745343741 745343759
    0x20a120b011d19422105010b090406150e07020604080708130303020c0307080f07030219090f0519050402011215180606030b1e130204030b13030306 65
    0xb00d0025980303940792403d445102c400e01c1d5502c40c2070396404a56a84803000081200820150a604001d64404035907008800451880340036411409400389220190204008801c00300e10809054441d0304240d0f0011503481d0040c094070203841800e0f80300d01070f00c09101c2031100562201c0c106103101c0a400881940c0e5541003050900c0440302e050250300322000080c0822003000c018000244075250030361816285210b49406060b09400c140e005034003100b9100e40c1400d0422003000038000c080010729040c0c11080d85d059a4000c14040207001d6041d0500c2d0000042c3d000b032032440501400381c1e040c080f08015000b8a8000c0c403040750140b0007071192540e0240907910a110b201c1c040d5806031340702d550300d1004000c01005008500d0354008842c07400b10000a03c1c0ca83c00342800245240705001166191800b500181a40c40e00103003640b04084030071a0140aa11485024038071036015a03c119110328410604030003802980e001400c01512441000b07090345000c144000a0b51090b102086165141e030420 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 745346241 1250 745344991 745345019
    0x106082109010305070e06130503061f1208120f071b0201120509030910050304021e0a0909170f071401020418050402031920150703110a020a120b01 65
    0x801000200141c6426511070b03004079a2140807418410800040c0801003202540301003180558810001d5080c0110316081c09407540083d4092a15010040000d00e400306038040c602c03030102800160341c0b040040018400c20754850f2000c221003000d083c03500f0309904441071001c0310000e000481000c1420010445140c540711001e8041c0c0d51090000007080b00103009080150030001b0510043c4003904840e0740340c91400c2445425542c3d080e41700d050910500141f0301c40c0a0034010600840d01f0452041c2c0c455204d99001c03160390b944d021502d0038442c1070044858450f80b0041e0001c6000003400c02c0401c41d030100074070b40300348100c140a052814882c0107900f00d01480c0103085201415034240c1c80619060303080030f0b401034001419106136601d1820300500c40400004204c0342c4905800311960000c5050900c410141c00903998010580c0740333245043d001d80300701c07407004081c89445c9200c00d5031103c0401c15032555982c040d0008a4080c6c8540250301149801d9200312541c2c04a8000415034610346051 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 745347491 1250 745346241 745346293
    0x30207030f0305040501062c0a0207030212071103070b041503052701060506041d0f01050904030c1109040b090c030703050d03240f090b0f01020d082205010608 70
    0x80e00c10074540c1e22011009040c0c050815207403036498007008030b0880c0d01154016a401d500010801c0842d580c0341800d0262900100300b11035292041c000c00010075004140c0c0070001c111900c0c000d82e50704036032034034031004040445030030b40600c9442c4011680724031440081090350940c010727107080d10780c00480272011b03620304994031480040050301d007111000b408814010030611103400480d940d40c540003c03508581040d4452620080000c09074440001010700498102e12020610b500c503604000104018810141c0010308000040e07504809002d002e080210640d40010720710b0324941494142142030308401d559442d45400b030400340701c44a01d40081c6040c1101d0380040505038010b0041c4081e8005c01500c40d0b10f4503040c083c8111881d408021380e400001905058405d0b80075a800d0481000840b0201240d950003000041c02150070740c0e80001d4074419010301482c1404403942d611031200940d909441044607420841c081030400c01406400c20740c240c500075002c5994403504040501c10310004107034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 745348741 1250 745347491 745347497
    0x1030e06041211120313120f0c02090c0c01090609050706031a040f0b0316150306051e1c06050f0f0606070803061c03020a121d0409060b031c0f03020703 67
    0x492030000c0d070b0103008043d0480980b44181d50b28108000200500ca500440380425007100c008110b0042010191840a400c5450f10704008003843d0b51501400c511f4680c0b00103882800740c400040d12000b804411265042400030080c0035800c8a86003110190040c082c080380c4902840d0300106569100781b003510240d1036021582c0705041440800e20005107211600d030401680c580f080c1c000c050702c0800c07004107118090708685440724500052411441c501c5903020081600340355080109565040d8105203001c141c0c200703980c4401c02d510008186580c004c18800c1e000d80418100d40512034079074000380c81101c1409d40801d00b0303540c010a010780602d003113442d603074403c006000400119111102031075002d5400340070204550752034800d100d0001c100c50f0b8214016423240507410100030b80d950307550b2010f0420303042c20350192000b28941000e251043c28003030b008070741d910040000e011954128614010703010302910309101424060800c04010442c02c500030074445148189254032070f1080b2052150107603 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 745349991 1250 745348741 745348763
    0x10050d08090a051f0c0204091208040c06050f0306010e01020703050d03060f0504060602031b16090c020f0c030d03090302010b060f04061103030c03010302040e0f07230402070b04020402070f061a01030e0604 90
    0x7003066417030820500307040e6007040c0d071544d00100017103101c4030b80e01c1c00040e80c0d1500002441c0a1500d203d501002c0e400400c00c2200621212010040407020b4039081402402d120700110b8074040102e00e003005507800502035105007080500542e4040d48554140c884c101408650643c83c1d4040c00144d910503c43c1500680c010001c0b58003800c02040d282100305060004d69035604200c21488994030741e190480c0c40d1503696442c0d0000f001c0d40411040d4120503402c4007034020441918006a02c071556a13160300c09258541d400c04040620030341c848111200010705483e01c585c0a00407070901c0303070094050038012170988140d254107101d001003603c1c41740352220f409030301d140c2c21a1300348805017801c00341d102214841c1c070148030040b507414805900034061783c4011448541a42000309a2641003400d0310740181d2040066601082845107607591003501520096982e00541c98590800c0c24444406002c8524001281028141100403542090030076a000c5c4800d000d480070294541c0ea00307036401030501c4048 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 745351241 1250 745349991 745350049
    0xc050919050612220b060f040c09060503100e0c0408010b06041206020a120905010b0a0b09062a0f0a05010b1c020d030e04091b080105041a10050d08090a05 68
    0x400480399000d035182c5040ca00340610601d132000c02002c240c404840a4001d00d040240ba0f00b0703c5c0d104400c3c0d8401c02c45052094641980000e00804500d016a070100500000060756041c03004504500825001d47d000340d280c500b03102050401d4215000c0c41c00c04d54206000c0c10214034002e07059406454400c2c610b0003c850240da41c5a00035804070890b80140885c20610134062a01c1d44030300d00b00f09002c6c80000c144c50220f041040544900c5410019807140244000c1c81d01d81c80e801d058446600640d60040d005803900b240c0303001c482e80c5100514006100d01044000b03180008189240b113207200388001d110a00e00c0008000b00c1d505003129102c1402d19100101c1e0251402e11840c010150090812984440035100032a00b078411200059800702c0c4006d42ca502d44030002c0c2010b00c01050407030020011403c0036600c28402c0c80540d607c40d070501c802880030610001111910f4002008001c1002195038202e10b407040d060340202d51030303030b205881c0c03403900040c541030210303288680e8103444d141d0302408455 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 745352491 1250 745351241 745351267
    0x70f05032206060303080f060303030c092b03110c010219080d0f050907061d031507050405030106061e030b06250204020703091503090b010308070f05010c0509190506 73
    0x150710a40d2450040c0c07040c80c80007040280c0700c0c14025602170b5840c1c040910b45900c0c155510103000c2c04540c02548100100100f08a00c402610100c15080350b020f040740d000b948080e640d0381043c13100c81504580420b401000c0580044c0306500c422181c2d4180c90600b48080c0040ea160208464070714005460303080288001415a03000701401c03c00810000760100780074803441d0880b4003c0303506d603105902004051140d5030b040b40b1014401001c40120305401d080b0800401e48171444000b1201d441d440e5880402d2125006070183c0c0d02410025008000091b0358000092032228003e0916035419860106a580d0360300c6402040c222610207405a49000340c410f142410b00c0c1301c5000c13501e030861240106480142c0d9580024506036000380d84403031940342000c00c001c0000103c1000c07842818585045940041c14042d54941100c0d0406820b6844610500304040188481080105154039203052152020740150180603800401d0f246041c040e1100680341004000714011540c0c00803040c050001085a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 745353741 1250 745352491 745352521
    0x30c050603041a100512010204210807080a020c0f010e010815010c0204060b070b010f03050a0204050c0c030307090311060408060c0d02070b0f0103110a14040507051e070605070f0503 80
    0x201c83c0b9444031510554896100d80c0c00303420ba514502c0301221030410032891070541c011100950000008500d8030345031005034000d40a10050b8810721011040b104014081e208017610007642e000b02d04241e4400d0b603110b00135250a03000f40c0c200d2064140d141030995651061110f00c817081d4040c0c6070030307003d5251000c088030801e600d010703130034100480b81d08004010b803078a00885005280300d2845944507203072881c0c400c00b0850140c00203040c40010040800101e4800030f17064541c540c040d20001819142c040d400759443c42028030078801444001b003440b462a40c86880102180c0c0104030720061003080504000b03140c4280d1283c1d00c3caa41c828004141c60b41d560000502d50188009401490071445035990300410008803003d80c400b52441c0010010302071000340c19090b1003001c551a00403242406464110818034040c0030b40219a1070b40001e0b00301f80984120b41c400c0d04d280340d103104103d407044a2240f507580420340845080f03080002250101d40034410b03040280e9000e0f00c500f400c581d44c2400b0541991 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 745354991 1250 745353741 745353743
    0x60c0f03110f0a1a06040b03070b030705130e07140c032208010908180f01050a050a0908010204121a062b0c0f0602010c110309120a120e10020106030c05060304 70
    0x20040c0701c030141285100304035000143d8420007081c140c1c0e01d03c038001205484c90090032a8025828082d00200c43d5402180c0750060b10b800b1200d40303481c2c0d11640c41c00c41e902e02403402941c031a41040b103c086000e102d65490940300c0c07881a0f50f60401c800f070f800072040b01409500072842c840e034810b100342120000010180d543c2c80f21003c0d07801c1d02050b52200341500b07560b080b80c015203030801d0000d50348401c102e002091040e545400d648800403c080c001c0000c20794800d04240104110020911440c510300c2003c4510040482500135502c498403030110003c421134001c4111070f100c103a8555a10040260281c4d1882854010300f030540c1c4002c3c1d004544011a84000c070448507080c41018400040e01108201c8083c028a0b044c0c0140759092103070181c01c50f0b40b002c40103001d1040f40312500d000e0395030000c01c0314201c0e001501c8038900728442d2803000c0e140110b400c40080c0181040e250902d01a130303001c0d0701d030b1414030f03030450704144002a40c40007682210145e0101920350380e07a418051003281000f8000716009 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 745356241 1250 745354991 745354993
    0x150a03020c030a030e06070809120a051c0606030c180311030a0c120c052e0921020a0f1508190507020a050106060f0e0f01020a0525060c0f0311 63
    0x11915003070005045038400301c030380008690707078a41080c1c1c440d40030417007103600c400caa013040055405d1052040340e40b10801c100201c18104000b44043e00300e4812016280034003221100e00c10060b603201c1d800c60140c011406074500003454000c1c5038070001d219144810040c801a41107562040c01c0da100c0b8620342050f1010190140306004040c1d0008000b1700303a58000b0308000c0075486110560f0302d0328001c1000c00c0d5112a01c500e406000ca058500c2d11034060404142884024400f042403880382a00c1c070703083c2507200080007400303504003a03200e40c1c031304603143e903c0e9208903003000d4403980b0faa4448004004900440c0d00c8900d008140c110110b0080e0a0320703800040840140402c0104021020162441142c42400503007099a0542c1040400d000340d03c06404503080c49101245241d1004000c55298511944101d880145401090340240401c1e04a5a0004149d8081149985c40c0b00c80880d5100b51010512043d980c0000d0348520450081030a80d61040b14003031602c82d9078034200c4940d45401c0e80a400c0b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 745357491 1250 745356241 745356247
    0xb1305040f0b090c0102010513050606040e0c0a08031206010f05040b0703030605060406020a0302010b091506070204140c1b0d0c110a090612033504060e01050103032c150a0302 77
    0x41003040380803030700c5083c001c401091260081800203003920300140030740404400e410312060011b0310202e40190301040c180d48c006010366203038503942d01c0c1030050514150011400f02d400b20b04002d01000030031201d54158007011a640329040111444440c4444500019009100500401d11490001c1104a000c0c1c075010840075214000624030f9881a840704016a00141e098010150207015840b0309480484100a040c41d04616510b00344000484a92144000050b42c2086561704d83c03294072040c580303180390796840c600703c03104a4195000c250b01c171034051a882065005070000044150006030144d840001000d01c03586e4072607840c0001059564008581000455050b0b81441010010901040d0420945207542000307044000b0b90201505ca050b07a902a8800621301c0725025240c3c9a44003221510659560401d840242600c007042902c0c2c0d420072000000741a8071501e40d40301e0003421f00ba40a03112402e014912065507400c801c540e0410031098041c4850f41c40315000e00300344040c82c140549 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 745358741 1250 745357491 745357493
    0xa020a02030d030203071205060619110601060206041e030504180f0c03060f080622050a050a0c05130b0102100b010302090a0b030412090b0304110103110c0601080c01030b1305040f 79
    0x402d2028502024000a60110401010a900c08003d0681c1d100220f02000141000d4002c1404c92140000e100d15210040042003a168840c600030006584520180d82c05540c42e80c0c0002e444000541d07060b0703540ca2020048080d60070300511b0f03072501682d06031100f42c135051402d03110710b0b03003220411841140d03d0740da002e2810004a55024000206029950000c1e600303040c03803612613000035150400308540d8083c0d006c20085078911b041c40c0080c3c10b544098007a0511092400e03900d088508040148640503000003001046000c0e15000285d072411030340908010060340c10314045907641d038500340c0103a110521482644802da4403102d240e100614016140840d1500400d240c00200d50001c6c801000c000200310901040f00b035500542041440c1c040e144500e0882060320310700010344042c00c0e0010003890700785541c0c060ba000140c130a0380300c007001da00d07011980d00350b40e01d07003400b446503040a009000c100a9030358820f22840103072040041c200d064418044500f54010000240101c9159401c903481c54 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 745359991 1250 745358741 745358743
    0x130201140f070b240d0206180a270c0206270d0c0204180209181501030302030c0c040e1002031f1e0f03150b030c10030e070e07090b0a020a0203 63
    0x11504a01a1252800a00740100388031813021403020345902080d24250424526036030b10464030b0b0225011141c664a6082030181803044144a940b00765001c1c4882c1c0000802c42c10501510100300349101041c65401d124103904c030252000c681c2c01c140140c200c480000c403600c078000071110074821182d42412941004182c5503140c010711042071001306407130000f400b00714036080c001c5012448145004100024190703000c6046c0510103001d24400d20f00564082c550440104200c24040441e000945125652814082d490354000803544407140191070484a00d0700b4140222121002804014000d2501d0100c01c2c2000f9003000d407224096001607060303800c01010301c1802c000a820611000740b400030703803080d020083c20880e03032060510351080031042001c84c0180912911198441c0c001280441e4018002070a08490005051748554000c1d45088000ea06034007058a6011400440e03d41c1c5440350442c0005600c00c89181c0c0000e403401d0800e0218140c10000740214100d240102c0e60600c3d815130010f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 745361241 1250 745359991 745359997
    0x204181509140706020c1309081303150902030706050a05040806013b0a020d02360402032202030a050303070302030f070807020703080307090504062606130201140f 72
    0x4800311940340c080d8441440300021515038550303140801441d8880c5840c030007a488141c8220344e14400c0304403900c10903100350b142d08459030250340301030010b50351644040384030840300c25404152031110071300c40c0d034450882052052464260f00200109916441c000007151309034010528001004014003000401c0c6108001d040c0c0070b00f00c100105007200311842100b01034070040811250310210440302d01e4100e1180c540105401550303180c400342e83c88910798125001b17445040c107134415841e5000d41045107006c0030080740b509862141e040140c040c1c0d41104010076404265502e1400b400509180c1c6c000c217890001700308100e0b01c060160b6003282c403a030700c0312402c541044500f6000720b9000010400180d01141c01140d01640c1d42c00c1c000c0e51030500c004002d641d80b06c0c502009107013510003c0444d000c07500811403e4010800200188032450700d0311400ca05220082d144540150880703a4100c100c00808500f003485049124001c00028071960011110300040304202074204208102884101c15042d0003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 745362491 1250 745361241 745361273
    0x110a050714040c2304050d11150310210503120106120209090606092103031603111210260d0f17040f0b090c010e010e130e0f010623010504050a03020418 67
    0x10145020703079548c003803040c1840e19024618410004004000250700c03000700c0392061303d10147c05100100035000d03030b0250340c9041d11006002c07488041910703964405012559030603244999240e415110840b84103800b0b901030721050590240c2000700081d614100080603140035a00102407080b294001c05058104503c03404006910b5040081004482d19410300c1c40340c40c140d810306d410814003501c40304101c0d290080400c1e12481c0c1c001c103170100c1c907421100341907103000d0198099203800c1001107000c18540455410802000c50249062852500c1e020b8010048103810726201c8a240951b4204103038019803004000302c41688000b03489802081d01a1031151191070014002d0003403010341000503010314070710305d82541004111001c9038400e485013002e042080c19100c030080303250703022036030310a0a0090b120b1b9107508643c80e0241c0065043c1500500c01c111140c0c84815000d42840c802c0112550711540c0500c13600000d24030320800040c1015403004601e039400e030303401150807007490ba2101b01440c50501 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 745363741 1250 745362491 745362503
    0x706081504060b1e0301060c0b09010f0c0c05061b0313050f1f0e0a05030f2b02030708090721080d060b0904060501030b0a0e07110a050714040c2304050d 67
    0xa00d072184c2c03040865003403550a0304108103a08541c944040109141d52400c402030036001d1050120350503440941000c121020722240074030621001134401042c40000c02400d403124490580800c1600d41501d09020700c201c1d10800e641d20315035400005100030040031004586c80c0c0f1030720505205814050241840e2042031981d288108120344800c64169841c09126012581008040e680055000411585100b40092050b600c03a0b610300314860048106040040060700d005210410100c4140d00440c03003040c082d101d803403003500c1d0744103186e680d50340c1800343d848414511714034020f000503243e4061003d9442403205c40d213412498401c282c1682d40715444440e0f41000400c800d4218a45409000d0180c071007844c04100d80801c010009010003400d2040190200d10080840e000d14420003003103120050110460303d07014010300d026552400c041c4030b50310380c42e02c80502e6141c892915010f101c0c0c01002e039545940e94504040140300345003481d5040170a829a0070031001030103484024580b0140d80c0101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 745364991 1250 745363741 745363747
    0x1e0503090312090d0311120714041a0c0f072d09020a0306031401090c030f02030c190302030706050301151413030b1905091b130612230706081504060b 66
    0x800c050142c03150645007804440060018841c500a40341c5070551100b03e89c0b41003810b40e448a02c0300d111a00c15038000c440103040d4803103144001d590440c002e00080f45c0001c1112103c01504030000e0f1034800d0340c082c494072117072080208000440401c0056028401180e000c01d10103a56000315401c980c000f41030f0078082601d800081003400030102c0141c140e0341d4050001d100b89005c5c1d44d64110300c4400350000611244020f403400302903440402c01d03000880ea0260a51500141d60320000c1329a122030700c0102d1180c07094200114a440c440e40039241201c00c501d1140150b10348091041d291501c3c26000712101400600961200102c9070707284400450150400140a0602102c4049003040301607100002505000a001085ea00000c20040030450742e00f0001d070300c02c01140001d02e40e08951110400441c100800821285d01502441e0071891184103001c0041d6488894282d012900d0f6064140ea40c0184908209103400b407080c4aa02c000d1208000034034000220024045444a400c500d070096404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 745366241 1250 745364991 745365013
    0xc07020a090b041b08041b060504061107030b010e040605060d110f30060a0605100c0c0e0f060915060904180203060106030b030d0903051c0c050106150f1e050309031209 74
    0x113415011826a81e80c00004403800c0c2340000e8003910451064104000c2d106801c03100c40d060a0050078055a8800065071480d41c1d51806c2c40382d80c0340c041c2c400341c0b485032619010800c503150950b00b5480140c0e00c100782440a8410718100a42d4107800000c042d00440b03d010961a2201c81c0b01c0100401c024810f0003052a4080c401d00c0340c036040d00202a00c501601d00082400141e80e02c2d01c289031420360303900d0800c0c0c00d10868905003000030076641c03105907021904401d2040145200720321604c10002683c00780281d40e41e83d0190030309440840c418a0300080200180030701802d29030001458070000415411081001e9800300349410426800000043d80c0c8502c060b03650724041c4411028614140703040208241191911925440c240303954480c0c15031032044041c4010f006511298049410034000c000c03880c4c3d904c0b030403c00346030b00c588542c0c00280035030340800880e03020303481103602c210071541c444c0144040150709607a01d903c003800c140401c1c4010700c0180c80a10f20390508070310030092500905100c1d924 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 745367491 1250 745366241 745366253
    0x40504150c27030807021002070b071109070e0906040c14070602030108010e03190f09051806031204030c09050915010807050918030a031a12010501030b0c07020a090b041b0804 77
    0xc044402e50b46058840e0042001c42c14035003e41d6007180c1c0450b60400c4403503004000b41d107060115401075481e4480030440f03405100e82d00d01ca00760010410341e26052184c2d60041c04480302c1c0028090964407000b0b040209010303042a40c04210020540c0c00c0917902546081c080180300c0d007001108481094000006000f000d100f0300039600e841ca500b00086040000410b140c03400011300c2000da01c20009031030104904c0e5032280d0428001400d024020340340c408003d030410401080100e80b9540030388a4090240c5c0a20002d900703c0d001c07290880c0f50400c0f800d00308035914007c1c0c81c000d4640b030024031a9042c4a40710381c4d40e680b0b10b24000d00c0e20200410440e482e02c2c00703004034510001e2903590790000204800c6055000801100d80140c06441c00041003520b56840c4415440764900241d005440314040100c3c8120552090341aa400350350595060b80d02c01017000000c1c03144e036038020741040300c141e420807403010250840c84080c10010030224000c00c00706003a180d2206540104030000b00454184414404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 745368741 1250 745367491 745367537
    0x60339030103061506050d0f090b0118050130060605040509070806010506030c09010e0a180b040b030a080403170945180102040e09060106020f0f0c040504150c 70
    0x1295144e1005291420102820b18010408510f02d074030f8440300d406946a1142d4443c903020356001149640e01d58544640c0340f4501c10714510003075060f00d054004280f506d20302d411813140c070b00c171000380c0c503045548903a2400391014040300803140d8030f407590404640c0b50b9540c042e007407084d2000002055040c0c6087d802502c1c0943c103902031802100104103011078220b002d021140d00210a0811050f64000d01001c140c19124681c0011900316030b00e091607400c021903400c82003c80034221014008a10031508258a644001da401410684100300c01c1000403002d10300c00100c42880b820345800e00c10040f01003407400d22550f2000d008103000050050700b103654400380b10150241d4401c41090440450300d111b20054015000d409141c1ca030b68607848860f0341c00d40458014101d80e8580100368200342c0e20240d0b8603402070243e2400b501403a40c400c6602c120001c0d0354640d09480c040180a950700d07180c148401890f01030001d65035040301d401c0441446c482c03401a500702c0040e55554a080c0f48214002181c025 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 745369991 1250 745368741 745368761
    0xf050d0306031115070f08180108010b03010608091903020a17120105010809010e0102280f0203041202010c060218130606050304061112010f031a0606033903010306 72
    0x5181003402c0c07010500f4403140e0040c8034000c2e9860102d0100c5849850901e000d40c1c44014020442140c0032030030070030071002800c540d882d0400e4846d8101400e90040d1440c4100b40500601d012080c0700412045204460355604102c4400680d8216140c0c3c0c54102d92940f10001d094025034840700ca2041000001d48440c01602e030920246420b200303400e607020448003018400e0303038100040c01000c141c00880a5121294141440008540d80c038a1025200640380101440800c558a644400880366002c0c9203804c05105840d4007462502c1c0c14001c64a11548640c1004d9042207015003000c00050b03400d100404110340b240031801d026140b0b41041242d0b160603540800802414541c0c10880540c210381680e4110798050004030703080e6100075141c085401003040305442c94158500000700400c1e00c010000540340070301059031400440d080f5110078030f8015281c80b5048401000041c0c0800d42e10986504c0b03050009c08002c2102518002c12000031501e460070394034620001004104000f1117101e208240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 745371241 1250 745369991 745369997
    0x106050a0c14160e0f060d1a15060403081306020729090a0e0403020c030d08060d050f0115300201050f040e1602150903160c050405040f050d 62
    0x104400c400010311418039620010640042184881e0500406100c2c0f801c10a0848001c1031400da90788074042203055003a03507030615142c400301c04524142001d0340d1204219410003000c5400c3c482d080007071012444010010b25910218205040c265940d400040c40114081d41c0c0c40794540d68a00d50608000089074002d5040d54001d0b0010091079100000b41c011544055612400040701c1484d01c03140303485410082c0e0342c0084c1c411004686880e128000300c2c000c5000340d003100e9280c003e81c002e250380c4084445525011411a800050082c68001e2403506024840d105440c51401d051a200d0300359036803405060402c0456400c05d010480c0b012100a1403103480c1d911104d04680100c840e86180200c0100c041d04208000950b8100c0381240320444004000b500b40e140e83c0c51420410154140c00401d10003c0180204054014840c4021154900a10020016600d003402c41401182e40801c420000c072040c44010300000382a0f40d1b20b11800b4400c1c0c1c02034034615020751f0140b404500f0208407070045014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 745372491 1250 745371241 745371247
    0x7050c0109060f050a03021e1c0911210a060c0f020601030c0620100c030509030a0f0e010c0b040f0c08060f0a0c030603080d0b030d030b0325030804080f06010605 71
    0x201d42d40030520902040c0c05003001341d62500d0740c4408901900c21300362464041c1200030440034041003883c000700070b0400840300c18544042c004841005540c00070601410307c1c100d0813611049403600038011500b03802c00c1c0c240401c3c0c0080d000701880c00c2409940b010f03a0243c0d60750103c00401c0b60090000c03440302e40148003500082d03065595070030741514207000d00010000b00c100070141c000115441c0f00d040020600c00c0f00c240c84040200b007405051541070340c100007420728010035442c00740042a9402c50790b803611140340130a840c42048074030f894081080e034100011601210040b131004029031b4061400b648805101801506203680c0d0402560b00003400d560108003000230908080c0e44107600007100840c0460762442040040303000d0462380c0c2020385075160010300021052070b6503200d000e2200c42642903907610306404100b5001c40b4107006016405400c0340321410000c20103034070404403c541d80140399080a0300c03a12000e072241c2254121140c45d0348100c840780c50151003049040e0060844e898001d103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 745373741 1250 745372491 745372499
    0x10170a0f0b0f0a03060e0304050d081810020a32010e0606030d0819020706020d02191110020c070e0118060807030c030f05010e010f0b12010b0f090a090b0c07050c0109 73
    0x155002c0c01c2d104c09484282d0703d00a06200c00c2c0b01740225401403000801055955129007829660b0303900510b503401e00200031845c4100c00742010303407925038401e5094000e0880e8906079152080b100c40049030019008c1d10080701c1400321000204074a8070b9141079800001c0f0022407028191030650060003080c8654086c020580807242d0000440d40d0000c0d1003846041c01d0078079884424064046c41034001d000c1c038004118210303900d42c158003820381c02070081b8a40240d1270354060280e804555107034003c0603e41010b542103061381c81c540c00501c80044a0030403a49034076075031743c440340c01c001e001c0c6c003c00d80c40200c815070350302d1843c0c907801404040d04250014054281c903560b40c89000d101c003440000c05860180c850320b41030080a40c45288140e41d1000203000070807900410800600c81c14032003900c10607050390790500c0140148501440e0002c0901450440f01d0200104010200020048507000d81c80e000381c800002d58000e2294012080903c10b99140c61091503c1070402c10b20307084260400c0100b40e0100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 745374991 1250 745373741 745373749
    0x9040f0b03060103031412070c1104150909080409091a151c020111160f08160b280302040315020a0c0b0703060807030b01140a060e10170a0f0b0f 64
    0xd411130b545410f0041c903150441d8003000b11805642d010044402c01c04042081c40c507088422061000c1c8104500c5050080800130042101d0384500b000c1c00c9005054030904c07804035603521540009000b803a2907400c2a94a45840003580c1e0314640490f0072004680e581242c10343c62040054009441001840c000201840400c40d000b69001300140d41020641011040d640075004541d00d40070440c0a0704e08071182030300109a035101900c03032407915950705e1a000503800783c046a0944484000c017100c00c038040c9004890047c07a0400740304928854000b5001e41240ca40c01000c400c0c84034880d480241c0c440c1d00e1400d0054030784040d80b000c82081c5004221048400d50f029a03210002070348416004880d4a440c50100c0c01081a60403d040500c1013175808024403006100301c504a6030707540340c1740701c00048510520800c1c4d43d031803040901141c44005120904c0c5416041450030941c6440d01c0b604520184000c554a0013080d0380102d03460769103a100c06038040c1907018046540005440388000ca55980003c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 745376241 1250 745374991 745375003
    0x50111100509030d060812120703060803030f04050c10020606090406020f0406020a030314040b0612070506040806150a0b2733210a020717030702010c080105060d1d030d0209040f0b03 80
    0x85040234074003000050803940070350f100c000901030050440f40c4074600041d1910100c001550300303886a01c25480c9001140c94818064100094154040c108079143c01c1c06015103400c0c042d104031009038080c400381c04d03202c0400e4040e200424880e4010000c14030305040180c01c5941c2181001d1158952000304408a881c0b4000c05401540030f03034448840191202106003009040c0d0000c951111000500003804d09002542c5030081104588912698507024100300b10030003540700300201444240411011071001c1c41d0b803880354682d2120000283c1421a0024822450504a915000309140404621016021180d221200c43c4e0070125151000386c2c550044080800c1c3d4a20340400d10039030000300701c50300c135805450f04c40b030b80100340800395a4404240364a6403c00c40340b8600540c6803034056180b282c400c034800384c102c840103401c2620340604020183d000d03010106a55081040590b0510f48101c8200010a40241242c1e00140c035444207601300010384012039000c010a900b000d000c00703641d550208070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 745377491 1250 745376241 745376257
    0xd050c0d0b0f07080103170310030b0c0418020403030e010813240507030e0c1903050a080714120307030b01021c021b0a03120f14040f06081f050111100509030d060812 73
    0x90725140d986049c2c41c0c1c00307040d40940000380803040a00c11700c000f50b01ea41c4060010f03a1031602e25a81211380150160007280214400900024428400b440c669402040203540000000e80080450f0855441e00480d43e082d0351515100307024001c5c02d41e03500c40e14900c52242c1010325450107203d254603d503011640d91104580c214032480c110a480d00034420701801c040c001f5540442030302c603401e4840c2803143c100e41240b03606992140c000d06608002c5140030032070b0409814101119810740d00d6902048004042c21a00241584503440e107021480c8502171704540303051010350050074101041c0c002d0740c4000c601a05070b1805450094800e2001420840c051a25070001c2d26180b9001007000c42c04540071140d5002000c0010360010300030032a0190302c0509000d0b280291654001926450714890f80030544038440d2a0b81d032804c00c0e051055600c1703110380c4110014224211554100d000c0090707030031036030b00381c1d000d0000358400148030019001d54042c0390001c05400000e8a44030102104200861041c480 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 745378741 1250 745377491 745377533
    0x5030106030c1b14030408070b091f050a0c1e0609230c0d0309050a0914010b0f0d050612030c060115180905270c03010b0405150d050c0d0b0f07080103 66
    0x1304490381c600b040041d02c000b440482c044404980d6102c150441c1a0302c55940d1038019241c0114100340d59130880b818000c1d01d18660380305440c124003488111184e00d9000320071200ca0340d5030b00700380603414074880d0000c0300c3d0740c0104000101c0810524014900510003401e5401402c95940301c0b24007801e01040c1054aa0400c1d03852140b000200d02d001c642403c65508078681c013504000700440c01e4461540b00014811030950b101d00640d80341c0007000b40500131001c0c81d0000f003000700078404100f2034981003c1e0b04407201030300d41d144036490080c3c61f0781180c011050300110340d0b016000410144400840040100c40c003410900c80700309808030365001590260080c0c844854a68002c154100c06059122040c03d609002c3c040b90520b40313100c0b2a03104c00140758001e2081d1b0900c484d0307070302a141c640700b1a4010f11000c0d20544201100c030090201c2e09408032030070340309800707444244a0103032079000d141c0480621840c40503103e480e204c0a0f0151441c40a031030041002814001400060465040c1d10f0000003141 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 745379991 1250 745378741 745378763
    0x60c170f151c0f0813060503010b04030f030e06030a09051221042904050105070905130c02030d1401051e010203090d02030a060f1a060903060a0b0111060705030106030c1b 75
    0x41000094000780b510040542c840d0b08500d805100c0401c4c050440840c01c900c602207219610402111349010a0003003406200d0200410000101c4071410285030341c4c487d050201c002650380c00000c00d0b43d0400c6030345422550f11588682d00300001030140f606002407840300107080c10000e00d5144920078002c40740d1a0700007402e002003402d01082039591390030044c0003030107061452603160840d01e411009032001c4502d5802c0401241103140560511800c1e06c00207001000c03032205c01000074003d040d03404d040c0020750008101c1c40c564555580140c4181140705904204c565250009000c8110051501d41500144503c0e08c03504e1a039012003100c070908005c46460b001c44c031721400000e01b041c800328002491903142c4011429032400a400101100040581505412414005003c02845010f10241e0726400801c0040d20050096204618008042c940301d854000c400c0051481c001050390100c000c80e0002c03004000031a4540601d0100410518200b00c54440c00040d21008c8503160340010b024040c0c1e1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 745381241 1250 745379991 745380019
    0x3190b0606280306170a0305250501062c010905100b03180f0a0201021c0207031202030910030608191509060608070b0301150f020307060c170f15 64
    0x403005a490641d00b481020142e4002e0105005100c103500c9400340129003407490000b2030741000140c400e22052220064420340361140d808890542c8010000703204d0039082c0041c3c0075009a10301c0302d54a03041c4200e00002d9603c3c2042e502450020650440c501030704070036001882083e01c115501c50454000d80b8000c03940340c030780b0100c0c0714400c21290010801c891010040051014000851080b07507a090700c00c1d0b8411031069a420394031100b5501c070107800350744400344101c10345006040035000c090542c41a680519100d0303650015155007410704500590000c5820503951400e003210b01491042414204100b07403512070070f00d40714102e4542c48420b100080111400307101210410891010301c1000c01c0103c80494a0054000c054074020560948240f150100754507800400f2203068441e251042601041002011540211011064011400140000000110725004003124010242c0728040b0b84a04200c0e8104200070040050002e0041907083c0405a1005030348134000350401d6070003c25000c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 745382491 1250 745381241 745381249
    0xc04090b030c130915051303050d1103040c060201050a060609030609030c150e070803070302060f100801050c0c010b0d0201090603090303150806090d0203041505090d06051005030c03190b06 83
    0x40b0044590854040440c0d01141e1100360b11084165118604c034044001402207003e00f121001c0300c44841d0495407078074000102e0701500c0a0041d241c0d142d00041070340c4488003687c47c50341d081580c0444007050003250503c4196028056a0750018000c1c0041210754030f0f10000400d000c015101c00741580707076030b01c3c0305406240c4100200301c400c1380c01c0f0400807816480620301d403005102d0703ca94200c0300d010ba100701162000003c811a011644c0513401031459450b8203c400c0304160001e028007a1014244100080c802001c0c0035080c8100d1020a405031500d070b0352000307a0309442041f040648110079800e140c00050382c0281d00359003920040d20300094980003a14090b0003c2c20710182105601c1c000010001c0e4840e00000c0306071241003d01c0036200e5000d0000400d03640c0340294082d51401303600c0c1c445a4145540b081024000d214802008504484c00d191200c80032500e043d0742c080609000c0752030510540c02d08010f4401528401d03401001c10408040340050b5848101100074031150400c804521290350b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 745383741 1250 745382491 745382503
    0x3020a031803110d030b0d0b060d051212010b1e09060f0408250e24060c07061107060e040c090810151721130e011d0c04090b03 56
    0x489107544240c0c00c030103040151031415203203418100351180e6000145034a1083c0124580c440c0c01810400c0f06545641d500034807071000400c02600100018400f601040c002c003c0c007003515140680c1f156980841e8600c030720340c0b444143c01800910604209901610380c10300300e50b003c80111150080c0e216821440007a1103803059014038009000d001c0f4012420b020007041008551010701014150500c45041c2d1070001083c500c1103a8104842d000043c1c0340005041c2501c0780b4040240e0a00f80b450925000148540c002c8545011182d0000301c00b88021500305210300720b1140c40000418070146003900043c2080c1c1d01c40401d60280b5260b503034000c0424001c0341820098a940820f90f110007540f4205040200050160240300100014002942d455000940d090484204004d000050300c00070780550990358000314025440c0d0300300844191034000c825607001810040003c5801549000c40100a4548101c003c01c0301d1200041800b4924102104490444401240216200c0c1440d00081d003411 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 745384991 1250 745383741 745383761
    0x3030804141608150a061203080a020d0612030807020f030d0908040e160305071704080310150e0f0609100825030605010f03050709062003040303020604200f0103020a03 74
    0x202c04144042001880401c440ca100c102400410b05542d480440c20019141148946030350102138140140100e48100e444c42c0d0b00c1492141c2c05860061020610000c480a80d4080c00054920342800420103a02100e681e0b00f0034264801031a2190305510341c15128450354090078102540c2e007046004020401050750300400c402541c11001f0305e8101415202e070b964880c21180000c0c0b0300000103d01c00d02450000f428084030501c4c0540d55515992241196032003d41888080e600340100081c2c451011001420907085d0780e66510f0f031006d2082c0500c4445100040141d115440512142c030954482010740c50066119140415403915000202c00e142c13400e0072001c2d035982c080c03002d4a01286415410000440740e080c0c0e150f00c00710724591021811103005503072036000260b4881d0708100d180c1c8a500c085d5125036100b240800c00d074a2401580c2d1031980190310071005070700108108810310503480c28000108040c40102c2500a90300c000183c46841004000c5040c980c0c0401c00c0c0d81c400344a90b102001071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 745386241 1250 745384991 745385023
    0x309021305040506010605040807060e04022703071205120f120403021b18070e0406170a021f090b130504090f0b09010b0604170309030303040b060f0a0303080414 71
    0x150003203800409058125029110361081e1000011103600ca0700440703044408050192607118100f500171620382e6403100f50154000c0d024040d034200340b16034a11705492880b03400c558030001c80f4064141810b10401c1e900c51250048600703901c80220301d0210710041292500b421056131f51964844d4111280a101301e00050311488004200c2090340006110b03082070b10508200c2504c2d1160001c010031000c1c9109030b844191442e901107280c49004181a1902c4400180040b0b405034860900803656603510401c011185e01500d044070660400c0c0c06203100c07849034803411602c80d49028401502c484c03100d01c15408900303c000390224800c492030242ca406000000d02c00c1c4502030081c100125145940001518407868010106114080520410b072101901410b85070509103070040c0c02408000003844060b0900007041400343e190b8041c8011481180314100f03420351400c6c0706040c40200c0005600c03850182204007020300219070050749181e44243e015070440c2420b003100c65040c0c10903882c0c070212621 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 745387491 1250 745386241 745386259
    0x30a11030906040b1311090711010e0313060f1d190b12070801061b061b08010305011109060f07170f0a031505061b070513020d0b04050705031303030902 67
    0x900d0086445400b0758041c8001c80c546880700110900c0020301ea000007800503246c044841060b040242e0900d038445002c0c01c180440d00040c24120742941c0d0b9a01200c00c56800c0040c442d8641d248011a20700a80700781e1030310303030300d0704500c0b00f00a022a2010038005140c000740390390340e06141d680c540300906a24201000d400c1019514031041c0043d820040041005c00c07101c0c0001100c036841464414121900390740d444104151002144544000400040d12580d4a500789444460038034146100543d80075540c00f2140e600d0741c01c0040c2103800030b480301c800465003003184000503520700c0213aa583c00c4c030625080d691802107140c44e110721007820304800000038010409403c60364102c806000f0b0030650f41c40a0080350841000c480d44c147c01b50064940c0800c0c14420101481c2180f2103201021504408450314540c0320000151010264145c032f21006400180ca003010400d0f900441d036000c101a1018440e0742840c0d036018105010040c140aa62500e90403e2014540b083e00808121500500341d052 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 745388741 1250 745387491 745387501
    0x6060504030b06011d010c05010f061e0e040b06210106140406080613060e16260309010c02040213031707050601050d08180a15020115170a020402030a1103 68
    0x109581040c801034a10780c007070100007501d65014600c0024841c1100001078048100c0c00010344441110329070540b86590784d00d00c480d0402c40103108100c042c00854000040c12074001c1c1448131811030740e03001000fa81104000b40000210a0400981c000504450710541c1d4031141070307202c0454500345170080240d801c0020000386c2501500100c0c4013244c003510140f001580f01c4110507544c101c00d85144440085505880002c0348544d0320560319107a1080550300c40b144100a080442c0040c0d03004030003150554414541101c3d4040180c0c039a0a842c10044e5090208500000c0e02d480c04404000c2d0155800050b0620078041e5541014051640300500440203000f480120b901600300a40894043c402c0c20000b1560b440d020030008601039000000910380314100b40800410b11405c04880c5c0c02c034603038000121b0b22621a0a0062601225900000781001e50240e03000240f1030039801501032000d01407880c801c0700e6001c1074042c2c1450f0192000340c0e490310741428a000510065400d21060f840c04002c0c01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 745389991 1250 745388741 745388747
    0x904080d150f14010e0609010e090108150a1b0f09090c0203090f0d0b01060c050a14030a20070303030515030a05100b010201330b0f09030115270f0606 66
    0x1c1920304540325018000d803034800c84a204640b0000d018089030b0040c46860b03452910130001c04a0250601d0002560307040000850082c5200b0380019880350080082d4114500e01c03124100d40c001050103050060035103141d404601940d0540320302d020414400b4500300382c94000e02e0501d0003046e50306010401d103450305030020f407a900807900e40f9200c0c20110403007402519210100c101101e80258071441141d20b84002580c94060080044640d800b844000703101080620003078004810500f4041e607520049014014483e034501d80100c05030000055040b0701001e4001201001e40e0f1345401d00107100e8440d08001941034800c016040c2e810300c01c0e10f140c40c040000104000c00c212700344100034404032046000590903544044419a050b00320610026410402c10040048100400002c01e81c0203403201d031640d04c04d92025100d0b042822002031584c0d6035040c00d200c2e40003003034208840705c90301e03605050800c03107580e041031500b0000e8000a807041c5102d607000c0e4403403004400758800400c4099910200a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 745391241 1250 745389991 745390031
    0xd050d0c020f04090b0f070c150f1407020601141306060e09100b0a1d0d0311150402150a09151206080c03210409021303170f03060904080d 61
    0x100e010310b02100051000d41018015040d030703143c0c4a0000752080d84c9154000b209178000404000800180c1c03041040480c50040d91030501d030a003284081106002020060140e603030a0300410b40415040040182241d40030950b581551183c140c101c50140c3d690001030708140718400d0f10314078a844d20000145aa40041494040203001d40740c04800303940d40202880000c00b607100321074161004006800c4e520b441000d0354201e407240c00c2030480401d200400412401e99803204100c020460700d4030080e80c680b03001c01c400612a18900c101d0f16041c602075011403a20404000d660713101300808545101c0032409010f0b480b0180c04c0700fa51042803028a0007008219a400c407080c074807854039010000c28070760408030300100070083c060014840300007149000008090b841b581101456414440824403c5850004040101c40f1001e0840c016042d41881d281c03203000c40c03002d406241c0003004192109040302066a070700c60400c496110b1550340d0360610490714402c00c0d40354030300c081c0740c0300726441980705013060307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 745392491 1250 745391241 745391243
    0x5060d0209030f0601030c0608070918053c091e01050a05100b1b10060306020d0b010203040e040b1315050a15050109030602180d050307030815090c090d050d0c 70
    0x21240041043c2400c1e0b5107401c8280405044031801d070b1420b00c9014041d10301c10740c0040305ca150540406503103501018a203030460844010310794407107040c040c45a11092854486030342c11a400500380e03001016108a04940c3c0542d0242c29030312800103032400b030051004064480e4a0819540569483c2d4200e500815045442901003440c200100e481c5049081455059a58801d1a18509500060300b100810002000c1d85e140c0c1c424546544070300d100a000390303c02036101c1c18002d42ca0301280c08006054400020070f0604651081c0400c1090588001d4225000f86d0800c1d4509001c0d1a01e03000e5006080848402400100c00d0310403034a8618816800340b4403404001008001c9640c0381848100002c80c544102d5000071091501032000c20001e9000b0240c81100032000390441c1002c0c0041030b00c0c0804200256515000410303444141a00600d50390340c07224580800402e541000342c00225100c00c00f80c400d00416201140d01495a240c2030141d150381030300101280d80350411014018183d81c40144 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 745393741 1250 745392491 745392493
    0x1d060916080619051008070b0901090801020315011b05011e0b040905030a031a1f0f030509030f2203080417120409050403021609050f0601020c010f080a0605060d020903 74
    0x1000150420002c148a8080c049207a072124a000143c0c03400b001508000d410200d0308458a180004d0740101000b0443c01002e0a120b05903d40141800141010708180d000b610142d00410030020642d07102c0c404404464000d0802a50503800b45585a8503080340c040c005105620b000e03002c44028035a540d0070307009651440c4080c00384c20310071020300c01980c01d11000108964030502081c00c02501039040b44c9140030316061800380c2d546d4620006807c00c0c0d6aa04111010700078032843d800e01507441400b030803012920382000d001c1424401d00c442c0d038030b20a1010030390401c207000c12001140403032054141c08410383c07000300b00d20640e2a41007004050b030081c80b40c40f10701c0c8208044e080d0140b00206503c0c08011324207910905151401c2c900c038021340b000a00440850141c0740381c102000e000c80b810350340907068a148c0040c0e1450404108442250080e102c1419940b040c03003054810f81e4000240c1c0c03010607143c0761108164882150303550140c500c0e50411540003401207100c02520109601502c001a4120 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 745394991 1250 745393741 745393783
    0xb09040b010f02150c0d020f030411030a03050a0c03050c01090c08060109090c09090629031207082a010e16060801080307080306010e06190e030f101d0609 68
    0x80040d1102020422002d000da044001c0710035040b2508140d01e0303803000d800f00b11140382c403480c4c480c0a070490780540303000c4850500100911060203080a034003c031007507054004040d456843c1d1005403c5002d000c20503810001c407800c9207802c0610500685443c0c5400500910283e00c080c030f80403200d0b1074980148541403003040c00000c0c11314007034010b0444664000040c01246804c20520b05d02402c0310307450540f455070311084105c1030f041c604a00c50050307254000e034000903082180105410500ea1101c002144038040c4180d10104a1400c1100e4030082c1607403418440f02c16490602580311501c2c444540306520303259400d001400c1c04640300200820614544881e2910340c03070b060700c007810700b801041c1c0d0583c801c0c420f400002e4078034002503030080340c1414006074142c08000014555071242c060070803180707035900c880e45a1941000003120620b070b04070090250092100c16030f0b652a07200d4000c41d092141c4a1040c0a0405401d1079006105100b0700103032109031a0070f2514566411885400580604407c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 745396241 1250 745394991 745395011
    0x311060a1403103503030c1804060806010314010c08070f120e030a030207061103100501051e19030b090f131112070e130507031101051b1b0a0509061210060b0904 71
    0x84100c03803250900406207414841c41c88c110018240380984981c0e00709685e8500410010800c205040c001e600c60100304a4451030500181d0a482d000c090351414807025106101c038960700050340240c014403614082c0c1294800f40d2100000e881c5c2e560514125000c0010b11441d0f0507031617001028944d00501e0f090003141a510403440c0703188812a44003500300b01410341888198851001000304040c504107222114000210071701050380880480075861104e505c14084886c1c0602480c13000103421602c100c800c1c40e0582c503603c02c00780010411001d01c54401e000801f000b42044103000c5000f00500140d1070700c0c5c809040950b0320301203806003000707030302d18100024030403c16150003580055114016142461031035450000e807240e01c440d01818090248404028a61032064580ea64100c000081c90300701e02c2c1c040d03140d20142600310b20901032450322205103c1911031825898110605a802c01c0458a8441180d414620f164a0160225081050003d0018040b01c003420403200c08840c01c01216600d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 745397491 1250 745396241 745396243
    0x414061c0213050405120a0e0a06030902010804061e020c07030209011707060f05191d2b060207050f010507020c180a0c1e090311060a14031035 63
    0x2880308029400188140b6400301a038441d040b15401502c29400c03504030030300101400d65150030200794280060a00c04c14103840d8070700350a40030010329150070100f01e040c043d03030002844810002c101a02042d151a400b07200c5000f0302c440100c1e581c80f071704c4046407610015145151030f40c6180c0300c143d00c01c50b030302000070945000c2010161241c2c1c0f800300013010b8440c9000c900f83c48000c0f480030410180903040c00030f14078074081c0b41504450f01035079948046180c1124a100745040c41405a1280286000d030000034805110341c15a1158020720382d200001c08555203400c0000e4425501c0042c240e000d440c000811410054210f0f6000f0b041580030f56100c0706000007030003000002c1900208041040c80042160300045030300ca107200c00130616003c49100d005c010410800401c4003480c0d800902503800410030300980c28210001075038121009890003886c294000e00d552010040c10401210000102e042c0100c003580ba080101b03940710340b80c1c5403502d4403400e2003110007550b044502e490400e160045000740b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 745398741 1250 745397491 745397539
    0x30c0402040b03040b090705060c010c030609060501020c010e0415080f06130b0622050114041d03030417070501090b09060709030308130f0b01080c031908040302040902040209041406 80
    0xa41d8a00b140c0c25540c40c2d0300c1d4501e43d440094044007190044220200e000d444101c001e02442c000c042c0007040301610750030010100c1d4460740c03007050100d2505a05000701e0380c0c0030541008002c070905c0c103200807015020000c0d0007002c2548034487c480f10700000000341d551002c11303810b20480d0001c0540f4242c0d51004940999a05d102d0f5008100c81c40003000070f1080e10b0001c3c9650441c1041c2c1060a6041502c040d902c0d00301c07002a00f01c05640c07076001c0d88106461502d8000c1c811a0900884000c100480705200203a03a8000500700400c1c0c2c5901d051482c203010050740540d48100c4c2c010000b84500505400c04608103401502c203685503004840005140c03a002d40b444c641280d605540f2101c155540907010800c10000d29001c031201c8624811040c0800c100a010340d020b040080c1c090310307a1009000c2014a480180c262042d902d100c403045400103c0c5841054804890701900d01155001751440080d009100e542900c603403180c0341043c4800a4940c080700144180303010742d240c20703502290034032504101c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 745399991 1250 745398741 745398749
    0x1002030a0b1e061204080702030d121d030a030203061329011107030209180102130e06010815100c140607080903160609020a0305120913061203110718050105030c040204 74
    0xb40c401c1000031381c0021501c0c0307110750280c040c0301443d01301110782e80002c0c102501c2540c4100006c024556001c4c1d00c41c41d6200301039a00300041c119454040716890300a844e8041d50121405060340480002c02646407205143c0c5c08120301d0ac402c01282c2d1080100300d182c180400400b074014944160010140e501030702620707001304044001004081d18590810111910081038000c83c1c255a1803440e40442d4240003808070000880301c1e400f02e0782e013400f401010200c0700070b1000e8108403015062191301e03507100d10355010402c410307200001800c90b03000741038a079100c25150041685416220344001c03400042038903401002260340b4002c0380d490342ea01a9941e0700070b9060303220010802110400c0080c1082d40b103100d19510180407412200e60b6920b5440c184000401400e26240000a00100d2450003110a00c0e11321000c410800400742005012803c03107640301801010301003111602d038894401000300a0051650f070300666104505403411002818007845000c1c0030348151142e41c0080d182030b0098030140d07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 745401241 1250 745399991 745399999
    0xa0c0b03041109041707081803030a0503070f0512090618030f09010c0c0e0903070303142202010210050a1d01020a170c040b0706050402120708100e1002030a0b1e 71
    0x40c0e0420400000380f80c0500300325207840c950301c681504480f150b0050103030a405200d02c1c5455034001d42c14020000000181288260010084000542e030040c09a035000400c518210346840130722442581ca600c10b070740d41c60b440c5101c01c508010307289a00258041c03207050320140e040051118100c40355600c1c0a1150003403610b0034140b0121081c0c0d486480041c1c070590164800c50100340c0e85810040301100c1c1626800300c56040044e40400381a0140207105400461031070407225890140340c160013a0600c13445140703544268400103815603100308808019500f031a1020009828240d1440c8014010821806441d07080e00202c20381c008018425192400d689489180d9040e084211819a02d44010b141e404015810f00c004608450082c1c0900786061180c036000071581802c0c0108214020b540102110580c0302500a0140c840b002c1144100300c000d101010030b0b1034201c0c2e07811500b0f0148964075032407110b00c003008103c4005169003003c0d040c40c03000e0740c40d03000e0450902c03050583c01c40f520540c5908 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 745402491 1250 745401241 745401263
    0x61606200a11100e060615070203030f0d0b1918021e0f0f1204111009060e040906140a14070c02010e18040614010602010b150c070f03050a0c0b0304 65
    0x241a0090300303100c4440740040700391203988003540880c0d41120aa000f10b00010380c4200d01b0003005080490300e040035084510b03115410000c40342c0c00203680f40300b0200342c04450400803901420284460304002e10302c06005014042c2c5d1a040e05001e920000e80f13100d0006620101d0710404c0085040f03200712406100588540a40e07010744013100002603005804000ba802020001600c000c0c0d01d010140601e4a641c040b07801080c2854101400680f42900d0001d22400300350f01c1e902051500070700888101d40881c00c000d001120b5200014004140c3d0f142c000c0c169030708000b050421b00f2420034a541c4600284c0008100c07034088801108107002040394101e0114100100c160050b601554900c840352070010714401d070542d40d11703026000038401030300c0484040d91203031b50010302540b040c2d20050261140d4030081194511000004288940c515803400503039074002291900032505000c401d0150042070041301c000360b942d14010341d650741515801e03078002d10590404194009040d0440e401245c2005440131 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 745403741 1250 745402491 745402507
    0x1050919150504020105070b01030c05040b10081501090510030902130203041709042c070801020309150a0e0d0225060c060203151c02010206010f0506040e1506160620 73
    0x40100b0780604141c3c1803003006c0c0014400600507143d00c0780030314806c80400c01c81c1d40c034010500098803400d4006c030f8421031240450001702c1d5400400d056004a02450300b041e2054102d0069503e030365290009038000800e900e007142d001d90140c02c620300740c520a5034100110b411010400c0200e00042e100140442c0030740100c040007071800006803080e400010400030361a01d040105140820f004609038134038030422000303030070303044010b0100d1801011044004e61a62400822658940114840e110995110070300480c03a0410542d004407044950390f4200c0c0c48414991502960ba040580110254a4802840c81c0c1e424020140940121041d07615003580c0003100799140c4004e500018010305c485542004010403541d6411003091507240e200b64400007294071400024140380058104d07031100d104e12201003265031188030840c1c04a88090104600680f20341c200c0300000c0038660020380e4001c4010406184900d100300b00d043d0b5040c82160100301c42c1314a84060512594061080b104a0305d041c49030384 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 745404991 1250 745403741 745403783
    0x603151518013c1115090c0405191503050102030705031f05010503060d290703150b03040305070507090207080315010206090a03270e2a071106041701050919 69
    0x10011203140c0c203002040c80b40218103e4034007100340c034405217035800a001340500c42109001c000e074804800d9600f0b00040c601441200c1c00910060b0000200300e99801303901901050f001a804080c541c4580255501c0c10040b000501582060301d2024400c3c25400a40202120440d01142201e0f010303101c3c1411a071796101001070791381210000766000b40c0194032071a10800200800949802152403800740c50030914402411512807a031200a002c0003403100b440000c0000782600d40c000da161401c5a610071040c42e0103400e0103150b034000d101d12400410342c40c0400c109400551320440880d9960505281014012a510324007612000342d179802c02100400800c0c030034604016440c41190070f48803c2ca001401c9150850036592100905c0482c040c14806201c0500c0550200da080c40181c41d10064000080046544201a001413811140e03000944030364480d1001e480041c040346002c1c21000c14010b40b00c0780a88001c4030500521301400445008a0740702e1129804415000110315440f5601c01c201e113 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 745406241 1250 745404991 745405097
    0x120c0e04031b050f160e0115021e010f0f0c171f0e160306030804060f031103130203060906070c08030402130c020a120c02060315151801 60
    0x754100101c0302010485400d891942000040c86100145034001c0100c8845061040d000c0c1128410080310000300044901d03d040b003419651440c0d410000702942800a9107800549402802d800001c05c815103540501948400881c201955040c1700e9a8800d1a441d422100418810030200d40c14549003403070440036840c007a905c1307040418200c46e91004014850803660180e40000d558910140400000d00e40c89062070070390032414102405114156a034224141c000c9010308800c01004600d00034085120303070816145000014902503490802001609030242c048000381c0c0248a205d02190a1241c000354803441043c10f0313914030803100419030351520140c6c1702500980e804001240c2d40141c040b02d5109031504c80b000b640041048141c10300e071146103888004418020700113940100d10150b00c42608407580082a51f000e9059181001d0014403949407022800420900205418040021400014203010f00c00d88501c082111420710300400e0308550090300181c080007603041da40b4130000b2a40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 745407491 1250 745406241 745406243
    0x9010f14240d06352a0103050906010503031602010507020303041d0f070c06050a2d0f05010b07110a120b04020a0503060403020c121002040801050907120c0e04 70
    0x1201e10741c0e846940496200030480705503103452203000905880e040198401e00000340343d010568100704500b0500b60038401c0c400901039803052071200c07650401520600401c0c1001d411100311420120045140c0071070301d9115000a40400e1920001c6607003240c0c00540a812200c000307004514191602051260944403440200e05009045c44a080180e07820b00207080038000001120014004400000c140d20300e019220075580403000090007903a41d845072440894a40008000c5040d468070043e0b00000d00d800e10407002031a8189003494200450034a16804250940c1401d011031011142000110350b028450610048420010580041e6001d4842060120000d2064400540e078140544243c008010b0890f0050001c40800c8110f00e012403808000d408268000e02880c40c0569020f540c8120240100f4032070151a4104201540200888040e040992800b503490b46d40e01e01003540a000280c1f101d038458090318401203840e81300f406140d0700480c2c2164002c40c21515022052510340c201400c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 745408741 1250 745407491 745407499
    0x90c10030e030d0b1906082a07030e01030617072607030302071a07030e21011a03060c2106040204120f17031003032706081509010f14 59
    0x8468420781001c0c00504004121003502042c00d8200360b00b04150722022405907089903100700814000075900400081d440110804817a41c0038010394500f410084508441a000c81c0c030000348442099440507060b809180280c030f007030082c25118185150704045e5210140c0c4507600000c030411080717800c401540030880c1c030000d0810b4442c40d400412810a1491f800035005640003001c100030000349032840d95410040920003605114299070014007020080300124410841d0b0701d4440744022000c60181d00800404e4000c2228107030036510380d14903c5118204a200e4081e5a000440541f04101200c1c0c900b1304416100082044450002d07840c10806090103422603270a000105e000004c4a00b40e4500a00885812441c40ca47e8900b510700e0012035408c02a0070391090090040070030f0068051401d0b6545800c00003030a0980203441d1f00ba802c060b644000c107124070b81e003000a10b0358011040300e01584030004c80c00310342c086200034003481050a01c1b58104528040004000c102c402c0410b60301c0ea444000c2c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 745409991 1250 745408741 745408751
    0x515011b020607061b0210110307390204060906060806010f090e0a020c0f07050f12150c04080d02010b060301050f190602010605120a02030d0f090e0a0f0f05090c1003 73
    0x740350013080f5607141d5843c9811410040c0c403901c01680401c41d40224000511060080aa242100000b03501001c0d02900c103001c068250882088a151119000c2c001d09080140045040054502a1514610050340114509940403500840b0747c0202d07401c1d44d03e584c580b000642c039900011141d42a805900034100160140c0124420342c50160280c0242c0d0110703009a1181080080c450a0484010300c414a59224103020402900c078814600c80d90001214010000207141c54018104008140860b00c205211001c000e515900382018100303440d0038104540145602881c140c0c01c030b800c0b40c14450380c4500c05000400c018507141c65413202003000508502d4519182c0031124400c5045904a41c1c0036035105c400900c0541084180c200d0380c03244640c002c210000c0c81e134010030307103d9000105141c10450401404480c5e54001d410074402007034941e035108101d2400c40044030040c180050700d692447d04200300ca0b12042e5903801418040c0c414080601480d88060003000880c0d1101c141410501d9118 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 745411241 1250 745409991 745409993
    0x14120102030c07030815010816030b040f06080106060512060402030402060403060c121b0c2003030409090201080604020909161b031d0d0c27020a0c0201030515011b020607 75
    0x20300145014104801d00389480c2c02291801a00e4840010804c0d00710060680003003c4a81c1d00c1511190010a04681c400c40d032030000b90f04901070880f04000c00c0c2c0103400c003502e18420f44425402403040b50101c80007040503548440d0201c0fa9407256000f0440d007460310310301044051501c1c0d8004c0d80c2003071006012624181e52a5119004e0300c01e50b007203503400b0410040d103901c842c55a60240c241115007101051000c8200014060017151480b1030140c800c001403c010500800000129500071800400712512a540d0f0b190741400f6000020040740028185404104542000e000351210442c0c001c003046115601c0c40300d003400d4444090383c03401c2049030410781d021028115114540610380a5640d085018000101441505008200d002c1c05002c0b441940c030b000c5540703410b1040686130038020f503907034600c1c2d00750211540324460954070342c103944001002ca0310785400c6400e0018584c400c0c1c07000d1000d992510000040c0840c0b480701c43c0d010410644800d500b118601c803580140e1840180307030764107003180c07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 745412491 1250 745411241 745411243
    0x80a12020c1e0301060504020a02030f2d030a0c09050a0b13030c080a02031c08130f05070f080118051c0c12020309130e0c060d14160f050705071412 65
    0x519441182c0c80700041c020b000c8a41020b004441c00b800c4107840a40c40c201003000b009541c1c0c81840700060500c035020488000b880d4505c07001568401e1030860410702815032100d01c655a42c41030350090141d5140c00350f0b2041c5c0501030a104011610001c10310941a45050700300c3e80c0ba41e01142500c180d407152110007200146400b040c00c80170b41000e0005040c0d40542d0701c1454941380303410310381818895a440054806613400714516a05c1024141456022601e03880c04206024620720014101c1c00f54110106081154003400c40403551258001c1c0084e1403102c1c001c80602d016050003401c0d50f000000490207250440300c03242c00100c55864500c0c0000c0c03240d100e00c2c12803c0d19100ba000141c200144503006850682c88801e2815040d007410803c04105039001e55890f200d800115026030000700c3d41c00c007010041c1d4420050340d0720361076101007039280410b01c183d140300d911001c03d0301007500c40a10b9060188200c09603800254040c0040c0451410b0260074408004205251540102d050f0224449040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 745413741 1250 745412491 745412509
    0x7030e01050702030a0e06130b0a0c050303040303091106073201110a02121303020d0f0b13020108070216090908070c0909030801090207110103052d011509080a12020c 73
    0x100d035002d1a1a811000b00007040381b00c00d2030002d840b40005002c00010310704e924a00310101c0340140340c012b030f032200a03420550b500159050045d142e8040442004185030b0590000c59209100b120484982c513000c00401616008185002d8a01c8500f60030600c4c0014113010040b08141c1008a845880210006800d0035111001c865400701440401c200c40340d01d40401090100c2615814690705102490000c40a6450a032102034400e242a00760207090046014000e1240c2da04155070b4981440c14041d007d00f402c864410803800503586d140050416880892030035800b00955110048a9241c41c0d203401c00f4250b100c60996014008214502c00142e0b581840740042c8a900e202280c0d81900d8203018180c410160311480b2032600402c401c1c00000c0d00d110078020141000d003000501c9854040b0201011070040a0084d014440d82401e40040d601d0020503a040b190b8a0307882030b9100f06014021502001030744a01586d560115441c01c0000300b002e4510310210006104070344c4c144042d540001c01c814 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 745414991 1250 745413741 745413751
    0x6050a0b030a05011a0a0819060207020a0b0307140307090905090705030604030221070809010c17030c0403200904080d140708010510080906130206070204021207020706110c040507030e0105 83
    0x1179958801c04005482c55469000c40754021202405964648640c46445d0401c51075541c2804d000540900204451079069511a6802904e1511010f444403e1a4856801500e0714400b00b5070200d1140445040d1900f02d0344a55515900c0e202000d00d07003a0700d800680400b0300340a5882c05000e8001c80c454400304405480380380203a0003410500e40010b1480340402c0182c0700c030000860208039040c0804c0404040350310140c420700c0c09844403111814601e00c4800d10150a00a0450000c14025400c160a0140007901d00516054850000300b1a80a1110011030000c035045408000024041046d030000b406200b1000240031840c41c140c6407500c40c030564115000c41c0861640c0c4014021818140c140860040c41d0303003072105c6036040000d0301c10f55840000301421407444030030f40042d0441d12464150790702140d01910645d1650032101c55580d0413201200c548005204800c4000752030740c0704800c00100611268054810f0304801e80c14003001d84402045c0100741034640c0c4600c0c41854007446894418 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 745416241 1250 745414991 745414993
    0xa021c030203040c060f0c111903050c0f04020c0703021012060303030615110c09130218040215030c03010306020a0c14071e06090b0d0e0a0c0305010b040c050706050a0b030a05 77
    0x6440d0510703004503001300c80d403c520100603400840c543c8180d040414441455082400303c1c02c102c1100c3c0016800050560300c42c11078100c40a000401c00c60005010540000d088a8200300c64881320180300407170182080400c00ca91007804204054141001c20030003110641c43c0c45426500c460b0200d50070f40e203141c4d000300c0000780d4a4000301b01c3c0d81d005d00c4a0803ca0703156898848401d5401200c0c142d520403900790341c01c0c03040010001252588040e10100c0328290f034058842f62421403400301c607604250044800f039010b000c1810400780d42410700b404880c420ba03d22070449055900359140c0300000c0d005294044184180305003140081a00c40e644117030850780702c10040200b141040c40b04000141202c3c00101030206200e0305120070381e0002180c0741a280e00d0349a154440000040010140030100c987c01c5183c0036a000e02c0062002c41c0800d001541c2c00381c030080c025000c075042070000311001c2d6024000091fa0a00070302001500b203401490704000e40940220b51100e22900003410310f406000b08481c6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 745417491 1250 745416241 745416247
    0x17090102040321090501030203090a020f060c010f0f0501120308150f0a27051e0c1e1b060f06041503060e0c0301050f090606060706020f0414010e1e060a021c0302 71
    0x420b1340c801c00e00e0700900030a28055095003400c44242d541c4039010480203104a10b00f0848800a13250502502e10b10300f900c4000340300c48103074022035500904c10110101c4951b030a160000c00c0e85c0d4403242c1d8040207103030306d0f40d6500c1c0581d6414034a40c42d002d6040c0c0542d68480700b0286482004e0365001960740141502145052903c41458100b070802017004654a1200c0e00b02410858181c074602c80b03007000d11000d944240103a941c1c45c54204140d21440c10004880352a224000c240c94034440702800c41c8801c011450b49031110300381903c903503c0d10103c030440702102014001420034106600512224403121440540c1940c42e5070310311080d180105d81d00a1154046440102d142c50240070749a044541c03402948654207040100380d8850380000e105900844000828070100606a0f040b101a8026090341d940c581e61600040585071070801070303c900090744040c2c000d58030302e04030b45a09000d4502c0c1c000d82035030888000501c001c80c0c0111a4040c1540241c014002e54655070700342e88030802102d5940165 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 745418741 1250 745417491 745417553
    0x80a030206070f0e1f022e0902031f05071106011809150501150e27100e04030c0b180601141504290f0f07022b0b0606070201170901020403 61
    0x458007c3c050680c91600d506101404203041c94000010103c0002e0710300400c6150305400440c0c07500d0714003c806480704007944062400d01c02598045070003149260340741c103406051107060715604c000038000c00705142900f800c440322684e141d03886004201d00c070b2403030060009007401c4004200c070b900340e003c1c09403810340c06e00341444642d00603d60b448840d030855494000392000500740e5441078182400c07683e1005103902183d160800364003000000c041509150070589007900d4001c2142048078012501c0880e9100400c400a4004011454000310b540040820342c0c03800c01b040e4460308007030852035000518000300e05403102c09c040007400a8031144a5000031600a0404c4560034103503100084040081400703c0340030f0940340d104403545c880050850f180c90300300b94000150084041d003410030114110024018400602503a00c040c0c684c010703290400250782d03681c10700007580704d004002800a40110001c184203032841c44004d400080c001b0006040644030f656001065a200c60164820007001000b45 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 745419991 1250 745418741 745418743
    0x1101030b270a0507050a17060a0f030303060e0f36010c05040311060408030f090307050d051005070f0203161502042306041a40080a030206070f0e1f02 66
    0x1390040d0091070b046190103c8043e000304400e8949404004101c4042c010030203a95038004880040d000445904004030b55901e4090014013443c82211400594100041d00741c540a106142c8107101450191103059162054920b0582003200d41c511003406480c101c000e440c000b441041c1c0710604a4850580d00c500b5070610300643c1c0b400300003161142d1020002403080134004410784003040042d000049c0c88410303140000341001c030250019030308070401038494028480001070420b60105186da003009a6110000b0841d8207a980703079403040c09a402004030038005010000c2c0c0f0138405004224001400115145070313006c1e64041d503c415014950032841c400c1161909207444884101100c150745413038602039144c1d06c1d00e103c0c00e8500a0031080410500044010000b8045603010381c0100c03442d500c03082080b8842c04080e0360710410944440c3c543d0105810b600000c0303c4220641640040205955802c011a07040c00a0500402001800d00904506451380414011241510b0782c0031005140409402 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 745421241 1250 745419991 745420001
    0x3100602100207030e090403020f060c04090e0109120c060b030a110907081909020315070921150b0a0b2803051302100c0c08030d05060105071101030b270a 68
    0x607416941c81000030314002a008076441d0300800040d501c0781e09540c1c80e0704050b1305010746031009012034004c400800c14560003080042c400c2c1c84010100301300030b002307404906003212a40440100005104c90039101d0300c3d0700840140b81030030b104030404501508500d02190900310b441400700c403007000c01c0c4a1400c3c03510704001c11640c0010285003060721440d21110751040c412080c014010300b00e81e10440d62017903440038004a004d80000c98024555400c003080c00504182e000d104038500022200c501c4000c2100a455255049401c6041b0211388041d00650300c2c0103100e1030074255030040070700d00c2c001010004100609040308100381408036100d40340c58090b003030070b070000d00e03075400c15181c01c0422038884a101040c102541e01070b6015040c0540703824095a0b1031034816406081544100700005060b00c0010080c000c034403aa803414480d54580c0d40c0151040d00031204007c00c6d1500d401009403455120f5401b6022491303004101c01c600ca24150340f50f030b002c00410004052004945030801c41d40310094025 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 745422491 1250 745421241 745421263
    0x103320a0215070c0b0a03140f07121802090a090c080624011e110f070f06020304031a0405030904050a1406031906051f0602071503180803060d0803100602 68
    0x10030b01c2d0015990783c0c8022080180a02c0642003c003050103441b0503c03d0340040c402e1240106162502d0a001c41084d800b480c0481d03940e03002840c0e01c00030054a452900405014100c8802c2c01c11042d01281d00300003881038028681403103d540ca041540c0814480740340c21004217401c902400e09814090304d0401928144d00801d0209030808603520702599000c15403010400c2c0d064050000341c070781080210751400c0c3e02e0031003011314491071940565245022030700000f01c07021000704034085a540c483c141d0300c9004034407002d4268846090300848191600043e0350388184118142e0f0701d0214a980020304680d4140c1d203d4583c1072340c4014900455000007a0703030341c00940440081034203505200b4499034040701081e00418083d1200080703400d408601c1010340540b070640e01c005155580b43c3d034000b5524203051060b440c40440c081d003d02d4129002e03110399458590310044914903e4080c1e00c41c190b6551020b40749a811003645a600004200c0c2c0c40d0103103020703c04080014010620f0228000c1c50003405443c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 745423741 1250 745422491 745422529
    0x40608090c0916170606090409111207080709060605040303120f0c0c110409080d2a02030310140303040302060705031b03210f0403081003060501140109090c080103320a02 75
    0xc10305c50150384010075074040100442d0b01040921161038001c0c1c02040024442e0b401410048080c5002c90004c117000d41540d0402040b20171444d9204508020707151f46100d18000301e80208000d001080c4222142004511186000720360240880c4094084881c1e2240b000002208000c51000304800605102a00d5a0855050010a0881e2240701c401d200d426117804d0b00130307500c504170044904103408030b2000f170440a84040e601015a5406526603000b100c90003007601c0303980c1340071405409000f800c2c00180e8016000311f003003508507800d0100c2c03980441d10590302c52105200e00c80b00c10f8052140608032140f8180a0345d110340c7d6010000d0b203c00b91214034080302058280c104125843d865030f020754402d400d890014550b45a10b03003006040c00660f00040c05060070580082680720f944903001c25001003e0f601c0ea402c90b5031b603000c214200c6000c58140400903d088004002058070072003001c3c0201c04154040e0201c14404142d40700b22040c0103c400c81ea608003420040552800c5080049220304001c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 745424991 1250 745423741 745423787
    0x1612020309060106050c0c030303040b27070302130b030d09050901060207182c01020307090b16150b0307230d0c0320040e06041203060803040608090c0916 68
    0xc0026920b0707220502442c010810049070391120303451308000780c044060002c2c0640ea502c1c202410a140041e00480321031045040c0d070880440c4100d468542815100901000341c41c0340c60941d800c1140b540713800c2d14456885900d400c043e041c41e03603050285400445071078a80c540510320b0b10060141c1c51405134482002c0d0740180c00700300400400840401c0403d01c400e4030008000c40c180004010001048560060048070500001e444000550045024115948440c05026a0340641ea4158850030000106100400852200045280c807150500200708200071850644440c0441d140c01e410381c0c40140c000440188665072500d03101c203071030500c40080e2074500c1090080d4a80741030400644c84020034103812504404044550b500411030071440080081c4213a0742c0403d10035a0340c820a490544640d04190450404203000b441510111189000a5800c052502c141a15080c400510300d048501680707800041c2d5640f40c2039038510444181036064000b0b04180401064608031550074022448a6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 745426241 1250 745424991 745425001
    0x617010c0503060d06110c0d080a0f0501060f0c061d07030c0906060e061c140a0b1e04090c030c060203040609060203040302060301121a090c10090e040f020102031216120203 76
    0xb20303c440c240705d401100120f001340130303e004a0443d2141c5860849980101181900071316072007140a40034080703d21051029690082da510700711902072180c2c1001c220f01084c81072605014a1038405528045e01001562400040002420400c100c60690441d00154403e1040000960900000d040090400c0041d5810601c000d1304c07101111030b00074070070540410744040740e14040441080c42040304000340819100c0b009904085402a03072210702482c2410500c81041c2400d1140d01c0300d0f03a090580740c2800101c5101031000074001c50005542281440e40048042402010004000c0005078001c0d59500c0c90540c6c020300c540c540d07400ca5811500108400c00150769540d0541c1e040d2564881010302c0c078600303450b0260740000e07249403c4c03000300d00c80c00803c545800d010425400011043d0b136006101020702e50708864604a60103101042095803020802190390410041e032540d1044c01140e103007500f005e40b804031101c02112020420f490041000b514160b0009203070116110350389041d411401c103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 745427491 1250 745426241 745426249
    0xc040f11030601030213080f0a02180714032d0108060601020723041b0806190f12080708040f03020310020304050d08040302030d110409050903190e0f040617010c050306 74
    0x28000c50f0425801141c160000b5042d141c500000306494000c944030344103100342e150307210002c0c0d240a070301c00c6401e24120020340c4000c102031445a1030590300c040044549501c6810142c001800065803c02450a07005014805201c80550300340c1c070401d000215031606940500d0700500034070071130464110100420042248802c140482902c010500607003082c10004100100070780c1030b20f05000a049000100d096801c103e040380a07200aa51280ca1714080151043c001041407040c41c3c2031200c1e4010801800615242c1c65048500ca07503055032500c440760301e804005800642080090441140d001c0003180307010050b00c0341c1e00c0c00640080d4250725080d11066100c60481104000340700c2038a000600309482401140c2d20354441407020414000000e11002154016024079850076281c500071034032203807000041c2c4003170321048080b0050040341c05508841c00c101402c209500025581c0642d1402d03a43d500950340500b070078601402c2c5011100b840d00d4296002c0d468041e08ac00030400a10190380c031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 745428741 1250 745427491 745427497
    0x4030c030e060d0e1009051513120f09060206270111030414010507020d050a0e010e03030d1d03041514090406060e040c08010e060d0305130b0318031303020d02120703050c040f11 78
    0x240310313003524406940f02c0c03084041d00040401c00034621000030120001462f045012803d9107100b41d6290700794a0f03103900c42079076a402c0a85808642c42c4800d8035414080c03002c5603c90500c03c1c802c00010980c03a207035540c103c4e801c1e0002d417012a6404098407500307000d50424842c01e0b60005181c401081d012010001c043c0c0300d4801d104111081141c4403204004c03a034041e030144040075030040c0c226a503c10b440800035004141e041651044080390000c40c2c0100310000003980c0c2513418101d07840800317941540c1d09981c022610f2001980380f0b10140481c04030f03551988125002400d1644500411403c2c1000700003c03103996555840038130800e8001806800840d500c920780c81802035920780801c0d1201e0805465500a452090342582c1c82040049081040d05010303600800240c00814011784801b28650f48030301a90310f200d031968081400c100017600d4640507502c0c403140003030300700b541d81c0c001800000c3c24808a070f00b00342c0d815401103a07605100d050910079804444d034441030070000325030750f040a44e0480c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 745429991 1250 745428741 745428763
    0x406090608090a030c150b03100b040c0203271903030302030601030f0915050717161704050d1404090509161d0a110c0607020a06060902040e04030c030e060d0e100905 73
    0x22180406d004189a401e5100d4045000000e04581c1c5104610303081034086d0120440842c045d42c00c296400180e00e000105850140c580396591074031001c05140c105005624490455910045030244207592600e40f1601001450007a44c0c0982d5910f061800501512100300c0c85140c072a00e4802c03914003140da0b0002e070186843e0407aa0100d1991208503003110405010043c45148511507020b12a056a6500d1000c0c0e012620b502c0703403500556420182440c401046170090b2864003c2d072158002184142d0540351007400f400021400e141c0c490070309008442c401c882a00345980b00449043c4013200070901400144008001c080039000d111040c6240c0c00c50281410500030348444580c1003d1040d00156400380d12420101c031a13501d0110002982d5040503a8280c5005180450114994140e030007241c1c19100b00488810f01030325150307421514095503c2060303003000600030302c4c41e55a544a2009003810b490343c02c030215026035003000301800d051400c291400b455250401240c0000d07070200d0069a44 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 745431241 1250 745429991 745430003
    0x506090f13150e180604031704022e11010b2b06090803160f08010e070c061503030207140d02010c06060513022104051f020f0406090608090a030c 64
    0x50720349414220060710380c01c6100c039002c01c1030070004203220701c22001c290b12a8032650000d40c00d00b11074000180d00c031002514041c2c001081c0c02c44400800c0904010684c00c24405400b1207504015200c50a01c0c03031800c8042c402c01d07810f00396512084142c1c010321244900d0071000080001c41c044030300040084147c10018404003040d41d0382c0005803200c2d0f2582c00e2249400c0740c130602602d503c615040e0016807049401190003803024200162052003185800458140c0e6120210a80d0070300e280381001c004024560010401c000717001c1c1c0d001039903a0261040b008140b101c080b02d19410f625004e406d002c01608000f0303000804800603202a603811f200c1110551302820625015003107810210040c10068104a0308403100e40401c103210b4000e81e0003040c103010f865040e04900d6044940001c10f5010680d8040d0490f8050380121210700c800a0011600120042005140002c2c4428407900c9400950000e408a01c0d04801002000e030072030342080d8041c0801d000b800c2c02c1040f40d078000d042001100300107041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 745432491 1250 745431241 745431259
    0x80313030b0f0c0d0e120d0605090718060503060409051b03120f0d0b011106090706030e010207030905060d0905060c0406141c150b030411041a0d0213140a02070c0506090f 75
    0x250b0181840752400c082840921b450b501c0c5040840d00000d44007078403425004802050000f600c46220785c1090210450385013583c41a545001411203441d0405041d184e805903030b843c0c05100050040180c020300001525144011942540c200741c10701080081301c904465080091b0500245c01000701d5001448a03600080c03060303140c1004a42c461603500700382c1010320422090111440d00091180308035085176505004620210507640d00380e00600c2e10080c0425185d44060100c0e2801340094074120f480c1aa0020309105a83c076864075003d0251040081c92400050900404e40d0040808400c0444070180d14600841040e034180c40c1014440a241201d40c0c03500b4208800000d4400f1074010800b0781d81440c0c81e410242014004907440c2254188202d03c1c240c18501101102c0060b00401d400080c403072200b24041d60240b10540c281c801c611030549a50309998001c0c5615000490f004034401000180c42c2c907441c0c503052581c4025900030a200b50030510100440c4c0c0d40d1821908001d034410340354200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 745433741 1250 745432491 745432511
    0x20a081303091203020c03070605040501080402010f030f091a060406050d0f061b0e13111204060212040515070c080a1101060b0d0b040f0203060f0613080313030b0f0c0d 74
    0x724680b07a0307040540040c0292488400b81030340042c4003c0000011010b541c0004e507100070540e0180f1881c4541404141144001005517006003c26494a060742c1070110380c020780d203040041140c5441008503011010696218400c1100d80d0400f0b5203c40180c80c200321250816000a010301000d030b400400450540407098200304040e0414000100f00e011417440b030350041400601460480c8450354000d080c0150302644140c1c00b03014910714000c00b100214500f0508103001d03103410200074029500d01d9000c00068000120100b01540700e54000c0015002c0c104c1049020b07060320304003a10a2003000340745100c800210b0380e01c00480b1454601c03030501803240500985440d0142500740e012581c00f040129860302580d40760341029103400c100704c40c00c01064030710025281c124001510305940082d08100780740c801c9d00b001401056840c420b001c0c03500c000e40e955503496245900101600360442c40d511410800c0000c00340a01d030308986050540c56003880c00c00c020062501441e01d00707a21041d100c1490301 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 745434991 1250 745433741 745433747
    0x91d01030210050903100605010210050f16090f0e07080f010b040905090f0d05030105040f05090a0807151107020f0102010b091f08030f0703080f04030e0103020304081204140d03020a081303 83
    0x4c1d078090700030b015501c52161940c2e246009004501c611400750188a40d03601c1d00b4002d52081910038100000e035107540e40c40d0818040380c0c5a510035004400c1c404803200100360103040c0355a0400418401c02c900c0b400e440d00300c00050121801074080712048501d0383c014080300ca02c20702950300361108040e000a0555030f1020f401e15004c02041140114000c0c48114100c0550003c002c50681744c00340c906106c118180d41c0b503242110001c44044c001504030316042c13800220140000c0203158080c84545602e02c980c594030300d08440f0401080c001c008000100b0702c0c1181041c010750071404600b400200890111880410300c0c4e030300c00511042640100900c5000c1807660812a0341c041c02040040b243c84070004e41d2104240c2d40082029800b003900c18002810400c40a10690b116540c19903406001205201c010740203508041d10803111a00184404024500013181d0b0622903030150b01d5020800c901c03c0303107036401d01c500d0103000410103004002c40111503030442d00054205404c1203403d100304460f41011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 745436241 1250 745434991 745434997
    0x1020a0b040f020f040510030b150d1e080a0e010e040209060a0315120f0501050f07020706140f0703030b040f0b060f09030a0b0c030f13020a0b0a0201200703091d0103021005 76
    0x50341c40307407800d1b06118824000b41c581400b03482c8155008040c80e11407030b5860400e031001c924010b41c0410540c83c00400140c0041a650f016030014003440076042003a0380301806c941199443d40006020302c4262515581c7c04600058503103410782c2c0c11890700d1601404101c56120b90050f1005140d01d58481000d28074041c41c40d08010145002d101450703003064600984054074801003603540b50b00307140105054a000b80d00d00c6010320030980040c644241b8010041d145035807003028001001005010301c1d1040011000208003117842641c0001300f801240007000100c481d500d02124499290641c41c041c03d86502007100c0400703030f03031b1002552201a50b0001a140000080c0e004040782507000920942440c5070015502a1036010011030950b650190140c010381000b440180d4000070000d010071605c9a018020702c8690014400820b811000c1c42900c5010040c540c0024030009000841c0c8060586c40801c00e0040c06412070000b1041ea84006102c00d2003406010203840b54420840c401e0320f8501403011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 745437491 1250 745436241 745436269
    0x5040e100503010608161d0601080901060e0c04080d0f020723030a1a090604030203030c07110a06050c0f0a02060d051e0906010302121f0c020a0f0b0109060501020a0b040f02 76
    0xa000d03841e1592840b07078885140d0007103207288100402c2d000c41d047c0944280d09008148000030320056550300401104c00071740107086241595070f111004074108501d961014130a003880b0110541d51458020060300d400003d460000401c00032074507081c000790740440d02004440400703092901c000034410032a8070622a850000f07905200b055241c00810884881c04441ca000303000b02c034403090382c2c1c102004c2d80340c8408850050044c1c0042002554044420002d002c1c12130007a00e00d0100034403998041200a06203400810103d43c02040032030090008000920095564a005d0201342450350701041d1280174482c0e410b8800341d140c00000360b002d4607115030305000741c01d40c0b4143e451130308080d41c038503440348028001070303001d02c0c0c80c0741b8440095800014803041c3c0c020f80304075038829540d002541d540246400301d001802c6006041c4641c020600c290344051105006004400d115490711070b1480450729554030490542d04808080c4021901c18141d0603417198205405e00e801290b240b00090340d82c4ca10502c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 745438741 1250 745437491 745437493
    0x608060402041e03060e030307020703080f07082205031914030c0304290a0804120516050105090f0601030b0a11130b120105060910030f0e0114070f030c05040e100503 73
    0x103043c08419500101c000490f80584810403024161080c91512403101b22807950259104480c00c0001441c04001024102c455048613410000d540e551007005620a40380c03046083c00c030300b100c0500407a600350b0507001404201d008041411444c02c4c06000c60380001000b91122050140c0301c0c500e0360f4244100c1799080c2d1244c05a1340d60383d490740541c2c044000c50a480502c84000c804000032a112242e0495064003129115201c8544e1a42e40d900e0b081500d0600f10000c00c0403e128112520517042c1409a40f907101d0030001c18645414801c01c0c0c90301e0740d80380804003140d000400400100c1c4002440c5900058903010100e2140c00f11300034800e41e40319011780b40c04101c00a400c0080e08034440c130054000342c400c002200b8070303d983c0c80080010700d0040041d800c1d03000c41066100104980a94042c00742c1540300000450840c020350f850501f110300e41400408482020300410182650086d00d100c00350b205401d040203406e042090050290059004180c40c488484011490406803610400c4c01014020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 745439991 1250 745438741 745438769
    0x6010c0b0c09032b050a05180112050a020d0e030a170a09170403030f030b061803070e0414060115050403060c0c0b240f0904020409080706060608010e06030610060806040204 76
    0x14540340a410413100581c0d1904240881d650100d0384904111201803140e950340f81e00f07110940303060041c890003801c9094140011101d10b0f440e0b000c071502402e482042605001a00c461103407d80fa4195540c0c0c0300d486041e90800c0160034202c0742c000060480e00119400c1103020340c0d9444118600030101e500c1c02501d4101244080c0100d100c0c13003801001980d100303503580501440c480038140c06a94401211079030156013400041600c110f00381080c0c07160f560040450b03100541c2c40116403a031a10075a8140e40c6185247c40d0341d41d221804000d05030045c0841140c145040d43c2c8028000c24038001c074003000b030141b0748503200031240c039205802201046401400303840c41d506001d80d0041e20800c14140322044980c250003440d6681c640302c55614103060b4080d08001ea595225820040140381c100707001c031000032040c014400810742500c2684007074003446d203c1504650600d06042e81d000303001401140720340d100c40d04110010503107a040c0d80840d070140c1000c040780d07190f0400003001380c0256040160450046 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 745441241 1250 745439991 745440013
    0x8190509010b0a150207030b0a020d021c0605010c0305120a1407020705030601080304030c21080409020a02010b040b030a0b0c160609020a0515122203020c1806010c0b0c0903 76
    0x107602c803511840703040b91001141a41c1d6018000402c1e0036111102c0560032140040003c15400c24000b54018155040145400c003500d030114202c2e084440350305603e00790b40c000101180f040d4400d44020304800d013844c20501c442e591f00188984034500c059503254000402085404c2e541380c100350369104c3da080c03110100c4c0c508250000c2d0341d0340d00341c410648244903205c00010040404030841d402d9035000300d84030710a1810b00032060b0548090400c0c00c05110210540030005c12000400b41c001340000e5800960348040d45a00282581c1c54a91514403851411500080390360b0001000806103a000c4000040c81e80c40250001c0c2e82d014402956107000f200c018040104100e9500426945200312504041d01b9207850601c442d02c4191720b50542c00c2c040401c0b442154814868400780c1c0003d403410080f60008480c5501c07044c00c03049010841c0982d005d007400208610b400c0c592040b480c011a5004201860310000003401d00302c002c0d030b0151400d5100030100e0300c92180c0204488401c0d2014040310304100340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 745442491 1250 745441241 745441243
    0x21612050304050c1212090f031905061f1503141303091a0702010c150f0c020606041505040209010c02040e0325020901060509040f0c02030a0207050402090a0608190509 74
    0x30440b4101c0380e038012040020068604003507440048103150f030007443d984550740c82078006a8059801d0a5002102c6006488035580820040a02c0303403400785041131b070200c94075045181a001030302060030349098012006041200061901c100e90b610405241b00c004410002e500800220b0289090030003850b003000405c030405140641c43c2d078426a01d02e50702e00d03543c65000107146403680c040007046504014040c003541c810055041154001e050700c0100702250f950b20703801c40d140c840c3c000e01040d071280720610405805104640d03100800384d8040c004144032a205441400307160091034840c0e60b0201e140086030b40f06104c0b48060329400740c001c1000342c550500c295500d0f0003122510340c0c114802038906141c03101032445041d10f9030f0b0103040101c0030390070648181c81580041c0700681e00281d503000d001c510108036005c6c82446a80507001703580d41c0c04442c50000d040084a402690050b0300410002035943c03503940c0040c00b00c4d090340c500b03039409844d02c25015a5001d1225406000142400144001060 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 745443741 1250 745442491 745442497
    0x10050c1c02150112023007031a07080103061503080c030d110c0a170c1506090105031501180e0d09060314011805060a0545010902161205 60
    0x34050302120340c0d02c40000080c0c0d0820b0800d00031a0b0400401140410040c1003400242c0005203c003600d10070401c000b1918826005145840191583d00c401020030501000016401c1c100268074001502841c0280c800341801c441807000038052a6216000f440e1600c001c60040d01a65100104a68480107030324200c0c3e803030300720110f0103104628080c0c0210394062290110340403158008090440c4c002c5507103030a10762081d84811070701285d2040054000c811310501c115030b407130601c0160241d2242041c0d014081d4952050300118001d52041140c1c0c030700000000380150450f4a100282d00d240000600c0c2e004c0504044501c201442c800d40b01e0f5034080d140c001e00c01c101a20259034042000c51101c80e035a40000300c0c28891641001c00c0042c0001d0303480c040703030000f0f83e000c003014120b01111580c41000c01c1000c095000040400c21200c0c1d07a04e42d4454941c62780e80100b050001240e1098103050103110701041043c0300f1078465590001d503580c43c0031180003081c449981c00080c1d40301c513501122001742140d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 745444991 1250 745443741 745443793
    0x80304090506010e031005100e180c011119111005031f05130902040b1009050103110403050d1209080d1a2211040302030303071e0206090c10050c 64
    0x103040c940000c915500c5080c50130b2135820700030b00801c1d510741e20840800007408040e04401030a040b043d0007048061031590054050f9200303a00b4950510200f4130300c141001501c40210b41041051071000a5a0500181452442c40301c9080802040c41c04d1502507021001c1c02e1030141c110315504055842c89400c0800f85106030003903542008140308004a09401420a0188590060b601c1c240101ca40d0a50780c04902c80d103101510008128000100040c9404c0030240315400003408035500f0310880d64140500748e09841c401e07078841e081c41e0540e50386648441c0b01101c0001040440d0002c8540060150400f80c070040c2c01c070300e2942d80c0303001410a04000c2c3c9803014041c019882d50384802c0c45079040c4001505850b0555a02c0d9102940d003c181345401f0700310017955030303001c40020300000c00540e41c240000d500510a50301e0b02c981c540c01611640c1c404020648c0b1180954000c10100801ea80d00480d0005800c2d00c05c50f40505c54400c440760a4501d070040b4201102580b0a00e07007a80d07410044140161680 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 745446241 1250 745444991 745445009
    0xc1b0506061c05030a0e01051c0e0717030d05060127030314120f090f06010902120903070816020d120905120d1b08090d08042105030304111504080304 66
    0x4501d01d0442c804040c40b00c030030052090b44108003200b00b0a2058150280c1500145800c501d0705105040c41c0c840003c40031a4000d41340d554641d03002904070208054001810076a0035a00f58a100488c4680c07640900d401130f081458072800001d80030781c8201064200c0c00c02120135840380e0300b100c40004030449413a020440106041400700000c81c02c0010030350300c90070b840a4001c041c650b41d10841071041d1401400c1c02c110361007041c4c480c0501e40c0c0c003881050f029150526005859022f29810200c0da44006040b800d441d40041280345c0214484108440c220030410301e000d60075110920105205034011000505010b105c038902480f4583d1004e203150031610205c1c1d0711450403995980080e01c892860304a10045140f6200010070710b0715030648202c0183c0156001d90800c0385002c0402d400c0380c1041c000301c4010000040c2480b081c0400081c41d01100015441000012126a03d181d541d100140018011503200d00200d07070765a0710704014281d00354420394416240c5590302c1e80ca941c2e0b608140503c40003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 745447491 1250 745446241 745446259
    0x21e0d0605030706030b0f19090c0e04060906120609021c150b030613110a090c020f0d05090a0302010c241e050f010308030403090911220e01090c1b050606 68
    0x2074240309001c0c0d00420031000b042103010221140421238840e080c84500365000700e80c004000b40360308062190f83d01e4403031940c0b20325240044440821040b50070581190700d41514008040c0302052482075107600c25580440c0001303411030303a0700008595404048140004d0082032105804000c07083c8240000c0300854002481590024410181c48450480b95503440c08145035801c0007042000704024107203800030f00210012516240e081060704e00380741406000d0b030310040484041c25070810000381351501d14682070b402c101603840021101030751840064108080400c105090024075007100c100915800000342d074078802c03c420000070346420344800b1068030712860b4a00c07944085004251080d800410410190384c2950307030f4040f0541026106030b00708a106140801d84c1039aa21984043d00701c488540ca807191074890241c500c01044c10404040c0a00c01c400c00c1004032000c0b0009410b4960782c09003c15100c011100444080f0380e01000140803807081e02001e0140403012404a0040e6020b440010f8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 745448741 1250 745447491 745447499
    0x170d0f1116080c010e030309010507020f040203072007060f1103120f061815010f30050703020c100e150f090d1103160c080a1a09070602030d021e0d06050307 69
    0xb817154550968941c03d60010003c180b9150b20900c0140b241904c0108408554020000031904a0b0412121103000c180540045100403513411800303c4001c000100404003942003d40041503040e505c07007a00140101d040807084104ca0501c265150390748500f000b80b0391483c00300100c000261050700e02d07074054528001e08480310702d80030755107034840d864415418802e450040011103007031021154410800084524250030307100d8a210303444a10310304800e49524203114401d85d100f12100074000320f05241c410802c0c1008480d02050a00c1240380b0410b0003d0011460040302e41020030700585103c50a402d0401c0088800c40d40099a02520307900c1d0850f04103000b40201555030000103800c21256500078018810212007103148540014811140c0c8485203030744042041c0b91100e004d004403400b1581140300c9503643c452048840c1c0c01400134005005003883c060029444c0d114900f0f0401c9010b80028070a40900c2e480102908448160519950303a080c0710458a40200018011584030b80542c240c001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 745449991 1250 745448741 745448747
    0x30a1b0b10090e010b061204020a03050a12080c18130618020325090b030a15030605061e0a0b030c192006060604170c0622170d0f1116080c01 62
    0x5d0b90200e02805051402140ca04844450600204101e074070102c05031011000400c14032100315420311808031443e414452500140000c00000e069031480b00c001e02c0308100326428201c030f00003180b00544540c2400d02c8100c0c0d10402918064102403c4030030a00c8002c805006d032603009600c5400c5050360b074100800031601c600c9a0580100e4198005201400301303000c540c8420b4019600829201e40000d80d0303c1072400308849000440e0f01c1503a0050b960001c0105900b0881d04622035020000c41d01e030805021840021030701c41082c0a0352040c100c001c000a101c0b10740003411500170310070202d41d00010091810b0001d151140c100c1c2c07100032001402741481000180050000d0113504001c00483c00c0a051402e02800d12803000300e9032035a80b16008010465131646402000841c1d00ca040200c54807078030b1611140c81c05456840301c2c018484c844107013181e210001c00c440c04280d50f103240003c100001c8a00c02c5840c440004101c0c10036005510301000704816500000d01140c005000b903446000d0a0720040d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 745451241 1250 745449991 745450001
    0x204030b010b030c0c0a110f10090b0c03041a1c0b01020c0d0609171308030c06151908030703080f090a060c03020409111b0609030a1b0b10090e01 64
    0x2082404400c00502c4801c1ca00381c0034552180001006500300000011211b103044021401500d0381c10411541c1120f41c00c0c09002880c1c03075081640e04901400344100000c0c41e0f070030030748651007000b240450a512140810b01c1250001e1008034819001e10754804440c1d00141d0003202c5c501c2c2c0000c84076030b28410485145c02000608041600034002482065040c031607501c04043c0d04070b0310b55aa64101c8400a42d12554110184c000d203024a40c441e80039040c1404180419000f0403003940c000d010071203402c000054900c0c0d10100106070b505084444070013190302c580b0018003180043d40700784d4010840c8680040a0031200340a07607118102500c0c4c1d000c0341c4101740c0040e1001010342e00100107400204540384c004040300f0140e45001071030290b42c0c0148800300d0706602c011560018000841024031140800001e10a680c1800606000e050000001c1e94900c00c3e04028000d1103102c0500360981d5402480c01c849003a0031041e1403105241940b00a01300210713601507444036501c0e241010700408014072603 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 745452491 1250 745451241 745451243
    0x9010807020a0314090a15020c0111010216260711040b0d080706051f080c030c010806091308070204020703110d090b040e09100624080c0702120a0227010504020403 72
    0x20310b80314140c24030010000343c0c0c01100143e0304481c8140001945921f07402c8030084081155000d00055041c4100042960a140e000302d8810707801404202c4c1111300e0340b0442030000d6407005540c140051444101850014100d80c903814600d0040303626018040c0e1007550740200d103012a01005600140030070044000f02440c80609040d01c1400b403a4005030f2103910180c1c020301c4801984482c8100c020449403ca48a038100d003c05030060204101241020007400041709001d0a0030781c4185400000310340551070040003088041c0f00c0200031424026100b08494104d50050800d5585403810b060140480400b604101e603248105228030f02000d2041364614260f81112448505d01031421b00400001c10f005001c0003901e000b82e860a801900e81e0f8031507040109038941400319040450390ba40a803049040d08280c090181c80400c00012072008012135241d0f507070440b040102c0d54000e541007440c1030440c144c0290460303018500c050b03204440402c1c030f109180c100c0462080b1a81c9802c03d02c4164015440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 745453741 1250 745452491 745452497
    0xe01060b0a1b0204051503100513030f030207050307060b0f030607390f120504210303180b01090e0a120309140a0b0703240308092409010807020a03 65
    0xc108001c0c1d21410442038500ca00001a02c0b01003041c0e00000c04071482a01d01010b40c0c0c50040d02074185040a111081c160351403190204074034603240300700700c030f4954260030020b0801c08512280d56149020350305884001d5080000c40b0340700c2c8502d1904038010a640d81c81c541c45948540413a5002e0b150001d41d0a20a085590355944444d0780c0f444003944442075028210303d00114a51141e400c030b1081c2c0300031041513000702001c0e00d8401c01c0b070070040b17000342c0c40458240030000100320038031400c41110442416039030300c6018803142e0442c0d428124020321488413100e507101030080b10b250034404618070490681d104240c0070040d00110103c0e1682e5041c0e241401051040301e00109800030f402580aa09802d00660709030700c191000c4c0d0030850805040030012510883c5e0401407003492641440b84644001c280c1c2e01480e85210702c13843e4070740c1c9210207100040c4100030000f071401281e1202040d0000c81a007007001d0b000f00c142c00c000603d60f107401240e001c90004408200240b00071b8800242440e030700c0d405032 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 745454991 1250 745453741 745453747
    0x102040e0105011209020328080c0312060a030b04020d0311010c030b1003060e0a0c0e190e060a03030503151912020411070c060302090d0209010801050f011e05130e01020316030e01060b 81
    0xb600c0c1d8100c014002c403401c0c039440c0308c4050b02c0b012a00444c01040350950b2040615540d0505910b203030540c00000d03142c980120b06004041c0001a06c5142694005404550108800c03050b850115401403c000d0005419401d0662142045403d0b070410302024904543c82000c08552030300c100c089278507600c151010b003481000410b80513038541d8040d1142c0c00041c03800b0b540150005010548038940903911003416001804100302500b61022820b8200740100c42e0002d9192864400800d43d00010b440c0c81004850190320f050181c0d510704480100c0061540b800d03185640d180e4884040a216290690046d400c029109400500007800c07108400d5100e445418814181030041300250456031000350401401c0c0c410b500581d8603010320a00030540100040754900d0610038281c28800180c0c40500c0031940500c999164201c48401b0500f5030ba0281c865240000100f600440603108400c070003001035200000784030420024000ca0201604103841c24081420f014540a0032075100e03110728030141e4014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 745456241 1250 745454991 745455013
    0x604150308121f061202130b070b01060f0c1101090f0602010e010f090812280903410d050903091908030703030f1d0601090b0108101203110102040e01050112090203 72
    0x40c00c0e120300d807600ea469006042287c80c45441420307a040fa0040384c0040317808100b201c10030100e450324034054101454500041c44c40301c0c0f07014009180c0500020540008141030070482e910030008800142402041102001c0e91100080d000782901b030168161942859580c03001c0a010f80202000030340d011a40f1854201c800c42c40c0d100c03426028001c4d004030702003000311004405840c0c81d00340041550120004401202c1c3c90050408c078804c08450390710048200b002030b050400c1c4400c6508034402c03150b46494002c400700f4541e0300e9116114081c00c5051078071040c00800c1400201400c0d5408054454030b035039070981c06004003085010310030350718954020031404001038032030b4114a1324900c54803004645041d040d29202031010703200b4001c60745a4050001000000d0b0b00b0300030f5081c9820282800082d608003040d0b03040d4440c4d010301441c1d1009600c0410101098481c010b001520040b43e00215140d80c0ca40558a07505202803140c00c1c0011490001c10200081c10f02c54442020ba00900503e01c0041b5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 745457491 1250 745456241 745456247
    0xf0c170a0914030706020a11150c0c030f161a100603110708070506070905010512011a0c160509010b04080c010807020c0307060c0c0f0503150604150308121f06 70
    0x20150445400c2401112403000c03000030400741c04200d100380d00141c1c0747e054240b0020100300380c18050f00c040342d008003080d49880482e0600d558110f40c1c0c408440381d40d0240c000d40c1c01e03d10310484400d0f00e4042e00006413a0310050030206400b502c0c52141c05031041c0161044c042500502056461505400d038144d81000841d00a600199000500b400d90324207246581c0c41d081d0b81078110100c00e031020781103981000400d0782e1003070303401025003003d0801d6810034903103140c00a030080d0f050141c0011450000721043d1195030440c15543c0200381741d01206c1c0c2e406000100c10701c8803038961040c24004c50720030001040209040b405e640a1b2a000350003400006019401198034000c06403284041d8001c800b40c18501c0e440501c0a00003800154032040418501ea01d441c1d04132240c2503001105049030204140001e90300410314481602c10203903452f02c19195140013030010003007980e4120080a070001c1c0003040240010182c0310101d207030b004522084d600e0b1594400000c04055850b006040081024840c7e140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 745458741 1250 745457491 745457501
    0xb0c030403020106050925030e15091204080a0c0b07080304020f121b0f0d030905190f0f0914070f1202070507090501030213020a050405010c0f0c090f0c170a 69
    0x1000340b0010986556540c08183c0c4d00c001030f244c3c800503618611502070704503030718004d4409a005a00e0308014001801004548031224045616000c0f110500498041c00003003141282d4000f46c401f00d25599a65900c142e940c0341c882845c11a4054120400042c406030140d0513074220740d8019070440c0c42d6681307590821072582c110340140c40d8440340400358034034800410802740700545a0076022017140900d14003000204109031205500c00c1c490074070b92400080c0d20100d15030403104c09441c0041e000e0941c0c0300d01d440400e05c58006807040c5103e04000518400b621100300121401c03988100014540d07507100c000c0a100c1121140c01041380c6a1710f0880342c03441440d00c401c6844c080c103001803c0c400141d8030700342001d03010340c48001040c0c3c5920040c82503180019840e15401d05203c3c003146030004d50380014000e4007652207a54144481c170518841404291031408128541c80a0100c4420303440318031140060284404501901d031030003420400c890700498444a044201c00c0485555075110203100001d00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 745459991 1250 745458741 745458743
    0x1c0e070f0e072a0b04030201051e0103021e0d0807052404050a0b131e17030702060f06041409151f0b0c0a0b09060915012409050a0b0d1401030b0c0304 66
    0x82c0010380501c003060f000c413078040c000c078880c4c0e0010505050070150015a44800c010a0036405089001080140c4e2410401d01030045113041c024100704118000610344824104082c000401c00560002042804180344064070346200c40808540c2006402d03642100c01110014825030100903900041034903454582d03405203180c031180f040c207441903a40707107044040c200c0d510750071100381c2110070308010214690400300200200e006045150020000b99121805021304003050b810380046031150b1a0754018048941400030000300340d0500d1109143d50304030350840b10301512060710201d61468103003114080c00d2804500c004070050300341011000241d02941401106208510f4004001103d0281d5544210b48240141c1405e10749140c145042050500d030741c3e40040408001840483c007500a05c500717002c003d43c140c0700080c03110401900c1c1d045d415040554841c0500f0800141c82c0c1091006140070b41c02c00c40103000501400d110110301031020700000300503560303040014111204603c0a50f03401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 745461241 1250 745459991 745460057
    0x7151802040e070b0408150a053102060309060a0e0714090a060f08030415260a0923100506030c09090c0405182505061c0e070f0e07 58
    0x8130ba07030300c00261159105501500303450b0007408800720102c86e0400b402c0d40c484c0703071803009104501d000c560a10a10303124041302051407038544002950188850f000a0855a003d44225502c1c01d0004040d40c0d12581212034450705428405540701480005c02e19004132030022442c588001001000c001040300000d095111555584100040c82d20006403654014815038010310740c1c0780c1c10503090340c0200758914040401d100e903860f400203500f81c6110106004500309508401c3c59251400c050300603260140024020014280e0560b00c18501444100005c540000459401d910410151020344004591803030381500440c280c3d040d02e0808483d900d03801142c40b41540c588098500c001011200e054440c1007407900c04100300841c010301001580c10210071a80101a90011404906820491401220300440d40401c6024a50310a201040300b17040b05003205003c1889060f641310765a600d0384c841c58000c8039a022000500f0b0800c0309400740036803101e65903990041440d034038030803e10f100310b459800d40b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 745462491 1250 745461241 745461253
    0x111b03060c1b01020a05071e080307111c030c1709060c0304021c060507030e0303250306030209010308031605040b0406030207080c010923010c0c020f03010605060f07151802040e 78
    0xc0c2e82c081c40200041d44194684076220710150502d0850f00c0c049810440d0116244115000490000d60a4a42c4204540303080c0c0d00150300420a01c0c182016014138246105450342c0c40c08016030150040c046554495a40e8000314070a15220100001c080d5444034a42e0885000325a201100d04010b42c1d00500151a44581502004140360b03401d44000b015a030b41a9524180b220301c2d5458000c050300d0300700143c010b5080d818802a003c400c000c01d4403c010380d103d0b06803c01c02002d4003d400100003507800600c503078441d681d2818030050310342c42110064820800d1140802c81c8034014030a0324103035a500380340c1070b007400d04018041e03009502c1950240c0c0c00074400d05c00c5150002c424001d060b01c407841003050001441303c3c00524641e121140c80a406c02d0790516450050860317010000390000c0c0d8040350b40c1c1100c00088408a4014240da0300100d410180c0060f40c07843c07810060000b003000700d03c03540003000c07680d00703038541c075802c84406034031440c81101e0b562a200b000d0310f85504205041c94840041d644 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 745463741 1250 745462491 745462537
    0x61c11060903060408040f06090501080703050a2403110a0f120c150c0302010c0906140702060c01110a0f08070e0424091d0102070b0c1c0c111b03060c 66
    0x4a0550200c03801c69100000007801d002c1140301f40001b07401031115061000303034541024006882a00014040e0b0201990384000621a482d1074003d1411142c0d0260440340030440710b1041e240036030140c00192009101d018100902c0d0400c4000306d005c13aa0441c1c0f103454501e0070500d4a000e0982d21030710640f081d0b40880f0b400724240400c1041400000003e403503400600c800b0345030282c29100c00c0400e01084c030404140404c241904000207015100000d01100d598440c0da00c00a10f860151481d180b410b50720b131600c600385000309240103250100094666601d91074a140c0200c3d640e00c4200c91040002d01d501488403498141604064640190f01000340d2141c801c1c0102d2881e13000865000d100001d03154001c10004000b03080c0c4c084014a05038009516207505515500304460780580900c2c6520700c00180710161400f20491060003819040c000e00c1840c0b604100106081d103140031140355400f4000e95003400075540020300c0c8248501602034802ca948441e6400166000f00702202001c0e00341c403c002c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 745464991 1250 745463741 745463743
    0x10f02011415010f020d021009140706020102030f090109080a0807050702120c0103151505070507120c05090108010c140c0118060914061005040203060a03020603041109061c11060903 80
    0x2502c20980c00d45103582002c1c81c0c5000404403082c0724859010741d0801100e4003a1079034046440c4184440e0640d01040c088103604e000c240d81c3c88882200946401240360108806a041d0003e40c001c03080c0c03402c031641d40d0702c1d01680e0364201c5d125140c009010f10002c12000d41c0c0c403402071502c40d620021070304025050a81940100f010b1107108181d0040c0307034010620301d0780f4542c0c00d44a6410b0075150180414500c1c7d090501071360f8001c0c2440a050180300340800c210080000c1001070f200a030038440f410303144461b414900029640b481340a140c0c861080da40012070b01050501c40c110103030025680310210300c2905d05005a01351302c500d16107400b5540b03952828801012030302c3d0004903e031007400c00044461880c180400c00403079500590210340c1248080c46948a183d0749804199082143e00607070f247c807600d0004144003140d52000b5041a004070420003480201c0036010b01a000965142ca40c959520040001c46500e9450107070441c40b000c8103040218010742180010490003601d444d242c0380c0004002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 745466241 1250 745464991 745465031
    0x30f030402010f2c12011a0d1b270b0d0303050604020c1509160b0a110c040c0309060b040b060403060b04090605090706020d0903020a0b1c0c0c060506060414010f0201 73
    0x903e204a0850f104c410710704042c109040034081d050001c001c84e000d202a105100c07404143c02030b105070f440344183d00038000b42450501d64005100076541c44155034ac00d4608400d00708200a4524002c13003000005000414050489012402481d0910f80c8040340d070180d0041034050705094009500707202c2c1210480d003c0001111b40010301c2c002d2175003458030010091614080041c00c000c14885054108003c485610a588000d429410941c060070845500540f400010041650b84a810700700b400c0d040d90303015404071031214041d0304248049180c080500087c0c82c0055016034020320200302c100041602607110141c881030003000411903440d19101d410940310155159a030b550042c806c200422501049942510202800e10300002071441d0001000c1140c00e00c2071700800c4c1c4001501c85007456000e003898124034070400c010004003202c044010104240e48004a5266151034085095468404160781c102c40c14010035480c05c42c0d40f41d004440305000c103c0c0d000150340d240d84c0150f4047c0750302610 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 745467491 1250 745466241 745466297
    0x32307030218060903070e04031e1e09060e040b040e03131d01030809100309141605010914010e0109240e010f02070905060f04020304140f030f030402010f 68
    0x3000d40c540202034003441c454060900824483c0e1002c008101c0d4507140440c00c0c1d42194903603000d4500581c1c2d203080540f00642c021110310200e0b191b01200c0079030150001d010340c0307030049000d051045111030000159010701a030b014000101d140400101d039035144c01c0e00f142e040004007400200d0010130b0301d40c1482c03450b0400724440b1031042da2442c0620004094203010380c08009400e03984025545140c07610002482008011801b484500d400340c20794138001d402c89001250b0084090400d0850040302645500c10b015070040c4542010b840066158414001d000a4401100d507541ca08146d040054604480403400b40341032018604000400d0b200724284a003500382c0608126030110049503000b00811400703800e1505214840f20b0280d510f50f0f0005008080e00c1c01d0b8040052162154000285c0d0713a200c0c0d041081d8454000010007080003004100d0103030000c0384100300e80c519980c420040b43c4a015000c0041d840c45020310001740558400c9001c0e1140020b14141001c01c02e04a03c1203007a50307030340040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 745468741 1250 745467491 745467497
    0xb0607022803140f010b0d1104090f020306090a030f14031602070506031305010606030c0519050904020c0307020312090d0627060e0d030b0d080d0b09010e3301032307 73
    0x2600c0e650215083c0a81b0141c580304503010502c40c801c0b075407204421f0070b80f07075140c1d0f000e540d40f40202c0b410862421400b4408a800808840940c0703407079894140c1e00c565001c0100c00161000340d00c0004c0303030b0080100070808150610300500319990f50345469034969403480124110700c14080c0001d041c0d00d8850086014050600400c081112070f4107000d425075203241d204100305481c140e021100d01c0d9021065580e1200200b90f01e11403940009000c4406000d00140035a0080c0b0008064074608000802003025502c250300366089140484402002c9000d6405801c2c2c010015a6038440012410341c02999001003261802030a500200707038a28018004203002c03107407140d8540e14040c1890701004640341c52440303443c007440720304541c5021811b00482007500400a44011881029a00c1150422540d10502803d42080340da526030140740316850907940713006100c6180c0f01084200a01e80ea451007800000c02500c1120034503c40110000e0040c5002840e0642c0d0681c01c06000010101d9098040e03d0196 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 745469991 1250 745468741 745468753
    0x803070506070516020f0307030c1e12050c0d05150703050a140105060906070206091201140c120135010e100b03071a1c050a0b060702280314 62
    0x114005103020000b5000c02c00b0300c2414407500607520056a030342c689156054410304104041640402d01d0020103030030050581c10080b0000c0b560b0341c4981140402c1e103050010850245680d4005d0203c241003444001e811074011185201d000d0402d80a0318460a11607000c96145c02232a102600e8912070a50305040029100c8051100781c503102d002e0005c58581c481180060b5514200c0046e0161241780b900c5c078040d21740414104195641c0340241c0d80d41c403c0141c000303143c6204c26128140200285003940c0301380044d013004030300225100010759650b0b20703048414160342c0c0d081850031019500d85e91260114100c1c528042c40040c1e209a400a078003804d00d8002042107071200d140d4906041d564074031070744441d25002e40c46040c0e640000310718080746c1c894604140c403004d03001c001b01141e2213000320f480c91070342007664034030450400365000b2845031904d52401c018035108203042210b40e1084940107075014050b540303045165100006801c400d1104000b40580d010781e2507980450403400c0a05584940d0044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 745471241 1250 745469991 745469993
    0x1e010504110103050609040210141908090d1209060f091b08030a090e070e032e0219030b130606200102070309090e0304180209150a050f030a0207020901080307 70
    0x40c0c0200c1c440c01c802400e05010710f141600200f50038480c0280064401c0350b80c241c90522090060540006030b406903010745076101f150030b2409140c003031600386520000b1002000694141404140f8035a24200c954441d40301008011580b8040c04e8000000d40741250390b0100003117206210700c980d1340c0f010301c1070780b010702807424801485003206580e82c40200d10380c10421004000351f44c0715240a040d6202035103130128030784800a04544841800e02e0860b098071034403804200604808445d501d15035142140c045038108150200c000b070380100d0011540d01038090a403640100e0080c1c00880001c0e0018040c20104e00514171801d040d10030541c84180414803188440100110135800b05810400030f00081d842d10750140d900500070105403007402c3c9a140d8a0b04403610000c01841140d0042031500c0c4e0000040180c020058004e50280d0449803040c3c03940c1142e150740814100c10b980c5511441d403601800c143c910150101c09900050180141681c02c0000d0320040c1c0c0e9059545000e02148030003180c0310521 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 745472491 1250 745471241 745471253
    0xa0b13021c0f0501050f011115070c050601050d030516030c021e09011a04061d060d0518120d0906090f0303021e040509010512100501080f0706030501080601030f051e010504 76
    0x710300982c880e142c10720005001d56121090040d445100070f1074055185c21980d0392070b82c01e01c1128080c5440d604406401d006c401940715080081c624000c009440441c0d0340c0342c0800202d1218048020089442400f8000c01c216042d0007410506003b0b040424103000c00b030b40003500d07950344640360b0083c9a2481081c88913078240284c2d0b41d0b01520b05885032022300c4e540030620106502440c4902000c205501c40f42038811100c140144a4465015140300d8a0f45030910404010306011120810010003025804200d4900007841e071400800d04039040745800d01282040c0040c020035841034412646403071038203000503500c42880c141c00d0301a640060321856112900001c2401c02801d401d41000305000500441c0c1d9100c80040c115039040f01c0c81082000361040e01d905142c5036100c03020742c051501c400081d03582d202140e01c4a80ca030044054801068442409034100c035400c1c0140c19045d40319200500020346100f8207083c05c58010b00450b4907040218564030414103042d420000965100d40c240410059 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 745473741 1250 745472491 745472501
    0xd0e03220f0e0402060412080306101b080d02130e01060801120507230603150306010b0f030a05040303140405240403020303041506081203040510050f0a0b13021c 71
    0x80da000c0c0c100c140c1c075081d400c40504916000710b20040c4030440100d4110f5480100715801031002000c624011505401c00c03006507042152a01d000d0303190a1500001700744074201d01078921241d90000070400c0c0c6140c550b80400d40011807882e0440d43d081108507070001c0740d0300c1d103c40200700880c0440815810000002c0c11000b06070312031100080c04117030204c00140003181182c151000112000100c0882481640d81c507640002801c4d0003071800414800749200c03004001c80d100006504503004c07642c1c0d8000c25111841a6402d504040c0424408900400c0d61904101d8216000e03280100740209900c903140d1010b0003e0350100ca070782d0320035200304440e080c152649180307e6540e012340615510317150302c010791603101c003d00080820041751410740220200b940000082c001c20012207980c2c2000b0f40240805500c25a010343c1c651103120103c140d041c1700d5000b03c1d403040b2104c00250300c541d1507444007540505040052164044802e44103042e030f4003128406050004104081003209042000e0094111a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 745474991 1250 745473741 745473787
    0x30507050604061b03140c0f0105010b0309070504051b040f140409030c0308060112050114012d0c0303140c071e0b130629011e080402060a050d0e03 65
    0x1500c01d0000300f0101c0d412625900d0020200c0c070b0030f0903458000e4035040301d002420703210802d1105004100301c0812040001c4160038095400c008000b240d80b215008070503030204484456659000190522590400e508255000301e0054045510641100f4142c0c1c0550442c0d01300003280b00f0040b07010090303200185555012403105850800c03401c022078130b00900c05600b0300c00c0542440103d50104146c4c1c1d10642c0d1031000740319591020410755031100e08500740c1111114109000420122000c81c0c01996529413030078214001501030100d403403001080d90700500c140d405409050760b554441c081d506000175054400c54803c800256a15803e1030401248031120f0782c80a06071100b848088005000e03400503d13000b80c800e0309901c1d0100c0b414507054010341806074603241140401c010310491101c0c182000d0389490000d80b2608210340d56410604c1054020000160025880340046005814400020b200041151406a240210503071301c10303081c1e441c0d4a640074101d62000030700e40608513941e90400c40320 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 745476241 1250 745474991 745474999
    0x171b3d0503090607180b2506022109030a14070c060c2108060402031008070801090308011a040b1b0f06040c090c0e0f1c0602090315060d030f03111303050705 69
    0xc404000400e0707058055028800b0668000507c0904500c0d01c4541c40e0807880d150815552100b0b41842d041000c1c0d009240c12070000c032480c1c04130014046030906410b20a95103c4025818000464011a80c0b0b50180c06003e030080c0e020800034010880440f4844081c010503114001c010241345451003e8040c0309075080d280302051181c40c010641d11641054020741d0884026860b23856131003e14851030281d500280700e900c03542000003885041074010019890003510740c002d96a0740d400030080f04070503189000208010400050058200c01d2001c0d0115400250300804081c0700d40b80050718180079403040c00c600d82d0010042004000000110704042d0a1010b402d00c034109490102420200980c00d07020f02c50802088141000c0e282c001d04680b5100f0441102094040141840d400a51003144954068041c025241c1e464031030201c8180d000d04805444120614615201203c4101d6481c001c40109500c03420310f2080301d000348003d00380c000801419080d0880c030b1890a5468032010754052401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 745477491 1250 745476241 745476257
    0x102070b0f0702120709090c0503060c0c03070f1b03060e0c010306080c01110f030a05070c060c080306120c0a060215060a030203060705070302030c0106171b3d0503090607 75
    0x30064007a102c03070300c1e81a602c071040301200800741800c0c040b01e508405204c0b4500300c05101840b07441d00002007282d10507030985d0041e8480705c0c80c00401d4800c404800d59140e00801411000404106402c450a40a0a61604024500e4000c0c1d4030464a41d801900c1244e00d4089081e003851090061010084c401d0034204079541c070340802e49031140802078400c0c1c140001404c54034501541440030083c002407460541380d4600e0360480c083e00076000120251081d0084810104900c0d0082c401c061042e0380142e00a8159a22a0b04100d0012540d81611021303024100c0c8810680e220340d01900c003c4d002e1a00034000790582c1215001542400a0000c0c1c0f00d020540780c02c00260700c0100d0aa44c004019161840c1c2c0ea00107400c06918502c146001d88105603c3d03c0000189086100601000c074004002900e44014205494048181c541c6c003c4a40c04005002d4101c0190403a0403000e04144000c441c25120412055201584442c010f00101c0801c03000008c0203001340c4244056540301a6034206600 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 745478741 1250 745477491 745477507
    0x903010b010c200d05030301030f1203052a090d06061701090f060b0a0e0408030601080f06102328260406091b06180b0f030a0b0a030b060102070b 64
    0x102501c02000c010000d40143e560101caa5200c9003014000c16411400f101d0352940c0d245001c0005c40b0707101005031030300c000751160300c010303e80302c0c2c000c642c080c840c85680e000185040340c0500690f0603006000300a81401080242c2041e207480c9049140103010703400006800c0d1500c20340c10090400813140b6030807640740074090320000d112104071550158006100060940c10400840c2840e0317059004002c245040c1403c02082100900081d40324000a80e1182c01c0360f03ca0b007646c1110b0315415030382550300407040341d0703c443c49520403810491030030030303601c0d1882001040d038070030806a611040c070402e0b00d090810f140703d402441141030383e000c56140785070042c0f100944030402ca40c0c61181c1d80c1e4802d640040b04c00803600703010b41c07134101c000800e4200d126650003800c3c0c030740c4200500400e40b0036800440c880b5018103907094201a030480071100c450b000c9511b45107500c0304000640e400149540442d039641c0192482a4a0304080030703000d10310038202004207040081c000380c40c0a00a42c0300400010701040f1a603 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 745479991 1250 745478741 745478753
    0xd1421161e05100b030d0f0c0f0204020f130329010b0d110a02030702010e0102010c121e020304051b090c07080a140f040f12031707050702150903010b010c 68
    0x614403904030120340100d2026003000790704204040d0001d003a40c07090303500700880304000c0c0d44109800c2e1021411210018540102600d420380c03441d081034041210320b0f00883c0812512042c0b406640d00c01880103103000c943c04601e0101d501703c445e11500305910448180b0401403a145028484c050540c004c03555025140c1b01c1424140050045190030320300801c1310000c07017040da080b07036465001452a45031a03030b811100080d500d801254040c0c0c0001c11800c14181d080d401131088044c80040e940c0c17800981d5480c1041d100c0507054043d240d9118440707500d074620700382141d03202841c040e0340310708060444c0c6140d2128400c4080b2900c812284103607089400d000d40711101c90110342440ea40054450785a50314103400f0384840a0160445041c0e1000103110702681c0110342c000d000b940c002d44451507281d5280c1c0e00e13120032100010b0005011480700d180320b01001d6030300e070081da90145961074030a191202d56808610311603265030b02840003200202e046030b02c0d46802e0040703204010302860b018601c4100381d110f40b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 745481241 1250 745479991 745480027
    0x301060807080705310608010f1a040504030f030e1005010f050114041824061206060306050d022110050106090509040203150601020316081801050304030801050f0d1421 74
    0x407210f0500b0a880c0d010540700680101c1b00414000001f0005039035079004410141040450a5111021047c8800a02d20b0140311b2507006e2505540d402051442c0380300103074010519000040b44907c0f0741d0204802560300360140b030b40604620380c400c6c84010300d08400585034580d0f2850171451000300b404280300d9124100107994030159070110114481d83d80000ca0700c440f070042e03100a800c1c0041d1603c0031542d07035044444800042c40d007003070400181e60380c1d10b4110200e0301c07140100ba80c0550a080310401500e8117481d24003501046004501c600b401c141c00d007a00d021250403881ca40e0305d4540d00100101900200398000500d001d5072452014a883d90003c1c0d1a000040c1d243d003d102c0d25400411000d910070805c0e58540c20702e010758120440e07001c1c00c0c00d00590308600b6402c0e00046252090030302d5544500103403401a0340c16100c1c43c0c0d46074200010002c0c10360240240d40e4006e40075649072000f10b01c0200000020040c04c202403d00007a02d9034944c1400c0201a2084a142030100074040c140c900800e20 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 745482491 1250 745481241 745481299
    0xd1b060305062d01141204151a2106010602010e0c010e030a06150519050307081603060e0328031a130218030a030206070e1f0c030e0301060807080705 66
    0x540d100700c045001a41d0b5600c1703260181818100200f100207403c011503004c42e00650180f0280814140302424031025200e05842e030030003c1c0e0441c103a86a05091800d0144003030003018840d4421102c089174894a0b10000742d02c031800503911044c83d14131301c1c5c20601030509080d40a1030640960000b941c040f07130b6200403404000b06159907071110441250030980307480300640001404a010211140c5005010101034094a0f110b030003416030004064100113203e41114461144d0500310074615122140140300406078008140070030071110b80c2d43c058040b054512030b10440e000b880c03600180c0400400701d0381d904148080b42c0b00d10010184403503030365000c0b080e084000c1c1100940e1300c0030034401035040e07181c074003401e65094800c4492040c1010b8003c5001442004a5500c0301b0004503418100701c000042c000d11510403d003007801c80c1c2c030300b10710410324105064084d0a20213800b109000c0402d084503560341c004a0b298000d568248040c240600800c401008200c613810f030040340c0f4000359034081d000e8500e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 745483741 1250 745482491 745482559
    0x14011e03020d150e16080601080d0c03110703060f0219032016050f03190302040506090105070302010212011e06020321040f08070602030612030a08150d1b06030506 72
    0x1c010750700183c0350422250850304000342d41003065403000b08035800c0424081c841c0517014040011411007030020f00f084510420755114071000da0692425a0388401c8414820302d14014450042301041d9640a101d41001c2c1c081c0c40182d035291364480320000c1752081001e61082500f0001c541580b0888140c0d002600103101e00500e555004d041030340c0044104000008045010300c42c1d0b0311401c68404009000012240340f8001d03998050750300c08904920940c00765541c002c80c140150400365104d580a400003d20034000189031071030003442281849001d034801d440c211100c6a80704250109511300310001c1c0800e0005505050140c000d8500d51450004101e5161b00500d00040c2402144810700d66001d400072200d0340d0300c6d129801c068000c0e40c000c0341c40c80d001d080b42d070800405000001080b184c80e1100ba9844442c26110241fa402d0400304101082d54440803a07021400495601f000880c1089440c020a1841070318010000e030681e2802016144203006220700c0415030100c00e41c1003000402151 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 745484991 1250 745483741 745483763
    0x60203191e0e04020c060a050403030608070f09020d020c10060314070f0b030601051c052202010215060402090411030a0f02070803041106070807050c0901090c05090405090703050114011e03020d 85
    0x40e0102d0001d010b401601c81e00d40c4101b82c180308050029501190050307000340d81c180449500c90126603a074100324480c204009010550800112480d5406040c0c104480c00c1d000d40b810030403010781813520280344900090540d903514100108a14400031064414800d40900304480c504840d03034801921a00c501c813858040040050680d030310403403c85040302d00c10b51300c0c80d00c200303034949040d03004050484104884010044000012181030f500702c810301d0b5816401008410264080c9005954001e0002a04280c0901024a40341d40300d01a28a00f01584900c041c1c4a28100e00c1c00b0003521034284454540c5841003244c900410603001c2240c1e4400c0e008504a00c0c803641c2c040109005109200000d06404008038100c02000004031b41690016011204603142c1d9883d130780c1440440d1102500103020850400842103181807a81102d070340400010190b8503d01d0f502d03140e075800e40b1200b0040102e6200c2c1c1000521070886100261444500e076624030541c068250b90100704503800c0341c0b5001e840035000c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 745486241 1250 745484991 745485017
    0xa03060e10150f06020105060f0d0311061f0e0c04050d0503121003050d020f030a0e0f0a1403060703110703080a0b130b15091809030c07060203191e 65
    0x40010440800d00c001c420404000780b42d100c140303000300e64040d0740700c1d411003014002002c0d4414000e5502508004107001d016401d244c04000002c00a504d0881c10f0103006442049540001e00c400c2d44610300c62609031303d4240d002441c040364007140f0f411008500d02d00000340b141c80e002e000182c41c252802a24880b48524a50406901e0343c02038412001d00c20103034030f0402c005058100c14103c00c49204034210f800c417801d0060166100c800c1c0b00c242c3d1520b0307031041c40150b40040c8207800590340700710007425000142c8001e0010030b001207210340140308a4940070241008074102000703c030f940901c280c901040301d003800040402c124400c80038090104000c0002040d112a0103070b115081450004140d1410000480b40c80d601600640007298854016440074030b440081520841da4904402000825401114881a45c6401010b80607160911084c440c910410700c2c1000840050700d10740e00115225503920001c5100b203c041803100003003054117018210712014102400d001110541059200c804803 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 745487491 1250 745486241 745486243
    0x1807030c090e160609050a060302121f0302090a0204051f0c081e070f0b01061403010e0c0f0c1605100f21020f03011809050307030f020a0f11040f0501050a03060e 71
    0x20101022164650903c0080d156411103440c1d03040728000c3d90480b041e240d54000a030200e0158045028003428007100146103141440301806031080244089500c80381c41c0d40200c1c0404208881c0e030481c05034002030078020303481c00240416518010b075034455498a42d45c64020b1103002d0303810004000203800310780c3d044911054039080407036080038645a516204c4c00c0c244440040004c40742540c21003841c42c00400c0b075034425490703138110135500a0000e01d0b50346041d660304400ea200901802e220101401040d00034910380c00201071707200014005082640c9212800011403950781e0040c0d01c5600c0902c11760006940003e100e80300e600341030400c00010400000c0102c047c0c160001601d4032030341300198075a12080700001844c10b80f09403503060380c4030303480b015601c50032101d14001c0540154803e00200780040d00c100c0301c0004100301031040c0c403180e00710f41d91500040c229407030003250100251030404045090901c62002d89030101d210610040d4036000114154860602000c1d0005131100006580064 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 745488741 1250 745487491 745487503
    0x20307090b0a120b0108090703260408060403080105180402040525050406020105182806150305010e010924020f030906061302090307060318050a08031807030c090e 72
    0x241c69001540e42c412000002d02502c41d01d44081e071090301d803100031a200e510410219120b18502401001c010307003075888160003080315442e1810400d519920655003810306034098002414140000e0149060503e070203802c00205800c101d0103451096690314204c01141000d9410a405540004607516890740580310420400c0b10244030307448140f52040c20743e03805401082160b45c1c41c0d00030071213625079070a400c509000d5459000e00c2039108a04151101c7c031410021101c4038410b403143c0303020050f02c1d40c5d200283c13040c41c03105500d42c1d840e900042050103c28041e40e4003000758480208950a502e56512003511003c80c8001c255400c40b0b082c1541806080e8122420554100350440d140d15202c4503c6640c0c80c011101035025030b1200703090307100e41480c90080c1d40318940001e0150031060308241c4124014041c01c200c140c104144291040c0100b0801e000d07850015016240569580c40d24001104560b01d0b03e10070941241c0c41035a0400104103c40d490740309842000c00c0c081072109003024200e14100c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 745489991 1250 745488741 745488749
    0x7030516110103060803070804090c020304090609060e014e06051006080408030106050304061e0b0108011502102a12060b0c0d0f020f0703151a010f0302030709 70
    0x20020300d110300144403480706807a8034190266414421192124000f54807070040303e500400d400e205000c10b002c81c21f2150403000c907021907881100e0801d40c0d100c011100b43c6400c2e0b4001460161390381420302c5110100c00006000d0715440702034040320646903001c252080f182e070031400e802d0304080c610b01c4048030300081c0c5801c0c15085030203000d039400480c1c1015002000d0581d90300200160700f032000a405802105401e200d0b40c0c01c40b035201e06507840d0240642d01e65100400c2260425a41c1212103250100000f00d000354540c44000009c5005850f0000f4281c82010f8109151078203941040d00074269000881103100c0e061460041f40140070340184103141d50065030140c04034603c60f64002c10080d0300c04440c90074221000c5040c00f0dc03541d10500b1080c1c078415521040f80c00d40140150f0700c9034500998442e55002d10900c111a03e01d521001c0203410103c00c0d4104a1b0340002c039150800d00481140141d011070482000080d6010a41c0c10020340100e1050a41806040c1c000c400105114001d090589c018 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 745491241 1250 745489991 745490017
    0x406120c12140105100311070b0613020c0c0a050a0506040302060d0f090510050f0727080106090e0705090105030303040b130206030f040302010e0a080301090908130f0503070801021608070305 84
    0xc1c0b00150a1000040d800740a11070043c6100405001044e119019214090f0002041d091411200b900c030702410301c82c028501a000448500d100b4038210151009100003030003e0003400c0c94131015801c015000d40b0a40c0040e11941c0d04c080140080c1c0e940c0320480382125411200d03150f4807007489100f0f0011741410581104158070303041d147c0781405000300d8040c0b08987c45c20f600700b0056490b901c400d0143c1609075600000102007000038140d804450651540c01d030b55010b0003000d0f4a0b61029210700390368154002e464115240d001981c2040010048003002d42011204a01190b05181c0440d0380c1f070100401c081d00003283d46020454000d012a280c085880e0007404081c0d40e403400701c0c1c031036800d0681071750220015842c010010599010108c0d00828903503101c0341d081d24517460544c0003800b62454001c159249441008110603940e02d18491a0050403d00c000c901c80c607141400f05424140705506c96519a4010080d003801034080c041303400304040e4008500d544492050a088a0601901c0034201c44 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 745492491 1250 745491241 745491251
    0x901020a1502040602101803082509210b0f130c0b1309021305040f0e0f0d0809070602030403020d080d090c170a030503040b090c06031006030c050406120c12 69
    0x40407464008005582c000d07000c989030607107402040c030101d0740110200310615a180c4416000a4845d0006030f802c401d044c215204004042c1d85041c240c141444880000705030401800c120b0303588200e100010344c48520300e4103a9609403989450555040007403000462211050003c1d50700c0040769441c2009981028800558503181c1040854a0380702c0c0000f0034004903a048002982c48107402199012400306116084403440e09080c00007415490070340c14240307a164040b25581c0e11040060040d500030315001041588a07441c00500003810203095051950409a014028560000f0458007220b0781603844044400321414a40f9441c0540c000501c000b0b42080482000e00072034105400640d400c0803152044209140300d00703642c0e40700b000d1005001c2102030000401041c0361400103940559648240e5802298100024036160310480e030708000407500d06418000c0c00d1781446090101012800c1052900782441d4014000d00d0148149880154941d61102c084a2241c000d11042001d031002c1802 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 745493741 1250 745492491 745492523
    0x905100e0a05031201080c060405240d0f02070b1510050703030609020c01051b0313170708070327050d02091b0412061413080a090e04030e040b0f060f0901020a 70
    0x4180d1020301c21b400c01071084010f9070807030b8603088080380d007258801000041d0b4a10b280d010003e001050207c80d5903406d10900003401e00d500c0034003c10110180403240183c1e10b00b158900820038840c0500800144841d00c24400241e884182e980c2e980c8445906009807125018501100078080c00d0f0005041350f4000310344c00700d0b02c503415008031b03015885c400b03054982c00f54084074130340c0180411030b403000d08030484d00c002002186074a01040781140c080c1032410b161503010344503902c80d0380c0840811400140d140b6590074050b10003180c1c0300680c14500d031000700b085140c1400504030300e40004010b842600645c01040d1119642050540140c015150558a03103540c1d21042e81d40d408800381c2a60a01c2c1400409003440ca01541c42911a5046102004d1541460703243c0000903088001c02000b13126802d0780c04206200d00d0030b03103644140e10a607681c150f60030040d814001038801c05c210a1780036014039404070030656114001d44298105c001403454540c160040100c1c901003001a000e4200d0120741c0c4490 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 745494991 1250 745493741 745493767
    0x305281a01062c060a0908011a1809100b040905060c030a1104080a030516050a062307020a12030605090406052215230901051008010905100e0a0503 65
    0x2412544281c403803003903a0320070580e50802c3e00345054010903002d020252091041c07420f0303006404003141074070380b5591054a407000f1600310364501c6010000f07924400002203482c81c0c000301050075116046015100707814034002540d603c1183d0280c5e08a0241c07141c440d1141ca072221703403043c40702c3c80c2c00c081100c16a0400340e6001038194403c0d00d5400c6075034100142c94a0f583d801c1011507086501c150010142104140c4013140c2e55001552140704807011182d41c0b1300898001c00100c207586005a034009400340d8540c504405140d003000a40c88540b01c94400c0100c4580c000c1070b60901107401120002100814103030840c000c0019400044c0d108501c0001d0005014466026501c901c90224640c0b15006420001030f8143d28408001012000c0036115084011071a801010785500d640c0c8003107024080e1070260011032241201d403e02030307079542d00c01c010100c00020440c41c004c142c144020880201f00c1e803035207600d8032800e81d0285043c9407900801081848200300b80000f00e50040252904c940701d2650301 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 745496241 1250 745494991 745495043
    0x70f150626120f04080d18060c050d120b0618030c01110a141f0905070b1c1805150702010c090f170c1f18030528 50
    0xc00950416050701e01c1000c50a103503400c0c240080ca00145004104900540940e40c81080f6161043e4414040040e008604200c0705104440685411a03505442a40b102d0380c6032090344a001000412104480400c602041511440d0751501c1d1502d10a803003031a02c0c0d0301030f10b5031090701034010000040c5203007080e030561048213000310200d05075000c81320b04100441e244011400000d86942040c92103900052080c0e400d00c1d80001d010f0261480581c2038020b0880c0100c0061034034040a8840444e20104442440b030807024100c54244182054681c0702c0c000060000c1510303448450355100c400c0b0386861050242c03125010f501104035411140080c000040f50706081c0c07007150143d0f0803d0900600140178140801c10346074a140f800d610a0f01e00704104000d02d6100b00e004020b4083c00031045904d032124911220380c600d00703040046281d140e050009011101a50410300510024071040c00022008100d5440d00c101000b0042e600a030608150104200c0c0d600d4020680e00b41201e076000312510340666 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 745497491 1250 745496241 745496249
    0x4030c15150510141c06030c1706150d0501020903060a2315040c0e031606090503070f03030305040305300f0f0103062003010b040503010b031f02070f1506 68
    0x40d914581e42c1d5010f10140703c9a02d4031180200b515a04010301d44050038018001d8160381c0c05039469003024803968041100c0d415002a6101c40210700184420019201d040782c034010300320014401c905d804804810308660708002144030303c40448046081c02000d40699040120041c00d0f84d13550300f003140303820b0020007044040d07560500f404c04030341c0c43c14500304203468418503d45003007500e80d641300740c1084003c0060380f00000901c40a0f005a000034ac4040005010703a030b5180c0a1540d006091103406402a4451f521581c40796001d142c051207107000c050f01d401c044a603d0308000c24603840f00e140c01d03202c0c2c0c0248905164114145840011084000c000d492a01101441500c0054407603010720300b101441181d40741494003440703004200181d403550104d43c4018055200d10782c0100c6440350390520b644280d12006a241020030306000902e030a1007000840d0f8070441c001c1c510000c4400c0d0940b01000030741c1e40c684405502081820030300000c0002240741344d81c4540511400841030070030704001d00d11402 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 745498741 1250 745497491 745497521
    0xc011505030c030331091b0207050301060503330406150509071b02061b0c2b03181a0a0314010506070807110604150e060a0e04020304030c15 62
    0x10150b24103003004401c80d40982081d10246421004d081184107110a00391050650540260780010709012503100342c5100c000b021807022200707421841c00a1901000b500254072036407500c8420002660000361100d82e00c51107140c030b5990000300006040c00e04094040c020000082d140c200800c11245a020f4400c070600c1c041700e09880c54407201403000d00321003151f000012800c92011540000c140314141d109040c401802d00d440c0c4291110219101029040c1e101d28036840710044d40681e151581114140628400c1007004d0440007041c00c1200185085005e000e03c85460f0701d100040e05900d07002c002811070096229454500701c0c021a10301c0c0c0c008003c04000900e00302c1000c03140c0e620f5048550413a50020f0281d4240200b980b143d4070660b02c2603404a800030500307107841c600c07a00c4110180004000020503003051900248026110446a48082c1d1040b40108240c1c0c420580010150712144402d0701e0060320313559503250943c0c841c410f580c00a4020a180784802c615080c49412541030310b40110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 745499991 1250 745498741 745498753
    0x402070b07410d0608100b030118031413050a0b1207321308010501030c14010903060e0a140309010e0616020f06130303080403030b0303030f0105060c030c01150503 72
    0x41c10030036604040d0402c419003110441c1001c004a091407010300140040c1010009a80b99110492481c24002d0341c58044401d448113145001ca28007032080c8074440f84000100d001ca440b06540050003280f140190282c6a00040707580c0c01ea0074074880c4070001030280605100c1b20243c4410350705403550401c00c10784c0c5c0b800c4130000019a00c14403400c4160543d460380d61740c130200c43c215211700308602c041c5a1681001440e080c40385000c041ca5040814001b00816000000d181d4150308040000031120b0304644208950700185005070399001c04a901204d410180c0020a0148099118180400d0410161250003078002c603030f02c10380c0040001c0014403801d0703c42d00301000c590350500416000322680741c4440e0056200b00340c054109160001242c280c0144075a290000b00010012204219001a00000c2182042104140d0503203d00207a4035000c0b07000b0360651400d03250300741028005002d034501805c000700e00d805078507a007042561802d00b010700082c03154100d1240304014070348092103007510a2041d6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 745501241 1250 745499991 745500047
    0x41a0c0702090a09051f020d0501090c1b080921150106030b030d050715150803030406050a14070309020316060c11010936140709050a0f12020402070b07 67
    0x1e02c944e01d403081e40324028141084c0880d00410540e80c2c3c24850516441d000c12000c3c41c103002c01d02c01c40d030103003c50101c0011a0fa052210040043c0303841030612454010500030000030458010640e900c048003103841c2c90120300807014900810a049903000100d2165076081101c07421700c0701c8140d040c0d411507a81000030315800020965903181520b229008903104122150106584c18002c40040c52401804111300c21005001070720080c039544100516000407044c001081410300955800a074558000e00200c400a054100d01c004081d0414043c150703a0300300341c02151002d0200544001c03036010b281c00740c3c40d9100005001e0707840e042000c907844031940c3c1d50703c1a10360103544007005a940d24071b4035012044010060410f400070095071001c94218240e009030342d800c0036019400b08102e81e9100e100440c24081809020450141c02c000c1c8120410301040c0300302c61034201000d08981640003500c2d404d2980b400410001c0c410700758050500c10b07000c1e040140980d0890010001e81c0c1040d100400c3c1c0c0440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 745502491 1250 745501241 745501261
    0x2040605060d1d210c0a0506012903100501030207020a09050a060303023f0c100b12070b1e1201090e1624030f0516180e01050108041a0c070209 63
    0x4000320700059107004c9038006203000d4070300000d0300d03a03e18003e0868110800d80d0300e980f440c0490036403107e01c16030740c0c20204c40d00555004201c0360904204d0850745056081000c80c00100360310500888d4100340d404100b0f030303043d5591903d500000b020681b0042000781071208003040513000d01d00042d0054441d00c1c254001d027408580052550310796070810715200000407001804649445000651440414480440598814041e82d40881c0d0700703800c00100044110b042c44800e5013019103051964024070020409908480304450020900003200f8420100e450401d0342e0072f00907000c20101e032a04100001c224100194801000e50030740c0300c102c8107151444200d560b1a000c01d806026000c182ca06048140307613003e0030140c4003001040c100480c00d000b94070034a9044034000c58140d01e423070922a954030400303038102890913010044099002d440509044008182907018071560781044407420006040c40300300b2917030f503015210360003840c001ca0030000d816503603035086010f00780d104580610100341100c00c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 745503597 1106 745502491 745502503
    0x80d020a03050601020303060d2a08010e071a04030206032d150103020a0e060309120408030406031b0c0b090c04090b010801150f090902040605060d1d 66
    0x44000c5000302550409003003036055410401c144400e0340c80f801c0d0003545081c0c03c403507c0c514800300324080c000030744a848d808003542d1042440c041550304064001c8000080d80d001107850003512015044001340e1021b0403c040400200701c1000142049400f80d603200d040d809107040c1c1512006041003141c25404100905d60b1250810806250300c83e60100c2c1c446503003071801314209040444041e00c62041c48000c1e61046d5800300c00581c1c0310100300076032f4806480b03586080b6106c9030707505410ba5aa40040c002e000200b400d285100140d00509450a1100c480540c0d82c50304000c02030301e0745c190040015204c0340d0755020381c05072001561154082d07128603d02c0380500c1c1041c0c3d85403101042c2141c0801d44c044d098440062000c205401e5200050000d407040d501d00003c201d10b042c8005402440a58001600010f001c100711003000429400400d0805190703089401c003520300b81486458403 = true := by decide +kernel

theorem cover : BRFrame.Cov 745323741 745503597 := by
  have h0 := BRFrame.cov_init 745323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 745323741 ≤ n) (h2 : n < 745503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
