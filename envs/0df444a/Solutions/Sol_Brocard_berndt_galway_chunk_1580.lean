-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1580
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:52:56.989636+00:00
-- url     : https://prove2.me/submissions/7bf80ade-d93b-47c9-bbb0-ce43efcc4a61

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 283992805 ≤ n < 284172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 283994055 1250 283992805 283992809
    0x5010b0a120807110612091c052a030d1401140105030a0e010212010e01051008010b04120c080703030306051206060f01050904060503030c0a06060626060127030c060f0207 75
    0x1160855444086240c80ba054100d024441d40c3d00c1200446c0c51909a4400101c6610905200c020b882140000000016a10410880c902c0010308140041c020790055081c15100840303a40141c0da000d098118002c81c03440d408208050300c02c0e51605484055044500c10450242452a102c0030202c01c40d480000c1075400b00404222020381c4940d418054580c007981150075140c8481d520100f9581c40342069011600203104507401764001155041640d41705030f42080c181c4880c48019442c061820703440b11203034030000c81f050f102215017104c000303483d40d810441e08c00218403036200410340b40c0c0783c0f4080107915607400603031400c0f9030044420403034150707510340d40f0410095003402d119486900e6000440c004001c9504601c1d0144400601c1101032840000c038040740070300c83c1d4400d00c41c154466404513803a24208118940c90410103035650030101c0c000543d65030011041c034203e51030704064855215150480801c03000362030030080050041c000150340d8640a0007090405040c00c0f9101c5100a603141094 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 283995305 1250 283994055 283994063
    0xa232a1330030f03021c090510020a140f130e0603070f06020307150b040e0303040203010605100206010306020703120f0b010909060b0d0b031219020706020d0f030b0109051c05010b0a12 81
    0x5001409101e0b0096058a00307a40c04590b1b1918400d1030200700000400070050140c50520589000031244070260003143c0003070450396150540d85541d00c0c1c0b820305030740100c01a102400028005d540a081445900c3d00080100c401c5900a80c1000350a041c10b08249810000c0040c40214090055075000400c0b110303650340c00b80724003001152130034140000342262907940da4000d062030b040308000c038000400355004500881c000c00c03485940d03400700521203e00000240141c1c000782c0040012411030303806800d803140a405d0184000b4014003e4500316039810741810845036950700207111705d50380054000c019102c400010070040303007440c050580c0750152024074503c580c1c0f101401000c580307080c0070800d0010070100420f500d070707098000003889a123050800f090042c071030300c8800110644005260200103006d82c940601b08040d0420860113000001410ba05202d40c00342c000803103032180e00d043c5c1e01411801a0300150001d103840d1050945035010b2106102c3c03c1d004c038082c80354495801841403440d0348 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 283996555 1250 283995305 283995317
    0x4090602071a0108241e16140a14071b060801061806230405090c1c110307120912020304150c050d08101d0a232a133003 53
    0x1404613902c1d01503075819411040c0c1340c86e21050000210a181040640c01156156070380c08004000700c00c9210700448043c90b00050317040003c1442e45c4818001445d400b40294100242042603007002c0c0041141030b801400000c00c5500100301c0c0315400b5011102e102903229034031300c0c56480c040e030040810061003024004d0f440c000355500e50b0341c0c1000c01110000c19020307013010020f151410389003081b80c1119040292607441d00340e0310742c1345258900c80c0010300c111a1071b0403421511003030004ca0f84800140e0340c8100080c2e40d4510300c408109508101e2580508a5000310342e124100b860300420b0001c000d0000040c0084814048001000403c000c90483c80c54504100030b07a03240802610140041e600c003010409030002200c1e03200c070120344030a01c01d0500c0c2c942480004210219501b0925403070036914800200000820041c4821a00e905100950816104412601c8504020a541c0b0160100d00c0b07000c0c81c4072081201d6281c0c0d060710102148640300c4004074490400c81401001481c440c02810460 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 283997805 1250 283996555 283996561
    0xa0b09030a0e0f12100b010e011e0e0f0d0f0606170309100306170a110a0302091305071502070e100b07030806032a090c1908040204090602071a010824 66
    0x4549a003030701944541c07411030308090081000c10740141b010000050010307070340004080c46035014940901a1144000c02381910301004135084400740540a9030940c40841204403014a03510004404a034078003440b001c506400300381c500041100d08550040764549240c0e21184c05851010050b43c84201043e5240e1100007a101c00c114002c0c2443d0300004004410340b04901d4404100107101d030300075481400300007034582da40f100b0010f02e8070b0b240c4002580140b010001505124840b100f540700540f040d81281c20081d242d5a0844001e0703030f07070242540160720425003000400300a1200301d0700704241c450071202040c103080c041c001a1240c0741020b400c8c0050500840e090f52000c0080200303a48a014000c202c6500c150640a9050b51850300a0b10840030740000c40c00e000d81e11070448800040d4040740701c1d06400501000c1e6201217005100340e9105640300c1900b0041040e5000614142e445940810880d0352210409443ea041c180c110b02e85690080007210f204600402d51006028401901031000e55 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 283999055 1250 283997805 283997809
    0x2309070e090f0d0f180b030403050c010b0918070504140c03070c08041205150610180f082b020705220c050306010e18061507060e0a0b09030a0e0f 64
    0x201e0032900b189010320400e141d40348a5607001d440e488007504580d4640514030f04151000c00603a04074052803d401100704040380c0000d0080d0000c20081d07419500114038004030400280d60001c0858442c18141001c0f4502181400103203d210003030841100c0421410750081d50310b42180e8001000f80c16903c8000010600035070141480d0a60680d0011106a5a0742c8828100684042c078850480700c61040c01d112000414929103058407502001c1e200081c00405d801c01121442d41041d2940307004114503001045095a803120a009001c10f2402403008001001010041ea1402001c4000f08103603c01c0c0d410003117501240a07412240201d501407103403420608041c1c1c208a1405521641070f10b88000408115002000b03548940e000344c03030f00000748520b031050000204051001548030708100000414a00c0c2009091100e03611900c41113040035003175034a00e1b04440407a060105181c6c0309500500810094200c803940c8001035801460409580f84006010300c401c80c54442e104040b2030880c2c0d4016 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 284000305 1250 283999055 283999063
    0x1406010e1206070c06050610170a020d09050102090127050405150904030804020109140d230f06271c02160f0806060108040b01140406090507032309070e09 68
    0x80c0c2007110948840e0f007003540c40a41440402107044400e5800d0100050f840e20f40240f5a143c0d000d031580700e40c90400601841c0e080c489200034050951140e0a1114400d43c900f544104034031140700d00700050b5551103490025007210f510344100c401d4602074900e140103011410401c241100e100f0707035021465860b06460040710402d88110660052028030800c0207041e804240240294000c1c1c030780b0020103480c1c1060314030100f00308018035088141c02c1140d00001c0c0707002240c03a20400c00c0022400c3e00c001c08450440c2401a0001d60707080561150040c416200e40c811030254001d0800001c14104c10680d11000d80ca039080110045a00d4001ca00020706250090102c9031a0340020194284802e031205102081c1d010320b4002c1264920a1300700044165000700038241c000c41d002008088144c0c41d02c0b010b5104000004409900680ca5100020385403c450080c035004581e29140440c080aa080a9800c1004203640440c5909684000c3c0940c2c02004206481036035401c480f80c1040ea501c140000f4a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 284001555 1250 284000305 284000329
    0x301150f0c021003050f060103051303110f0601080a0b060603010f0b03040c17030a0e040902090610051e03070e03121e0405030a03110d08011a03180706020f0d031406010e 75
    0x3000c81c0303d00c2141d169078582d103d10b02c941041c1402000540b01d5900460407a20100d80b2514602900d0301010013090144181c01182e420010454021205400015040103800e078820310044c2e008003140c03010414110310f0a0b5001905481060642d0300d03240a808103805203104146440900202083c180f0250300e00301809010011203c14045600301c459564030b9014101201c0000c40002032000c0c14541402080005034000704844901d40f540c500f00090542142c40440610404202c5811040060300c6134031f11101e6200000b81c0c032031500c0c0c1d401a21489040c0c001c0e80c466000640d40701c01d2042240e003511080e03490f092510302e40410300c10101c9050300c503540145500d80700b1245500201039100c0c2804050704404425210b1b1102401020f4451050078040d00407504641002e2030020700d4074502840d4801101c4440e0150801007991860411895400c1140180c0044040d4894203d040103607001d098000d280030002000305004482414001905940c1000b10152551285907034800061003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 284002805 1250 284001555 284001559
    0x307150314150102010606020c090c0a09090f06091d0a030302030a06030c08010608120c060109020307030209040c0807080702161a0405060d270f061d0f1e030301150f0c02 75
    0x5042c10441409103800c0c0d03000d014a40158200322011905c41d01c00705803091403143c00784c803545194072480a0141d0981020300003d041000c0c03a14000355143c03940c0103440d4401c1c1c0c03c0780d000691030304001d410000e44128030101c1500b01c5d2460348900110500041644c1c080f909440c0043c0c81e0b13140c02d814800905540d0f400a0f08d01d01c603841001c50f694006501840403503d500040700d60302c00c18144034403458050a1005c03c440d030001801000602d0090300211b90081003442c0051a207945d581c0050101c989054a02001420040802403210342015207141c201d0158001400340e80a2103100075206403490092032100b08a030b0085160800c0e1032402e03200a0980207010581392250740101d40001c0902e0100c1700710303010b0450b1448440001503009640c406800040b00080c403012900c4003005860f02055200308400340b030b480001141024001c068620729118064100e00b90810081d084030960000000c0072a00b04000410810344607078442c12165040f418032400d032445000c1c050752200320084000e5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 284004055 1250 284002805 284002841
    0x2d0d05030d06140105180438040e1b0d1a09010605010c030e06030403090515040509090d08070c0f0b010b09040e0d08070507110411250203071503 64
    0x41005004805801100400d41c410840b640d03881c01c46182c03060440007424040b901c100940c0c0300e5401894020701740d265026101103585852440c10903005004081b20200584040c100c0155210b515181a440d0b01b50885017400318195054000f600d40e032004103403048441d2090b44e1091162200741c0400515600182c5440007a86403800c1446040411140c100480d4601200464103602035076113040f041d0341503079a07001c41d00382d41028440b40380e1000d00250b06000c40c1140000c0c0350798074407069000c12146580840d48642c944001e2000c4c1d028042d02d0900150819400f03d080b05511005181d4068064034050354181500d05005440c540c50f24400b52010540b140081340102904000b00070126084d00d08120f0241104c400711b03182c00c84040e24500041c5000c0104843c0c40c0f10f170000c0c05c2128004c0085170700300c030207800c006802c4400025403500d14100119201c4c00e040c0e18101890030064401454004105156000a8a034059401002e0baa40e499a4803407079424481d80c002d035801e4040012034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 284005305 1250 284004055 284004079
    0x1f0e0c09040c05090f040c06050315041e1812080601121401170307030806150f13030b01080d0509010f03060e0f16020723010203120705070b0f0103022d 67
    0x140c64441d0a0f40585030080d42d110000c99241884946007522030340d0014503030b00b2640d040c15811905540058205c0303003080c0994101801543d01c034441c800324442c9054650003d5a42041c0341d0003075628040901442c0d808450840c004103816529955490041e8a044003c3d561800c0040c5c0c4c943d0340184170000c40c5441c00d01c01802d540c0350025001c1c160b50204080c51058000700687c140e4074407031420b0007400030f40030300b011450a0a1803404240d004200c03002003130400d41e001c04200115001404030703200e0341d044030b8010014040f00c036000c5030146c8920000780207055800400a000c03071013243c1e01e581c10400940110403620340300354402000380501c03a0010105040c4140c80c10010002035542080d8481a02c4040102900014804046522510b40102d0b03203c140ba00344100c076407651401c01d0650004200719080c034841a407a40384640301039203520780c5540039410300e0007411800914002c46c01506a00500269458880d10f603012040c4c149011059644c07044d45161203030590300041d400034040944 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 284006555 1250 284005305 284005313
    0x122003010e09070e160305100b0d02030a0b03010b150a03021608090f010305060a0b0c0102040807060f09050102190b0a06051c1505041a0903090d080a0e031f0e0c0904 73
    0x5503401500e004040b6000a83c807204000b540d0101507900584540845400c8a9940c6c06900f05a0380f010110581306203141c1d0750141c108055202c5018804030503400020442c002c11984214008100190000c10108500304007052161034070a1041c0c0d03041030081070f03903054540320b40c0480d1200c081d011409142450181303001000d0703800811002d442200307000085d040a501c00d00c0f60612942005109010031450484000802d90120806401c07954003000007080c00f40042200600401e156a6006800c4284585c000c000e04595000941190072196509161030807413044413481c81e820000b28100d5480305e1024000034001c42c0d11158000c1385030304842d01c0040001d2600182c0c0d600480c541e0740c940000030030f443d0407218203c800905200070340c0003212026a440a0381a440201803044a10344a058000982c0d014000c01040310b940c680048c110110316402040f28200701401c0d4000c040003850421314080542c5040c0031603902c6551484280d8540c40108459000b410740a00501c1361414030307042c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 284007805 1250 284006555 284006579
    0x230c030106050c100f0f140c16020d0803010611060702010203010f0b0a021c0302030a0e011512080705011a0103110a020d050c24010e0105030304080607030b15030a0915090312200301 80
    0x4031140b160318000c0014101087d00d01d005118103c9070701601c4c90080f2010140015540c0b1b1401607800940b1585c0000000380d0400046003e0300042c2c035010b80d04011400c02d103280400040c6418116401440100038401031410858140c81d0501b920940315100000e08a10b0042654481141411301c0141d032030707071550540d000b18001c9441c01c1050000b40801d59200f03081e1030550a200d0324403c0c41020410074030210040b2486034901c105401450720449894050035174007008091803510803a0071f031041096800d48988009200a01c0090382004229040a5212098280d150091160008948140c6c070014400072a034000190399031940f12918000c03500710a8800d02842000d08042800412079150000947c0c088800c4000201180d50750380c04110045c043d0314401c03a8000d10200c680c41050b02c0204055446a8130b00310700002c2d036000b6070418032200103041d620324610b03c1c9081082c1c00482e42c40707060590010b11129012034031300301c020b100481c011b065105100312074401100100c1d0b0101505 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 284009055 1250 284007805 284007821
    0x622060902130c090e150d02091b0318010f1b0f11101b0207230a030204061502280602071b0b0a1e050405040c030908030703230c030106050c100f 64
    0x3444034a0f00d41c1e102405044560020070706e5552281d2600000001440d00c00382007640b10708100003210048000b05401e440c01e80003034400203000c072000488140342000034806d2400303410819405004001700507000a04c7e400b4640303124802c0000f9000b120107024018001d401010007110201c40710812038030501c80c02000e00c060040250100704000c5039241c3d100288131003e4030141c131144221100406c04840c03440070040c0301941c010081c45400030151396607100e48002086120031424001044881c000d0901544039510340807a20703291a12040d001d07520ba43c0e021019404040141e640e1301c6400c1412481254001c003031482117010001141020414010708099038150b290190804a091020010907900031801000104d06000c100190b140c41d401c456505641802d0001e503507086038903600c1096000301c540201194032614141d0394003000100d0340c40306d00320009010075141000ca0606480348010f01c2003604100000c602900c2624040c07020794480035403000201300c01d0600700e004002070b107111 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 284010305 1250 284009055 284009069
    0x309211701120c050a06200a0203011b170708150f032b02030408030901030f09020d1103100b0303070f1403040f0603061e09020310051905030622060902130c09 70
    0x180004d000c2c1400f09281e400e0b40c6403030701c030159004170388400ca41d482c01082c02c91000341d108041819025803000e00c6030180716010707a1034850080d0180318002e803442c048614160360a040d510100b20760b1561181d850364201c00c2445000104a1050b400518240400c410059160181c1c00d48540c103040444101c00c0070074805100c059145c4108281a610f0380140e201e800e00ca40c1007001100c410358400d40c021842141d61010008410081e5004a002c1c901d81220448154065200d061401e26040007502c2059210100500c0103411a0011030f46074003540070000d020130242c445c900100007802a411000c24800401c580d101d9542d014a0079584046c0d02c54000420300d4628007081c00603200c111940b05000d81c0501070082e501d0b1840004c02580000c0c8020021282403001054039503468420b908002d0002c04c41c80085401d0208050520f41e001d800140401100e004500000d440303074688085041e080080000c070004a40040740008414034018041c140c60301640204c0140c002c4409400e8800c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 284011555 1250 284010305 284010323
    0x10b030402090f130f06020408010e0c04060b07030c08030408121906090507082a0705030c0601080102041a0f0d020304080a0e0907050d021803030c0604050d030921170112 75
    0x3e4003040c4580528103803000114880c080e4503413004038907243c0101c4c0009104560040c5060380c1d0380810b41c00c40b250007003200b5494100c1d0703140c2000d5103130a000d0710001c0c002150a2510304072282c0d801510704031300000020300701b0300044001024005c82c0c200b5640c0015481d05400781340c0c5040030707944c04000e240c082081e460301d2600c1800b10340d4003d0740c41240d1182d0360945980d201038845401e06800400030040c800c20b24020000c1943d0600400c0703018184240c4150020740c3c0318040068024140503053b00b1214480e8814030040001c101030380c800a49440c4401980c590b2074084200f440391034814000c1c0c0541d014000418402000b252000800c841070a070360760030074110b01140810600a40a54112001800030720540044800b503500030000194000e010002d0166124013003811501314240914135900410200420b011003440f4010710840c00e450204401400c541da8524a054140d8500c80c83c0c900c10452071602c180035a0a880c0041c0110b00300030820340e525489580f428656206c1240c070911 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 284012805 1250 284011555 284011561
    0x20304030f030f0204030c03020609120f03120906090d050c030f16140109200f0d0b01150801080a110d1a0106030c050306030606010c0f060509161202090a020d090803010b03040209 79
    0x42c0c03803003030380c007500c0d07005180380300301d91039600ac0040e0768000b03400b4594056580e014504030803004011042120071340002554a610716507400030110503000b4446101500480d042042540740450301d20103042c040d00342152103001c4028447d00d140a01c50080070100030001d03c1d05e11000a103403020103101c0c030640621401071001000503003680c0d414100204082d030b00180f00f060340d0340b1203807a041c0a100702521003203a0240202c001403000c3d800e030206403221070900b001801845c07092505c1148080540c2852169945412103003981d4915071000a4504021250403052643d42d1040031580c142d040f101140e922881c058030703008503500c00c0c400c0c04042490004000c2a190140302030f28402c0c5001000b51900b903603403200540300d00b400300038200d030004800d200d0480001c01d544a03107801990040b0050001602c900c0768111082c0103034112a4400404004030001a41c0f010842907000c40b0398603016881e170407005002405003100071001014408080300206900b80c0c45800b86200314000c80713042d42c440e2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 284014055 1250 284012805 284012831
    0xf091a1801020307020907110a060f05060a0e0424060e07090602010b030705210a050a0f0c0b032a0f0403050a0b010b04230d0b070e0109170312060d06020304030f03 72
    0x201c0303130340e0000390000c401d1000102d100d4042c09407004c10203800401d690341e4031020342d1031a048a407240c0d40000c3c51035850041c4080c5003469203000010340b401000e0800d0608085e2540b00701d9a807001c0d0b910040440d02c2000910200240d0040d40c01030096804011660a110340060448030b25805810015864580c446010b4940003032400105c0e1406401e40d01c1c07403544990380d04401c440c4074103040841c0c403803002c1c8c400000700c0401002c52207900610790702140d4811450705900070301b42944442da60303400510601c12400040e0784050408500d28000440e40c4440300070044650041c20303d05c00d41c1c2d80780030a000060200125041c6d410038440e205070003140e81c99064412481c043c5002e80e030032284501025154201513401d40c620740305c0340240840c0360b03007803181d40d80360340c21100f201c0c0280021014000c04c00075580100c02d010290075100800c01c5002031081d80310350390380643c440c1c60503902000030201d42c140d1901ca42c1100b2844e000b000a65a038600350038080c101c214855801000039103031801c804588 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 284015305 1250 284014055 284014057
    0x60306071e0516080a110c030718020c0a02280b030108030403140c0d060e10090503090f0f03030c0c0307080102040503030f0315180108120702100f091a18010203 71
    0x445401c03034810000e4954030440b600d401082009150b41843c00151001c104070b00041e10100c121a62450010720000d0b00450030440f1808103035019504c8810140b2407104541c0341c0c00c00d491a41800180c80d02a4401240c0c40d05903400780194000440c1440d040c105402050b86103d4003102420171400070fa0369454002d032600c4240f0412885400130700c0b060000804110301000e02201c003502b1541c40043e00070001b404192000801c0b62039680d62480e0216802c02400340380c030360614110b420441000f058442d503480b442124409032103a410001061500e6842d00300c100c03038000000d001c480d102e03421144c400342c0c1ea17a405511940b02c4e00c190400051846070500845082d590090084d40c10310070f0143d803156960b00090880c05000301482c0b0100060f03200c0320072140c0390356082c0071035000651620440d14140b9505400c04c402031002001080b0258494100c40b488404181c03074588901c0303030300d004101c624209a801c06c4264003007004c0c0b5043d01c0400b0f030004e00341544401131440c050070302120041e696 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 284016555 1250 284015305 284015327
    0x305011a03060c0406110f010f0b011715130612050105090106080d0c12030f0216150213120302010b061909121a091006060203030f09030f07060902061e0306030607 72
    0x43c204100001c0c00458419401103505c0404a000c80301554030f4114503a080d0342c8161038031701c03580f0b580390011a055a8418282445031030600c3d070208a03401c0c41c0801707400b8954940802400f9041242000c5102c0d01140e100000030301c40b402ca040c1160034640781450107064280c1c3e00a60350b60801c030700480c2448001c54a008a0802500e80fa01825000d9503031800c2d003135401d145041403555803a90415148414001008810032580c071010000c0d01c2803414480400d034115080c1c1b40346205200c1c20070758026121048003170b40c010000c0c2032010070072440e049024088610007260000c9000c95906180d04100845121261240e180d17031010755180c1d40d80c0b52003140e0350340000c1c02c8800c0b940d880115500d030010321a0307000000305040e21076100403000254103540c05030703112400580c170010410071034010790415a604030f1070001c099031524080060114082c0501746000d026071341d807144000c0465855030200d401d6807410341001d0346210a00c02400035290011281c09000f4003690000401d0341d0b2148505c2d0341 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 284017805 1250 284016555 284016571
    0x406050903160815040606050603090319080601020a02040e010b061201060e01030510091a060a110c0a051018031707050f061b0a0918060302180106080408030402030312010305011a0306 81
    0x11343e25040120f1400c01c00d0001d04113680c46030703540310040743da81c503078034019442940c0e49802556641c000040f8002c605030180312410420031903e0501071207a901040a41ca202c1d0100d1380402d2981600c00800d00400c100030405a01440c0025800e40c40500007012504803001500c0700600603a0f004010b4007a28030464500700011807800040c040d070482940403135076580207040070801031078500c40405c00582c0010403000c0410000080380f4904d0784208030b6403626110640c4c540e00e40c3c5241c400890080f190800c010001d00402001150407102194040c000035600800018808252106000065480348505031294024203a401d0a05007002a84c0e5000ea90301032004440c17000040381c0300e80160084001d01c4200502d11100240f0201c105440c002040c3c022a0300241d400d10794410403007030000300500e0000b0400404010405140c1102c8002c3d840b41e00188020340e2542e03a480000e04502c500c0c0d868410440c1284004002c1c00350551107599100f031800c01207100d19650004050741c03a03404aa02c12 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 284019055 1250 284017805 284017813
    0x5100e090a05041a0f0603010b03070b030414030c190b011d07051b030c1c0c050706030207030509060309100f0932060114042003060d02120304060509031608 69
    0x581050007990046034000e018035a01c000010001554500242e42914010407410800040c070090340303001c3c40307240d8203180c08038002c0100380d160580345d83d071900000b1b0016000c078080005080701e4000030300450707011281e02000e8880c03445403030791f0341002514004c600b95a12800744002180c0000152280210102140c0401505a4812804036030944c00001c0103008140c0310394081d10024420005032000c010650090b181f6550a00c0e0700e050156400380201c0c08010110401c800450700c04a114000d8844510f07026998113450b003000d407850310030700c410103070032103000420081301c3c2201044544076460079803814442c114401020009850082c00c0241445d4146800251559028440400141124001400c444543c1d8503010f0420000740d208044001d1a1160700101d446d2610504100300358002144401815504881d240e9000090210b40a40c42e090200d506555403111082c5000c1c40c2e00080340c0d6215215140200a0b0304240080c6010348140045640e50b101d101d2416030076100c010001f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 284020305 1250 284019055 284019061
    0x30605060d051018091a070807111501060809011104080706050711090c300103030f03110f0a020c03010606080402220c08071e02100218130605100e09 66
    0x610010880a0030500820f202e910700020b0401400386500c0128000200c0003d0200f040e0030300711000c03000304a4080d2900c0c0110104020345030030512803500590145440c2c405c222400450514001d103003800d0003510200400005403040c0d100d41c07400c3c072030003148000f8400561101d01040d00c501031405240303456081314900348905480b400180c60006c0c003e41d021110000c154001c02e000c11820365510186c4c8900080003c4006a240c44203c10882c2e940ca04010f206000603151003030384010f02004041043c400d0140380031038070981100160b1020803040035981c82e0020403401265100c00c8581015024030034180d14145418411041220324940b00c86000750b459508020f0b025410242801010003c0d030082411052288a000c4200c1e810703807542c0242c2d00b42300b00027a28000292907100310f4150b082d8071005c602d980c08a00a103d140d045540035854040c140c0c200415240765007440394100b107a5040c2d03980c9084460b0410004c42d01e0681c2e80800d060315612044418800b81100f03103800010803004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 284021555 1250 284020305 284020327
    0x31605010e07030b0a0f02190c121404050d0812090601050307050103111b0f0102041e150c060b04020d050f0103170a05070f020a0b0307120b2e14030a0c080703060506 73
    0x11403c11342c074102c2d00040c9003a01c3c2c6e1640600b1031080400c8e1000240030822407104128100482c0d26000d0f03698188441241c0300c0c03005101481c441d50080c2070040c1c8500c03940700c040040220545180380d110340c049011070300d041d5441d2992a4801d1050900c0b900c1031030341c0001c2a502902c1040398442c4803e801034908040703500702e030011443c90f5110003030500c02e050700b801c8402001c1c4080c0000d01b0782c01c980208000168214103012650503003083c00c40010b194900d02030f590300304075071842c0c01d40c1c455804102c07500341000181c000c0c0541c00348640d096082c24100030b08103401442003816207118115541c0212103002000001d8016084400c0110b041049980041000000386401461008009064958480da00f0904035001a45c1c500049100320410007107446d024000c5c1103001c40103880240c400040e91015a50f50f84401d03250031950100328108a1140e841555051070013500c28009956a04040e0125801000043c4458000442d80e01c08240c541d4424010a0300315140100340c58104a0ba0307201d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 284022805 1250 284021555 284021561
    0x10020a120c0e090c030114060a02191707050114090109032001021309020a121505010e0a0f03080c0610030809040c03150b0a080901060303210608031605010e07030b0a 73
    0x290009000c0014901c07007441da2030f40030b43d61160560703104058072549401d1802c1074401c800b800d0940316410500c804112242e00049a179088401d448061b8281d54140c14070602c9a994610840e0002000040042c20702205400204580003001160710041d580c2c40b40c0035088a40c20403006000036189814071410028000c010003685006500062501b8001100c05400c88100d03808179044a4000c181008100d0f08012405580b03034842609105d0706c1c807040d00040c0045840d000d203d052007a000e07550300c07458841010302c80c0a04030601c07281588640f603081400903600a000410858440d881c00101068011300a00c401c403a8070040312401c01b80a2820840a800300030001010142e0b40d5618160889162010034000d103918510785541d10b400c4000100220720040c11440e00c0e030f042180402c006684011500c1a4095420092003984146d0070020060201a880200e0030721002c20100c00b90400741030620485403180000300301043c400038051341c46110760711001d04000d40c0e080c00240040441e030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 284024055 1250 284022805 284022821
    0x6090d0809030d0c02010e10050d0c0c0f0b0f0a0207030c03050d0212070f030c0914190906030b01050906010c0f0b060d02060409050405061f0303051e190210020a12 72
    0x1040c00d80c1000c4503100400c2c6000b01860040b40060620030489040d540c224042c00701000301a20000010640b2420242043c8102105c00c04941d80d25540c41900501c10305640528030350100d610030214406003855801103600343d681180704100c00b00820316001c1c103071080b60745059150300c42401214054030f007505c454220302240c1240503002c12903c881c05000701709071031140c492920364210301a007681c4010201da005114100030711061010501c4544414030b40d80f004540100c964000f07090400718010001196a40301c0c1c19170038200300000c401c106019500da41030f81e1040c0c0b584046a5110001140e002c091480007410704525064110007256541018503808603000c1c004801155055002c0740c0d6a503c25801103000a655006100400c40103200c104d0304210050201203035070b4800e01456200b11202d00c802001d005001511807501011040104d039140e0081070607030740711402c10340c03594900c900a54000740180071b08407a858580301c0c58800d41d4150f40050755181c80c105c0c41c10303001d0030082c2002c07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 284025305 1250 284024055 284024063
    0x80c0a090e13020d0308072601050d080f0a050a0210090308061201020f0a020a0501050115050a0c030201140a0b090703050106050f0f0706181109040812180f0a0b0c03040206090d 78
    0x41c1c0c4030b02000d81c8581d141031100c0391080c0e80780841460080c20041508184031003600d41107001000b840000c00c1c038452454192041101c0e43d55072010149012421880b445030100404500814411a1a5044005013074540980e4082e05c3c5400060f4480c041110990071b40100403a40ca40e02049207400c00c00c105c620110841c0c0c000624150501e910751109400140c6100c0041c1d003c6071032041000b0080c01080d00410f252452290104112a40548a4000c5281c0c400c00c102e1400c00c039400b814402d4001a401000381c08510900d410949401c00c0980060100140180c50281c04606814405e1150a0403217049684140c01c200941e42e40260682c00b01040e5803602c0d00030305c66640801c2e1140b10b640186040003880d035910316001e146c81602e0314004800e42e4840d1048004002c040741d9100c08642810703090341546007036603540031a4956141650b0b0103108540c840c25000510300b140000340700303550318060341c1681c51950302c8260480c5a84000c480003504102d051103100703030b13500304400d00c406000c1c41 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 284026555 1250 284025305 284025331
    0x120503060103060b0d0c09090c08070807020a060911120f031605010f0518160302010e2b0b09150c0a050c10020705010209180402030d1d09010b0a080c0a090e 69
    0x148040b40b2655402111700c44140507950302035401c030503400443c16402800e080700700340200345104502a00759a401058002030094210006004038030078450302c1000359006004001c040007a06048844013200c1042500402001016040960300040e02240b48202c10380118501a2007901114919491030f80c04c9516640315110b00184c1712050150620586071004855003008001c09a94074102407801030440301d0601001c1400541d03440b031507400d403104c400d4a4443d0302c00c0c1c118004051020450044c03a41c010a080100700400141c004060300818107102200e030006040201c40030019403d65001c400ca10b820081021068000d0780a041205c1000040d61034625008910201381d03405400f00f102c25135400502c0c082d0701c1c5414400c5161400e003440000541d0b14040d804079660707884d006009414401c0340b0b1021320514407062442c1b00200c7e03014080740003030759554105500c0c6801003060440402c14440001d54030400b170748103968000d40d0030b0307403400f00390f03480c2002401c5050000382c1141d0142c19 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 284027805 1250 284026555 284026559
    0x50c061609080105151804080301050108040807082811032703100e010f09030c11060c101a10050403060b0a0f0312020c09090a02040b0609040c08011a0712050306010306 74
    0x1081c0310ba148982c034203107249004c1d801003504012020b0400d907218106d90305a40103120200e42018107580c1512003e003490004c644440c00d02402c903015248008140d0300001500501d140103044441900e031400103141b2541c9002003070162444214071010050070f510a0010030001107500003002125259409007480c10f05030003002c070f4108904402050f1889849298840190109104d07186c9580c6200c030040211032207542e4000d001030b1200c4c1016180104940304100305a03140c908403150441350000300e0313002c00200c200340c00142889003080c2c0701e07454216030303840c0560400d100f119440d03107000e5507003a107058196540e0340c0c0113124070101c0c690403550b18400481c1041e45c84418501035030150602103000001d44800906e45416454098002d50701c231001d0106460340042c0306101e03e0390448003c140720b5800d501084081c043c0e80821503005081696001110f81c0100b007843c1a10000344002061b401ca0003180001072055910003080030545d003001254541c86400519000103051402044081d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 284029055 1250 284027805 284027819
    0xf080c092a040e070219030507320f0a030c0219050a12050c0114040501050a05090904120f1412060310050405070f08071202010507021f0519050c061609 67
    0x1e40410066410356400a024410321081032180d42e031003c894402860f03005603c0307001070f201842c8804010f0520201140b1007080110781401009405024103004a01000c444090302d0700b064080040b580e107015001c2c015050000c00310355400300c03d0300f6489140d590b00d09582030208141c4245074051b0500e069400c04142c44e6180b030050001000b0001c0c80c0c0400700c0d00e03030404c00d0420b0400300410741030207d08503200c84171b00124000ea5045403400d080450300c400c0045400d492600c964141164821014405c200030040329800702d1a0010056641c26001d174400c50040c0e0327403120400c5080266020038020255a41440c2c10309581c0424042e0684003645c0c410320f20007050711010389007159240c02240087c82035040342600d1074020802c200042001c1842c0455061040b200700d0000385c10494005240001d54895080c103c3c0034641c21494800811280ca070000c000d42c02c08034001154084004585510038030410a69044054000c0a0040b0f030b10f0f1840902880e00c0e1003100744050000c0400009501 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 284030305 1250 284029055 284029111
    0x110a0203122b090c09140a0e1006090c0201050f010609090b120f070311060708180a050604060e010305180d032a02070311010c080f0a030219030f05010f080c09 70
    0x10b000d48841c00704903090503240180030144c4d0394101141d00d40c503106940003039048203188140c0000b91b000d00011843c0d00d850810b41170070403028130f5059103414100d0004001c0f02e2540074240c0b03036030305500070000e0761100701002c03460038801e10500c0c002408818040c03101151030382c4444420b140c0181040c8081c5d9006540f80c0c11300c04030005071400c0760003003802001842050f00200305400340886105103031120542d50814140102071482604401041070742c0e150352600b00c4100061303d8020038103a1900e075035200040540995620b0640020b0401001c40c1c5084101c44078a0342c40d4007688054a41100b5103a4101c0003002002a8062200b040d03841c0101d100714144134903e801c415035070241000794198242001400d080382c01190400c10015045008180c078581500c050641003041e00d80d40c0c81e00c4030001c1303029018021017070034000003800d240524541c26501c0356a4541d2410400d0120740e98458032128406454410442c1c00e420018422032189014254241d00040e018034070410100803090b840b0f10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 284031555 1250 284030305 284030377
    0xc0709050c07050106090c0203070b04060605030a0818011b122123090601120516140321041503020f13030506160c170c100507110a020312 61
    0x241081c0010800d007480001e0142c0e9000d8100140c00344010f40d42900029500d2003a90001741800c03070b010300410200a8590440801040014111440c107004c1d41404041364740581c14440240c10042c0000d425540a500c4e0307a07501e8001304400d25609409078a55807485a4405034100400c6032226050b060414002500041c0c2c807069000081c600300c014120790407200140715000048003080c0204840c014000440780e0550302034214400034010342d481d20710300d052030140c0c0e00120b42c0d00d42540840d040c06040207851203840e00310100c81c03c0c1c8120311f1001c410b00d0707a000b100c55162581007200344410400d09104440e0100180390040c07400502ca01505500e402c481080056441103403010414403204114503034000f44040c40860070990f5400000e000c102804000400880c0c00c20385510401401d401600d658400c510141d80080c3c01c850480e90060408440700c81c08140e072101c00029448000503011020fa50180c01040b100400401001054200354943c06590060448203040d022001c00d2001e6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 284032805 1250 284031555 284031571
    0xd0c0201020c07090203040c0b0c0304030807030315060e01020706050c42090a020d060e010c0305012c1b1e0a140c0a020d1e0b01050a0e06030604080c070905 69
    0x18840000d142e00c2c0c0e0a0910755480124254014014000404c910307001750f81c200c17140e01886030b540300c60082d1800c0c110302582e400544170030000b140308001d140d0150480c00200f140307800d007803060a89131107042d9503030b40b20b6032022401640842d8090240500810040810010031011614150304885c1e100050007212854408454000d0366030b0300444c41d008410500c01260040c0a81440ca04102c1c401e55420744981d000e4816594076042009020803980003601c0c0a8403c0700900c09018000e4014003d4102880f1340b4811013100240c0d03001c4032804a01144950b500d040010300ca0b9101c41807120040d206000038039280803010050318a21490344580354056250301034074182ca031000c030f0a02801b10240021040482c402c10085202400000300c0d03050003031075044424000030351480c1440c4c483c0958083c4100d105184011910044c03101070440c95040318021503461080703c0d100c007000120103034141d903815003560205c0c001c0350000784424081d208030003400f000c84030003d964000e51410380d141541d07042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 284034055 1250 284032805 284032807
    0xe010b1003150821090118120209010803090a1e050d03021b010516230105011d09010e070501050c031306030209010e040e030f09041506110d11100c050d0c020102 71
    0x10342c8144903894036001091a00c010b08203900004500403d904c0c688031011076107820020302444141e001e01c5080b4420981d98102c03001407901d8a04c05101012401c405070b01c035841242c000111070030000205c586030032020f82007600440c40d000c40301ca91264900c5d03c007100d0040c0c1a202140645400c0082c2c0c1c1154040d0340288080700100c90b0f0207000d40540454141049420030069004003c112a130904459000100308040002c851083c4450040f441040341d0950900e40001200d00309509075103010500007102007415140c05940c14202c07500e854640f5010340150500f008a980110302a1880403040310540f840c1030ba207000e6844240300b06410200100368086400406075030301c545690400340042d41c080045064001c2040c0c0e49006a109a024154000821039115283c6400c41110b2404e6150141d54050301d03008040c009070062082c1c1c102d94494484888460b44c410300600911000700d80c06820054090744102c4c000d0030183c1e6003c02800001c0042e400941c40310b01c18985a1322540d4001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 284035305 1250 284034055 284034071
    0x3051b0c0d2604081c020109060609050a0c0e09040f05030705030a0201060608010902070b0610030f18110303190804020f0d110405011406030a090507180204050906010903050c040e010b1003 83
    0x104500b29492100c070a2141e2050109014071240050f0380c410712407881c2c0c0503145141072050101e0142c2440d100c0100160308010001940b00041e4200d180a0304002d0000c2c4070000a04400701e030250307110014154010940c4010070085010046944032131800b4205070f91904415458091030342d88043d10300d0b80181e54a9600300905a07000e0079980c054844541c095280a80300d8440a100386c20113003641d4400e0110802c286d840501941c007034089101c1c2c1c54000d018010402580030909080e040301a298603c514030015030518000c01190940007906c0341043c5084030f003a40480d0380c400001d004a030050311079007151a0955959410b444a54442c0401c1c00207014002d082c0800d480060f806041400c14410580c0c110360745120603254021250940081c91146134144a45400e081c0d6000c0341e42d0706130164041c46070b20416002001910070544031440c6a440d5480111512041c03440094019000f07810308104602d05904405140b40803000045a011400c800041c04242e0606038100400d54661103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 284036555 1250 284035305 284035343
    0xf03020307060e1e1f0e04110a0906030902040204090603150c0915080604091202060a0c05030f010902090f04020c0c01031505010f0f1803080c061303051b0c0d 70
    0x181d20107003025141550f00561000086601114042c242402c004c0c0008080b050707070f44600210844401c109850300304100b08101004c1c01800c3e840b00000e0155042001c4c6400422402c0111082d05078180d03035051a8600e0903000b180202107001d4100c0c1d01c03075020880003c0000b000d00a03400510300400c01100001d41e4400710700226808626600305005641008024004206a2a16580515040050f09603035500005001800064001005ea01d0250f142030a05507000170403d100d244036083c01c0000320031480d425241ea020840d15481001100801446801d803c0d801600c0c5482d40907041034a0241e840e00002e0903a04008400d140076070210052034903030f42c0e1500840c2d07140c0201d118907c51044c2090b000800d143c8840060505222081c42400003941c070850110420300c020074240c407201500c91600c46544e0380900700d1503401c1c0c41040003003210840d001c1907441015074182c4682c0d181c5001044420040003031364018070720382c2c01098041440364460740111285540319041c004016082014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 284037805 1250 284036555 284036563
    0x10f0c02060f0903040b07080c030a020d0f0c120c080d05090606041103040206030c16050706080103020a081f0c0513090203010302190605070b13140d0f030903020a080306190f030203 80
    0x302041c4084404803c0c00f940303003c040104d4084d100d450300340c10f6540886003401c0c4031030b100c1c0d8040044580701c00524425000e40c0850010203038010784d9921140386c2aa0300b01140d00fa48403100140c03d6034030007402c143c10103004205104400c0d00c6040c0706802c2006c4010108200c4a048485619680109007008500e00c1e25104402c0550855400182581030540109402c5d0200903c46e000c2500c00046600c1032044047d801030324035610400300c030b0509072503030389c000c26404003803100b2805000034501c042a18140407d4480e40c188000100324050700b440004540640b13841d000004c1801003c0002c0002da146060110014201210000d41c1d00e514501c14001c402038900440144158011428400707540c0c04022281c5168011500e480c3c10b0f00d8581764668044031700b04000f0403001a801700f16100c0d140114105201000d075442d00f00119101c1c01e800c2d81540c80c0b0200050050f003080c80342c81300280e600f00103581c000901500444100e6410307840038000c3c0e107094000781d80c000081d034000c0046103030401c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 284039055 1250 284037805 284037811
    0x1a070e030a0302060a02090d0c0f0e10150c0201140a030509070602030319050c0904020c010b0103060f1202060c07080102031e060414010e0402040912110118020a06080711010f0c0206 80
    0x20340205440811610001e40b101e1000e801c6011158000401e480d8a42c8c80740892500349810008140e0700c266220a001c0400155103c2c4240b1059100b00090020700100d000344210307030700d1032100c4032880803c480445030b50307204100490500c000e00c10154440c0518001410500c001910700007014100f520101d4a050701036400242107510030010401e500c0144001100f41c0c4820b040085410b4840701d000c441c0c07034003440c94590741051001c0b84003001c02405400010300740e0400c2c1c82c01c00003282c6984503070340180c04600031041496034450300e034001810300f50001c003804100c0303100b51820151281c072480e0980c3d200703880980100f000100244031448a4070606608102d044804000000740140007024803581403081c0d41c4413040c40000103040d51104e4001007805981700740c5071810608440e40c0a040b207105034050030780f0766180160b001d281199159084024039002040c83e00298500101161002c00042070441008000b0030440010b5109020f510341c0340030b2840300030900d101d20310341c001e142c80f00003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 284040305 1250 284039055 284039059
    0x9140a020a050f0d061e0608061e120c0a06052703070308090414190c0809030712021203070f030b010206060114090f120c01021509281a070e 62
    0x400440044030b4206085421549129242a455070341c070132495001020a5413002604504030305050000c804000003483c107564564480c5007864a40d80280071602c820185184070091a502503080145020694101005200000c440e025030110020481c00c00655221001185021803600c0c10704e036144e80e41c104000200030200c40003000d110002130b6594494800a03100384000510f000d06502c503a0071480c2d90102c8414031041c2802d0010b401d90851180b03181450702e41d45440c014014080c85411440d01821a150041d810f003030f0107444054030341c4400142103007507208640fa841020401080610320440050b200c1c07854001a00310003800b5a074030341c5600350464204104100d0240c6c0c00041020030700b481c0d0040300d902c4000800100e038280a019200980c007000c00711450340c1140c800111010000c4083e400c0e2010f4100d90a0b041c2030740101651101e03039941108071564051040150000b46e068006011451175642c01d88514502e03c52003030360348002c072510780200001720b41c2001c2c2c06000d400381 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 284041555 1250 284040305 284040307
    0x2271521061c0b0403050f13030c1203050f031509010905090115030b0a0f0b06040b0c0f06071b050316031d030601150e0d0611031909080a0503190609140a02 69
    0x2e00d00902c0250750648400510009002c00070901303052017001075400400d55804041d0740c607000030f00d00b000000860300c02180d92000c021004580102204104502c041d03040e2511810b004c0300741800c94090f0030041c641c9a06a000200e081d20f181d4070100d00600902840c203000440381020b020301da0035140c1441e0b00402c00da000e1102000003d13698441c05a110b80c13401c0c00003800001c644c0c1082c01034032411080c16888030f40400c011a1203030150006100c640c001400f140c40c1030160800ba00d0300c40d001214080e020038000b500c0071401e0050b1481000303250b4419425245000b004009409000c05880000d800042060103400c0f0401d540703559070300079280201d00510300c0e507240003103014a40d54043c0d00001084141d64036140c0e03545440400110141e48040700b03100c5001080f50941581e04110b91000400d03110011003011030030303544a4075040c1600210030380e15101420b601a40c081d07001512040c4003604459004503580c440e0310401d405000d0848007c100000c11700d00c0b504c4a500050542c0071075500c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 284042805 1250 284041555 284041579
    0x10303110319050711031e010501090c050a0c030306030f15050a0605151b060a051f03031205090c310506060301030201030e030c06070f0801090227152106 68
    0x18001040042d02d0207510b0002e5903000030b8989103840c08802c03e105501441070803030700d50960b032280345180700861120000300a01da0fa502d592109459055010340007056003000004641881004c0042e01c0e1406400c0224200d5641c0c3d407880a4400035041c1504c454482c1842540340e00008c0c02543d81021540c14184001800e01c2c002600300c0c181351903200000c8100286030581c0d030070070320340c4910b0518014058840b107240511200c405801c045038021030b44224410805504101034040205581e09a40d07106400e68894010200900d0041d1041440b03105251842c0c1540d07a0701d981143c00710800c1c40c0b242d0060541c81c1d001080d4039407030313003a40e40702d4a05100805c03405460740000d80741142e40919011442d45201440141948a5010b103d03106d80948410418020780110544169844903920b095007a82d032448188201e008180307902410341c21030010080b00c400440020183c60000411804c1c48034070104c00000250f10919091310149030034841c1540940204185c942d00c00c0d070581d15800340718 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 284044055 1250 284042805 284042827
    0xf0b030411030f0706260103050307060e120f0d060902030403020a0b0709051f05070506070507020a1502100e0c030106060905041a090c1c14190c021005041703010308030103031103 79
    0x156160045c03000700201070180042c0f15280404469504c0c1c02800402c6d03c9503141c0c241f01d605c2e0f40c009001500c0403420b05045035039541d80000c0c090400b50b00b0081c07070b07414018240d60165403544113014000c0d110f501d030400800c2d0000c480c401140a40e1017900103103015400c0f03141c400c086400c01032150080c821440000c00c05a100c540c10707041d400c00c450840d98074a2181c0b9030305588501810394050442c0c403848041004050b0460001d1003801d0013102c07101000369850b105000d9040740140e4000044c0c0010010b40c82d050940c0d088031404289640554210140c41030203c0d0854040750311039400120181810046428544904003184102c030301c20602c2c80b0768000100e410320310007814055100c80d0024507800444001d2641203200d000741101401543c0700c0d0010b000710390400750703a05140c065440344414182d41d0740d8803030024404000d1b005003c030003c00c05d1030341d8020040200180c6030204a001001181e04010008502951180764015160f50460a008188001c154020030700c0780e10801006140d5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 284045305 1250 284044055 284044063
    0x15030509011b0507080c0a031805040219030f0605190e0f01030f03140f0d0b0102010b010815010c03120c081b090d0618020301091101020c09160c0c0f0b030411030f 72
    0x12002d82c10318554408852404411911640d804030880f4003407061700c4410181c0c400411440f4a0392021324480a94a0314108000c0b80b00b50818108a4100441d126451a0003038010071903140da140300000b192940da40100c0d86d0350b0340c0c04d403038a074400310035490030b00050101090081c2c00440c05003450324198115690340c0404211100068140602c682c504810080a181103030300341076184814548480080307a100c000f6000c8114442c1c050b500f00702455000e54440e0300340602c110103100348030304540e15180040d03440c1c00310a6829400c1211a5201402e00442c9000d0f8040080c0c10b903488005a00d807500740e02820f198407411004200104105c400300b143d4414040015841e0070400c0010500d50300900c4d11294525414001e40550030000320406000b1419091385a0060030707000e480d01900ea010401592640444101028501420032070903d503105898414030580719140300000580c4070714503000000c10356441904c44e008004100320801c20340780802010b240b0150024030100d04040744c05500c07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 284046555 1250 284045305 284045351
    0x40e0604020a26010216140c0a05040e0c030307080912030705101e090f020109050109050d110f0a0807080709020a050a0309150f02090a0509010e04030c02010c020a1503050901 77
    0x500200f40740503801400c491080d0309903124a4000866a800311050040401c0e000c2c507000b600d190340d40582c08040030070003240c400b140f40310040c002140d05003444204801010f248080301214481c07141c0c03c68894800704000c1400750301844410741c441c080c08080207800507014400501c690000e01045001441c0044c3c804001c0c1d40e10a000b040d5860324400f00c20000c81281c0001c8d18050610400c0c13801d000c95020480f05040c000c0c0d0b981510580c0303e10066904800c64401c1c1900712480c540c00402150410000643c1d00314020f0071800040c5051001039500a619044454a030300308460070080d001c0100540030041c010800b0a50410301c800c13102810500521102c0b00a040c3c44004803003c100901002e2040c880c1000e1042140701d003040e0010009410160340380b40a603013900c030082040d00d40110711074121072520110340842d547e541d8046582c0c5c8025501241840205a040c01c0142c0d030303100e01c0343c0203041c403800d00d0000071a58040c01007c1c0e600140000e000c80e4908810841641d8490040c000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 284047805 1250 284046555 284046569
    0x40b03030a1b3806011107050d02040906050408030a06140f040513150b121506130b030d080f0703060f121a0a1e1401260f0c040e0604020a 61
    0x266180d082c00c01049540600a401000780003450f1400e49080881d064030800c400c0350052401d09542e15001910140028040e0312800c0d48030f00070811542c07800e5002da0030090710260010940d100300366901c0c000d46d0b000303030f4044900310004000c100c9110340d1846444000d000f801d080186c0c0011942c04038140d82c841700080c900642e10707000000d00341c1071004584001d1a5004401c24285c14075205000d00401400c90b142d4401c0482c02c141c010101000030300c0b2904d00d8080c13414503015480e45000c01032085219407100c0320486d15140f1602041d5800d002d0850100e840303441d101214a422040190107510050a401c285880d0040034091003280c20300362804c0c0c840081410803030041d14140b1540d03003002c3e8000007091b0f134801400c000181030581c0140060ba40d1407140d4020840014800c002619041d00e8a008060001c400400c409100e002c1d40c0d0424401a9100c40840201441100c1c01e14002402c1111030354489100301044d030a0600c18040c0380c0c10b41034043c01e19414140d00052014105226000f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 284049055 1250 284047805 284047847
    0x906040902010309021f1808030a050901180e0601090501320715090b060a03081215030a0b0f090a031211210702120f0a0c0311030a0806040b03030a 65
    0x2030440e40250f101005068000304020401c4404602c001c82808050320031100007201180c41c0400c0c4e00c95016081e05580011f0083e500b84000003004550b990800070040707040205030002d040001c1c03e0158a030000d042820303c040e0692814000240007010150f0015040240e020131020924003400071000b4000c0d001c5001003048a1188804000d82c081c8900181150b0030941e01c0c54085030f1241d0015110700d102d810001c5043c0e45107030402608803481d1001501101d03080111341c0040c03a4a520107940700000c02c1c5080e0603802e940011a240c07500e944000c450300d8540c1ca090044820040c070714030398842503802c010724200d030f1240e600410000300c5d860080d1301103440b01c0709007080c1040f4000350b49403c20b858074004409607070240403140c2808282d50503005409a4401365504146002c01c40d100d1000c1303240710914102d001c5d00111951200c0c40000e400b00019826505000e032800d00040c40c030040e455642d0071190030304208110440d80160240c601c694010008106401d030041c200790304d81c07a1001c03080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 284050305 1250 284049055 284049071
    0x706200301080319030627050105040b0a1203051b01021b0d0509090a02071403070b070e0d020f040908160326040f110301020d230f06040e0f0d030903020607050405090604 75
    0x81e8003506c1a50041000b02d1851091404040044103880c80380842030441405507907603030814041210488008590081002201800074410440141c1080d921901d4510b10301481c0d50700d4000c03d400f1105000880741d400040403180c6108c0c0381d41c40145602e00b1000341c0b1034440e5400001d0010702c909c0c40c9182c06000a00c0000d514841c80d681580d9245401107901c0d40c4617030a04503466141e031b2002c0742c00c0350828004004905889d210310004d0b08024070143c4100d262514607000c0103d030300d13150109103500c01d44410040000800140c080c0288404041c180b01c0140007030301d000b9101001c4d81d030704010b10342d0031442042030308100354004e07e0300160040d100c581d048403079041c4214520506100d494066000082d01001c4444560061644042d44858901501c440c0c4041c45281c5200b900c0c0c001001011402003842d510700360744504030f01d400c80c00842d440402050403050074003142c012400c4c0802e079141c900c0c80c2450f805002aa5200540341392561400e800c220000c0c46080001d0501809580d940b038007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 284051555 1250 284050305 284050307
    0x501020a05220e013c060906050304080301030f05030c0a03080601021207050d0503040812040b010e011509151701030c05010224150105121305010f0b060d020d110706200301080319 79
    0x170034034103203003075140d1601d8a8141003041c9004403141e210b03070400100c1110000492502c105c0503070380110760208030246582d1039078844400f95848541c00b911640070802c1240070ba02800c01690700203520944684400d0301d000400a420503008414800381c07203200304001000a0750120300440c00d01c1f40c2d804d1843c0c581c0c5032420004d035580141034591900c440307040140030911400c1070510781204c42147c40e4501d507030f032643c920342c441020742c0440c0303400304601d40700a00c03a01c0c4400014004d00c0320305141141000700c0d000b01c01ea122000230303881940c1c1c28017581000d004659040c4400f00500044550f44640c4622480601c0c4030a40028801087d0140507640034480c0d071700c204101c417520081c2d420500410b0a0001c1400a00303601010103c40940c40c018450f82c3c00c030b4a40c0142301110b40c0c014050740c141a003842e00c000281d401011200c008a90700c14481f071a011010700501400d9014000010342031003020800f4a071004204520400100e0504c010400e410000044515501620030210a40614680 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 284052805 1250 284051555 284051609
    0x60405090a1a0121050a0f02060d020f0903010516090b0c0a0c060807021e070303030917040e101a0409021c020f1819170a0501020a05220e01 62
    0x1002000c5001c21555112454107424202e4181c0c0e01e501c00420401c4940342c4010b02841040c14000c0003504203860b00408607000716001070410b0700180c01030f45001000c02c0c51404980c8070310031040340c0d9400494a2543d41c1400d1003490342c03204510031310359400840c0030b5003d40094058802e0003c1100001540c08074010284070b0300b450981d202c0e0341440b41030f4803075002030940c000840301080188141003080940000c0c0f4615004075003203180c0034008240c00c50f2006c0300036045182c8156401c0440080355a01c0200440042008000c8801410302d42c1c00c1090034101045c800750300c24112201448800000100f2900c206c4085902c504001a03407040030000300080e00141c508506d41180c80825043e0350003141400402c203010a200d0103d1001090b6002c000302c501c001d40c124074071081480414007400c1c030341c00500f4001e040312004a0700001d0701c81d61880e0071381e80003d07170341030001d42c1c0030400041e414546003000b07511191803040c0c19500c41c00d0035203a4010050520401103154051070b6002c0c52a201c0c80 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 284054055 1250 284052805 284052823
    0x90c071509061b09030c12020a050d030f08100501080a02160b0403020d021516210c05070204050603031204150b0d050303010614040f0501230c1515060306040509 71
    0x810306100e040100d0500c000100015080d00d01c40c2c1c0040d607605141d142c032a03051181626800091803003514202141070404688040081740c00c00c40404000c00c1540c0d6401c018000c480c460707551200000701d040c2000b000c4840c050310014241007888028040350380c2000c1030507885400e40740300585448012110f400d0201481001420740714015051001f45680806c820a070540150211034074a81c411491441c150003c5909144100700f059040003081d200b21940c403501c68103004000c40c40821103050000301d48080e1000760208000203003000450910b401a5035104100310091410200c5071001c00c020340c40c00420003008c03502c070706940c1a9192000d9003d1743c0680c4009d801002007a1080c906680d9070350081c0144070200d400d6040b41e0401260020480e011b840c0c802032907441c40d600c0c0000568a00584400038800012012000300c4106100c0c07024101c2040048000c2c42c2c1101c9a500b40344125401034418030481007201e50400f8951512011607130404401d032030006060381c40100103401c041840d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 284055305 1250 284054055 284054093
    0xd02010318030306051906140d0908040b030105030c01080705071407080706020a02031b030706050c011407030914011521060905160602061e060a0f0b0408010b040b090c07 75
    0x1c007500350900d9807540c0400207880040d14803040308001d0741c6401034040003d100340800104400b02020a000900018040c45040b0010105140d04641d5812441c0c0d0002c0d0000107403800007000401207441c0410080000313700a0070484180d00b40b01000070030a108151010300800c04880b031800398220200710700b20061207804250f0304083c0c0c589000a403500c203045001d07840780c401c00400c5601c00c01c004002c10014035000f0000c0881c81d18080b02034441d90080c1814a110355070f1200d140300701c5270414030300500c200319981d03000070000021700c0d0055030022000d1583d5066898461108604a20b00c00708500340c4102081c0003d0154400c010303084072000c0348070010485414003000398100900000d1030707030450f001c81030303103071409501c8000403680e0302c800719500300c0d107441d080d02c286a003068440c00141d08a8406480c0c0500e55441c1c042c0712622100d1035000b000122800281080001402e00c91200450300883d0705000950b8030740005000e80700081e020003a030300c9000520381d0410084002406e011300f00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 284056555 1250 284055305 284055341
    0xe01020f010c170109020301080a12121803110601081e070b220803030712020a0e030607121a030a060203070c06090605150f0109090c11070b09100903050a020d020103 73
    0x50b9400240504a0692001c00c060092000030844450900a40b416a0310440090503000d002e900c0310700c41e032000f4070148018086030a0a4185400040c0a00d02008002c1611030300b1a0303000f8a8020031300044141d03422550313005070005001e09440421050010800c1007030a00603900c0e04001e55013040896403240348002e600103a500c0001c1c40c0c0c0c0510144110326400c0c00e0100598514065440c1c0c401201c20700c00152403a24a00740500c0c45a0160100c40c101d1300c0c0c004d2255003ea00030a00c0d0203404c5e0365100c0401d44880651800c18094000d045a40084c0c085201c00c0c51150360210340d8032a90b07550014983d540220026515500c80c5040b900c1140c0c1084041c003034244241483c400411042d250031050032a108202e070064200070b86013a041043c180d540102c0035152800c3d0700010100b07000c1e03503010002c00101460802d441000031320050003006a0080ea12606581000b0002c140c1044090034004625000c20100340d01045400055030151480f1008501500c0100c004010100c403072110303508 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 284057805 1250 284056555 284056571
    0x1020c030c0c030c06041d15060304060b030706030c051b1504120909020702130f110d02180306010e19020409021b0c01030513020d060b0414071701150e01020f01 71
    0x42c01201c1c0102075042d940000c103903c0602119100764013a00c9104040b18500260300d1014082465103d11b00041c1010f01340c80c3c1800003020380d80191410b0340c0786a1109458901417130240038100003408103080400c408000e040019040d030085082c400c494005d200000800c0c40014071408410010603c0c5241c1076151500d02820500c015445100014a00410224541240b0700c21140707001c2c0c0082001248500c0c41401310080c195424400013956191542c821900981d04e001e4202007042820150311099070a004044221f44405606d00c2980314000400107480c13807040c0d264205112a91640c0400c0c050310608001c0e01c240d900c8000c8291000a14414285604205002518141040d41c0b40f2001c03500044098030001e40c1c9075516076150003000d80061909250210303c6070320405011412000d2040064200c2d03585034102d1b01e401e031030102000006503100403038400c485a82c1c0d9001c0d80c0c550420600c3c4100b4140b0302e04150501802200041003603000304201118000a40000c0c00485 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 284059055 1250 284057805 284057827
    0xe01060303050301030b01060f12020901020a08040906211205071106040b040303020606010c080a0f091e0302210309010e030c130b03010e0f0d0509010512090a1a070f1101020c03 78
    0x54800d11050386d20f881c18a002142c168400c404900f45500540d40340c078055045060f82e00003e41c046410035066200d800c1d4400006114800a80b00070000b10100140d814a00592103070101000c502100e9012400341e0043d000951078004050000703c9031400c00e880d04240e14294009132140c000c410390150000c40e00059480c101001403054078425800e540e5107440700b81c015201000c80d00c0740100348040500450511503c90703098588480a14a414040b1300c0c3d46a4921941c4124040c502843c204a100140300358241500b2540001980c1d501c110854100350300020386034003464084904003d001e041c40b48003503904020090301440300504003c0030007650b2410100608100e010305000e5400e203201c00b82c1c48ca4002c03034030441c52850100500014540400219996400305400505028052004a00f0404c00e041c02500c50703d0008010030b198005802c01c0c50700d083c060042c000100a00000b040b503210f6001a42c83c00e21006401d040c403064900160f4540607008070403000c0c0b120711010521b5a408 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 284060305 1250 284059055 284059057
    0xb01020c130b12010e062403070603020c031c0c020606030a150b061b06060103110408060117011b090e010504020f070b09030f13031e1a04020607020a18140601020c0906040e0106030305 81
    0x91907920807d00c0c24290484a401c002068158129a00d43c1100e06e007041000d00030307002404002403007070a49141039218141c100d810070581d5408841d041d5030b5840e0744403030b036010000c01350010300440090413a81004e80c0c038858103d048201c0481070a80342c1d8580200740d10360809540050500d1407840d41c04880d4500000e1b5610b000701e031000d0004e4100400340210010200c03c039000d03503030742c180a0000350f82041401c80389034210300c9411016640e110481000c904140d00845006a0260341d1100c041d0318003100c1850310f00341030b00711611952041040e060b0701c494810444000310b6021840c043c450340c2b69009281540941640c4514802c00010403000e10031049a0940940380708856920200182e43c50b07500c91104508002004940a070a003104031170700e00c90b850b5621038401468145084c120b80e002ca5500c2c8819440124042d0350340000152440c924010300510400700384c100c0b003643ca000710001350748903001d0a200740281e180101281c1c0d60384a40c0c1118004005642c000d001d015540d20b001091 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 284061555 1250 284060305 284060311
    0x18121a01050109050d0609050f060705032509060f09030b16020f0a1e050a061b02010b030a0b0a020703090515030412170606160605190b01020c130b12010e06 69
    0x440500640041060340c0154010002d542000d404025280103550b201001408401740c250303a10f1003034882681c0001801c00c00c29108420303560722151203051221451090440901c03140c040a03000300e680340d903025409400c03017046400c0740c50511280350220509959281d1280c0010b800c00212104010074240006401c5c0b443d18615030842e00c03a070034064212a161500e001000307082101c95403501c0411581305040c40380300d038028800d0318003980c800d584007030465404500005403011420304000d84190280f01e0720010b07850079409030042110541c0c1d51101600c008002c2e551040d400302d508030605114005c840050a40a0071260f860300c40303441d4110182d00100d40c125050900280d9080d0301034403580c005010100da0300c1a2150710f0300c41100b0000d85410010320740900314000010480070805600800b80a04c86800c523002103c41c00c0008003094410b030304039860540d84a00030510103a101c4483c002003039020300c3e01c0001c19180520001d5413050210940824940c01e00d0842d01900380013003141c0340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 284062805 1250 284061555 284061593
    0xd030c0e061305190905090a030906020a0201081b0906120f1b0301260a0b060a05061314011b03020303190c0e010c0503130303051902010e0d1812 64
    0x5000e8020300100211032003140591645848803460420160502c90001d1403491412214400348649603840101221411a031101c0554000078280c0d007811713042120b44000c0c0481d407026000c0da01e4250000b0381241f00281c403204240142054420510146074140c95091400601c020707070b60b155600704408616002e0302c0c8104000000404034a0a4400411ba510325003240b07111107056a01e00762030b003140f81f0040948c600001c085500c0c1600c407400706000c01420b40e031141c10101d45d6800e18806000d5900c7c2c440e00180d0280c00c04000000402481010b68000c40300302080f92981003048a0040325112000503e0103a800350701e0039075004154010001d14440c1a0004061500005040e1048150740c007021503140403c6d00e18000660740d510828100c0740c010301480480f03240598280e01c0301001e2000c2d07403086c1d0000c2c0c80070852415500400c19410390b4808039200910010b100d80c046c060f2254901e0b5804000c4c131110443e4500d04024900308031000f07108210070041d0504030360505141030b140c490340d03543d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 284064055 1250 284062805 284062817
    0x604050105090712060b010905060408031b0c0d02041d120408250e041416051801050a05090703060b0f0c0c040e061812030115090e0402060708070809030d030c 70
    0x500000000110401120340d0313a0080c40030030400b40c407254000c10003604c0841c1042042080410039440300d100800c003c016020040d50ba030500b0000d080084290b01c410820903820505581a550f13446403900d040c401e4048600144440d1403a008245080b8148907100c07581c080e0080d40241e010500303020b40300302c610780019a022052450b00001c0302206c0440d44030010f09400764144200480102000d500620683d044a201502802c16a1404050308142c0711076805e034160910032802d01c0c80b001b400001c4040c0083d150f5504010024803840c0d9035014090040641c640001c44580c07007174011400038850022440d41d1b031103110400c07400650101707040254071301c58000011194101480f03800049541c000203006e054171004103d41511441001001c0c09220342e4460321401042400254001e14074208014a05606018042d0110707400d648850a4040352504200150b1144000c854403568040c50b544e0347c940d654940301181e0700910340d40503050311505101d2030301c068055108540c514420f440d55 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 284065305 1250 284064055 284064061
    0x31b0102091c0203100c031e05011409060607080c100e061e070816021e0601060305010e0106080105130e1b0a08030a0210180f0f0210080915150a06020604050105 71
    0x1c2e000c00e900010002d416074041c0c200d8054601065005070301480041c500450004142c2c2003040c00303180040150040a80e54000410440c0007a4103100c911884c19100032019140410020355107029800010f80300100000c1d80700c89643e020303c05034080c00b00302001000868105a9500d0303481b0001c07512440c440b48001612007003400414181032280c185962490724170740d181303081d1391041d0f9241d41d2086c00394820131311012500c590308281e0130700c00348003580100300540c500000241594010703440345180500b810014032040c1d601075600c9054070800d44d5558104c115032400b41c8000c0880d840d80c1c160501030507455900c24805090100b1986801300c983c040e01d16100d401146c0c40381300365200540582c3c407800c40c0d40032080180e04002401d114401900d450900151906040361003284c01c1100d510001420440441c03038148c00c24920619a840d09032241d19005550507034559603e106142c208a207000000c00c48260740c06080721068010f0840e44250790390b02030180da40d2005a40c110b030103500301000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 284066555 1250 284065305 284065339
    0x70b040209071d010c1407060302030a0501090216060b0112110a030e07051c02060c15091c0806010305090a02040c032313031404050d0c0303030b0306010b1b031b010209 74
    0x74031412218001140f40c848400e800558030042e1001088807900d00889181d10b4000c02400380078000c0205131009640ca2401c074103503804440c0c050300400030682c03040c4114400380d001400c030345041c0c0d6400403001a041c6801c20050300c400100e5410202e44504040b03c880040300214058101f028850f1010b00100715941e17a030503151602d5004c2c082c0c0040007404442c0341f403422000780740704070b41c00a49154582684c01c1d50540c10714007112611141520b03d5414030003405401c10001c0c0c2e251348418241580c0182c1c034a0010140440940310504040d160004a80c81c94424401c40d0b0000307078014020042040501c8010f4090100300496a0305035030300461136a40d0300710381c0c14540e20071005d100020007014040e58094031440717140034150301c1c2c010041c000413420740c89020f18080c038140030f501500041891854000e042ea1008066540070b138000100400180c01c010741070b21010000440c03015042144050250b01e940245080e0700f07240480b80b6069084194103600070300014006451400300d82c50380d500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 284067805 1250 284066555 284066567
    0x706050406030b0f1f0e09040c15090e0c03040302100912030b06250804030516090f1503031103090402030c040e100b0d090f151505040c14070501020906070b04020907 73
    0x43c0d0740345c11800907440744221202111149516400d0303418095130481e564408515048800c50f000c603400e003102c0c1c00610025100c0620203454501e02d18008440c0d034141301c0da0105111014007009154074010000c2030402d80240489507901050b814101320040c00343c00d01207280c0e0301d03101702d0030b01192034440e000140341095421640c50405003d400c00080807110400090003200d1101990800814800800054001d002e181400c60b0040c1c516900c490800c180242100e0004c0c00d0794108510781003c9908240c0c1c55000d240490350075045c10341c520080ca044c202c2c1148151502194064800002c104d03604041c0d40281055038002e0003040e1856a80d012100161303a544d014940e80500140322400381c0716025085981b88a1003107541c0807004100c2e80d140c0c03114a01c642b030f40c001150f407030f0019042c1e41a880c4440703d0003044111402d12170408903180103006c500d190030203005541c00014800040c00802d4040b16090500540001d40e2042a41080b001050003500c0480c4140c4403040410700c2c00344951 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 284069055 1250 284067805 284067829
    0x314070c05192108040201120902011d03010f0c1d10020a080304060b0a0801020304050d030501050d031202090d03090e090307020a0b07030c0503030901410a020c0706050406030b 78
    0x101c02010080d089050b0b00d0600b440310101241c40611031003007031510b0101c1020001445065490384010b6003020302c0090440c0a080c0b40500d8200d240c40d02050250b17a004070844110103203070b4400980b512000e00032a014100b04407000404500307011440c00038a901c03100080c10751101818102c0c04288040401c2062070030001810010707802504a00007141c0090b00441c4c100b840b0350000507409001304045240c51304280c3c41100c49075404003c0009101e000d101160408003946000c1009604201c0000c050356005072000d001c000fa88000e103902011694100c2d001c82000a2113040c1547c0d0b180390007810b40c85c550007856503012009001c0380c1c0c00c1c1000000c5d605a66801042c07981c0e210700305409846960045103082d41004082400c4c08042803040c0025030090b05000c0011980407003d91091030501d88580a00810003000c1565140d080d4001045812852911040980e55200c449044029006805040c0428011840c8c00070b00c543d0404010811240345450034003084080b0b904001003c0311071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 284070305 1250 284069055 284069063
    0x1110d0f12180c26100b04020c070b030612010c050901051804060f080723010e12120d050f15040c030207061401060809120a18050d030314070c 63
    0x34010404060740039a4103410784441600c00020801a000c0c412240100c8100c415200d1103a010800d02c10721122400d04462000400402081d00741240c0c42183d1310000349091481207551505072450b941d9494040780c803626030301c0c004c582c8075a41304d8040d10741561003038031824401c0b603030043e04064545040c080c0024a4605488040c00d003000180151550350103188084200020002c0c01000c41e032715849414040c00009a811007000e042141a602c4c180e075036006458030203000f61107401219400502d00d4a58070082c44c1514050402e2404100ca049808102201d14060000c01c941d01c0501040a020721401411b0240501e13112500c05010010f800e480a0034400050f40c0300780c1080c00c00cac0e084101201e034580760052078043c080e01d441c5c04540307119040d4907a802d24600100140d0780c0c4907000540003210040034044460221343e480e4614031441020405104d071b0700641da000e0301c0e41d03180e4003001041d000c2c2c182c4c039106800382740050040c03081c0a00003850564075030104030a5031260356000d91090f48 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 284071555 1250 284070305 284070317
    0x1e040314030601030f050711010b0406050901051201060308190e0406060c0311030d110910030c080a110f0a05130b09060a18090903020a050709090b0609060f120a0201110d 75
    0xc40c0c200e100241e400280100e040c951114040d081902882c440c1c2881280a80d45403c0d09019a111081c00d40e6880c00d00b50703100d1400c00b03000340300a03900c1c1820203044a41c112284c00d240004085440c0c090516a8006440e0384030100306030900c00c1d55a12410008596541e0b82c0351034681c0d0b04100012160035003c4c0e80001400b00003400006801111030340d901c002c10108480c104040440c2c8481500c40d05040300e40507038004184442c6606012031544030050f035504080c41098181c0200500d403100040c00c000030740780c071200d0703501d03201d5050400c468a100e1080020755035404c2d0401d01404e99486000003c05005000c0c0e4001081101c95099420108000701420720384490550704480510000e4005211800745c0714002680803200d10a01150078030980180c201a0140d0a1550802103268442402c0d0b0381000b1040b400208141003c0b40e03c210202c03142e004c03136258000850188000203404030b4004494101d0344082c140001642100203100340e0f6907003905410990116150b08035504801e000c620 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 284072805 1250 284071555 284071577
    0x6030715030905070306050c07052109060f04030b0109020702030f0a0302100b040e0303010f1508041502070501020909041b054f0501091a010804030e012001051e0403 73
    0x1100b40c001c400501d000320b0448019517141d440350000c5920a1716030790560400040c40804002080c0041e03031440c02080411107002a020802c00b100e40304000f1864818000096624034419090065401458104d0100340c565a11403406200170b6005041c10b0344603119200391001d401d000058104403440d81a0b01400c1c01e141d1503000346026190b49007080390310030f4840c85460f0740282c0400145008050b410a07140c009440c080245101d600748030070f00d008000c4424108070210750f0000d001042d0489560b00180d5583c0b160608500a0003410001603005525000380300038007481403000d25109500d5100001040c0d1740d501046800501100305a03441000c40001021004c0d882c0002c0b100050841882241c81e00200d0b00c4065148035075100d0709482d0340d20001440410f503d8030a86a42841c0d401e081c41c1041000380010f0415000248000c0070000c01c682081c046034800c00100c070301070035105c410080505541c1c2e400c9001e01011030b50621110300b102c1c512002d10200c0780c150781c01660543c9030125400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 284074055 1250 284072805 284072807
    0x605040e0706120b03010f1a010f0906081803071a01050301021303020409020402040b070f21021c02030c010c08041106070c170a1a0402030601270506150a1706030715 73
    0x40d410fa502007445542c41094032055202030180410a881d801d4000408034445580490510514101c00f41040710b9481c0400702650010b00f87c4007030b01c10500340b0469503515129511520f02c003521848580c0d0002180f1030007002075050114040603409440025140c1e01e59041c18200d0040168410100310303549010000b504183d88518805400580050315040c2c88000640140c3e10002044400c2144e420700201882080040e076000451500000c1c404900700f075130020368030441c0310300101c41d10500502510b0311600820844d0309181c0c1c00070081c07204410000010b42901404c881c00da82c08281ca0000d0301480c40c001d800c9803586035001c1c0c0400003007404c01d0100d100581c60080b5900c0507100c2d4040780e801040000902c08a03480b00100644000d10b070030700c10b0509211040c0c1c040701c40079105498400b0200d102c8003080d03044020303820002803656074942c0050041c0010304030016807003100146000400782c1c00720356125402d17400c0408039a103890305001c1c959030705050300c40d00d1151246403407079441203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 284075305 1250 284074055 284074067
    0x803100e061507020f10120b0301021c0b0a03021003061805060a1a130e07030b12060714220512030f031605120109060911070c1a0f03090a02040605040e0706 69
    0x214005420101017515050100d0080c8889048100124120060209100416006030056120b040c0d00a5007040380384030508102402c0c0028000105440d21003103c4180c460b010fa0b00010340d0000c0c90548490740b0598041c0040000e402082e0322036000c002c01c03080001660040078002c00e405091484800d10342101703c120040d103284480920315003048000c041da200c0d0503094018000009500035035061081c0c002d0100c030030801c065802980521200040c00d000415030a91106990402d12444170801004004c544280090709420603590007403c04d0000901c0c280380290f680944001c0403c10390f02504a50700d000d0784908030f940c900c04000084080040c1000c00391030810b0750810030b040080c03010340311003401001d07000304803070950b101420442806540210043c208240d402c061404015448005e1030401e24028043c8604911010a0141000e88201c1d101c014045919076207078207194611a80b04c00320a02c0503403040d07090080100d04c91034070388180411014100c00610401c1c2c5032803425214 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 284076555 1250 284075305 284075317
    0x1504051303081803130510081003020402160b0411030f030705100b0d06020c01090c0f030c0504020306011704030f02071a0306040e010b1002010f05010e0408040b090a0f030803100e0615 81
    0xf40c40500e04241e0014020001340040340d042c98001d00030a4202014456840b09012002080011480500c41d80840180e441c90950760150380260303980c42d2003003105d09034414495004160940c641c0030401404a1464040301d00e0740110152031034200005d030f405950b8001d1703060140860700500c4e0300441104459000880115000e408405000c0d00d42d1100401c0360420900c90155944a000c400c041181109281000c1d0003a07805010034113041d038890784001082ea01860713028540c00004100d050703015811264090311a203074900f0780d501d01460006d1002920002c81000351195030070100d096428010301408604c80c0301d6030075007550745180c05c0201038407100058041a540e12030340703809541c0381d10300d840e40100c030341740c001007004c2035044114001c071032050741322416092141007804001150541164100d910624006490b1520b410004110050507071062040645080002042025010165220340d500c040140c1c3c00c50740e41d1052a804c420700319070280e80311541f0207070b51100b030ba13000c0c020380f01d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 284077805 1250 284076555 284076571
    0xf1b1115120a092a12080307020d0503011d04110406030f06060501080f2202030607022a181f090507020615030d050c01021201081c0c031d0f1305150405130308 70
    0x103400ca03605e24030382c20000591034095038440000400c00c40c0340303601084106000308151402d50328542c9040748850300350301102090081c10302200d001c0b5082c03119014640444440c01801041502d40c2c1e0314020b048001045004c0b01e8041c2070031400545580a903480c3e03486141275100d010801c2c1e41d000c103060314092404d8651880d4100084815001d61000c0241c2072042405400030011080342034100c02e01c401910780486c210401c0d610200c0015102d84062044c0c0d03259081c00188075449020003400c1c04c14074030748108a00385184000107009030646c0c00050084410390240d805039207404a003004020701040e01140c26903c040106a64548079070020b1a0318124440010308100d00c480844c02c1606c003c0e441880c1030750000740311910504200b0780c0740a01798003c0c01c02411704d1400d81c0c1c001d880c02c00d42c80c4042e444800b8071031901d50151654000910460001003102d000000c825448100611065482e010742e03c612440b15585414540306640c02043e04083d019036440d00ca640450f80100c1c02002c00e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 284079055 1250 284077805 284077883
    0xd0906080609071115010915051e03070909060b01030f02090306060609040f020313170c1903030905010213031403180d02010c0f0b160f1b1115120a09 66
    0x21340790f14028000c40b4030010310008009072651524541800b551010030030b50071790400a0030108025601c07c60400d1524800e0200d1410140d44e04001030b0524019030700807100a8103010510041008a07400b5203e92042600e04008031f92040c0d16400c02c80c05484120f41d05a0300031400f28010349460030140504d20b50041012072450355a00701c4034140c0e001520100040710f08400d5840412003800b884031f1070304601940541c20b0a640c5c40d4a199140250b200c80a00e071803c1d66407050a00d803007500b00c0e0782140c1d0048002d40d48c41c1d055481000541e1060f1105503401003855001804000c07010003266007020541c00c401b40700e102c00c1d00c01c2000d07688030000d00300e050007140c030008800a0342150317103981c032341d030003010600300c43c2c90000d0340441d02140011281d1700b00140c50207101c0569401c03000741c500c1c2d1032229000321080c00343c41c50304d10186102d0250300c5920004180034000c10f00940d4004001d04014901c0584280d141d52810805481e001003008107030811202e0301d40e207403001000802e019502200001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 284080305 1250 284079055 284079077
    0x7060536120a05010b0612040b04031209080d0b010212040522111b06011a090a03170a120e15250e011d01051912020c0f0d090608060907 60
    0x30714035034440c812400d25810000041040c07003802c1c443d10f040520140c42a62030011903207a0307200b801c0c40040c00204000042c201003001d00d88500c40380400590700c002c0400088219040c41a0260004102c2d10485414480c1c2400c0551002c90b0030003035141040c40050500f400c003820040d0100ca0703400d03144a80c14405e01407804086150203034458803080c2122803a0340b1000b641d1075009844400351034000c564480001000950010240e110f080b1511007500c3e074803006604000f07185020a5400034106251001d000340c0b11444200c010610b40b0b180342c031050100c20319008140103480e4289180b0010748c02088698680002c030416841d800710741044c10001101204158090f5030000e403042400291000b0b50f43c9403156044070004100028800420412240c0000028a10b1055050490320341d1500304d11600d401d4003d04099030341010000080d034855078810291070b541d01804454036514071540c1c40c40c0e041c135401445008140c40c1c2a6031080950b699000a00c28884030162200d405c0160b24406 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 284081555 1250 284080305 284080309
    0x7140d020d0903140310031401020c0f0601050118031502030405030c06040c14031903050c0304050913020a06110a021e1806090a2c010b06040306090507060536 70
    0x10026840c0c0d07124002910405800c0c000e00340f03480700d215408140002c1080c000c1030003200c1100402c40303621019a020007540f0241c1140a07004002c074805c40c0c0d04c80c0302d148440b134034008100070741a02c40a80c2c0f01d18000030b4481c2c003040310144034072002d0b22045d1749012280b00403150b6001154068020b00441303150804603031a052030303c4400c0358262a10980c00c28107024803042c4004c9035a094000304d0003014000c2e4100341e410f10380c08030002d0003005d22800040400c58440140f00b503a0007440f00404454642c5028503004045452001080740300301011003000c102c050080443e44080058440103040d071021036402c0c0720b0950202c1c00014099400d80312010100d0703940f0142140c3e00e00c41c2000c1d121041c2440707018898810310141620520500303011a201403e15215000812a00c20455845880790003448881c0101040180c0f91b030080c40c000b60100612603140c010311807092041c0e003161043d5035034000031503607030113400301400c1c540c074207004000800070350a465525403241d152070300d1345110b0f80400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 284082805 1250 284081555 284081557
    0xc151403040f0c081209040b04060302130903030b04150e0c03070c0f020117090c0a090507020c06090d0803010803190e18191b030b09060609090a02071509021c02030607140d02 77
    0x1141070140317140080c4403981c5050030300607107440f480143c40901c031503420769000400c030f05800c9c0b4504215541e560f0015050520a4103c1018001d0282080101141042c070320300a90460340100045010000041000c400b400401c69208034426580c2170715200700380c0d03100002c1081000c030690400001402d80d803003c1c00c400da1614007a0b54818018000841c1010034410300382c9040d4000c403031144c0b0304020080d0098000c9001e0680d040308031040c0e82d8681d0300c140060300c1a10f80b0f00001d4012600800085094580000100200080c1400600c0c151b84448021036850310015a010741200c140b4613805184005c8902260b0002141132010090030b88034102241141c0c04111051542c0040340c000c0700b02c0c19018824200c0b441c40c00d80350342c000e07807402e003010505038130449090780e000f8424080011004503e55058030340340d55000d03855140c40d101c5444400040c06035010164860000017102c040c1c8840404541c0100d1036016000c2d103000d40e41c801007030743c060300054001940352400304409120fa000d03500c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 284084055 1250 284082805 284082823
    0x70f0311030313050616120b060c060f01180b060714010917030a0f14070e030f060103030c02090702010218060306210f070b04030510050a0609090c151403040f0c08 72
    0x10055040f0f030007a0700b0407500e418000703014101000320111030300110a41c841c0240c0000e0300290700108210615002003407031071040485001d041c3c00b4120511006610039039810341202c5402c07440b0f600040d010f11b550310884070711224569101800300038000004030031040d035410315114003000088480058840401500c801c07008074900b61350010030406058298418a1030b0503444d079008018050072581211030701440900840f092100011500202b6642049004901280d4a040e07950341e503903a103000352200381134000403881002d03001c0010300f51174414401c1e0b880c950110241040705400c40c80500004d0341c4054511500000821001d07541010180001c80e04550800b0080054844503041d441c10f00f000340d01300c907031440c03401c00007007000c12400220729151200404001031643c0700c0c01d05142c002c0285911101c965420100c1c81c4050100303d2008108480401a5040000d044200110360900400c680703802c60400900120b40070469403801c1444851145a1200f20a901c410460345041104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 284085305 1250 284084055 284084071
    0x1d220504050c011107030b132301050114040506061c0e01021c0f060815090304050a060c121b0f02030703320303040c060e01140a120b15070f03110303 66
    0x559249a00f560f002200310412600c100282164605580c3e54a182c031201604020395080d15a0206041c08aa1007083c40c48250100359184604802e41c2c0c058081c01007485451202000004000341078285400741502c21a4001c00081c1781241c2e15094014941c890440c103002039a50348041079018209100401079007240516005003000006d5800b030595481c0c42012020509019040220700c0340014640402c809094000036682d445101582c076502039503001c0c44d4403241c0083e00088d95a0050443c2c01081c2c0995a01580000445000d440c41c0c1000742d8150b044819200b2a040454450f800e00c540c01c81c401416110325a81d070344c6540c030811018883d508001440c419200242c20800b00342035030303042000300c05181540703883d859001c0000101d2280c0c909109030111080303140c1c0e1003400700814441f4200740c1e0a840308030906000b45541076200ca040e80003072500e0001c0010f85005615106c4002290108510b092450340d240eaa03490034000040301400f81842440c20350354003e0002e5442940c131 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 284086555 1250 284085305 284085313
    0xb0a03020d0e01060b071e053319050a0b010806060c07120b104103060106080901060b0429040b0d0207031e0e0103110c0105090304151d22050405 64
    0x141407020603034405084803a402c514040042c400038502180c07481c5c000d85e0205009106600b1403030741c0e0710120000810b407001003481a040108190b1544403071441e602b03038240100150340c2e9580c108011a100c02a0351804281c55100181ea540740c10350081c002c500448040d24143c9a07901391008014204040c11104a510b07e0b003042100c12000001a00500f8039500404030302c035810f005a03003034a00d82d0003c048039004141030184c0f040c07801003000c400a200502107506940e076642c07004044107000e4034015010350909100280480e207910966054601c44174141e98801d58840c10b002d8003a003400740b03840c00000244000916030440b600175094000c0419005641c9400c9860001c11204e450000d0100d1901d03104034101c500c0b41c2c0005508071010b42800e0004101400031407060075401881b0107044203600346410420741034004005001103074403207480e80309807890320b80d0151100c00040c0c03003580e0303030301e103403103074280041c5401c545c100480900c0c803070243d840f10f5940303071040180c0384121402d658640c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 284087805 1250 284086555 284086567
    0x70905091501060507060218031507081e010e07031b0e01020105060a03030e0d02130e011508030c0d0f2604020102100e030a050913150e01050303040b0a03020d0e01060b 74
    0x80103104504801460703940d800c41035810040b01070f015006460300a00000c3d40403c080103811006810b41e0052034005007141e900036903001410100e018200c0c3c2207000101a940400c009000a01d0a0388a000444150452503802c0c500003d080e901c004021508240d2a400301c0703501001000b1b0200106100ba580701e03058294500006425542d01800e414095041e030807040000c203501c42104401004111000b180005540c00001e1002c013080b080c02100c6441c1c00d4500180010550000b40d41c1c8440c42103030342800742e645584c65142d014003000380c1c4868020710b0b91014124465006002c2d008081e0400840c0b00681c07181c662406408144440c01110032513091105568040206400c0b000311014140300c94400c00079080d4480c01106000030038040c02242c500019910b00d250340c3d44d85140c3c481d00704840f1143d8840c80c610483e00d0711400228105900c0045140d06020003146c05894011590524002d03100781d08500075480308074071004071692019400d062141c04c0c0500b0008180d8840d01a86602c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 284089055 1250 284087805 284087821
    0xf040303060605030112060c031e060f0509010503030306190e01060f1b0507180f140f091204031103030702040f1e0605090a050c070c0821070201020a1b0305070905 72
    0xa2254020b441070242c1800104442c180000f2644203255000e04081420200ba5006501401d4401c190401055840d8109400d600442d8040400c6881a00b05002036aa8030340500244110030b02031b054143d0001c00000e21142000f44642c103004003094103010b40aa82c404050002050a800401c00210010080d203010b41d4809040452500c4681d08040507001c2c5545450f0340b0101442030f00c9103403040001d07854407200560b100b03001c4c90411800c1408044418403044000030012640e510540021001051001000050300b010400c80441e0480c0707024256201e4a1140a410b80d075241c0c10703c0308101aa00607180d03070103441d00f41d2440c017101041c3e01501070380350003030240d840410415041c6000c5042000ba1754501d0f105801c0010342e100040c090312198440e207040d1056102c060581c040c41417000172030400c0001d51215040c0348100070410700015204550107031103484006401a4803842c0220301081610030455550f00c02c54040c41056a40c2c0d0340e4032820a02a58000c14515603900c08001c140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 284090305 1250 284089055 284089061
    0x3030501090b01230f130e10030c140d02130b0406150512100b0c030408060c043f030e03070614030a0f0207060204080307020406080706090e09150f040303 68
    0x2400c0d2000042c404194900002003820044914180c01164100c0185190030032240c101d40189010080080e0303514603003250a80410894070640c1d0a0101a50015070100901901c210559900072030000c2c0e01c615050a2a0a8049031000958030004d500503002c0180c1d200c0000c200302d01c5c0041c4002c80c00c4481c0300100011900e1799402130001a80301044602c802e0f0307200040364030f44190710030f0660320b60b140c042050642260503042008601000034002903420702c0040076100f140e908008a54250b3341e01c840d030039864003803072261803060700c103e0106101208000c1c41040111564800032000703445200b041400c450000c1d0001d034049801e9000c94034a909051007100c000e00002d0410f025101d511480540d454400100081c807590b0ba035030344002195030345070111160260000d1040d511a500c80711000d03142d03800540128401e600d090300001c1c0d5000045882d404460041d00c0d542d868500d4010103c246220080500a0324000c0100c0c1e80e02c03180340104d496000d007a16480c540f016203000d02c0d003c3c0413 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 284091555 1250 284090305 284090309
    0x31806050a2d05090106030503120405010506040b01140702191d010806040203070e090a0b1e060a05060f070c080109060504031407050c060903030d06061e030216030503042105030403030501 83
    0x584003400441e802d007030604500007900e542203000a80780e891040d42030040c50700380c2005000740030014002a0b9210340911680c01540540c0003000b444d03d0750010003003207540004029010440079285400120004405850442d00143c151050360508002d10207040f192508144c800b4285400401c6105501c0d490060141c1020b1005182506043d0001b9586607618403c203170701701d194040059140070b0184a50904070381e02000702c81081c04c1010140000b83c6011055101045e80d504c0010020300e00f1014140840e100a010795140c0034007080b40d00038581c001242600c184184007000600110b0922998512501642d40024a4141850000c0c0a0b0b400400402d405040a000201c04a0030202d8254205801100c6181d900c1c408140400e0550040395070481c00103141142c00101c0d290801002064200d203880f450b681c0c601115804d800724044d1b078015080e040110a11040042e01580083d5040360281501e2000902610721240b0f510491600d4080028000700901c02019018024540 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 284092805 1250 284091555 284091581
    0x3020c010b0d022b06021206090601020a031e2102090a0b0c100c030b100c15092a030b04030909050f06090609060103060f1715010b160201031806050a 66
    0x151201c21030300021010707010003a440c9400411900d02802c0003d415009404131540108250f485143c01c221525145004495050050b1000b20020340c45600c0450305109665064441215031a440030340a4030400c9611000c2040c01400d1850402010b000e20366030450007040c20015980e00c41c07900c24050600415400499001001d001d90050170102192440b000007038000001200400f42c50120060b058051055070004a0502c05a0311181d100c0b0054201c2800b0b42c050041c100084d021506c00c5030f03030180014090668420f180d41130440b032030103031303110b40040003034802c541b40d4172078482d50b500b4507040c0c400310085a900803040100421502800e81d1021340b40040311510716091000c2076040500401c1d0a00c528400310005490b80c2c0203500083c050080612224802a2640100301ca1303840074000c0d01c42940300c2c00c80054110300c0031000c240d060b10304800d04c560a00c42c0b036180000b0044414001203060548031041301050000801e0440c5906001c0c03003000c103590a08944003c01c458225507100b0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 284094055 1250 284092805 284092819
    0x41404090210050903010b120307050d02030a121104080303010e010e150603010e1807090609050f0402010915050c060a061706090d0c0c05030303070f020d020c0a0312180603020c010b 80
    0x2009a42c45180341c000100039400c00d07594415080c000240100744404185038042510314080f0b82e6000000f01409840d841542140d010f001c406000340da4074000e0f44a8040001c0401d440f01d80b00c51066080211040002550507007096182c46880e8110b4000740c000500340300103640100300f944911038000d50001c030102c00103580810341c3c101140c5648014016a15001390817000300c0c0d00210240700101c10080346105031554291641401c002510350b0744030382c4010509000210b0302007001c4920b454041d9505854bd070106a1400c80443e00f405540364040382846801c0c00080e42140c4e00340f1400f44a0b04074401d000440c2400c12048000300641e442440c10380d540004100902e100c0b000803404000122418000d0710b1805d41d02d0100000e150725040a60103002c0032040c00f44160b00007404141c00745054090b51016607282500f01e0360307500c8248200c2e07400382c80148c040001c07034141da803096040d0f5140d10303154140404054424107101042c2e030120380040d50000c0d05240566003803090b0290484115488 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 284095305 1250 284094055 284094071
    0x1e021504080604060e0c0d03030b0102010c0e1305040f0501140103031202190503061201060f09050606030f07050702060d090302060a0f140406020d0605030d031b1e11160803041404 79
    0x100b6550a03004100400c2c0559a00784106146420004162100070061500703000c4255072a006024040c040780d1103003d9030038a01d1510109004e00c0105512000c0030308102150250b00002c0c8002e414090300550b042200b01c0c00807070120710280075644030b070411001c000a00c0c3d451460018030304107034500c00c00c2e10148144000e0b0131110184518941d44a500e26201d0b4480e01e0b100005580341c40c07241c500e104c0701d40c681900096961a0070549200711000e07500104015542c1d1010b0262078801100c540c001600100300080034980644080c040c20341c00176010b1803d29001e0344400088a03210882500035a010008000301902c15004241c050100a003080c0f00008041900703529061380070300006c216039008121580300a540703038400d1000700002421288032101c01301c0c0240c014141d800c406170210025141c44884180103030021481d40031380b404650340880d90400211140c0c40c1cac21300f06005c140200d030452407080034240102406041441d01855445162900c0c1310380110001c2d0480e03009604000301f0f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 284096555 1250 284095305 284095319
    0x1b1002060609070509030d0905041d1c050412050604050f0705030c12210403170f22030503041806090e0a030809010609020a0509010e04090c09181e021504 68
    0x34190304450107031000701c8161a0110b05481c980510060103406100317000c00030801542c02492682240c209581c100051407003a0001ca1900014016813500307580640c0b907000c005c6210712003003000d120580c07078a80e0800342c40f403550b83c0111501501c241c038a5841041803000740306080c4000740744e050f030f00310040c00494501404a51a0411b100320148166141c48401d030706900144112f820b10012690040201e095444e10741c511908a80030503240702082d54841040b601c15a0200c54039210010b13411340c240845074a44d442005002c1841c82140403104038008001102003020300045c081d8040d42c009103041440d0008220b400640c0311a15a50030304030418030700036000c1141451590149002c40d280d694121a540c05001e407a40401d003414400100741e6042c0e0b80c0700c00500740c0c000e4240e8400d0a450807034800c0200342d600700c14000d84100d4294608004000d070b158001000c040f110340d28070030f8521031603c501e001c0050700350100d40c028070401a01021403828403010480c00d03000400150616042100c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 284097805 1250 284096555 284096563
    0x307021014061c020405010305060f070201020a05090f0325090b0d0206030106030c020319020625092912010812070b1f15090819020d0f06060f081b1002 67
    0x3480c0c003c5605506044903003940340c07103407103d05030050f0061001e942d50340b800660715041261100d824604c4400400c000601c18021212400035030741d186810104203004004810f50001c2600707602d88182540380c05080d10001502c604480000c0008800c103140106100c103499808108521aa8100840c04010b0380e03440250f9064070410f15000962801640c02686075104001b5100030159025462001071a4001a07061260321174004a80b031142802454500c089003d4040d0b8003c40d010503024011806580d882e681000c00380d451582c001864400b4124145e404840b0390354410034602c0046c011080100030492201c9155680203103080c10700d880d60703000d01801030b0240044500e95a0100d601c5d55681c003050f406420317003007200c0540c0185418064140c2505100390451070040c001c080111501540803d8081600640441c0346143d40da0b0360380340e528801c3e40741101c03590307a603020101e6100b40440c0e01c0d1010700743c1071000b0b100070b40c8032110440c204011401e2451180c0e031001c039000d031203e2f0b01113 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 284099055 1250 284097805 284097811
    0x1a09030403051510051906020c010314070f02250302031207080307050711090a02070b010501030e03040306090c0b0f0403052e0c02281412190207090c03020307021014 73
    0x541000551340301d26040140301030040e8001d950050340191801e141796101c05200003200d996408650b10110404015405e0311800c0701c0e0940724418080000d41014081c181c1c00b00c00e41000e2040d100c1c8010344031082c1000340000f400312500b07640c4000080c130850600304915a803450024034120b0034607499684402305480010003203400c00502090320010881c00a0303101d6201c01c0d00510113001454011008802508444000e13104024054000151540240b040103441030b0128091494103041d615000e020b01051203040b41c1b0071402601c00504e80201201a1051031380b03d4106c42e5950b8998101a407401541e05031140032b0300580d50b02d07081100b000603140d02019103049004a4022480b072800c0e418000d514005111984000c403404906c1403404043c003008074420440301c8001b8025004060b954448003c040c05100410050a6845001c0042c405032440c2a0f1040320407943d201c0c81c408080d2070500d615140426008030521040d25014080644100c010490400110290300e00740d1480c500c0207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 284100305 1250 284099055 284099083
    0x807080715020a0204020412061505060306100e03061f0632071704081b0607030516050a1a011e03020f01050706050c0d0615050405090c070501091a0903040305 70
    0xe2207204103402403140c2e01105400400c115240c994a40c4450b940302c962880840e8800e1400001c500541501c480380c4007a6080072703042d00d0450b620301007401401042c00001006004c2d030004030021581d001c2000511036a00d4404040d0013014100d40303046512100d810150501800c402003860f07240c920031400070790103003200488158041d6451207040c2c0d8400c0c5140600124100b280005d400c100c124011300464141d80119503058000c1a038941401040118983c0d1002e02040307100c010a100c6c030060515032f41405141d1030300081e1a501e0b545407404100f411211210300015450840e990312010500500407040c5845510802d20ba030703a01001410b02000b842030f2062100ca16482e481801030310000360b40f001040006007091000800c80e904540c45002d503081c100342e00420f42e0042030f941744143c07030720540310b0030309281c00c050421420701002040c0c440d000da0140071400108400340034800c201801805941d10b40281100740303045d0240c0081c807481c0d040d40208410030001c0d40c0065181e00e06245 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 284101555 1250 284100305 284100329
    0x812120c0304060e0f0715090806010e15090106020c041401030201080a0e01020405060703030609050901021e1e0f1207020606060a080c090a0e0114041107020d02030a020618090108070807 82
    0xc1e842d01600514020f0105644c903c10b042c030003c04450000350b064251071001103619007040000340210307410151405840550742003880100311012a00010b241c01a011036044500305c948c01c0041090326074242d102100590000002034810306043c410031200e2020080a07802d07030360641d00081d10382031015001403a05507a4240440d002078080d0b06880107400001c041541e25902428000c002c0d0075280609000980f62001080100340c0510031160004040000c108805a504808a02e43c2d0000c03c48004d0090030200918100100c0200800000c101c90b080d0341d8131441c1d14003a924141c0350052409040d980000c080c026141e403a0010b071103a002c40c502d80300c0b400b59200e1003400c2050082208664018201900200f080754002000b24140c2d089812810b80f500703001070800c81a9012242141c1c3d44420800090300541041d40412a51900290031201c003101070350701141647d800982200310000040e010301c40c041c070340100365071300602da4080209a8941001701240d10b035490703481183c2c3c50b095 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 284102805 1250 284101555 284101561
    0x2307120e0d02030f10060e16050714011118040507080a0902010e0306010609031203051905090a170c010b03030702030309121f05060108060d1505070507050304030602040812120c03 79
    0x19601008150003036003e0f0644030b0056a82400565640b50202d0000b80740e420444003041c100d0241c80710300d101d0000400d0b040c0d04040090410355640e4450300e01500d11140141d5400d040b290240903020300001d003540440d685000d8111034040e00d114a0000c0c41c4600d0400f800c2c0420a903200d419140c018180e820700103040103482c40103032009156085a1034050040000006806800800040469006a2a000da078000303050044007113a0044680c0701c00318034104802154641254003155001c91280c08844001038161502541004414105a0300013170010310b03032850380030a024050030210194015400c101d46917000a44901030035400314014030f00a00d2050051074204421040409549a4100e850055810703170b4020b41421a91a4003080384140451801c0c00c080f0219400d503030300001c4000451074003070303080b4000e407501070f1164003004020b11041c4040740061000744000d5108040060303031181740440141c20305041910715030004a05114803030001514090042d40842d42001099886ea = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 284104055 1250 284102805 284102809
    0x12020c010905060405151006093005010912020d09030803150d0303020309160602030d0e070f18050604020405060711031204030b1008071a0c0102040302060a2307120e 73
    0x3100d0344074042e100344600810303c81403000100d50b49142540c00e072201e6000c0d544080744455009424030400300040c003c41c0e410030801030700d1003100d5140b50540f420440d0400c7e50100e4000c94a04103501030703585035510601c01c4200001000607048405190020741191500d54038081c04422482c4400b82c00710400000040030300400394981d0700304d40c0008100d007400c141103040050082d0022a152402807041d80c0b1000515280c00c00c601d422a034540e402540b811300301e100d03c18080c000a074816900e0b4403510380d000c0b6000c18025010300c05420004152840880c2c240b40c42001e842d0050000c1d40294030400007070015884110881d00c1464000c0030b802e46107040d50b030100b40342200c00542c040c64464046004400c002c24184040e00034003414174150141c0d03403500c0c80c60362103400c02e00c17a800d2041c0c107a814110303481002e07402414203050b0080005003042d0340e0b500400c4a991260750540c0c0050052801d1018100c503040042803070401440445045c20f041d9542c1800c6482d00300180c40038130001e103440c0c1d00d0355 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 284105305 1250 284104055 284104061
    0x152113030e060904090c090f020304020d0206181c05190f0b150a090603110108070f0e060f030109020a020d020712030806130606021f0b0f0108060a030b01121104020a12020c01 77
    0x4050068020045e98401e820501c03120549401249a16400c14204248090340e500a0700d000710740090004915120702c6d070030030070554043c200448150f50350b885051039995a8224500b4418403c48500c07090701c080d842d10354209003000303141c0150300b11901c1605002c2401140c042080c1e44e072044100341c0300c0d2145450818020701c4440c0d42948007d081d180401d10480c44d8001000f101d00c02c01c154180311140d44010b54505408440480006404a5110480d01c1c8148515004550702508281c540f00c8940c2c050300136036000340c00c12058141c00243e0400c0d40e60b03040081c0e2000309254409000c81c50701f403440e000b1010105072000f408010021000c40c1030b81c0c1d284058554401c01e094030070804190f807004040d44510110025030303402c0c1c035059000414641c66008030142841c00410a13013104c8411001034030318110103032000e80c00c50809580400010f0310412610301038000310030b8440d04844545401c00d581c0c01030401b094081c0b801404800e0302203030482d8820503803491500c030150321400200026801 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 284106555 1250 284105305 284105317
    0x308132702280909050106050306090f1b0d1409060907090b040225050105010b0405060d02030a1506030e0705100f030c181e0e0903040e04020a05152113030e06 70
    0x3003051010000100035803c41c00080442d002d1001c180442da907280c1c02074420740001c80300250021100e034000381c01c4124003941c0c20b5000740d04010b903045461800d5a4119140c12000c000e00c0316070b035145100d000007030ba41c0401c95407001d032003801407000c0d16085076400d484001c20300c0b0b00c6600075200c0c0090829540c498059602ea080990241c1c802c803030b030109806544082c1d01d41c098807154601030000c5041309103501110140c44000d071403180781407221140e000082d400201800b916542c0c1c0d24014031020040d0900c0740061483d642c0c0861601031100b011400d220250340301c6032145007004104580e0a81006500c001e020842c1000184140e01c2d02c000d035141c02d003a0701c500c042000e140c103010030085520407142030f016940e03004000f100758540c94090603001d02590b40740b450368014801040540c002ca801594000d00c060b101da01c03103564500200f0866040c440711210110008a402e58503001030300071406105000c10451101c90801403032524143d00045000703800c0042c2500d003c6140d803241c3c0200e0788 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 284107805 1250 284106555 284106607
    0xc0f060914011a06160305090307050411120a0c17074a03030f0a030e0102040e16020d141608040b0304140a05062d010308132702 57
    0xa0301c400c001c80968020040a541c104541c0c4443c0032030045400c0c07590543d08410b40e190405525000103842c2520203420072240d60b9130510038420013042070b40b02e81c01840c3c40040b1384500c040d122031200c42d40104c090b000030407110800e0301d010030b503084182c2d02c800c90701444640300d00051034170349410000311880900030114121117501a181d082c4040003d0303e06081100700f922500a4152000e00d411030f500840900d900c0e81036000f407109260061000000b03208180460600044c8a141c00540b1400d80e0801d5003d1454668082e040054440c1e1480e006151080d240c4003909800070b02c00006007164503040c42901e0504004600d0600b011f007a503030003080710358100341000e0f1515501d00320540b1640c0126002c40b01202e46d0702006902035400030304001a594401c0140c6038964528440220b113082844010400c0940d8000c00258860202d140300d010303501401c68903540c1c034042e21a88110800561041c0c0c8070b0301c016044885000710952058a203541c041c1e002580d15130050700104c185518101c4064 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 284109055 1250 284107805 284107823
    0x909040302011b091706040203060103060c2006040204060909120e01051b0a0302070e0103080906071a100e0c04030309090203060609090f04020120061501360f060c0f0609 75
    0x50480c940083d4982d08840d00d0126404009500344174582d00d81c1c0050310002e415910044c0103000041940e001005009aa40781800020041d018415850484000a40126044031007804254140380c0142d00207030090040a200103a40c42d502d2619a417013901c80e200401060040b05141d40e0311840482e20745110002800400b84480502c05459541c40d0000702c000d4071420500140c040c0224480604907904041c8403400c05100006021490340301502c11645400c640c0b0750ba0380c942d001035039032034003850034565034040d400d0601424034219800500520303040341050108000199001d2180402d8400b401005a100e03180d4401140e900e01500c0c081d82c1e03000408074100019070400c542200d10880c000d0340c40d40705001040d203094003202d0800c0e807556625000b0400040d611290001030392841603042c506001c080c0140b110031510041d103124106404c0c401c0d500300003091140101d03c070010f0200101c00030501c070302d80400581400c501000c010403a5490a0f071b040d0500555038824500141c20201d21 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 284110305 1250 284109055 284109101
    0x2206151a030f010603050903041e0f170c04060807060c0c031406070201050a09120c021503070207030309080c03190507051c02040e0c0f21011b090605030705090904030201 75
    0xa4054008072100d03100070124100010f0000e1186c002c082c02480001c0181d031030a420030600400381041d00b2900b03c2250a1a0b0001072141d8049480400921a00c0c445641d025060f003021401c040340383c5416842241850803d0107540000701e000c01c12500d203810120102c170010315018444201c19400584a040d4441000351849804146c1d20300c64403041d8001c010583e030719000c3c60101d41c00810040c3c4a045491781e00303d58a80500820240300313000810b10752181c0d03811710380312030264411990440142c000c0d40c0100304241c0c01c8004078000c0c1c06030310041c2c0a002c901801190744c6925042002502140844681c0148541030044a0142202070101d5a0480800030402980c01111004901a0b0701d4501095403010740132940c0c0e40c8406004164941321001d003800c0243c04c00380e08442032611a40c014660340c48980900c56241c2c01c3c00e001070031500c2c030301541c040500080c2c1d83c0e521040c00c1c03143c200304000020750700c0400c0f900b0800e03089030108141c5d151810100d0052101c05c1005e085603a6100b64 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 284111555 1250 284110305 284110349
    0xb03150d05160f090e030a05160b0907050f041a06071b0e010e0c09030a030f021006030f05071707031e06050708060f03030403050303270703080403030206220615 71
    0x10100640d03529045030448a980c0380520f43c11286031202407a0160014002202d01714444d400809c5480514141a142d44039940c8a1200101054035030010a43c0b0465040109080580780c0e01030384a421036082000101c000030700510604880ca00a01c1070340002601c0c42004410094003403055640e10f96000c01d9901d424014011000a0082150f100c1e907c50000700c3c502a50f1301200d00f03854002e00a004101e0541d079059518187d03900400781980150400c4c070344e2030b81d032603c2240002e50241c2400030f03000f441ca090690501d08a03402c05440c011030300d110400e903070b4400501038088039484a040d0780031422880c2074101c03503800043d005181ca42044103101c0410b0340200c82c00d00071201101c28a003500010020195244a103110040858106100092207000d03001690209038904034103030102282c5181030141060713210f41080350b0800c1c020809000745581004103583c84030b00721414500c440f2820208100900707010344010000b58070780401030010500116084020b080001c100f410108910340c07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 284112805 1250 284111555 284111593
    0x90f0d030908070605030f062d0622030b0c0412030e0103020720030106091b030e07170604060b09040c12031e020d030b060a2c0910080d02070b03150d05 67
    0xf0300b4440121009021603064074002c00c012009c250031401030400111358010886861128401c07079540550700380555160f00c042c905000303000f41004038541c0702460851174021036a81d00503050781c01c1c1d04020300c0144021580f41070500c140d1909401c108001840780d8004a0203442182001814056500c422011b050b0203401d82d03000d5610120000d0002540b40c0e04801c01f15120812107402d9150035400c00c804143c0641c2c0b03c401480042c00503114940d40320318400d00c00c00c00751007409005034007050800c81400814494072071248822112518941000c0e142e24004800344c0c01000c00b030340703481c030303084030030903004071012541c04020429100d40c81403510400b07521001020b4842021900780036041800740742c03000868030b01d07610945030f40348030340410a2510300c0410055030042546105c01c0101a403913030b81721020781c030071440980998199070615480074203201140b055901550b102120920100e942c0d001640e40c0107521541c102170b03409112002404400c5115406840d5000701e8039000c1b006c4425903 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 284114055 1250 284112805 284112811
    0x3120304111906080a1407110a0c14011403040215161406100609080604030c080c06041b06020f0c041a0607060c0e150418110c10060b090f0d03090807060503 69
    0x9220740b602075030362020b620301b540d010309450158601e01c00e0000c2c0516004180d55001401c15000b2214082815595540100100c0d0460000d0340140000c410306980c0c0042180c0609554410103411428103501040b84603c0181804410160100b820726040760901d00d105105a001804102c5000020688948601050383c1500240e5504600400c401c0d00074002002281c403858010449642c90303440c2140c190711601c034200d40c000c004010320f201c6080d0405c1010b020f5400f641c4a2080085800500150381c50300f07034040d60954010039422600c0100104401048540588000c19841e40103d00000c2070940a586240d200e0710200f409d03800e0281d107a2107045052100d03210321100207440c000b00b100884450342c560390301c0030003000280640c0740c40418840e1980080007010580d0120a071a24030503421805000c04941d01003a0800c0340e1404601036a0000c280015415181c014081e002c100b03040e09420200d40500c80310310740d6004261103036100000405503d016100e186440f148002c1c0590b0080d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 284115305 1250 284114055 284114057
    0xf180b0a110903071806080f0f0712020f010c02040213030605060a05010801080a170d060311010212090105071407080d0503150102030901050301140d080c071a03040203120304111906 80
    0x109032903807000d1004000312109030074000c0080c50118034000103c51046a910005002035032946000a400d00e000c200040003d48038101401c0302562a029075440d052090f40411880d05580c0141009a00d43c884080d20014080c42c000c4807400040c004100a44504802106846004100001072041c281d100034041c010444c0d12a40702139a80004443e103100a01420b0b001c1c2c0c120010141c00140d0401a40e140f0801200c003050810f105414040e0031640c0c1d5603c15600745d96008680b281640c0c0c14006900015005900f150403c402c0c100024124090808014507181d0002c644061440d4100141c2e8003d10880e0201c032880c101c8108004c0498009484409412580c0b102d2910558004800d40f18284810f80d07505003168a000d0301e51445401210b0080c1d080540140c09002040141c4010035a02d03105100400c0428a07045a030540c006484920300c5006030180284801a0350200c0e0040480705440d074210340301c0d262400d00d90781003052440080e61103111803142000a5034031300d41c02804c235070303c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 284116555 1250 284115305 284115311
    0x90201090902130501050309070305011518060f05060915070c0302090c0301061706011b03021b0603130b0403020718050703060611060402100903140303150a0303020706030f180b0a 79
    0x507840c0d80c03006078042c2011401280704249030500440d441380b005160b008a00100300c03603416030780c2c0e242c01d402c4442c030b06607403110207030080b40c1030086034105244040f42d14400007040001e91b1900700700b42c4c0404500e0041611800001480201c19503c082c590600400b00310901c540e60440e80c82c0c25540d480d2144822801000c040b80080e0621301180182c0f0304031081500d8250021b000300b014407089810081103035060281c2640d24240c0f14040d00001e880c0948690001e084a4010508120011580c1c0d1105449404200304111b110002d6503203107010960720404001d026100c2d450164100041c581004a05a07102035025040a039203030480c03801420603031410042c040e240c10703003295280409090342d1201c3d40100042801414903501107000040c591411211582e102d50300d4100b01c80d0a45d401e81c44690011003800307042408840c3c0000400008c544030403800385140d60194480d140343c400c003000c0c9582c1e1010302e146600c15400840c1600c001941d0504180000c1ca44028030306011385131165110300d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 284117805 1250 284116555 284116559
    0xe06011103030c030c0d020d020c0a02120f0307021302040e0a0b0a05090c0715020910020319090e18190302030307090b160206090d140a03080a1b05030915010909020109 74
    0x800700449008241c1c03d000302d440c660700c1090b4401e0943c00301640d1038005034208028400c3e60810301c06070500d410300c44040c2800400d2801080042c0142032090701c1e440c0c100a942216040f0000104d0300c82950584a12140d05c1c030403980700e402401107a1002440301c845070b08004211074282c0c85040c176020700700e03041c4c4030003502d0700140300c0d081c001240c0344900c5a00030420384001c20403145503651150041c02000d1318100300030011603099055895504090781c404650f0703403208600503040c0c8503124840c0c0341100680d440e20b0301350750300d4076400303000540401054041c489000009014459000c01c0d0140c400758002024a0001d55a61044a4002c000b642412021071224011000c813040040c403910360b60307074506042c0c0810045174025240b20b0f81c0a401030200000103280c00c035180c480d508001d80035140028203402c028120030310003002804040d20303243d0383c3c0407620700e8442245070f2030125240090700d0351b80d148c001900d00200180301c140c5e24581400001005041504a40200362027a0780e6010030903 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 284119055 1250 284117805 284117837
    0xb1015090e0903090109090b13060f090608010c0503070810080624090108120f0d05130b07050703020d081306060305010b03010e010b0a032901030b0f0603161503090c0e0601 76
    0x10013103450a0b8001510080108861980d41e0068146124000c040d100903213070011500c2d0458015a01083c00342603510001c2048240314440c0e2001005c4042c028090b603011030314024458480105080140070040020524a205031503560000d13080010496007281051103503c00210b540c1050240303101c030b0404403000700303041105000b0b0481c1c0c113a60060a96041101c11650150460003003188000700038802c000c1c40d0011401100e001d070390f5a20703110071000860b0400b0740440d5030060002003070200c1000303900c0010381e0015200090100e03610b0302c200d913621003400c0c0140103244904c001e0140c1c0e042600100038400b0640c003224407a0350850007080041c0b541c00b4490700740e402001c40340303610500c01602000030035090306144502d50001039407818041d8a0142e0808019800c7c0c2080d60f02040d0301080010781c0500d009002c1c1c020904a004081040048011400300d0036035000b07e8844140c0c1c50a01000907000707801145290ba4408030780b030502a19240801418801164514001050703c80d03030741d20306 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 284120305 1250 284119055 284119057
    0x80414040608010c140c15011205060c031005040c05041221021614030115181104050904060b040f0e0c0f0a15141605240907030b1015090e0903 63
    0x40685d44980311503441c6211143c9460b002212208030501402220348003a403a0807018601901c0d00c2d03420207411101d5030402c6486d000004002d440c114504000b4444140c140e65280c0085910440d40480c0c2e03088031a0003105c190055030b015184041400502c141000300341c07607440600100d205460041e88220b40c100b2a43c80714000486503003411a00c4040c82582012071403101000000340000c2032914403225070381000002d9901c0b019036070700601e81210790f54156015245040006510003400e05061030700207080301e40080d00c002c00701541c6502011964a0740d401c00c440300c45c9800c44c100000f04910b0301c030725140e036611400d96125200000c1d8082e1140340c044082c034203580c0e4481d40750346003e0307501c0d40a4a00440e9031450544c01d040601a04414115411000907000c0c8107101804429802c01058186c00c0c94014944440030092410041d4406000412204980e00100501e078240c0b01c07882c1034243d66403907411400030410318040c00c28090380c22800b1a001c03034031390030350101c219518061020340b6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 284121555 1250 284120305 284120321
    0xc0a060519083903040503040f060206041212090b091e0d020303270723010e0306130303060801020a0c051603021f050d0c030606020c040603050a080f0708041404060801 74
    0x80745910120201c0101002040140c40c0d00248120710b0030078041c3d0503018160300b045804441d2544009002d2001d1941d0100c00340c0142002d000902e014102581c3c0e13403881c1004566400300700411300321103800110042c1c2000407202e801c070102010030b0920850068603a10160f000c00e14880c4101c0701d401d011440014485241d8034186c1c0a1400c50f150091070b4481003000d1161011380c0000122107401459003400040d00a090103528000c080c490751094030715040801e035045d414490801d00c0e5100a80700403c071164407148048285503104450f02d030a40c000c15580d003001c03c0c00d41c40419800304040e044524820034501401c11141034001810403036040e02c009000094209d01c00802c9031403132100c003160007000340c04d017130800f82c1c00c24003141d028a04944410010000283e19114200f0a103501405421204082a1070a0058a042d501c41554402c01d15100034441480080d0107082c00840e40e080d15103003517001c0c83c45503a5540d900740040222102c1859a40b01e03901e002000030300d0160500c40c0d044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 284122805 1250 284121555 284121571
    0x30825080f0f07050d020303150d03091a0d060b0403020a120819050705060a0b1215060603040501060e040620070203150709080106031a0121140c0a06051908 69
    0x110784001c1030304002080c1c00034000000d1042003030003003500140c2c042c840d900340726402e135004640b80c2c6800c0c2d0f200516410354203141400b41280a00d03038000709078050880400d580c48240000f03503c054440c07003641640b10300d100030440b640c54130401044030071007400100700300c9008075039103003040e500c801d20085c1c015800e400047c1400d408000d80e0f45003e0709042d520b4880304050812a091891079100c090401804980c001012a51a504800301c2d160610000c0b4030768000b0f5008001200c0d103141000194078010344094030a00340800020300b0402c00f508604094a000a50301c1141d081074540340c00903010008120351503540208010413003150f910300f0b035111a0380040007401076000e0400d4a060040d4050911010454810f9000c60b00301c0c0e0901918000790310030b00800c44004940503080781d0401d4180c100d0680e03094412105504084003090a21840f60002d40380b1004613028034805103032a050045850704891800030009270203070400040d04942080099403c031072014858202c0300644111031050b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 284124055 1250 284122805 284122807
    0xa2c0604110a1b020901031203050903160b091e0f0f0c0d060c0e061803150405070302191d0103030e09010503060c0d0e01090b093003190603082508 65
    0x803402a1140a03c5145802c1c688000a9840d6060700440d54244003604141c8000b445414120000c9a05105259100c2e0103100036506005030141400d000410030100507084a09980c049140541d05101c404850251075040e900c0d441c0c0d02640c020380b50080040380040300c0c001e4511545001101281d40c195100700205a02c2d00c842c51959841c00421141f0494004c001600b942c50100340c50300c0d4014440e58407044440603030300680000301403603e0740749805010a80b81d010140000070744002607401c01c0e25412905080300303e00107040041d900c5055884120f010b02e41c242821425220652510b040c1c80c000c1c2da44035403a201060a01200c01403c2c8507050301075002a0011318003402c003c0c00340140c240924404501d11003140d00490030350f410403d081d104210b0f0301d000c5c4408054104551a00d415500034140c0704940d48102090b80c45070b00903020244840000000398107048110250011031040c1c540030000c1d6a00c0b400c4c01400c503000517981c4402c0100c2c28092108444414110321000c3d1790100b181 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 284125305 1250 284124055 284124067
    0xc011a12070e07110a0203010c05030604060f030809060a050f030f011a070c0b0d020d1a01030608071d060d140c0120061f05091906090b030312060a2c060411 69
    0x440e07003010402200d828600681117034900598080c041c0740c00002040c4d494130740324140030042000301c0d081030b40300400003044d445082000541700300c140c0c0c2c2e9181c0d08894030f580b07030b5031802c6090b100b40c131420340102d122010001c100140044e40c00c140c54141c90000e0103031100c2204074000310791144250340010302815128a810840c21200e40c006154110301c001d00581040500211001914075a52418501d00341c030b10601e03005540e252080030000c00c200402040c5581c40d01b038034818003554480c0c61812144540000822a4540b40081c2e050030b80d00004082d02010b106850940b1810b145440900042c40b4405100c440d1508a4030f04d41c081024601074102a00c0700c0c00f042d0480343d05640003030b000050551f030008003951103500741e52003151983c1c82215540c005008510880340351750085810700c0c1c40c01820400f240c40003c241c5020b82450f25003603d1980300c14000030300882041d0b005032071007642d9800700c0880007400088007100c89809081c2640c0fa80f82c000400007a220200d99000390400e0511034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 284126555 1250 284125305 284125307
    0x10c02010609090f060b12161401030207030804030806061308010902011107081f061a030103110d1101030203091e0f07090b06070206070303150f0518060609040b060c011a12070e07 79
    0x3241e889518010040d00005200c2d041c41c40c208990200100c106d21040c0108122030027240c05d80070142038003442c00310f02d001e01da40e0f40900100030240c009010045040700145107600c40c0c200f200d0000d0360910113400d04541da0007100e406006100070480c00039040e4000d500010000140303400650b2070280c003500c0300000e201008030f820020445520711541e10344c4030010b10f8000741c074401e107d07901c40940c1144c2e4960550403c00649800484414080c880b007044010105241408148203c074007442c016030b580c0c48540886182c1261500687e10514a11150400c00c02e400201d1001c000400310030b48404175500da41440072030340542c07040c0d81c0058040050030300601e0604d00501040e403181c00c0004461141b10700c0c8002d290b40b035421010940d150b212007070203149000840201c00c1e41500346503580d80d04d40900821a54002c0c00700441c051034680a10913403a56441d81591101d202d030f0b80c020010604101b90108203030404050031801800040100142c49401248080075100c0b02068030901e40c41e5000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 284127805 1250 284126555 284126561
    0x602011d1b06090603040606030309060810050405040f02150a031a030d050304020105160c0302040501151e05040305010207081803030301140105070606081e0610060207170c060309010c02010609090f06 88
    0x510703698425020000d0031942c0d070310000590300560091500090880c1103140c00f400c000c506400a6050000ca0350802004c000803544010640f20140c40200d51621189040c115036802c9210081d840f4031003a9044151901c150060301c0500c140e03031303800d01640802c0a141c0030b5240e84540c20a40540212405400c0300780039400446e003003403061404911b410448070401d03640221001d01290603500b000c00c00c1065142c00d004040c09400003003112480a200c05501801d04650101e20034081040c5c4000c0108007070040b030a840c000c540140095585048500d8008a96030104460034403040e030b241c4c603e1001342000010340b0305946c07240099890f400e429100546040c0c00c00344085a00645039040401c80032003d1000c10200040341c80c012a00040075240103040040052456a025010281c2085035030f9000507190221410211522109224507210754142002c8a44880c1c02200010500800e48015409809180c5056000300070094441e0007040980384000405010444659a000702007a0307187c2c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 284129055 1250 284127805 284127853
    0xf051003050a02190b04090b01121a09071e0203091003090206031302060f040612060501081018021306050403050c030c012001060801050a200a2307020a0e010602011d 73
    0x4250703104e240d5035071100c03400980e00c01c3d00031150003611014044030550b0003042e48030012881410500520750132000c1d03034010b5055006661710030180c0d036000c2410240203800010b8511030b61031002400f03248060010b5a01d40c0b0584400f401104c0d207144651042f4407074421804829070082815145450340600004588403590042c0d9110908102003c50b107040c0f0f500400003801543c55001042d034008401c4070880c1d625030301c0103040c40800d03010000b581d01d11001c203409a504694011a44581d0b1001d0100203008a58401241c10783e964008540726400c4409802141d01c10411280510341c850145030310b6240c2816130a0220301e0300e181000c5279280c24a481e482c0c08951030f00001d01c0603500e805803403e54a094a10b21040d5981c0c51100080d1034100702000c4d040f140304000d59242005010000303008001c842c00713018000801002c0000200c8894084030001c58004120102c21740d00c4095850f4000700a204220241d8a000c1000b000481a0b0a80c10188407901002d030a525414800188010b000d0b1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 284130305 1250 284129055 284129089
    0x6010b031029180108100e0106050a020c04140108120a1209030e031506030c0a0e0c070c0e0106030c090603090507060e180a23041e140f010f051003050a02 68
    0xb159410b03424080c8080c0c03964502030034800c2450300303000300054020300e03014181d0b10a1311400746052108203050489281114010714000da56818141ca040b810500030b82072080e8401d0504100d00002068054040d069601e510f007641c5418803280528071461085140307020114100e0110095101c4465000381d203014028180b0000341d0f941000040d00300f5000114551440c80403c06104a5060820403140006015120001102e00700001010400e000902d180c480c3da038006165020030140d80c0c030041c0204850702c80c0302841d584485026000d030030000041e0000a05106000911a21038042d0340151904240580040c906000b0115244a80c00c002c4581203188508040401445000c0c45480b800350010002100c2c60400760045088400140005c000480c58040c44080740041c0d0030708110340701d481003001c0400f10514000210030701006005219004004000c03140785410b40140361482ca8102c000c10040e03483c8040d44a41488030301000d400c541c4060000310040c2050504841d02c05c40d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 284131555 1250 284130305 284130359
    0xc110703080d0f020c060a060906180b03011b020607020c0f06030a05270c04060603060e15010c02180a0e0d02030717190c0302011a0f040f0f06090b0306010b0310 71
    0x103c03040241039038405a8120140e13031120041140700c134075920031207024012114091005a180c030083c4038554000020400c001540c5000c090001c2d9002d5004680c4166101403c05c03946542c3d1501a44500c021508a0094001d504492a81d4900b480d59229680d00007030256065884013000040100002401c0c003440c003000c00000120041095100f04100d00c280c00140480f1805070184000e40d02c0c194031000915080003014846142c102002e21b43c020890f0030450180c0078a0030040742d821980d100044e4204d405000d6a1014410860040d8854140400140201b1205400c039594850761030390030704c0068109106500000d550606101d0401a000d21207030304004990310003800c1c40c0b040d41ca03245c6c045000c5000040805070203001d044442d802c0b51400c80c40000030400420010013245094500c1556034143d010001d086c643c0c0b004202c001503010030404640c0b180ca40c24010010040614420300c500030001a4000a41045904c611213000c660840f5518245007166104c4e910302c1040100d040e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 284132805 1250 284131555 284131571
    0x1c0e040b100302180301151818080a0c02060703030b240a0c05160806041a0c0d0b010302220503120f0a03230f0a060b0712050306210604060c110703080d 67
    0x45d090050040b00e1800128a001451405042603100c03040b8141450425007061380c00403600c0040103464144a400c1030700d03183d640e41d24000841d00e803000780c0402540a00003242103000d040e410751002003041016074001101c1c080b03a0401e6510b10007203032504030a00e1410002c1070387d1648224608101c09124a044070907084031094145003100241e0040360280d40504208024000316002c0006901c00d954080b10349810701100c2005207220b2003140004640d2a1480001607034402d42c1229840f0400c0d41d00410044911880e03941e8038041031240307a00c64862500243e0300f22520004a0700c006c80b000362180e182981c3c3d00016009081e1580585450000503002c00c2d1217014a00440341c482c0d10301c19602c209a10b4208008001c07128290012642440b01348003074800104202c9414030084800c2c00c055807659510000a80305049e420403032001011421600c00034420300080041c001c3d0301c20f00f01030000d000b0002048940c9001242d481015a01c440c900b0008900400001d1040740d50025010511f04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 284134055 1250 284132805 284132809
    0xb13020f040e04150b1219030e130c090f0b070f0519030e01081b2a0a03030608060601051c0911040501080d090b0a020d050313051c0e040b10030218 65
    0x28040300e040d2034202c0313400c004010b401e580c0e00c070380440148210740c00c2c1e21444802d40c4480d564003c0c100f044001e004240c040200741409104041854100180007403114151000325002038003481031000c000c192941c50100b008090311503001d0950390a0712501c1c0c2400520384a4540340c01408809440c64090b91001100200340104100c404500039103400e902c00300d00d0000180b82d8480207081c450503010f2982000200d0003402c080700e98200c0140c85640d40c40c04c800310b0000300803881180050b40751081042c05000c00d50107030006812142d860041c2c07459560754400640b2a8440c540301206100200b4011600d14100350380613085580c044c401c40f400e00c12401020408444003070b04a0b10715a40454030000f40c50b50300c07948000107403920001700350503d203604c0000b82da618101480407040c804007000085000c0c0c2c0e16100b108071a900042100c0300c4046445aa448002a1100080001d595203180014a042c54011900c038900098200b0904910005040b402508a4850181d8030304140085102035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 284135305 1250 284134055 284134079
    0x5090a030311040f121401050c222c0606040302031c0e09100305100e030a140d090c1e08071401110d090503151005100507061103070f02010b13020f04 66
    0x40c02c50b001140d45405654146000d010884840001b81a81400d04000e4045044001d45240340784110a110903001c059040e4a101801500603458034000d222111962241503140100502c00340c08038082652109014401d9500c41e600010303425074010281e42c0f01c0085038041c040c0b10742c041450440c0d0058502000034540140554200c00c0e010070420080c814040d0901809403080c0318114100101c1421171040c40e103901800c803401d028400c0300c02058035104c0c1e07010b0441c2c0380c0c016a1541007008201c5440c142c40400b016004030012540c01c0009221600c660107034110507941590f0051414a20749401c460506241010840c10404000401490088200300b4103070f900c4607503101d101106090106152a002480181941440441e010f0110f90b102e41103070324056480541c0c3c011b401869105040e1003134411550010481468421012088a000c0026502807581c0703955042c03a8540183c0100c0c2079070082000d095101c40080c951203048e0341940e0040040c10780c14420b10313040a0317441c2c1c000450 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 284136555 1250 284135305 284135309
    0xc16030309060e011704080d1e060905061009140a0902070302060f0c040308040308030915040b10050603010303021c03060909030201240602330c0903070905090a030311040f 76
    0x101e56648030034010950002c0f4641e0001c40f0a05e4907201c030102c8501c09541090740a8005030200c000022040340c044000d4110001082c0c0c40404091011030011180004105501c2070341402d500e020080782c0c4528024050b05640b030000d640e46040701c0c0c00d00c90319103404000c00684581c0700c0c4c205a000115410386002a0078164001e170050301191920b0a01105000001894114207050400c810710004441505503019240c00040d910b45035524100300b90b190024401106403034072248001c2008000081c503416102e440240f440304001c0f6070b11011f0020f035001c00e00000300981c2006021900c071082c41c0001c0d0b4540a483c1c030380440c00302d40d110003050440b05000b01c1500143d450f66085080b4255014480040182c492100300b20585000d500a40f542c000e280540c0c401802494039a00c6c50b202001304891030313030713441c0750f549a503042c00c5100942661004241074081d005800300014100c1c1c0a100d154841c0340200050110200075070b0303089006056004002130044014480810400a00240540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 284137805 1250 284136555 284136557
    0x7020106051507050708030301150320070803150f011704110603010902040501091d0412030e01111804150501050f1e07031716120f05160f02011a060c160303 69
    0x30b900c02c51404d0040c100200c40c0c112119a074001c200401402c045d0481100c211961442c00251001030f800c24580303140c40d44202e0000482002ca07940d03050080c551300540c0241c01032400b10300369212260500c18036030b040d08585030216200b0300d00f0030403d088141c003d41c4c0c0030f440f8034403800281407120002141f6400a810501c07201e0ba001c94140400d58000362207201809480c0c86082694540c56050712060000520040400c25044880707110140203400c0902c503094400000e011051260f40d8805084d00041011665081007400d01000b80c2024800c0b013540b0501102e4800419062800540d0b41e503001a0309040c0741a0204642e2001c60419001c0c582c08202c080d041c203941c1c00d00c0c2e05009011b907030035001041600a0102c24071008108405210000d048982001940c01340c141c0b180034024800460b0081505e410802002190000100005421255034840a40098080d10128229030005158032000c000321500412589828005014106040c400b119640001c0204080300340d0000c0e40110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 284139055 1250 284137805 284137807
    0xc0307120f0201060506040e150109030c0909060b0d050a06020a0210150602070503150a0c030b03011803090b120105090408042102092809031103120109050a1b08070201060515 77
    0x19007002d80c213004500050000300e4a45d42450300b403280240d109040644298005034000c00410380c40d900030340d00701006503003280b0040318840d0b4481aa030040c00035140e0403200e0f10b252a541240916000641c0c00c0c00c1d603040f0740200040b41c41559090000e501100d0200c045d403250b40035448000c1601e010b12001c0c2481420031814052409102910b0041c15400042c4030750003a4858000c42005146d02c5544010f12000114002109640a0b001448403014a5405509010400e2003a014003042000700c14800ea5400710000e90300c03e0b02100038001e540d500f000d11001c00004000518006a4031600203000d0301205107020b41d5134810b240311180c0080460101290a5030010a40c900f80700c01551041d401501e00201a40c2001c6440b1100048100b180b00035640b40002400d043c8a44a00c110035080441180e41e0b48108400b01188860248240107101b41440c002580341c2d0442d0003401c0c0920002e0300d52422000071004103441400c1d005041c0000c56503070b2940090705a84008001150162102c145 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 284140305 1250 284139055 284139077
    0x207060f0c02030702010512071206080105090c010e010504050105032205060115050406140c0f030309070503070f0510120e0604030c03080622150e0903250b0c0c030712 74
    0x14005072030418140005541003800b03a50003503600300d0201c84281c0100e510500050340d8007403041d42c840c0d003c103503012440d40c544440070031048015403015010b034030030b0400c41718a884104011240340c90401c0fa5035001070020300040081d135010700042e40d040944410941284405c03221446010504050140c4182c0d04c410700410049582c00d98a510380304582c035010389000e0624001901c100c1203003001c220074650001d03030400c50071010b108841408144100b5243d0b40d01700100311540d84c41d0700b1f001e1648240941340e400103000300c14100d000100c03078000c0c20b90360f18212020825201580c40031800043c413034840300b154500c000b041c4003551090b0b229495017100c460203400c00a01c480e10042c5181d0140c5174180480700300a80c100a4668075521140300810b00d10360719000350008011503401a17840c980f0502c1441019000071003c2c24400e20031380388640f415501d40042007640f0044c2080034040d07a50800c00f00d0707000e0312320324001d00d440781407881280e28040e081d0380c070810010741e03043d10b10000420001039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 284141555 1250 284140305 284140331
    0xa051b07052b080d09050106030309080d0c051009021c0b1014030709020a11070308030402032a0f062512030915020306011e031a01050c030702090604020904020706 72
    0x1110800851101102c440305014100c84007000840800140c031a050124840e07540810a400100b0750aa00000900106503a80b60113814a4003500030350449000c0c001c4032401c024802e0f000080c5d065080002406100f030700b20000d0b0000d10103280140d17008038144185c0001c0c1840b14071043c030307141d00c101c08800032480d042014041e04030700c03900840e10007091042403c0c0243d400150a40c1520303105000140d0740c0110b000d042d12a0254042140c420b40030721100007003480703c650050340c801c0d4000d8050b10508228020810414082244142050f407120342c1c040d2144d00b044d50b40746801c0c42c0080c1c901c51804000881c02c2010303090346030454100e1951441408100080c900e915000c2c40d41f03d00302880b000f0303080e07a1540440700445031b400400650100c00142142e200e054040000c0c0a4107000fa80550200038005000c3c100402036038800c2d040101501207554072810884050100315006103040140a5081000c15040a840d55074000e40030f001d445800e507158802000390303a108040c009500701d58840 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 284142805 1250 284141555 284141569
    0x607030509030d0f1e0e04061d0c03040f03120609020d090c0902030705220905071107060903020907030e070504020d0b120a0b0105090702030d0f0e0616140a051b0705 73
    0x204420000e41312040c2040703a0300101c20001d441040c59451401c032941a40071906415080c540d00e50043c02d110001404813040710360244030703a1401410150076515095031081c04e10040d20024420348103600d05c42d002c82c0c03080351003500c41e0881501c0030800340d030344810032000c0c2d030001c02600c0c04040d0f507019220300b000142403107400149980f0340154110701d1312080203880c0340140700d1034011008046400b140341c05011074180c0c0c05002c0c030150820003410b01510081c0f0031140c2c41c02e601483e205802c008907481d0b00400554003201e0303000b0010003a50751000011000b60500c1e0540481500c40c0341c4c1c0c0883c40d0b82e181d0000c0c10030000c1507440010551010020030003482c80544030844150056124100400e502100147c19100142caa202003502c450f2400c80c6035105e2400007111442c544044030b40c01540f1608100c07043c200d400c08403066501d4242ca02e0070710354a01001c1001040014080464040d649406489800013a0a1250038022800d0f45110395500b03490001150380c015900c1031049141c400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 284144055 1250 284142805 284142823
    0x1306050a0c0813030801060c0203070e0c0406090b1204170d09110a1a04141507080304020a0b0a080402010e1504081e0d050403020f0a050612060306010504090c03120c02060703050903 80
    0x2079800f80c0401c085450103804010103019910030480f007189840300307540f01007003100000e0100611081c80c5203096101c0452680060241200181d481503001032b01c0480e40080e2000c80d44250484c2681752251740e10340c0b41e2030300507003e00800c054007030004040040580c461503454a00070340c0c03c80c131a40d101408010008260b0303000044000c5182000410f40c0e01000c040d141a0b501070f5120003030500d0f5000000e40720b14040144000e009200040f10301c00c10210001942c055032003600c4c4040c1141d01c542d140c0b1114041e503944400050300c4100040d01546c070070b0102d400d41001c00fa00c1468a0081201241156805a0808030540d8040d0b100e000703540d0841a1002c6030303500484041d00002c0c41e00c2100402d5440380b844064400c0d525401c2c1c0c46a07682d900440b400040c0001425203555150061382c00081c0d94003128568468081e0500000d03560400b405800d07641c9600140d9107a90b1811507441e014620140c200010800100c00d00520068039008000c220942c025154281c540b0b00040c209481c100c0c0107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 284145305 1250 284144055 284144071
    0x506010207080a1103030c06010f050a0b0304150f0204080a03031b03050405070603050718090c0f020c13020711060a09030b160504061b020301180c05190303081306050a0c08 76
    0x50300810034184040f0f500840365601c161407050b01c0c8406030001e40b0358007c9510341e0240740551400056511000d0303024404450094401c81c0105035285a40b511340d002c104c501801c00b5601d070f01e40da4041286644201c0080e04101001400d2540b0741e001e0a14003100c8040403000300c0ea0300c1380b042d400c040b140402c440c104e00e024a003e0129140035550b040c0c9415144c4a9801415181c601040302c0601411012141c9a201001d4110150751640000081c0490014680224119604500501d880820503d4484c60081d184540c484115207402d4001e5121010a40d0f00701c1e070b24002c2c410103641d40b030024031007643e00b599000d10440c10b5042001c880503014000e00c55040d02d1640f4008403680080c00c0c0d03011a00306080255141101038500c00d000c0d410359400a505510341700c0c081c81d00038916109a81d4070b500030768102004075100c0c070a0005840714100c03c43d420010002d400c0001038401c402696100300103000d1403510035200d565580c141e50060f12141251a284c2c0010110305a204134115844640c0b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 284146555 1250 284145305 284145313
    0x14090603010b0319030e031b040c03050601021911030303040812070f0c0f0609020a032406030203070504020906041d190b01120b24040501140c06071b050105090a030305060102 77
    0x2e070340c0042d94603079504030110b4654000d004d80205240c01440031201002010f020f480c40181c80f541d50381e2810309440300a9100e1441e040c00e40c40318600c83c0c4580380c1b0512040c2c0080c1100002e028001104103030410044540070f01510700040710782c40c14000340d030285104500c4142c50b078a4600201c10012002400c210400c1a031300140d004003948030701d031000c400740c00a0450111000604010740640010180a50403188a00c1d0001c1044580c4c221001600b005c1a00c9095000000e42400103842240c031010754036a0044c041441103140039402000c80c040700130300c01440d06d0380e11071001610074002c83c40000d0241300311041005442003451200b00440501f02c040001160110000e082421b8664080c07810560340c55240b407482c0c5079012522101c10120f035005142c89082e0814060700d0380103020302070026099081c41c6c582c82480809490f060b40400d80071b0503072580c13028011140811404e007135090b000400c3e408000401d02c00e1107110f0050850001404400d452400c0203019101d01410341811540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 284147805 1250 284146555 284146571
    0xa06030507151112092e0c23030d020c1509070501020d0302040315270b04140706021c02070b0a0e18060a03030e03030708040608160203030c16020a09061409060301 72
    0x2c20390040f2170384a94110b80c0d00c1e10050454141c40d408241008405a04442c42c040040354540c2140c0c0c2c0e10000c3e4810044284800b25826243c5090644840301040c15031003441843c0104896402803c901c1d80b1001c03c17502c1c07140c3c448100e03011031a0250b4200200c1c0c0c00121061005580c1440071070711545075800e05520b804c0c030b15914030300c4c0d010b171901e407500101e6601e01440340281118000301d08807500c84140b0084298041c102088041380035034041740ca4280c5002d1002e0038540c0842c0040c00c0341c1c1d6507000f5000c18070000784104440a6485000303401c6000e405804520030180202070184110103a50710072060344081e040c0035181c011804210081c3d035600c000c1150941d500d40e054030a403545842c0004854030000c0200b4603601920700014065440071902007001079010201340c3c440c80d0100e80241030003c0456007030b030316880301382c9903524101000c02c102d0103607800d140e60403d50301d840a00b020f01c1513951612030404a41080e040071407400d01d003444512941c03900d0b40700036070881d404078001c2007016 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 284149055 1250 284147805 284147833
    0x5010e0105010c11090106180e0f04330903020609010e100b0a05060712091a0712200106092d0c0c0b040623060d0305030a060305071511 60
    0x460148503007070420243c4020704041000080d458000424040c0c0b6030310b855619104040c0c041902411030800044030b8410020b00300c0c0c01258214003460748050051040e071102e03241e0008000944840441403141c01e69500b200c2605000c80198100040c04002014038040c60f0003414610060481c442e581e0424001e180011004519101c0481203030b080052144614804215031034a01e511059100402050b03c0d01400503220324020114110b50314041740341c1d00d80141790941f0f030716201c5041a1850034088440000c001c5640c3da2030b40106403c10f90365400d42480b651041034550340b03040c107469441d03c0041000e0095800ba50140d031001250b103819188580a9061503443c2d0405440d030352070340742c0c2d00d056005401201c1c11074206030851018001851706c3e0826501500c1001c03081900d581c298401c168411284480603070181e0750003482c000c03002a080d20100c0e03068101422030f422490340d5075000000644108103040090032840700381c0004521015014281c1100004241c00f01d0300715a10b134004007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 284150305 1250 284149055 284149079
    0x627050105071d090c130e0112020406060203040e0a0507030f050a06080c12030d051314150c03010510030903030b040e0a12080c0a11030904020a1d10120b0f1f120501 73
    0x4141000602901c0e0a911419a104441b030b550080d13804500c404000705003821110394681c00240255030501569a03140e800302d07640d100b6031144520a2100602044541d0243e400c520781102c400c0c507012404c4411007001c0e000300c41095845d40040c40c0e4076502044200c4080c8845034100008032000000b1040d089061602d0b4400e40c200481e845aa4a0000384482c0c80104200c03209600003602c00c904d5040052000c1e9144500300591a21040d15400a900c080c1a00220783c142c40c80034141c07040001032014240d024040d500401c034141912101250500c1d1139910560420018032401041105030700e06184003100880f02d80700042081340790030004001a042c0466219441030302d0b240d050410300107420743c118020308c2403007640329000103610b000322a0b01c01c02d14079404142c0e5008400d4118031508001e205400070307020a000ca441c203540c0c814180304640c8444035043c0c010303054144082c904030025004411807015074240f9031440158044091340181c016815000103002040071b541080703418210 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 284151555 1250 284150305 284150311
    0x6050a0e070510050a050d1803020d020705060403031d0d210813020a1a0405060f030a0b01020109020a0b090a080a080a02060906010303080f0403050c16140415030627050105071d09 79
    0x40c010b0000d026034404032070b41d0107111905801c8d8100c04103100b407898025180c081c200e00440c014840d0302c101289500e409801c90381183c0c3d0503220703640c0c03030020115803004c0e555140316171642c05080e04150304042455107105902004100c0300b2040001c00350480076000d1034025007c01c0c8003945900e14840140c4a102010003995241c501449103041d40c400068020310954004c01e4004030081820102d60850b240a1802584018014081d0603405001207080f80d61064000e03600940c4424204207008141000341690300005d8002c00060791a554407070300e40b1300c982c213007150083c034001120082c81c1d6051040942050000d40900140d51468400401d07803480540310101041d01c0308042820103000344101d801c040215004c0d00c030030b0300f02d0348022411030840c0d1045032002c0204842c2c0e0b604501c3d00340700c0e40018107960a4481c0085003140c540000138946036034400708136031110b45406821040d2055416602c4d1150300040340a05c0c1c03552000344100800648440c0d100002c0700c0360102c1c0e07035811030142e40c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 284152805 1250 284151555 284151557
    0xa0b19020a0b28020c03040e060f030d030f02130f06021204080d12090506040b090606040c05120705090303040f060e0409021c0203010204050a030302030d050705030f0106030903020a06050a0e070510050a 89
    0x1204910040d0300d01c06007004505043d944c0c40001e14400080f0040007500480b030072840c41d041140e880c902032164038643d02055590541115100307400d02802680b19810361404e86d07400600701295490011030002d8650000b142c1e00140d20402c0220f10360402850140c010b0341446241802e10742500301da541c0c00030000040900402ca50b20640c07400d00c680c845c0134502d40217070131a003860410c0d00304400c2488007a622190540a4200090210b0505000c0d92021750305981e102031612169004144240c100548001c0c00c001c0c0070080709515980c100f001c4c00191580c2c8a07540b801072718001001d0302c0162440c156038001c0f42410740983c00760755103911802c0da10491000b41c05981c11584006802441981c10650f401032080d1004030a040d8000003504d0b85032404d00b010092912407e4082d070305070108031140001c0b5643d00303006000c9184a900581000c520a00454404000c5076440100766801110741c0440d40c4d5950103040400d0b07004103c400011b1000ba203103001c01c0d14598000030304601c201c0307032500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 284154055 1250 284152805 284152831
    0xf0b1008060d0b04120306060e01021510050d03021510030b0606030a060e070507031403090d05070f050712030f030b0105160203030d090503030618010608061e0a0b19020a0b 76
    0x107a1a854650720036094540c084100d1901d840c1c5071400c1040762038886a807100091400c400072441600800102c84a00c070305800829604201d54050b802031400104540c050000906d400601d54458001d03041040d0b109030058800d50f2810030741514000001004185207016108080021814249080b600304000360750081c3d4030f54960081b0b00c0540940e6002c0603000001c1c404000105900c80003800c0001e100741d5075501c2c1c0382d044403407c0241b40415202c200c01604514410804107014000411005101c0c0465041951164807000d08001d041c0c1d0000305444450200d100400d98016103500c1540c050342000c00045266100082083c041c0008840340301c0c640706040c0b01596010003c1d100701d8055604103100041c10751400ca43c036a08181d42039401900c1e0180c0d907010b460700e034400c020305859640e0348404036035540030300304051140c1944909080d00403000080b01c0c4c07611100207040180c000c85600e2940c03082d6407c4210109103400030000115007109840000290160020503084002d4061031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 284155305 1250 284154055 284154061
    0x702092a0c1e030904060504050103020a12020d0c1e0e0403090504020318100b1807050d05040812100305070807050303180411181c020108040b040c12080309010f0b1008 74
    0x4a1900c281c282d81181907002c0d042c80244020760000040107094401d03501031201d241d54030248000d440080c00300943c44000200180003241202c40c4e003258540c0010074003244c0e500c2d1600c5014072000d158014941038070b200c1081e0014484203204c40001480d24408491007480c254070020004010341c00386505c1240c00001044420002e8542231004440100c1969255a0803078a040020524480d459024034440c00700300c42d0080003100a64031440d81c07511080d00d4824800c1f1131400500f4014000c8441070401d00240c421800042a51440fa002080c0c1340707445c45055051051902c46c0907402850300e03901070700e0203101c551808001e50704c44642e0000740c1200710b4095400140a05003c03600500c0c0054003090702c4500c2660298581560402a206c114801c4c500714030402101020030000386c041200c172408034001400c1d590b40558845d00460001d8000c644402140800400000041d60411000310a02c1800c00d020b10036a410f81c140c0b84010000000040d0205005c101040030b2841800384075000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 284156555 1250 284155305 284155327
    0x50124110c18100f06270902070807140c031e153c010314070302061c05010e040506060112060510110c01020607120f060b030405030702092a 62
    0x104010700007000c02000150781030304101d03442c1e8111825100041003610000d1107802c9840e514003070300d14a41c2c88003140c000c61807440d0b50800100c064140c072001030880000d14400648042d1104074070480c401d41d80c03100e403400c000407070400480c0c0c24030150300500c0404015076000142e119112622070b6a850140107001b540c00e0401440c03d200c2640750b1024410420710380700760180080018800800851100a0300120144100110b00c0e0180100c025000500104450403003c0d400d00903c801110070700c1f5202d40c0410b4a42d04500c1a00d8008560100d401c5450305850080d00d0140c50700a58000d02c0f85060348845503a444060100342c14060b030074000c000b44080c1608504090030018103030704118010800004c1858414042c07000c0c4074010140180c00d0342d80b0210b1054010701c1242e42d002c001c05034a06901d4014a843c003900105a0f6407007a0000e038071074240b0051482a4080c1010315100e003003d00500041c280010210000c2403011150031544c0c01100c4808400300304454110ad854000ca00c0c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 284157805 1250 284156555 284156563
    0x8100f0e01050901200a120902030c0307090b12010209090c07020d0c030f02042301050f1201090813080601030b070f0e18011403010908070209070e1206010905012411 73
    0x199100040d420502000001d103015040214100c5e445214014143e0080c0100d4203213025240090380010040b000061203c0c4003500000daa060000301601c2002d07600c0c1000a29104681d03029803031807030325280d1070030440c41c203030651052428a04c8025440d0114402c0010ba400c0ca005185120011010610f2000d64030b070900300400c0c0035801001d4140d025101c0c10b04062404195000324802c9041c0340c8080580e10314109022851404041c9408581c0d09100401c4041c1841a20b815000001d041020140d00c400340541c105c010b018580c03d90350394943ca0028800c21000f038015403610ba003c4001000060020801c1642c0301481d403902c00b0504d00c00d8802114150004905c02e40c0c0500418110003c5400d15003241e4100d503800341e50b500481e05443c05142c240c0345c4248028013400c5081c07003500c015062100d00c0ca40d02c01d109160a040600720301c400540c48a0f10300c0d403403080c2d41d80403d005100c0c840292051501400020095031020030b00080c2240d50001480d50400404c840c0702198006d000e0104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 284159055 1250 284157805 284157821
    0x106020111070209070e03030706060e100518060111011802031002120106080c090a08010f0506040c050f07050304080109030f080f0c0301030615030b0c070b10030f1e061104050306070908100f 84
    0x50a232541e641c4207080480250603580100c0001e02040c80108010420060880c2c04564026102c030980c000303c00074a61541000401282c14031410300c12040000c203080c070552680001704410003406001070b0041c0b6103040010004001814410400110190080314009046454a01c0c0c850b030076070380302c880c080540d010710080540c1100480d007001c1403421044d084101088014201003106640740400c0100b83c464001c0c03150702051082055036103500d400d2000b42000ba00900850f03140c41d540c0e551071400c5a03001002540001c4400302c840e07200c1540200001e03082441000c50740040d090072001c907074492006100003006156164030031000d50440d415400021034000a010350345142c4528200740799408000d085418101400c001178407a9070307108200080d6500b140591403074120a03682d2021041d811104002200f5402070300f000001c2d401c0c041c000300009600e1445886a242500380351900c0c0b40648034005010883c2d505106111001440c0364141c00909000310703000580e1120040100160 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 284160305 1250 284159055 284159059
    0x3100305060a050a0e120d0f0204030515071206060905010c030c06051915081c200a12111005130f0b0702190c03030c1403070b09060106020111070209070e 68
    0x50700400070354980a034811442500110818001201e015440903203c0c0a1000c801c506440180040181070b5119032040c0002c0c00e0020300145000d8585d2505841d0031001e000724010a0404000c000d0312a078040125880c840c061300052001b1428100003820301c50043c003035681000340000c200c00506100700007020f6180d400041c200b05505001190b4107131015415140180c4500380701c4c680c88001002481402120f4451015280303041c0e1030f200c03070085050682844030401c59060740c0c1c0c2c0380100708260468100e1010300005c0c48185030310302d000c103100b00080c0170003001d020041000e110100004504454102c0e500d06001030255204e81c0a15104020700c1e20140c1140448100441001110303070390702d801440c1c81d8080f01e41901c0c000c0c54510001d40301c440700401000009004000180c082e00300b00c42a075100e0780360040722024040a091070b40e0004c42c0190b5a42d40080c0501010800c02e0045501604d801d10081c002d42d00a403007569614072030084000c1c0103500d2080000c0c80184241000a01ca40740 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 284161555 1250 284160305 284160313
    0xb18060906040615020f0d0f0e0405060301021207030b0a050108040b0402010c061805011401080304031e0c050d030206040b07020303010b070b181507300207050a12091406030c030c03100305 83
    0x40d180b000355520b11b4141c0d200214400e00e42642ca8a502411074502a04455600c1c1400e00300031740c0c18840a0a40076003c15055034003445145001180001058841c404d10303a80050341d1081c0740b003000340b9942c455011505108689041c0030101c1c6a50840b03aa00640a0034103d45070300340c0b07282c940001c128010b40f03200c205d00019100300421a040d080020416410701d20324540d6600ca0949586911a500c8001d14042c00051454601c421147c84501054000c00c41440c805036500007084440c040c5410031001600104200003c2200f4019895004001440110305640c106070b4586141d1180c0c5501070320381d42c0c2d144c00013141c4048101d41d00d030001c107580c0300380d072010b0000032400c07941158142e40c5280030424000000d0500c44503d03c10500c04c074400c40b00e070b04894180b4082c600003940501c00613a000c1c012038447c1c1002c61480b400c41c084c1c0d44410365403020480e241400c100511310940c21000e01c00e00b4100140f1018010b43c9050320703000860719040a80c2c0c1c2d110300c4036080d401e004640c401000c0b402 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 284162805 1250 284161555 284161589
    0x1051c06120215030105010207030f0302070b04060c0b15220b03030d09050f0303040201090332030418050c0301090534080a020717090d0213020a02010b180609060406 73
    0x1c0000340078180910075500b19583c03100c440f030035018a02090060398016400710400308007003810030214002c07050090058a02d5603490b039440c180389a0003038201c5800b00d0481d15a0504010740041c3c0d040e4012403c125485849a81c400080c103102c032804005591103880341050307904600d00f5400f0b0200308030014100d0f9610898003d481c0301400888900307455901650702c24804940e00881240c0c469a81607460310741141c00e50b5210300c12480c401d0014954140050700c0a0142034a0394400c0c8448103440317000395100da00d0b080d0300b020807100020800600780c1c1410f0502030f0401c80301d400c2e40c3c19200225804201680c44140e9103690300001403038000111003001007403200e401410b00c2e038034140d880740d034078006c0b60713034401c12401306034415503100400c480d440c6c545039a405007446000e0b0864550043c01c01d4000c01180d00014902c3c0108070890405a50015501d4230850302403041c00c0c1d80c50016113002e590402040c180868400d0000d02c068040c030050350004119130703540d604c0300300940311015104080300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 284164055 1250 284162805 284162819
    0xc0f08090304080304121406091f0b09090721021f140f03010f0e130303050a0e010e0601091404020904030f051603021501060206090322081f06050607020d0201051c06 73
    0x6110003030305a41f40c0c03826a0301c101c0796480203d2071034440c000c03a0b40200766450310011010980e065555501e2480d80d44c400c64450340f551468445030180580c04e00410040d401d060059003465000f80780b61244001d03c152440041e100c49001c0b9640422040f904003042401200c15203480b101040c0324180c00c0000125040d0312190034002c1c505032002901c0e080203a5481e010000440d50013a00c0300191100101d81900010f482500910b50009c01c1490100755005c5107060b5500703541440842c041d50303400080061003002c00c030744208418400e10b072000402d01d090036000720b0500040600050100020408400009409403085540e10141c1032841d10200c2150300b4006d4440361161000c0c1030041040c4000a98144000303040c50182c040900034616041240581e50007032198011054420b01c42141d00140022080c00840025485141d140c0035140258a4410880d802c0390090303807088009201d541d000d61903290185001d181d0a003841d0b0360b203c0b14004103040310b8100c0300fa440301050030000040340075 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 284165305 1250 284164055 284164079
    0x40b04060c05070f06080411010c12090315061d0702031e0c150f01090902010c0501020a050306010813031407060b120d1214040803100b040915090c0f08090304080304 73
    0x400d0150081d01d090f0783d1950050981c00300c2911405001a54074004100840e00c40700034851254814140350094885c0c903620f615210048400d207102064582303008000703202050303128049443e0802810006903050000c4c100442c090304840301031401da824001b600681c020003c03150745102d0304121410b6070040e041080344030307800080d428816004c0d021000d120855613112507400703442c800d9005040d40c0c6c2001e030480014000c0d01e000340e042080c0c0b0300d44030740031032000e05c0107001d42039081ea51030f681c0f840d2510015200350700207440d5003042d1040c0e043c0386000c65403050400c0c101039000c1c0841d40c1d980440781803102c050f01503520600d0307000440d010790203517803000015419041300494071001058045100c00340300300d03840725001e030110b10f164100280004e1406002541c0c0000c1800803004103603101c422a880c1d981042c0c1001d840c659803240104000f040103001e11004000c14007007401103a030000f070000e0001c00350fa038110051003038400220758401381c184142e40207032480c6002c0340d440359600d50203201c00c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 284166555 1250 284165305 284165327
    0x90b030405010c0e030303060f040f061212030b0303030709090f020d1a03010c05070203060606071a010f0e0a060b090d050c120303040c080a0308010e040318080c150412060908040b0406 81
    0x41000301c041013425043c040152441220001c20b100210f40c0b01000f407101914078203404c00e04080c0d40356000300b80c00349075641c058011801101c1512690401d44c0014080702e5804600a10070381c010f00400c0240c6070700102e00405c3d01d40140c00800c40203000709824000e40a02c950400400341000701046e985524554248801d520440082c01896107000058440d84503c40f0b0281d059044680050504e040200042a003a1700c43c04103041940589840340050340f8003a0020315504070700350410481311800303419490f04004900e034200082d600d84aa22030480c0700300d450240c06140060980001d01c0f4050003415007800740640303042c1038031000704001a16940100c1d0121100855160007040e81500014402c541c00c0d89034440c0480c1b0390810301d00403901c2c0c400810407020000340e903004e03000c00090881400000c01c020b0b40204440b40c40383c000c00100000c0700041c6803030704001384410094600c4006030b8a0b641a005400018040d059003000c00340d5104a420100544070000b81c0000e0050b030204003046 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 284167805 1250 284166555 284166557
    0x30201060501090812160b0f0a060602010c0c02100e270c0a05091302071712090a02011b061d0313061e200607030c110c0a0312090b030405010c 63
    0x159a21000103540f605a640105019603000400000c0d15025410042c03180130140c0301030002c48811540d4452491404035481c010212903042400b0122151780500c6024052a00081c451800040401012820840c002070303c1405101c8601030120700490030702c5c07890b250140c0f07510440728041440a10071000c54152140707261806d00000c44440f04001551501d0302d10395140d030b2420b21804100208a41c000e00040c500710760030081600060010b4910030f10105810302c506407540066001d509580e500241000801d4000d0041c0c040184e81c00a403002656403242111141c04442d800c000000704bc106508150750010381902c26042c010000240020a0144511090883d261102114500405422080c2c80101e500000501d280920010841285c125407550041c0d24800c111130f02c0e107001910b885011031ba4502c41c111525a01190404050075100020f01c0e0b2801114049440c601941c03101034510100031002350800740c801e003015001410118100c80d12070070141030440c028164003080310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 284169055 1250 284167805 284167811
    0x10c0b040b160801050303030406151701060501030513052e0614030c100e0607020d06020d060306061205190303150b120703050c0702010e01140417010c030203091f0605060313030201 80
    0x841d4803c14000f41a2200600618156126035462602074100007145c01c5110010791404103041070301c1c0001d482d82090f00ba0001c15898909000501144c2d000b80c0b420701c2c8094058500404190000740c8440b0803101c0b0f8240c141c41d4204070090140c10101129031070019410144002468128000c680041d41c000300e0650300100e035084104620140c010b04544042030341e009502900c4c4c41c04401901d00c07507002806000c005041a9169000c80c1d201400c0b0740c140c00d42d988414070034007080344140c801506200d15032540d9824151107296444072102c45069410942c40241003c040c400d402c066080034056003641c0259450b03c0440b46c103074101041207038044132003400203019584203000700c6001742c0b40511680d01e8201160011a407801c03400005505120026152b01c13210480140100010003680d111000308442c0c44004a0a4075021403410041500600601004500100350100c61022522000000c3c2d010700c1d100d440a050964050365101002100700b14a104c0c000c40500b415900c00d9000b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 284170305 1250 284169055 284169091
    0x7060507030507080f0c13090e0105070f0219060207020a0e040302010b1f050a0908070602030d06050612010e04060902092409070503010501051e04030c170a0f11010c0b040b 76
    0x4800710340003100c00f40c00203a44900031950f20082c0308090740d000000420710350700c5c22030601802071240702c1c6c641c0b007030700c50b1a91022550840c12081c07099a070885280d25100c11000e0400c00000c0d07503101c120240d01070348495031074580200a1260b04a0b009158043e0030000300c982e65117000000c3c00e4044800340c026500300813038030499203020611419507204034100211010b0304080111a190001501107003840900d4201041f420300801c03214009240340e90003036544a21401c0018190b03209a4040c50055000b403110b801024814150a070643c0c401c3c00450b5111358550500c1c002400d0318640c0070313401150301c20903c48580508041500500590746400400705440030070300140d0f180454034000042c01c180018070880d0710440007000280c005110f01d01e64003282d002301c9000c80e402588216440c40407007404000020300300f0311082c8130380844400703003000e0140c5031a02942e40750b8104000701342d03040031402030030305a00a50700014174503044098611540380c98600030300a01c0c0140e40000f90400c0024403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 284171555 1250 284170305 284170307
    0x30f03020c01020d03140a1d1006061205010e010e0408040e07080106090e0f0412120e150108031e070218070c060506040c050d090201020f030309030d0b0f030307030c0303150b07060507 81
    0x5901844820407000101942c1c0d42082100240440811042d03507032318100600550351000c00c68a120040d1011001548501d0400040e0041c000310540b180c10500385001000542c4007070100c0f50444003c02c42040841d03aa5140c0180c070344c0b00765045032443d03907400c40500012561104106040e503055854030a13595445184000760400704403041d140c4100244006000150508102c20002282d0b0500e04101e120141c0c6000c15030700444032a481a51043c204400c8105005151500402c0307854040d507d05000ba140383c0409001260514401c0040000d0b11021901c81001444025119100000c91420108001050392408183c103803280750500001c1621841c0921881066020580f9003516001031110334502400c032460003a03043d80102c18503212007100c2400114441e890403400386a8030725000d46480c0484101c0014039008080c200c4a80715544c400204880209400d81000b034103001483c0b40403005014a0306200e114a0602500014904a56005424110310442d028803080d600d910b8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 284172661 1106 284171555 284171561
    0x6150f090b0301051302030a0b060d1202030315060c03120901110c0619111b01060b040f0305100504020a030b130b0c041e0e150307030f03020c01020d03 67
    0x51008100e141c00e20031164005801d03400100701c04426004030788d9681c00450018024403002c40441c4542e9912600b848009901145201500c113000318003d48030342003610090200d941540010185141000540e4540718000c0021801c040030090880c00d83c0901501da48180e540c1e650400c150800e0000046c448a40c0c00c400602a03800d2080341c0311034220541c01000c0f4074500d400c2a04600202c41000c40e400c481d154202c129a65141c00200390061256610203407110034009400584040b0545121003100c0c0203105580c580044000301e6400e850302118000c0d4080389071441480018030607003565801981211b5000001241551852002c03041581c00780c6240038041010032111130401d1610007401441050704242c1031502c0c13040c030540c90014124022621508064a400c1c0c0c500300801c10080d5000710303c1c1c409100290a010f500ca41c03156000c9401070040b4040d0301007060080c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 283992805 284172661 := by
  have h0 := BRFrame.cov_init 283992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 283992805 ≤ n) (h2 : n < 284172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
