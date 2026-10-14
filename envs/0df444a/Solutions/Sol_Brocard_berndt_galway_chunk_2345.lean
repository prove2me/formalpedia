-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2345
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:25:49.496592+00:00
-- url     : https://prove2.me/submissions/151bc524-52ba-4241-a02c-c117a311fa43

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 421582733 ≤ n < 421762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 421583983 1250 421582733 421582739
    0x3120705210c071412040803091305131509051501090b121515130903141305040c0c0b09070f09140a05070e030d080103061b0507060e030409111b0601 66
    0xb00c1c65100f110006050080070090134200414200003c042a08400f650283c45690b40c000655998000348115445200d841409508060701482124800c0b26101800c004400e41c507200c0300040c0e250025030b01409919150001c01040e810000a5a00d80c94000b51240542c0b5015010b4215131400b0600c0307201d0230300142e1f454810311002440d035074600c2c42403030f02e009191527520500310100d15079074501d82c21481c01180d80d400300700d1541c00841a01c0c000d44810020070074074480c0424911500d0009500c2184200050046040c60741c07000100362400c0c00c0c0744040e07210f65101c1d25220303001192018199031001c4c5c0d0034072410b12011444002800220024019810346d2414a1801c003c0180144402942e0b0700c001004a8811000e4506000026054a041030703c00100184103441c01d0005840003030400502c02e4840c0b00e20203510740441c03281c1c0c2d11582000701d5680d51101070510100a00e0b0144800c0c4004034804049109446103070412010041d9240b00405040c4050090280c0d03000031508400010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 421585233 1250 421583983 421584001
    0x90f110f060307120612050105041406130807020303130b070c090911011b0206041409090d0e01051308060703020a020105070c020a050d020a091a011b030219050312070521 75
    0x9642c018400d424415041c02d0071302641e40080c540e950003814030079045209001407020660089005034014000a0081c081490b452940c505083c3c03001c000c58040c9401040111306a07801a006051008082c2c920745050401d241c4080c4403160090160b480000031440308000043c3c080200400c0e90b050184805c046a0b1610f000318140751091038140480500d01460700c481d60002483c0495000b85000c1d280d9803203a4405906285a00c2c046010b44d101c800410340020000031107000e6990300e44d07240c00300311130b400e00119020303023202041c591440c0e00e04801181c0d601d010311900f80710300801d541c0142c84000c4c20700001d09580000e0305480030300203240c00000268452034000d00c2030b0ba030b0503200000000c100d4404911003101c0c0d58072910400d4079005503500c00342003140244a420600340e8a240e202140801c140f0f00d4030110394002000769001400c803044641481258015060103642601e05000201506014020089804030006540010344c10030440c411480c80c412140c9007030410615240200f41 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 421586483 1250 421585233 421585237
    0x15060c02130b0402090d0b0603120c120f0f0c0114060f09010603110903030412020312180405060a0305030c100e19110604030c0305030301050907050c0d031e090f110f06 74
    0x41c84030658a607014810952a240c0481d8845200500100c452240c0750402240c4c182c01034070f80030303c03038066503000c00c4c0e200c0450000d9078811480d11001d0964107440030500c0c2c80d02c0d44101241e0b00718910900c0014071510300070020700495440c10300007003242c4200d444c00421078000102003501ca2000384281d03000c1c41d00c454a04906481075418001a140810603103200d880c012414440d6240c4000200454061900c03c0740d5072142c1c0c426012100422008074440440307000d844440c518541a1301c02904c030524107031704150b0700603001401100c080ca4890302d032241164403078081c0d042994090018010301d800786100f0200b40d07402442c064100b01448444000d9103200e0008003404c03108450b410300e03000d50342c2e5200700c800441e407142008021607568a0196200c0d042441601d101300c43d44800100c6440c001d500711030a24136100040c080c000003107401070b4014000300f100401c940c0006040545020001e105145007180900396500e0024581d2404800034005500b04500807080f1401c511655102c1c501 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 421587733 1250 421586483 421586509
    0x5160303020c091009020c0c040b0f091f0b041e06050a0c06020f21012d060c0614090a11061201030b190603030f02010507020601261f15060c02 63
    0x14000d00035265111341208810142c0c020700400c0348002400e08080324005110b0303020b4a0261000d1115640d10010881e81401d68002c0c9904180410300141c40319828040300b4045400b0805600010703034031025442444d070400c1d00710341c460000402c0c0680982507025140d400401080c0341952504601790002814401003640081900740c0108205980150f070800741c841c0031480c2207a060300c1d0b400501410030b41c1306e1b081c89030411903d00911521402c490705107018a16007403041c104c00e1107600e042011207a09001e88011f48940d0354aa00008800c0c0304051413600178164900240301001c01e03400c2075010901140503443c4103520800c0f000b0300e044c182e05000c034110fa0700001c6001155907111080350358004c00d41d6030b650066203031260200805402122007000b0300e81b0340e4000c1055035542102681d90360400c2c082d604c0c03007003c90300200203000114000c4059521525060f0350b0f01c080c0403000d0f101b1042080c9135001141d41c4034980c2c40f1118404c02e0707001d07009107481d10704060100c2440c1c0120701280d241030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 421588983 1250 421587733 421587739
    0x10503030a11010204050d0303021e0720030a06090309051c120f1106070210110705060f0702010b03120c21090d062c0606010c1a2502060405160303020c 67
    0x2002940e1500e080d1305079001001c1c060408030301070f2201d16000b0029403200d00030740c4031104100b603c000b00303110800503103440d00d5005264071164911000e40d10407006046003c8d40d0300d841003040000001c2d01301d0107540707c081d01c41e4a607500c01d5070504040150076450007000c869002c0700498400041244139400c0f10805001d0b051a17491844c1d51941103507140501602c4000501c84c941c140410640c0c0003541e2100c2c200300b54000c01c5211203280240c041841054000740c0300768003010105400381902401c554102e0103d000018844004d000800d00f030112142000c0d03c02d031804103001207040000c0c01410240c03c0c00c502c07410310880c401a000c4003d40141c005450181c5a000018420020640c1c054006c8088040182c4000303030000c500e030500980c822000b40c40c03034001c00f00862a1075001d0021001100d83c0075040e0a604030395190340d02000100201420b858800c000e03084220403424410000b45001c41c2e41c05480c2034602410000d2510641d142103240da160900760801c0400d50101e5075001c0e940c411 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 421590233 1250 421588983 421588997
    0x11041103130f0b010e0f06060a020604060b040b030706050309280807080d050f0403021c0f0804020d0606030b0411030c1005130f0801020a18141009122306010503030a 73
    0x42d040c491502c80354080000c224488200c000300e02070001680d42407080e81d6101d1350710310359603e803010311055000e8803d944002d60310103400700380064903603000218852005800050710300e00107400a0324040300c0303904c07940c0450800400d21913908014070100c0308000d003200000904048603006490401803000010708040e002055020401c80c000c4200d413018007195a081c050b900300b050f84950492400d8130110094070540a8080d4413000c05000303040ca2185a8131440d240120100043d82c04140080080340d00411122069001420500c1214040c60150159803558a010300d44104008004c1c6081d80c4241d1140210f0b030610750b12230418044602c41031600c01e4941d4507000b22100d00038142d422428040d16100350200d5100c80545c05001040195a1000c42d0507440d5110400c00c041140560040400140d24075a02400c0031506c03062480721b01c0c0780001e05d950762001080070700100c40e00c0840344c400d200106d84003c1000d0310540b02003041e445d40549441d5241c50002580c0b44101250321044c1f11107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 421591483 1250 421590233 421590271
    0x1503070324020301060801140a0b041703040506030403020a02120606090a0207050f0a080a12060b0313171c0501050108062b1a01080f1614040b04090f11041103 70
    0x403408580c0c469050381d1095440c1c0d40c4070100580f08150901840300203e00444139460207207410921202141c0d03454801c20701e014140401c4081d8000116500600d91008020000325a160440110300c194066030151001410b64410410101c4070b40080502d03d40c400001d0050590b221007140780c006030722910060b600c0d100ca240403420a0000c2c01c003000c40d030041c0c03c0500d05118050b402072800107803594400c11400c0d103160070720741100e1860040250f1440e05200040c03501d141c81c07006140590180c004044030a1210300142100c0d440627010f052600041d800062a10b40f45014136409088242046c100901d01440844c0a400c4250400110703411210380d52607244407081903103c0c000e60050b40d0005240f60001c04205004002c0c0b1500c03071580711301c4020f0342c0c1007140800c0450316002940c0f2ba424120b490074070070b2461101d00403540c80e0703c5a43d4941c40025075845103c2c211000c1c2c4124824540d52036181089890f804402c50207a000e0390031714160740702e064090400c680d48076181d40c1e030340380c01051 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 421592733 1250 421591483 421591523
    0x90405070c050a060b01030509160302060f07080a030e12162307060c02030613020d0303050702160311090610170a0e060c1306090518060409150f0515030703 69
    0x340714807020b0428000e600d80c1d003041c884e80d904980c1c0e012038283c0b4140702c00d8542c0c02c001c40d0f86a00981300c0c11a0306c03070a1182880145030031401401c20f0300044001d0340c01e0460b01d485261032640f1819001d00480d644a00354098503e0901802003d215402e1615080104000681e041d0702503d2000618180901079400b4105400002429502039000201c0d4466134075044d014040c07000344c481c02d0703109208050000d948084000c3e1001400c40e40a08091a000c1c0f03540c0c0c003a0b010745000b41407a0305601032446c1183c0224040d800e0038000718000c01c11400a03d01c54010300c6581100a0a02405141e020300944019508840041c0d580c5085c000481a07030340d2160354100082c550030b80302444078041e20b000c0c000b8030b081442c05002e10042c0b41c42150300c038580c0c400c4161a07017400d81c4501e9410145070000356581d44c500c0d440c20340d030000d030150010074446915030b43c0701006840183c080e03a0301941d52414030105006841034650006100303807400b088503650000070ba41c40d4114400248560b14074010031203440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 421593983 1250 421592733 421592747
    0x30f01120203211803030306220204030b15040e0c030319030f14060a08070503101d0f16060c1a07021002180f030a02012c060418050c070809040507 65
    0x5400c1020984100036802075490103a02840e50303105505408440d5440c1480c012080381c1c015a801081010026000b0000714600700089c0000f002c2c0c59030078000003000c11109030380c00307104074152280c920046c0c3c00c40e8200310444203055820a11035100541d0503901d40c50003c1221002010700827040c180f4110000e0032409050b2110840140c42c0c144008681610841e80010b0702a040c1240c03401d2099454100741c503a1003055101d481ea140e440041c43c0c1c040001d55a1040d0460f0040661030500d050140e00000c4c5003d4200b11003200d0351307004140c0f22202e1118504400040c10036031a060f01140026140e0b880c3d03130440c1400310740015600b0000b052540d4003c01c244080001c1110703040d911084840b0b24452500c2c16020000c5c0911142d101c0340510745170100d0150f460a60503121000281d00c80c03000700600d86412034000200b51640940d0840a80e20b506c0503200428045d02844101503a0700d4180080c2d130b1025080710000001030003050b00207040761050700c82c080c80560b00014541d54440c4200c50072 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 421595233 1250 421593983 421594003
    0xf0c13030b0a0e030f0c0708030f0d0b0a0308070b0603010b2205100e01060f080135010b04020c010f060605030106020717031c090501060506090a1202030c061b0f03030f01120203 78
    0x34400020800b12041c01c0201805865606400390303030152340e8501c3c44584070300c140300401d00168400c006d0f008104c0307955031018050071806001075646a8495440c001035902400302640e015007040100049440c0900524061040942d058004006440c0d0488080882c40d02000d146940340c1c000038680e40280c2d0b420320f000700241c0e01c05d0300d41965102c002806c1300e00100c0e0b80c04006000c02c2c001054140d09420074408003145140906015003000740e101440720365800388901d42d5501d4281c20350300b41d0385d2800036081140d186000001c18420815544049a025602031030511406000400c04150082020012a1044100d080d5000e81d0100e106003540b04c0c050f101c6212021664564201b52125071100c1010b42c4550700801c02d840d29102084013070f000e10140160700030502c020034004015900108107655201500315038018800707100180e042c2c0c000007205181600404480410810200a50804021514095451418240503950b40c1c00070501401c0f052a440001c00700454508214209034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 421596483 1250 421595233 421595261
    0x9090203151503010828020d023015010305060408130b0d06031509050c100c060204030f05100c0e0f030f07030302010533011b0611030f0c13030b0a 65
    0x1550207030b54150046800c28040d01c0c80c107214030f04444103655503440703000340f02055100c00c0444075440e981c02c10041c4034115200326081b069000310740c0751030011080c842000d0002e821a8503200003110300050715180c2c00b41d0340c6c03001c100c100300010400b00708081ba070984c019400c01d0301d140e59064002644011480c060b03110210030480080c0790f201e004072991121041e00c1c402d0f16004c5241c07541024200680f040050040c020ba04290f00c502050314211817104000c641d9400c125040421a072a820200c0e04541d0007929050700c0008450300700f1805120034050034040100401c82c0c4803541900604000c0f140b0303510307802480b5210640103561340800c07151ba15002c40c01c040f075034a16200e1500a010780801c1d6001140c084610022a402400035a503000203a00b034100e0307040707106001400446151062190343c407400010041c141300841d00c50f01440c680391240d640c03825034a00f042c2e8910041d404008290b80c25107a01440300d9141e01c02c1610901040744d400150f400400d0f1180c0042c4402010100340b9840 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 421597733 1250 421596483 421596499
    0x40308060a032001030c020c1f030605060d0f05010f0b040915030b0717010501020a030507080912070306060807050618010809031303060e0705220c0e0402030108010f0b0a060909020315 81
    0x400200341c00b0143c0100d42080c0e80074480f000038a041a41d0310285100210740c408404000c041d800b2248071140300d003810311441e02144055440303020a001303603c24410b4042294996003e03000c2c0d1007060060380d0040c00d414901030681843d11401400c24012402424041a00c0e0002903550791503805c41e1101a5030414422082401c0c10403000c1c115110711901c01d900d04404000000703040d800404d010841c1340d01602c0361490003219070b0714440d15512601809500800e500c0300010034410030000750014500c81c8400290007030510050900d04000e6070302807403080208120440ea0381c1300740d0003c080035040c01c4c20b001d0281e85031083c19500314040e076080c84c2e1819140d002c000042c800c242c4c0141ca00c207150f401c01e8803070460720303402400b0b421070f42140c85a581801e401c1c0c1602d2081807561180c0485911840c001441c202c0d40c0c000902039a100f039000a6250f911009028042c040e54460032140450884d00b18110900c0d024006d0080420307881550491680031000820f40b10b03030700f40007148140004040794 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 421598983 1250 421597733 421597763
    0xe0f090703050603010f0203060609120f120c1204050d020907030b15090f030f07061b0819020c0307180b06040807030f151a0f040f0615020d030212040308060a03 71
    0x4000740000c850044c800e40c2403c000075050f80c1c00c1e00c2200d0203050040e1400e4130f031075807110174440c2001d540724224000c1d20400c880c3d1100c1c0e80062160f400040360011b6059580c403900e83c2031510740144c002d0740c601c6080003004100000d9490118090b442a4183d682d403c03195a007010a600034410768040a4005281c40149141c4100c000c00900e21400100c84842d2a80c0d1b0220505940d408000f8417843c480d804503100b0f0094500907070b021020030641d00e041008211441d500c10f84160000d211400c00e1f5101d04080705e64503a0144401c060b150015801000020301e04040100f103807468809182c10a0f0fa950302130100c9480d000c0849000d04031000c12150030640d84c3c9007105464054603005d07641030081440002c8401454050000920380c001d83c03108101d880101042070102800e220719a0003a42c40115014040450091800805030303200440200b089227031001c1d05120300711204a08052040050108940901e400941c00c160185880600e954800c004191b9020494001610051f2001302c11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 421600233 1250 421598983 421598987
    0x30715030f060f090e12070b040f06090302150708090a1205041d0105040b0a031212021204030905030c01050f1207090e0903040f0e070c060e010b0d0b0402190e01060e0f0907 76
    0x4040300c880500c05c00034250000091178403041c1250012900960810601c0c000c2645000041c0e0018000d403030544d244c180b965544800ca0300600720850250300904140c41c020121601890b0f0f2000c07190802103a90700d4911440c82e04c031030042500030400b659070002c4a0381140b00e1400e84010349031040b40007a50a1400036080c134011310034496030303100342d00705000e0030300f6420105000d1040301e611082c00b0302480e1050000f07450700d4460500c40e1841640c00e001201d140300c80c04200340d00450180c0c81c1c042045003000203060400351010702050520400308003c0384c60400030804c440e00041c420304000303802c2c0c407034107011510002c165000c0c85c801203c0d0424011100004001401103500311480304444541d24801604c1d841c001b119070070082070896640101140968000000300c004020001801d1900500041c40d09404010292940300c2010304000c11400e04101c948000000d130b003011210303035141c5181d210f0000d60500500d0208104460503502030f40b030710650040016001040500c803890000b01c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 421601483 1250 421600233 421600259
    0x8010e180c030f070f1401050a030c0e1e030105010b1305010804020a030f0804060806040c05160c030b010602010f0e2d010e01020a0509040f09110d05150903030601081005030715030f06 81
    0x5e0101d0001d07030b00c507001840721810041e20076551810784985003001c0c8406000d40003082c151900c001480200ca40b2000c06580d88a0400d0320711100140700b2440d240300c80305160856005821884102d10704000d0349240ca0359400c0d016003110400d01e010320b8079070359605c0071410141080d0f000511850b1810b04000412040c81c01501c00d5400940da560f4075643c680f0104000e4415024100d008250100081900034400042c080c1c000e60080740149402556903a03000c8412409070701c0400143d548045581d002c00d8540148001030822000400390761800215803242941c0c4102c0c1c40c1900304440c4c01d03c40070039808ed000803540d0350040d0021911189010340190455002050103841107107030910160b400c80e40762003081c0c3c015802071403c52001c5081c605020141300515020b031130034465180c14155608159400c82c3c0304441c4807010355202c1c10304500151441d41d029015201c0002e5212051000d51400902402100c80f00c401e4a445411100b5056004064081d02d889800782001c6c008900504201c01c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 421602733 1250 421601483 421601489
    0xc0e0f090a0207020a030f2904030c1205130305030a12051608091204060309030e01020312390703090803040b030a091e0b0613020a050304060c1704060b1008010e180c030f07 76
    0x300c2d0820300c8c140300a51210030380304880060104480c52a43c0700442c50707101c072003090601242071043ca4402400800d0305186807030391040302e2960001070a4180d043e8010a85100f1903030080c402d00c000d0600c911840d24031007184083c0340030084400d00181e0710140030800c008614001072403103079903151034000c014090100c80100340c010541c0b50001110551001040701c18006d440a423200d1540c41d8044400314003242c2140c08402c80300001035102d1888403008000043c0c2100d0b01100e6920b0a1500c0c0c041c09400f820b070b0084c409a00180002c120540381c642c120303a4071a04441c400140d03c4082c0c9000d900800c0390200032010468445100e00400111104c1c66009000441e0369402002c1490488001c0c0d105013204803002410a00104001551541200150350403a040003a1040083d1000b2220030360200c0b000d450482c3c445804611900b04070303004030320522141c9041e072950346c1800b002c802c031a01d001c0d048002034500d020380c222441e03030f007404980d01c403007070040c180c407082207445034613a0781e8080c240 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 421603983 1250 421602733 421602773
    0xe011e0e01023f0f04030f05090a2d060c0809060d0f1a0a1a0306060c151f030f020d1505010605070201030b040c0f080702120a030c0e0f090a0207020a030f 68
    0x40d503d0040700fa5442c0c6120310807604580010910f41d500d6804880300f03003541403807070180181440061000c0e42d0302c0040b80040c14070600d603034200b4095800d84010031030001d900200b1004090400b8440d0036400002200709036080b014260303640e5660000b00301244101120903400c0c510305000d140e481c0c10144c002c3c27a15000d00c010b80c1c2d41c103400b41100700300484442c1d200700140c001c00d5041c61200c1403440070155a001e00014045420700880300007050502e148201d41724541640c41e001c0009040a0b01094165205602464082203086558040204c1c090040180c8255030441d400420400c0e0b9a40003855580540b02c18026543e444002a1094102c160228040b80c108001c2204500701841802d501003581c1c1d407600044004203070b0586407100003811007001c42c040d400260114800850080401e011959400101088801c600800c1a076241c24000e10602e0030340c003070190542c3d60344080c6401c45103149005988a400340b00250141d08a540f00420f007281c0303080441d0030302000d030b02e050364001050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 421605233 1250 421603983 421604077
    0x1c06030f0b06010810050d11040c02150901061409130f052a09040201080603030c0604030e040f0e071a0c2b1b06020a14130305010e011e0e0102 63
    0xb07a00645210300c0c12141c0413415509440c04000510301000d08806c03850141500044941d1010081026110406400c801503401800e688058a0655110681c40078070380000300304003414195903102000285648501c6240c500700410b140461821f071840516501452010f007031031951030640d0302c4400c042a40b18480d00c00d111225291030700d144030b403c1844c030700400b045901e540b182d0040d43d0010b806030145030140320602c00548010f230100301c81c5002c0c1e0f00903180e00d0700c40a106800c010554a0580c00c00d04060b00303003000c42d0a0142d00007202c5044c0c0b20030710410f440048200c0700c1910b403805054000400d034494110741810170b40d21b821707112841c0070a00452030200c3c0003800e0300351a1403662180c248985070403803000001054103640584002e4000d4a090b2503081204a081d07a9035410220028130403100070314041040104c240320780114604580003d000c110340e03c440380f1150840310030548401a4844499540ea01000e504407041041c414800103401211103000c000104406610316549443c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 421606483 1250 421605233 421605241
    0x20606042c0d120627090f080706150503190219290a0801061d090103050309120f030d11040f0816060203030114061303081821030a051c06030f0b 64
    0x843c015101501c483c21100d0f50740000030580000a82d29845c55001103a940f480fa010001d900000b2103001107014140c0a178440700941045801c45801d0100c694030f091032000300b0815500c001c54806e400414002c0a48a01e0310b00d030010828100202c1e004002102c151107000c5010902c5080e403081070303c4c6c26003100702c0d001d00c0040c02140511511124001203007101c001003042034440c0702c01003200c440202c00800982c01040110741021001c0e003044686420100e1444114281980440c071110701100040c0300d00710000c00d4203a102d03c1203007910014591241041c0da007200c0c611040380c005068401c0b80030b050550752004292a400481400000d82c0b40030000010b0711807001003546d043e0780400c3d04400d100d298840402c4200d6000d84807035040310500500000c0072a00002c00b13013003500b0444a500350401114000c12007140c032542402c8030300c2000b805d0420340c40b0f14000107494100546040c4285d8821940c040c20103036034407212010034003600300040802040f0441d0310a0130414840e44c1054060b440f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 421607733 1250 421606483 421606517
    0x100e09060c0f031e040b01061803120c02040b03071205120307050904020706091719110d08100305060a02070b150f04050a09061d0f030703020606042c0d 67
    0x3005a4041c19034103000d00a0b881504030364001141c006070a810710b0601d0075901101d07030a075010112001c0c0c5805090500405c5400c0c1c01605c803501d826001684400c125095903203526001e080c031401903080020381002101191201c0d4050b488182005086840d01aa504400c0c20780c4440410308840350301810000e40420385030003056a004080603151541092800421b100c025004903905441c100e46884445001c03800c040380c500002c003020780b01d20b41d9403000ca40b1184000d4540c02401402c10450b10703407e403502c004c0400c0515a1351900e160102d82503c0d403410a0108001d2500040c00c1809140b00388644500154024982c4520900480d40d950342d40020f6070747c0c0c910303807a24140e4000e401064100c540349424de00035903106c1002c000000f460b0a441c0c55280440c0c0391004400c030300358010040b40c190964104115107454a0160045241c0880b030744c1e00030745441014091501444c1c46410502d0103070008041d0a107400b9817007192080d06c0061141580c2d5480c041030746400410f00203000c844e2604 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 421608983 1250 421607733 421607743
    0x1207020c0904110f060f03090a1704052b0b130b0a05060f09040c17010204030b01050d080720040f020d05010509090a080c01091202100506091302011d0405100e09 71
    0x1c0e801c400919035055410f010b000c80c1003800d1031100d50060f030410215040408081c05540984a0000108002c040c80e10b001180800c0c8a80c0d2094201405d0108018556510186031583e40301c8042049902510100c0c4c011036000c0800001d120808502c10030600511020b001c0c4183c0e80180c2040c40a03403641d4065108645080e501d06800a1502e0408401414685421508144211107180d00c2994600080c0903807441c801d480340c01e5940000e000c005202d0003003100c80c050700d81103540460350101540d840c200c41c490b000c40280007903011080c0103460f440301401140c40c094050828022400760015800003544100038461030f0030b181000208490401c004014450002003001b44626507064440910766080844006055900d0f80d8802002038140c0c85801010075983e0010002d4111038a84402542c2004058a00440ba80700420580f01e6100200e40000c80e02030900c0100901c10310300f00008055a00119604542400c003030042c524000342138542118030829044c0745035183c3c12030207a224 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 421610233 1250 421608983 421608991
    0x42a18120c09050603070e010b0405030f060106050412170304030503091b031b0a0503030f031905070207030807050a0b0f0610020a02062b0504030513061809051b1207020c09 76
    0x4001400400d2110840c0355103c039411070310040486c2e002e16603c010700c070300c0041c0903002009550b0b030200b4200070703500302000500180c02001010300700c65810824000e002e401180b05002042089020250502201705207020781c444552402d117a49103058240a00558000c0d100c0b5000c0d88189d100992222100c180c04e0f6a1300340009001d8038010398402d180d001d200c0941d801c5107500241307428000800e69010001800b20102142d03a00e0380384d1418070701c2d002e80302140d8110800f00c070b81803208202c4440c0d40498032005881e4441c10440d228001418950b1030320300e110400410f10300c000c4061282d101800c0c41c08030b203d40c0302180c4901841014510880e04c030103031400d00a411081c1840614282c921500c8001890101902910040340d03c07078009205560b400d48083c0d0200d940013030003129403c84200c011001c4c080c5400d194080010341c0c4101c00f01000140300701604569074001003421006861480300040c2d10442d50b01c0c0e1100700391180400808016a0040d015208940d120181418100500c51003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 421611483 1250 421610233 421610243
    0x32010506010c141009060c0905090403140708040e09010b0328120212030c040e010b190f020f032b060f0b03040809040c082e05042a1812 60
    0x10b00500e980e03034031030301c0341100d419410f500070406000f0380082644921156140220004922a040d0180203000041039411280c0110243c0b41044040303504144d0444400c031070b040340300d5907528413810000f400d0b01036500600e0240d000b42091042c50384054002d6004420101c0903070302000c03c1c110404551460102c0c5c030b000591900313a4180045089110743c4071008e11030303005903150501d0140c040580d9900480b4540020140820240580648007590313601400d0010701c0ca5240c84050a541d5614120755140c100400c46c01c15019442a0300c24020130420510b81d10071644c450b481a480e40441b150f40140403036076159080020200d018040c041c507402c03600c140c0308070b00c03180b42050001c2c1d22650004000f41e0300110104814030858607580b00c3d400d0b050b003407070340c0740c40c070a0825801d0300d0604205980400d10303141d8201400c402c80e100707104000c0c2c00c90b00200c60006401404034004016840400c1c0400107511103100100b803560340004441012985141c0000040d548a00481401c030700f010b08040c0c6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 421612733 1250 421611483 421611497
    0xb13050d020d0e13090813030c0503010c0c060507110f030d050907050f1203040f09091a070509040b01090b0a0f020708030c0d05030a0209040c02030918313201050601 73
    0x40c16013001d8103130041800b002c00021403401c01d144c840d010030740d124501340c040641c0740321800c0050024901e034140150904400034802c4c1181004020301000311707500c001e03055540d508080b403400b07070103003000c3e40c0c1e0107800000f85c074000c200b800b04031a200c1d0483c513903061140c1c0c140b500103613001c400815000c00f540c000034400c0011016850078400240d40a203800e848520007088081a40c12041c03400d98002c0907046000b1544881a01d8214065001d8041454900c407040090003042c9030003401742c419421007600c4c000b42d038001d00b01c01200c01880c0740d440310074503c1000400c08d0040d54881031001043e501d940031078050300d903a0f2076190750720310420104000a8020000010042e07100303200860304031101c00009420110a207001074212680c9800b0000942e0001400d00d603075003000140320640030000004003c0c14540704440d01a400c0d0808985448594100d0305500114408150072004603000303035a41c001c0f403032994030806170407107003600e02441c9840c0861001c2520205000705827082c0b006170354880f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 421613983 1250 421612733 421612757
    0x606020c01120b1c05070905040501060501120902090a02090103060308190f08070909050a0f0218030705040917030402040213140901090c0e010818010e06152b08070b13050d020d 78
    0x508079640d40b8204441c1d40c042d041000030400088c0c0107144c0271710f0050000060807483d100c00505000c280c1d82c01d00602504280c140d80150360b0b02c060301d80d0b000e41050b401503901d00e440d40c0100e005001e0381c1c0009000300008525028909172844814001c11140d449510001004c03941c143c6090304100e0b000301c002000c10a0030302c084103407500242d4210342103610100d0301c2041811500280e80041400d030001d46405503407044907240400082c0020300050f18204161442a02d071140c081c2000b00b010950304a0000c00700f01152180d5040384c50003424109916909519840c804d1070f08407000c480544600448400850088440d100391041c0c008207072175606298000c070700196004e1000903c1080b03d4910782c500624424000e00821021551850141165140400e501109100c5415502d4010304d000540fa901172a060034101310f0980203c11030f0322608646192012032807145d079100615049045050080e181404d00044c4200c501c203000707484849000343c004036900d018500180740011900b205031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 421615233 1250 421613983 421614019
    0x1d0309090c0c010b0a0330050d02211609060f0903060c020708010204140103050115020c1507050a0804060305061807231204030f020109030503180309040606020c01120b 74
    0x414030403440c2da0011070030042540010300b5401807a0300c03d031900f120b0586e5415000300303a4060352407a00000d624940f000082084020a207024100070080c1c1164005110070100e0751251001c1c48044d2502d0f640030083c900030200c0c7c0e004048403030354000070650301070340030810f14014950940d01a03d555119a05140345d901e40c0381c003130301c0c0460002003503010b940e0011407012001e00061002d40f19244c8040044030b4100c00040489005910040c52410031159070081c5550100f5911074104041b1003440ca880c600b0b1051181a2041010040180c45041c0c206010408084060000c840854404000c43d9031910103101500d200300040c1e203000300b02c050005000500601c15440b0b000582032444101e660405c8800070f041d03004c015000030906250042004241d4800205104030070f50344000d010001b0310b40c0d4041c110707000140a1003206410030b17003006030b45281081991808000200188080c40d6116406034980d4610300d4000c0c00982094a2548507aaa41c003070790f41c00000141c0782c4c091084514403030f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 421616483 1250 421615233 421615237
    0x1409060402060d0513150c11062a0409020a0f030b0f090c0a050d0203040c171c0c020d05061e0604180b0603030712080a1d0d03090606050d03031d0309090c 68
    0x80e4030143c0908400400204206d040b90586030030310071800194041e618a0060a500e100080c410385a030711090400000300e940c504809070b4040c429260360340341c2c04841ca220881d405544c04c5184d4441c8007241c0d02c03d038243d0000900b00c84a9540e1410010340079550140022800711100168100d001440072680c41f403031050041c03040408910b00355040040522400301030360b0003501c09a8000c4043e00091041d0b000e84003258514400c010001d1400600441941e041000303103050b104103010b503030340168041d5107801d0b08203080705a025081d80c40c03030700c2d050a940c1c1103500b1150184004d40324180000b0b00030b051521a0b0010b10a05028041300c2480d10703540c5da500d4080c02008590540020f20510000410180c122080e0341c0560700c40c000c10340b40c0703152820304039564022090303003c811401300a44c40c0000451450318040540c0307804946500282845d10180107241d111507000090129140d050507810351210881e285c880c01000138400c00300c0110341c0c1d40c2c021007150356800a0314101040c2440c2081d40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 421617733 1250 421616483 421616491
    0x603071b032601090c0f0c0b0c0403140d0e06040b04050f0d0c0305030c0d0801051c0609050706020a17040311091506030a0209100f0e270108011409060402060d05 71
    0x10b01507216401002e2000801418550a402c04800000060003e80340500034150300503d2480c201a2425141d00d00400c1c07204280e00103030a404207800400c4460000c101150007440e04810105591b13600340c2c1c4a26650500d0b000000d0005044401d40032103441c00d10121811580391400c02800d06003400104400c0c03001c074920443d440b40d02503000f1400155445032100003580610007440d1140305001e181030030407420300c0640c0200440c401c01440716584034040445108040344540e001c00506103080c800810180d5405061881414400510340b580000c2c803003407062058003c0c10039080d0301d90201249000d00c0c0002080394110106406543c18409203440c1d02c6980d0008184485100c00040b41a0350f000380ea1000c01d0030b40001d4070f01c4003418802c1c01c1202d42e410514080e080704400c01401410703507001d600014441d001d10b99405c50311020884900458a415070143d10f100d503904ea4959009207001809081140c88000001d5140d42c000308403075200d190043c0c0814a000c40442c030792001400010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 421618983 1250 421617733 421617737
    0x105101805030a0303060509010911070b04030323010510080411040504081909050a080d0905090603071d0604050c032a070803040b010801062114010608030f040e060603071b03 77
    0x3640c0041ca5540c00c02044070082d009450010301d40d810881813140d02201600050400360420403035484450480007100d00041d0010250009a1210f160032070140544102c1c0064107584620a18940001220414100c81046902450200d4a5102907440c05003c031400740164008a042d03103060305062708a554020b220300c1d40507182c0f1345814800920640c603080403000050000c0c03000d02c024288003d0080c040c1c004c83d0000c100808402000034511066401080e01500304040810001c0d00e04000348405000c0d200320203074117007000d403420301d8103007908654840c800c0e414000441d0b01c50540e801128000c1c44860b001c4003520404065004462008a4903048a440d0401101c4041080300000e103000d00d2181000d10565450509203500395132440c0c00800030070b0455803d902500d07000000b00fa1046a102041049001e2480b092500400c0c1c80d900c00c03a09800001040034494030140024015585500c0000c203583c3c07540d40c180b00c485d000845000c0089044655a4190162040880a00684a4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 421620233 1250 421618983 421619027
    0xb0d110a0512010b010801061b060903050913020c120a080106181a0d0e030c0a061505030102030103211d010c05100e070f1517041419031106010510 65
    0x1d4030100b003460a03210020b01040e5520391412900c1e44c0c0c800c080302d004006a161401e01407400c0c0c1140c615000d1628801070405a130b40440030201401b0f40146c0d0762140c4000c104501116840321440c01942c031000c4030408502454100021090195017684c104201c1507444600507800d00d04151030000da0207000f00c1004030050400a4080300782c0c49400d4002d20fa8101a40c0c07070740040f084c04010b0350b44940f40d0782c1072a001804040c600c4103001480600554012102003021001c41403003e2070318200350403a41c1c05500010012003170100d6500303400342c0b84400f600803254484070083e040342c80740c00c01c108494948410140c0128250b201d001031f040018016026a19113024801c110f10403100d100c0c0e40652a03401c510010440c203020310000c4c00041c03035000040c1d0030b03001d13011a0083c80d0b00d20b09412500400220300c0800d00b400302405844c2039100c1602e01310b40000102100041ca64459648101c0018114a0200c2040080820094106c0301d010b4079a083c0348081102c10b2310000000b0040510b04118 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 421621483 1250 421620233 421620239
    0x1d0405031c14060d0302062202040608031e030c0304060902060d0e0706022e020f1312020f120a061805060c0d182a03080d1e0b0d110a 59
    0x100400c8041e144921800154500c00c15101c0280d50800500107032050080840d09000b283c0c011072000d80c8480500c0905080045002104d03c5000c41440c0294100e031401d00d0100785500008001d21210b04030302000f42000b0f154a18440303080c8000c44039614021014001720b800250b940c0c118600c010320007802c1d00d052002c2d1401000499140c0f030070300078480e0301c1014201b01568042c814a1101440b0400c15412400e482002c0000e404500c44000312041e4006041c00840700d0705019500c0003417444400e00d003442d968112902c030b02030000070b00780d00c110000703800303216903140040c00c0c41046012100175095290540c2c6884000704a00d15006071019164030341740b000120148281c1d849140d0312a6501d031205081c800c210200c5100c203a09151040070b46007030b2002310b401d400944003803925000d281a884081284045030541c4183d00040c0f4205010901c0030100d001500036100001049041030540740f0243e01040c01e03180c0c0b600b03000b03412001141c200170103d41c40e007803030794803114000d8440805c20755 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 421622733 1250 421621483 421621507
    0x21c03090b070206010501031109030715020a17221d100b0703031d060c04030b09073503030601140d0b0306040b04051b010906081513060f090203011d040503 69
    0x900b114900c1c01a08407000601c003540e018441c61700d06090b0b41c050350741042c1410000c81c1d5282c01070301401100c42281c0010350401e0b0b00c02c10444401c0c1d9031290304144282c0340e0707c01c042034a81100980d0398042040c198003483c964840e01024048602ea40e05403100c64120080340d501245014103402e1004c0c2e03d40310041a0300840708000d1184500c01c1d43c0002d40a01ea0242c4c45e0161800742c0d128556903000482804062003d44083c1d030300b625003210a0110340d894190380309280c08c00c0da030710604800356031101e4400c80030a000c004500e1009941d0041c2003904100000640f00e11003116114081440966804414120600a03119a5065240004400c0c1a0034000703440c0a20842d02150041105010403040180503c142c10500400d25605000c481015002034508200b0340544010808113400040c0030703a007220162064400007500c0c02942007540707064038000d4000d50160b2241c1c24031801c2c001442c00018800c50f412514181e0380c001c160001850a0201c0f55030140040d40e1611090201000e540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 421623983 1250 421622733 421622753
    0xf070813140309010909110a05030a060e151002012009040209030303010906170304080319020a020d140c15160320070f06050a020c010e01020703050111130b0406021c0309 75
    0x758880085803500c0184000411026094001c004810300b80540d151070800030381d06807480040b041c10840d440c1d03607401c03070706c840103002652245510a15040c05c0c80a22000811680c440507410750350a403528084900690903280c1c81c2174180040b00c070a00b402840070540c0c00203480c0c1100010009480c000540300004e1451704281c21403c1da0569401040050100f015200000f40c6c800e50007440c00c0a00c0c01101da03849016142c402e400586086018940291003800350040840d4000d061000c02032050415500c405980122145507110782034000800f442c141d6241c804800d0f10f0307136015150200e122681d003051080c010084041c807d599840345040001c3e2119030f00031495140c018849249010b02c1008412107541c041d401380803041008180050f0f02165031103a120081c02c3c511080d002060040385441080ea1018100e54603140300584001c21001c0140f258258115484280d140c840e4135940e840e2140f8411400035a00600317100841c07419141b55502c202042e41400101e00103141c031000c3c892 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 421625233 1250 421623983 421624013
    0x130b09150c0c060309390a03110f27060a060c1e050f07080c010210060501080f040512220501020f070306050903070f08090a060e030d050d09021011060a050f070813 72
    0x82c8840b03901140c03402c001101d01782031b118040341c1c110342091a64513108a0360102c00d000d07900812a58158040e142c642000c3c181c0c10300c04004405204111340c00e02c0c11503201081d10244c3c451044040000341041c4a00b8211000a07008400c900c1c0209150600340f120910b5100b0403101d40c001d17031a89400c1c5940a100c010000c29009010b850700f0782410000a0824110000710300e0458588101070002ea68000407440e4415182104040c0f9a1240e080c8a494425008140070840200180404540d11810781225903002030701165040d26844000590711188004400100ca5000440400c0458ad143e080b5a811004240940b403400d2a161160480359003959000d0340c09a40000d854821410a01e0340c050040c1454608490054886000262505143c0301e081d0100900814081c014164507440080142d6005100ea600124400c0014050445c21014000c0da03018450016020325240d01442c1e205030840e803180c1c0801e6642c1c100680c3d45d58005000c10009040d5040000001240c40300c2604074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 421626483 1250 421625233 421625293
    0x6090a050301110406021203190c030e10060509060a0302301207141606030b010306050612090f061509042604050a080313030303050c130b09150c0c060309 68
    0x240c4d40c10101c010345481041d00403102030503420001c101407a900121804c4895000b00c4000c1a04001c2010840c040d064240c124001405104482c00241d0000c0c0d200000301c6009079a0040907540300000c00c9000c6141e8440030f900b0100e100a0000f800032110841c2e0398240056558020015644a21310b1034407030f000d6030181728444001101c505202030103940c1d0b11710303004900041c554a42c044505000500d2944100810301d40c40b034a006540741e01036007100c00078103030250207103403104114104411099015070300010980642035440c0b92a081c0420854800d9101d0b2441848072000402440b28504005100b40c035003000c43c26030100542d00e010b800a001440392804d03542c03079504042c2080422900342e070211080c1d40c0704200c3d080200f000c2110490880c0c0c0c1500740001c117903030759001c1518948119407100502c0404090085041e2174030304060001c00c00700b0344295926404000031030a0034401c4854842840c0c0c40b201c4100c80760b103022801181e0000178001a10403120050580e040b601e5070b01c0d090303601 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 421627733 1250 421626483 421626487
    0xa0b180a050a0204240512030c1617060705030c07060608010c1d0d0c03061d030406030204080709050906310b01050f04020301031502070516080312010806060a0506090a05030111 78
    0x810340c0f501e0f0041600c02002100a8011795a800380404c1903600c1d548150741c00f0300a8040d0444403074105006445c0645c59039016903a42400c0e200100801303108901402242c00441c002040000d0340008165100d0482d68440c6451911402c000b0900d0307800010044401c2c03500c95002082d009028060140b6414031a290740400801b07403442810300e10322003113400d4010654407510001060443c0c003c0c4045a070032580c00162400e070100c01d549008681d030100e80c02d80c0300019000500680c1540204111590441940e28441d255034282042c1e0b80d0940750580b940d8010408100b100c3390102480988c9200344404103814814022900c0c01091b1000d8142d810481e4140100700c00c0c10700da0343c1d604490108480441c0745d90704503610703840d110b2601407064254941c04210001004010845144c241d42d011500c0c826565556030000d50b41c1d40100b903070070110500c110000440038030003d541400788100034058010b1904190038030034590400300181351300c08880c2100090035102881810b101d11940544e880d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 421628983 1250 421627733 421627753
    0x60503040b01051f050309120a050c071202103b010e030a050303130f050a06050105031b0906010c021807020c1c030e060d020d150501020d0306080a0b180a05 69
    0x5041d410590001c4c0c01811030100700c018480c4a00c1c6210210344540c104039480317071a00d1a600c1d00d0000c0381800b0015108002401707080c6203400501428040c5200c104072080262580110050481050341c020740000c00d514104011500400359034110025440514005541c0c0703002484400b1002c14041071b4803080308820f03500700d5a100096104180c020340040c102c2950345e99841d680d03031100030a04d001c0d00e84042030b2041000315079484124055004422a080b003200350612a00a0000f846282c0c401e2264040d0051841141e003007421174060f00510b40100c070781d0340800555581c200e20108980c0440895400120030306c1540b851401a00c2030b034004d000d131503101e00c184075680700c81005200d011110302c0407410019900c04c0d03440f10401c030243e9500f621103009111020190241c0e4403a441018180034500034552100803d880446109074221100c840f0901029401c580d100d000b115000c0d000443c0050106240036103443e0407400c81c2c0e0303001800d401c0003100d69082210444003280e15401400103c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 421630233 1250 421628983 421628993
    0x1c090804050f0a0f09230709060e030a0c060315091a012c130209121c11031b03070b040b04030801090b18070909140906072c0301020405040606050304 66
    0x6400c2c10a425038640b02114184200e104040f42036100341d110807601c61040000100760010003260b1054050040c125030308140502904030091400740c403001030b00d8807111038002d10307000503020045a0080051004541080b01c00c401609501d1441030700f1003041400000c4d501507500c03601c00100150a80510424140c0c030004020b11b070700c0203901810780e00d1805004084440c1010160342c040045902c64103217040d031920107020307000d55400564454840214200142c10204007941c0d180403110a0402140609506a41101d204000403a49920501038018142c10b989171403804940316404980c10310445640e5000014000c41e0101e81354484201403000300740d003103500c00e40906002c480c02c0c0114003050020172001140c00100c40e01c0513a800e800f08040500400301d44001d000380e9032040c08117011900e2506000001682c04070094800c050002d07203228031401c88010312140b003c0654000c94000a48048040b01400d522076065508100000c1ca6941d01e1013520000c1000f038840c2c903243e280c24204 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 421631483 1250 421630233 421630249
    0x10612050105010311040501081c0311070b0a11031302090402030708010507020313080d08070503040f060e0a03140301030b040807061103100302100f2f0a0b09070f03110103021c09080405 82
    0x41c0c170b030165082c00011300050801103414220141d00380892075105c3c011007403c4019280100500359510320003c1d10009200055610380d10400211038140318840c20a0140c82b25440101e40c8052522034080e003078401850402d0310940c0007030004003210340d50b54036004c426003101c506036411005079000141100d0202c03004442c0c040140403120160001c0c1c9010140545608401004007080000002c001000c000107800b641d1503260300840204001e6020005441d660200705400b80c01240c500009140001c41400c1102e043c2c031703030141801101d070b10741d9902c4502e00c0e000729500b290a5900e81c005000400c1614010310311607401140d4459156145006100400c1d00150300c0e9410071141c000b0100c1c90310342103040703160300b00c0710b9070805100305140c21800e01203000d50540701c2040f03020b950304800500c180151000d0040c0d030020241c540003507440a0b204c41174480340c48010300c101802e580c002444e600981c09801200e07000609102008580c244510032100d69000481340590089001e02250500031070b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 421632733 1250 421631483 421631513
    0x7061e020712020c060703080a0216050601091521140610180510050108060f04020c0106031a040f0201050a0c02180405061b0417030f12040605160e010f020106120501050103 76
    0x509244c0e0b00d01c0000c5181482104405402d12404001046400b4401d44c1100c0b040e01001e0040c003060303090b0f4030f001606c0b03c40038403c0d42900307403c04024071007e0040720741003000c0780c164081c003030018103081c0514402105241070541d24901742409a2400d02001c1c401d840c4112800c00c5068815801e14055500b6a00c0c1e40441d00c180510380f00400048140b000c00c224151182424003a0450362001d000941c454000c40440703410a00200d044200c0c0101500000152803041c000498084400709010809200031500a061640210454800741d402040144201e08561810101e5001c180e0040789800000c05400081640b40c441000244a410f2103000d4004d00d100e80c001d240ea05654850104a00480c00390300014424040d00844800c1c0410859068000300c540e03c6d9100c05500704c80d94200c19007101c2c2901c0703150400001800f54449169003880804180e01d401c0c88223880e040044640c80f26220621041d59690417021908180410a10300054403a100100d40d541c103601e06100545400c1d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 421633983 1250 421632733 421632737
    0x807060f0b010f031113090b0a05010c05060703090206040b0406170f150108090106090510150c1205070203010608060c0a021b010f050a030b061305010e010c03080a0207061e020712 79
    0x9007601c241a03901c2540100308071040d240c0416003044401c10304035107105088031100b48903640a0001084003680d0410300b48101c08580403482e5130f90b41d00064480d241c2015008100d030b0402000034001600a43c40fa4440c00d00103032110f401d05440e21440000e551140d000b403000f01c1c0b03400f42c0c002c1c0e442c40b9201d01c4a0344010000400542414000400242421001a8070707050100f5000050650307102580700304001c01c0340c40b00600c900d0410701044e500ca0034a82c0980501c030851200300c010100d002d040b0501e1504d5019840d210614071040040760203821044040360306548502c1c000801d0b900030000d85001c0c0c0d44075002903035600080c9101a24121170301c0e6901c0540d009400032a0083c1c7c0c0c00043c0c0071284011424199950764122008030020f240b99801c03107921035000300d83c000d45d5410025814069400a8032140100300710350380150703442c1c000b2140c010006500c90000400c900713810340103801d29510038103000c900351071581000300c114104155803007002a03000c1800b0081c801c01060341c07403c180b014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 421635233 1250 421633983 421633991
    0xe090304030c06034a10020313230d0e1311041412070302010807020f150106120e1e0a0804030605060a0b0307020a081305061c11090604120309120807060f 68
    0x220300d01c8000001c48031005e8a6000726009110380300f650078000045080d1407480210366900d044060310a00807803200042d983d10700850480034400307000d074a140400c440704200928451034425811258010382003c516040940a00b074000344400c1800345155012449003020744640c2890300c0040d5220f44040868454030340e540e2500c103041c3c4040b0340721064035028a850109503845110692030510114800010341c0314008004042c49140b03900d19040c0c58003581d40c6542030a071510140c081d115194529506508042c40c000b440c8280038100030801e2180c103003540c2003142e0f80d4942c2c0401d6041544140c514a4480040003024a02030400d80f0140645407020b41c11030502c0c0034025a40d601104000f410703082c00040c0c5555207058256004001d0600500702a95108444820075010707950128078240141071102c50882c0d5003440c02921076510003e4042c17400c140c03806441d102903805040703003682402508400850000354404842c8040c1d4040e14440782c7e5608140340080031102c41c0c030451680d603450 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 421636483 1250 421635233 421635311
    0xd030c140d05040602040b07081e09031b130e010e011401180e030706020703050a031b05070b0c0c0d1106060603071e02070e0a0905190c0e090304030c0603 68
    0x400c2a0761a01ca2a03550000d40c43d81d80340341000083c411500950700512000c100041040f074201d00804403401001302d100000c90360744440c0c00b08d034001c8952280d8940c02540180301861f4041e200e24043d084024105c0300034150b24a107040c00c4901403420100d06075140c0c105041c120f0b10034010414111441d0100d100e166150414070b000c04020206a0707204070f6107604280440300010000c2c0d030b03140740c0c218000710f40e22111840d01a0142e800008203034046420282180304018070055180c00c07040b01c544581c6d103444240da42e003030200480140702d001600300501c0611181101001010323580362107519812800000645664500400207041e01e205400420822400907400b80340b0424030741c1d600e80d2034000c0341c40c0e5500980c202603564000b140d5542c612003c1224015568214000312400b0354180c4440680040705070464200340400540f4001c0340900c00c108020701c80d44825400100707170050300d040039103c3d964090a18030580c004130000343c441c071041d0400e040c20104c0aa07810802d40140d410080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 421637733 1250 421636483 421636517
    0x15130c1115090706080c040306150501031a0105030703020703030e060925080d0c0321051b0325090803030a021306050c0c0f03120f04080120040e0408070b04050d030c 73
    0x8420b002e10b004205c88080071a00345000076064030041c45e803003d02484404404503810345846100e101d020300190900d1100401c044c1801240208881d060b56010701e15582c80c1c800307401079403242c0e500f00c1c1010340da19071b4140040400d105150043c8400405421200c00b031086000e410140100901c15041d0344090402071080005154a00300e030304c9040c01e9500082c80d09007501c078112092500b4a0821400300c2c1c1045a50319580800d100e4040c070300220307460702c0b02141100140d02080710600c81d07040c660b2030310140c9201e0101c0f1103501c1441502d03040c3d0560b500d0340d0032942550070544900f000e294000c0340d5002042112503400000c0d207124941075080400c04040e6503030b24070999100c9402116400341000c03117a1810301c4143c2100d04440e10483e03540400074184217080e4058440c1058035460014203152500c0064044510341c03c00d41509803c0900303240003103070b10020190048070113041c03c0061400051041038041d12840c02400a4150800c03240006800e595020309580100715500718560b5807d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 421638983 1250 421637733 421637743
    0x11b020601120204060b0d0603051209060708030a0905151e15150c0d0908070b0a0801090b04020d05150a06090f0b03090c0303070b07031503020915130c111509 70
    0x44016207001200507043c008600200410f07000b01c0404200029000c0001845400c1003046a200d2000c0381d010010031b00d1040f1450150900d82580000d0802c00d00000c5400030024541040d45944000740f200d0195448070310303004e4500d04841a0036a0201001610205002422a0820300010444262900b0304c00d000e007610a5007012403040e0822206100f0660480b41503410100c0700c501150304404840c10080c02032040b0f88900019441202004940400060280c4a61415607101c0c00001d03400c200d0030364080c0000707081094000d03a00780001d0034500700501445029100f10107482e00004403030814046401c105400c160b0034000b01c5002000021039042c81041140c1e0705d0301d4420b03120b0702c8030040141400c5400c2c2249a01d80b1010981100340300d00c0c82c0400e4010b000c1c80c4c81c100700d0251007144c3d611006c00c0368400658000e40d080001110003d114884120940d1b00400c011a0f04214440391000c54405617182030005d00304a40407006500f080000c0c4460040c000d1200c5024a0300c290016564 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 421640233 1250 421638983 421638989
    0xf1520070501150f0e160206040f0816030804121e0c0c12051e46050d110102121338060d05060105041104170f011b020601 54
    0x20040040e424040c40020350000303107582a045003111000703942c0d203080302e404091070107404004081c2801240803000080f80b5956441407640181c2010ba45a0f20781e454410b41170401941e0f004070410641145e42082c0100c824070500c00c0d1100c80701410030781001503812420030410824002c0c900e52030151101c0003038407080e9902c0140b4001144090303a02d0b000b0600704181e40060200315281400008112012440540120b0920f10b040d1050428a081d250340f4944c244c80304050004a6443d00702c03440946050103882e01c0005900050500700300303524003a504d102181070300c1ca81c01c000c0b0320540095200e08160340d001800d50080d0304000442c4010070740b032030020308500040c06c080d444460030003000403507998140284048035454503e9003440304090511803c1d00201840d10400003514507e04010482203440d00300c0d0090034580e08107403d100040c0325020412030724003000d000000340b02140e00d4190480c1c20100c0e015204038a942c00d1031780d09440d00001c44409100510720750020b210780c005842411 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 421641483 1250 421640233 421640291
    0x102030412052d090402030108011b090e01060c080c0d020a02040e01020703271208040e010f08032205030d0c1106030108100f0f020c0604030801050102071809060b0307030f15 77
    0x210283e814031000ca510400d440c441d0824000300000501d44010341c0105003035400c51982c9040b00d000404116800300940c001c00245512800040c81041d11070f088141c03000c0d116242d1a031a00d01007003d40303840e021241203074100680c0054a50011400d26020380c801c1e00700040002d508009460b42c01802d4211344400c040340018003243c0c520350f940d14410800c03000340402d02d040c220003070311818640e565502c5230142c0034804d104400005944e0920800300c07000c4035880e80c0554100380c0c128800304900c1501800b0760b0510001103401044030740d4280078a0b80107540e99180c0501d40a070b07900c2d2200300301e20140c21070380c40b81c40f092004020000c00440c41c5685480b01e074000280c030440311080480104070380e203010024030348003151203016040001091401140a511906200da80c2c030001240d6903220b074099000c0d404e4484881c131460390040e81000c100c441c41801e01081102120f40402c1c80c101e110b42c81070700d418000384001400c0c049030642072810090400800c0c42244121008041500c000d41100c107030f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 421642733 1250 421641483 421641547
    0x90f0215041202121006030807060509070b0d0b041517010605030f1509070f0f0e0f09031902070e070810150e010c031209141e0601062f010203041205 66
    0x1103245805c3c0031100d03161314010f504000356526400c00b089260050301d412070300daa14001c08100e2800e40020648101c440c010441803078090100b021030042d1041c007488603003040d114080c0900d0b80f842083d20310301600b180849a40e9421140540c142510710300d600950181c3c204c400d003003440c04408a980c0300724151400b400101603c458001c981b801c01181e000e000240100e280114a54020040090884907020b05140d581c0e1100c64042801c498244d500b4209a4803c22824001a040c83e10b46181054a0f005440000d0350340c0d0395044810b20215403140000b07442d98204130494812100d14005411402c0c0c802c0d42c80348925802804d080c684941280c1409072603044c0302d0815211b0b800d50036a0340c48548051120080e5450f010035888010741c001c80c4103005940000818066008a011f107070824040200b03c10b034a80181034404500c0f40160604910288046200003031841c0b00c609440419000010707603c0c51f05003000500d000c4500c44a13001c110f0100801c40c040301d0b1203454041441ba00d450b641e5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 421643983 1250 421642733 421642759
    0x60310110d020f0d0905010209040b18311a01210305180409030e030c010e130e1606111c020c01030b0111010f02040914060d030f12090f0215041202 65
    0x802d0fa0144203040003c01d41011400f0007042819009007401e09010788060141a03030700380c1008070b904010034050b200c0460080002e82a0314511254181d01c00c0c0d02c00c10728401e90480da60010280d0031569054503103841600401042d824014502401401129000035828141f501e80b101c0c6900701520150802001042a1402d0000307001ca22000f00801402009156030a00d00074051040d40340d2030340e00c00d018241c01c02000c1d5001e0054410f0510303004050480000c1c21805110050440448040091041c10641d041e2956003251031005042c440e15000200300322a00c4e0700e403901c0c1031030164404815902c1c40041c0104e4000442190154003401c0100f00da95031440100d4651446110798001c560038180e00d04500b40141c0c0c000e00690340394035010b00031840f4890302c4c41080034013514595008a22052200c010a20542d58802c502c880d038604082000d582c0602c030700c284d4030b04803000da4071030020380781c1d9404600c3c00030070304041c883d280740c2d00340e007010b24120103513440c400c030b440002e0702400703e0791094 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 421645233 1250 421643983 421644007
    0x50f0702012306010e09090624010905131103010803040f06050918090a060c0512010f06020307020d08070605101509050a3302061e01050a051507060e06060310110d02 73
    0x209085c0000035010070b00b81e14101b24143d0340c403002607840d460b2814070704100c85010840c40da03a90f29803001c1138491040180c41e01c403d03c1703105071544000b520110381d0b41d9200d50f0030b4002000211b00030103001c00203544039400c10303104180d0750351a980720006008080150300d6030b030b40b904000310900300d58408500715680d8455112504125041400528141ca05588001c000ba0001c01401440b0346150039040581c5c0c0b10b41d030420200c43d59000d018050707401449801c00503d09070355010305243c456041c040c10518079550365401e858050b0744030380801d00070000034084014100101510556103243c2036071854138000116082d403820b80540d0800003d60b020f401c24058400500071400e20865418003030300c5d141028000d445c0e4800395864281113441a07a40d040c0710030340a0b041416204010151240c1c107103004200940c0b030401c00f82e40841c250043c408600460098414202c5011070071014125034503211040500f4049400c14580c052440c1407015020303074684070180c9480b100c407040d00581c1e415910b005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 421646483 1250 421645233 421645247
    0x60703020a05120d0e0a170912070603020a0e01032003130b01031101080c0403030806210307031701080a05030405040f020705070f030c060503090a260409050f070201230601 76
    0x54840d100f0b20811200540d00c4030004c100400c0100d208110030412070243d9500c501d034020300a40038002e0303e840c0c0000b45084c4e40c002d0082500080441d25000080c600c2141030007042d51212001c00d50205d1545130722900800031422140c400d20b0301f00400d506c03180301003e002c4048500e01400e00b101100003084125020030841040c0e8002500d18590341e541d1034000262440700e0081c0c5e001508460100f12810180c00549003a41e41c1511016400e5880703105000c0c000c0d64400410300500000c0520f01c0340d5010900060140d9806640c91185089000420078240e88042e408551b40d5440442c81c2c0002c00c5010003500c0995000b120301003682403e02c031046010703018030140604103001d0540005210410111f174002124495082e5080950fa10f002c02d48184c00210f6014001c0d030040100800003e2901c0403110b00100c10202c10711f00001e0844d1810310540094000c41c0880780d45605110001460700a8141d00078180c3c4000d011401003101001e4009a02003801c80e148003045021514980c02070036 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 421647733 1250 421646483 421646503
    0x2040204051809070e04020d0318051e01020c010f120f0b1f03051f05010c05010e010510030501060506040b040e090c0607060903030c08090c060c01020c030403030e1e090606070302 79
    0x407400070702c0c01c00302c10750824914040d0b0b402c0c62030780304800000407802d4503100aa0700c1250001c00510b40300c402901d0030b40e150b201912401c10000040c0c0c2011585641c0d0309164042000d241540c038080019600c006842c0246000700c4506000c1d90207101d040c00e5910605a000881560201280d030302d9248501001520b16442001e901803d10744401c0c003003440c010f201c40311000541d0b6090101c0d44442000569001c90f100954030340d41e120b04400d04c640c1d4024440742d848113101d1000000c20380103c4138841d086880a40b020f14106e20106010003c0c050240205805000226034061500f803405107600031030700c80ca100364403030000c403200006c1103841c0500080102700d1025180c96903810030351418100a00c0001800c0340420302d8504c01c0c211052240f00e91904c1001d003000104140384000c010040190441d0845003103540d000c0080107492881071000c1c20086120752030b1005061402c004108084401441c0f941c502020000681002c3e0b440d20b1856405c500d05030f035002c0c0c1c1c0e4440b5090480c14030fa00e00e8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 421648983 1250 421647733 421647739
    0xb060f130c1e0203090a1d0103030815100f09171903110307030201020714030307080c0c1603050c01080106020619090f1a0103110301060b180d0209010e010f0506190c0204020405 78
    0x49440d42c0c800d8001c002001d000782c089858000c680e441d0501441420f25410f01800c1682c2400c005200090041000b035410000038844400441540400a00c0b448402c48803500000c201c40100040c40c0e07008560403000d0b020700301100300342d80d11031000e941c4c1d00c0c19000b640c414440c2402c1d080038107240c0112801000c0500305402d8a07607990260030040d01071b40c00100216031009000461003526000841524040c803080d594103481030300c902c0c6000c0d4168004a240810902880708455080507568503e10300443c842d030301030107465140d480051701f41e82d0143c0c014003c0d5000a010400905441c101000511020580005210050381030845100c4c040460081402041a40c0d5680311819440401c0c12030b84220b181d1080307400c41c40d00389400d0398841e219200050300184401072285031511480a00210007600e80c0c024220f56400180813407500783d0080c03840604c10f00050140c0840481c0f02d8001c2c00007912564640025051540d05c54040c1a0442041064440718142156155011100200801 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 421650233 1250 421648983 421649027
    0x604090206120424060612050402060f0403050a05012406050f041703031603110d0f090b0708041209050a060503100803031008070f0b030c0309010f0c0c0b060f130c 72
    0x518082e07814200362030041d8004241d006511300000318602401068940a54500004401d030f40d020201408002d007080b68031240c02e000001203405ca61015000441c041c1c4004c09200540c1d06059084601021240c40604524001c0c180c41024545005003110348528000d5501c55020303400034040c0c01203405c48400349a6104031046010700000c081c6000310342c03c484c0305800107500c000503000c42e910300d48109103003407080c0802c07a108189644181c81000a11101080c9015140d590240a032000c07900c5401080024003030006000c45520340246465140c20300044141c240800640030b51041d1180d50200800000000d61840045032081b0040c51160101c9880303040031000d10701e090016014a03a03940c03240020024445030500071400817181d034641030343e24580301c0041340c2400c1e600c0280907411640d00c801d4124400c907071034854071004490310342d0313040c010012030715045442c01005040c4038031466814460510641d81d003529012000000c0200159212340c81105903100a021f20740e200d071030015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 421651483 1250 421650233 421650241
    0x2010e0601060305010608070f0206011a1204030203030106140304020604150210092109051e15070b010504050c03041a090708031b0d0504120b0408041e150e09060409020612 76
    0x1034001368141d80d0191110308295582d500102d40000000e0102e10041e8070000040080700c40c003044011a800b9540c6e82a854a0085071210f00749403020b503800c40045e84000010004a5803041081482c4d2030202209440e600345030f00005c03128000c4d8042c4290f8840b562110180042c001c0003810050b40000406001c0320102d03040c00150f14034480c1800c04840d030340c1c80b082e01c049031050400b441611030080c1881d000c5a05003401c1080c0841d0100b0a9409c110f0748002c440d001c1003024043c000d091b20400380300100d981450207010a9402c00b410103030b11004140305000c001071000d6002840c2008000320203603155503000495181c44140e41c014501c0340400180b101e42c40b0320b90340d1905c4050410100302c401030103820f141190070344202e11070070301c2a260035110280095461031a190b00107009140d540d0410340c0b50592aa409108601c0044801c02c22070810044020440d1307a0707200340c0b0f03c42d05116642c0501c050210728500c90060400d0302c1a9a606421300455690000f0341d000441e69140882e084e144c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 421652733 1250 421651483 421651487
    0x8040509130804030605221a0a020921030c070905011d060303161b0b0c0f060c07080f12070c02040b0406050609090a0225050c0312120613020d1e052502010e060106 72
    0xd0b403514070606401c03038070000400680350ae0084862501c006810592040100340080328443d21100300880e5034017082005581c010801c0000f072020340324000c400205549013083c1c4c03201891800c0c0104c841e590700501001071655001c0159a003821540841003400030301c03403500301c600c0580149600c003c0b100c480c0001c280d41c5030002c0540304440c1d0130002c603114007240c0169159603840807288903500e910100041d4000442040103803142e400081801410a1001c203030b1a110454101c9030100003400080ca001c2c2549004e018030419143e043d102000070380d0820000c106240319007064203021b450344c4800300d05c2c0020a40d0407030b00440d003000f529045217030070903454440a411021094500d0b1084601301009490040394000c204140a40e48030701d4080140760348145514000e00703144c0d00c00392119081d03800d0040c0d40018040c5a01c0f201001864001c0c003a42d03802c01510718800610f40070b1900c81000072484d4100300800c40154208103010380003045410803809001301040808140c001c100000030015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 421653983 1250 421652733 421652753
    0x103080d0b0f1c03090e011224050f09061506030705130302100504050a08010e0a1118040501050a0c0c0507050603060303040f090506010e0f100e010203070602070804050913080403060522 82
    0x1d480381d69800d0404e60b46508600b0b206c5001e0040e40c036900310b0070452000107400d0780144201c65003001c001741400809505440219801241c4080c82011401c0401100040c1401050790200d005a10010910000b80120b040350000420a009005000416200d102510080d0340c0c021a4014680000c540c0c00200050581e0840e1103040d009008018021413810b0043c02002002500c04008201c07600498aa03407002450a0080e01c0c1c0108002e468250324805005003c1c8c030641c0504004115400c0c00c03000b40c0701701e41008804c0c804010704002c00c1800540c001c00c2c8007084450441d101c98883d26100300090452003240d0006020350f04080000460311060b03001984112000d07219170a4041c419018808811040d044290b03002c40c00000c2c02c507105008800c00e2403181010300c1100c1c00c0c011913913907400032a0321803482601c002402080c200094503241005d103034031900d590403c05d2014a1a0768140b6903018501000380011340396000200b00940b42c4003016005011405414520140340c00c1240e000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 421655233 1250 421653983 421654039
    0x90307031b03020d052b0c110c0604030b04050705030a0f02100305041a04080f0c0a02040e030405210111041502010f0b1e060c0307030f0908060103080d0b0f 69
    0x49400c0c0c0c200041c4aa8241ca901c405a5405401400b240d004495049542ea0f210165201c42c1d0440382802c405040c6030381e6441e40c0700340c1000000081c40409100050400a440640b1441c140d10004441c100c03900e07110241ca040301c0e802084c0041a13215442d00d03170704002e481d4011030f4141c440c0fa07100300207104410030b9a00880d40203881c00c0c000702c0d840c688124142c0d002250b0203083c1201c0800c2c4400444035143c0f0256009000e074840c1400c0c0070000d00445641ea0104100390b4140c0e0001c80b0040641c0303018494240031130402c1008500d00381c03400b13020a94004800c0b02d4095100c00c00c6041940680e401e41015a03403e50a010b810380d2182c4560020310409040c000c141d00641c1381c0360043c25500c01511402c146413100400c90b440b009064000e8480351580d080b80142c0002082c4800702240e1005c1010b0310046100762540440151109030003441050a6407052b9091b920500042011424001c03c48144225072076001ca26800440b0100340d13110520703d41c40c0d800122240418909040303030f001500003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 421656483 1250 421655233 421655237
    0x61203140c15042a031401110d0603020319020f0d03021213080d08220507050d0602030615030c03010e070e0a03050102030114030c03030d05180109200102240c1209030703 75
    0x4049039144c801015402040200e41200740c14800520101d400c00e103102240b0300401001041400340d524005d491a00001000c04003035841d00d409004510741400031300c4005140b80f002032610800d43d0000f034284111014214020003420304680c1c1418402e000c046103010a241d03032103550712100e000084845050f8840d0706028040c03940030101041c802c883c0d0340e010383c0303060001e41d40080c0300c145110748102c03500d40101c40c54802d2600c002480d0311180b41c001da803a4001c03480143c80303262610034050042039140c0c02c1c0c1a1003c041041008000b425000d0380d06441c81c258a40e119076032100d40943c0c03c0d2240081c030f039a0004000030004100941500158180c5020b42030341c910a400c244140741c0d85200648401d030781074009000b8041815090340c8031030741c44070080481405001c2d4490030303142141d8940b0000c2c1d416444d01595030408018120b00f0030380d0410284020040411143c4610300580300041180000c00030b084082090348882a05441c003003c0070b0030807070a441c1015001030f40c3d254094182100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 421657733 1250 421656483 421656503
    0x705070201082202060f0c0a1b1203090324020c0a03020c0a0515300f0c16140f070e060f0a0602060a052517010504061203140c1504 58
    0x2a0000f01d103500c1e00c0202504143c0c3c40546855080086503000712a0a103000751090205221040c01001b812030414011000102c000041141040c0101020b401501d20b640107460f0b40e13400240d001c60082c00f100e4010114942d540c4d00ca48400140180040d07006040e240082400140854041200b2041d01c0c80b0380c0854803549444020700106c01624403e0b80e6003c00c2c0c801414000c2c0c40004000c1502c803018907030f050050054013102d00500f4070440200500144150b01700701021060340c814540200818061900b805200300100000042c50800102506810a51844500c00800400c002c0300c0b8040140c0c0c0c019a03c0b61070a2003c6241111014440d000b40d4800f05981d09101c40048141c89441e0301902c80c5603503240007007003e05000342c50840312041092804429404405001d204961070b0707600c610030b9100d2513180100700401030304094405c91038620200641096400882602c070350606203040031400c00e844c2030035940200c0d031104c000b900480d00d089041c00c000d00741182c4581d00c0b9404080c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 421658983 1250 421657733 421657741
    0xa030809030d0305071202130e041a010b041a070213020316080a0506030721020415051009080c01120b09042906010207060828061a070206030621010203070507020108 73
    0x1025200180c91038000b28801b040c003c84000c816800406105010080304810540e45956040b15001c040341c2c240c88000b020303920490b01c40d00c41c2003040d006000c060300745428141004c00c80c0601c0084051036202d43d08000075100c0c21074a0380c005800404000d690215260310749140b82c4c64103d80d0035040d900000d000440050060301031442554040d003006001401454106900c4440b00c190540c200c1e034601d00040681001a90703a40100d24800300c49102c0a41c2a80c500820700c42040351700221841440101032040c0162000062a0b0000799401d10300041c03000c41400c10300c002003510b00821500b0000d0380040100703228506401c011003e1415148088640c05046411160a4240ca445005030400b040c20054039105101c500c0d00107400b44c4c0c40c0a0072640303100849014151040700480c0d215120101041183c5136541c10000401e059139605181c0743c1d1560004031b8921000380107600c5004900d207800c0551024010080c104a180e40085640c0d04180d60040c085400044040740041d40e010006 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 421660233 1250 421658983 421658987
    0x6090b04090b01050f0604080625020a121d040e06010311010503010806010b031e041a0106030c09150306030506040b060f060901020a0b040204021317150f130309050a030809030d 78
    0x80700c40079002640c1e110a039003800104040e103040c46a8155005e1000c0c080400c41d0003003072000034007622900c012030300d2000581820b10b801c8030800f0b407101c096402030000c00011601459a400032040b081c0b4280b40140d84c1902c00d20100789202c0c8140303400c546030120490002e034000a0040c1a41d001e420304009910710040115214407090007040f0760f582103a0010080416440091508910a1030341c074044050000c001107140041258262444a0100384d02c85600b40042d480b1805000d0f145414400024440c0780505400b465200d440b0003100000c11a08848d80b00781d0141c00550b0b4400140d50a80c201800d203400d0602d826688544200c00d0402c400d120340c80c0080481c1c41d031010607006031080201f2034a410400c0f107401002660015002c002507800002160000e50150200141d03075a00380055511851800c0c40340d2440204102d5000d0501030b001c10715081140d400300d03030b00120b0f0390f64402d5483c084034102c4c0250301a540014800b036000c4200003095018108200040c1c044800c40440c103501 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 421661483 1250 421660233 421660241
    0xa050709050c0a050a050d05161e050405011416030203130506070b04030318051204030b0603010501050108040b0c07060f0b1c080a03092402220602060a230a06090b04 73
    0x18800b10910030016010b0040c050300190408403201d0030b1050800c004950701e1003c0d58800c032000c3c00300c072031208000120346400c80781010f0030100203080201580305540000e0b045100f203020712810310250301c090084102c0040100c808240c0c016690405600c468600a96240c101180807502c1c0d40c440540030885041400c19140502c1c0c124403824025100c1e42c80c250000c100030031403580440300c19008400800e00070024807504940ca980507039540c5256040c4003c02d07000c007800342e51080e41030400400150380d0040c60307990044d41001300601c041c1c41c0c1440d03461152042c11b02c020440c50408140d111000c80300e070300c22080f00009407a01314521a40c070140304000900c080c802032101e41d0600016101601c80d92000c21242d100f0185400c2031520082018041940d00500d411520317000a107421620345940300d000c1000707a1446490140a007080d00c040c5d1241030040c0500003055551891581907000804100306d031081c1c41a94800b00d041000c107000140000b40220b0005609000009141d81002e01c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 421662733 1250 421661483 421661491
    0x903081e040c060f03020c0109030203180f090402090613091109180d0509030309040501091a031203070e0a030f03020c090108070509130203010e0d030b030c0f1c030912050a05070905 80
    0x4840e02c02424031a0640e00c07200030592450816600f8480382c100c01000740325000b8881d000e50011610341d4001a1000c1031607418203250b50107030746415800b02d03180e210921010b421950458441c1c18940d41d00c1c000c07030f60600c50b07515140286810054440c0078002003498001c81c1e4a4103840c0758401707540315030110602c505164a0044030b030344584140d104440c030a1002e01b501d20310040c1600d28208200300000c06480003038002501d22aa80c01401162044800080c0420b8806070301a005a99503049048200e003c020503c4003484104a4441403e81d40c650381e400103141d000c90350385010107590500958903410401d04030701500340d403800400d511000107001740460780001c21405030b0303549401c600c0074160030120049801d503485a444a8000c0c0d014012001c031107105c1c1d6400540c0ca80860b0070546091030710b0700348a0207410442e10406060301c4480c030010100c0c0851030341d0039a44105103001c9543e01a2a84200110b075095481481000004a01c040c0f52600030021035041d1521031072410704807030003a9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 421663983 1250 421662733 421662743
    0x503010b0f09060411091201050f180607050a0c0c08010218010206131e0b01180c05070c060507020312040b0c1e061609050603070c0201121a1c05010903081e04 70
    0xd00020404c2c40c00d0b13000711503020048569036080c0b01708040030890344802106664587e03516041004510180300e049d4035405405540b00c01021410700700002d450300006850203040002c0010b0842c00103005002103400b00c1d9224000788603113940c41c0b1506000350405d41c83d0401802e00d4900300e2295610000315070b030082d102ca1200c03800d1007100d0f56429088401d10500314200d51141208840070503920641c0030300030324200b03141502410881c0b0b801811200109021003e100381806100c01180005400e041501d41a04140b90307504050300011f441d05082404a00580e0400280820400d00740e50190100301c01c402d040301c0088114104100364160500da40080130390ac80300014103155003600c0b211041032920704041000030388400110300f41e54400c4400402090a4108440031964000d41da00701060350a00100b08043c125440e51340f07801540e482003441011402c06600f0505000151140c1c401e40c460020402807456207000b0707203545004c03a030f05075400c0d281418140c0c1c145042d400c0148102c0d845 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 421665233 1250 421663983 421663999
    0x32007021003140a0b0d02180412021609180c090b13020c0c041d010e03040303080906060a0924180528090606030510050a0506060f070602030903220503010b0f 70
    0x41c500c032030010b2211458041e84490115a0200548c45070040028408079081c1a02103038178150809501c1c28207607a60742000c40d40000071603032250110080480a40c0c510030804544047c400c00520756984400b240a01203004501c0001348521256221030405407003175414645d4618a131200c00200c0c015020807401907004540c0700c0440c0d103000d0b8865660103401f105141f020f003500940340c0b82150418807420340303070390b1001030140241a08120041d901a24180040c5442e10f4601c002c102054102c1c46608105a10798403076014030480e024584003c44000001c402d2416a290140303003001c00900b602e14030711440c001c0411648032610038061a03103054031600388003070804000000700034080350405440569030745001100003041031194107141d60b9148000300380c505015212030215480540031a2141e94208501e940c60181082a0366405400ca40f0050f12507603210350541c150310801d240c0e8803200503100c40c1c0d003105001c02c0702988180c2e80c0550080110443d004148a100120032020703a9020840e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 421666483 1250 421665233 421665241
    0x11e0e1c08041401140708040602120c0c150d180204060b030c0708031003020402040b03040b06120a0204020f0d020a050414030114010905070905030f030c190c06050a03200702100314 80
    0x1100b08040c650f104103140052400d841e0550383c0070301c0e4100030400ca4481c00000340820003a0390400c00300c80950302c040b08140c035040516000341d5541070030003051800f0305161410740610700f1106003521106155818144072030700d101c103604807017108540400c910480c6400d00100c0e00c3c2c40e80c07009587c0300391101d410b02442c005403625290300981004100a880c09401140800161158006030008042d803c00c800d0300c80c10140790a15200000802d00c0f07001e003d03084500f000c10100003c41c1070415806032801640c540d003020b024061446541085c21480f0b00000b80b207400c0560040c0104110391160380e41c0c80050007000d0030075080c1c0d039089008002840c060380c0140200c02d5954401c5400c00003c1c01d01c10805941c80c0c011030700f030207111007444410340c02c082450030800c40140310318481ca00d15910041d0440100341c0c0c444844481600030030080100200301441034500030b5000f86034044203043d45031551480c050100d4a103030b00c4403d080380178005605588084034043d0248514100c1002c1104806031f40d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 421667733 1250 421666483 421666499
    0x1021507051209030702041e0e060411011b0210020f060912040303030e0a0606230f030d08040309030c0b031905092a040e01020c060c030403020318011e0e1c0804 71
    0x10191443c001070100304500001a5154451841c24005a190a00b1400081c0035160120780d03100c01400e125401200c200400140c207050761003210442401c00351b040394a4420617403009080d40200a42019140c89015070b03041c0c002580351201c1100c6411035035180d641e8000540c075001340c0c00c00b80e92204c00071b11040c030000e8000c6d00626a0070308000c0460350402480d071035030400e561041c0e00071420696914003003002400c12805419210b281592000104007072140440c0d42c030b2191810071700403c51410041401c06205544030001190440c036200039441c0c644c86004883e43c000d541d9800ca61141d030004045a003120301441e0310078080c42002d0599180324041c2c00701e228118560011010009184400c2c0a51722071090480004203100016202e141da80c9046140c0030007e4001102001c05008010009a00008a0317001280c40d50112114130302c6000180c0d0300400c00c115a0031550454860402c2480d0301060aa0482c5402c80781468044030000c507200043c0c0c2d024801401c441030070081400601 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 421668983 1250 421667733 421667767
    0x90c0307121101030905061305070614070605092a0319020609040906111c05072d021c030b04150f14030a0c080d02070e010b19020c060c010b0102150705 67
    0x82c806040216100b4030300d40d240c0e41082000c0300c8403400040164900f10501008204d2680902040e0804561700254024092200e00640c00300a24881d2a040011506d000612004241d012002144900ca202401703160b4108509501c555010b803080c41040c041c0308504110444401c1e401500c950f10b001c50f400140005001483c40907204143c8130303034892040103c1d8400030070751241d41149040d1030b00040d104160036500c0c0030301aa800c202042045000c00440207008224541550509451882c283c13078040e070605d506001224403d1200c034035aa003482e80c0580101115920403281040740390903202508406203494000d800700000c4980e4144400740d4000e4141168800040c00c0f00c0c40d55030240e580400d07201d01d90308104041e801100e00711500540401c551000b6040780203034082c0a60600e9810718003030003114841c600111154020000b03050017805084003406000d001180e40300b40c500e042a01a04d17a2164040c018400c1044101c040489050340900400d07a560703829192151700040c1305c04c80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 421670233 1250 421668983 421669013
    0x4020d0b09010608060115030e030a09230913021201050403081f0e01060c1401021e0a2706200a0f1703011508070507020a06031104051503090c030712 66
    0x10b6680d0301021130502c1d0304000d410300902d0041000b03c0081401003006003034540c4040300c0c01265206229030040c49070015194070a40d0055880c1034844040e10a100078004080c103212900400c002c0c3c00d02c400c0c10218082901d1050094440e02154590100c0590883d0b100700c40240000340050042011480d00ca49074205002c040070b103000c4400d071209007100e8044e03000c0e8000b85c0450054007030701c0108038158810105407800440214103000d020304220a1000c0c101101c5142c042001134030011710760044000c2140c0694140d03158010305403803180c0324840001c40c016a00880c0e418403d10a0054841120380100e00d402d101501c403284003507032481c01a6400a804071800100c481180f44418202000340d402810841804601c001c80c0780782c007500000025200b80c0070480100020005a251458034070216940361030005a490041081b004460143e60000b55000402c01401e820716802c00d00518081c0c0b00c100c0c2034462600501c0105a96000140b0400c0036544903641071501007070101c1b500000ca = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 421671483 1250 421670233 421670251
    0xa03090504150503011805160f0306020318060a06170d0903020603060315070507120905010804110112020c0102090907033c020c0a05060109050702030409020904060b0403050d031404020d0b 83
    0xc4191070f180004c0c2991010707111440098150780c0a6410310404214603290b18180d4405000014100310200c00700e1402404050b21080e000404a0341d0703410041d200b804016040002c3e00c40c0c50030314494070350140c00c041c8120840c2980340c40e607060f401c00000c209107981c40700c5601e40a240c580344ac1d0a1001d01d40000344000d80c18000c850760428802400054030303106e00f0755992060707542c402514140756504840b440382410000044424080759810034500c2d60415007244a0303d00d07241014004a6442081880c05940140042036410160a054010702888136046a0f104043c0d51406022012034030901c812145110382c4c1c6100e034240000100d0031000c0a112102038100e209504417201040c2d038000d00f04c2641a03441901c50006019041c00000d014150340785080c01344e401d181100a5482c01940103140c44503a000031010703070956075584507000801058590700e498070360f41c0c1040390f1540c401d0820000403031b0411180ba00d41030181c403034591140340e00070044404143c00d03807140c07198a0310003441120 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 421672733 1250 421671483 421671521
    0x403060b0409050d1e14160f021018081603030c1a1602100e1e03090a0b030105030601090e0312041e05010219020a0b0c070807061a0a080a03090504 65
    0x810f00601c5803908104030303038485022504801070003880d203070500d03603140e0708120041202099004c014011a041d20403450400000d4035082d062041c0b2154070100000d61000c2d001240359041038022102820341c11061008150303055903480c0700c6845400d41c820307054010034000c0c014070000f4042c000c046e8005000c1c1803590390702c81c00b00d80328241c511015102401da402000c2e070b41000007581000040001c3d1490700040c002e2003455190142d68045e590301114181c000c0780300c208620b1404000b611004000204004091940c038078461034241e20a00881d07020b402501e0000c641200c00d80158040c00205000540c9440c10128200c6018480078004840b42c820b00c1580503410040d07a0781680c0e00f10702400005139200046140181e9100c00b2403600025500301901480200300641001c80d40a4442e020003941c03020749161040051065040c003d00d09464842050102400d5045420f5056419a02480100c0e1034000856035450040c000400154080806200d03900b002d07040009a0300310360b03600e40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 421673983 1250 421672733 421672751
    0x9110f0c0712150e1924090b0a1d0a0615030818012616020a1b05030601060c080901120216080909160c03030b01090510081015050403060b04 62
    0x5403000c00500c090710a03049a408940a040291041300c014446403401040d40407000c40e00300000846840014002e040c0d4110303803821503103040c585984070b6004440d0400040c3d103203141c075100c0221709031240d085080c50910302030030220030046501c2e850070303114000313020b401e005558030009484000c1d1105a07280030b500d000000600d030755001c1c00400400e03024100448001c1c5000400020000d0301003098150071081e555418810101c1c1590044c07002d103042054010a68000d034540740c140e003030080051480c040c846001440780140d22003a04c1044003561481d036600c8030110303401d41d076403403018100040400c40031481c0e41c050500b00344012030b110009404c0c06564402d060a80034100015106503800089800152802c0c4034010380c040301c0581034400c01c0b81401d0000f8204410610014141a076070020b4000c2680102c90601c000e10000b00394105580030b00200030030441003034606407698a0055404100d01c2d56603500c8960090090f52001e007001d207152144000f4240402c5071581103a41d40c5540 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 421675233 1250 421673983 421673999
    0xd0b06010c1410050f160804020d02060705060a0b04050c090120010c0e0f0a0609060521010f0303030c02010635030c03040617100504021b0d11010609110f0c07 70
    0x1010b100248800a0b00c0c40140340e2200f84280c3d00010300750b44100c03810104014581e82c40c240341c0d0541040d9450b2824281c2e446d440407810201c120000a540300e00041006070400c980014100d02c00d03407080340140714280490f824002603950540b5107488486050145c2031035540719118110001541c025903a4a007010141108d00319405003840400140d0803607600c4c201800c020b02c014002040544500340001d1900c03500a002415a0099004003e0f00140e41500300813035102e1001101c802c0000ca04541d41c2d01c5040d030040015a11088001ca0304042c1c0a265180c010b1180000710b544e0010a030540b11402140c3c0362000000d25031001148000018404001104002411503100304000656690341413010190505000c500f007044038600100400c25a00101c1c4450320480d2030075600503864600c00056200d03001001c420304086403203030000d20748050364440d8542c07041e0780c5500005c101d01c9484042c2c00c402c1d80c00541e1410100d402c00c01001440300e00c244000d0500051190030f40c0c005580f18903823 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 421676483 1250 421675233 421675253
    0x1106010e0402270f0109150e0a0509031c020a0305060603150f0d0507090e06091c0c060603080a02010b010806030a05060112020a0807060c06050a05160e01051318140103020d0b06010c 80
    0x244c525207106070040c40425481e104140c841501d084c21848140d107001000700c84020010700740400240c032000401c0c4406800c009582030520100300c440d05500100404200075004440304000280c20701c400315401c0d081601c1100c1c000da15042c8440400030044081c0300305034410340c80103600325800b641c00e03c0100d0380c03d1001b580034100191010070034a8a0480c25450702e80050144403558020125066a10480711442c00c038100c0f680c01c151411704814240100106005d510240001d4000100c3d0102d241c0d041d404a0745c00007003621b681541e91144000e0580d11640d50b80c00801661201c00180600c05125842d08202840206921032181d2501c06d0b06007041225031240d00402e15401400341040420300a40d0740c0314022590420041c0b6024000c0e450400400e48070b10144480c09400c0b9810764480d030b04070382c04000e00303c0302000d910380d840c40c90a0f40d0704030020403003400314a0010015070304019006524102c1e90001d00c84500c0da842903c5140c4e0041000d45440e0522005100d030308002402004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 421677733 1250 421676483 421676491
    0x1403030d0c0212280302091305130206030c0d0e1908070c03020303190f0c171303060c0f090e0c0405010810051e01020f010e030a03020c07050901030c05011106010e040227 75
    0x100f42031800502c4c80035022806072a00d400c03401d140c014060030445882d8006641c004000c10b41d4082080c7d211550041c040200c4d5140180d00518000104400b80a10000800044025820420080000f01d40603038503288590000205c034004042c01c400400c00390005021594065140880060741c1d950000745164001c034030f0041002498903a103082c0d140c01c4400d4400140c2d00b07081400300c80d04140d031440405007225401302281140451002c50340030314691441c000d5035201c4010001d0b1082c0b1100a1314030015100e2102c000740c2e0114000c200d02c0f0213444613038096541d9031882c0d401c01e82020019074224000402c08285c603055110006000d50341da80920b0203402840d9100d02c0c400d03e03840d000908005214400c0021681000f40c0004248800022580441ca035890b0061311103021011940c241545030740001e80c030150000c00802440f80c81c2203850101c5009885030f0484400d5544c4245d141c00091040340c0c0040038038000100981815266006160410214001f01c24a0341c0718a0460750300947e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 421678983 1250 421677733 421677757
    0x20403050706090f0f09021b06240d0c05060c03190507060b03160306020a0c05240f010806010b0706091a010e060303040b031618031b1403030d0c0212 66
    0x7034010040280c00c03001c8800544900004101981d0409248003d1070319148500500158002403e501c0301c81c801199119040d442005d88a8034240101500c40c00442c200810000905030721040c0c1c41460110a00032039103a208101aa25a02c0e003020000303c0d07000040c0800300350000304095641c00700b1444078081400a6510b8076078a40c0420300780201180c100300300382c40c001d03405140080d000040b051044001c8039441400940d440c011004210f40000480c08024a00d102e5054144190f0800c502e1402d001c0f1080c0d4402446551010a400e041c0b003400e10030000290483d800501080f9030300401052014095140030424106d1940d40d01140c081401c1c0081c502d1003581f005000748003880e0000c80d007082045008500745401c0941607505440003520840e40c1d89803100710800144d001c0e509400c2c0003481220b40d107640a64900741107000c0c480e990201c100c800408140401c078101c80c1e02d1580c0030200c02400075802c0100c01c0802800070410030b0707688400d41c4154150005441c42000c010100a4540 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 421680233 1250 421678983 421678993
    0x705120409050c09030a39080c010c0b15030109140606030705010201060b041707080d1e080c190e1207170105041a1801050a05150a060504060f1202040305 68
    0x201d03800045500c040c0030500d080c0d0082008403010341e00059102c86440c1c00000e54400060403078801c52035a07505007100303440349010101c501d0b5812051061907040b21801c03000c1e00e03448140000110b48101180c3c1e0018240d00780b1a01013204020181440c200118020b00001980d88194079560ba0840342c0c401c0d02c134001c1e803100f004c011107820280800340007041c081c00240400c505104005480340118062440d8031480c0c4508c0c4404078104005000c01482c0c85c2d82960413040c10b0040040c00300c1c5520703c0c41c2c0c0c9000c6d40b0050f0407500d41d210340c0f405ca00c40e0049207101ca040866a0040d401d000642d0201e50301007120200c00c001c40c0346d4408818400b00102ca2008207a82840c11407001100c0122504d404500c5e4035040401021a65001c0701200780750900080d5503c035500d11348845c030142110140e0003403a40c608003c0064a0040703511090258125030148000000341c4020400b00a13098080c40002420a01042050034046c0404801c0034056003820b45602d07601000440c201e810a0703000b91216800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 421681483 1250 421680233 421680239
    0xf021207020d021506041109060d0203010f0f0b1206010201020904060b0a020f0102120112050709060603090b010e04150f0b030f01090615030503091e18100504020a080a05090307051204 81
    0x1040614004080c43c00984062803600c0030000e48a50001d080381d000355151200e050350b00511100312100c11100400494580344011a000020b4000340070792000b403100f154001c920322070103950540445178809400d900d085c04c014014a0300c113401800780c5040d0742d0240603840195882e402804003130a001c00403103882d0310000100900d0080c0140000c5400d901c100540d101100e0307180801e50544040c0503002541b40301c2c0d403600d2850510a94001030119240c8500807400035415089136078a603014030750240c4c060740c031050008802101614024810314030180c43c07844240498214a0000010400002c0c6441c80d000c04a800c0c4a500001100c2c0c6942d1441c0d000108003070303846002d102544a00c40701040a06507a10150742e48501c10340648103410005014881c20018800010301920141c28070500032411892034818880c25601520706084c19880400c4e00d0409100352000002d090341c1d914040d441d80c0303110500804000d8240400c80c0410862038010901c104041007019500c411301070341c1c5038a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 421682733 1250 421681483 421681487
    0x302100e1c020f01030e070e07091505030105040c050408150406021902030d050f040b0c030c130314010e060c0427091505060613060e210309090a02130e0a0f021207 72
    0xc800d0700b076050515181106c00f600b40002004416910030304500e00068031040030a551110195110f9906104446c51100506502030083c40c100c61060710280640c2d00c00400944480c000c030700849840e648000d0199200080e12402250014040c0c1c40052034000300d203c04054001e2600040005684009400e01441208ac07140540c000424540751200382081c2e44c41c5075503450058513030f0315456008000716003980000d00807500e40c003600081c015082d0303a41749488003600c50b440b94030484030751911a001c00305050215582c0c0c4103100420210749010f05241c85e070000c64040c0c0c06108101841c44201402d141c00c10710070007610b0340c083c0c0b40107900c42070080c0294050703920042c40d041c041c0e0f8041c40540f0300c6c0403410b00c0704001c0c1c80032800c14101840704040840d02e06a9104000113029251494402c04980c0100003400608000d4520b84a0703a0380381d105040c01c1e03200d8241100411601c3e800104000c0391004080c5410564144005c00c0c0c5c643e810040000f40d8021204c5900c040f11031f01c0511001e01d03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 421683983 1250 421682733 421682749
    0x150121050c07020112110702101b15050702070602031902070305030d0e060907060c0b090c030d0f020c06040f090e0a0611120105180a18020d12030e12040302100e1c02 73
    0xc0c0ba941000e01c241d00d10702c045a0a240610380b03000380612604420714202c0c6010380541040700400002d01c035480c950b01e050412078000c104101c10302c41c84c941400300351131500c0401e030fc0d0290744154000794a403580140301c001403007070100d80d40021400345810100014406100410b40700c025403401050031604200c00c94149980500b4903c0282d20007201000215040303c1c010b0607668001d11140e113256202070034503081c40d039500101681409003044c0481010340060039900302c1040e5038201c2d09000703924028480b4500c1140201403003c00080001c212840c4650403085600340c1e4130b015646c0c0c00b0103603a102c03000e9400001050022110210b080042426000507181c01400d0864561803445800503080303105110190101201d15240c2c516045000038100600c05040d0707001c1e00099006826081c01c40402c00c880609500081c20039030007400c4410f001425414440042a071546001e280d0750800000e00000030250007401248d61745008a940c52a2030042c0c1c00e49144140c8035502110302c1008000d0f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 421685233 1250 421683983 421684007
    0x90606090f060501022e021b0d020c030a0b012c010b19050a0c0f020a080f0705240a110c060a030f060e010b070f230703030905030105150121050c070201 67
    0x107600145d111100d40c00361120038444401246d03607080e00d0f45101030490019110300c40c91000304c00e804032214030300705000241041c10710084c0d80c2528001072506c000c05498080c0d80c00040c04510302c003030050245039011001c1d40c0121140034680070401641a40900b84090300b680071102e40c070f03030208105601c01070b03100d105c01d00e180c05450003902c2c101603000090b2062807070704000762284441101d210215140c880d4140c01400c542412140340101d2082c0c80b641e2007056029a0f4000c0340301d1074000c403c0c3e1400000300c00b454906064200d04292450204803540102c21184010b02d00c1401c0400d80395031039050081640e2041c2c1e950109803580c4201030039081e140d50350703c400c1c18100201c0040000300441801e9822160303001644c1d100010107401c10001004000c0c80c90700d501d000041d88400c440c100007400900b124031030f0f200c080146541e48109400c0ba10112051101034246811800c1958410581801e50090501e200d100d02025203100d44110b03141224243d20100c3c00066200c2990781007803d071311203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 421686483 1250 421685233 421685237
    0x303050603032107110303100306020a020109080d0e160302100f02010b190e0f01081b0609040204080622030c0609081306020105012603161509050c120c030c010e0301090606090f060501 81
    0x55810994105030411a003272002030483c82d8007160407200399101b9041001d07002c0c0c00100042d00c940846402da001401c85c031141c4c900c248100c2031031180310544408080d003280c0e0010030031421500d48920030f031030701a00244040110f540e1912025201d56170059020580030240b950140301d44d0501c00582000340014100c0f042c006803030070040001d55000a03403455242e8081911050304000d03a008214980946a170682d4402d00200300070035601c100180040c81000c002c417a507042c0520203180d80e80705081c014000ba001035450105a0081032064104201c2c082c031440034a49081e13111000d44040c3c0d032043c0c0000005035111401004003480d2441d10000513450425203503400c1020080704c5a591003009440d407040b03e0242c1c00602071010751042e03000311102c0c0c00f5052200c4044d1745840c64503601014050f6224035040d0096068058000586915540c000f40040030b41c10300c032800643d2400fa481c0c01030381e071664a52406500040460007120001d095000b00807079480210306164060f500c1a03003002e81 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 421687733 1250 421686483 421686487
    0x6010f0809120d020408061e1003030e090c04120b040308090c01120b060f0c0102070c06410a0c0210020303101707030602030c0a08100803040303030506030321071103 73
    0x400244003082c900c1614000300e41080e0f441c840000003001074007490388040d801e8016401044421105003040780203c0d07124000740010f80d900c041440340c550100d40030180000310840c0040c100742c2016100346410031b80004080303090555034146030342c251350404421954a0303d0101030000309034102c02d212307803c0b03104600035080034825400020020103184162801040c0c841040803542e0300c40e4000c443d4044001e24249545504039101036010b58060700040f100004c4d2900300180061145c42026251041e10600110000510345c005100c0001e424031034651070829007500061a80220090050250a85a00704240389500400684548028803402590800c00030084075a14500401c03003500c100051109401c0c496070380640c90901c05e40c20081070184000240090541d1603405003003900c003d81d8501e0150381ea01c10341924a081c1c507125025455006000c2072000900a070130260340a08013804036820001104003102812003c1a03617081041f5003c6e003030003481940302c80081484440ca01c0118 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 421688983 1250 421687733 421687741
    0xc110c0109140105090a030b010b0c1009200a18090b0a0b060405010815040903080a1b051c020c161a12040206071a010806150406050f15120f06010f08 66
    0x12102c09600341025040120020b140c00c2e0f10707a01c140317503003014540004501c107540d0303103e100840300c9034003600d88070741c1c0d51082e021403148161035030103030701800d59000c48480c09100802429032821400080c150383d010740754a00104140581080c8a600200a15000310f00f081c0c0714100784600c81d00140000f00c04500700000f01c105270304c84030100c0b01203d1080c60484850f66800d2003541c2c0c00038070584403540c050700300b400b148103140d40002e045000d0058007800300300c5400d89060150b08030548840c1c807408140700f07000414100d089200c2061400700b40042c0540b4140c2040b05442c1070001c40d117402d41d500c2d0b0403068144005000f200d04004e80d4609444001c2c07404040005c96500755500900080c850840001d0b4607003045144013030040889214100c5800395610350a5158480404072101d24106030b581403640c08a282600889084403806002c2c82d41011043c410701640b107240c0140c5004242c01000004940940d42a010740305802000d44100d01c1d0070260b00050006a0071280d15040003a8a0700740 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 421690233 1250 421688983 421688999
    0x120b04061b09061106133017070f0206040303020a05040306020403082511060d0e030a0905030c0d030801091808070c0e0c040b1602042007290a0902010207090c110c0109 74
    0x400100d43c0000f42da40300312002103899480c0f81f9515400e03a011140e501c41840c865a08815005001c0e071a81000300c80c55030710640115803d030b05071b40f0f0349001039000e8000716001c03e000364014031880405142135458203480342c4175a400c1e85c1c0107520481e0000400584400b80d0000150f45040c0404400c100024080030742d2946007090300030070710b0076204200002b0a8504542540e02000510603d141502c1d195080846c0243c10f0703440134810507020740a0090748031094600f4402c013466140e031585400c0b000703908000c4010002c104418500c90b4440d98118800b02259481d0042c0409030b05c6503544c4403c00d81080d01d4100d0950340a8101c0c03450b04c1040c807082c0301d0315000f641500e000070000c0110403d0728045000140c0544100c0c00e417117984003030803192140c010f55000c00815005004030003d01001e807035024030303d15820100d100c0b0380303885070b140300803d10062260b009a0100e9005104445c3c009031140360b003804275140700c407480020841c061083c400905c400e04c540d0481c2202400e004000d00c0c80d103046 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 421691483 1250 421690233 421690261
    0x304050a11180103051c02010b06040e10032406210b04230d14040f05061b0613031205010f05150706023001120b04061b09061106 57
    0x1407080d8680031251800d501c5508040215011100840290356902d04213603840d1646c01d80654850385204410000303a500502580f2403100780604218902440c0c0384560101c11740c050011038104160040010114040a02d5085000040d00c040303000264443c110700110741859028003220102c0040341e6000c50182e8407144c600f40e40250205500b41d86600c2d0450b0048100d0020885000e818070760305004040c0090307956444001030306e500480c4445210786604a005501c103c8070701d80301000f010b101a007400005407001c030b400c8612040385040e10007041070819501b21004401308c1640c144e40b80c00d00d544842803050080b50400108059418070a069035900e01e18081e070790084082d00003109400c00c502c801c5403205074100c0c0c7c0c11501d64030030301c071030400400046203500403848015400600c100170040500b8101c400318238134803500030400d541d04221654000c00c1685c02c56614210840c00c1081c1c02c04c2c4001a4929940b00054142401406041c24112040e004101c2e841141005014044106 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 421692733 1250 421691483 421691503
    0xb1c03120b032506020d050301030203030307031e0f0b01081303171305070e040209180601060e0f030610030b010603110f09030102070804090605030d0503160e030c27060105030405 79
    0x680031400304002000b080c40c00e00812482c0100c42c1d9400003641c03400030f0650107201036607219401d648941d100307400c0440d1035000078080a0351540040000c00e60f104c0c044e03070000701001c46803101b80c2e0b03688408080304000c446101e1103440455480c0c0503c50003039a4040c0005a1000f2101c3c2d1540c42d0b0700c800d4074002c26118094002c49514600e1001082044003c0f480c2c0e02c0303480340c0c040121a0f100d40c48000101040100303480890060f0911300c0402c0b607400d080c80181088080e190000d0815a00e4000d04035010b40d4008800303030308024440fa40180b50b4400344686440346c440d048900e85118590314180790013050581c0150201761070702d01d0061051241c031086031282d658032000d4548503a80c2c1c00c006802032094010050500d8800940060400aa0b40024003114130403400c0d9081c1000e100c4041d00c0c03a2204640b001e40c5c44c1e24480c45e06035060300580a1071142c0304060308403026011100041078031101e209601350220f10110382186010750100d101168000c0e02842e0450460810b030f9541650350050f56 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 421693983 1250 421692733 421692767
    0x8061c110102070504020a020705030616021207021c0506180105150118211506050d030302071104050a090c0f05090f09030d1811090606030a020a031e0b1c03 69
    0x881804550382c420003a800c00b410f40180110f595007041e0601940d031380440e00c0349a000740140400991484606007034440601d15580280c80d41d96109000d62000703034010ba200320390140d10f0f4a821200c0d010102813100600744904000d003500d041c00101c00000c0310308003440074a640e051400304010420b500500c9110309a007802d00d204032505c110300f64081c0c45102d4102c844010840d10b1a16043c0601c1e800f0311000d64004c2500c3c0b01070300030200400080e543c0a000302500101d050100000003440b03503000301402405000740c4068a0006400141560010340e21240b40360b845000b400280074182ca03803003006110504e0b1039903005140902054844100400242d100184500058401071081c002c0321610030001e1410040d40481c09042120219018015203101c0e0600b0071010031401c107030007800d0003550300900341401e40c0ea40510130070183d40080011700c105600c4401b041040112669807a6100138804400b040c14000a01444070725041c4800d0b18103d4818a15503d000c644c00490441c030040c3c0786 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 421695233 1250 421693983 421694003
    0x172109060901030906090b040b0709081c030e060c0a0329010810150c060507030507080c131a0306180c091c150501060e0d02011220030f01030308061c 66
    0x41c0c00164002d02035080042c02e910708040744a82044031040b0100d2103207101f450480956141c3c44011608403c140c060028503038050000710700300203210f0040c2d10107410389141c0840c00e812401b0300c0c1c6046c044e0a136080c1e031a01c03802260004015800d809003d25210000440200c450b515920b184003052280309050f05012449000c2403904100c0b8140380c014201903001d4a2200001840c006c0510100d58016601d2925210129084902c41c0c01054001d03421940e03014000e86446500140d0b81c1e105103401040d0014940d400280e0900ca45008806801f1103043c0c940c482ca070520a10010102506000310303010300340c0c0c0c00c101804040a050b605003d43c00e03220083d174040104441d490301442044040d14055180202c1c803440032301a00070606a4485580703403011030048034244985104040070080c0420030035082c001d0f40c0d44040c0d0101071241c11109100088682e9090b0404dc958010b84140c00c0c82202000144149504000c510b5041039081d07038408800300400110315034586400724010401280 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 421696483 1250 421695233 421695247
    0x10f0b36070c0f0c030b1003050d08090f100501091503080a05030a0f0203010b03060a09180201080c131d060d030801051207090f0e161d0a090c17210906 67
    0x4035502c1c481c0c040760711026a0840f00054180040e10300418802140c07114100800540600040d5840e403044030b81c807400421041180080569560b90000c005d80c2c03003485050b084502034a810440c1484a11030001c0004540d41401e032218192580c01c41034280c0e14500241c2000044d4a090031502e104100e4a8031b2a102d03100d101080e00601a03900781090130318000700c00801c503400ad01c0c1c025070003400704035040b21207140c1c4c032141141600e4a004003d107034110003205110255000385c0301d02d54040705100b0103d28004001041e20072a100710740000340072001c010b5981080000944901790802c60450700800c40340090342e002404120140a4103000d01e1015800c0442c0d1102000301038090600340c40c060244a24207001740c030003400c1c1c035070004c00f07607220b8960304115244041c8111000c0e00c4050503c0240381102100e802c041304801b80c4202e251a5680900b400440e40085917140035045220702c40000340041c84e070062500c0030300c901102c9501a0008408a181459012144da429090300d010740c50b403030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 421697733 1250 421696483 421696487
    0x3032006280e0606130b301b0f010c0b040305090310110706090f05060414010f14161b23030a0c11010306092a080f15060c010f0b3607 59
    0x280c0218035900400c981c803000540e2030513401000580c203c10040e401f00d01c08122403a070307030311010403207030340821014003800c1402800c08a010600c43d2006042c59000c4213442d03a10403034801000c540540009a01207911140c500d400c0c41031400c1c15001c2d6105101c181c6c19400e8000e42e522505c0d60080009a452002504100b0f00010b01d0607100e400c07006030341c01403a0905040340c90a4080b4035883c6154070f841203044909600340304052000144080445aa41c0c902000391801d04c00407408006103c2c00201e86481e681108052800345803055811440d07110480c10000707100c01181c1000c000c03d8009000034148141c4c02010300702c6032500303e00302121030504840140c0c01460980c020308201d0f41846020401d014000b0300303e29400d001c002d1090803e00041c042180c01d41070940e44d03201a200b29501042041401d049200001e4100400c0c56260544d09501207084450b9000280782c065240c214004076460001c65814030f0490084507c5007140e80300ca6018011218007240c154400034080210f1043c038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 421698983 1250 421697733 421697741
    0x10903032f01020c0601151803020904140a110a0609050616140706051c020319050405010f020a0e03010501080d0f05130801090c0911070c03032006280e060613 70
    0x541c1e28000c40d995112150002c1d03c50700240148081600121151f0321018855440708480440382d480e074220340c80c1982e00700719000c40d0141c000e64680d284940201107034941400060580340c40b40568286400b1a40c0c240442005243c0c408014081030031002c001d0303610340a003201c40c1000341c40d010251302651840c00b400c01c0d48a0703200d42d02041c0b040880104403107400200a0002039079000c00a11b200d0b44241e130f0003050748011180d215465071650f10342c1350144652303048960020701c10300000c0b0301518561040c1d4102d0308141200300010b01100d200a0b40c0b41000e104050160035a08040e120798200ba10020740a80180e4182c501040301c00609420284007020808001d0680c14000703000d05d0310f4070b0900701070340d190702d0040304107191809180384840d1901c60110748445512003010840c09146440c2030301d42e4545420000301c000d0800d168090300203002d00030a48030b030110350350383d01d00d801043c080c030344440800500d4000b07050700d4400e060310030b200000740066000b58215428456a008044250094 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 421700233 1250 421698983 421699067
    0x1030e0a05070602030a020708012a03060503030f030f060405010e220c0303170a020a09171e01020310080a051c1403010e070f021606030f02040503151501090303 71
    0x103001d00b080200b0b055501100030241c1202c194200d80036242c5468400e4201c642400f02e030ba6034005440a00f89194a0145404540303034a28180026404d9644002c270381940c1c4640301c0c01d004180300108220b42d20320103c880039082202560100f2684d814800142e01ca89005071900000701003c410140c500640c10215540284c0c0c0841601c10550340c0303280280c00c0400000035029542d04100c000b034004e103000d00c240c583d46052a60340f0340c40540f421110442403045002091480e014104841d201221248500020112444001a076a181c0100103008882d0642c10070001a0006080307480401c070001051400107222001e031800212001c0c80580d0501143c610200d110320003c0300001d1003040440113031740314207516180d00c08035030001c03501261101c0300d54010040f0f500070180107000ca90302c242e00c09203443e08600d0005140544400c0000d00d802c01219000c0c0400b00e8440070000a00010a00b1031180310081c01c0c5028403034119900038000110681ca4070100c00c034000b40c2800360203a415001e00781 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 421701483 1250 421700233 421700243
    0x120b0118020c100e1c0203070b0403030f150501080c091e03010207020310020706060f0e0f06010302220315090213021e0a0c0201022a0409050c0901080d0813020f01030e0a 75
    0x1207800b8400e4584040c1c40480303030801e464024150220114030010703486105c1c61209034065850005203036512020f0000250095040542d17649411b0106039252003480d2540224445204045140600040001c0e0f0001c0500903c01018003286829445000f0164180c1c0c1ca046403610071240401c01090080c090442c001e541845800c03c142c101c003031554000d10201c0d000e00b00a0204a4031440554401c0089e8483d260040484000080483e1001d005d078079080801454090714003805100900042020f0a10f074020140c50072001708108007554151441c0104203880030300034964550000b4901c04404000e405240e0b40005244580e104407aa22180d840c60064643e03441d1006040010203142e05258102d02610130031290740c86420000b03150840322892501030018070a070400901014000541c42154503110740b0001b81d4481e500d42410a020300075290042c0301c80c010010005200701d07405004d014280c0000c10000000d40c0f01d050791000880000c0c200414000d0f0a22011440c0401c40c40700509 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 421702733 1250 421701483 421701493
    0x8030f071a0414060a050402090403121104080d02010e16030f052b1215120f0203010203010e060109090603030203030714070b040506091005012102190e040606120b0118020c 76
    0x300b0040790903802407402d4101e0341104c900340e0314400d00004490007036901a51000b0318400050029100381a0500144107007100130504010501000c0d103540c10039045020242c12007811729900e6a070910500580c0c000301c40c001c002000d010920300c2803020701c902014210214502105040c0202008a15080000e800300544071400c820b24124545d0ba83d00a008001030203041c80c108905030030302a500d203400341c01c40265070706e600e411410410b030350700c100b000c54400990541c100003503035003031018600902c40703c460415685810f50004040b141d01d07410200700c48d07242240c1800401c0e80002038030ba10070030174103048c01c03507039a40000049207010b0034100920302c48058040000f0000003040c1395001c0e000900417108200c80285c96081580c409014030b00c07000d01010b4603900100c04822028400d9400030b0f00403001d502e03540b04011410344d4036410420034406c0341710610040044501c588001020181a00c00000d04180c3d501500b040040c407076041c444200702c1d8907904600e2294101c0f8a10000c84080712 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 421703983 1250 421702733 421702741
    0x60c021f0b01030b030a030e1309020409060603170a0c08090d05010c0c050d0507150b0f030d0801180908030f06060f070501200903070e0a020714061f08030f071a 71
    0xd00035203048809240000d043c03203622030365400d00003062044a5419115070701240c07280418009500c1a41c1000e40080e074a4554000140e10340384140c00c92540680c0012a1660650403c8800c00200386007414003410100200ca40407036200e03180403110350307008241581d034940072000a080c10181c0403026155510300380030a014150801565180e07144507d0607103400c3d10300b0a9007520617000300e05000c0c004401c480110f40e4102060b13409039a01900061450500e50103545c0401c1c5003a00340c030034050114070104014820201c40200034400390f9404101800940300950f0781c3c50302404044e2144402e403a40002142e0266038040588070020103a040b181c1e00d4400d039090050203071680d5480640c0c0c04014030140324880f0203100c110b079888100580102607291415407421a410401800042a40e0303091001000040c0406404007045030308600906142c20700d40040103007510100b101090810100e44100200039010083c0d0380d40180444040351100310a082c40101088401c60850300d1041e00030402c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 421705233 1250 421703983 421704043
    0xf030a1d060d020a0e01030c050901050d021e0a1b0c060f020c032401090218060d06090606030617010c0801060e010c0822080609060606070615030b062b060c02 70
    0x1074004ca0000d0343e40d0800c607405510044d4220b072081c1000d81e001034000c000c001c80315401540100400160240c0052034558800001402c1c1182401042080070000034214200d607031065030503003528001140c102002030701e6516001991594420003040c41492040048603d000740503000010001030b0564030540c069482000001103680b0441d454450288000b148414152003600c038012886807100381c03d030b5201402c0202907000000e0450b040c13500d0f840301088140090080360002c048a880208940d4240758100c8481303008070041074007580c0b5040804240d60752100c081c90450b01c183c00e10840d8401e428004a81803840750201420250b400101c48032484451500810503c5075040040041074485000c0c549803042543c2c450302e283e022801180d520700d41000144070042c0b24190000364481c00d0188210044480d52069034448207900401030942000c401400c9012007954a440030710702140741d60818002c00c100058580c03035543d6002040907000b0080040c00203c0004d01c03210741581d5000c9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 421706483 1250 421705233 421705237
    0x11106100f06080c3f0f0f0f1501021005040b010509010f0b04270c0807080c0c03030a150806090c0307061d1005130605040f080f030a1d060d02 63
    0x810907150050640082e00038842d0620324012003080040c246011000000b2480d01002c07110f45a000402030310b80c044190301e61007000402500c4907000c5684602d441c02452012180080c40841e5441106003040b810100007a003da03408940714890441450744440100d140c45200d95911207294a84401d04c824041c01c98441412220b04403141a242ea803504035600d414000c510400202c0310090009000c824a24450304041844036141140e407100c0401044083d11411020078011508000c14004542e905c03d901c154040040810b03070740341c20800004941d40e440000c041c1c0482c1a0b490b04903940003480200780c90b00810785a411521076003000040c5584038800c1c0c440b2031344684541c2c41300207a100c2c0281c41807404140803141e801c09c0c1f001c0b16014000d00d400860088020454100200801d00340c244045c90084d04131583c40d140c5039410243d066010095a811011556001c07c02001a65100008540740d0303181d64500003c00307068901186205030300340e034840d0b944003034089080d03a191000c90740 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 421707733 1250 421706483 421706489
    0xc0b07180909020a08190b0601140a030b0405060105090a05040f090813061205130809030f0d030603030216030803041e0b13020f091504090c09110c12040509060f01110610 75
    0x11300040309030b0f441c00c521b0f940b184881c40c1c0b040001d030301703840b1540850780e00d0041c42ea2258060510000300c2c007480200c407040343d0003800d015001ca5600d407800045410544943c603030050082c2061840d203c01c20380010340c3c8076414468184542c0e00c4001d8005c1c401940c1c4c218011065202e50b03030980390714013144515035140c51800b0382e000040382c3d800c2c10281481103000d0346000c0c0c400030510603040c40e0143c8921000b030340400703407490b05480cc10081d00300301c0030104411551030289541c0050010b09519000b400c00300c036203078401081d039407030181070000c901d1407800c60742c126030322455022a19170f03608040c4003091462031029010640c0d1108204c02c9058016141000c14030844012902e20045820031240700b000355060814040d4000c400f108074103107580020710850050481106566481400b64103444010741103501d840404100030078042e8082002441d222034041e41e0504060a02e400301d070342c6500c0200031505c550810200144d80d82d0160140050804140040e100310f490081c0034040300c00c0e0148 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 421708983 1250 421707733 421707739
    0x90e01090f14160b0702060a0e1305150d1713030602030108010603060609020c0606210a0c0f0f080303131703040f0b07110a0605071115070f0c02010c0b0718090902 72
    0x1c519480c1c2c241ca407000e114203984030011309504100c078540920840f5002000d040d424880c141c000e1103042c2d60f44807014041c4117203212001c40c1a14042600510303c2c81040c001c41d0041000c0510b401c005402c3d000e000c034202c1d101c8241c0e40d0f2110b0010582d528130f01d4280d0b10240410340300100100b0300d0901901700724140c034010502407081a603511082c3c0100d11564041c5500364010102040d070500d0710410914404628a542c001015000302c00c1500b4032000520803105400f04580400580c10b1507039031400104030b400105012185800c2c0000d80300d2100400361000580240201c00800a07248021036040d1003840b52a5101c1ca0300b031621045510f8002000d40c0d2030845400040c62442c401c0d0340f400c2005450310058000b00b841075590710050714001c0e08000038445840300000403504200400015030019900b03043c82c0f070600a40c040c10760402c600102040140300c0803c0400350f60400d091203449503200c0c50aaa241d5185082194200d5083e06a1980c3c501c0f1104002292845a040048054021 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 421710233 1250 421708983 421708993
    0x12131202280b0403030f150f0512070e040b060105120106030b0a050a05060901030b1305070f0f0206040b0103080703090b0c10150e0c0a030902040504150c0f0504090e01090f14 77
    0x4196071480c078600714000140721900035000600060b01c80d4100300940d210b0302e80045140e04c680440111544180d030446038412462000030491880e0400300c2545050310000075000d018202503107030310a220010400381405200e00301017002e0b039101d6402c43d004059a0290b1001070750311500001d01510506c419907100300711014010810b8a42104940300321034004100320b1405030090015000342110000781c03030b40a00000388110403003449000d402d00c5500c16607140c1c448901d800401502e0103945070465000c5510201c108400035001f0903116064a4100c0c01f540e8035404189002c507201c0d1125001000c0b000008581c444800320700203005c5101e20320503107041c0008012100c2c1c08002d13903450300c2480c0328180d40301c0c041081580c02d10020326841ca505c4ca8086039460036600410300b5036074103840032100c448804202884000d280e10501c040a03601d40f2300b00300f410724001c0c00182640520b0080341a41d036a00c24180302d103e1425807080f20f06a40c03280c0c41d10032940242c00c2060f1245104050443d0034051 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 421711483 1250 421710233 421710283
    0x309060d05150118090e07030f030309021503040c030807050102090301090c1508090604030509190e040c0509130605072003030406060b0705030a0315032f010e010512131202 76
    0x55595404451001c20400c0c64a92174442003101400d40c4200e241881c1c0291b031804404200c1101c030141c0818041c2c0c4021981e43c54600c10300904140b21000900c0381d80c0d040c001e0000240d101c440350811607400000c455241c40326800c0082c02403143e25840c960561034503008004015150001d02c1c11281d04c00c1d501800c0d60340200f000da840c2c640c1110704c52040d802007400100000c2c01503002d04500c520140c080c00c8205903611115415070b600f500000003034520b41c0104030401001d0f0426801601c01510b10a080c3d042020a002d220f00c44800004c117595106c500150400d4814460080d2040110003041c90140c0c19007401c3d626503205613010303600c1500300a000700f91a113109048400e10b030f5111300214504000302000710001c00a03080003e44585200a001010400449001d5542c01090614a020200f84030400c0c01c500001a081418081c0748850509543c0c0c2103c1030b01c5c2008000d49203400d455039045a039045502c0410001003190415182d0982c1c0e8540c001aa0598030207881c01c01900809 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 421712733 1250 421711483 421711487
    0xc020c03210f0f0f0c0706031a010c14010612060609090209160302040521251403100c08010f050a0e0403030f060f080f0105010506160f050309060d051501 68
    0x40542880740c4441111030004035840240050102c04002c603081410301c10003030500840d541c888542909940004240803080c801c0900108004100c00d0070204000718020720f00110120b84c0c1c518960600440400410500061051800d00c041569008010440d2070780980740f140d000303045069030014a17091000c241041c05104040003207400408a001e540d6603510b0515800241800e0442090f800340400256502d41000500400800900c10045c89166402d110303d4080c0a5a04580000706c0010054824460000c000181c07030007a180700c40c26006500120386800516040c0b034044500d44070300c0900781a400b0000c64182c864000071920010b90b11020481d01e86601c3c010307201c002c1c4c0041c001c100000e02030751000b081e10070300580208009588100801e94007015a100f69060f812903030804e40c4441c0288105030140c01c044600c141060404082e51201040d945002460360600c5030051062100c1041524401e04000700311941e1103900c501e245d80504000c1c3c80d0201046003254a02c0460341c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 421713983 1250 421712733 421712743
    0xc03030b04020301080303010b03130c0b0403211e02070b031e070e06030a0506190801230408040303230d020a1b0302250302130212012102060904021605010c020c03 72
    0x1745a8801581140d082c4103001d1150382c0080d080000b421290341106000564500100000302061030f000c9840701e2541c1441e0603101010403d104c0c00502c0f42161425081e040045034040c1074000090b040304440d42c2100341c3c03400019401803040808003208102052060740041210350020200c4c00d48692150f03401619011009084550302040c2813000a0303a885180d07003e1503109000800c80c1d074100c180d0443c0d002c050b00141d00070000594480300705104111001c40c90550501506d0a00b0945150a0715032803054050f80c04010108044050300e84110106651407600540c84564a190398040e1481540008d601c0760cc001808640085275810f030001880c0040e02c4219010b401915808144105c05040d03049106120200002015400310150311228050312480301e14a0005030749004407101888000c03c164031500e03001e80704107640304460715220802c0755a42c0e0306a40c2c180d100c07911100003802074043d10b0407c0d079488800c1c291480520205401005140c511078080e5041d0078841c2003896150 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 421715233 1250 421713983 421713989
    0xd02060115030f0209060705100b15040308030a0212180d05041d0604061e034407080a1d0f0a1205010207050d11060108072d030209070c03030b04020301 67
    0x501c1c040c0701c4041403140a0340000792050101c0c40010700c2c02c0e0424000803005c4e0030154054030541e21454080b002c0901700c2c0b0802c1d0801c0c104840c3e80d0a2030131141940b07180c2c0e10880c000142445000700124101100e1601980c3e07000c071440a0f0071b402403800346441c00909805404075643c92050804031800c0d240650304403025201046030b0540d203070700e003000494050344024082d190410380d140320000e88540f144619803c8070b404003540302d0306640340d400d010054140c4c0c0710f2010410440b4543c0f500d0104040e900300010350340001d2501007880424091952039006840d005054444006100c2c99178603030241c107501c42100740d071013400c42c6006124244111040b10410184d0040120a802d0024000c007240c00c480c000d2040c000076181441980c1c902e03040554003020400403640341074118580e00c1c41406500d005d0080c003002000070301d242001c200c120301c0080701c0100741c5e1000548010000e2a0503c01100615009820098242043c1d0401490843c203550142d0009140c80c0105403e440e00340216812 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 421716483 1250 421715233 421715249
    0x7081903090b0a120b1216030611190f030905161d060f240d0209010f03110306040b0102030d0c1e020f0601030209102114030304020a03030e03120310080d020601 71
    0x84007161303000b24000d003280c1d0205940002510240d0401400402080760030055100300c51300310a1a51600000742c0354074641e1030b0720aa4040c401015400710887c07010000321114905003000007003400302500141200100074040340030f405140300c09190034541407030490f44901c6000c8100903100e00c1100b1507007002d45503164000b546000c030840902d8000044401d4154941081009000780714200d0f0031030f072003603502d040304940204084445603000615502d0042c6582000d02c200546001d11200e103100c020041407003656210300c20091030341300b003064841c0c40050820410500e540400c0181180c206054040c4490a581c80c07500e00d128400f20713000c8402003c1c803000304030a0b400e607803c003e1400801090119001380b8110000380c2c1c2da41821441c00c26141445030303000b64000504084d13148004d40e0040b010998020420310006807666092541129014541825141e5a20700001d0400b0052040f0625110303011041c019100300d082d001e502124903210480d0011039612030107903100c1c81c00b4424000c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 421717733 1250 421716483 421716497
    0x60e0d08060d2102030412050a0203060f130224030a05010e07050f0304060f180b0103031206030b07030e0f0a0308060a0f0b041a0721140309070302060c07081903090b0a 74
    0x1d0b00345203040031600f280c4980196403c098464400c2c070481d611020b41130740c03d1740c0000000000d40c2810b019054010925080d01a4640342c60000740004210400000303002d269200d185101514961354a10b0400c2a400341c138070350320700784540f01102414003070203030a02425541010601d414055030444a001950702c2d40d00c0e095a45507140d41009115091007070901d1600e80c01008002d00c400782000c407000d07208055810a650650800408400b60340e4004d0604a140050500100306030405495124501d444e0105102007180026410700c10150001a075a100f81d2405408140d044414a0b110b418259003980c2d40c265142070000c2034040510454410700d0040009010010440e0a2018500721040c083c2d454040329540b41c020a142410180400d011001405099194030a0385200c51000c074030380060840c100502455181c8559101c001c1c450301c0c000036101c14403641840403800504c12241500e24100040c0c3e0100400300401d4030480000354404408160b544002e001c1d10060461031303484c00c0c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 421718983 1250 421717733 421717763
    0x30603100f0608030403150e070b0415031d0a0314070b0403110304080d0e0108060a0812130902070804060216031113020c01110a020c0607020607110d060e0d08060d 72
    0x20400101032070052600e88001080300034040001300000e500c208603003000100e048161000304c0d0800000000180c005410410403428001e06540c1584d4800004130301185501e1001d4000701511250200c803940003841024141d2008a59441040c2c0203850b44805200550301d0900e01d8851117200800ea000c1d00004100820300c142d02c02da400f208080f00300c070f25090300c61001c10314001506404030001002c152500c40d0310359100e001c154208038151002d0070b03201d04016506031640c25030242d00080350b001140840300002e490850f4402800c9401c0300b195164190b0509101d90386c024014840503118481c000002d00b000300d0422011a0380100c4190400440401080780843d506181d03160f8203a002d00441030b080c4028855840c01120080c40e269446003210006800c140d990740c0d006119840500408000d600c481c021035080ca41d00508038000040701c48001501010b07010341c050012494491960b501c0d00d00002d080302940d125448451041da20003081241007404c0220003080e1520840d980 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 421720233 1250 421718983 421719013
    0x9080c1813050a050a060c05091305060a05060d02031509090c0603071707020601030203070501051e03041b0b030105190501230c010e07090e060c03190209060a050717030603 76
    0x200e900180c00140001c803040003500c80c140b40c8142d1400607a030030340000030313103008012507031155071032182140c02c0c498101558200043c1103901c14a1380c074000d403601d600000d59503596044503038000c2e110081c00301d500da514042070034009400c1210886881c654249840381c2d280740070b0402c24451003410f001807500c0400a803d0251540018146000b0b0140421001c0410456140c489100700500da001f4006585076004262070031960f030784200c0c1406401c1020b03580f14100d849006002581e0360652603034030340342c2c1c2c600040c80e441412540138500d50056030200b0944245d000550403a60708641c0101d500706154542d10a043c420f100d004e001c5410003400012131203d4002d024000710200801c117041c07034030b01070381d0343d081d83e0031425001026000300d401406030b850710f0b10440c000c1600307135001003d1520303203444070400310b1202410036190700f500032080c0c1c0a40350385a01190a00c12010f41303101d03119003031a00f001d001030b00000c008582c0034000d19169242d10502034203403881048000c004080f00700f540342207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 421721483 1250 421720233 421720279
    0x3091e021003020d09080d0506280504091e0b0a290d060b0a14041b0e2e081909050304120c0b07050c1009030503120a1401080d09080c 59
    0x8116261700d42d9949400b0640880c050b00c4482ca5a480100c1c8902d0000c0411228200f6810400c5607501c3c0030104010100a903201003003511000c0d03500103000e07a03d90030180210301903e10f048000d8401c10080404001e043e0f01030a01501d0b01140902c5101c03050b500484520703d41102400140300181400109440c00c180201c00d55406014006116407400020a030294001e030848407803016404150b80c0e807814075100702c00a150240c6021030040221440040100403446a03482c49400e28044440c80e4442c3d10700744c140d60780300e02400000d12480c0e10310b000d0207640d0212070030503121111001e600030085040c051344a20300e038410040c6207000c0c1041c40c7c980c20440c9100b02503810340c0c03d4000114004005000622046004d0350092004e04503404c10014100c045074840010480603980800c00110000162910002d1080c5d040c07404d9968013500000400d4108c8949090041c0d110002414680c08918410805803541e1400c0e03040307440319881c95543d1000c48044c0e81050080c500095a074000d078003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 421722733 1250 421721483 421721497
    0x4020f0714070b18040b031c170907060503061507030e090702030309060f151e041d060f07030e011a0307080d0519090e0103060203150f030c0409140d03091e02100302 73
    0x72002581b50a1440400d01d810300a54001e00d0001d14040f16081c03042e0000002110702911480d4240c0c2d61801003000c0761500c0040c031824092200c040080380f41913854802064070340b000c1c440045d07140c210b241801080c40d0300303840b107841c080d40040c03003c24000361004c02100d11520741003004000035102e503074100c10240b0300203040350321101182140181681d03400b401a80c4031180101c0e540b2500001a080104440828820440d01d80c007170000b201c50810045200e030750104821061400039903954100782e025042c82108184554030f402c0e010b8030320030345036100380c0c05181c0258112450244c544448980d00d440414070700c0c0c0415001d103c07407001950031102c8000010903d01d450401e1a40e100c2e1404c462010a80089501030380100030800000c0460041e5100c1c0c0404903a00707640e8817910000310f41c031501d01380407040c0600c0e1600140c5080c1300303800c8405a0310180c0c01d01112110f40100400400500c014482240e490078918031100802016008031107a21350000c1c00c0e00043c0c0340c048400e50007580609 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 421723983 1250 421722733 421722739
    0x60f090c04080f1006060905031207030306030c0305030a03140108070e04020d0606060206091c0e1c0c180f06030b07180504051e07080103080f0c030904020f0714070b18 74
    0x120108041c681070080001d441c0d840300080c020b04d01c40510660640d0503a0300314804125400ca000c10165500142030004c0c4840f081405680748141d0a04030054003a503000986400000300c400820040008000c0c620000950b5081000c8448580000b901580a105201c1ca913840006d0600101140d0000d05820500c000c04855030581a513a94206544040c0d00850140e08800e0804c03030050010711841c528410205080501d1200c13864015103840311284505004107040740700c46400c10050104510a55084250040890344d81c0fa074441e185c0c290400700300d088070b05200301d040451104e802024142d9610410210095580c4c41080380e5006101c074020440e141207103000101340d05d49101b42c81c09911090305401e03201583e24800042454003811400070014514010004909203c0036110743d540c04207410799403070324071540d00d901d140030782c14225610038800242d02ca90344454000424940d841072000340300e01c0111004907921507190b44540b000c10f180400140030350701b1510507603000c000002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 421725233 1250 421723983 421723987
    0x1104020a050702090405060105011103040e0106111006031232030c12010608011a090d1401151823071b0f1a130305070803072a060501050603060f090c 66
    0x70b80c0000e40c07012005d4500b41c8041d017000b0010b01c0b0650344a00e9000c2004020302c01585024038105c116070180d02c0501c0381808100a096541c0480c21040c020b040451140ca1001c2c03284940780c0c1050210070003400e5242c0d000c200390283e140c203105104541503106aa20042c0c0d05c2007800c51795030780c40c50341d0b2008040c1d4280f240c04001415001003407101d0305010303050b079039146c01083d0305040395030540c192210061000074409100b4909d880d81c0710b0381070101c1c5c1d59004d4a030030361070300c00703440792502412000c1801c0c45903420100c004101c290003c01004e9954003401001e124000c01c00c184501c00074404528180420f040e003000400b207a01846601c14201e00b5107460148240507038035801e0481035100c3c41121661031100d01c50f00c1c18640f03001c041da0040710303800d1301480303038a002d0b0350240482c4685000201070720700110000307640c5401681d401e0406008011198101c6a000030904888214141d044800074601000030a41e8140841502c2c420440900503a501040d04410419601801445800e84401c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 421726483 1250 421725233 421725247
    0xb0114090120030a0315031e030306170606040b060c0a03051c0603060b0102060115021504050f1f0f14060607020f1005120606090307030b0a060503122101031104020a05 74
    0x40c0d0840c100e0200e5409000d5a00d035141c13004010166046c40300c403c013003007070f8002051010a10191250761040349010000040001c285401e6028040c03992028003e41c503e600c451000850100b900340c4600801c0f01c0c2085040f128100f0031a10b809520000c1c42290702070300009001074001d4005106801401c5104143d442d0590040d03400c1c1e400c1c64000b1200c035605e0b100000c40030350701041201d005d00080c9415034590003010383d00960b00d500340900c407071544c0400c801040c24400d05202203a26a611501a903421300d201d089404501d099003d89540d055250040880c04403001d8843c20840c420350039180d001d15190710081141c10b03000448280c0e80002494101d13100d0759150f807200c4c3c200ca601c03511101d44805000c3d2a8240b001c4000301043d01421081005581c1c41d900800e0000a59500c1070310503900303403280e04810b8018551034010f140c1501c40c0a801d5007904245001030040407503842a90420901c1c0c001c5604201d02003031000500324000d11000d9022803030550094103501c80071b45000340c2460304d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 421727733 1250 421726483 421726517
    0x901200115080a1e0f0609240e0d1805030a0c0806010f060c032105040311010b040b03030f071e05011d0a0c0626011e05060c101e0222090b01140901 65
    0x20b400904807a1902090348101019552404235542120724000c10441924800c80700d0341c840d0381d00c0341d210741085824070401c040f42008018502c0a858040e04440c5d40c10402c0c50b01010000060180da20240704800000601c0e4000030600c00540701c2d607a860081c004c401e40e4064503d080b50700040090400000c4a0000c001d04900c030b060b100b1800f03903032810f9450304e55101c40e6003100c4138000001d000d10300303004041020352000001c507035a52525810f45552091141030080d418810240c0f0002d01184003046801031200541014180c0c00510000d40043c60140c83e01c1951400031200c02040d940d1641010060345d4015008030901c1c001003903812006071120480000481c8098121105280d82c01100107240c803408108000030b04415110189007541c8039510301c0d552002e050405800e0b50700c440d0441d400e0550303031440c0040b51003c10030a54076990f80d601301203000c40c4403440e40304549041e001d000074450a90302410030702c0c0d41c043c0c4850440c0303842c4c41c202c030210740e01c104506414003444105011480c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 421728983 1250 421727733 421727741
    0x50c2701031d060414150609090c060408010212010509010303080712060519080606030105070912030215090a0b060108010f030b091c120c050708030601050901200115080a1e0f06 78
    0x85041070140100346028500050400d05c60b8000000d10340c000c070004503c4490081ea1603402076000c803040b180503611100014500340540c0700305601304002140c0000e20074415000b41a1070020090324050f180c0c2c0380d40c28441c0c281e10920002e00050455030100308054014071500201070030014012a60325124000701d00e150441080444c2c00c4135440b01c0400c030400060101030380101e030480c000d100c0c034101004014410403440c080c40082c0351800034402d040500800c000c1001002d40000d4a10600d004246581c0b61290400f041d58018517910026000e5032046000c40d05a41780051070303804007800c42d107801d0910440180313481c14501c04d200221801111401c05140510003540e1080d21601c00b200d8064240c41e141588002409401d00003540090403130025240c1c801c00030b11300141c0714421140101c400e41c0141c00c0140201004890030246000e040d002145070001140548955548e00d1031840c0d45ca80b40d1005c05010502000103000d01900f000c00041900341c05005600180c00094035003104503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 421730233 1250 421728983 421729031
    0xd0b03010615110313031203060906090501080f06070203160203120f252001120603050c151611280512010209030604060f0f05130204050c270103 64
    0x1e10440ba042d0312002d03804035403441d41240d924003450030052030190503c41e0700c09074000249001d11803c007240314144681c0c4110b00410454000b403021965410400004103c01e00880703c6c1c41c020741c1d9080b0300e011400210203004800550040d4170309001440c00303a0811880500c12a4540a4146515003402655020380100c1484104003681c5485c40301e084071a06070f14850400c905450b4025180c0410380b140c5040d807120910340f1164020808c11070041b9002c0700322190940c840c0b45040300200a0110004059884400540d04d0b68854524180c10300010f00400c00340544000c0700e404141c0c00a10780348015a030040000c2c0969818074403402840100b40031504034032540e0903071a0400c0010346005c0755050000000c0c20000c5103840500c60200e40c40b800c0042011300880d44451000708555010343c0400324481c2c0352001000b2908010f415603100e6604240c05a00c16410800418000502c040440e8540c0d095003142c407850750400195410700d0300c04079500c01d06155860141c00c854a004c0350007070400c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 421731483 1250 421730233 421730249
    0xf081b0105041b060903030906082814070c0b0103081e0f0324100e0a0b0703020f0106092a0309020d0308100603050115030509011805060a050c0703050f0d0b030106 72
    0x5040c4110403800f041c0c41e81a0711800030000c0400741000402d80000341182903900c103280058959541100007a0311000c001101e00b0344039001c048850342c8084036400301c1d4502c0c482641c000036940302d40e07500b181e9928002e500980710b40341210042001030034a00061101a00c200c416041c480a0300e601001c10383c0118005251601c1e000003000b0400343c603008020b60402042001c59035804800d408140003040c84162401480190011524265204041c0340014409180003540d221030f6490b0003500c54000400c03d510030341c00c040c2c001c20010b1050044041a03910b41c280c030f01145450520005079003050451043c1410341d0b5034413820240e00d400e070801143c81d0080e2145d00c058107181820403050341d05603001c041018a0040103100501254405004000784d9150209050f110754644030b0041c82c1e100440d1201145460424082000202c1c03c64480d05072440200007995808250020500c01c03c080100041c0040152301c0e10400d0b040041c1480411104000806100c14000b1038211003043d00300d00a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 421732733 1250 421731483 421731503
    0x1802041805071505070f021807050a090b190f0c020613230a0501230406030509160e36030318010605150c03070803100302040b0303070f081b010504 65
    0x400e1040030441407000700703000700c03c0030032072050300000800a008282d40181090709004884056543d800304041c000810350304481c15a04040b24050a240d0051301040d003c1000d180300040e000302241c007500c0c51118074078000d034600c84150f5400c840c5085075104500c203206414403030f0000340e225540a00071030031006050768060390038000c440020281c0116076242d45040303901d0070345007915004407420860b0300c01c1c02c100302100301402540e0a0925407481000700d61300e000c94005842680354100c207005909080a494203c10045003540d5102d11500a056180d0440c4002c21002c60342c41c00001d14000880c0f5900b20b0504081104041c00000c400448000e54030101c144200040e194035010040c41c0b0001c02004080e2400b4045400c0842c030100086e039030180031881c0c03c1d803903106100301c50440790b01420742540d92415420401810103640000c4e4019413400e1010443c070305002040f1401c55070440171850781e443c51076555450039841442900e11083d190700700c1c894070900034003881c0e000c0c5106800c80c031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 421733983 1250 421732733 421732781
    0x21c090305041409071d0a030203060c0304022704120306090c080702070b07020a090f0e0625140d050703020d02041427130503041706040614060a0504180204 69
    0x342d092100c0200d0b204041341c0c0c0904c414107800c00b0b45100703644806058401c01044610000c0c811460a600294047c0901e0040240440c5400001e610440c802c0312054030549100245201d45004a41c4910301710200d40017060204401c8010079041c00383c2031a022402c144c40e400d0100c00d0380d80000d22600491085024080c076240c05104030009480c855002905100c41c41c4c00203100d43c1002c0c481d542c43d5540e904404c4640089030b03008424010204001c90f00c2078101401040b4681003881d071421600d0300c81503c441e02a030700c10101d504030000f010343e16505004e14860a90001d00002e062481810303800c00c4281480241800a0300c0240312940403981011f180070203215080ca05503d4003986403002c0c02a00280c2c0d850040c9850300800010725184c0c01041070715010f46503120740e4008806508940c80ca103202c040d00050403d01c10382c840c40090003000d501d16000201100c2c1520b5043c0e00c20030610051100c0c1c2095840a030820300d900c49044071800054000c02c1c200d444203030001c0b2154012500700 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 421735233 1250 421733983 421733999
    0x151f031a07030b01050403021c080705070e13030f110f0d02010f11041212090503030706020408010c1107060c1505090a050706020a03021207060e0d021006050108100504021c09030504 80
    0x2a0360190341c600701070202d4404500000c100d40720302d005c02403090010600e590040c140099480c484554400582580d0300400d0403c160f0351502da1158004c1200004c000031040c55001c5840881e0582c55280c01d18030000042080c1d030207401007091061180300c1c00c2c904001d4a20308201d0b0031004c0f90b07180c00000c5c00100250b0f60b40280c1d1005181c01411010400003001603403000c3c0f021045080e089800034801e00036a0070204d480c1a407a0307225950512010138040d051042c90350040c021240303044020017003241c1c43c034010b41c2c1e048204403e0070100c1c3c000e200100011801084030421079449412013400d11a0520700040071500255909031075584003101c074404105c0b00300220406031850740020140102503a46c0203503104e01e0b03074401100810002c40e05008001c281d422120000046006440600101044c0256119600c000e140442400c101000855501944e030450150009c0c0a01800803800c0c6014000a58021840495000141e01e20140740c2409440351060152203543c4041d559440d01e126 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 421736483 1250 421735233 421735283
    0x50610090c050f0a0807050c0304032f031c030209031b01020d0203030f0a020d09080d0c0306150c0b070e12160b04260309041107060c020f151f03 64
    0x40c0000d2003003c204074902c2c550200113552140d90145050b111581c4c0c3c520301125580a003c0407500c9610010501000b0045004d0b0380001d055600b0250300c0107880056042c9010840429401c0d416070003400c4100d006003c4501c2000203400e5a0030094604600540070034a81304003c8912604000d5000900800c0d41e0305201c000d83c00c01c0903200950a40c141040c03503194104001c3c104c030b0315180d0b0004881000495941040b80690780140c44240c540250b48042000b4200500e03001d40001c0c645540480d940c80d1500c03820004070713065a5811840101a6521040310701d026100606000ca55114034031103035100074048900c5a2804040c2801010308070300c6070400400c5405c40e00301c084041c0024071122240c0044800048018410701d10b2580d84200d041e4111311504034150380190400b4240790316400c01800030308480784506010045102030480072a200d5088003071080b5190021090701d610324840c106442c1e00010511408400544403201e52404025142d20031603074004804003d4480c00110070b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 421737733 1250 421736483 421736501
    0xb061b0703111002032d040611010b030f150406060e04080d110304021c0204140109150506090f01110708100504020405130206030115050415090302030f030a090306050a0905061009 79
    0x20343c000302580c040304069101c1c01003905c22000490780c00d0f00c0e0200b0f41020010300c104002d030300c6a8265525102c09000701100c0c100c40c21840307550b08090172020755040009160750100c8841c0c4c0030f44006450140341d40d20a5001a00070f45d01e0a4464002007806444111418020380c0310b45082c80e5034107030000070001074404036212222008014010040540c41300c00c1c1d03912100785403480c11100e0520a100040c02405541900385012052400203c1d84803c503a10036161012480100d03504544c2c0d4600300a002c1c4100405681c120343d0002c00c0e190390354000d401441460407450180c0f1310b03894076244210b10f441c000400f01c1c0030301a1104240425414107102d0f90380c10001c0310b1089400000c0d44d8010030820f10042c45059040c2c041980c50b4034800780724109503409840d40a494030464104044000d0400d0700c0d1340001c1e0302c0b83c060941107040e151000022107202c86503a17141d00c2d8105182d610740c54000c1c80001e04c0604c00d151a2040080000c10a00c0120300c2400545d0f1400710300c5041c2a209030480d69465 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 421738983 1250 421737733 421737739
    0x3021005040305061e0109050a1506020c030c04020f090609012a020f18042405040b0105090f390703030608070807061d03010e0303010b030901050601210b061b070311 73
    0x2040703014121711a15450644100703050201c3e0030303144c08450078002d0206003030740769075070b00b604401044d480e0b03000c1441c00d25000c003141101d0850301c0580070002240b29011075000705400030086041a8107044010342711180d014140408130415091480d010401066102e41e030f400720034030350756013140781c140d100001040040d203040c203000102c01c5458504030409080038200c000c46034802d03041c00c43c852258100b41030b140c4200303020b41c1c10300b4170f0b00954016086c041c6501c11140300e00000d0101c4000c404c014070415a94441d1101c001e2400810480c510350020340d0320700042d840a025800341d84000003440e06a00c40d56001031010b140146c4141421103136080100d0716001038004000342c503440942d0040c580803030441180580c115900003401809407591201c00e50101100019145006c00040d45c072a207507490003880aa6100b00c01107800c942800607104040105400f0003420314829448070328466005003489182c625541c0710094611045400c0c030701c82d507004c84402c0c01084070303540d0300c0741c4002000d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 421740233 1250 421738983 421739011
    0x200304090f0b2815030506090604020c0a0b07031b0507020f040e031e09041112090d30050c0903070909020607120302070f030306061803080a0509010203040302100504030506 76
    0xb40004001c80144040d484103d1550542001680070460362031000b07103802415030300802101030024016040c110360b118459210f02c0c000401c5404c0038000c8881034008440689540c803215039564150360b002400d10400c0545c4c0b0304240d684840d0901d03090601080d65240c040e1103218034410002500e644180c02030080303040204082d040d020000948110706410524054406580c0062882501a030a01c1c1c0758001e0408074111484c04512000b81607156454a002c5090303590090141e40e6140c0c102818000103d24071861444184400103c80f00308034510801c4542d00c814819020540b5419503c0040c403c500040d0401c0d50b180c10030002d8020611030a0510400d45142c002035203d00500001a207200c4600d034101c000c0e64403d60480b01c00981c4a010300a14210f0b9040c020003d0070640074000c04a41181c004689000303030364803031000b181c0d4005030035880d0a0780710600b15000c0c0c100c4005241944424400400140e0b01e0301c030b049070403c00755521140c555185041903803a00101819070314001203c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 421741483 1250 421740233 421740251
    0xa091e030e0d03112e090c06050304140703140d0e0303090415030b0a050f0f061e0d14010203040b100f2102061303050606031207020f01200304090f 65
    0xc01c14014284040340c1007502503030182410380d20380818400f181e0990103000c81e0510a80e510082000400820f103280c00428995124908121200c0c100044c003065085d5a00300400c40c80340c0c00450703020b4412418010711095030708420f0314181030b5070000c039008210700400c002007080410840f91490080d21380304042c0e41c0c1c5040420b0b00c9100b0039003242e01454581103010140740345208840002c0d82d101c68802843c0c940050190300400050b10b0b00c1c98120030440203e500d0248201541e800341e88001c103402403906005510050700c07015151456040207100c106000494422071914101126500015a40f4503091601e411103a070700501002c401d0900c040c051001503040f813440c2c1d054500c00b4002c3c40e40d41011240b201e45900c02000001d600080011350360100f0020780015004992083d030483e403007901c03880d08254451140049080d01c1403400d10040016251469032600740f0141814030001d1140280c15107200841e5081c0e001d001a4000030781000707111050b2044181c0c1450302c00c010004100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 421742733 1250 421741483 421741487
    0x1020c0616290c07021903030e28060c060e0a0f12031d0d0908010c1202070c0b2808010501300c02010c18050604060c110303030a091e03 60
    0x9030005001c1c2c50700784001d503240b14080d0445901e00710b86540303004207061490b003280f040a0550000a00301c2c0540455000001e40750380000c003030029254951201562085e000003848092010f03040c40e401000d00703400000300d2450049100001502d4156102d1018691500b00745007a6041c11401120591296244030085412071400c04500c130b41c0301001000e04a54004200c0260555103108600305a44400309420414001074812030040c0c1c580712805d02d2992110352600703c0d81c031801e0711004183d800c0d044660a0289a0043c107003035100e419915455501c6680c03498142d00310151280341041740c01901340c83e425503560a80c014800d03a01d41850b4175818200024240214403400b814140c044480000c902d22440900042543c9028004c110310080305030024040d16110b0248000f04082c460009520031800304840269613028100e685400e2070858121214582c0050a4400300050f110600e03090350140002c50081c803030b0201c04190380110742031130602d880d10000c0d6104500c50440350720001903 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 421743983 1250 421742733 421742767
    0x1050f0303031f030b0c120f06060a05070203160e01180c050f030919030819053907050706030506010f0207050108060d06060816120c050d0212030c0a0201020c06 71
    0xa055086400c241c140700c843c41c03e8484440341c00040c0b02c011440b04001c2c4403030021016117030322070310083c2c03c000e981c8503012641c1801707806880c0c05802c20700400c000c9a04500a1008020135817002d8212007408001c21200012040160031014280c8903210040002c14000300c690400238076188001c0104201c0764001420901c41c143c0d24000d02200070000030110a010720641040101e6044504018001c500d00102000400c950010711104905a074003440060341c45034607c21480406240024070b03120703080b42c1880024074228518201c12803181500004404081c00801e44202c0040c41c80a04128002d8151507004008a042006520407003103455400034410044403428200f10f1100e441d00000b0504000443d90040c1440381130004c005841e08002569881d16109400a070071003a8a5850008113290180b1000d00320760b201d40428041c51800b071640f1000355200805040c078000c0000c05841c21600140480e250342d07002030004d40150358040c41040019035040f130f403e5251161194803140c00c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 421745233 1250 421743983 421743991
    0x17030c030414040605120a020130050a0b1c170f19050c1e0c1f030f3e03011203140c070e071403040b0f100b0a0507060501050f030303 59
    0x4500c24404481a00c0f0703944501d0140c18050019141c0074100d81c141903494100c40703c01c0b40090035250b44007290700035800d03030703051008210340f03000b0740016440c115100030744009820080c810780d90343c0703442110b603540700c81d8035440c101c144543c52951540b038100b07101d40c2600d0003852412a4020002841c1189418003200d00c581c00480b101070b80c0048025088826024088503c250361190041d0a481403182d1005045240480800c841c600b03816407082c400c07803000a11000c055900c100d441c040580c1c0c040c1d00701c1074094143c101c0010700b4090102040310910481400280d1022011008000368503140084091440d54248441d11759450500b80c1d0221109441000e401c000452101e040c107046118102c0c0d1944152500300d80c4c80075214082840c281400307440000105040d4034101a000050509aa10a41d00188521010391b10036580101d0640000e00d45040d46440c0900800c216800707e029152000050399043c1e00c1c0d06031842c260084a4068005501c103420300e1354a8400c0d59000001c8a0b88 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 421746483 1250 421745233 421745249
    0x9021602061e0417070503071a07030c171902160506070c03080d02030105032803030e160e01170705030d030903140c100b0402090a06050a14120117030c0304 69
    0x1984514642c1d5500c0070721600c01050051400050004034801980040300c40b51074424243d40d00d180ea01c0003050794038070440c07082000140000b4003092800200c200500203040c001c1c2000e40a130314841d540c9440d000384030140b511351514045880c00b5004080122668034481c0c034001030010203420608442d00f8405072040511906002459004100031282c0d10001994426041500c2d28615088000650824028035000c0d100301c42c2d0040c0c006215402030302207120035811200e414007040d10210007400b0f1011407020144246110000700c44034050460000340400c02590f6150350405584025211a814402045034403907603042c44203a03000b150076000c41c03036241000a050b400c075142c140c902040d041d01e4007a2029010410b80050340c00450040c6014030903000c04c002460251017003200b24041c003680c0c0b9402003101d40040c0609401100200703020075180c100040382104000741203109500c00c0f15025803101c201801048511461041a01408410409142019031210b02d00d17a490007681307c0c1400c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 421747733 1250 421746483 421746487
    0xf0324100905190f1e0204030204051b09130209090702010609061403151003120f0201110f0304110f06070c080609070612021c050903091810030303020903010f05070804030206010902160206 83
    0x80d48204942c0310502c0c004c004105c020900100c1d00f41c802c02034005105c2640200d00300702c005003103011043c01da00b4103c0ca04c80308490030050301800344602e5160304c403d0b00d4042682001811142e030342d0042090b100d00c1c07292340042900390400016405491099000b500a0340070721405032200c0d40c010404544100e0200c000c2c0b09980d0700c048200307610781c42c00c0d0310107400106401a40117801c1d42c4142c42040c07140c1c043d0024070840c01030400070501480b582001546a00702840842c00041280000c480c0714140140102e0751321030520009030165012075002c03204500007020400c80c03070f01c043c010700e42d1015142010f1b1905510300032001d851001c000524020960b800100d4848c0300c908910155080c0800400800070b80c0ba101c910756640e0307800106200c0c800c2242401c1c46521428031100d95100300124045401a640b0f1650164042d4210203c041c0e499503d0f2120f51111280c40d00c101c078440c82107542c600ca82410036003806030601b0010f801000807540108a4200080c403030b182444c0d00d01740d05803810780d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 421748983 1250 421747733 421747751
    0x2270f060903071505130f2103090905091516020a0f08070c0b0a020f0d020c13091205040e0a0204080606092d012c04020f032410090519 60
    0x19003071150301c0e004003000c404c101000d8a0140c0d403280107001c42507a425089010907884010300180e03030015108101034100541506401030009811503c0501c0c4203007080300d40d05460740b01c2c04041d28412141c0251551054811071640040a45c1030b50f0071101c00e100c0013400c0400c100c00251228054203001d0022030300020b402082000300d004490302d180d00050072020561311040300f001d0951040000c40c00511031072038105040400030441a541c000079030020300c0f41c0c00c17a000601c800014400e9056441c13070340e50580e9502060141c03000e05125202650f9503552a420424000400e0f507001d0020b40c00380d44144400d0010310350019803a83c1140e4202c40032011540c0740048a0511643c00465101015101010050310740e90956806c1c140c501282000d0740824501021078603815011034540c901c0e2000e440420003504080080c0516400c000d01030303500415100002548030190b581036560109100030400020002d0540c110010300080e24091046040603000e81e0303a0380e12080f40300004a41d45072001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 421750233 1250 421748983 421748989
    0xf030b1c0803060102100f06090e03120a0506010201060902040f0e070813031d0d0b040b06030a0b150a0506070308040b0114010534050307020a0e0906180304030605010902270f0609 79
    0x4041d008084242881447e2031000020041c01c134078444c07a0b0429080c00d426400c100303000f2090315600c2d01820150340c00c40c4e64840d280000340101500da10305555a450010070100d4440c002003001c1c007004840c640d4402d181822000c0c003000005c1c220820803950405001420b15040e466850050b05842c0c0704041c0840b803100080c00d082c4103154150300032000d2091200b00400441614422030044079030302610381c1c42406040e07d5400d070741001002009103100040d0300040381005c2c14241e0170081c102e0584962a00c01180ca503621003403041d03000c03800d0f400410082002d40c02841e8054402c44181c0c8940f0000345001074007a020745401d0040f45103400c0004802c444070101c030f90400348104c3c07508001c5141c41d07040040c0c0b030f80d110043c10f03400b8012800740031034640c0034905180d000e0b030b40000081540d03599404055001200118503d0224003081000201040381806030901800b4040001a0b440303443c4c0700f81d0345401040740050a543c40102403100101d540c0c1c1c6041c1c1210320703002d44086613a01d81407000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 421751483 1250 421750233 421750243
    0x1a01110715120e0a050606091302150702040903020714031c080a14010605120f1e1e01090b040b1e010c05010f11070302060a0b0a0603091b03030f030b1c0803060102 72
    0x1407000151814081c061084030006011340c54601a43c1a03440c6611524140140c4c0070044500c1020070350f9034010000107051124000110321100c050450030680c4503070001c1e0990b038501a050300140d00c08030081c84513440504402d24418070484c010b003045200c642c8024605098068082c1c00c0c4000200082c2c905e083c3d9810640003103071407641782a400d68507288003610782e0300702000000b402c1c281c100004406904181205006405141c101c80e00c48142044071001741000030038035903003420304a4440303410101683d54540a0030b894280440d12004c04002e01c0100e6032030790422845039000ea01031803c050182c000b015800102881d003907400080364101a40903110b0710b4800c0d284ad40c07074854944508a0b45402400d200d83c0300350309696803901d0f030f600c0d6070701580d10000c07141d548000403403010030001e40070740e100003000c0e4454001c500495140389143e18580302540c0c0b0540205580c08450482164188070f180c80da0f510842d130324500d00e07600c1584203211841154008180c090300101055041e802005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 421752733 1250 421751483 421751507
    0x1030803070c060c180f030f02040504020d0501050103060b090a0c0e090702010e06150f03150a020a03090b09060402270a020703030e0d0e031506030a03030911060d1a01110715 77
    0x100a004490804800a0805e00312a1140c41c000180ca030002c91351100d0719294504894024844054280c056000c010040801400c2281c1c411507803028800014030a003c0d090085015080026201d0404014018440001400c40703c1d1145460101c40c03459030400d415518118050f03e600d451a9a10035099004060b40c3d0207143c00351240c0020480e8402e69154500d05143e41502d01c003150078840e4081c5660307000c0e91107074851146005800160405060750141450301c80328a80410b511185840707445401105648034203054000f80e08000c15814249412640400603a010551800c0450311100312140b02030801400945c00180b05801d161007a04064110a2110140d852014901a015103d188050b60385ca00074003441505400c3c1c0c2500d005072910440001d000740c034008541c0d5404500500c0c110000b00c96181011040750441e840307000290003150000c0000007078030802c502d441ea40880c1c0d0b02610300d04004035a201070590140c04500714040340d4600644060045074003a0644600a07100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 421753983 1250 421752733 421752743
    0x1b11060c0a061a0105070309091a150307110610030311120a0504061115070e120d0c020414040c050121290f01051801030f05090102190c0b01030803070c 67
    0x11010700148655503100c2c9111803d03600c45407108001d85801900d4500030424060003080d034000081188024542110700c03002c0e0101e41d80d2829004640004214003142180c030700e80d501010040252094008162089d00c024002c024841362914403410448401c0901008042004001045c82510010080a07188490390102661500001c0b031009020350000d2042d100051145141a030304213401041041d07070403d00000100540d0344801d401e0307802052400d000e43c0c001280d4170500070030b00c13003e12001081002c10303521744040c0c0d0760500401060b0344003070001c4c0341c207055240d0602c40043c002503c0d10080b50001c1c200b124158600c8500d0303a01d0001c2d81d1450310440342c140346071000800c2054107801c1c448040c2202000711141c10f10b09002e0130f0040300c40304901107001004204c0f0280c0c0e010841100070300c8145804510280326401c1002030310803d4036400202c1c2c0d00801c9400d0340c10110110ba0901034220302c1d00741166103403034881141004062201410180000000c41d134070900c5294010141030b002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 421755233 1250 421753983 421753993
    0xb03030c060a0b012d03020705030717180a121407030f0506070f0e0a06051303020d0602120f09030d0507090b03071106070201020c0c12032101060e011b11060c 70
    0x4400d120014100142c05140045c1c546206010030000907134018400710b00200e0306403448001294290001e5000400070b54081c441444824005681c180105404031920203090380c40c2c00e481c500c1c0750341d8003610400c05403152034400424050400d498007029541604800c409011405170303139200e414954a03420140100f00344000e1070f0244000001c0036400342100740d4800c510581860021100524545119540180108400c00916210320701400d04011100c0840d01025501c1d400608020403006007129116004110a200844007200039944054007030f9058080d481c1c035004094891140240b0300c641c031681e42001c85c1c6503030b100b28031220282088580302c2c0c0c0e4900b0280c40c081e15042051000c1c602038400e40b800222842d1042c001c0d940103103502c03402000345c4252682040701210321812800c01511007480070003103503041000040c01040d2040c8001d0311650400b0001007840450ac521141840300c1c0c2c00040d1a480a141000803909030804d807041d044413a0700b4001880da10441001c0111440341d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 421756483 1250 421755233 421755241
    0x30402040510182703020a1502190c060b040b06030f0a0b060403050c0909190308091203011502060703060612020307141309060806100b0313020303040b03060f0d02060d0b03030c06 79
    0x21540c0308425072004c403500b400403514920010340c0e0003041c3c00c60050040c0c1103510180c0004040c0e801d41903680e06400c1c0c000d810b048403407500d00c540b8040c1d4001c00b40021a000882c1d001d02415204440560400b600c0a00c00c10380b41002042d451b10001d000c502032201074500081c0200400d9000d0350384a100240074942d1242d403420001d41c0d900b002a1a68880c102040105580e0000001c82c1024010100d031641c2c603581d07868505982c880c10051451003503003d40340c41c0001b4229942e0046000e4010314501780707404084040024a0b245000703003414180b502d000c506204160700700c03405c1421500c002c803000d6a00e584116049505404050100f06000c401144d440315070070f40200b00c030007076940c03040d0100031596903500055590b40040d50f501e200008030000c28802250204021580815040945c44007148640e0120f8910b505c664000b0a0042011040c8240c6180c488c080d0b4035180781c00c8a50070300318056600041d00720320480d80c0e0070703010350b580721040056500c05109840c09400728409603845450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 421757733 1250 421756483 421756529
    0x506010b180402161406090d0c08090a03050f1e1902040b09070306092007030f0216030c0905060d0c0e15120a03140703080718030b041a070201060506030402040510 72
    0x240b407941290a8100340d460142c60b00b40c0062803510840c6030300700810145c1022344003502c2d0300710100303016036150a08200c4d81d2170302d0300c0e0720307004000942c8900010619070040141d0356090020b2081d4141e8090103c5840c4c80890500084402d0301c50010415010480e056100190050018000058002d00c11204001a05801d42d02c10780440b40c0400003031003a05001c1000c60225a4070911410200c0000c1c450500802d03c5010308101b06040b0740100c40c0304988010513656000c0c0ea641c021074144420321418468142c8902030b40c1d0b00720708299024100020103170749150280300303079000380c00c04001c62200161680e901c691807900c091320044c001e001840401000941c072040140c0d42035020503a202030186143c900703802101c3d10b00c1d8040d0746044003501c1c1c0c1401182c5010210f880d1107801c541250f80400803621400515000c0c5214560100c80c0800603000403003032000003480b180c10f40e45010740401254450204680c0c3c80344d81201c00040b103907120100350300c030841a50080000d4805242d51003032900 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 421758983 1250 421757733 421757767
    0x21615140d0e070920030a0b0307030b090318010905030613150f140c09010801140105070b1303020f0c030703111917100203011d130236040506010b180402 68
    0x36216030400d0104001c1e00d1038406500030120f1a500c181a01040000d48180d03c88e030200505603401400e03141e901360350703850f982c1e541c45055840d4402d50b0000504100360340741e90160761600003020f09010302200d03c0d100c0040e88500e00205a001440c3d4030040d944100010b52110000e10b40200004014a401004020340104000004283c401c0c103002c011481040d800410b54804450596507106139a00340080d000760309151004039411302400380f106000040a03000c3d4940b095034900c0d0040003407625401d000303180060306201c0e000142c01000c0b9040c05620042083c3d000d41e40c024034104406d5859101041b00c01d20010301c008a021203a100110341803841401e840d808014403011241800042048402203120a1080c0701512846440c8002e074828040100c40d4000e404080002c1d9000594001c503901003801501d800b06501480e044c0308580c5090381034414031481c0c0d071045110710f01d81562641d980c0c580600504641c2000481c0b03031039110032800b150301c0601d0f0001d0030954880c54007540c001107003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 421760233 1250 421758983 421758989
    0xe060d0b060f041d030a0818070501181805040b070e0f0613032901060806060703030e011401150f08090d08040212030c010f060b07020d122a03021615140d0e07 70
    0x50040000322345406c0c000480e0b4070305804840042c002d002e02c1d000042da84d80c45a40215441c41c1001800002e1a800300004140d003e1090ba00200740c6280500d81030740c058038010880e00602c15982c050005039294003641c42c43e4280d09a54155540980c140100340008a6910080018200000710b90000c040c84e00b004085011a440030b4919903210341050311030306000c075415500000d05010f0640840d10030340000407604000000003403401224002c4e400c0c0304409801c890401490075554000f4540d101c0746602c0300601070b10700b4420034104030114903110103c1e51800001c0000c0c0e040810250b40e034282e840346d90440312204a0741d0b07400651010601070a000e944840034686032201c002001e240d0403003100d843c2c6900034640d45443c410396448480140d0090391100401610b52054040040a81c0030f480c0d03ea180c503c0a92076444951500901c2c2142c4001411404414100200410b5070200418462400f0b281002500c6480003807208145005201421003c1418911107410b1550089800016 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 421761483 1250 421760233 421760237
    0x5010e01050601080c0a080c0c0d0e030d050f09130e0f010501050a0b09010f03051503120304020310060f0308030c0d06061d010203041a1b06010b040e060d0b060f041d030a 75
    0x6507842c540151610481150b03611222002004010241c0d84034110310741c1e0180580c100d0905158007100201d19146080c0300001c049000280b0020760b915040080b01c1a6590500e4850300c1c120a0400d904094051444c4007802600c883c40d00c1000c0c0ca60982000d09940e001c1011600461440e4804901908007845140e001c0c61301e88401141007c0a0b000310740c012201a110030080580a0000b2070080a004140c0460f40c2c0c2440050455030b50709001d402203081007540010307168140307801018140f800000180406500d0041d080240007104000c0004036a00312202c641c60750707203e48014405104440c0e44201941c5131050100341c00340c120461641200c2d03504a501000c0707880303a005a070382c0e03c00d501481d82400481000241e90414060051425003004003010042c03429514800349013510a811a140100340441c081c4160000a07515945c0a482215000301055898440d001c001e04090100c83c090201ea01142c1c1c0c43c3d8a898100801401c60680c00030603a03202d010003a500c035000754400c400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 421762589 1106 421761483 421761491
    0x30209061204171303052814011404150c170a0e031b010e0d0323060619050d0b03010506090f060d0c080106030303060b0a020d12061205010e01 63
    0x40c05401c55213120005411481c02604018215805181c7e4051312403404441c0000309a40c90422030f00007401c1203113407040300358071409021108440d1800308420810b05c0100b100c1c032424100420301c020420041010000c104413010724045c00c15403a02070041001c100c8088080d40151416819001140d1030100e00c2204154119070f0092075031003a9540c1c000c0f1411688043c017864806c480da07031600b00305081d6450a0362440000303044c10710f80b002410200280568884108071005c0d03800e032841c41444907042c501d00410075440419110310003400d041d8121400c0c01c0c1401a98080c1b40010001806030342e6140032280c0c40200100503561140c1010180c501140704c0c3c24229002d0800b00d400031445900b1400c0240a0b00e101d64024400348100704201620326a005c1001010740e501ca1030619007405000411402410143e005295040b040300b8005040200541c4400d00c5e1072041070081c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 421582733 421762589 := by
  have h0 := BRFrame.cov_init 421582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 421582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 421582733 ≤ n) (h2 : n < 421762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
