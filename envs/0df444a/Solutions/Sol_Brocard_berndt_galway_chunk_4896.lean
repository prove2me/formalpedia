-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4896
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:05:06.314175+00:00
-- url     : https://prove2.me/submissions/b6cd02a2-7071-4ac7-803c-6b59f281ee93

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 880395683 ≤ n < 880575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 880396933 1250 880395683 880395697
    0x1050f0402070f1e05060a021819030204150e072d0c0203072705070f08040f0b0a020301060e040203101e12030c020405060f01140f2b1419050705 64
    0x8444d4138600c400c20151111080b00da1000d4599019046c0012801000d0380200c070083e0300c580030308186d031030b000c4401c100c01da8002d004103551140d440c1d040400141c13540d00c600c040d103410704c291300103a203403828a0650700078100070712000c01c03c069481c5401940100840c41244101103140d40c1521300c00d158401c450b184c080d4140a541845240000206a030030325020341002d8403010240c02d041c0910040307941c05d6440541340140002c0c03409600d1840039200d020210381061181d0b18180c100c0b451a114a04e00d030200380c1d038410040794000b00420860b1742044078001e10b074105079070650541c03070044c071002e4201d603040c400d42041c40800441615a920464400c0c03018003004400310071015405d09004100c0501031200302e010310700d460086112850a08140d0351041016034500c501c1d202c520240e000f0039080301c44d00a5504405001070170640c1e01c441ca804400b0401138411179020820742c82080b0641d007a1015488030407002e1414440901c074103200310ba00d114040b44020a40b5111008101d44600c034000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 880398183 1250 880396933 880396943
    0xf090804030c091d0a020f041803030b131109040203070e030f0622051c090f0303050c0d08010e0711120403062405011b1a190c0801050f0402070f 64
    0x9804400c004800502d00c065a04200b01044000c04c04d00c3c400081078070310706260840340e001894183c0185011305440d06003c901910100b40009055102402c0c81c10201084000c02d4030383c1e40351842400c000910250440b020403050000741d0780105000050310903101c4143c01b135500003002850702c078020319641c40c0e0320501034102c40c4110b074840009602c0b031005403034000c8601082200d1070081e444000d40320035807036000005080820303414104c415081c4001d8450600f80014a000010710343c01b11125000103502a445203503070f40444035052403e013182c1240400520102d01d00502102260341e401660188043c2403e0001c404001011440e18144001051004c0030000e800b04c108403203604038074421a444400c10b168940e10480300c9406000720701499002940f01002000c43c0c880810340800c02d24040c00500b5441092407404082020044a04442d01c02c0803002007001c00203035100303c200c0403106240c14802d03941814002075821100c1980d15100d40e40124018040c042c034500421001c0d90f2007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 880399433 1250 880398183 880398187
    0x20a05031e1b130b010909020a03020c0624010c0602040806010b180901050306190e072c06091b0c0d120f1808031905090601030b1e0a0f0908 62
    0x22242405559003200101202800340c203092010302c800510640324200300080c0b61508424000c84188014039088030b13074504200c800000001c031400c1510081041d41055540540c0d58a00078110307030b18090024100c501d000c0318040044109603100d103a0000d00b05403d00e461900c4074800e00b40140031780030310340160403c0d00444000041d03620f40f441c001d04081050440c03055284030300700100880e00500b480744540607042400010700c0350600590354801800d10480001d1101c2d0000421450140c480e00f000584011600c248541c544c0e56074a2084140506443c1e1030715850020b000c80c5450b2400707080110301550070b021142c0000e001cbd00a80c0d40c040200800c541c904100c1c02d400608a1041c0a0300341c6a942ca802905900b1800d00c0c0601081c000c2c40d08a445110221a0340e003610652005240b402d04a07503402040080305060b00400307000300311040003403009505500742541a03000c0a0060028800290f8064000c4203100e80700542c0900e84100000b40d0b892030201d001c0103880f00a0000b4804800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 880400683 1250 880399433 880399453
    0x7031e0f0f08070f03051905010e18030f0706090c080109050705040608010209091b0c03040603020d0b0103020304030c0b06040b030f10061e1e0e0903071205091309020a0503 76
    0x4061040d00030803410303503200c003580d02aa0609941c001015180d0f40f00040080e034031458a00c2c00390f08015004010985481c0611110040310400c0355003e070002d030038402e4540107100004214100500303d51030f00c00040c5180c8080e10451951921a1a10003030031b0a403907000c04000e00801c900003800030301410000b0b0180d240c7c54544161950b09a016107407244e860858040742c61201403080c3c40c1981c10180c9840075903112a401501d180450142035200180e040042508403002032010380000c1900342c80142c6c40b0140c04210b0030030303500d4022450b410144148200000b1a070b01100704800a6040280340c00642c403a040403401406400c80055054410144120280440006c1101407850055010030241d07489050966030a0008001c0502c00ca00094045c0724103084004013035600801c0111130300e0f80580c1d0b80310381c3e040c4010031a06007540d0707080454901c040c01030040c50440b07104090f1500e546030415a600240420420416040956946241c07100464540e814200d0141c600201110100c0c11 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 880401933 1250 880400683 880400687
    0xf0f05070b1905100821070819030c1407110d060e0f0c030706020c010f030219030b03010c0e1302070302010b04141006050306030604032d0e0f0d050c0607031e 70
    0x105920074040c0b54904400902d40c0c8544481d01c006980060003d00b8400d48110484990205e0405552024000401070b080004030b4070720040220b52040140c0110040040f0400b130304998280c000300c800d10103402c0d803074200303c4401412200c1c0c056001480c4030b0841007a00108415040a1788018042443d004a54180d0400007a0780c2c00000491002c80358002c0280301415155580c030f00c01c80001d603210b040c010000d903000700c90180c0b844101c1e01e001801c03c61100c1160500c4c18a0000c0c4401180e42c9100d4005907090a00901003c900b0a0800c150100300141c0030030010702c088e035044c0c1c100550105a140415100b9004150200d1006200b44604d4001c0e200c440034801003913a8080c109126034500148032070251090303078800c080007005804c0076542e03920240d848070303814810303c0d015041d0201802d903214440c18204464911507615501012001c40600c580d00c861840e02502c039820000346440001c400003103201e00c5480680780c0b980c6500d12841e040e1600d20380100070020940d50180281d007016 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 880403183 1250 880401933 880401961
    0xe030607021e160e0414060103030c0210031418010902040230090309010503370e070f050d0206070c0e07080f06011b03050409060605090a150f0f05070b 67
    0x103034203020040340d4203084114159079281c04008040c0f8410000070400510b0ba01c49002948580118190b0711a0303500c101c0b4460078414260812000318604c51058015414079101100200620341010004480840144801048002c0011901c52581d41184020f4402908a8554564060019500d803200703103280e0380c040d80d40880c40c941e0101044180c5c011495001d14240c0c0601c107130740003440c9028a100011203059100030504907251800d00841c105c00c0c0c80b41041711003082c040320400c20016001c910c0302416a0010500400e1a41c4101000e00c00281c0d0a000b0200b1600c02300c4198130010043d2011401c0da008442024008000c0784100092030f18814004500c2100c01c2c0d074494101d41c0e41c1044844103140144c42c0140040c1c4406034034069040300580c5108194068100b250405544142407010f40312141c00240002c0c0f00410700401a0501c40c00c07440c040d014176040e44040386441c5000800305c0b03891410580410080c406410051b0340500304581d155504034420403014907001200b0541e0f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 880404433 1250 880403183 880403203
    0xf0b070207092f0403390603050a14060109120510110705060601020109170703090b0309030a17010806070f050c1603052104061409030d21060e0f070e03060702 70
    0x811405016999026444000c8600317403a4040c00c1d006c0000c4910104141c04043c0c20141541030f00d28040c00003500f280b0b007404400502003550049001d00e40043c01ea404c0d40c0e40342c17591120700302d0b103030080c842d0aa07000104c0f40e058402c0d245c031403004050343d810020302e8111045410f0501524090700c0c440054002401498034038003640442c1c04649482004900300c074a02e000250030840403c4071505030328002c2c4020140d80c1d000b8a041c1c501d1645640d06480c0c1540103603406445a880000c110040580008510040881c039080d0401c1c6036241000703041e04c684000700080d04202510b002801014000c409884841d403400c030880d0301e010181c6184802145180c04290340c9845594004503000c4005034922a032095400205810b0a01c0c0100680750036120814076030061006010100017510104245c00e900c0d151540c03100142d0030800d904c160032440c0708840c21400d5080401c10702440c68141e10791504009040051805650f44842c105c4039076002c44001c507418004e0340c0502850300d030300066410301 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 880405683 1250 880404433 880404491
    0x61c020910020c100203040602120702030a06050a0e01110414010c230a14010e0a0201032007080a09170c0907050c0102030f09060606070f02040b0402040803070c09050709030f0b07020709 82
    0x41e12130043d009982e00c0c081c500c12440160302c00d18149959101c558040c00710140b024003240d41c000041e0b95440246e64003180c0c0009402d55a58050360000d1090044282d0320100d801c40c1440c2c1400c081102c1c05a607008040783c1d0610407107100200803c81c0610018854400c1460b124010030390306c000590701c1e20400c0d1020746030a000c1d030885804c1c1000611171a00c0000300400201100241a0f0056024211301e1014004518245260360051044074000781202481007034240d0350345800f01009001d075030b8250411030380400e40502c002c030703803200003d05400c1101c0125000c038825078071602c2c00c60769441031903804815540040b007880200580d0704000c070f00480c00c6605688c2c0325640c0000303003c40782c06003120140400514070030410250609600400425002403c054a45612801c046203180d110740c50488800700e9500e0100310100441c4140790300311000c4d141c2440720b135145d92620b0607043e0b1041b0000e032007910a00d0104860a008003d004000c0088000510040c06003140b040e010311324801146c44 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 880406933 1250 880405683 880405699
    0x120a08090406091406130b03010c0c150506010512040c230307060521090106030503040e0103050114061815330301080d0c110301020d1a030c061c020910020c 69
    0xd9a000b040c090103079480d82e001211681d0f81c4d42c080c1000f02c84019a003542d40002d07507d000c616402c1d10280a5242c04203096105c405181441d841c1415200d1600d032900100e0528040502c0740c140e0340501103074040000d5010080091320b071400c1000c0401144d80c01440004108003c500480c800d2042071258401d0403803c1d42c420642d180c00982c2d9034840c014070b5824000c00c1814041040020020309504203501200014030180c59a03201791455010b50481d4070300400e48401001009024040c05150644900034550903062000103c3e618606210020604100100004407030003060000c2e0211a90010803110005400202c003803106040b1100583c80c4100486403010800c048200b120304851604000740b41810f083c42c41115003401848044461003206103c8068a035800d0029041a210103040003642d04c1045c2c9132503140e926085000d902a030030002d441d1a0396036400007610f003414450703130713500300c850084d201084024030070181900d901141d00300354540000d1b13002411074402c0c007068ad8070342 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 880408183 1250 880406933 880406939
    0x80405040218180601140703110a0318060c031227060c091d07030e0a14060604060501030b180c070c090b09130c1802071a160e01020304090b120a08090406 68
    0x5032110032102130303000c140c1440e00c815131b29011034000c0060034041e280281e00040303156040c0e410302c08c03c0c200c15130000d488100c442c00c0c405440c6a41400824040c1481140c41e000b03960003030420004038248a1003e0760300c41002c02a030313005200054031000c1d20590070346103000c50b1401c1c90003005c00f4141e82000418441d00450780a00380040145103005803040c0081e90f80e0380c6c506c12405040b8910b0a030020b80503040321180001c1c20f0f0080d010751210f0540c0030740140d107400c006000840390076900c07580c1010305210642055440f98000c042d0042c00c2c40d0f10300c800941e5030b448512028411008001c145080190307000481c81001d43c880684500d007114900003e40307410100c1e40d80841c00e0b040280c00300c5840b05040025a000e4404880c0c0a0344600c03015040c441c080e12030b82c5e12074841e10102c6205024001c01c11141144031140c50340b035102281820301103481c0d0040002d5032070080c1c0c088d1300740007650362140c04515550203c01190701c1120303a00319003404030765140141403900445c55007030007a406d1130404 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 880409433 1250 880408183 880408219
    0x50114100b0421050d03050a1416030b01020c1503060301150f0e060414010e100803040f09050921132106020d0e120408100c0801030807080405040218 66
    0x303012a07059404540c241410071001c989a5110303d10242c10684400c3c091a0028406200300b02c1460016140082c55140c09107004040d61241c140e641d80307c102c500c003080010101c003060007010361540d14002414008050041c0c0c41c18103c00096540808444003003105122124021482820150002d00c40d40708140341c211110b0445004615403500c2204042c400c070382d8552260307588030400510100e44001c101042e0b03c1000001e800520400c4031103010000114440204030707004040500040d40780920705920081c0040f05401010b680503200c2020031140c100810854015290402d840340c0c0b08100c46c0c0c54584968440c04a0710320150340004001070180c0254414403100000005070401054103546110003503002000813801c183e070750b2110104c1140100a90b140c6001d103e166a0b96540c20308031114030384a49050b52200d0642003545840820350b0020748181141e074042511a100d203120714240010780900e400154100d8800325001c1a156004186202560400d0f603124400780103903909 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 880410683 1250 880409433 880409461
    0x3010f061701061e09120602031e090615060708040f061808100c051c0605031005041a0714030a020318010e0c121504050a050f07030b0105040203070516050114 70
    0x1556010644800c4002220a042c40c0d40000c020500c5c500085055141d400d80c01d40a140b691059800d107902104100091103100b1003800c24080d20000c41850340f500c0c0070700d59914100103000c1e50b80b00d040000455020344540040c0d41c01c165004021a44581e1508007403541e0000500c50700c4d001030001c40c20000d03042280314150b020b135070200b000f904403400c551641101074030840d0091002c1041c00c001c20403203c68803880c8101d184046035400f18076030f407600041518100e494400508028900414000002c1ea5004401903004020303003003020f15560100f003500d401c2da99021045003100e00000300011299103030b00441c0700790f42c070f4403a60031907a1004803c1422a460000400c28941c420303030f02155245448010741d10005c25040c104c85411941c442c0700c08102d682a102100c2c00da111920348020000e060210711041c0308040c008104141c510f4441c1c046128041c86518040c41e40040410283d81c4200c0c12940c1c0c4c40340c04001c0060050300380c034110b07000784000c912186108004a000c0344880c00f450036 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 880411933 1250 880410683 880410689
    0x1003060209120a0501050f2d071b240e15090a1401050619061d040219121a060f1c050411030f0c030c120c0405010f140a051f02011103010f061701 64
    0x42d09008000004661a00c04940a0b04120612000001019142c052488ac03840c200340700d0041d0b080f0040700804c50a4241448031400c1404c4d41c20402e1003403a041d000198607950700c80c80c030840c0c4d500e81c4405002c41d0404d82410310151a401880800718181441504074a005800c25074000c00401c1c1c8641720642ea100322805248001110f011075101042c484600382c10070303c040104010f02e400c81e544100801c0c201c00c6990301001c01e16810410200910300d1145208801c501d0006a00c884002c400041440c03042030b1882d5072083c404501200e40000801d068541c3c1c05507044100220305090410002541c800b14605220b4410700354070065406003c01d01d101c400b40050700a110340000340c020000c84500b800c0310303400544100d400b03e0805940345d0051600070700da0b6940b640513642c2848811103440913401c0800e0f005240c498020062900e0b1210107408042610310000741030303958076200701c1c05803032701c1c0d01c50070a41c0d5404400414205000005041101c00d5034131a18808080078500d0186800244 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 880413183 1250 880411933 880411981
    0xc06030f010303110f0d110705061204020108041728030e0c0616150222080709020702041532090403050f0f0a020c181003060209120a0501050f 63
    0x40c01000000e01640c4140398001503030041e6041c59180c00031070b900d005141141c040008200001400c01440d0500640c000f5080a50700300d40b800440303034403103400711070f0140c0700a0400a60700000f50600400803d003118880788001034035036840c02c0d10442c4183c017420440700c0c50f041c1c0468100c0d1030b0032030282c4900f072943d140d22405081085108010403005070041c41000700d16000301c2c0e108000203825550b050000030400305005072146640c603100d984c02240d00c00007a4a50100351010301c40030000040000486003880000b41e40d480c003910225020f4502650000d42c84418200041294150075107100c01400d102c24803802202c2d10480c0c034002a420684000340c000e115803000c10003003480b580040080b2201102402e180c0170100c061640182e20007e40000141c02c03810b644155407401a54081c00032070354041000e0a418040610349500b0380270703c80208819800201c165031612068042e040d805910400d072481e1001a00700360340a441c040740c85400b650181400210512804401050700784000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 880414433 1250 880413183 880413211
    0x806180a0209010c0b01090608070f031e060222170316080f070b090a05010f0605060d0b15072102010c05070305070501090c0b0c0c0915131416020c0603 67
    0x1094088002d62001c0360aa0411824100d140c0108082222650080001da040080c3c070030f00e0040740606064081d0440c06d0150306035070041010898100c01240c2000c0900c0003508032148902d4514024803904184800b0b0100c904131503840142411040e008889103121549202ea40c0c081c1c0e001d85a1143d1802c1c0704200a0b00082d42d004600c083c030282c8161400e803030400380340c000103403122814100c1c12140010164440d0515004102c000e000369603c40401700b50034400d003820080050014060f075106003d03003680e1010341c0d04407542c4981400d0992075180a965558001c241083c101811982a000ca43d10441560b00c0201910500c038a8090310110381d1a0340c20421070741c0c0c049405034000d080c1078940303640720341605c00031a01c00e51a0a00a244005203250360f0111404c0150500f10380e2010584141c00700c070204544806c6400204862150488440240c00e9090b0700b00c0c40201010741ca680c034030072280b404000341c1048000461201110503005c81c5ca04658810800c0494031044484100c00d100c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 880415683 1250 880414433 880414441
    0x3070306020906070f0807060b0d1e06061a0a170402090601080406090602030f22030203030c070c090f020a1b150906020c1b010e090c031803210403080618 68
    0x8603074060441044014a21031900c041d6031a1544c44090703d9009a603050800615001044000d00c54054004001d850f000b0b0703010070301e4841325003100100008802210340031815104020881d401076015052000c25520541000203d40c41541c001c12075680105001900c2c903911280c075005518852940202000b250b507680300011992020054401c03150707142c0714074a00c4d000904600245200e509500b03c010701d1440c181400c041000e103081c640031b45e059982d0740e40d9030100340e0120880b036000302c030300301c9181d41c402c114500310040900b65400b4010980c034140610021400c5a00242852102c60b6128070b200c1140c166a154001c1301580002c200d03007101d001260f0aa40c0343d810944049028203001424200c0100059051203007071981c1c0e0519203450040501d0b11340e0000f615410036402514442c4140ca010341e0f514034113102c041d01c1185440d41949000f040200108101c80c01d9066900d55011007551005500d12070321000d9400314041144400010350600b4043c0791078100c030070484141c51403600c0d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 880416933 1250 880415683 880415693
    0xd110f06180f03190812060906010c06020a0c05120a02010e030a080406090303060519260a060e07080717100903050a030f0f230714220e090105180c030703 68
    0x2c00a040190140580350442e0181c0558a00b02c010302401002e040740e40701c00c10301c0c5018420b00020450340c0300300213110500c1156640300b2542c0c0344070356008000507601e1340848010398061040c0d0030024520320403401080f104440c0f60000c0c141021443c0c0080c00700d0341140402c02d0700d9001e4111910002020040018045910340d0809050a8001d090024100b92108049200380107008110700034404154002c01000c0251000c016010200d1103101080d0079008550b503850b45007215000e410a07454001502c05280e003844a100248407103030454040c0c69031004a13120109a4100e4030b2014003070224101c40d0140bc2d40190b162140e031640d102031071b2401c00c203000e40040000c0b82100c400503641d0803030014031069500ca024404334032010956240344848283c410203040080c5008c04000c2c0164030001203521a1017130360490001e20500e9442544441c6107040c41d550298002a4071115403000c1c44803200c411f502107805805402ca8075074000404c0e20b00c581c0d686000000e40380c0c155112007030420201d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 880418183 1250 880416933 880416949
    0xf030804030507061802010e09090307020d08090a0602100501090501031101030e0705120a0506100f0b18040f06032003030a030c051306090501090e1003060203060f0d110f0618 77
    0xd00c40c0c10420b04004144d00c40d0411a03d40c6440004e04455080c00341c402d66030040400659040c0881d1201d1481c0341c50188030782c580c014260000d000d6402c5e0141002003010103004c2d16480d0802900c21002e250342d9101c000c0d038640c0080e9524051b98500b030300100d0396150a00580d81601e8101e40b501e261822400e004500508810040030058000c484e4040b03410b5584026000b51020f02e02c004000c0307040981003da0901314081d1600380411a00b04040040168a443d92422a5a030040184e11080c8011801114000704102d0139406031030540801c4602d912a03208005070b9001d00142e61100c10b1280d145040c07048010700d8144d0550042c0402d0310303401e01c02e4009898814851a109040c03122081e1007003041c5080390442e001007450303c0402d0020b0350384070041c9001000c10241f48101d0b4240500020340f51940703800044e01140e00040064903e450316070400c1c0b041c90003e440502a602c0504000e0340200002500900c5821845803000e43c52410300181c400c40746680e42017021042110f02008284 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 880419433 1250 880418183 880418191
    0x11505060d09060c020c031005060f01050901050705010204121e05100e01150b31030f02150d0506090105120715140c07050f0a0b030601320904050906040f0308 70
    0xa4403010304078000f0f6802e0042510209558000f4a609195042018144510f594034903600c913107040c041000580e128440500440030a08040c2d0f030b03c01c044001200c40d48140000a49598000200001c50100841c2035601c0180600c0868180d021640c0324048600720202014003641c0c003d200b00342c40c403003d5600584002c08044000500c034400917500844000043d400740c3c07a503041c00b065581d80000c10780034208084088090500203050a00440c0c210b06095001c041c01d1401d4059000045440d80c1c1401d551104402e4030b4140c5803024200071601400f403c07a145402440a000001602d040000500302215403d1001d04245030030070034050401180c40701d0070810415266002525018403000410f81308400d100503040d130341d00384010700450805407041ca0780121219282001030206030b0b400d40360451000d2a0900c11500c4e03202104c2c440300240d00340d00d10321180e0740e0340550459100314024045001c068605001d40e591321400310f41c07112800c0303402500092210000e0030020740301b04031260b84 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 880420683 1250 880419433 880419457
    0xc030506091504061a090a0e060307180605090c0c010e071a071502030f07180f0b1c1b02240c1b1e06100303020c12070519051201150506 60
    0x61350350750000c0c45074549498070518039410000032007012034108414000007034800c0c1045c1d00070340c2c01e1401c00710b96605418800d0784442407001540c0064149a07130041030041100034510100c909055100d9040c80e8400586008198a0031490b1440e0b03036000318100d02250011884d2495410b08628038650030fa100e494212071150b0100d10301b003881282d51000d5400340b000c0850746140380c43c0000005e40340a12200125a06c074001050401540c00d10543c94810350f041408090b844d0841216258283c1c800340c40040519410a95607400c0840e00c0c51409440d20001c0e0b085983c080d10a442d640004c0d2114200818070f0402c81002800281d11a0010840c0007400807e0a0304007035200c0c00369081c114200040d40c101035032240320007010350707041207a1a080360700c05140d00f0b4481c0c41c56401035504e045540b4158041c0d803510243d20143c2c001840302030003c180c0075010f2001c01000201078100c2405600415208502a000c042c66080052086114040740f00000c6074040d81000100b2613503400643c41030304 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 880421933 1250 880420683 880420691
    0x5040b0a0210052d36101a0108091b0a0b3601021005091002030a02030907081b060304020d080a0903060b010e0a030807030513060c0203010c030506091504 68
    0x42142d9951088030721484040d0044010180130840d040c004c080d1403030b0001ca04406510034098a54050040030b0500c1040607030a110450301c041c28070300304050716440345120b8014525880007014081c0c000d588080040340f01d41c1842400310b001942e5460041d5240d184aa104800c1e058441d20b101d10741c0c20305800020b200e03150559a90003401003643c00550340c038540f00500c44201101400719001803c41c6064604030b000d88481e2680000c0d500d1300c500500e0159161503001044541d030050080741819505003030155907901d403100b095000b079030055410341c3c040e2085e040c00082400d00070581080c40c0c103d035105512410380d03c9040001c940c0000d40140c1e130200040d5104c0d0002000c0e000107245882164580e900020700c1c5040041c200d8135101e01c000d06000d001500400141d803914985025039a001840c507488802905041b0b4550040340b200303000d020840d4001061032500140f0140085200703c2c002d11000a4451044040c0e5000b075482d03a40106100c004034665030000d80142d20720800c0500009 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 880423183 1250 880421933 880421953
    0x2f1c0b0415022809050a120b0604180f050f24090c041e0f11070f38070302040b1204060b1005120907050d0f06022106030f0d05040b0a02 60
    0x34008503006044406880c076010000019904662131200400046505903416803030507403d20744040030700000401c1e08112100240080c0e440303607c4420420340c03200007001a40b14618100001c0d1228440a48592140c4249400c6414000800f6440f861142083e1000a513603c001a403407040050079030782c031a0003a00d0400c0c28684452080d12600e080c5c40084e00d0741d107990b9182407000c807400c2c0c07102c084c00c203410005100341d000300d04005c44039403c2d8840c110782c2c03041315a0708103c42d12180401c00d0a1403c041541d808030f01ca21400400c0c000e000403e200c80c0c40a84610d10160304a105904c2503000c0d12038180801440410701039645079025014840c00f003190002d1400150740d0311161000f0300040b843c0440c43e1000c1583d2031000c140d0000c00c400041c811a030600000802d40ea00b2200000d000d0062043c0e036400f088120b40640b0344c510401078040c00c2c3c20245502c078191000048a01c54000c0c0300d034460245590200240800141802e502e4080c0351604009081800d680910129015071143c50206 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 880424433 1250 880423183 880423207
    0x50f011a07050a0813061710230405010b040501020f160909030509030d09090605010e0306060d02060f03131415010b130f0f05030d2a2f1c0b041502 65
    0x100403904114000c8107425003031200c0030f1f142d0340c9038144014208000c181000039110781d001c0b50070241d504440b5400a0301c140e0302103200031107084102080d0000e080400008862070018054001c0d80e809800ba201500000c800840e59004424076800c0f451107034030010862032160350b100c0481c4600a240042c6040d0800f408a07280007503401c0e0410000b07800500400c003005951003000c0241c142403a044c01d0920343d07880003035510354014007d98491104403e0703c07000c558070ba008440384111311f2007000c0d80306d1034040240407250518600a5541d20b0701149400144079010a07411100d801d105007141e190303400c02c2e000e00d07556008140070304041e015148000c01c044d151100b466009200350320308451103e0406c030078542040b4039150b00c60300303001c403c000361903081c40107060192040c0407101c0c00d80507162180c00c04418104c01d400d02849900032480c0d1040707030304038042c021107009034060f0b035482e0326100c0c421102e00d0b80b5010503d010300b000a13100041400a001c038001c1e250b4007000074101505191243c010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 880425683 1250 880424433 880424437
    0x90607060e071505040506041a190f0f1412060f1309230d030b0a0b030717061e01080c0c010507050a08010905100312030905070b0c01050f011a07050a08 67
    0x1c00c06074048042008140050944400410980e00d4100e042501e4070010850a02a41c00b0340c041d01e000ca40740380b0040800720301c20f035030120b905014070030903528800c000030303148400d10301020000800185695a140c4c4c0031f805400200e861081b5000e19101140d280b40c0c00314040600f03820b0b40441c3c0030f0041050b40d40c5840000c1c041d4401d48000103000f2485103800c2544035000106004200610b13181000e100d540410103100903110b41c1000303e941a05000010400025038102440c140e4010080c810074075032286000c10400041070b0f40300304c25111070301005142029030101e480214480d81201100754403030280c098003d09441c225a0510240d000c4031802e40c3c808452030400a840400c14080d09540030f507955004144104040203981841045860ba029540c0005010032904010381d4500e503100b9800108001e0300310060b202001e483d00c43d03c1450754044540903610b58203180229108034410394081c0e048a1411941c414010b0240e0515180c83c1c1010409881c10302a40f0070481c08201c034000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 880426933 1250 880425683 880425701
    0x3041b170105060301090f1415010603020315010207030503030c0a0315060c0312050f04290702060a061a07020f031203190e060f0f090f0f0c0406052409060706 70
    0x14400c05500a8200a80c00c40310028041031207681000c0000000ca8400800b60071655005440d85030074800c000007051a041c501c202c500d021800c0301e400010040d5065024501512048807039440c00780d28980120f903600a40c2c040508550000c00103d40450084030041494035281e050200da200f031001c0515030404c01aa100e8000f050f0480007071400c041c0d012204111410041004000606024022400d205030080005211680c0d0064a4101820104200c9000da04031304011030300d0b261000e4002d450310f400351038400000d400d010011030f02d05524011801c0d23000462100350308004d410340030000b040b981d04600541500039010480400e02d503209c0154860315250034400704101141d03450310b0448010001c224502d130824024403210b070091503d004d4102030703e0304185141d62183d014890070b040d0a0000300324140314078403d6981000e00860b0403034420004403010070449540f0360a1044e001e03201c4564002c1007403038449040c00481814050182c2c41c1010344200e0414155a48480894120385 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 880428183 1250 880426933 880426949
    0x80109110114040f0303030c0e1c020102060604020f1603030608030f04052b02010c0c2304060f080d05070809040908130504020a0c03081b0a27060903020603041b 71
    0x24102105582103010250b0600200b1a09450a803900c01a50301403000e0740401800c05440b0355030000300501c688020350002c580109551000010030a8510101c0030681d4202c2c054003440c0300054031841d0520a41e140700910b40c198030301d0010041c5800c040781c3ca010038210b0502d0b50720701d4042030780001040070300050009652041ea495003000d041028034101641c0b00c2c00c00034115164691081d1800c400540f9241d07080c200840d02c4d044c10711344a1138010f00b60308214082c094000708080d0076601880740f0300c0d4400082c0c40802c0490b48821010344042c48600a131415544820340b810a000d204e50000c24101d4024860142032403c0040020b0694a0300041500d135090003141010818184e100e4030390042c64200c81c218640038148401500c1c01c0c0b8200406014468014000b07035401d260102d05801100f90500a03a66070616048050a00e01d00890b40485c10389030040e501c3c016010441003e003d55009494410b13801303245508210701540010421240d400041e02a0350f803400c0b04d40a0310b8081d000d04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 880429433 1250 880428183 880428203
    0x3110a15081b07020a09090c05030f2506080c07060917030a15031502090315040506040b22062a030c020d08060906040506030715080f070206190203060a080109 70
    0x24070440d000c8408158250107000c02c0400c001d20060fa41c1030808001c8070724030345011444c0c40146c10700001e031b804103511150f01401000c125002003100030444031103180c90121040e40004070048804084075450152101246400300412240b8400e8009021102c0c81603c3c0898030215079074410f00010140c1c40344c2e12000341c3c00301c01d001295a150080d6003084007101c070031810740c84c40c54030b45498007040a0b6801d02d6180d070020b0f1f00d28031904d0501c00c607420910b00c00d4000c43c3e64101480c00960710700c8115402c0d40c000d0750280c040744042090355107451541c41301e00d1403085080340c1500e8a100a000b500b000c0c1e900c0004909207042c0000d800515443d02c680380303880000350700030002006802c00e10401c1742002017180ca00c08010069035203090142d082001036038002156650702000c030307160030095041902e10b00030740d90707000305090783c008001c510801820500d00c9083e00c90b504180c1e580c040a98081410318400060311aa0b1940da5002d16070242c8014016649540c0d83c0b012582103840e580415a000d03402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 880430683 1250 880429433 880429441
    0x100f090201080f100e0702030c070b090418050709020306130e1501060e06031506040b040b0301150f08060d051f050a0c0e01090b2109060604050c03070903110a1508 72
    0x200940340c2c050fa11200640061515140c4031844502c5400717000d110039498008105810b10800558004554a004841d14a40c540c0c036103080b01d800044c01c091141c0d050210012080c00014600b01e44c0985c8640148606800d04c40c00e50041c0d00b0003003035a03822210400e80071140c0c08040c0a214440807484000d0a0140c00440b810005820b05801281c284650030a40012039102c0504403540035040580d1140034031140380c0003d001d031086910800e11150049404501c40340d45a00560403900560075502c02900c080760700b40d0b03403d100428103d01003540c0c0c600081c02d9041210300150305d1445101030744c010505d800e90540208003490452008071380c2e83c40802c08a55250f1080440c46503850030700c959165a0b510008111602e14014203254400200da02030030f0b03080350b0072030020704516018040c8180c0352000c0c00554458044071490711450612003c220400c030f2030022030380689520b0761488201400d5440300a00300003a80e150541141c5440b00c0011251602d450f100404142691040f4050038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 880431933 1250 880430683 880430687
    0x1404020f210c03090a0201080a020f04060210061a030103030302130b04080a0b13020a050d0819050c0606010c0819090e09421807030804081b090109050603100f090201 73
    0x401124182e0b60800602c40066400641c0384265542440d00c0001a51000d0161000e4002c4568000000c0c0020402040d501c2e00030071400b4001440260800066a440d0a00f50094603c4d000707080c900720027000188046031003134005245000004201c10005179444040036051b9001e0703402400ea42e0480c0212800300700c0144021508030b00400c4101901d20895000a4525004c603c1964410307040540c8000821074a00195281c02c000707900e1900b05d054150364043d01c96071018411081e9800751400165241d80100c0c2c08141d450b42150f04941030503440700071216a900b80c91000000d10000d000e0004901d10b10000d81d6200e0702640015003820ba4000c2a00c0340c15000d0b64800c05a0351040b0803d401c0c02540c220078440362003030038010a01840d01c40c220826613800325101c0c1840c0c940222040403043c000a18014011a084481218216000c03046a4554070a00d1301070070341e00602640042005020907000f0310f40002000b02903c114420114200f0b0880301203940c00e090360703601c40340d0789001e43d1703 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 880433183 1250 880431933 880431997
    0x40e03090a081e012322050312072d09080109110a05060a080c03070e06071a0109021c0906110403120e120307030c050705180a06050301060b041404020f 67
    0x55440f90081c0020303440b421000040d07000660300300b00882081c1000801400d0301040c0744605120a003c50000d122450420035103e600000910702d04d20441401324603030500c03071140b80c14a1850040d812000c290392910500c200501602c5c5d100c100446807038003082220080c13048081280c4151140011010040240980c01e0303ca984580d01c00c6505020241360749801145040e0700c55a1180a176aa030b9881801c107586128141c883c9541282011864000700010340211174400c3c107401d00410020b84e40c4043d618243c0c810004040300302134055140003100042600b100741694428400881c000000e41410034450300300d548140e5403441d018052124454000f4030f41264ac1c40c05803941d591880744c12003d26900d00c184140202001120542c4100b80030f001d02c610300150600400c0a1810030f0843c40031601c03d5416602188847d140c070100113940e2405102e02412541c24441182c01d0520b00800541c0c890095104690007507000c0000c640510344c49401841121240c40c810015080c0240c1080201 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 880434433 1250 880433183 880433233
    0x120f03180102120103030503130c12330207050705090c071203090b01140d15020d0b0d032f03120103030e0f150a0512070903210e040e03090a08 63
    0x907481000074400c3d252071850324a065035050304002e952600c0d448640e02e8407801115018190118a04010400f03018242c60755181074001c1d20600030020540ba16490045225009075101c00d4400d06101030002c0e80d5000b500050307002d00140e0780c02c04d0355007011403040380e402c540c1480b0f101d50003c1e20108004810300380c218400280e203410801403443d03070303222250040c041c010440054030140f4154950f5076180e51a82c48140d1000d03400144900d0030070340070007940011703d6180c260b40c103155440055003400780840500c1e58040c0e880c2200c03042d030a041900481034124031841844800d40912805000410007811007488240807041158035600340100f043d0300300807805206400001805655907210f07400c240c071498060380e80b075075580301030030b42a50b04c0e12440c84524030110b01030701000405600000c0c607408a80c0200f6814014034542c8440b003c0400024900701d003c03a01800d0818041e081c69840780640c44040400c69261030f40da07000086114503250f0100001e40d1008200c01c0042e489485110f0300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 880435683 1250 880434433 880434481
    0x60c030504050a1d16081b0c1f060504090506070f020703170d060b091005030703150f06140708181309060f0b042702011407110f0604030302150405120f03 68
    0x5103403a0900c00034402d106c007030310704203510038511000c9180007800000c540c4000321034021512902505110310a40420140b03e485045191010005007410300c1c0c000d041c46140d000000e000c151791403540a80d4008100301c50002144200c40700880041c01c40c101050488100c466011340b111003400142c030549110750010307400b03038005103c01000c80e00d40c0e00342e00280b00d8060a00d9038903565650412401002409000c00d40b0001040c030004078506101c0c040016500c0c9662740c1000c030000c0d856a20300030700c01d2031001406002c0030003075580100360b00e1501003045900185180c5040a038508594155249810180d1314a541e4814540d000e48413841940581001643d041c400ca4001000304085a0007001c800d14000204190540441e07101c1d1151030351500ca03070504680c4440e40d50900b14140c0f071401c480c0a001d815800702c0340c1c0340c81c903040c400d40741103a074142c0c002d141c801000c4c124101c1d40100904212020711800c0b0500d441541c0300d0000c0c0410f4500250b0b015141c0c50440c96025011404500040d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 880436933 1250 880435683 880435711
    0x4111c08070f1401060311031c1b020f130203060f0307050d0b0a020d060605042d09090533010b190c1109100302040e0d0207060c030504050a1d 63
    0x10010300004240c5030441c0e00848200d5841010381050703241d1a002c0180040c2c42d51070a0000700800c0030030940c0c1498100c042d000c4885100200724043d00300c002821521020910030400c0d0880e260701c0080e030141e244d101a1001511a10750004204400e208403140c01103680c01204011840c100000314600c0b1100484c000c0030090b180030082a14043c6080c0081c003800009400100c2c203c045804598911840380c004000c02d60342c940c0000d2071500140900f0400d480e4200d400a03510301c28581d00c01110314503c0000088a107440c0a0030001c29081c107080300d99014005050400000d026041d504150300025404c040c003158600e5080c0361801600001c40e130314010300802c00203404007101c0a081d21420305201040740c6032410221b00c140340c840780781a40800b48100f00000e00c140e50036800101e81c400d990621044518840003921484906901c83c0168051403040119900c00c000b2505101c3c0641000307440d1540700d03404142802d130241c10904008000849218150151031009a031020442c0141c034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 880438183 1250 880436933 880436989
    0xf0402030c011e0302070f0803040f140303010b0a1b06060816060c121407060504060c0f0c030e0f191203080903040f05101202030906010303090f0e0123090411 70
    0x520b149400c4803c00109039020881d10200b1050041045040750001c400075180d00c0c162500e000611440e50302108e0b80c0c400440081d00b100f42c00819241070340d68a000c2c0381d040011a440440b0020391801850300102e2290800101003101441040d010b803010801401c0390341071281c034041405e040d540c820760400550403003110119848600c80343c1144c00510b0b01c49c2e00305412861070440c0b4020007100cc0d02080c544400c0c00100030183d800b828803100c05d1b448210184c0203401042c0e407410181c00c030140102d10404c03130304031052400d11030416011400500420780b200803040400100b0005801c00c0c0a03030007410f044030044c150090032030b0f68050f0908005500d02803c20a214103200300302d00ca00c03030055004e40d290000d80d6014040c02c402203d18140d0454681c5000300090340d45000070300c019000301d01c2010000c505800d42440c4102030b24482c0d003076900281d1814629084e801c80c94060700c1c0598015000000c000e640711200036003e24042c00d0030140451610307003004040c0405c81340d406510701c3c41e8400c0b2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 880439433 1250 880438183 880438217
    0x103051522150e0c0702061b0f0c012606040f020a0201060f0e04050703080304020d0f1b0614040e04060b10090614091008252f1e0f060f0402030c01 65
    0x680d00c240081c07001c0c1d491704054030115050707000311680300d00d035000041079060076510000790000030214034100716803442045030010340e10100c1d0f950340d00003034001448403035020300076882146400c100040c3c4005031014a0718249400ca0708401e10900050351070380810448005104c1ba6040940440000010725082650310f45503508170921008242d200d02000107801d540c0d51000512085070071550a00b4609801d14080103140250150340903900720800340803d906210b400394181da046104015407805080c88540c00d000c1e03400400c221100794480c004d500d100d8441c00099401e043c0c0d592243c00090f41800c00c040c0070000d098542c9001c0a40501025000b65181c00010900d440700781403000140d1100b2182d81e0041d0440d003283c9100100740940050703442e60291030702203103502c072001c5080910314140d4034000302210340d1080400da900900c08840c01e8990302c61598030203a1104119880022030168083c00c0c80000c540140380424403030b00308000d5007000d21125002c43e03024070300011301c0c036892240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 880440683 1250 880439433 880439459
    0x1006110106051f0212070b010510030b0a05040e0a082a030a0c290906060114122814010f05092806030606081c09080a02010305152215 59
    0x114400380091003d042c010702c2c1c020311814154071034082c00f4503904c80c00f44c02d15400914080c41074a00918000b2084d00c1c0003032183c800d450380280300178694000703545450100800380c26100400e507050f001d580031900020b000b55004000b4410b05800740307008100302060308159641c403003050100a400400c80440d1041e802244101c0d500d40c4210102c1c007002c00d90300701c00300200c00d6000444d180480f490131700062940000c0c030f180c0326000907031300c43c031854070020781140390b80c010400218030003814207010401d031641c681c450300402180403c4c100e24030b2240c0d01c2060141ea9410302c1241003400c2030401444000f0700615410301420b81514600c1203420600754070742c808036900550303585202905000300d2180038244c000c10015070300400c05101081d16000c01940715104409000740c0084100700c40303641c41b40101ca00c0c03c21100398001518501031242c005500be003074010282038100784c00d113100d41055030f00da04440b490071720b10320030a41b58007000b252000115110408190b0740c480c0e01640800504000c800307 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 880441933 1250 880440683 880440709
    0xb060a06110319050405060a17060d020310020d0b100c030e180f0406020d09050304091401060804060c02070e27030c030d2307050c07061e030c090b03100611010605 72
    0xc0100312007900c1e000f0448182c09140c0015500c07090006030b00030001e40c05500c240d4009a08648032106403203c10800c2043c80492400a4050b082202c0700b550b040700759405002042c07038484011a8850f8103a0000b901139407210b440b8008104101c030b46c1c42c00e2580c02000700c07204810a0b00c03030321b4403000d2080000ba8500c03070080019101ca0080000501080701030f0301a00c0000550b200184901c8489207000780d240e0b041806802071030b628040760b604d031162481c03100da4101c828a44450302c590b02c40352101005007208101000540c480d440c130015a10304c020140394030440c1212041b003404a5200d010141e000701c00000828549d0080c85141072011010040b1003413414151800907103502d51070544d8040c2c1500040e04a6214040c02c2008001c6070010b00030100300b000002a500b401c1d071114000d0300c021050b060b10050303021400745041041d0780a9071100e00d1004560401e81201540c8820f4600694030842d014a260043c0c1d0104100c0c0300d80000d86051084076039002071104504100100f4041c500a036 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 880443183 1250 880441933 880441957
    0x3050a150c0c0f02030c300703020d0206130305061014040507020618011409031b0604051e010b100e04060905060907051e041508060d031202250b060a061103 69
    0x10b2000f00455808000c2040c031040090600fa04070307002503450042079003480c0107a4410400007800c035407014102081010a4a600a0144003000d003a5024030107680c00101d21443c0d0000030f08004004200200002403280c40d510342c80c2c008450078402c041c80e4461441d0b2903507000c0e80c100000e006501c4c0c0c0218442d540300c1030390035186074034030311152076940900303039800400744200c1840c8140048a240480140021106081d9089445542d251002c0c2d0380d000c102d5000e4023503008241da41c04800c0544803031201034100c6200205100c0c40b1200041c85101c0300715200b101040e80303181c0703d0540b801c242c003131803006010072070303041009207400f0300819030903180189501e0400c2000503048421642c84a2050145030b1207202d0720b43c0300d0b40ca850a825030400d6600e003000120f000480050b02a03d003c00b07e008405516a49107681041c0d0f00000002035040840404080340c8010045996a60b8089200b082d01d17004052030301302070829400f404000d01c2145c2010040100041c600c000d254000000c807500790010b8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 880444433 1250 880443183 880443203
    0x2130306181a011716090506011e031413020f060901031503050c210a1b09020a03020d0c080c070f03230304060605061e07050c090103050a150c0c 64
    0x44000d0055030a05408000c101c02c10a1100442c03080b16a40380c036058071030003400d0103600d1004641e0700f81d407150700074081e000e2045a031100340305403042604115003001040c10010030790a1608020840341e0607500c45140040d0392840038568683d000c41c2c805412500e4a001c247d2406160380104220b0b101803180c40d4014040003400c4040343c0d00c2a4080e89021003074000c0c04185940300e2400c0c60311040c40592462041c80d117400440703040e42c0044ca01034160b01380540100003032880da0341d900c0040c0310b403060515042c0e02542000130345140940001c03c44800f40303079001a5680710a140c08003c40d07030031403038100070808100e0400c0040b4080e007003101e0286401500c43d0300312040394a012140c1380d020902603d0345010504c03655003170861030005580507a201e07450900c40b49464070207008080c0903441075a0b100751110304411016000c0d1500a00c4c0003405002030768a800025004164060402c2e881152650b009906001c24482c248410142e0344031420717803e200c4d00b40d1600d0b009040328880000a0512140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 880445683 1250 880444433 880444451
    0x615030703170904060e0a0b01090f14030f03031003031b0b01060507140d031d0d0503010612061211090a14010308091c2a030206040b0c16090204140402130306 70
    0x40300040d07800d90f03940140b050085030781ba10766401883e5001d9400000d014144024100950f0180507103101f40c84c0500e140714121444c01a02103090b00a156a1a8040c054078000c44001c02051006500c18204907560304074491440c51300400401c09803910f4000d61402c1043d007400140d41c464103c0c111041031508540b00c1c00142068902200c000320f400c0d202c0c0c071688662080003501030b04203442c42c3c58000f2810082004a0280b80e48039940306010100103a0200b00602009001c0d413580ca560800355600025910f8440c280c5e4030004180c80c0e01503480607c03852425a00340b0b0010055035200700c1e03c01c4144a03541c64211001215401030000414002d004200807540d5110410030a01c11034a086082001422a05149039035084c104826140c0c0c10a00c002c451001001c2041281203e5026090502d414a813010303030f05454000b1000400603005020454250002c1d01e50904050111005e005940f2854010400ba041100e0400c46000700c0c0103020010340c0041d400e009808580d04424003003102c1c02 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 880446933 1250 880445683 880445723
    0x30e0a0f14210303100906152a050601030b010e0702030f070f060b03060a0501090e0c03060f04061407030630060e10020706021b0f0d0c110d0302010e0615030703 71
    0x8102d200c0c5141500c0044104051201c650a480c07080350512442004070a031200040031003040032203018804580641100d00c42101040304050540c450f020036510005920341d1494101792080c0d0050711482d42060040c01800c103202d81c51074010b20b050004501d0103000200d864610b00a5041c050010420380002105001094100311020440142507401901e400c22100004180c203020301208507180481c0d200b0816070005800741c060000800429080d0b490700c00c11101d410000f0000ca900640310340f90480c0c15280c140c3c03218010041510301103007071410242c005c0909150601108440528403581c0600068440550804241c020a010a25483c0b003a18145072100c800d802150642c030000740001480f11a5000e000c101660b941100c0c88076480c410200c0e40c0340da008000e81595084101240c444c2070040744007a01d00c510a281c1034480d07540150009509a45840e000ea0242c0d45501c4026040481840b42541c00b48114044003914182040401d40d61041030100900c105000001400125 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 880448183 1250 880446933 880446979
    0x4051203010e040c05030304081b130615080601020a0c0b0d060e010803070614060916020a291602030307050a09050307080a05060a0902060d05060d0b04030e0a0f14 72
    0x1116545903599503550310900501070001c540076100344e405500301040740c1c035003c0211000c07615000c00615445200c00304402c0c05115012282d0380c084030051840c1c2d464a414000c0800400594842241001c00d0300c02c05440008000c20140c1190000410a000600b40b100c1c89015100c00c0030585071259140d4400c0001001540c00c401d800030403400001840005c008020002144135900c24020950701c109460f41044042d00c43d0f0340d00c0040200028414600300200b10a09152403040301c220b0a0151a15841c0d403060340302d40151880d4000c0c5207040000580002d60f044403031b1100000000145c028025100d0001034400c42c100100010300040e418821000320014080080965150550300c107829507aa40400504651600400c40056182d6495100e03600e04542c010f080540b419403244a00b200624004024540c881481b450b2800480c44094004d0322480c842e881d2800c01071400010030240011640c02040c4440c094001803140300280451000300c00401e880500c081a89100100d60807 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 880449433 1250 880448183 880448203
    0x31e021506030a050f0d031d03031303120f020904060b030603250b0d05070906110a03030f27020108091603020405070212070809040c0306030308060d0201091a19020303010e0f0405 79
    0x50f200307401c40e085c007240d004124070324100c0c1075071010000d40d40703408952902800c000710410355640040c8000f6140b80784180713001d41c2c0e1a1017231602009814100f1120011281a8010209100e03030218012010741003d01c07409000d0040f446695045151400001c1d81d903510142905650440c06085660410030000021016050300d1040a85821251b0303c50300003014101c80300000074480000025081c0e0003400700722500e20301d05029100701040b90700c0c2a4040c00e8603014603c6819501c000381810990b00d40d00070300045000130f0005a048245000040802c00094205401038104c0c10035100ca000c544404503048031390503074000c516961a24016420b048419948100381c007000a0f800b020441d001c1c1c010243c0502c202d13800c00030f241000900701e0840d1098080100810b890f00003040325440c1104050603003031b06c1490036140c0325803078401c90300240880a12003801c9800c00f06040c040003003416a004642d500b40d00c002c0d8107640c58910050701505015051468540c1480c01190601c070301440b100c3c0d40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 880450683 1250 880449433 880449443
    0x60902120a0b150f0a0b0a02030f1803010b0f0612090304080322080604030c08090316180501090207050d08070e04021303120305010f14030c1309031e021506030a 71
    0x11503911418484802c8404a85406640b498043c58552600e00400c0a1402280203014a020103040a6020249900010307600f0158402400b0030381340784008070300402c03101404800041c031240c0403000307050030348142442140c89011081610031294803040305a0b450101c4003402031405469039120340c1e0440c0b01c3c50300b0000c841c0c0000100d051074240081000402000c009640c1c115042c1d85403000e644401090364018001401c0038400c00109401c90003400480c2c1d0700409403074040c24600d403030b4a50720149602c00001070080d015203e144400030301c6100e00510b540c2205502c1c090300c2c5d0b9075403078a9400c440300080034041c00b07001007901c9600c10641c540e9a8000500115a50410713090443d40040e030303920044441024101c0103c844030b109014a80c102c861100b1100e04031401e00e031b000110b801e081c101154140c0719080d001410f45e07032900c0e9030303002101a0303034400500107001c0c1c1001801407500c0c1040c0c031040b005a4100c02000395000800748880c4e400707030302804140e40b10703180002e0801c8002c050181c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 880451933 1250 880450683 880450693
    0x7051804091a1302060906031e0109050109060605041d0702030403080d02070c1410031113090b1005040b0d022a06190c020a08090a17030d110301030503030406090212 73
    0x820400002440d40d5020b540c820018140e80c0c800500400102c40074400940000301449011110700b0080d0180d90406c04200b0312360442101401071410f9a402648070024403612030b0010010b43c005071041c1e8014041c18030f442031415040402d036883e038161b07688843d407a41441000040b0f12501c248240c40c051603100c44541d40d1840c1242c6400c000e508056010303114447c03e640002a446e03c1001d80004141020340040240010100180c005100080030103207090010040c0c1c0841811780ac811034041e2096903000100d2a4074142400f90218010490b03c090140410007800b00c0640310007903524a492840c00981c1d1804c5c04d03c3c0c941283c440d010710410410314051440c101150f070204410340324850304504440c010344d04840d040b09a42c041c0030441c0141e0410b5072000041048074008001d030100c003400c45900c5c5581d03040700400034003612110802a81001c02c40350750b50791460044080c0305a10b0203a007070441d4107644030319483e4131014200611503692003000904544690303041018a03842842034403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 880453183 1250 880451933 880451951
    0x3090f06040303060501030f0501051c05120c010e1b0d140709020a050304051204050a0902090316080d0f021b04200d060302090109020a0f08220c0e0a1407051804 71
    0xa00548902c2c091175000c6410a03a420740d200301c551003002d04880c3d000f081c03200e0054114540c5a16400842d4050740c15004906401420b01d004100510310880f10100004113402c5202d19281000c98001c0703400c2c003134611058050910359400c01c13940b00302500825040403000c42c1c14000f034030b04201c80c1c0c4800e1407d4004070310f103480190000301861285000300c06541c009140715400400c68480d84c06000d900c00d8070400280810707100f40d409040e580001800700c91071000d840340003c0d21044c0544c0f055556901414403c0040b50b400422000e92114600041045024003049894821881600b00340260343d54a0010041c865801400030780603041e03401150b440300b000001c40c002c1c0031240800c1e4002d0740e40c0000011a551107100f110800007003503a03400509030082a0840c3d10b0a40602420b54807010491001c40c1c007440d103000900c04c14400e455080b901898809031200e0080014603946d29185460503290701e01591a1003558080910305e0480d0340c52400591500007000c0340e0380400d03042447c01c1c2c048 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 880454433 1250 880453183 880453187
    0x20a0210210c120b060f0904151e0608040302031603170c090a050d0f12090812071e0c0501260112110d0503070b0a0902040207063e03090f060403 64
    0x201c40e2120750382da03d16025901804050003a20700510166811000030851941c0d0f00d410840680507603400180003207174400c013150481c440a10b2a0300308648180110028032407064088601c3c40080951381440101841d054030041e48a0144008504841e000d581c255010144500800740303031140501d40d00400303802c1c507041a0303803071341c2044011500641501d8404105441e0490100c00f0481e4804000d01c0341c840b8a0f40d506145d0401d00010100b8094040004241c4400030b10840341c00b5030440790300c1d40c1c40e48014100f8540c804003100c0c403903081c0740e02c001c82040411182c00b00c5070151802800c11112540611040d24000110403000400608640d4000308031503140020249005008040c07903c01100700000f00080d2110559004095900070020503000545000025034040310f42c200000d091482c5070085001e9038013105045500b50759508850359030150300030065144c50804581c4800c0c0008080c81011540207071100240806800310000d1409002002040020780e40303070301a213103181014030300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 880455683 1250 880454433 880454441
    0x5040e101706060411070506270f0a0201030b01090e06010c150c0806030f030f0d0f09080c0c130507020c06070206040503010e0a05150c07030f03090503041409100501020a021021 78
    0x500f074403da0601c0c0c40c00341201492415102642d8100380a44810340f20041400310510304070442d81c0b1003401d10402d03404140c0040c081c04a0342128400038000d00c00492000500300d0b2101e80225042c0058508c050001d41c9842d8103c4d0385c484402e00309140b0301e018905000700c0d00c41265109800580c18181c003407100b00d51041d03c050055006404440a0521401ea041d84901500200020700311060024180d1099140c03c5148020700f2030400280324401515450510780c0410400f540607808a4404403103818045140d03d01d040d40f0503c20042e505001d40d0003521903c8041308540b0411010469a040d9502e040894000381001002005221018414141c40304462402a030703071401041048440541e030011607038410f40e600e00704549841c000355000c0d1055081e40e81c2030000c05070750b1b50b103950009000f000200b01610044011a842e18126030400481540c000d00c0c3c21082800081c0c1000240d80000725524040c0d07040f921003100700d2001c802180c480800980180b0348910006083c04a8591940 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 880456933 1250 880455683 880455691
    0x22030e060f0903010b040203060303120c040806160f090e011401090503100507120b1f03090c0f05040b03010e1b150f0a0305150907031d0102040f2405040e101706 71
    0x1000b40a82c018085c10001280807c584c1c2c150075400410080340f9151040c14050ba0100055804609264030741c6059031601000b11040c901c0182d60020f00314405ea086105800345540b1881c164011904021001c030704414107102d012070b1503e8500030490300e603025081030f00141001808854a64080c1c46040c03002e0301094a240011403504221013003403038800e0080b00304445002e8040901650811244602030368091a010101a070324036003540003c06629101c402403442a500c4021f031402c2104001c111104850780b203100340e242024000c09084041642c850000c01c400e429448900c01038003050300802c90b41042d403072005000a400f683d80031004085d04901c0718643c2c08121a5682218141c40c0b201c0300c44149901c042c2c520f00107410544690011890a545007440045031003030855681c2c26038202d81c01100e0b036590014001d0120b5109110302c01d800c6070300038010302120400f403240540380303100d903000d04800c0314445000206010302c004144001000300c0c183c1c5a480491065080b0788421040d1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 880458183 1250 880456933 880456939
    0x120303010e0f130f06090f030c0c05060a0e1e03030c0102030a0f050705121017072c1909080301031b080715030902040605030609030417030322030e060f09 68
    0x81d002c509200c403028007081c49000e0440d00c000003141c55480340c424514450100300c2d00070b5115091080040c50103050900c40e14425201d13500da26880745006880c68540d5084603001d402c00307110904199500c44c0700703982150401c2c1c40e0016518141c640380c10070f1040240441360184000036988210751015401584900e038240401c200c8403032925404c006483c0b0985800e40000c0d028009080010780149250340c100c107620040f0a0340580e1500101d0440010a460300c0d91500008410081c030306003070740d00911101c131408603155041000c0101c0c1d100d049002d094240c1c6000c0c00449001e0070101d40d405925a25000b8580365129030750b07031401d030200114007c0e80280151030640c0005041c0b03000a406030981c0d40d9542104c0c01c1410f10001103006040383e05003030760f001d6116030002546407030510407103000740407000c0599521420885a03560350b00b0000c0188440d940104104007841c0700203424050030041c460b203292200041828112030a05500022561101c000901c0c401011550780040ca0a40000c1d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 880459433 1250 880458183 880458209
    0x50601060912080a030f0902120c010e0301020301030b1f08100e1b0102030319020702040e0109030f0207030b0f09010e1209010f03050c0403141906051b091e01020102040512030301 79
    0xc0064011201c0ea0410040802c80144010404d0320702a42125140220407080090081540e07000109080c0480300c40701d003d03400100083c1e049581c02001c11603604c2c01580258695499940e95142ca070380000c00381c140010402251000006c0941200c100030010300d8101c03044c00005030b11540080204d1448004c0c588500110f017210a0302c11072010710070801c141c010310b0840d0307038080c0c00690032102c207600009450b60800034003005903a14462414508801000000c0000c01454068003c01086078441d00350f501c010010400940b10310300c0f150340658040c003500883d8986446c80c1d800350200c00610f41541c056402c580c0e00c440b100c0c1000e404890401da072030111a00312000e060303007210401e840100c4802c40800050011840840340b20b0380c51603403c0100e80280400100070318a414a10208585a035165800d01c02862008415000f5410811040c0f614041c00130340083c08054034035004240f407200f480241c02032a0700070360555005120280548690401605003140ca82d4024059004a1414 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 880460683 1250 880459433 880459439
    0x409031e02060f0901090c180605060c0c010314010807030303020d0605041a1005130b071b09050603070e13060b01020705060d060f06030509101104121217070903030e0d050a0506010609 81
    0x2050081c1446c0c80e800c810a40c000f1410071200c150780515005848041c203480d203800007400d40f40c0c0301c02404211804005041c0301510540010261580e9401c01644078040300c005101820000c00e01d441144d90500300141d8509030170f05900040c00382a80a5540540b030001d851540d0b48641d1110010341108581c0f41c186200c01010070390719805103d1540d030003200700840a00c040e0710003c00600096000c1e5442c0e15056070210f080301508411900001c44090302e035401e02890b410100300c0100900403110724010545082010413810380c180341c00c050016034a8580d00d03031550740288560381c081d09003d00b98a94404110119901800141c42400d071074000c031100000b41180300c0d03c6a075009010b0400a0194a90440f00b0700d000b44c444d401d25030103902001c000010301c5102510007082442c0c420303944e009560a0030040500710000103801d09503490303440c0c001c0009182d0b00c0440007007902d0385030502100d85102e841c081a50035000c24001020741c0301e403001105c00d102001941034100c807000c1d9103030241103807 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 880461933 1250 880460683 880460701
    0x308090105180a0201050306060d020c033415090818120c010e09041407121103070b04170109050a08031006050c03030412020f011e0b0118050409031e02060f 69
    0x10b0b40e02100d01c050f000001690015881980216042000108540e091002c510395a104a03840751010700c1c015070000401c2c07a2007902d0130300e00498590303014028080703001c148400f81c030028002060050088500c115032851703640c0c40c0c2c1d2000c0c844035040404162030345051480c0a0500034070840c014481e03509240040450000040c1e9480004810394504211215460611054135800b900803035000322045440b03001100301b009154000d18000032260035404c001d040c8005856500f41680d402904039240a200003901042101c003251812250074100c1903031035084600406400314010300c5409015501000d200d8004086c500815021503280ca81556640d4180e45510462807225180c0d0414800200400c01c403407040031040c0c1190040e00d420b90003148003242120b0350309141100c160108109080e4104040c407803070300b411000b030812510b651001e10380140d4400e0345200d0a841952580060f504040c4a95483c101410550a200ca510401250080d4031940f0440303103010307a10381c00c1e0001451070b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 880463183 1250 880461933 880461961
    0x1e03031e060a03020d082101030c090c080c090424050405090604030c120e1804030e03070503070306020c330a0b1809070f0b03090c041b080a14040308090105 69
    0x70707100030411008503280d5428030105011030241542c003031000f405140d050606417844540c4000078605004034a41c15440c1c1103809881c2600410561803400da0103c41c43c54101900315040b119900e038864403070207014002405400701811020100000400b1400032486400c0764074107803103045400f4020b6607035104141d950765804580140004407038540e40c901045032440c001500086d1480d159001f100034502191080e918240815035005000b0200808d0692085207040840c8080340600f1007a45000d000942d141c150780030140c81e0b1a800248890310000070441c010320445040600c04940f6941031504406c004020003102c440c1d1041400214441a2446a1064000c00801000c16042421a8106419802080c2603514458024041001d400954001c1c0042010044071030340c0380780c0b440d0000e08011210401500032418000500d1a00c01d07030b94150700d6241694038101c407641c0c0c1d60408180180114103000c800104503807080c0401e156101c10b080c1c1c49100810001d000035200d036032018800d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 880464433 1250 880463183 880463191
    0x1302090402150c07091b09060c02040605060a0507060f1b08101a041409011a071401180203070506130303080721050402040c0c05120d0b03030424030908040603020c1e03031e 76
    0x100c43c0711f418000e25019412076209980050b1001600782e031210045036280e400b007469140840c6012a1680c00c014403030090704288148048140000c0340c2c0005868086013031242050b00307220301c01c00010030800c184d2060341c00420322005c0111120000e03c15a21140e482405010b00071450740c0e00100b03280c200021428100c44031030311407851351640180c00c40c0d09908240001c9828044401c034000c4403d100b40500b8100848814072401c1c0f14900b8810545001c056034006401038506004d2a9030b4080c042070142c08580e0141001002c070b58507444100d4803290440b10100a900b14503108194684080d07105a00c681d100396800c0003940070b25401640e1f400030100340105264031407003003004031000d04070290103100d4440710701041c000f4030040040d066030051382081000c10070070074014400c40e290750080e804200c003505080110200f540c595110b50b100d00c0c0a410141034000800042c80d0404000342c6070076815101e051900460071228454503548169201d5056114494840030113005142e0a1406 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 880465683 1250 880464433 880464437
    0xc030d18200a05010e030c091810050103080d0c110307150c110a031101060f0e060a0b0a020c041a03030d0b011202040e16050f0304291302090402150c07091b 69
    0xb40e18649001101d210030102c0085401d801900b440010b03c0e140c080c6424020181d01c012016000039224966140c1310303403110403155071030816004101081c50380044820340014000040344244200c84d0680b506c24034425400c440c1d21000603c001407215891800b055010485400d11942d01c4601e01242e00d031850319031201031030b0001821000068010714403111000d04030400815079503039605421030114070a074030054860001800704241d92a14050820180890038102400c00b0718040c0000c0d03450700011004d50145950f00c0000c02c41d400410201c240c0c101d401001c4a5841038440e0341d007009880c400c2001400700b10601c08040842e025070003542c0549010324000c0d03c80e591942c4d90701d081424900c1e40041800010000c0c000f14041e41d0b002580b155000d42d0390b035150804103520488101c12000c42200000903010b0074010100034010a030305100c0d4040b00c040089032a90f00008807c2e001044c2e10f412100c20001ea07410000d072020900e0801c941c000303d010400300811110900e9031007040810f07000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 880466933 1250 880465683 880465699
    0x402010206071e03091506030c0905011d0f091207030c110f13050a11070302070617010b0d02071103061006020c030d020316080708070303090b090f120c030d1820 71
    0x40c5081c407951050b03650354040c190406000300c11b00c0d10741040780c0484e00f081e9034450412805001c000d49501031580107269031080d90544034429611002800e10140902d042c0e200b0142c0418410b510401071414400c11005289903a1101440c0150100c0300100e402c64821400c4c130540c110a2a1102d59101000f43c064084034a07054000c08040003040300504450110b80d030350f08000d400800ea0000390050354401d4004040103810300102400c031815000070035108003c903000511901c4a0402542d0500a4080d070158a60000745002071800d85081d105542503c10b881c104051014400255011180c59800b910000b0170142c003815200c80b8460100805039000304450390380b03848400941400c0a004949a600b40f603525030b1116150b601000c0141c000986a0b10400c082c404141d18240e000012a0010602c0b091031034102600c40c840c5030700a102c40c031400304c0c0c0c0500099042c8101c42148039030040800980c00e42805051018000e0304080e541c0d241090200703918100c0c1c0301c21400e21481d000300010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 880468183 1250 880466933 880466987
    0x806070302070c0f0807030b1b1c020d1b23030417160c1505120402010302180a1706100608010e0a27030e030312011701090803070305040201020607 65
    0x15001c0d512141c012258070701d210b10000342101c10b4408100150071500080d19100385542800e03690000040c0100305800c1d034050490003910010001c480c00c001c482c1440d0000711119002e5200280903100302403246504240d00c414040000d140c00c40400051600c2d00c0c982d007500c001c1807803131072a049900e41c0d054000400108011035508050800d01800c0300020514080c5007040c040142c15024400315102640030b101400501c01c50f0400300251034440c6442810b0800c9011440d40000c000780c0040e043c1a40091204500e0083c0c9503400f030a104c003d880e0445240d0f0711080e6180e65800c1c42c0503511607010362004103541240c1d5021050864072a50341d000c00603400c095025800c10800f405c040403043e9690201c10708500c132050120360250205041c3e504000c5039060140c02140e116454034401c4e041005007200c0c088000c40b10030b040da4246911013004151442c5440d00418804001070285070b004402c111038168540c004601c02c602c02c4c2e003500c403180c13501d610540f10220688a030411600e0382c55501 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 880469433 1250 880468183 880468187
    0xf0c0a0b090307170d180308070207060c02030a03080a0209060a022d0601060e1332090312041403070f03170403050301051018060906020f06060120010f11030603060709080607 77
    0x6000b0b0395890580029400c3c911031b48401d0030520700344088000c03c100d00308002c05107070140f008100070052814030f504c1e900340c6a40003d840310b85180b03004007408810800b00d00300e10000d6050311600030b00901500d50b56811320b00007a643d400115010510455031044458180200490100e6440355900043c900c907406c0100654035401d000b410590080565104290862201d0082c1d1034191aa1212814440d00c111502078200503114560b142154820b0103101c0711101c00404c581c02c1c03d03150040080c0940711071402c2010726114101c41101071201040c0a010b00010b00f1100046900c00d0700d0f010310860b0a00402c001054080320302802080341480104881e041c400c2c0b101703c00c519540707090b05203c2c0c44203420841d580380c0c41d0050701c00548448000d028494041081007140f66175000141014548800001c00b00c00000103c803020f501d40424060108109420041e144200c0c0e000910a0740104481c0c40c0300d64004540080c880d101d45800b01d00c0503400783c1c00c0502076800d800c0c00b8020030b42e40c060017 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 880470683 1250 880469433 880469437
    0x717010e07030b0a112b05040312110c0a03020d020f07031a040f0209010b0309010b0a121103030d060608060f06070c0e06060702040f020c01050f0702210f0c0a0b09030717 75
    0x160b401113515402000c1d5201039071801410340d6018051003548103d0043c06810516071070503048600f551509040c4000300f500908440611030ad50329011a805442503180149400303080c0710741c8080d2080380e031200205500481c00c40c42c00c0d501d41d400c5a0901c00041c44290f9200320318480a051051034501e0030740001c07042a50950312500440603125801b0141c0d000c200082001d81c40506064004018030808200038010704509410403038004083c1824800e95a5814048042c020040c03003010062208a031824400d503000c0c8015038030200001c40e9175001c00348c542042201c01512680441001d80c60501d4460280e4001c0780d00810410070941c00c04412100500c009408283d01c160f040c0401c0c0010b81d92401081c07a9001686805a11208011141c03400d4920190103500c1c9240c280003000340d4641d00040c016a005034080c20312820100024050045200f80c480a0b407060100240702d002d03443c00002c2c4002282c6c440c0101514656981c5011601e0340140080240520303401d04d4420842000000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 880471933 1250 880470683 880470691
    0xf0d0b01060315080a0f02130905030d09020f03060f16080415110d0f0f05010504091e0807060e0a0c08012918011706010504051905040c0b0301080717010e07030b 71
    0x260f00a40c036402c12074079180a0360021240a55240c04110443c200031024800313042032500d051046003040d9407850f449000f03944684441660700c031002c5043d50b5070070300710140030f4002800307032001c0741003040e180705c4031070012075075242c0702d44003044070280a51245500c04e1083ea04514078541030311030044440007903c0003117046000e5501c207004e074020600d4103100d401c404a121a10009280c0f00a11822040c2c0d00305903c45032240d4981140034011070b4140310500300c4203a12401c0c80740d04000c1b80c5080c840034002c40d08041d019500c2d0940001004000040b007000f0680aa401000240d03a14503a1034280c40140c81607043c0182003003900040d6040e040d00a43c81c00e40300800b1401c400305024900344002d8402da1011840c3c10240180030300508003442258050300054805000510348101d280b805920326085100d0300039519400203060200400c410310107803009455603a601c0d695400425a00d400d180103850302180840003030241c27000f051284441c1d040b000780140c16242e15540381c409008034010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 880473183 1250 880471933 880471961
    0x1312050f061611120c010f0b040b060415031e090213050114060d061505031006050a0804020609040914010f140f06060a090e070c1202030304171b0f0105060f0d0b010603 74
    0x701201c51042e014130301801420720704500008001410354801029900030600c4640203600d131034040041502d80c50201e40a6035000040f00c810101c0383c1d4411070041802d9501c001d400d510700d542c1c200c0541c03916003010304064000c40c0d14888000c2450740134011503000b8841c020101d907902408020904041014003420400c4403400545070ba641e00414806107141c00200b40001c01c0042089a12407007491810090165881c1c628100343c180e05c00a4130824020300068030490010400c0320343e55403203130884507a5685c80b5861500d4082c0d1284054041e042d010f010616003418910b80400000458030340c14425140006422031a071a040d083c01603641c0700c08008010041c9242c408944400c0251005c1d0007004260f54803d10400a4180148052411142c10086400030000e02000c1802c41000207001140d98901d50f0b80e40d180c84c12040f0030446074023104c4880c1c1c000c090048502c01410344c4501d01c20302d001d40e0001c95200c903090410000000b0f8203001040c8020390001400444c1c0300345d20030400c00c0541c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 880474433 1250 880473183 880473193
    0x8101a091b070c3008030105040513060f0b120c1f0302041d0f0c0406020606010e2202031807050607060c0e0a0e04060e010203070203041a1312050f061611 68
    0x781c41d40c110002d030300d400520340c502c00100c800004480c4082c15081c40c000d101e034034031160034817a83d90030103510040c8181d910460f16070001c0360040440c903400c5a0000c0c3d122030100000781d0020590000382201c030740303410b1041480100c40c0d4009000861000549800100507641e44fd114000c2d4494014035030900c030080641c24032020904085040c0e01c0980003541a11031100361602c4001d40041000041850b0a00042448100801034001403025084102420070f5458001007101141240c04800116400c14007200031581d1540784660003180240611060a442da01c40003034034641c0c0310031910501c0c1c0c01c54020006400820055800000346c0786030340c42d02c1c00340254501c00041d075000c4140c200d18078050111044c80b0800c2924440e44001c200c8160003507003145407242c0041e49a0080741304414800307042106403000e50700d124003200c14101e406c40325400c203251102203800ca40a005e101c01c0720a403080c09500768080c0c070700113955072142541c3d61802610041143c41100c8422103501d40790746511031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 880475683 1250 880474433 880474447
    0x21501170106230d080c0703030207170304060905060a121b140711060d06080604150b0405040309060f09260706020102040e130f05060a0c0216051f02030c030408101a091b 75
    0xc2c03203048000c49c083d80c0180040d6003414541000328444102d0785100394000c00081120503081400041203403406c4403d20b403513000ba09002d89403540070a603440003480c40c2402d15104090043c3c250f00070107102c3d03a16135054011254583d0070764811444041d000d8149840c60f00001d01d0001e0081000d2580c4400c085401607582001d01e00d00301e41500c0848110001c12161200b0010511500e00450f108880c1072080b810680c07406000d02d4580d009a100b0854200c082e4440c01c0d00810302ca00082210510405801d4101d008d04080c01c1404030b0700d0005070082d05c000040300c40c414000d44041e64400e91a0924644a10100c11800c5011080440b0f842101072080d40210b002404520f00c110001d0a001c234550300589002400e04070810015690300104603070601807601c0b800d807a02c4602c00a0340b82800750111030311042c0c0c6180514a842109440001790200d4041c0b40460340384182500400207000001c0509210b46e0030b403c0b07805c0700c40c0c2c0100040c800100b2074101c0c031814151007104041f00303e151940e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 880476933 1250 880475683 880475707
    0xf0f09020f184203060901050103050604140405150c043515010f06030e060f1317120c04060507121b2d0b010312021501170106230d08 59
    0x1044050151400c800003800c020309554150403c03646000c544909481e5160680c0080c801e06011f0040e141010790380c0001540355110780c0d024000880ca00c4232404600e28051411554a0203151950ba202c40800004101c00d1803000c003c1da070664030341c3c007100c82e0032042c010307115048801d42104803041e0034072264900c1d640010030300c03680d00f090b010006016401c0d8104503003e990402c0c07aa020714201440c05581042c02000403801d01e0b0801103400c01000c0a4542000644014041280290449146540904000f044017006000350118a10600d800740d48640b01c1c2822130040744254004540300300401400141411098a40700040e4100303403041200038408030000002d5010102e40d022480d600c00c0341c009481ca8104140044991003925140714144d503030200307070001840000c203001080c44c041110540240b01000001c1c940e6103a0003038540e510b980703c03445040b0311800280325500e410f8003c10610202c000281d903100002da580c5040d90410010301090354060b0009a545aa0500203504c0d509 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 880478183 1250 880476933 880476979
    0x30302040906060507052b110c18040b0a09030c02210304060306080c060a0e0618030a030e040b030c011d01030902120a0302070f030b011511070f0f09020f18 69
    0x925600c040e00c03001949089468084110750121284584c43e00c90101014287ca0040e2101100d10702212500359011000d1314018031010f00991000d0486008000060820303503c1d4800d9028229481f82625124082c90840e04a102d003c0e000440c0b8030142c0003d818130b14143e42030107800110080d00d00303540c0111903003117030015040000060f46a05003009403000804c180d4100740d408907079203441c1002001020b0f101c0100340b40307014019840441c2826100000c848850740316100902a035100a010785802020040110b55840c030480c0341107448411401c1c009000e500484c4107840e07100c0c0380080c0514280a005482000504041c2c0352003900005868402d0506001800c0b40018100c0ca6450329010341080120380210840c09091403081006c41c01412090741118001d051b01c1c899548001011124071030802086100c03031260040c00501c200c1007250810403110284120042103071101c803640d099224171103102d240c44200340b046c030030000c0d6143c3c40d11507141070003021140005440c0080e04448 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 880479433 1250 880478183 880478189
    0xc03090a14100f0b06030a0b0d06050a020304060c031a0913020a0f0e0115020d18030209100e090a02010905270a0f0c050c100c0302040b0c06090c0910030807030302040906 75
    0x750852280c0a04846240c0207100c03201291400a1004613000c101181241c00002d10303559550740c585910304604d443e860400a500343c1c101c01b043c48030307142107005c84000e54030550701100c0380361511604066880c8248078a19260036900030a081c03488070340d401c004156602070300e41e150ba02e110a40a0005a960762216002449075030020010f0b2450503803070488564050f0300620080c3e02d1036251546140c3e021a20070720390002c2e0b080142d0000c8030190a402c4004098000035007242c0700e03806212005618407002d10031101c8054a80080e03641da010001e803105100140240401d10842081c00b0303038030f0400ca28454400815001449682110240000d0000c0546184401c00e0b55a00443c601a9a50040765100d801342d0410302c0c03811108100c4079542d481c5841085600c550345080c211a11442034048900030103141c0c0b541916843c9003c2c905480752400c1e64000190b00c2481140300082c100f40c00924880d4040c0e508854250349142c66040095100c01c104804141d803c1001081031582c42c4504400703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 880480683 1250 880479433 880479473
    0xa080402120d02030313081303050102120606041202131b080a0b0109050607060c2d1b02210f0d030e0c150a2607181d0c03090a 56
    0x241054014003508403180c00100c1c01c603400c9502c001e1800368000040b682c2107071a4400e401080019402c102c03199000d4100740301080101e0820000a001054000c3e128800c074984156001c0e0700c60304c1c2009400c1c80707907104241c07142039403040da04054504502c48001d42502490007003078658200318100f801c0510400050049401c0300f09004070342040744518420450282004580c03030b410400028000c0c011514024030103038680700244d07251441085440801c80c0c0d4404505e800201e82e000c191080c2c012040315a00007541002000700d50903101d2032680341190043c00f840c2d01e0004000581c0c5184004e0207038545030b40300701c01149400c1d0008102146410200c1d40d00002c180a0340c8404905000c1c5013102140b182d8001e1032844016074014049410009103418540c101d0740020300b0950440840080c00d2480300164010001015040500304860000505031703003a690352202000d050742905410b04c0502d03051087d002a240e44003034402147c002d10810111007050403680e6514400e1440d080311140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 880481933 1250 880480683 880480697
    0x20601060e0d111810060302070f0b04110d080c0d03050610080603031c0506010e01020d020606010807090513022a0a1104020d0e2d150406110a180b040b071103030d020a 74
    0x3200785c0c00e54a48001525140c03806524240703140e210206030b0544140054114a03805d800b007020403600000003d540c400c09840d540c50b42c446400c00501681049049540c1801803180303100a4a101c0d10400344925002400b12004c0108032004448407a40140807030b8162004020080c500da620410001d044118000c01107000c3c81c0c80b400040c0580c1c415220a03040d5444080c031015825008a441d9034820002e1030014915613074590112188280342d400346821096986680c0c02285454006000070150039810300c450000c3c91403240a88420b5141401e0550400c080c1c80700090301c481c40e001070f840d000400150401d1a00d03261030084411040e01d80390720380d00c08181c0c4e47c518501414140c40e1048912803580c1814010118540c440360f03078001074602d074011000040c081105513884203042101c00d81071075445000d1880c0140c0700b003030040402c403421010784a001030030a000f0b004843c2070302d0846c2000383c20000c1581c0c600c00f080742201c800d02c0c5c0c10700013800260300c0303d025440501090341d42555004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 880483183 1250 880481933 880481941
    0xc03201e0d090609030f0b0415111902030f0403060b150a0c03140c1009050109060e07060816050f0c0f1009061103011a0a09051503040b07020601060e0d1118 69
    0x14101041c2c03644010f05100b044941003001c510070302d20000001d50000c0400c261542c440c60703d075030101401d81010044614000c0c43d20140000320340505011040550b807c1d0040e42a564160b0340da0145080c11904442c041006200046150300b004400450250429030004240c0c41d045003c0d0700500e40c050000340d4480d260101307050f482820b0010800c8100c00e10f91501000c500c0041c0c80d01c082c0003996114545a000050411000354402202d140d04440200100303001000900d40ba08030500c281c100156031303040841c0d142400c84110f88031142154413814035040c0c003d03075544001e4020038001186030180e00744440b07a00c0400c0c0311101e200d58601c100002c4100c0d41d03107490401c881d8001e031002c5e0b6503101030006005a258454003213101c40c01d550344540c3c440344110720445a201d501d8101503003001070b060607000e03030011140156010341d100320340350685079a034918100d0b40d849091240400140e107800090450b070500e003154103a03190240c4081e0040049a00c04141c502c1c880c244500320a858000400c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 880484433 1250 880483183 880483187
    0x503063912090114100b09010e0a0b04030c0801020c0709090813080c0102010f02071101182106050705130b1b0316051c021b0406031e120c03201e0d 65
    0x1004c5903c0c46460f0506402c8000a52954001d0004041c4001214a12a0f01805079100000002072045111035250f40115002da001480b044a09083c1d412012070140d0041c0261104680d44000500c03500f887c180800340036159a19064460300c5041141852a40e2186403030800b030000007000b001ca10004100081c00c41d9008504103610603c14414540000d03040c406003c40c8480900c0c0c010200580e01000c00b1072401554410080745180d24009d007002c03c0700303084a030074140c06003100300020b030b45414094403640f160184c00e1905080400f810301246403284080c0410040d0080340840f411110550180340d41d10406d280d0101c0140000c605081010801c00e129081c1c034203241d40c45000e059a8006903a840307514804070750006a8000c1e54034143c0359940690011604505014508404084540c529180401d001d560802d1b80d10701000450f8045c10902d0003030b0343e00d0395900014010002c40c0d1007003400b4400c82c0301558000c000340510442a08001c020140044601a100c0c0079203603600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 880485683 1250 880484433 880484441
    0x301050f04050616050d0e0f0a060b2d1509120a1b080d050304060b0d0b04020a1703251218061d06071406070e0a05030639120901 57
    0x1c0032484c2200385042007107079000041c2d8410180c120340214004e2070703a005c514100283c82009880501c00e018144040c0081a00540d00851040c0c42040c441015020b540d030a00e1085036055106078400f00c104103ca051030700300e2111650b8800707455800e01d00b45000003100070240407003260b01e541c044446072040c0000e036010701d607200506c00d058502c1c6601c1c1c010036948605a0b0b41401050000100004062003010f030072601c03005100916128020105103072001c01540143c4040c0d00403c0302c034001040a80d00c41c0c80c41014010351000450400b40d05070b2550021451502110280f4800019400d002507041252041400c1c03440d200c6d0800c1c54180c5601e004051990741c440c0041101200c855440c0301480764401e42e00c02c806a44069507041305051000c0c0b11110088031a109100703100c104554030340e2200c44240027803000c8840750400d9542c1c2c8209503482005495044010001c060201c1c8803082d03040f800503608020700701800a03e214008410582d802c03202a00d480580540200680715000b842 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 880486933 1250 880485683 880485691
    0x20a03020108091510031112190f0f060c080709051c020d02090a141e0115050c06070e0f0109050612040c0b0a020604060e01140402040c0311030103060b01030e030301030f0813050301050f040506 85
    0x18082c100b02000240c0c0c10380d0781c1c5040009c51454034011100e1424402100b40c0c10035545d03000012079a00320107a2030288001c0c010103541200180200000c524101c4c400c100810807171701c0081038058031603140d80e00c445da0068158800ca0b448114168030400503200d00c131195100d030049a100040030740c80001140c50010005055072880344c00100104d0789040d40032400ba043d51905600ca200c2d0240c110300c04c1c1d685208801521960b0b01c41c2c6810024095489255000d03151410380318640c1c0090100015103e0b131649005041c2d00000a200000070140c11b40206030740b141c0a04000941d256960404020f03d9100c2624080141c005d201000148201d60040401c3d03891084000c100a00444000e18085d00e00640001c1c4965180d03850001e40a1103030300b00808a90391090802d81da0350f5a0300d03141d00105204940d550100c3e0800d4800520290048103881c101c98201c0e181c0c0080e03014550726000d850b48456461406140910400b1880f51401d21410f44950303130819165100f4105030501c149000c8000b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 880488183 1250 880486933 880486939
    0xa031b0501110a0330050103050f0a21022b090b07050604030c02010509120303090d21021c020319050903271c031806080103020a030201080915100311 66
    0x654500b5240b1000564103452505890008818004081042e0031044220407980c0300c400980c0180e0011000e65014a040324400c500300c0b510007050208440d1522000c10001e0405414002c144401d03821201d9505030000035407050b40d5071440e040c480a05059021180041b81d00600005480440c0d00041d00300040d000500c003071407d142483d03a416650b1039000300300604004400014200b1640281c09450600d13400400c951404040b00101d550b407a0021103049119110303c2e010481040e029034900850300384071040c01d24001551200c1c007070195109140014410b804c07159031004010861018500076107000304030802a2004010b42c03403d90b80047c1c03801220750020070100c10000c42900d4000310359410500002e149240c640c0001c1c00d00500000e9000c09011604540d40800d581704180803c0202c020205c05191031b15514201c030076141c00d01009401c205074001c18009580603800b41f550003900300040324525104180d0600c0204415550301040610601041c01003044840f10000740190903 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 880489433 1250 880488183 880488197
    0x6080a0b100f030906020a0201091e1a0c0403051002030a0e15060103091707050d0f090b03040807061b11010b010e0a0519080d090e09030a022a0a031b0501 68
    0x4500080d0350810318a0510140b25205021140c1103001c4d8000fa26401c2c0c005e0000c6442e101c6a000190203000b101d20221807594102c28800110300300101d411107104d40080303098034040520701218503040b1020f041d8801c40c050510002000540801451520780004100944c507420315142131410384800d19030f03001d601d07000a03440714070710240352103136983c4080e0074a400f10301c1c0092410300380100402c10700c00d40314482c40000c010042c4040041c0c000c2c81c84146035582d13201e80c3d00b2a5003c0341c03014028011084a088104085004507800002a1203018050740c2c0010320680110100448503a841e440080400c03e4200307440303559135003031281c082503600c00c1c00c106c00c0e680012000101c14a4a601070240302e00c81404c10f20403034501180032140030744201300c111010b616100c0800390042e4903900c201e21640d00f501c40087c00202c408016594a9452038005195891a902200c1c0311254014600419040c40360041d2003140c1d2401c5482c001980030310801c400080c40140324644040140d045181400340d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 880490683 1250 880489433 880489451
    0x3010c020607030c0c080f041a0c100c1b050f010606090e01050607050106030506010e220f200a0f03050c03010501080d0f0207090908030a0e0c030a060506060708040e0106080a 77
    0x20901c290310984601e070000700d43c1451001a5810780540b0b001130800c0d000855402c011010310301c020404c0d5a03405080385000b081011081c5001c2c032030401c001c0c034141c11005444120611540101e450141542841820a520100b9442580300c000c50166080d900c565440342071080c1c01e110701409040f071441c10540702420400f0441d0148410701c19607020b80d4000490606210085d0702140c00346902a05542c02560358680c112070005007503030101d40c1600c6484451503022051740004814a45c443c4040210b0b02141d103480340380d613804a040d01545030140f14072000030f80e03a80b62010050311481094030011030860a105142220700d20106000ea898030340140840720000070030700015a1245003007000500901812411300ea9964000ca0801d4140145081045001e101841c4a441c407a041040b03181e40c2c0d07070304a40d0b80341050041e40f900741d04a201c000f408109560041c2e0b030701c124064a0145484420f40d81c001c01a8441d602501646000340014481194003140c000c0c3c01042c102024040002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 880491933 1250 880490683 880490687
    0x35030301050a0501050c1204062a0c0509041401020c0f071406071403040503100902040e0115140f0d030807020d0807050418090f0503041401180e0c0c010c0c0b0603010c 74
    0x4143c0142818010301081c8000c038405c00300702c0074241121100c907843c1c40f180d071054047c0c00040d0041010400d03148a501c114000ea410420700c4041035088050711039500c0c608014001a51000b40040d20341d1050440c480010a0090004041c1e40400380000c100e5201142c95550074000071341c0003004051075803140203c440d40c40206403540c968001030404503000c2180d019034554441c580c49541c0502507880c01a089402c02d51005003664001d4400748080c90040c5001c900b211406c0300c0b860340300301f00d2400c2440007003480c1a60740c29401010b441c50500007e03140014600f540c03110307000c5001550040030440f2043e03040c442041400304a0a242509003032100001d40300740038a0043c1240c0d000181c0400c802d21800da00403e4110390030209065606085050264032a84031340240b144484a20709041c4142d48641d51302034030075142071040044181810724140313451001908940d82080c042c0045082c07100f00b03111325110710305181c0310020409072900e4040180c900040a45100340d14240582c1c0b00c0b55 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 880493183 1250 880491933 880491949
    0x7090803040b12131a0412020607021e0705031504050c06120f100e190b030c060913110c07050f060c060a0b0a120311071418060a3503030105 62
    0x344a02c1d103000380d070303030b0b81c154106206a4441409002c1039818010703085c050b00c0e82c000325809140a40b88401a040c1c2c900c13401e995603032060b1013403001a4040264551004144081ca00c94100400140c5210700c0d61140001d01c0c1208041d1003031040400c9200b44401c00a003001089510941599250b05100d048040d40c02d40900c020240114005c0c1034000134114034150340328601410343c645014125007481890341c100310380e17541081910b040c940b007104501d5103000200d00b000c2d02001400945051084000d10858050000e15010300c40d40b00c42c094031460741150042e1424038410b000800d80c4511b054100680355501100720340c001c03601003000c1e514002000c150b00c2d5001c1c19210000c111148814081403080505900038004548003d29800030981c0c040d600d08100500e0b4001c481d100c1c0d450720f08141e0050058001e055111000e41e81c10b04c400c150190000d9400003000341503091090ba80c0c000c0040010462000703d41003054044114810300c1724134181c5425681c03c900460556040001084600c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 880494433 1250 880493183 880493197
    0x1b151d011b0e090a020d06031406040b311b0b12010f05060d051905090304061106010b071203091a0603011404080d020d021308010914030a0f030e010905070e07090803040b 75
    0x2131500000c4004000c0c000d600840020741d44082d290303011a1403174a03801d4a41005030303401c580240100740811042c0c0c003001d0313655511408401c0b6003218801d50f1440009019200001260b24901d2480880f0807841207083d44401021441542c82e036507101010700e000c55440580001000c00d0700b0041c00c0c416501c85405840a40c92440400103150304d5102d01c0401501d28014800b4861341080c08128083c5404406401202c00c16228100c0c8d05006100b040d440740400d000e02c45484000344403a5001c41c0c964103642ca809019400c0001d84c8881030303141c003508100501d4551a00b40c080b10305114407030800340f240c0180307010108800d000d0b600b401c0c2d4845a00b4400c0001c035075044d50300442d6104c2c6144031607040326089201c17440920301241d901e8510314081c0186003000c5c0d521508882d1040071030031001c0100e4181180035942c07000c01e001d0599082d001005105c940e65000c0d1342c7e42c007060300000d03c10009007003e0900480181014500030400070214801030b0051030745070300181310404c030f0b00f100030040c0c92203 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 880495683 1250 880494433 880494451
    0x3030a091506060e040e0318010c23060114011e03050606210a1b120c0905120c09060d0f0b360d1b151d011b0e09 50
    0x181454104000c03896010080407410038541540001d04a811081c60740d840081500c05200b107000c03180c1c40503180c1c0504500d28510901c4411403030a15032041c2444080c2c0791043c0d0403001503102e59082c9100c038004502014182c2c4d4000d50040c00600108000000f82d20801d10f02000c5464462542c4030881d03c0900e002024941c132480416282c0d13451009603030b00340389000c4d401205c140203034010594041040c1c509038107041c0f40407210a40312170b000d80030244921799622150985e20300008036400401c04080b030503040010300300000c40c3d20340c1c480d42120140310141c2c1c0289681c410038010002840009400d00d8454960741381c0a2002800040703541c01095007014000c040750f5103035000c05048154540071500c04141c038840403040c00c014543c250380c50303101d400c0c2159150703101101c080d600b900000310040203c04000144800090043e2501c144280502001041070f8503141815025412081007400d81c82c0d459005d106824610710107801d034418520b16103691006400c8003c02d0500d007014103c100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 880496933 1250 880495683 880495691
    0x3030f0f0b0f0108090705030d09090f0204030201080c07030c080c060a060b0a093b0106090506030f0406090609021e1804081608090907050d0b04110d0b031c020604210203030a 77
    0x500c03841030241c0310041c07001900740c0d88018027400c0000d20103c224014000041e1030103908a04007042c0740b00b80c0f000d50b64181c4440303003940c80e580d81031070854100d030f1022010400c1300200c000026941001610034490801c00421b00b0782450034042c0c003500c009030440941188180000c031070150707005142204503140742003615001c1c07503210705c010702d5060900203070180050320841c1068500c0301f02001a040396001d5440a4016440e0410840c09202c151045410703803c008000c1808214160300c0300045520070b9100003241a441c1c0d0200d004552180780002d500120383c84614128203202010504071040740342c00300050301d02036031a5280b601a100c2d0140b95240000401003c0000b020100c6105440040080c085450f080358010010740c001000c0f99082400c2c120406040d0400e406201c50300203208903118180240e1055000003440140103095140c403800c5001400c0000c0b030400da602c148550ba028007100d28140c2040c5241d0f80c4205054421016060b100444c040e6006c02987c2e084654844081 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 880498183 1250 880496933 880496941
    0x308090d23090d0231110702060a1704060209100c05032a1005190219080a140f01081911010f210c180803250803010303030f0f0b0f0108 60
    0x103480ca524440000f908000d1801203030707100c0c22134260071105610341d4540444174480d03100030607001d80b90843e0481c005124107204040051900002070060888949400c1000807941000c5076004003090300e06681d259400500c0c000d53303042885e096481d203116804c1800b200a16a52030703d40c1c034400c45a55151801c14994240309400c040a080164890240300715101c02d07000030700c0417008140503200300500341d075207052580950025009030b5803007945501074507480000ea02e0060f07603001c038020880140c00e9652056076044c201c504110900a2580e040901400c1d030411440c2c2c3c3c038100000101c03641c00c2c11a48040c5000502103181502c04802c00c0c0381000c400b415680c41658400c003a528403042c1e9146131204000300c5020b41d40030151074031065a0390062103003a503426890345207150096403600c1e042000343c481d001100343c8072070700c91141d00031460301406059100d085c2c40340c000303030000c40c0044d48540e06080f00c036040703024400f00300d00d005400704400ca13003210000c0c00440d901540241070040c40c038001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 880499433 1250 880498183 880498189
    0x1e0702010e060304060c0201051b181318060c230c011418070f080c0111030706090f061505090a0e0c040e030904050906010b0703050c03090d0308090d2309 68
    0x1e01d4003480701400c61900c03410507142a8002e000640c815000542c03070403001030003613100302c180d4864200300b100000b85001c4c0e2408405100345044041e140e042860720b034800342c940c0d400340308154a9046018440b1124403203460a6425101e10321000f4041180304600c12840603c1c403110101142d132100f87d22941c61540c1c90410b4054500d041202801c2da5864080000380700c1c4c3c5422140920340c1c2c002c20b48208075104d904000034401140200c5141c1d51042050601380d5025401d01e80b4001c0c5a042260305001d4241e580b18203944203000c040390700e0890740c110700040002c64010343c000030b40c2507501d035045203060401103515502c0050200301c405d40c98507103c200b504c0e0240700040c1d0b80100030380144001000c0100b469034075840312880310b00481c5000001843c1000220b50340307047e180c000001d1450826607440854054025a04c0c65602d0700040001c14010b94454110301c810501c00d8a0748015450004051824030310211420000d00c024806400341012080c0c4400c5500c401d10b050050700c03400c1d48004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 880500683 1250 880499433 880499447
    0x10903120c2106091806181511090a1e08010207170f0d050c0910050403171b0105190e0a05250e0f0a1d0309010c11040c030b0103111e070201 62
    0xb134203041c581341a03a81a003c0c00c203200b020031405000c0a100c80900b064160804400b2410040c0410906081144104180d50048460044440c00c110309012200e40000c0403041940e12040c800c80c0120203100600f203d4484950041000e00d0085091400c41c0e25206c0581d202c404800500b8800010411004444c9600f40d4008459a00c400c1000340b90040c8043c245500c8603825500c2041007110741f040c03841c8103100302d90075a0f51284462144441c0204104202d811002c1d000d0340720400b9100c4160b22100034859180300e207003800d1407109500340320300b07180b8111003800260f245507030420ac4070342d400700f20005500300854030401f0002c0d681c08000314204110581035046071b508c8196100901003616402034440c0d0041c154100b040000c82c8000d008002440c060380a040403a8000b44844505580650b402c0f00d40b80d0b01a107811041e0300c11030b40004d02101c3c8000500c40100c1c1c0d40c0c1d072040c1d03003950b4144111460031800c404110318282d410707a000d8680c2109030105000cbc184000804c03404591103059 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 880501933 1250 880500683 880500689
    0x21030f081905060d12120b120a080d02160515070c0818190815060a03030f080a1508060f0705030702121e280201061a1812010903120c2106 61
    0x2080c1c50038070305808002090000c201b94041c0c1c0e82c6003040383ca00741038034140341304900c41240b40340141450300303080c0e440141035044900b40c04402a070a2214480ca072481c20f840f0042c2a11510141c459640c0161440d030100001806980402541015100c0055070b0001156140840e640c0f12200c103003214000078542000d081d40c8682c00740160324002843c0717100017440c1c030b400ea0b80c2c80400c0790941e51242305000540c0344512018000818040790500702038010180740b5000202c04001043c410b0b400c400d16010301c80c103580002c61a907c14020801b07072401e1020000d410001900d003280c514207000100a41c1e60384003212101070000d0000701d40e21050003200c84030800503114507015403602d102c2c45482d0b003541e10710ba005813403141e080240d8010091044c4122400d0300c90400302c0210f444540c042901068100005c3d5202c0c5004030610010107a94003020354000303011020002c07800078002c0c134000f045a51000b039030700710060038901ea440420350000c0306920307458610850072512201a4912002404042d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 880503183 1250 880501933 880501943
    0x1309020a1a180414010b030a0b10111b0a170a05071202182206020c01060803030a140114100203160809010822060c020721030f081905060d 61
    0x801e512031640c50000140c0400d200080d0070003640c5440700d00788411340b4003d000418410a4510040c051610306e0b00287d40c2249900400089101c00306012507500c0c6079000c002d0000c07075440c1141d4a0001c108000000e0340390a000f0401c3c440303c00b036001290f200155130140402c0140700840450001c17100300007028040d500601100c5d0a40d079200c1c1540311405000390168084d43c4400300303008201c01c1401c0303141c0c05002800c031100a0038413804051010750f0307010361b01181d40316020018060016003d010306000752205502959070f904120013010308540750b031803041130b00d400b0718130041006000048a4020000c005c0e541582c24410840f401c034114131482c10b0981d090101c0c0b910304000d00c0401ea0240c0403600702078031401e026883d00c2c40c10800302c41c42c0042a590400d021035a06000510302d400500711154940116407034142c4074126010700200112280c1841e4503100c008070145a030059149400801c40e0401c0c0740d071400d01c422501529000c6880d07a0f0704040d2100c0100301c10782c17621212014016040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 880504433 1250 880503183 880503209
    0x180e060411010c0515090601060504140402030403031118010e15031b09030a0c03031205090309100909091109070503090d0c020d0803010909140f0304030b1e0c070c060c021309020a 79
    0x2451703038200c3c81001136845440611500002103065070099080328155608001c0d003210311070440c402c1202030350004000b01c08154490380c4840b80107118001406a5200c04403142e005400106c0c00186500002600c40b441030700c02100603000d46a4500c00c4a40021b8400221900801c3d020885480d6101300040b0350303054403c1002a2091140809115040e6403007603460090824004400500760b0341c041e07070312040341d82080162207802e242807091600c0000d280e00b48040e90340d90b41c400c404200c442c600408d613440c40f042984042c0518080790b05036444142414200c3c11070401a0426548290b0200010180300150181d203040d5a100b600075020203500c842a40c0d5a0342e103551080020707050004007201c500085250b10400841d0120781c044490751000015130400e0b245480d04407a1402c00340c0f0210300040c0c405d44600821104a04951140000900c2503541d01c07051328100e40d041d50303158828000c00c03948030f0302c0200583c0c038500310914000206101283c100c030540001110004140d001e60420394003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 880505683 1250 880504433 880504453
    0x40305070905100f0e13050d0e010215010e060d0f0609080a020c0a0b1c020f03100512060f011203030f05040b012117031305030a09180e060411010c05 66
    0x81100503618110024807158446120300b00c1040c003240030380c60480c0c03001c002c107100e6110008417055202d111862680b400c4601a19000c2c141030b40107007943c1c0040c0c40b50710344059a507010000241c8003410b001502c03607030790301d000f103540003001380039007031600c81c590901443d0b043c8941d00455055840e0000350810003d00e1501c0c100220b5441100018003500981003003804c10301e0200032481c100c4400c56102031800d0130407414040564003608448040c26030911000d9005900c0f1006940b0a407031010b04030349090b042c00d0821030f1208070194203403200d82c82032041003072003c400703070101e411541e100c21800320318801c91400760080d2600000c8400101d15204c100018407110b070070414100c801030b240450b1000011040e02124003a098009403000c3c49000b01e84c14034030540b40085511810107980c0d038070000382d42c4e41d1b03590641e4085a0801c0006044120500c100c00140120207082402000100401c503103090089440300380060020340020048010548507034010044a4402030784070040d582c039445 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 880506933 1250 880505683 880505693
    0x30105040e071d04110f03060f09012a02120307020a030c020418030e0a08010e06160207050307090221010302030c09281b0206040b04240c0e01181a16080403 69
    0xb038203c13010340301d181c06000b046855003059140318107200006405041d05540c0d4264803c03240c0b901600f400b40c84e641c0c0701c100e94200e00c2c0d050b400300f040c14440d140e00711083c201e030440203251249001440d0312201c020030610010580000d42d503940c207a49818402001c0005000003002010060880004201000e00c01020540d01c02c02c159130240084544036002078a5124403800c80e600c2c02d8030100340344e0240380418031001a0f5200a04907e03081c0c81110205601c0d4000309041c100642e00900410780c003c2074114030603c44804410010007082c1d0041c120750300d140c002a40d20444840024000d20340c00011545c4000302a0110940c00c51680c10a4910742c1c402420300000e112501ca05201495200ca404041a01c0440c03501d010b541c115840c5900c2d5102c40d1100204c3c40f100c1c110407540d85039440317250002a500340c040c40c1c0d407403185a2154080503c00d440050803050700c513990941031000900782400041d4009039068003109040020645600864103d000441404440541304910220700001040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 880508183 1250 880506933 880506989
    0xf05120406050a020f030307320705030d06090b2d030619142a040302090c07053d0b1305040c09020403020319061515180b030105040e07 60
    0xc55401c541045138503801716034480c00150366400000300f07030032101d0b509000300c032003504020307000c1c554a2101c1c8050109400c00562145500701c400703800101d0341d940e00104034030505c0d004106848040c07010303000502c0080c0070200d04e240100703080e01c611900c0d4041d41d0104c00c0c4005480c1001b85c1126000e003003424009010b01c0c80341c901d4080e0181802c02c0c0040b18615614180e02400f48401c084402e01c20750342240400c1203030702c5448403040000340000005603407100c4005008000a1964545d07404450405038100180341003180c00c1c6990060041c261071003200c0244a0400c0500104255550354080401c05000cc503c5c0895000c6944c08580c90100203681c41790340501d10404280315810340d01c100141c00d80c01144000703540750304200401c1d441c030100580c100c1c604c00d02c1110000382070f2140c101c056140c20043d0300508a070320308512198556a4000801c0118010750981904140e454407504885500c01400b40c0c900581e151031a50155450070048980505000030007880c0c0c0d003100c00500c5582c5c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 880509433 1250 880508183 880508197
    0x6020c150c01093e04180f080310211e050a0503033309062106010305060c090f0f011e020c101106040b18010207050f010c0e0d0f0512040605 62
    0x10381d40c0241d000d4402c00808a00342641010104215000600704c020400101040c01c2e005c24043d00311a4600c0c0001d483d1070300ba24181c1e12928031503071031707041640701084005400d40003d100b00104000140014094100f240700700e0754006944203000d1f11900080409803086a00142240305098490040001c003001540c806c0c80040c1c5241c1c454040341408010000e080100041e03290008446c5425a09280c8070780703584800040c00c80711050348808400540440c4d030300e075401d4081d04107800500c04c0010070b0014a8000c0740c400ca6407806c1100d030b03e002610440960704210720860641c911481e440c0d008840c0c550740e500704911040c4104000310000b946680f84000d80c02e01c00c508107014005900d00412501014154050051030280d517550f40d2070585902c007030500b4041c51948000500c20810900003004c1c00f92086024181141e50340c2c102d1401d41c0d410084800600c05a0b0250b2002a180d00c807100c0180798111150f0019031401e41480c81c24185400c49012034000001000314005403c00020310302 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 880510683 1250 880509433 880509473
    0x61e09030709140907060909051e0717060a14090912070f060506030313030b09120d15050f0603040b07030f020a0801080d1119030909151e06020c150c0109 68
    0x1541e03a513070480548840950140c0d0011915080090105c8449a800103a0104d130308035401100420078442492901002ca45010002d010400810903502c40401480d4003e24150744c014405420948200c1c2415040070760a03001c1c0c4003c4000804a44080217812019040290129a2210341e4101980000d560301000d07101a421300000c1102800c1c004121140c1a501e400c01d20341150a6540305509000040c0140b1030a20072521005101c0c0b0035240100350054001c03c0000d8001600c03485440f83e050300f54403191040324641414503c54a030303c0126540268810700e10396036036481d1102600145003407142c81c0780c640d2010031500b20148d000044241650780901c1140d5424003440400c40f0400c0086001c80700da07800121250040b80c1020850f00012440b90401d21401e030f48400781c1c04225500d00b000484402442441044620300b146090665421139918410f606410720002a640c0d004100b80540038018052440c118659038409888020301daa00007805031317071040d0034407583c584803041c02050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 880511933 1250 880510683 880510721
    0x3031803040e011205210904020a2f07090b100f12050c0a1106190c1211090a05010207031e140d0804060e0703022202041706071706061e09030709 64
    0x1c08002642407811b10b031000c03040041c0c902020a0300340006074104091440c1445641100c00c00d03244d50402c0c444010142d00760a01a50818041b040361070164980c0c01000600d1a103081c1d000161604c0440306400c43d954140303a442c2401d079200842e946c2e4011300c03050350081e28002c18070404001003c02400103035260703583c0c000c0d20b503c1c8415407a11483c085c2c80003491140c0002c0d03404c2e043c0310360743c0050310514180e007002d41d40031b4201c80082003502c02990f90b01510410000b8030014620300030501c200940b1081c0b004010741e03801d56981c82081c405010b41c1480c840600d8501c6810460b080e0300c058010200101030380d0300e411285001520a02e13081c2c6003211036034241500380d010b50a0002e030100489030010112803107090004410007050006460003c0c2e210b40800012a4008500c0c030b0141c42c0202ca007004021a1401a42c014084905030411140d004040010b00c0403544e62481070f583e40e07a1008101c1880d202480d030f0f1409030b5100e40d0501940501945d540016181c0083d80010a20900180055 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 880513183 1250 880511933 880511953
    0x30c0c0d09050918011b05040801061e03110a1503020c070b03090706050708071b0e0a0203071d0d060c0f1202120f191d0f0f03031803040e011205 64
    0x760304069640900c5411040a03800075050001002010108401100000994003003900c0b01c11041c0002c50400c00100b000020200012117007441010020881c0144444c8103030401e0801d07000742c0040c0e03c030240480d000c425030400c040e030b80d10160b20300818214007a400100c174400c4024020390091801210680a103aa00045220060003124030500e280030240408500303192090700c103508044001e0340c0c0f44e5001d01810001a9840e0b4461a007007074404c090501140c94103519102c0d021008100c0d0403154018000d0002280d04210600c0719502d000792040341078480c99020450302c01c80080040c0560342000030781c03616660894902e10403400113039181c01207124850b6051050748142070b91200b003200c40500103801100d1210441c2e4204924100b0702e4040943d010380481940c41c16074120000b082107518020202c00108558802e190041d800b030f02000200254a58030b078040108001c0c500e003101d1200b00000c40040c0200c60180c5600d11460f40d0b15615040040c180c1000d40c0811034003071040c03200310 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 880514433 1250 880513183 880513187
    0x300a120f091a07030c17040f080a0b0105010807360f05030c150f041d061002060103140109080d09020f03030304080a0e06090303030f0f1b07060e030c03030c0c0d 71
    0x4106440c0e450000c0c0c1462800c40302c0301c40040d0b0144034181c0c100483c0709034040001c0c684001000d100c00f68480d00a84aa05100500314015501d80c0079982a5204204100008030740b14079607070440e1400d08000009685003801680c1812814103c03250b450030f44143ea07041085410b54188802641e41c0080c29101c1c2c0f19900a01400200d000d440e0b03150b0f112000400d0103246c00722400503024a5480400c5c14140038401c5104990010b810000415100b03c0d4081103840800c210380703074084000c4508400d524481c0348003035160b443c1030001070090407200c2c90380c455050b403d4101e80c0d40181c0c0404c40c00d03950341440301030310000e002c150422445451006800890303441e00005030317405a60044205841c1c56889101645e03c2003407144900e0304140140070f068095901400503500c2545108640042031400f0754412100e01e10082c0303102840c140361006031f5183d1002409070b5220b80d920500c0094407034002c00a503491401680400d100c944000409c110040c1c1c15140500840031004044481d00c03001d40c202 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 880515683 1250 880514433 880514447
    0x903110c0d060b0118030819080112020f0319230f031605010b0a080a0c290d0b0301090309031502034c0e06040b300a120f 54
    0x300c194400840001880071034001c0d4414500c2c440c05061804200c003d1504803d09403400d640f06941c851000308802103881c1490392840769032032030303882c003008107605292540050000520340607010307001d000e42209054808110103c0c0c00800d405d03136042d904046242554100e26140d61802101100c0310245104110003c0d4083d28501c40710041c40c01d040585002c021860321525081da034641d01c0e50144012900d4040b5000c0c00391207590b018200c00c50082c20413603036055240c0e12050041d5030040d2034404181d0202c0040c10040030b160002c664030381c00d038401d1201905130342a81c81e51552034070080c2010140c0103481441181e01c500c890161501c01c800036101240012503186c05200382140c010000118035401d2155600d6428040c0c03d201441c000c0c050081c3d66407001c1e10f41c000040f4200901800d4201070b040c1d035001e1411542400700d483d6203c007041c41443c61110300784560b041072802c00350b09150b528040b2600314065040f80d68050290611003017030110b40300711001240500a98070f0b40035110b201 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 880516933 1250 880515683 880515703
    0x40b060928120303020306090709030302061605120702031e070b010b07020619110c030601150513080a031d1002070e1e1e1f033003090311 61
    0x3050214440d05002041c00d4009401822000ca1100004034001c002906a29841070007a540142c0301c3c0342440c1030250745007000e4803210a04c4005842040001d600042c100d074455400405840d04640500d400d41d42c501640c5485a08005503500300720341c95034004050514400001004c00000d0000040c50415200301c89010780030903e0301c0014001c1216140c000c00880c0d01c05800e4a14299a802c0300d840b6042051880c8800a0700028056080340d100f01b1550030341490850240c1115458040b40e0b0080c0f400300200801070000128081c0c403c280c0450541004005035403c3d506076510740d2074018030f207001045001c8429403e080d0000707034130704105003410401d80745a002008018103241c00d0100800000300a5202e07a004a0040c0024242040c51103000e400c14060700309441200119032044440000c02071031290102428040318065003180c0001141d0701b1511300b4034182c0d1110841c0501c1e050510300a022140c21a220b84007465140d40b01030b42150103070740c13203840b80807202c05d0345500c40c05400703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 880518183 1250 880516933 880516939
    0x406050604150c02010507150506010e0406060e0d020a1701060e0a2306030c0d03020f010f0b03030a0e0402070204021b0c06191206121514070c03120b04050114040b0609 74
    0xc0d0440c48032900600f810704889005042c00c509196031542c80d20840c0e11034021480b500c5884409000555801036440364241c4411a0140480c9041030301c0280400e040d03110f110300c02c0340d44004250035074640b2040603019108800e0403030150100303800703d0360181c005441040c0043d00071000003408542e883c883ca019503089050f0b800702948004540340c000007000350034036505000d0f075031a1075200c1c0d580c4044581824843e03000792034000300c906d104070700b101c900540d062292820b02055420640d00801100c4004100342072a0070001031580c0490028016510700039000f80c80081c1b944442d112303074501c0d040d6070008881140c1095210605004003401004241c28200143d18088507410b03028800403680a103415800017011652031204442001440000b99806900742981d19080c80d030a0040d4101c0c01e40d07801d0507400c00e0170507580081018195020140c02c203c504584450a0720b41178000c6003201c00020800d2086503115140070402e060032400e003034411071401020300854180364041d211041c00007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 880519433 1250 880518183 880518209
    0xc0702010903020609012c0f0d050d0c030306090f0b0415050105030109020702040b0603010617070206070503040201110c040f0f0b090f040210050f0c0109141c111204140406050604 79
    0x103a090000c1034201d0b9045c1414080701c050810409206400c070345102c81d82001c00310350981900340c00e1202803038030301d030b00c090080000d042540f0104900040c80b08143d0401c1c906421801c00c2d60904a0092080381c00590100341480707007003a5040400c1d004201422004c0301c041020b04a400c0c14a40189100d200e17250105005000400859145901503e1802d0010300041f80348403284d40000e203958026001300700414614800248964845d43c1d4560740044280000d002c18100040050204c1c00024402810040b07031070105414520f060090385000c1802810900c0310003503c4c4a104043e25003100561241c51810700491050720b446d80002d03015070072040b541d00e000c0c5c80700e40a000358549060151400c1c02010000c1014408000004000440c242c4000050750300b0189040c4444020050340141e81d980000c10414004100380303503070007141e0054106259403000040303116090568203000300c424078001040001c0c032807501401c4251045000c9404004042e240c60402c241d90250b401010800790b030b5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 880520683 1250 880519433 880519439
    0x1180504210201150b0406180f053006090d0f0e042d020c06010e01180504030908122101030807060b220903351504140f0c07020109 58
    0x4078850304001d18101d44000f0407061902d2480342200720083e442095101c400240402007a54821035002ca41b075441c61074080400c0c0340602060b00d280311400b50510490906191003004d04c81510901c1740103944000243c0020070350f6003055100c200131a21805240a5620203034041407007081d0001600340280c64a0190300c0300c11040c44014507001511071100915102d81c8541d00e45441401c00680b4100e00e80940d60340829400141000c4060384104012141e000052203001c0302c00c019070009214540000469541394181111120640e40c001e078030034043c4a840e1540b03050304000622522a1100d02102c00b00c240300c0840032501c02c01d01c0007038480241440580e000880c1034005038018080200f88031078881070032200c055090f05454080700c001c1c0d60703503088d001010380118140d40e8403080e845001c900349070031102c1c2000d09000311200700c070a00542000a24100c05001d561101d0002c05081009001281403003044401400d9825840181c0004006080d42c580d02c0111004a07070306a51382103006103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 880521933 1250 880520683 880520723
    0x201030f0c142d070302010f02071106160803011805090f070303201009032705210f0109140303040c0b0313020d240e0303041217040b01180504 63
    0x10a88112200c44400d1094484020b282003d41014584000f41941c0b06030a1402030b08403074131020504405030050056401040c00200382010540041e00c1d080d039200001d0300400d418040d40328005141a60100000c9540c1c0c03601c1e00c050700e4941e031010b010000b603211034140303a075a801741c404000d1f0190b000f94401c4c230002e4403800c00d50320001c180e0a0b000c0c0c00640c030049100d0502030803200034400103656891450034568804c01e0704081d003205010081000005030310184000c007042c0140c078000c0752040301140c8003c43d01c60044624410690940b28155405980b860281c42145802d40d4921000850445910703008001c5901859000314010001d41ca480c000c0100c0307420082140c41180001300b20840580c859070240c0e07880521a0585010381321a040c00b0b044042542c005240e00603150070420b80500b0800011240c0141d000003030050f40009809040b140c10003080c07003980104c0f07500000c0c00100690910b032507050f64083e000e412120b514441e243d504442048502620703851284031004071400d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 880523183 1250 880521933 880521937
    0xe070e042d1530050c040528020a120203040c05031c0f1b050f01090b0705040605090904080f0708040e0c0a171008120306030c0a030c09020d1b03090201030f0c14 71
    0x40b100100c4510b0b00b00c488a007032804800440303c00d0714140c0140d0081c0300700f46040d01c61180e1104081c0e030001e00e8400e040c4500d005482c000c084040c070f000d0b0f0008510715042c0c040c0c2d9181e00107403840281555689130516017014502202d1080340e00a10030048a40407201d801d06886810704142e603101200102c004070704546100954110b402d1101c030140003100072030f4042c05203039114030350340300041100390844c0380030044900c1c002c01000c1001014001413242607800011141c002e501241c004c01d031904c580c2441c0d8030b103205035145000c40e40000102d00040001c04400b0304205c48448100001c11303690641207c3c50b41c8555000400042e89842070030070701d601c2a80d20f42d50421591b00c401c034407298586070b4141c6800205200e2580180020040045030b280400c504080c0400a90307001c201503240d0340e20340040081c1c1c1d000d440015500414031211500781603119030f00c0091214504d200c0c11441c80f1025000f41440320341640000c1c28140e24001d00b5551340200c01d0001d1300c03643c03051114a41601030402907 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 880524433 1250 880523183 880523219
    0x10806041707080a0e0108010e061c0510180506090102040f03060c140f0702040b0d02031c0e10080609060d080a0c080c0d02010606090608040c0e070e042d15 69
    0x400c09002d018049103040f0054041034060381c40d2081d2000c0b0f1000090101c01e0160312480900410b0740402c655622260b40c0400e21500d18042c41e108076203140713072240c20088464100c0d10014901035100000c0e110004101031482c2c00340c0d003919940d8a4100e8032509030f100746d01948a941c00c412000f040094142da0001038100d000d403610519031900c0c22060091075000c4803802541400c08240d00095141904c1480c249150449000c0100c04090780400d41328203407008078000302e107001c404158450b40980c50705050400000c3c04142040314100c4054001201030f900c09010750342580010f416414840d084e10052038010908904054400c0400c588a00802004658001c0c040c00402808042001402e030408460740010611604141d0010004040365001400300b00981e0b06220100b1007203a01c4030117031156081240a260744900e005e5450100a1440302e0300940f03011781d1021081c03940c0501800030800042c002030110201d01c40c81c810343c1c1c1950300e48142d010800c1010000c4603d660386e58504 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 880525683 1250 880524433 880524473
    0x6040201110d09181e02030105030f0106051f11031c0c1d090603240a0b011e032a02060702120a17250e03010507110a03180b0f1803010501080604 64
    0x1112042d005d205c21540f030000d608400d51600880140414501485420700300c258100003000001d103014000b80300c86640b8065400b2060101502c030302168800d0551881d981c0307054080b6580c03004401d500b211149206252051140c0c0b5010510390228402c4560114810035412001f18800c1800104141e5003c0075152941c14882c0c0007103482c03401c12100c9240021160084082800d01e840c080c940251825071450354108500750060105000700b0280c507824440d410f2400103501c241a034540c81032141d80005501c0c66501c10181d4010082d800282c007032080b0b00d1542034441c58904602c00c0c030700e140100d412500c0881c901e0400003080c3c00f9110b90296010300340c1c01810343e228221128060040b0880095400010f0464003d80094142401000c1d0400c42924003000800c0c1e0004200b45c039450320300c00080402c04920000222a184c4600707100c09448211459aa143d8440d00d80143c00d512800a080030300b84001281680c0b49010301c9941c0c1212038240250145550715607a21000f0404c85011480c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 880526933 1250 880525683 880525691
    0x909010608040327090c030e0f0304030b0a0f0b15090a1e0e060607060c0c1e020d020112091b08060f0405120c0709052809081602040b1206040201110d0918 68
    0x50220001d0091a020b031b54207450020758080f41104e60341c00d10002e40940042a4400c010030800100420b1020381c0c040e646040002e10298405100c10252160340601d41d840042d10b1b00c00340e40031001b82c008110200b030445250340005e0351404401e4000500c1b101840c00044035810410490704007140582d4001001400903207080350940c4d4410885540c40c00310030000e407540544d58200240d0f00840714101e0040e4a40403a0240e2030360000e0760b05401103000a0404c00c14541c1d07028a40c1e001d4001c8202c3c5030380080e03400c4400140740c0e08189000c01600c2042103910511010920040050307003954040d54200014144413494001c0c01070b5180d0100f40c0070b04070741c03240c00760006a030000c500c1004e000d082104100040c1260104000c0079400f081c060000080f860510003c001828940881302009108003942600429a00008000b021238100c06500428104000c0d4101d5402203440c07481503200362181c4441c1c4816641c0c80e9502c2c0070000340c003004140810f07401e0010b4188040c08482041070140046 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 880528183 1250 880526933 880526939
    0x40b0c130f030c031403040b0403080a200f010b120304090902060d140610020c0307180209120c150307021f020f16150c05180f0a0b0909010608040327 66
    0x1003449001d070303006a404180c94042481003009200015a96281d83ca00941c2003604180411f0802e21071031000a040140014a6049d00b6029400c1c031040e40c10f52018107014401e415005680764003038800e80c0b03001546400390031044c501c0e01c00361000c3c1e6404014001c60a140c2003040340c00c02000764810030b07640404280903042014040d0b00503e00e92800d8507e09502c50300300141489072294a01c4044000c0d5002401942d54584000407034000302c070540000040074038605050440240f1030280d010b0b41000410f00004000f10700040c0c03481400310281c0b807070855070741180880f2070140000e032803020040e0040021221610303a5580808030500c1c60003070044c0b900c0651981000150b00a03c4801d4402003614407107802d0004000c1080001900c10ba004e121110480700d00030142c1c0b10b44100b0b0f40341c0c503110420030b51840c0c545041d25819424007500c0080200c0c0c8840207008190032401c1c6052286a5110001c5a45481001940d019540c5601c5030502c14240c581410b14104c81d061010540707030140c280c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 880529433 1250 880528183 880528199
    0x605070f0b09070b0a0e03060c0906030f060402040909050303040512040806010b0a03290307080d050a0804050f0a08120112020a06031e0606090609080c0f1e0d0317090105040b0c13 79
    0x10b00b10136503251101c1031390610607014123050900061445200c404184070407480303525645e040381e5010f410486008003603520400090024022031b0481040c862500c01d000d001c0000c000025070181d809401181c0000120000008161085028051064110400410006281c80c025140c40c280d2030034081644480315030700140300154178000b0f020141c440d1400280d10f06003032066401522007100a0302090140c40300c080c02034030035504484208080f04c40010144030b418004a5440c00b80803065482d2100709062120b2260030828a4400d025403003030001480320241c007000d0306240d0780681a2440d607860807130705070000c00c0c4100190b0071891481c00c900d42c00c480c41c0d1090401514007130b160300c40502e050160007044a4aa074000c0015680038411b82d0340c1942e21040d0300300c5e07880310403641d9100600390001c610b40c4c074684a0300d6468011408801e51010581c014000c42c2c02004440f01411442d5103140d00c0c903003654010780b0040c00d00354564002c00c0601c1d6000c0020000300341c3e5807581d9810150b440c440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 880530683 1250 880529433 880529437
    0x1a0d050c040f09150504030e100210050702150c12010302012604081803010905070506160506070c29072604060b0301150f05060a030b09090709060605070f0b09070b 72
    0x250182d250741e03051960304011480c0304030843c1d0f200c0c004041102c0e243c0359a001d0803283c0020510f078451a403a01039096289d2082024a1981d600c0600c113103e54201548069070f590b141d07281402079210b818001480c000700c2401910405100c074003560007564a542c0055075060750690740f4080e0725020400c006016031319200118011807040e42502c1c1d0b1041c0c0640600710b90b00d082007078a4401c1c1d04115040c0045800000c1e00b4094803411a8a41c0d41c0340380e1402e1320140c0100290f0020858026102003001050b0840c05400409000f640c941c4524911841c0080d0f000300e820041900c0e038084034008c5450a4412a06031503110580f1021102c501d064207040c500480044404413020764492000e50000d040a0040d8900301d200480d01b0701e001400d0842c0101c0348001c0d400380e1402600045030307007604640300c1c0c0c01820360001c000d8620b06041c01c0440480c0d403911100e002d240191410100000b4180d803103041104c801c42d130414501c56000c001591118031000740030300301d0761051140620100e110412140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 880531933 1250 880530683 880530701
    0x50d050705030c0f0a03112e0215070f080a0b03160302130506030a030f0504270c02030c030406030f06091806050603031e030a141003151a0d050c04 65
    0x401444803516020400d80342075240c4110600800340c1c40c22a15490b10f03240d0306182902d60186c44050300741d0000c0c000c10401c6104d01c45035803d80781c209000b05216940c40203e41d007425440d40c207071110b070810b40c0c8041035100400e44008000401c0c80c24409000b5100c2c5800940010303410b24041000c859090004e843c040e10f013070801c0010804001c08000314a0100000024110140c0c1c06011901d1708400081d101d00003000d000d81031100d45014034003810b00c901d007210b0142c07202040e990b4040d0105103420060401d010850211585080040040c003400001910100701d00da07070045140500f0b0070412005041c4409107400d549840d54401f18414015015640f4141c41014505008142c10300381032060303403400340c2001d00907003040100f40c58400111210788000782492100c1566a04c44c94010340003071203041c1c40c02c184800032030244400764840d100341c10308881c051940b0140a9034002071800072602c540c0340c1071291440d0030600034418100007030400c035000d024030309a030020503c1c0004034081e101262 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 880533183 1250 880531933 880531943
    0x30210050c0d0e0d020606010c030c0b18160e06241204021819111603080a0c0311091009090e100c02031e09060d020f0409060803030f041b050d 63
    0x4a45103072502d005114040c500050040244111075002c407020751035100240c20f460410483c00c5c4044185030280380e001040540c8107021132050711f0401c62034008100300408020050060b0103400b40c50310b2084a49500b510310090303000d24603413200d500300400341c200e91142c4216100007150340c005064400c0301400724012600b1a0400300d20b46071042001203c440e00c48003c401011000388441000780400745040e490b07200d940025041000740028485000d121800e0501d031190078144e904165014034a24020b22400e1000c1c40002d054220039404e440900700b10090505052042c010f540c03404500c884402041800c2c144403054541205605603000c01c004410300381d0100c1b0f6008490704a9226000c07100c8041d101440c00d140e441010070034284c042005103115408003107104e5429982380c03021a09260300e164021969442c1045402d07000d50803c2c482e11882600e81040010906004800c5030303c01c0300411414030742a0341c0e0f55035a07544080c00800000c440101080041001d4132a55611800c5a00076 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 880534433 1250 880533183 880533187
    0x20a0602031512060c09091003080d0c030e010618020a1e0824031015050a0f0f150503070f1b0302010207110102070f0905090307020901030c090c0c080412030210050c 73
    0x1100c02e00c407842004100003d81c1d03a10071020081c224441c0e2050300c0e01054119002041e07a164400c54809510f815000036000781e070002010500030901d0f5000d01c00d2980507860078880c0c20304403a0300da8201c40c954401e422519200f440803100c0c01c5015801854400303a50308148294400e00c21800c518030980d48152004901080c091140703240030b030300f2501001014014a01d80030000701d408261104640d0018089084e140c1c03401000c4030781c00412000c06890050445441c4035035807800d40703140542c2441952400180d000e03020480080e5102805010146a1201840e546404000f11103103104000c1d04401c0002e000103030080f021503e00c1e4441c0d01c03030082c1d0006d43c0790a010f041105103088030b00d003114199030003840e00300319640c40307004841f045a0240e030b4001001e55071060458218031607140020340c4500e4600c00802044445c00e0039130242c8803080380421208020680540d48152054800b0305105403d11041000c801100c942414591181c810355404981c41300032078081e22010740b5101c0c120500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 880535683 1250 880534433 880534471
    0x30c0a122105032e03150e0303090a03030f09050303130c030204090f1b0819110a030f050f0303040b06040e0109050d030c14162a060201290f0907020a060203 69
    0x1580c0040310700711480b518110761304000c10325030494506081c440140112000000f03600b44140d55808042c44110100a90350b592400448858032080100070071000705e4500403000c0d1f00492288034114035603600400a501e182c0fa51550030b00f002c1d010203000c880d400d9000e00c0100c0180c0f254004c10085038030550708041a5501c40c40e0081640025a10350f581000c43c4240411180800080303000814400031110608401e003030a110714a5452401202d811071007a110000800c480410103044190281c419611300b100103075010f64992001365005030042201380081072980c070305644a00341c059004400091146c14a54420303043c0288801c9442c0440d0755000744062076a00070301100c2c0a104004002407501c0c0d2603000703561030515980b10217001503441e1000045940c0e9a170340040080300031140410b4480c1c0d1b551b00300901a015091130b40c400c9025010b662400c10042d05034101c6407002c010110064007407002c0038052100d074028151400c51007800c040078040345241c80150300490710824003090b4240 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 880536933 1250 880535683 880535701
    0x211409150c0a260309100b0a1d07020607050a05030402220903110d170c0a09030c080d02070e06030c101206120b09060403081b13080615030c0a12210503 67
    0x245141407442115810020400017600200f504240001c0c0b0a000261000013240400c881c00003d411007009044202d00c4034142c0c05190105500c03403455542210011703915900b080f907041c024070401a0201e8070910106005107041d8110b022040c2c41c0218a43da000c0340d99650760107036010050b058000c070b15111065003024100f0f0216108168950614440c1080028035001c21410300a20118880300e004c500864a203100303401c440d00858106400c031402580781c0344016229410607a005002d40300351440021a01003418120740302d07500080141c412030480a040c0110140f0040080c41001448620341c2781c00445446200054120303007a01d442003841e18038050607840c5014050329441e9002c04104800294007400301584a0780310310f072040255504101552450198410182c90780800c0e00e0b010442c143d0000e403141c82400c40502002039000034030149519554007880403a084900382200b4801109840d2240880511442c98840d11480b1401c4214080000084801c00110b00000384080f8030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 880538183 1250 880536933 880536983
    0x1501090207030e011823090f100503070e0402010c1502040f0305010f1104051005090409080d0b1f050c03090a0e0603060a0605060d0f1404211409150c0a 67
    0x51420f0811560344684045405074035a0188120f646d00c40d45024411907030300040c0c52645411030050b2400c059400e10007140c0c01e00c040111444e0402c131b42c80d03a10000342c0d450001152001c413070080720074102c1500c1d550011a100c0c0003404040c0c80100e1038504d030a01c0107400344000c0008000c844001d988581c00d510f0400c0c01d45641e0b06c5108041410104011410052882140e00b215402c903104030410521207000d0310280100f901890b48140382901034410300c0916002003040880030303041004040c1c4c510b0100509000d040f44542d0500401501c1d260100c0c1c002c0005107c42203151040ba41000e00700720010350030500c16004075100381c1100041c0300d0141010011a80c100710882d07803d01002c4d003400046417460180c0041c0d03052039038440c0b404503c02080f6501074a000082d944142a03603181504020602403080103505e003500070030076035000140e0300c6500e161003200800c0f0041803418a0907001c101100d50407070b0342c86406082c20801282440010003a641040744141d1001a243e019050040240 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 880539433 1250 880538183 880538207
    0x30a05181c1d0913033b060c0d031d06090d03060501091d04020d02060324010f12051005090a0c0206010b0f0a120e10020301030b0702010c140c150109020703 69
    0x4421429003912a582d6040c4040340d00c00d03440b410003003810400d03040886910720803503c0003901d00c0c0111001e800c5003840c07500c050fa00c0c960000b55829060010007e2045603c04c00d4001c4426400146505900c0307842600181d445500618038030250030220316281342000c1060320520b805a0083c00710301e0110341c050144100a145c01d00703000d5281d52a0140c0002c55240d001d0984000303040c0b0100040031503551100f2020490b8000d0041c40e00c0b858900208980264800007012a84207203c2c0301149070b602c10700302100d00103280d43d07680c5142440355480201415010f4212a210321b0018000b041d5070f26480001441075102090100d42c841d891003002c1d06000d810f0300b04541c400d200300400302d407503452003040710300e00411868084450031503095800014002d030302101e51103008010448504103815000365043e24028854910b0039202e9034410390807502d050081c000410004180c0980b409201c901030080400392009941008000c0c44120ba10400249c01006103e580401d0042c14560701070010342207 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 880540683 1250 880539433 880539467
    0x1d0f0c100f091208040b0307170f0c0d050c07141608030a0f0f09080d170a15120f1a090c0a03080319020408070e04021503040305030a05181c 62
    0x4000340100000386800d44034003d414019820002c10000c02001c803085400900252480d16205c2c102a140100070308204000b41d42d10040340741c0402c0e0f0030b4001e02c0d1402e018820000e030307040c94444901c0d900c2024100080c030303c10607004240300020108004814908417521500c019045904a000d06015064010b40010b40700746c0c81409030140480d044444402d844210b400d202140076800c003022508244d003500510020301800c0c41c41600e2a420900001c1014a40340c5001ca0941d140e16922007291a41003241040e111580c1c3d042100701480c035600d2000301d020747c07480e50b60b0030402e458101d000021603110840c800c05140400c44607290a0000038221081103600b07440f464039540740c2551a010280540000324100100c41d80703d00603640c1203a00502c0a80280c40255a90708011000528119070980c09a528600d44e0a05050520102c0e44070f1035141d00d490741141c682d000060024071001308070510040b64100c2690000f0020080251890080505c2201140b03003818000c145030301b0b84030442c00e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 880541933 1250 880540683 880540697
    0xe0a0608090706110c040f0b100206070e03060907030201230309061909030c030e0105161101140c07090908091f0e01020a020312030402030106150305040c05010e0f041d0f0c10 77
    0x140d08102043c12008911700701d0b03001c00c001820180d80c200805500071155804400c802814081c2500424828031800c200d484145400d41203109060b01d9200844000140e43c100320028001903019508c3c50020500341004031100600b44110086130f64802d540c041c01552080041020201c4d410581d11030b01034080e01c0a02005925940c0507102d00b00e585002024400c0001920906902c500c0940307234406041c032403074420645c007414091080902500090700041d0358016280780d01c1c1500c0115030000718002c000342890361401c10690010111040c4c100c3d0131041c2009001d201d0390b14580d02c0000700024000a040c0d1081c0303450041c0c07140b0011004075042d900040d007a5805a41c01046440305600e404441310350380d9541d0320000740144906e4221442d403145e01d0451401ba90740c90f900003440b680c821140142c405071507030700545107030951040c00c0e5070141282c885601e25050540001c4607400080507010710302e501003a00242884240740c01a10301d5030000701044014a021050010b000d01c503410001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 880543183 1250 880541933 880541957
    0x120606060f170402131a090c1303241d06010501140909040213092004020f250b070c03090b03130b070c0506040b01090f110a030c0e0a0608090706 64
    0x1c0c04040c0426051035a00034030350b00150554540d8514020343c006001c0c41040144c12030209540005480408140501c010000081c4451140f0003105c207082c000054410000b03145a5a5018524903600031544090031298114051085405481288040b10166016420385d505429103401c5059008504200c0141c0046944240c018110740d0b003000290b0f040b4842d6900d9001003100700c00220080043c0307518125008050080103510000d445120604454ee40280b190402059028400d1154200401000350850000c4c0d040041c1008143c10109030382d44101c580c43e00e40320301604a40c00c402140426100341c0416030702c1103414000d081c101c4c02150550602e215101030401c91aa0002e00301e00c80d41d40480c51442c042d00582402a0340201214580e1404e0310304406540d400703104030000b031803c06010700304c4180d9601a01d5640c400b45071a2500b0710b130b252b210403805044410998014404110300e241406d8980401030302c00740520f603d07488078500703082001500d00510b41e40090f0402c100e504d404 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 880544433 1250 880543183 880543187
    0x10e0a02061b160b0426060601301509150605072a0e0a052419080a1a0907050f040b03031206010216061209060b030601120606060f 58
    0x24400704030745001000d0038030000c110b21510b0f00c681651400c40001c40d4140c000f41c02e14107000104195503043d240000703411106054068040104444415560018000500f955200e61001c1c6502c034a02039040c481c000d00c00c840c5640143c1e0081c00600003c0d15070280710325000e01e1114020081c144120104228000700c2c14103689035155006030000c000300010450140a04110001480608030b9030301c4d44282c5441500102d03420440c800c0701c9461210302e0001d081782405200b0319100c2e40344000c903900041182c9100a1910340a961039603406400394048454801c2d0101c0514003600020b00100340c1e0b24000d0030003040c03540f2140da07c041c2403012801000342e401c0c008a002411a2401e50394000d11910303c0000602034490001029018400071812440226480100600419003078003603520003440c01c461900407072054080c0030003007400118402c40031002d980c00032080f1030180c0c0c0006088001f6500203420b04001f07a02c40b010001004c031b42e100a000c00d5100710350041400341000440c0501c41a00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 880545683 1250 880544433 880544437
    0x80115021f090c060c1208010308090103240303080f0606070309091119020a03030509030405011413030f0309081c090b0a020a02270a090308040213090c03080408010e0a0206 76
    0x41c00000d6041c8101010840040d41206520b00c0d0300202c280c40340c940b548001000c66500860550f88503030707035020907060f060003401840c0c1a20707042060b451a0200c10001036003e40381c191034264013005142d02c0c2a446c1000e489589001e14800c1d914841c29080c8010744c1c500b112005000248564001c00000e00004e410250280072140700c2800420040c4808254101ca4080e0b1a015001ca0400402e17502c4210f50115441241510a071010001c60322140b444507035a0089000d640c0c080355548060840d0003000364081c11145c0910a40c466006807070396600c2810b0021110100c001c04d03800f400a10014400f484050070f040064040446441400c0e040280782111174842d1004580300019100d112030310a0005281c0d054001d007008000d0710341010040912030348000b00740340c0c0500c1980442c01030305e030f1030288101c11a01903513080e813a901c40c4d40800c11000d003009460740c1415515110140001c0842c3d40d4074000b90300510f1081e071030300e02e415506407c0d6034004143e05610f410003000c00c0c00507036403401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 880546933 1250 880545683 880545703
    0x70e15090a050316120c09050c12070207050913020a0305030d090308090102070b13080c010606020304140a0803030106030e0712050604120305040203211c091208220c0e130308011502 80
    0x1c0300e00d409003d080012041b034460b003146400300d044c039080210400000009102d0400b0317075861155155a031031000c98441c00c40c4e020b00e03a8040c80310f2010841c184015580c40c0c3c8020f000620f481e0502e552030b500c0c2882c1d940f1001f000300d07407a901c60191509151b04080d00c194420240700c000c0d1b1612000c0e50703c1c9058014014061000c140040c3c804009002061041e69400e261142c02000800c4d00c900000c0d540e41c001d40304640b18200112440441401c2000006084900010040d41141d081c482d060340070741081c000b403080d248205040000c1400d041a850321445004001a01081c00d141c1040120480c1d803124a00c141401c002c203000040c3c50020b40f410038401c1d40c041400114031030364061a1a4420041c1e141c0110100c80c2030382c0194640342d88045a064421800500030401521007503c41e80c07400c5405e402104101d1052007011142c105958a090f80301d501003000c401d0301c600140e140e83e0003e5507103000100400e03104008240e041807010740500810010305030520b104140003595448008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 880548183 1250 880546933 880546949
    0x3050a0303090f0206120f090d080f1e07050301030c12030507061d010c0e041b0504031101051606140109050c070212120c1c0e0a0509070e15090a050316 67
    0x800b482c82400040d240024145900400d069603800740150201d074040b81c151a0003144607000070106107070800006142d050741e0341680b505120340d0f40344070000b180c1d100001c0199500d118200e424051202104c000c0b244549019142c0780d443e035046060440d003402d5180c01030031038407200314100e40200e600402500c040030ba00500220f64209401c010840d2420300c0d8010350781c0781d802c00e8400030b115a0826070340d0080140940d0108003004074014030405602e19400c000d0003068040200344007042c03554200d042103600605000d840e10045049040e0b210302d811030306680349940e982c4401e41514400d030202c2c0c0100b041d042d05000d541420348030b4903020300c01d42c030340244618000702c0d018113140030034000310000c902d0000c07405443c0e485e03940b445034944015000040b405041d406a1150250140c0400441054041d20f400031190a01c1c003842040240070300300606000c1704501080706c0b0341c4d980d0b1143c5c1c041c1d400b00040a48a54801090040c10f80e07072030704943e1203908446d0346408038408080305401125411 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 880549433 1250 880548183 880548191
    0x9280f12110109080313030308130c0e0a1b0504030614091209030f070b22081002072307090f0203040b040f031e0203070c05031501260a0506090606060403050a0303 72
    0x90700040c0c078001c405900c01310507400f01040c244c0c44d4008140091007128002d07101c00030250303a0310114205900c20400014400e000e0203200f8003d0000c4a1005a444140c19100080003908402070100c000c1c00c0140200006000040500800640b0700034050742a2205240c1c2c6084e080c104811500d8182c8500d00522a5071702145050040c3d800b0071070342c8580c0d004801070398881c81e119800803146034000e01180c1d52411761140300204502030160b0726022541a1030207002c0f5501e407128100040d502000f000c3d55092507040200140d902ca09810352400c0b00c000006102c140e2510f03405100740d40000469103003281c0b0600801011400b000f5800f540554460225101450280780179a00f191140355035080d0200042c1c80b680701150008020541030340102c1c0841c0e1956641c0d020581d448ca4030210040b0020072100041020078180c805151041d4040c40c1ca09400d41c2c0103070300841c50304821a1040c1c80c2640264103016550400f40130780354202200f40c4e8402d140c24215120940da0b09046c0c84000c08055a07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 880550683 1250 880549433 880549463
    0x3031021020405101a0f03060108070c060c020a020a09021813140a0203100b0301050d0f02041d011b020109020d0b0c09120307032a02011409280f12 65
    0x80c00800350200d580c014410070140c1012010300d03c00d40043d0080400d1400090b208480c41c500c1042520115003044036003a1840c0d403005c00440d25080042d100b10144185821082e0004819002c4c03036541c40102c1d40148844280e90040080101455200307282c0d10703104009564072071040d098802d0b0442d0701a43d10304101c511441c0740000401016603100307442010030060060040d05ea400440c043c158110003981c00e03d0300c850540881d0700c42882500d82c0021001201c034002180c00c103690010900013031000598244000c03070855002500c01001250b07956a000c0e19103091001c3c022000d810310144020000c0104981c04034050302e40c2c5013000303040004030000103011800828201e610f400c0014010020b120a44000650760790010541240403031900681641100050b4603840400504215103c800040540065031040d1070500024441d03d020044e00342140c03a041944404800900c15148058075280954408402c0d176410221200c54aa40208000582042124602a008413000c009102 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 880551933 1250 880550683 880550729
    0x2b0b090703050d020d1101020405130e070e0108150a330909030f1211030112050a0501020c25030b0c030601020a0507140301141e0621160602030310 65
    0x203003550008201c0e10400c080241c550f0740c0410326012010703080d10f41800040300c1401c02802c2c0d0145028040e0852000700310f08000441e940c100742201c03070600c0180c0d91459280e2000d488009400d8101e80855031141026881d440400c0002c5640051503a200300304c84810707900a00243c3c0740b030001c0781488812080507503840f026440c4007600245802c001c10002c4444501c2c0c041c050410b42c00982c00880e04240c4080c0c0041514094032520440700c8402514503800d100315a0a030842d4682d0036607092140c0c02041c2c0024209100420301001e058004100c01207804008141803010304481c08240654014100002104001d02c550801c0030400c2141c1c9968803c00100e103001031311440a8180d1048640003d13041d44500e5800084100c20350083c04206c4081845415161046c1d814202c00c2040300042e4045140c004035007a040003008040d40880440c0c0c031040e03400d400502c00d22021981016603c501d074003a80109440062400f4000b035030440c5000b074042c003182025841442d0305c19840c003180303c4421b1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 880553183 1250 880551933 880551943
    0x718080a0602091912420e070e010f0b0a02030702010305220f0c05121504030212070b070201050717060f06130f05031b0d03050a0521062b0b09 63
    0x959038495072011203660700b1042d807040541082c00d46d486440c44150b0420a88072a9082e80d070805c00c0d14910385030300754107400388090a04008084440641e105c800c600c11007400e0101500900c81d103501c090055041948104040440d0f600c03180c103042d404c010340311440780c01100383c9007165024240080e041d03446000b51900c9901040f50540f1041203005020304114041d241079550900601c2c110800d80e071620140a01c44000c00c00400a580c07007007180a40c1c004d0440d500981c05803191040c0d550901d400d0030603205640005c04c00701e4080842d44100300f40e8980c240705859020384989411040719941c110460001d0b0800741c242801401740810010068550700c08030f85000007e007500c511a1a902d2032500c2c10303083c060055620034000e0170f2404d04115685c124040e84080001e0a02d55050181d54080d201613102c0d041c604203224040c4244400c008402c08400e5844828400105243c0341840401c44c649400c001c26185241112060540080c6503501c0200c1d8260710200c9142d1944a0705d080a10701 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 880554433 1250 880553183 880553209
    0x6030506012d08060f0f010b070611090307060504061d28080f0a06060503070303050316030b040207062711060a03020706020a03060f2313090506040b0718080a060209 73
    0x201400c844005600b100004104d40304400b040003e04c2c00703440b00c071903403248031a080c4641d000c558402e00c400008100d05034880d940d9503083c07d100341d140500750000b10f805d20040d680098045000401e04000040d008040c004c4514800303c0c0c4803e8a03403440001030f03060240410781c0307102201d0815203000340c08840c04480c4041d0652070300711049941000d003956556404602d089030160304110b00000d40d4100051010107596040d250700341959907880180b5100b0814141d5202015111300c4904d04d036803540d10080992034003e5030045621200b6002d40c118a200c19210b02d1109040c10300c00401040501030b900800710422221103030f490040c49001c030086d0140d140090a801d200143e8181255010352103138003140c03141c1c18100d12007995902c1d203d800c04d40c0c946507010140d2031030401d44108e250130101106010a9080c00185110344c1d0b40743c5ea494894100d4003115099074501c14841e01035003003048000290840c0740f008203003908040c9060b46aa880403070080601e900410b0001c1c2e241d0b240e00851481d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 880555683 1250 880554433 880554509
    0x161b0501020d11130b07050a03030504030c14030d0e0d0f031e0501080703050606010c0804090510080114060f0d0c03060b151810110a0b0a0e25090603050601 69
    0xb00e9000f0010584060f403080d8038900c444d030500040011420704071000d6401306900900900b000e1903084d2010741c0a490002d20031001c004c052401000003ca00c051414541d0b295240190b454815032403017082240d035881000019648001014104540d015012071000303989450003107485124401c1201000580d041100c0c1020f060a0010032040d6002030391104990042c000c403456070f11200700640f5941040200945076440801081c4010303103c9810054008001c42c8008041391750729140303107003152000d8454007056280d103401d1044d1450604070701c4040d4002191002c00900c056034403613902100d0781c4070040401e501d41d030024043e175540c034000d8511200107461040c3d943d60601102d000025012401d02d1103400c410303000b141e400d03114045000701035002100503c100c2c2f1341e0b6158600306101c020b04164515481d01e4503251041c50030700150148070758003070ba003140c0400500c1d10400803000c1900b1010700e81d071600c5030801c04980c00240c01c0741103030100402c5501c000141900c01501d800c1090004503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 880556933 1250 880555683 880555691
    0x402011419051903060f140d0816030807090b070323070b01150e061b011119020c04020a230d060f0914060a2309010b03040b161b0501020d 61
    0x565004801840325620a040f81854040c0408040d4120344140c0100c212034100c8440622003449004605102800024484100b140b80c50340c0c0c5e00b07035a0b480013049125031007075a582c80c4100f40d082841c2c42e400c030360641404002c00781801c4900106020b031003006010800e95600d0107001d03a405a81601091f00a0840b940e5540314500780541d00701428031864000b000030741c210502891084005c510a110010324052a10603030903015108007040b0f0314180c1d210b5580b0b50910314901d0004009005881c8251a40c0000e14880480a803d040c416038866002e2801040141034466015040c1034035201d52528440c401da124060f05076082c0140c01640c146c0914148001c500100c01240010859103c10f03824031000a50110450740010b09903103441d00200990303014014801c88098034114019a00007100700303402804001030642c8400e901000ba101d100201344814000c1c440c0b92964001c05108041811003a900b800030800c4154412030321084143c1840c800030000290100c8446803c1124144 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 880558183 1250 880556933 880556977
    0xb2b0b0c04060801090b150711090901051515071704090e1e01090b0c0d09020301020304140f0d0c03051b150117010b030a060908040807060f170f04020114 68
    0x9019a03006000b00d9020030202e40000036034000b14041c01000b244040c0c5256192410b0f003503910451f030000710b030442d03c581c604030414100d9168075031040d110f100145c1c00441c9504024110890b254050894030b4090004000d5210010840c7d80407200741039031002043c003201d00307440c1c250104c41c00703544c10100800d810038101d251841c00025244205500c4050350981040c60340b40300900b00d0320b0308840185408805000036a101c1e90f12000740c0303a840280e51001c28582d81c9940003d08903401100c04079a950501c02034440c526008012103203200d01e449004028045280e280541100e0350000c00504001c8001490144a80319070944095a6085000ca485022160f8040d854181c802d02030400319401403902040c4103403050040e24034412014000e443e12100588500c400344c0321113034080c1d414042c01c010005107140200304c0c1000501c51a56102000b81c01488010170581c651441071658031010014860004d90940700313142c216a090a00e080e03a022010814001030141c1c2100b01d403600030040500b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 880559433 1250 880558183 880558201
    0xb180310091e0b0a0b010e0a090915060b0324130c0206101a0c0309060f04031e0b01050f03010603140c0307090608071511030a0e04050a0b2b0b 63
    0x2090000e20820445020b81112404038405100000000e030150b4060b00c042034402213198072848030000180752641500c542240802d0f070440640c0e03c20b40141d41c0d1031480c1410700c1820701c00007002d42101ca80c14001503203061a8a1040e02015002c03d0030380403000b000120301d0b03240754407104046c000a44000c86074294081f202c001014984800005401804005456400e06135200c50a4684e60f40c10502c079040c0260340d0350081d420030039212440b0b1104003d91005aa182c1c00034008006589014035640c83c1945882d0200e801141911540250120b140742c0001c1c400c0560207055401c19251001081d40f4400001e01500700e0f503002034414980c401c900c019820007c100100080e609504070741e03400c1c1d07892000f00111035952003070380c0345500031440c1030010285100a241c0031052500e400311303c1c540d1010110303003542d015000103030104180b90113044090515000da19400811342104110452050000c41d003a50902003691003044084041040405215402243c0d84d58101442c000246818511 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 880560683 1250 880559433 880559441
    0x513140c0706051501020709110f2a0c13050c22051203090d030c0c2301140c06010e0903040305061f1a09100e0d031223010b180310 58
    0xb9500c141c10000050900000314510f50762400041e402440c4691804007900c1c002d05a092400b4a002420000c40c10500c24440281120080c0c102d090040303070303a00c40140703803000b050319183d0b0070190840700c403c0300d01e6558495150054002507002103030503503d41610014611401c183e0342c4240c0104400c03a50041903110004080c1d440949500d2200000502199a01d026640c0c460f9401603415020000103846800904180ca103d694521007054440104c00305a40c40c00000d000c1340c9054031070b00e03440e0f9030f171041c02e5010004007400d8141c40c0440f248441e03034840c507050040501189a00c0041201100100122402590000d003607428909000201c1124502800300b00400031000101c007148041488901c03c2240607444035885c82c04000c6400e00008842403110310080c8144d540454541c1e4030b0300351502000d130b48640d0755a100054007a480104035602c1c0e00000720341241182502d0307607100303d0f2040c1c1810740c0d80b8505120f03192081c2d9140c2106145009000315054040c9410f104001c01c01d41e00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 880561933 1250 880560683 880560697
    0x405041805010b0a0e060607051207030206100b071e0c1a09041d150a0f06030302100c02011a120c2205010b0304150e0a051f11030601090513140c 64
    0x4003e205941c1440100f0080000c140507403090708441030041010307464076034014031440f845032003651003684a102c00d079501500985c0701900560002010000c00002030030000000d40701d4515902e04100c0c07251104d02502c43c0440e002201c4400001d2003105000c014641e1000401e903040154295007031504850440e80c0154800742d0083d410241014449800c0314580c1e910742d8031100050000c0304d0121410302d440000030b0104010790b41d1324040c3e924105c032240122406107003e50001e000c58a4090f103002c0403150070000039021a45800c04040c408006100d2112840004444030300374000c0c01300765a41011006145554402c982480202e0810072018800400c05120703041081142c1c0c1e0b88410b2a80344c8800c030b4005040840c0c01810a46e881900d0744015890401e107400c43d0140300007950b4140c501454000e180019401148415200704e026004082281d045141e4072411814985c0000c0c2003135031640101442102054000b490350052540160344500d0001d84108450030300085000c0720f80d0201c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 880563183 1250 880561933 880561943
    0x405010813031b0807171c06050906101103040609080d170f04050c210c010c05060106081e1e090102160209092104060801061403010303050f04050418 66
    0xe000841a95070240c94214a03900754403921142004003800d0356080c0c02003181100d1105050040d00045100c28080101881000078103c0c1e5445941e9448425011504946128a81099414840791703c07868801500030ba02600c0000f1502c51136802a00d0482c100200881c5500c030220b0002207455104080c80104c4e0f030200700f0350300341c4940010122030004000c0301c2c600002d12003001140982d05414034056215000b0400d5409180c7e900700007401c1c440198404c02c6850741c400c01056218202809080b01008007400c01a0310f1401d90344d40d00303489120510609080c8244000004d415005040c601d00710301d160340c442c003800c91500e030185542c01d52000d5103034121101060001900c0c1c4a0501c01c5500c10440034000c000c08400507070801ca05401d008022401354066a5070704002c0621442050002c80c0e007440303d043d21181010350080109005a12240400c8003c500c0c1c0140e10880303c00b200d040d00c3c0c052400319542c07110903200d29040c0c41241d004070341003407900c0410b80180c00d140c1000e44020b403190b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 880564433 1250 880563183 880563197
    0x1050d151502030703050f1b01020d060603050a0b090109090323030406110322023120030705130506030a0903031a060d15030b040f0507080a0f060507090b040b040501 73
    0x707840100d959004035040207010940c00c1200b400035401c0700001c0c01900d04488004c40c1520740324005142641c01c00c906000324aa151b0005110150b00350195a901103c0320800704454842c1c1c100060840e0f00601c0348998807540d0344a11303800d142c4110b120610700e48000008c42d40d40e4101021411066004031030a0f118540f0f80050341d2010b840e20401c581c014104035180c0030703445080304100c98281500001c1207074040006003006460500344011000404c010a1091105400d110040810346030004407070714289a4000d03d0300091210301c4207980c2c00124030301d401c640768400d8100000b0107208079044981e000e0004010012045041c0c1c100310350852181e03806200c8944170321944902406182c461030340c08403052011050640d42580140004103041d81c501007240daa070303101d50311020f80550f000e507031010143c1c03488024080100000001004143c009110175001d546030728041c0e5501100042c14a6110380110740d2640c881c000602c06441400103d41d62555503208124a581c40ba1054034003003004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 880565683 1250 880564433 880564469
    0xd18030801032f120a05060901021c060837121b0b180c040e0d02060919060b0d02130c020c0105130e13080a0c0b0c090310020901050d15 60
    0x80480f045803900703e80743c210842080e00301040704200040c8440300b5180f040c1c40b05103010400801186000700803900c00103035249240300345001c02d40c42c0410210065800c2c030f8401c20080302d0001d02ca820020340003c4a413402c240e0140403400d000b218400c2d03016042c4983d0a00c0080c001d1003c0714042d02581d584070080000a03403024800440104000541070051080016030030000340910401211200d06c02d440c05040e03c1c10000301120b2981842d90b0b90fa5004566032180b03240c0400ca61500f004480c2c000300120070080301070b00141a15107500800c82900c0e14401c15007078071035040000030540d00070300c4004000d0034214550001c0801c180c00740018410034030b140540754083d8040f10131840c41c0c0d040b02280e190502e84040403201c1c0207444615500c4244140384003041c540006040d04000a07900c0d0500c000300c42c14030840340800642600e6141c201081306004c0f070b40e000070301c0840031020800d016803030300759150041ea024052016009507032400c0c4030400014082c2808c02c2c0c40be403241d207200d07007504d620 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 880566933 1250 880565683 880565723
    0x50c0d1e050f04110108060303040f08030703020f070f14040f091104180209042003031201060f110a02010f21050603010c0e030a0b060f12061005040b030307080d1803080103 76
    0x100b0348001d8407400a0703013410003d55126603411a44020007600300c900d0107070382e42c4c8040b01d400c529030f000344c4858101040303100405905105400c45007a8803401003e00d42d041c014041d0003040d5610540e9a02400d03d1806036180e1103541000544a00e00c0b00e040001850604142c0c140d04107503214107101e20b24140310380d0f0007803040b024008400b07600034100748082c0d0740b243d444060350f403070080d98980d11080e100160116070350100014500005022404c1d104c0303501d0080080d14003051440c0d803c050105104c445044904000f440362401ea0302440c000c040c0400030341007038031541c040c1480500c0700d080903100083e50030380503040140518026402000601d41031a021609000c400200300d074507800410544011805812a098004200800c0300d40041d0803400000e42401c030740c0c9030312929500407508000ba50040035110000401d01078800340220000388002a40f28490220003d140720b50210320600302d907055038450602d80d4030710805c8803c0284c2c02c1c14090410402480221900e66200008090500b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 880568183 1250 880566933 880566961
    0x1d1906080a0605060a0905130606080a03050a210204150e040614120c0913051905060a20280302131202030c0a1413090503030703050c0d1e05 62
    0x500c4000207051140300c0c6a84401c0501006000d003a4080000d000201e00303c1c1c05403056a0282c0081803035000119914900282940c0507a441f000d45034000815400109800c40d00305c40c1c3c0c2c81c2081c40c00b5035007116a10138001e022080042040720344c52020402040340c04949184082566040c0c680b13000000e0201c0404c000e03180c940c00303100c9d454004d45100843c942480c08100d00da072104201511900400e61010558030f203002c0f503c00c03041040702451030341484414040d8000941c010181c0212140654580302c0e6070f08005401c010a040ea25291070040e401440090201e114010b401d184d511070b2582c0354030300c2c0500b20059030850000710985d1406220b001f842200e074100c000884010016190941c040c1c000800414145c2e0140240500243c9607540d0740c40100160a003101003c02512400043c0821044046860ba041c0c81c03034001104041000003040d02d0744041d86c0c0c07a000ca115519001000720394020346410140c6a070400c003014001d054031181910012103003841c100a03940d1400d01c005210 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 880569433 1250 880568183 880568189
    0x10b031c020312071716140310050603010e010906050a140f04021b0d021c0e10020c061b010c0521060a080d08060f010e0108010b0a02071d1906 63
    0x980d100c880c040662400050651490041900589050102201129102078422503021001845c682612103c00c585012440e40141e032040b4840a0340004820190592075000c0a40341c4118011000920300c10302c5142040181001071312264595944080d0644404801e006071000c0341e09141010580f030802401301400c031f81301d440d410800d25850038103020a242c1d01c034a0164000b40c003003100380c2001c9105c0c85030b06000710900005049102c050702009080c01c44005038100841c901c02a000c0d200d5501c0003906400d02c0c822a5502c494080030841a0329050f082c0000c0c5400100100c1c01c1e003902d03c8131141c641d80387c200500090103229011801100c0c4ca1240c0304d01c075030303540a4828440d82c000c00407861030740d888000646a6140e5a8542d007204d8a090100024000012100700400680e410300c4041c01d00c2c0c0d0f01c020300300b00040c2095203002801c6610140500e0b00d190b2030100b2000e9030300340308001087c02000200e20320408901114241d400c1c024044400c408640308800042c01c0d071640b03900c9101d0031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 880570683 1250 880569433 880569439
    0x2061005100f05130b0403111206070507110f0d080307170601090e150a0b1c0203040206070b1302040606090305060f0708180a140d080a02070302120f120403051308010b 74
    0x12525582d00191101d03086192003200e044501c0d1004950515541c0080002e58007070306526245e64006801c2101c2a0703481c02004806401400601c000c00340c00000351440c156201552021002500c0081040002c50320040d42e803046480b5401414024040000c1d80581c9a07551505424140140b01d40017440090b149240000c6001d2020000c1c3d40703103030000300d400c40e2101410922403240d210000e1900c040c90342043d1000140003030304501c0031112460400014201e080194150702c0c05800040c0b05005e800d1024002030301c1070f00010000030a001d030341d183c001d50040040001d0342e19024002d1420a090008840d41e10034500483e140f10340100e1414443c048968540745543e413407240c0c03a44040500d1400380d90030704c100c003d80400500000d001c0381c200e08990004003061000440700030102031020300070100081c810018040881c1e804900008180c9660781502d5030340541c00c00c11907084c403c1c0680c400441030381c0818841010340c0a0300404402c82d58403075181691740c46441d4035003202e03614585654 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 880571933 1250 880570683 880570697
    0x1810060b190215010f0f051f03270c0905010503061302150c01020f0a020706140a140408150f061206011401020a23010f05190e03190206100510 63
    0xc0003a601c080d802807003070900d1043e10000c9030b4100030118850000e8204449004c000c0c4014000c500030032502c04010082120107000035400710800d10003c451104d1000100343d1079451004d01c42e040c1c078543d034848011050040d44280f2a82c14800c14107011801114101c60900000080c64a00094640c0c001c22980075038145a001139400c0020040c1030780d915607c800d0f800c0c080c0b035603410740c01e1000c2c240302c5030a03001d050b076103640b00200203040003440d41000041c440715034050344202c2c0703528055544880340d905088859a41200040b002030080750f0200303003039100e6030b5859600000c1a0104901075010844103002c02d48820040010001148450354610f40c009001000720f0607100021141d51541070041d00c1c042e200320b4588000c00e6403080b840244441b4124802102410244255044e2540090041184d0f0604124200000c029900041d04071038581c40488203c1400b48115400ba481400c4218800084031502a4442c032044800816000200600142a040183c0142941d12507595615 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 880573183 1250 880571933 880571947
    0x33090f0f0f0409030201020c06100e0106051c1a011206150318080c0a050715080a020318070f17030a0c020904060605102001060501080a0c0c0204051810060b 69
    0x328039202a4416440600400c1040541d2036511030a4411402076002580e030712001c4042030718203640078000075041d040280c800c01401c120b001c0100e0554000b8a0140e0f6600807001c20070045004103100080c203a0720b8058000048a425019280b0b280350a8a038218007034030380c01c03441084a002e8032403c41f08002c00500c00051600c81c0d03004106818502c03803002403205071a01c3d103042036006640040030310b42c4034500f04d100340130081001d20020440228108003007061840010040b40c00603140d01700f92a00440030511078249020701e681e01518007812074a50300c1d80e905228071499590310801090022180785035607680408001c860409405840300d203c094165030030b2041039100244165111541e444001c5003030341d00e8006103070200444d5604c0b9806401030710301c01018002402844d01a40e0300d044410400c1da41c0061580e03a214240b0100042c415100b2081074844c0a140c0100a41c441d1401e001c0040a2150903d4100300300340302000c80300200e04030b01d1480f0031200c84d40200380d24004240444 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 880574433 1250 880573183 880573189
    0x70b0906061c030c08030f04031202090a05010f0203120f010515040b09091f0605070b1812031e0108010f110f030c0f070501021b0d0306060905090705040533090f 71
    0x140b00b0b400d1107803400e080b240155483d00c00b5190000c0d40c1c2c14102c049104280020b040e03010102400c10401032900b1890444020b000418129280c8200c9061064081c1844217207070007030041c1c40c9010490f04102160b854400000c4080072030900405102c1c0051840e07005407900500162810355031107010701d503d8540100100039048500410750314200740d06039500805501c104242c08000c01d000d4852036220a800e15044050000040441c584c0f082000c1403401c4120001400d001d502030180580b65407a15001c401c040015400c0703800b1060003044a00000780420305500201c400b00403004104182c2c4117490f00049588103642020000440510200304114112401804001e201f107980c140340417080c1c2d0300e560980e000450300001324082c1d16040000b540061020403000c1c1030901d0100061414048060500d503460701504d0701034000d800001e0350711405513046601410004000788880788180f88072601e40c02e40846190080703010302a8403044c40024805541031100018500d80080d200c4e0018 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 880575539 1106 880574433 880574479
    0x210201092c180706080609010603050103051b01020106030b09010212010812180d172d0307030b0a0e0c0c0c0a0506221a070b090606 58
    0x5020400c00000036120610041054000440d80b0b820745001d14804408410200d00d100740507000c40e2a40d00702d01000d106120446803002160388414048064070420b201c020090b87c0088042e0031407048001242150800600c00007030700540d2a26800840d180075101d00000744d5000170800c502d42c40799058280035106800007000c5000030304030f1841c000e112300e01120750319032030810a03210160f0354014000492a081007030407400452032801518242e001203803202240484482403003490450350350009442116120f110705680d60701200381d02403c030100d01b040c0c0c4404038880204030048003010703460044e410040c1450b00c40001078011480c1041c69007a9901c10801c00604000c10750760700d000c41d03103090300c9a40c0d01072610b14032201c0c1c4001030900750442055110011040ba030b804004a000e81205030183d0160155515010203035078a070401a40c14540005030302c15000925510112 = true := by decide +kernel

theorem cover : BRFrame.Cov 880395683 880575539 := by
  have h0 := BRFrame.cov_init 880395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 880395683 ≤ n) (h2 : n < 880575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
