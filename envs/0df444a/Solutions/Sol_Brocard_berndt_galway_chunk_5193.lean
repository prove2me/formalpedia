-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5193
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:03:06.516477+00:00
-- url     : https://prove2.me/submissions/d557e71d-0598-482c-95ec-e16053d7646b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 933812949 ≤ n < 933992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 933814199 1250 933812949 933812977
    0x110a02070527190c0302180d06111612030506060d0203150604090b130b150d0612030c050d020304060c0605070e1509032503030c151802090907030804051005 69
    0x1c00d00b0890f01c500465015410201e040c200248035548a100f4802c6424402201102d13440c0d0000c0001003007150141e011041d14625201c40302d101031144124000e00d06065051b0159034049407900d0036917545080303004d0304004c2c1854141044503a1300e901040780e5071a85c910340c2c0141d690f62100c8824030502409642141c0203500401c011801260503441102410811079402502000b0b0020410544846580160300105481c58105d821000c1c1005071950310740e40700c00845c0458441c0004c0c085400760401c242d0004010552010030f000c0248102c4441d0456031014620b480c0c104280501000c032200001005a61343d000011900303486401c007a00081c000800b1f61041d070014003201c1d030b00e5402440510b032007805403c0c10041c5442c0e28a10a11014100101540d60315280d61401d0303a0440c0006015212402c0820782004d50805504c100024111582840c00f100030301801030204c601c074000e1920301c55500c11001400407a042e48280c400711541180c80900003041c503a07003120f07a400382503619241c023 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 933815449 1250 933814199 933814201
    0x30402060a18031217010b0414010207030209070e1009060c08090103140403091a040311121e0303011d07020c1e0301060e0a0b1912080913050109110a02070527 70
    0x10a0585242c418004139a44014041781c018800801c03a403428810030340184802c020400980c0392401d070017100c060050050301c40240da03036008181c170b42000303e801c2400152200240d55091038a80ca0780c800c03400c994540048010f08144c40584595800000908942d20118000c4e101d0780c420380042d40d600b220508002c46909091801500383e20490180755001000c4014801151422109980489811001000c1e40c0c0c40b0320401c3c00b846130705107086030442e03005001e070040f10343d004540240c0842200d131005664a40c03605640c0c05444141c54411015514400d041c840e01950005e000020320f80304866018182103140502400445002002c07501542404800115068610042e070312800c541c41086c0995000ba00401415188800d45040000d4003001c00303101400b4011030051520388180009440c080784800021259a00403154180d01a1560018020844680514241c0b05038070b115480c01e024148078080d450345042e00032503004101c9446044121100400c42c04100da81c0b900750b05035a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 933816699 1250 933815449 933815453
    0xd020712020d081b041203030209120a0510091a0921250308040809150412050c0111070e091c0903141b04090c0801050a0f05010b030705030402060a1803 67
    0x291040704158a011504043c00601c0341d000d0341e21800b003e040c03001485031410341009203855544c0e100315400d40c00c0560a02003250706458280c14a41c202c91100000c080725940c61425502e0049910400300b022414000c140000446c14080d0855810000228114070f507139502d562490000d60890610407070310001020321120f000100280400c1001100120240000c000c070000001404000180000c3c0100d0009001c1901c0030081d03e1001d03c028200680603d92031030810042e046900144200b03a4005c884a0400c0010807503d2a00038080c2804030540c024952020f880382001e103e5401040b41a60021310840010306c00301d4065400108030b0642e94030800001000ca558900003128401c0c1c078480401900c0d030380011040041c1004070148100c2e0300001090101504612008541c0c0d072b01e1680012030112000e00400340b242c1d0740c01500040c11034118203100181c0300181d0002015000410074000820781c09801c40b070340660140d82550340c4086816040f0b80c00e5807400002a0b68113908140802 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 933817949 1250 933816699 933816703
    0x4230108030909060f192603040806060d1a0a020c0c0f0619030204030204110c07080102030c0406030e0a05070602010507020d050c030f030c0403122c0a0e060310060f09110703090b0d02071202 84
    0x6c0300e045141c400545281c7d2842c1103950381c0c071450044c41e8035a40f0270390001e0b0b528940070b50000680c41c4540300f240500b030034180e06404081000d81c2c01c1c1084540208020707a80705020041c82103032a404891040c035004800c0d0204819110300300380c2c14140d444201650000d1750003901210019039000d4010070101c03c3c1c0c903d844140c0d070031424500003180a04c0310000313048101402580c1c01803d160314064542460300d00150002c00320101d85a030a801a00d080801060041c48444010701480e0000b080a250848009042130041c205180c00c1c098213000a14144500100752042c00c1d240c41c001550303d44914010303c040d4051a4001010f05200003e03010a050303122101035204040768144094805911461403910341d04041070310741080340c0300d10411842030b0310310f0001e40000c4050161800c01114400143c00d50f082e030b0300f019a80c840121000c101400081c0300b5801e00c1c0c2e19110059091111030354004150001500c10f0603a030081c0410301d900044d10550480e032000c1d034000751110101e00b8440c1c000e5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 933819199 1250 933817949 933817979
    0x21305030a050c0a1220040e030a2703051b01110a060c030510120209041401060905090f0d12020309030f0a0206060406081207080705030904230108030909060f19 71
    0x60181d415601c00080c03004041d131205d6007043e803000400c0198132680a0581d018016100d480350b00944a0118080001050008102d043c01c10360b92080e5041c0d11401d401218007601600c40400000c0326000c0000c200f010031a138914801d448c2c5041c0504405030012500300451010219150160034a05810401c8a81c40403060800b070b0b8a0910640d500c2c9000304003941c6540c410344060441c4118410300525002c4566a0720500c02e44448261044280041d421140d458106019481e0350b041440000d030703410000202601d20031130041450005100000380840d000c4000c020745160040007081c001001801074030b8004800c03281c003603107456500000a40e41c0e001a82c1c0315016a1600e030011501030404158010300746283c0001d00e26082c1d03256100c0e81e007984907807000d481074081070100d940c040e641ca000311201d10081090030050305205402041529106a02200695004200e045c50b9901e0381d510245c0d101c0030403640d0003010320a60021625149628103400d11592036403e0200310303010400c1c084 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 933820449 1250 933819199 933819223
    0xa080a0b01080a030f0f0c1e02010801051504050d030903150501090f0603080a1b0501050709080f010b0906090901230703060609080705041d06010b0a0e041404020103021305030a05 79
    0x4209180d9a8550142d103c401ca001e0140005200f0b8200c9100a8014503101414009031b02d400901e85581e038594911200120300002e01d540354559a501c1035681c011032050241200700c3e4641c0c0b14039804102c1301e9a52180d8031950713015454001d0504107040c060320740c440084ac0c0001c000f0769400c500d56142001410240a0109840d18100303038a60780109603c141000d6962141640d03142038407401050344c507400c5c04c0b003040d000a8210901c0f403000503405e0003014002e80942d01c0d2405842d060540240c1040c62030801070719a6803414024010301d64410848680200050701d0b10031b025144d440b1050301404c4204098404002d0602080c51151245400688182401d035010031000d500c68204503840340780e0748101040b691080409101c9032405922414060307a40d52100e070101c81d501c4003500d0429000764426490b074400400c1c080030182c0c1200140c0b100001c100ea042040c2001800409038200300503002a0400d580428040d90300c04001070020060007005040318102d280740c3c60400e40d188000c1034030b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 933821699 1250 933820449 933820463
    0x4140f0109030f060b090702030a0206180a05013e0a0c030509030d081005010c080409052e031a0c030403110f0a0c030c06140f1e04030b06041d25050a080a 68
    0x7c3c0c10510100541b00c894055a015009039103440f80103210304094506045440d008242079180002c4007403048048229401503106c450b4007900c50145c83c0c911a20b13210b4804041c0031304440c0004400803085504108480c101230701e0400711030604517620702540d070407650148a40515010340d103401c01c40d10391080028020383c41901d5190801103501b4040d0341402402500240003d104032011a00259882a030300c43c0c90080c100f5100e00c2c10088591081941e072070801c07010109205100079068005525103e6031140401428a03241940c128400200302400300a900c42d040c0380d010707401744842c2a10410201c100c1b46445294102910040004e110884000d0750340d40c03000030040d000f0300e007071600c41d00102805424a001c07190208026484010380d2101c01104502d12100021840041c0000d103020315240ea182e40352030004d1200721060301303422070300220300220440d40f42040011188540814600010007191005406800c03e20356034100d5a441400010007058034080018030504140c0250310b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 933822949 1250 933821699 933821701
    0xa03020c070329090d09030f020f040c2106140904030c2306090c0901260102040608041104060513091103060403030509150f0f0717040c051504140f0109030f060b09 72
    0x81120364034074080e00004049003401c1b10810100c0c3d541081201d282d40007800100c81710800600160454042040d01c9000c10034440010f800088201c0300314001c80030724035040103000d00300404c03408144502c0440c030b48107020400000d010540700c3c0891603001c551005d80d400c084800440c910200704241e041c1c0761101d20030040000c0488000241c10007001902602c50103240c4d08000010301050407100c09041c4c07140b035460310070715448004d200030001807845960760100c0381454034102079400300d2264401e11450404030280710558400e019181c42c240c0e80c1d9400154498a454a6174080b010b4014095042c00748401304000d040d01600300d54170500800068484403400c0750381c1c021084400f070790300c0e00080b02001d0005a483c40300e8101c0a0b0424440c0c2820611600380404808019100329005c60341020a404108060b081c0407074610b00d101401c0c40e4240c100350501120301842032180b50003a1080624000054540c0d004101403406140c00ca1440d80079000d56007417003006000100c1d03501e40134030782a81c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 933824199 1250 933822949 933822961
    0xa020d090c06030f0c0507170c0316030c020906010503040507050609042a110601030b0703020304021c03110f15162309030c010302030c030406051b07060905010c0f050a03020c070329 80
    0x1a007140c400e2980284045148141008c5482154200d8202d042044c40b040014108680b10084128001442a41c42008441861052002c5101d010b005241844401d105000004502045540546070f00b03440321912604c84100290103410203c460580201540c001e8042218004144840b2000d0741d0b258440d10b40c1c8080556030b41d924007440060316003001030020401d1640b080d0015a085400201894103640503141904041e92031064202d010404821070b5001c0c0400900c0301d1180c030030000005c0d1800c440c10304880410401c0060080340c00e0000c0e4014403649134015980703011648400500c3c4003c140a002c0340326032562000c01e80318480d10458040c0f030745942c0302c0d008070792061040c46406030668a59640d11009400c02912040843d5070b400c2070000780e095868080d0428901404000c01c5100e03050410500f15030043d5440010030007403000091001d17801500301e4060789800d180040e524054941c1c91800d108407500020a0140c0c2050117048003a03421000e607100288170200c000310b6403241 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 933825449 1250 933824199 933824207
    0x1006050406050703030b010c0b01090c1701051c260d0b1507140c03120a0e04050105060313140604060605270a0e01090506270d02060a020d090c06030f0c 67
    0x588038080010380100303d1000040e200f9000041a0681030400e0742c4104000ea99a41044009030084039a940e600c030026140103910644c04940480510008201075052202103a50108100320b00d10301d412060025004010070f02c4e00340200038001c06186030244000d0400080d0590060b0700c6d4140950500d07500c468540380c25200851000407040300c080c6814100e5482400301e50190f03049403414041c006a002607500c05000e80e111b450350f1ba142d403942d00c01c0c031544003610020b9008a16030045180000500481d120542146c0e08501c0406d045035848060f440d2000c028084848115103078010001031004010481e0049000d0364411102d80321401c013510006810303101c0d04c000021142d54141c000c650401c0065024a800000c000008189090161034a40c5810402c6c3e079100c01d20470854810a040142e040b404a100e00b64640c050800340e084054001d541c0d090140041c030249a00007001c0c960408160710a80c0d05681c4004e0401b0120740e1094054000d103004c520381403499090980244406102d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 933826699 1250 933825449 933825457
    0x14120a0206060f1305010b1b0705030d080402060d110d051509150402090603010f08191226040f03031b02120f070c030602070c0b0903060604050c04090e06100605 71
    0x15640148281c1d51800c0030016945000749240d40c0090315040340600c040600d000e003d001e03125281c0010354681c14108d001515048480c0c04d03203410b40000328203000300d56001c2011000074602c1d1070504582d0700e9900001c1d17981d05c114181241560716090a101480307400310040d001054120008100c52350b5103009010305c403091940c03100e90124040002403054807011496802d03000303010f80014100718a81c030100b001c0e43d000b03800c0301a585c042e2000c1004156030400c051003d032071888982e600c500c0415514800c40340440d420003418400f1000d01050003030038058031081401441d403280c14541c10603080642071035072000801c0c0d0011741442016905140844030500c02014140c2c0203000c014440102d08400f0340040704103c3c070a02007040117101185007400503030042c50040f100140d691055251054031103500c3d070b020030010321042c02031240f140d60114109a200800b614082090350f035101400c0c400d0b10403508011079052514209842d07500001a040e8881c0d1802d9104030440c2c1d46a01090741c00b401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 933827949 1250 933826699 933826717
    0x405070c0210020f0d03090203010e070506040b07060b13050a05090712060509250609050a0e01031401110c2104030c1a070606150305070305060306010b090310091412 73
    0x20480000e030005042004045120103035a2058440301c010f4070146605240107081c503500041e4480101d041580780c05e10918040d100d00c40014003100d0f00d0040400c903503001e036108101c2c0c00d120216102e01480141d411481e00c0007001080b2640580c000b0880b0002000e040d500005145d28000c005840c4000000380c080540c0d400c0505c0001d0b1144690b102c10160800504034201c074002c44500c01944109100000300c0c7c0054120780b81c5081c1d0502a0041c405505540140c1c41072405850801c02e0400c408a0340f41580e411003a240b061281d441101405050848818004028006114000c0400c04100340d01c040c10302003d0007034041f8903100003407130324000d0b0700010380180d000160400c462040203641b03400b81c3c008114a107080031610788880084404940c082003426840c1c076076100707070242d0500c40d0b543c1c844010700301007045040c9800030030740d918014000c1040071207001902008076541080740f91125100b00c4c1c000c3c4609010307407030511098030006001030013610a403190368052501900c181c8034188 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 933829199 1250 933827949 933827957
    0xb1617060f0d050c03071403100605011b0503130b0301170a1104020a020a0b1e0601110a0303050901020403150209030106170604030e0a12261e030619030c050906040507 74
    0x1082020400010b0500c0e10480f80ca1007040e00311132068401780461402080354200d10082448041d082c1801d00065440d251100c41c43d140003800b4903138100d0600c40100008144149206c0a00d140c800e00d1849071002d060750910703003207100203440c1d20f100000b123068030702202d4180203070045052000d54031921814000c0106910018405c0c182c01c060b406002804514030441d201f080242d182c101003480c043e42c2840e40d0030724800408201250100c92550004828a01011855407540149444418042e0700030105501d8802042d104030007501510003071038101d60800f0076803082c40c40a20095000b10780441c025400c03c44001404007030f00f5207850039802d078070002d041e076680c581d07030121012500441c001d50310004540001c40c51b100300340e03500c2c05141d20070f0b13001080204010a41c0302d4900c1d07440d08000d060040811208521204080c124010f545030000c2d110740703079100d210003c1e8205120500840c03061800020000038007100c42c18600448000342c0740d000c0943c50304014001655400c84000c0042 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 933830449 1250 933829199 933829219
    0xf0703080f030603120301080105040b100b07060c120c05280504140103061503150b0a0c0b0604020424082d04110901060216080a0b0c070303090b161706 67
    0x101d458403004580c8681c005003900d00343d1104912007215500203030001d000680d5940300700b00802403a01d4406810502c42d08054440f1413900d070703240940d4442c80000400380350325500750603109401a504201c9071035074503c00f4451600200d074000e1168119085400b04c64032000c140b50000c0369642d2001140d070846036035652a1a04240041c0442c2480b03070445410940d17207000029030b11508210b903c4418600c0da4002c11650200300702c1070310b6144d1301d4000d11079a03e010480c107410356800030a601750b602d500031460741060740c4650002d0020300442e4004030a8000891035490b0310034103415039401031031031512100307490713203414139082c02003115484032504094002800440390807030200110b030300510500d071815a04003030401061108000380d001c0c0d03002d40d00000d000302c1031000001145010305172160040000304c840391942c4408c0f1030040c0005040d03510001d03000c1c0a26209070031202c0c40c513421030080b41c614140700740c80700e120607851190040040d2140c0420804e81819120003030262000605504103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 933831699 1250 933830449 933830467
    0x11109090412090b04030b01230f01110c1504080d0f0203040603020c210901020d210908160b011703120105040b0d230607170f040807060f0501080f070308 68
    0xd40308081c80c01005103c01c0503800102c00b540000208040e505c83c0c807440e5131551400d402c04052407082c8207043c0034112030880884040d00d9902100b400000e0920f0080c020030a140b000d41e091003e40302829420444c5818001c425011038001001112100801c42d09072020317a4504035100d00c01302c0d1840700141c208200c10400f20f44070390040c09188020030140e0344407500301b04404a20608508120001760f1020600c15129070701440010569902c0b42804007800390a2121411030072030f09250719030100d594200d01401e008a0009581007400f442ca0460454245414200d40d08282440764610103104044082c441c03100200560b040b4031408103003503108e81d0800d020071001c2c000c0104020b03040080a4a5440819060f009000700c8450541000214140310101c2c2414000c00403e00d0081c41501d61000c50061071001703c5951251849170f12a910b504c2c1ca15090949107d001c2018000c0303820110340180d6521241d0000c0d048804e02c10456809260155040da1204403d1001500c50742052001c048 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 933832949 1250 933831699 933831713
    0x8070506070c0b0a0f0209030109050d09151b051504050a050c0609031e030f1c1a150c030f030a0c090603050c120618071d0406032a0f080a050111090904 67
    0x45c45040c0b111000d420901118042070860303091610a84607984440c1a03070800b950080e141501a06444070812038000035600b02505000c9175002d44503010020101d210140401070000441609801d00c55541d01e0a16040859550380150703020388260142a203459070924104c01151240c901c00307000341000f440c1040c1c1580d8084c9862007100c0090204002041da0990418010074070045c504c0c042e5040c509442402c0c9040703c07420020010344040c0c410343e00245684200400b02504850b4410991350f2183e43c1105085008484412241c8900481800100030103604041149081d03686c4050b82c0f01c0d0b07212421401d81d60151002c02541200300000c085032086c12100301d900c41e0f809001341001c001550420107078054102c5e001130000d040c20040203001420b15441d804105000c031401d00c0040c0c03d64940d41d03550b1415651030007581000150141d904207440300258010168411080551a920401140ca0f160200000c498a501c1c01c0c5029080346064810389049010150003521555944c1da900f02d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 933834199 1250 933832949 933832961
    0x40204150e0f1507170c03040e100905010f03060c0e0619050c030301091d0a08270a090e0c0405100e04050a21110303280e06010308070506070c0b0a 65
    0x1907040b460900080c40d003500c466001402e20780d04a20182c3d50b55095082c030301d02d8a03803101c040c201a1030b0304012407084498000162000d480014850640d1621800414000301c0207540c41500d03072600b41400006c0301307c0c00fa0b1805084074044e1009100380402c200301112980d007042c0c0815401036092200e44c05410340310914012103c510f0501502e0700c40e21440c03851454200741d108000444e1070f5680b01407a410384041c248609000e08000704201d6400d1740d00d0781000d000701d142818200e0a80f8800940141f40c032407401020040203021040c000d81c40f11240c030301030001e814550440e407080b580d800d0319501300781c440e281c03186405451f9041d030681071450190301d1007400f030700544080c4901c40710354000c00d4800c000d1b0b9440c0107c680401000301c071040d20182544100d2110258240c01c280100100c11500f6821364a0700000120040702d030160301c89554004080e0b07440404120300c00c0700004810442c41c68004c00c8600e02030021100c0c1641d500c0d038111508042c81030001c1c00308049401040070303c42d03607400c16 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 933835449 1250 933834199 933834227
    0x1b030a06081c031407050d0c210b0f1c14161215060b090904080d06031121070303030f0906090b1f060906050c0a0602070804080c04020415 61
    0x8a0100c0e81d5200320792404a4a02c200c0a101c1e9007140c18010941e0076105003050400c030407242ca4072518002c0340c040c006d400340e80080a500b907207481c41c900050744104014081160307844050250f00d081280c06500400c07046910a0040c02c000082805500c0c050010300c5180c21850396900382d604459032020605d20701811000302d41e1150080c44070f56040f01d501b43c00060903210b40c13400b28520081c2405044407400341040c9801e50324004042c481c080c0000d080b541e5060003503c000303a00751a0ba02c2d0010701ca11510b4000c0040390302d455000f00401c1840c1c0c1a1800c1d0b004101c40306035440e0f032002c009403e201903d51300f600c0c02d035200c41810400070380a0f4100c001c60079454400041e0a0320f042e1916403c2d41c82c0030400b01c400101ca48104001c0144442c91005641025400d0806080c200840600b0081c514040d440c180400464542c2c0400c1c41000001000d0342e200c0b10540d200c07517240c9000c00c140c3e000b50244a150303000f04800c000260810b4800e07101142e2040b5181d0200d9689000c00765220300c07201c417074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 933836699 1250 933835449 933835451
    0x615030c1b1225080f030a0c05070b0103120905030f010c030f0b0102031215061c050702010501080c0d08130801060302120105040201050a03020d0212070f17040c060807020f010c0f0e0102061b030a 86
    0x40f0228a840000d00240c1e428502c005070303649404d48024086900e500707804401d00802b80514400301d004900b0441c15280d2100c3c10000f5062200c1c0700b9586094558840340c1e00d0f00c07552084c020800c4044d0089044901e4503181031069044a001c100705407811010300354010303072051184032030711458000d03410f030003004965503807030841c0f0500007107040d81c2e04c204c01198480308868002d03040040c141c420345074401b540d07100811603541010016511580c0d400c0c0c2d42ca03c0b0f04a0850190140941182220381c0100740411600403a83d4840c0d449000c0d0411348001d03031143c4100101e080e60f8601c103006a502c1a64140d4505280221981042c0e009400480d601011181c1c2480000711a4100500490292045440d1640b00711004400203000c4e4011030304401c2455402c0c4203000018110994540c16a201030511503840d9452020481c944114150180d440d50b007041c100400580d0028100c0c0d14a05c09a6a000402c038011401a0b039a0ba0098a000c8040c100e01300980c111010b1080103140c004a102c2d0b8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 933837949 1250 933836699 933836767
    0x618060630010e0f270a061409150606030a090f0b0402040f1802131b17010f05031e030c1b0a05100807080615030c1b12 53
    0x4600e2245518200710008101a41c091425041084a4014010070a48107200300c0c078038040e0a000807121029020081460119204041d610503400f84502841004021941c1c0c0901c1070903d103015100355601108240984400719017824008610142c240a074412420702c030343c0740c01e800d200785a4002411041407681d1080040001002c548601c540d2034020b58034cd408e5410b05004020454241f09000c0070301904e03118070510340e00000e0402a11040d0115091103118002c503031a440500394160103c0341c031500003242c4100580d04002900f038403034003501000540e80c0c1c8402030700e8442c0c0414081c50340c1c99846819007070703503c80000403003007000c281a0058a00380643d03640114036080280300006030f0200248214400382c10a088600c0c014070040b546103c03500315401c00540420b50141810742040300e01400100940c80d015464215840443d880d186d9a281c04040310300f00f50809264241c00c0c4601819650150000091035403031188140401c0e8a004680d00b400c40581b40340c881741e4072000310110 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 933839199 1250 933837949 933837967
    0x52b06080303100608040c09050c0c070b1c0b04140103050d08060402092b0c060207090e0321040609020a03030e090a05190905070509010303030606170f062b080a020c0906180606 78
    0x10027454007826403200803540781c50007205040d0828009800c6400c031000207001c650707000900d40c0d880504a07800c40400041540020000c68060586400c2c400d017220010130002081080001e0030b4110322510780d40c0e041c41502d401c02004140e10464001d56406514a028500e094101d00c000200c000d00d40030000401d00c3c895518488400f916a01003009a04181c0e410401c0c00080e02410180701d014001540c503042a4002c4a0565004140051144040b0000103010801c0035030082c81440d40080c04086510780e01e140040003d0b1402010134020b078070b00c4001c150042094042c0c140034003103858412001c0861001d44078001c041c08103041c0c1d1039120741000050283ca0b031151140c0618001c5d03401041d40390030003201410450204075112550906c91013000200c690154010f0380058080b11913090307110610b0f42a1003100d400f5964103603581c8248407901e0801582c04014210026140c0030340354880c58410412050510490345560003038004600c1400301d6807294142540400d004248038240300c000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 933840449 1250 933839199 933839201
    0xb121503070f0501021009170918040809010306090c080c090d0b0c0c07080f0d0f03020408031803010506012c031603050303100e071b0201052b06080303100608040c09 73
    0x1a80c40079642030102d12040c001940e043c002c090702201030382818000000c080d602c28241460b480d14241000d000821510880d644900703000c46014204600003283d41010705209a0540c400860180828076018000031400143c0c020b0315034118a541703d421040e907812031500b08035070100761b505074083ca0021400000500041c010b50182d03605000694170b42c1000240e1600d0894641c00502c0030358048035090a48a20014903182213a026180600b580d80d40981c00741c01a00650300280507074040400c190f80c0000e05062801c81d240801c400034800d540301d44006580880044a40d0700c403070042d000400400b00310215801080354405001c0b20f0306080c032489e840101807a030ba0070484080e00000148040c4032403508440001d030091003c000b8180c00c2031343c809801100300704090780c0d80d4040d1011080a580c058800e40fa0595180d0195080380c2c61922800150403021002d5400340300e280c03000200d10b001e0004246c0c0d10417080d402c100303802541408002d80780100010005c1380c12804510000c189140301d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 933841699 1250 933840449 933840463
    0xe040905010605030606031501060c240b040b0402030c0f0705030403020d1a150603180c060c25120212030d020703090303081303270f032105040b121503 67
    0x680c0000800a040c9400c15051810241005100ba48800c0d0b26100d06600c01025034115016810041c000200500d0148a07008030400f45607111070092030504201c02d05500300002052084808100448c01c40c0204405c900040e51103401d0640c0c1884031400d02c4c06040c0003041107501072012a07007001c2e5643d001400d0421050b40454940c1050600c0e101c800e9240c501543d0811200c2407003040006105000c103070310b40002400c580d80389006c800c40142d40f8609000c40d005803600544003a035209540026183d498103040c4515000142c0d030102c1600a9020710403580644200c11460283d0041a0b001c0151481c801c1d0f80458150008208801d4044000d10042c0841c3d80309448a00403680b65003809450140b008103450a6078105a0208000035030080c800081c140440000d040c2140403c5518240c0d00c240e070308880005503102c207010080c0001072032103003c6c40c0070101e03038911282114202215140100c4c0f04443e02007209026850200402200586e802640595521854410100000d180000c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 933842949 1250 933841699 933841703
    0x80715091509030c0b040803161e030e03121603140409180b1602060705031e0a1a0d08041a0d14010503010e0d05160305040812030919030f0309030e0409 67
    0xa03040500300f003001041c0e8041c8000b44600810380341083d1400c5461620f0b4402c103040302c4083d81c242e00800040040d03842c42c0b1204800d4010151000c1080c500e005800e15007802402803082c800c880f69882100c0c0f6210072201c40c044440c40b44e8200c026141d030252891000c035011203d00ea0070600c404a680e03140b91040c103201e81c42c51807003c4060354590070180b41d07001e00a0719850b0002068000ac020380d6800145140d04003502d4a80b00ba50b075642e02000140500d2010010b003880f418075002d1103280300e42c60b009004100308122400c80c00d04c0c04081080340034501e42c9401403001409000411130350318075140408010701e689010910f458103400d100002c0350340325180c100000040360010b0060f401c0034459402d05012103401826560708000024142d0301448054411300340c030b810440e004240c440c00c180c030f009006600460b0000015a001c4940d541c1048500142911404941400d03245c8404410980690503454401c0b100d600c00030124060400302c0c1080d814020001d004a600303444034420311400754 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 933844199 1250 933842949 933842957
    0x8031b030c13122301150b0c1509150916091b0311090d060b0316080f070b04350a17030105210a1a150a0807150915 51
    0x4582d4a010082101d042c1c10400c0c4810403a18400005401c0d44804030381e808044a81c0280300110b0305541d400761245410311a044150f80c1c4d80000d010340038a001e0564422100d0a88040840c44002c00c0700d6080f084443c0d400b0382d4007601200080c034440381201030b0040300c030720240c0300c0003002e291f002d031021032050703016254159032032244041100d030000d9410006000d40c9401c0c007a200e00d03001414480d0040b000014402c244034440281041142da0001c0b42c081c0300541070390904c070b00104040390001d03103d21608020b0b0180308642d580c441d02c0420380ea01a210400150b50a02d400c1c4041d220b43d1415050103050f4a503c0741c2c01c601c100920b82070481c13455528a900074190500039107081c101c0b10203918070b14445904180014403540d901c081d12040c520980d814200d0380344040d003440c03030b103040c075114405040780090005442d4076440d0040414407401c1e521480c41ea0100090342800512010ba11502400b50040201800000040303010249124048c1c604060b186071540c40400c42d0602c040c035244042 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 933845449 1250 933844199 933844207
    0xa0b031f0e04021f080117030904180215040b030a020702030f0a06062105030a112505040c020a030c021917031806040e061c060f051909050a08031b030c 67
    0x42c41c18800c80c00c0c003110382e501604c0b040030a20fa0b02030800481030250820a407641480c69600395000c00c02d0311501000140280141588981d030b43c00d002c01001c006034000c0180b4801e100c01000f1035011901142c207400b00407031540d50b0340c80440b002900807810880e070600550b2031004e020340080025030400e6010310302c0094010b182c141c4800d00c94181c440b4648140b5a101404008164080306440800c400c504144c0c042d030741c00c100030504064404d40388415a081604002619a288030251000d81340c2c1a90b08200c1c0810184081c0e80d100c282c1c40e00140020a4030707505500505004004180801040200d222059100c0d4500404410b540080506a0340042110b204c411003440207842400b105884880c545402c03c0c2d000c2c10340e0080180031501480f00c0000c0f414495070164005040c0035009032003005031204090f00900982400c0c1c481c4002e18814a40e1804544024411a0704440c1d110f0300401865440340d031494656080100404900c420803c1c58420070303500c6200441c803e403403d905007907803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 933846699 1250 933845449 933845453
    0x90301021c0f0b01090b0d060807060504030302071208070f0c080a0b0603070b070203060406200c0a0512090307060c060b0603010608092a04180203100c03050108010b0a0b031f0e04 79
    0xc03202c00d09482e01000f41005241e403a142d0b0030556910944100078030307031607645500602480181101d9402440640b06013840059070342d41c001c011784141d13440f075400d0f03440c065915413001da030301d0144003000303010142c0030003104e00010103072002e00b44a070748a003c50241060b500c2a07080d0502c0c1017008283c46c801b40c41c508110062905205034030113070000181140c00c0880135004070b6520340700207000600302c50f5112500c800e44860320217480e40c90000901c1507507862004a40c420f845202d00101207e0520401e22066085c03aa01000e4030450100900200511490711600321040102e040c0c00380d8843c0c0e90703121aa405038480c000194041d0410b82c41d40c405901b0418840d81c80e000d0040c2c8940074200101c0031f51b00400c0c2100583c00860072045401089000e060010b051094540306802581481454000c609051542d00404001d40d201d44003003015a0b43d8000383c03420399a00c610b035241c0c010700b545400c0c4004040000515081650a8a00e0001140d4241095280156500014100d90b00c2c40c0030082 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 933847949 1250 933846699 933846701
    0xf14180a1401120525150908060a0c050901031503063206010219021c03180815131e06051501030221090102071a01090605060703140f090301021c 64
    0x300403c0061201495510316454071901c0d41840c44081405940d0319000e909400c01c44040748028101c140034148064002d09006850401a1710583c2d030345001d400002141e041c4140b150300e4858620b51602032805110000441c01005101880c28500c00008000701c0403801c0c62040300d4000707a00f01c2e9565402c1d20704d902c0090711810000b9410f500301020408018280e42d0100c0c50b1b0090b0240c038001c0040600c4280f0000c3c1500c4108202d042100305a884c801050550055000346444070190b05c4100241c0c40d00c2200740c6409842c0c0407040d01d00c01100c041004650000c03a0b04c0780b4135003d481d00c41039500c9800f21b194558459010140c03041500c1320240401c483c0440002c0125082c00d00f400c40c81d14410500f240c59000c4901000301c0d102c000e0038002400160290112201c4560164603440c1e441e07260f00100c41150710130b001c3c0c054601d142400220719810050229407102e038041e22540c1c1204203000611203c0d9002408039252840c3c14410400b0903182400900900401030301d400c24982c400881040c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 933849199 1250 933847949 933847951
    0x12c0606030318060d0e010e01140c0c1c111006090f020327120c0a1401050423031306020d120c0f0806191710060f14180a14 55
    0x80c86500100800b410080001240810b90305081c0c0300a40c44445900040c070090640e600350146c15400c00c0001080c800040d80001c1c00c802d210f0380d07451394580701d058070081c060040750442001540510303138801800351001500c41030400245448240c54003261007080c00c20103284a401c0041b502c2d21010310840c901e50061408004031007200b1070540c0303000b1a000c00c1400709001301c0d0600305000e101240c21010300f40042c14a90903d2408142d82d02c1c0c01290482e500c0740742c200140da55000310340c400080d040041c00b0f000e005a400c4204c0a00010786104108100e035416111807900d0700c0101b0000d12102340c01c1700140000c0c1881e80180055449068010b041c00301d018004c108001d1401440c4640c1c640c001844036a10201803030072000030b80d0b40c080825520f65140d18021020111141c000031011000c0c0c030802800000725042c0c1d225040106101401e503085400781c0c1e078160056420078030010398084c07200460907000410003400c0d0800d06140e0b8480c1e0005031029119141c45002c00507642041603011 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 933850449 1250 933849199 933849211
    0x50307020c010305160503061504081005060d05030306100e090130150c0306091b02190f110301020d050c0c1b090c090a080601060804030305070f090b0c012c06 70
    0xa00051410160461789080700c2c00d001c10500c10040b01007440e0303031500d115407008482a0900165607035100c0c40c0341540c5261041c555170503e41481d00040d118140a1038103806039611a00035420f68540404001034104c6540e01e880801840c040301d00c0d0107944951340c01e40284021103c90b41030700b00c01600209840c18003221460300b00c0d02c4d01400800140784880518a1092803a000222046071002c120060700c507582c03004244a04028123003800c9205540b0200701d46800d9000c69441150140c9442d4040244107006020341c1d003101c50603000709101004400066100500040c030b0501038101500c200c40c03065a062208403000311f1800c0f82c00a00300a50802e8400e05111782040c03c00381130001c0c0c50510010000c1801c0c03640443c030b1545c00c0c0c45064210020b00365001c1529410760312440700410302c580c1220290b0009041002048000d8022a021680845c0035911951120b09100f210085580280342c039a82543d40c0e0502114500014090306039040341035200d2007000354407580c02d241f4010024081c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 933851699 1250 933850449 933850451
    0x10302040507020a0308010b0f07052401230d020402070807030c02131505040902030f0d230c0a0f140f060901060803131a0904140a1a0f060705010605060a050307020c0103 75
    0x10041c0401c4d048400c4904448150220720f030f4810100127446c0c034074012080c00800078410362048081d01c4060103003000d10fa220b060102d010681c0d13030b1403002400003d1940b0450051030f070b00e151904c850a12665805403203001400243c5841016641c3c408190322203503058000070340f413594600451600d070400300b50100b8402e9003440f1400c1811195a01007101d0b2044620840e0b4560101046440c2401a414008400402e403a801c04280758082c0210b0000411400098030080f091640e043c90001070b164154901d00007000004510307550400921700c0e214054415800800d0000740c11030003000911152198a00500068141103180e00c0c2960b001d9042481c185c0c0080c401404400c1e06010800e0440352004992805070909900001c000d1280300c500039000b5003014a204100131070040310f00c2c0070300c1021004000c2ea45580b010040d0300300c1031400040d403021f1072840c03c035018900480a010702138080c20001420b00d540e040000c509922280c101c0340406c402004010aaa4060100860003802820 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 933852949 1250 933851699 933851713
    0x170c09071409040b1906051803010c05090d03230d05090a0203060403200d050301080f0105040308130507180e0708010c0e060a020f0106081c030605060403060e030f0304030801030204050702 83
    0x41601c025024040310a030081d6a42c400d19080c0b695800b201120015180c4804503d5640310702000301507078061543e070542104461005541400c0501c21070b1495105950748034242800d40c03040100e04c4500200c1581009455a460300344800f80c0c407864241c0c1c10051a2884e911a01d0054031406d847d4000d100c840030343c106c2048640542c8001ca905075100d0b034149440031128001c40c41241c0712010b95100b1040d140702c1c0b41d00c5001c4d4150404001c5040e501d83d80121129500e40c0c02415090f070301c0c2110010300058140000c0390700d007200a100780c0c41e87c5105a0545540a80307540c008848100c84005071090180c80e0314211004080c00d00c9500e020f083c811b002842144002070303001d0074044140c60f1190080c00001183c5c3ca140e40b09009040c2002041c1d8001d100184d6a42c078103c1e03580003140c228410f40a802d600002c2420700134818081111000703400b4a04052640e1282c1000341064503010078140010020f50550030803a8000b14800c80c440c0c0c41c0c1071081e50550040c0b00444400030020015548160 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 933854199 1250 933852949 933852977
    0x3010f0f05060f1b060103050706091205120a0e090411090c03040c140109170a060f0c09141c03110105150d020d06060b0703090317130b0d06170c0907 66
    0x401c03900b0910501c80b0320340d81c44940030026903944c0031003021001d0b00c1c05000c00200400c24082a00c0c030459440b913032102d402070307129102c4980101100034010510b0740140030f640008080000030303060851301360400711103152030740c00411000c0900726022102d031580341d800d0351002c2c036260743d4054106202c010302c24190b207404d6490380b840075585d000c0c2c0c03c3c91005084948040741c0c400e801c0d510141401c0b80790510050146404113985220110b42107501508048881d58106050711034165016400c0c2d075000b50207483c14400590391a29051915000171183c40340034030f80da8402c40d2a10100384244d50f44c2a1100400f01d8440c00c5640c064183c00744042c209070003601d5a039441c803100d11442c0d0100c40c2404100c01c0c1c2d00d0450014141da47c000c00c100ca0001c51404185070300a03403000e003243c0c001c12072180f01550516001d107c1d07228401040070082c3c2c03901740c20701003500c4181c06420554103928001030795a40b258003144007500319101c1e0034101ea0003644030260608185455a030448001e007001e4074904240 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 933855449 1250 933854199 933854209
    0x1e0309010c050f0a050915070501020a141305012006090d02070f030c0308030a1407020c0310060303021504060f020d0204060f02010606081302030c060706150e040c03120c060f0203010f0f05 83
    0x12030880c41c00c101700855001555030342d045014000d0800f9940c056950600d0b40b81c041e002c1e40056003008007241c22400c5200707010000704125007080c2c0c140111005400e04200c010b5076120078140c814001540d0030391810f0001c032810083d803030241101200501198205000082c600051a0841040201c3c020410030014140c3c20100003030f6036201080984964416a00400506944a090342000340d80401c1c041004c3c3c02043c0300800c5030702a01501d8442e0b00c070340340e6001a41e159100040041c0e0019a42c14941240f051000b44c2051081340003082486003482074600385d8000daa0000c03001d6500080c2001401d030041104454115030307000038000640317003031006004d07002c004251780d044501c191900404c5544c2407100c0c80a01800801554031040203060403001403d4080110558414001004c19140d12081103e81b1135a840f03110012000e04596801a4003d450300c004e805001d031a2121200040d414011a0b0700ca04906030016125854401e541c80d19a8550303102042c00b85114209010a45403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 933856699 1250 933855449 933855457
    0x903020a1a032d1f090207050d050f04030c15030e0c0f0111071d09060702060906130f390b091e0d0b0402040f180609081e0309010c050f 60
    0x14182082109103584a650502c054143c0701a920380401204100c03210701c0040140b2001031351041d402c0306071a00d400d5040100d1041ca003018096074030405130427035200c1c8120000c00c5429800003d1504207582c1e80d5514261035040c1d08006210011108c0d02080d817907140c426000e90405a800070705141c0e40b1100032074102c0c50014130240c108155002882010340040042200416101c400b0b41f10a4050b03c0d03100e6450380c1f05071481c8043d03000341c0020490091000035528000c20124002e0300c0544c50f40d80e10480c4180b007114007103403c1c032110307041c880101d440d12100c20b81611000301c2c4229890250565103007461028289034440f40202002030180901c284103440f0408026500c1d4500007001c2c102011203203103801012640070841c440d4640c1041a8403030703140d006034401c0d075092003030071052020403044c0e607402c0341c0700003980e042110309201140c543d8000d41c0126024904040c0307032041148080e00300c0c0341030801414100e2000400d1105d07040d800d02c03c014240030185401c1d410700341d00c007a003401c01d40300d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 933857949 1250 933856699 933856711
    0x70b0c0306010c170c030a0909060806070206010605031003080c0309010807260a060906030515060102061506130503010e03180f2101180f030e01030504020f010309060f05070903020a1a03 82
    0x110030b01359504480c051408446070640e0344401c80303450f0b031007210005024800c03a01840039010704021001900c1e0701d00044070350103540036801420381682007604c2151a9000180f0034030340d01d83e1041000000c102e910009200c03024581d000345541c0c00048001600c00e1030060444010804200800e409000803e2241c103400c01028007000490746401b00842c0c094011500084080b525119002040203000503510040d00070710a000300c400c0e604c45005984508003201c2039807490716203151759181d510700031009020a11210003440c5a07a6102c8000c00c0c01c40d1a41034201d106070b1f000003080e91900c1400050002d080a041308d90920300907081001c02c4071918078510050003480d002142c007003030b15000c6d007100c00340e40c082000700d00e009055030810b8030f40d44502041c00d80c04228000303010381481d4440c4c060f0038400c5401400f04c5c4984814800110300603e55200103a030040e43c1d50301840d44004107402580e010743d40c2d039542e2401003070460040100b0603078607038800b6035404c00e60302e040481042040244c1394054 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 933859199 1250 933857949 933857963
    0x23100501030216140304081204080a060906020d060e0603071202130b0a030f050102030106090e070c0209090a15090210050a02070e190903020f06160203180f0d08070b0c0306010c 78
    0x8a03c1d12207251482c03000001010fa000ca84000c0c100300f54000017034022601520111503040c102c600340d544881c03107540641e015036000202801c010407103580042064a206030001032800b03d484503030b0811141181c00080b80490400140507040c9000c110900141440c1902c5a80040c65680040c6d440c192500031aa28140c4480f10328545075101d00d02540110307009a080d841581e9140b401c2c1303000394024000c0e8000314100c0c2030003141c05d64550600c144255110380301c0c0300e5a51083d800b0028059001019040c0602c03071002c24800040e074942c0341c0b03601d032080484045000051441048241c04509600204201090010300c600356030005036041150030040840840344c0380d50034602c041d02c28010840560f1030800b02e030281010307030001e44800401402401e40e000c0b13072202524051101c0d10051010011b0740b0a02038960030010303441e40500c03043d40003844924001061408907280340000b1205507203000000c0b9601d400d001e4400314040c3d01c149050405e0b840e40c901980060103085215001521031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 933860449 1250 933859199 933859207
    0x30402040902120f010209090106140307031515020c03120307080103140304090203042a23040608011401140f0a06080601020c091f15050306010f05070204020706231005010302 77
    0x5510f41c10010f15507503d8101c00c0d074040150b01c48619001c2d5004032a0903004480c0304000148241c0304003841619410007504592440c1c86007a0110f000c1c00c03450303803102004103172038000240144010a0384800c41107183c0250080a481d01c04050409890014451402d001041004051640101c010341960340c00107048600d480c401520500c0c50190380c106100091001003400103006030342d1221482403100582480740000300380002800c80c10540f00e1084a414061080c142140c800f0010740300ca4030001d440090100d98600e011800c1d105045c180120311212030006002600d03000c01d500100e40c1090721111081070b043c0001c5030b10012540303d140300b00030304500419096807003070201c140510001007001c006420303c1d400d10300203440b80c100354481004021100041c180d569414011198180351650790442d07031040d00540b44c0c055601c000c4010054108030600040e41c0741c1c4007070400c243c0641800295400c1c84000d2044064441d810000e0031141e8000b007007080d40409100c0d105445083c81c0258503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 933861699 1250 933860449 933860453
    0x42414150703110303150f0a0303081603090f081c0605010e010f030b0a0e06030c03120901031d2e020c0c0f0d0b090a1b0e012606090f0714060304020409 67
    0x920702c29892500107000005c1444510409a1030601103940300b103602141d018001c01c200f050304e44d003611008000c20225800213806480f90f40400f8440d00c07003814080b440c0c01243e03840300d80039032108030100c582c01e00c0451408246c40e4240f0980401c001e0a903409c0280350b003028000303402d08030094080d604000c1002038020b4124481d410405c2017040c06000450b1458490050800310384085804601030b118a400019081c84c3c0080d6460318007500c200c00da8a807101e003074011406071051203a1111100405140e0080f207803020404130320815040400b40000380e03180301803040d00180140756a00054010b01c0324100303805000c00d000030414411a800500301d03c50380003042c142c6007204e0380500040140341c01c1040b80100401c682030307018420000242c1003004020070240010050298007200440c00005014290000c1005201c42c41e05d5500340340406840141c2c280750010440300380c0ca1941049208108181080140e403000d0828408002010800c1c83c02007649800003c00192260b5110303000442 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 933862949 1250 933861699 933861707
    0x230105041e0c0c171201051009031a07030507050702281508010f090e030703050906070b1602060a0e030904110405030111120c070f0803060a05042414150703 69
    0x11074910404010300202d0382d070740e0010300400010842560180c048241192124144100721501d0704641c54660410b0303401c20007402580c1c0d401d01c3c411814018006404000b00d94858020089900d940a6924072850050350040c00d641d0003618990901c002130107800c0051b0381c1c5446a8096000b04502442e5038035408140100c00d030810760105615041c0d200c4612202c6074440c1d81035040e91045401e0f1001030307648000107400c66503c00704104558000f800500b0000344078400504100900901c183c0c28281d40e80c83e4090140400d5440c0d085159180034000710050301404820750284504104001003036100b040d0f1506c030310820b0000e51285641da02c1a5102c50701c42801c1e507020b00300c050020841c0c40c0c1400142010f07903001d0780e14500350703190400001c0d195002a2003101c0d810341d40010096500c2020750342d4403400e0342020380203540c008080302003c00c0b152994810050014007100f0a1009513850442203c0a01c0303480e08604140c5012170054005911150854a0101ca50305850740d9605400d0a040b9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 933864199 1250 933862949 933862991
    0x106061718070321081003051c090302130218040507230705070f1a0c120904020c0a061a06041508100e090703060606170c0d0905030c010207050123010504 68
    0x916011031040c1c1d4820103285403188103011001070321450354940f20321811b00c008903060320009109600078011140b403089055400000e00d112400c0010350142c4a900264406200c0c04400c420319a012864000c00741c0104d542c251550fa05403410411400d01010040c111350581c03c04004449806d0303c102000d1140b0b00c120b40d1010b8020090750041a00c038004401404054070070102815400e0a01f00b115907802812a800321a948005003c1003501c6d001451044d089841d1260340240d090000d4200e814003030116213a207a20800000920425242c654403001d0041d40c00240074071001d020601021011108480300c4443c0380c10000e0243d5940c100d5a0344401c083e80082c1c40031400f82c014482c2e050400151101a83e00c140024400b550311000101e40150030030b80504140c0540101160550788001c00170151010400c0d004105174109494640c50350307102036804071482e940011041c4c14000f00f0b104442260f0100284505540c05e080180b224408042c0205842140c2d981c02a50400f00350940715 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 933865449 1250 933864199 933864203
    0xb01170606040e09060f010f0e0103230f0a05060a11070609083106050711100201110f041d063601030f06060b030c0d090f050610030501060617180703 66
    0x2240c0f452524040d00c1e5284c80003590524002000d580000c90041a0004074105541d00803644942580c038544174400c004d690459090140c200840070212a09003c0c0300c544801e55410009150031170441c0340c0a8500341d002801c0d00344852915420f041421012000c42d904550404004941003004d41424101032003496a4840d090240000b8108422100c03c0c00c42003088104065941965481c131003503d0038410100c00a181c4118014004440d01e03103660500421031817840005000c0514400200c1540d0100100d0151a01c000c10100003180c40007000030401e4641ea003d051a03400c24802190717101c003c0719142010b80003059140700c84043c1c41c550307400d40c000018540b041a56540c6c28040300030a02c1c4a002d403182800c05401141d5030340b04608a900036007043d0815403400380d0190001000700b01c1c00408948a5901c504201c001c1542080128001d0741031010980c0881d01d5882c0c0f103801c40b96154402c00500540c0c64490040d0710740c802546c5c0d4080d6a41d03c0986003001090391440c2441056040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 933866699 1250 933865449 933865469
    0xc0102130807060201060815010621062702040305060115050c060c03010e06030f07120812010f060f0c050705130f0903030c0207090506090a091407080a020a06030b0117060604 77
    0x249007100250784411280d4a400803c0385c603440c1d00c00e807a211200c107a004041c000c00c000041120070b00c29940c0d0400c1d0a46a08440041450907820400340c0d0015445402031900e0f080740704641d21464039405004858200085261619650302c0c15110101442422050303030030b81c03040d041c26a01410854140c03443d40e006440399807601514142c9990820302034250700a5064001414178280007079650f0804901d28001d2107154907101c8188504600d00100b142c0950f010310105074100c3d404681c2901030800f09040e04441820b120340201480d031030850b8032003000001c1c1035200c081500451608107a84080da00000540c99001c0e06002420845555090451402c440c800515505920500342c14030315500b69080d507561900d04070250360040d50000d9010440c0d4011440d40b28040c1c2c80741e440d0070301c10a90401e46080d400003007810302031143d000c018a600806104000c51820b600008050300203410204142d002001c00200902004000380b401980c801e40441c0b0140d1380e14040d10010081825 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 933867949 1250 933866699 933866737
    0x5070503040e04060c052a03160c0312090e01060806060702030307030f031a0310020a0318050f0d05031302011d030d05090301052203121409160b1606020c0102 70
    0x2c0010000d541c1290705583c440d281c21100640e09202e80e04550000380d4034014070303a041d030143c5003d407010524401d1408103840304105080ca400290440040c0c6240107810710100e562460416460701883c0201200400101c40010701842651035250340c19101d840c6440c54842c2d03681e40102d8014403400d90080d500d8400890f14104050340081274142d240e006c0d603070a001c2d040c07045459034189030218041740da145d001003a403164005816405480300488510380480c20f142081c541195041030030030709890340d4000b07507200300602c00700b013000c5078095041d17141040c0f0310300d480c040320705d04a41844402410022414403008100b40d0043d81030b14503400040c15104100e00040d000781c05540510801802542044000b8110490304400b004039003241c2c48031203881041c1c65600b210341080c4148146a91a5500240000c0404041082e842a0301c13983c01003454041d80c03441500924a254040391002104104101c0007a034451203050389150b1002000d03031101c03844840705004e80200c240103a4440c801c51 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 933869199 1250 933867949 933867959
    0xc02031b061008012a0e0a3201020a020103020906040906060207092a120f0e011a040b0901030206030a06030b010e060102011a24090301020c0c0a06030908070f1a040804050f0108160e010507050304 86
    0xd0300c2607034001000c0d4407500048d40140b15900000103502080c0b8056000040d101340554000e4008003070b0f02070010b20062911b6220240d40085417080d801140041e88000c006101050b4503115a40b8024a62940e40c0d99040100340300c02510301c5554011000c1048211250107010b03956044404182001d10381848426405d00d030383c2c0e000340294030203003403003c1c034002840e003240c02c241c031940d1900e19000d4294040b80c2e0840c1c09000301d55002510000c0c40c0c0d6520780001010454031040180030f8052030a40102c10f0900038002401d48500c3c607140800c80100c1c2101040036650000705055030b00e003120214040044040c1e20310614010500d1507900765000180f4408501004201d03d800f007a8211200c49156031500d50880031120381d008000d201440c03c109100124003040b0000d07000510031807508044a40c070200860b142c4000392001c442c0100c000c6824405071a00701014880d0300350a20f404a042c2c5001c410510105003000504014400303908061645a440399007140d11884e0450100c1e0b98550b038074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 933870449 1250 933869199 933869219
    0x7081320181515041508040f0501090605040b0906060d2a0b09040e0d0c0318030f0b01051002010b0607060b1507050d1d060d0c02031b061008012a0e0a 66
    0x2d082c01c0d62141a044054102d022101d006036030039140d10207030002442c18861000d485200029200340e40d60742d441080000050024007920100c184520030104941c103040ca058000d6080181c0000404d400c15820000152180741003000b5150700300c1032607003e00c40c20700c032002291481d981003000829000140030440100c0e1070b004003142002900c0811090b8441b03940c03261520301d4005500005101180b02c5004248510300c41c1307600c1c19400d07404c00350351592503503402030b50002401e04644100001004120518119011402c41c01d100e00080c0880d00049000658a00c1241402801c0700d035200e0000c2c8498440d0b450741102c0034281e0140650311049400c209941b04c5102e00300340d00003014070500c004148144202002c0051016003903c2c20900311000400c040c01c0c00561903000c6100a20983e02c82c01841161503007112105805081e05003403d000f40c207503044444d000b034901070381003c99040342100710242500307600d20b00b030078846000311f6400c1048680d4000390b852311354041e80b6003c0221f4003101e1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 933871699 1250 933870449 933870481
    0x16080d0e0406051215060108010819170a030906060b0c070501081504020705100e010b0604030206030a1116030305061512090f061e06010e031e071802030708132018 72
    0xd172009103020760391034400448074050240204119600075403030900a041c1c064048210940c40307501020a001e1540340f819280d900f00c0d01036903001941702c2c4680000e00284d40b10b0380028144160f66a8503055055515035500d1450f4403a0ba810801c02d44002101a840c030768040c0c12008001740300b55680e00050800503030741c080780e404040d5824541900c4181d40c203c1407140c218202009000c40d030500d85140c0800c08683c10090594002c1900d541280c0c0700c581e544002002c1c4041c02c40c0214070404440e040007802c03280010007541c00f9a1201d81c003500444502c400ba200300d148030381c0c42000e050f5122001141011072a19442d1107511441c800d00c840c241003031200f0700500d200350341105660b0381e84030011208001e140020300d406030800d80302d01c0034800d43c84003848913110b02c95040354900c1c2d540d0701d411022400c0c0040070a440903404014014030f180d1003811150401c5900c04201005a0306442d504254810143c5103004540f040d610029552100d00886110141c41d207170715440d03483c08410b11540140303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 933872949 1250 933871699 933871723
    0x10e0409150605130504031b03020a060507091508010b1603022e050a09020d08130e011d1317090a090212090705012a0f14070816080d0e04060512 64
    0x10000c800b90202612501c617581c4102d800d80d81e0240344859203070b00100041c0b07404006908501030b10030300300041400c60180c98002e0b0030a0740e03a1202240b926003c00b4620b0242004041049882d400410030f10314040144d0b801c0215013001c410702d244051600b0f80c9840d60310a4414407000c10500100e84a120040140540c0c2c502ea08080c00303181e640464903800c9501c5a88000e601142148411011640410103043c4c0e8552121641540a031501500411000241c3c0079003000b400540300111280d810081c015040b81034400c05190201c070b942d032621a9490036605508c0100340c0440c2e6038041da524040405c004180340c010031035a0f200300038090700315400c1c1266036803014800c2c0040080d66500c40c104107a0146d094031a4550081d082c0c841e15004100c1c648030a841a10200b181a0003003008282c14000403403400c00142000361918820f18107100b01180b2106c206071400000700298140810b90b90740706a8035140a801c52031500c000200100810340116400c103102c500484860304000a403100684 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 933874199 1250 933872949 933872959
    0x40c08150607051b191809020a05130e011b021203070513080a030207080613020d2d0b1308030109151a18090411120312101502010c020c010e0409150605 67
    0x13242a408005c602a0301e2140f10b400c5031911038a0300c8031009031391003c0c00381c502c001e0022007800d5071400050498556002c0b004001603482c24003184c102c00c24420428045180004a030070300050410280d140e10000103c580750301c13800000034604034407640803140c0c01d25450ba5401c80c2c42e910344584960b51a01c001c01180584152100840c0034a80041d01500c0f0f40e81d8514180c0035128a5030a000313050094490449000c01002640c004c1c200103c0c0441181c0e950980194200c5503050416100313241e03001d8030303180b0144000b91071b550110b140780040701d05417141c01e2004501d0000040c100d000304030165012580c0c00107065110b00030302405100501418040340e81e40c04809040d40100030796241c041c0c1b002028001d0342c001c00aa07500304000c04150f0511460140c0b0b040100540f040700c2c0380700c0212400030011007a22024040e5032018030f0002807200d51803000300908056414080e40d40d09902140505000c00c45444080c0303607a031600b10141540e88114003203201c401d00240100a003a00e8001c0c14807030703 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 933875449 1250 933874199 933874219
    0x15030305070b07021f0906021608031006091818050d120f06081b01050409020304050607030f0504020a03140a0501060906060f0f0f12060b18010e040c08150607051b 72
    0xb0300c001141031174920303402c4100b0000880782e40c2c000c0050000d49011500c264080c4200b00500000e1001301c107101e1b000f82e0312b03030b03549141040c01e001210440da00010b0a1002005041c0030139500c2e9403000050703110030080000c50215a02509222710600c00c0c00034141d2081e680501481944400344600701e5113149418805040e040031140281e520a00400e0a1540080a032181011404540c0e81c60464103051252a05807208a4132003660700859056400303138452818455401e42c58468400b10315a00ea01c00c10036800c02d6800108900c489100c00380c010750806101d6291044188190341003070340d002e8020010300782d44131001c4014080c0d80c45800d0105030250441c0581c1b50082481100c4040c0d16603e040c0d03020308000c02942c252a110215040700d544c1c4041c04210703441440c0c002c1c05204200d68105480e65503400c001802541e81030200e60180b4101079464019981140050760080603404007407890f6101580030403002c0c0103440c0c003c2c015102e18610380d0050303040b191820385144003d1b100d5440d6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 933876699 1250 933875449 933875461
    0x601030609080906340302031218060a09030207050915090403020c1002060105030d0905010c0605100302100e03010f150e06181e0108240a0b030d09170a0302150a15030305070b 77
    0x117804050003000e00075801c20041e000e110345810344080c1c2d0050341c1001d24409070640c480704500c0c01c1411030b64450a1a611007090060540400002c80100011215805185400c0e54071121a048000c0514000c5001802080802d0700905c4030344006103025043c540402c91410000707664034028400c8500034060403401007108d030321903d01803045e608182c5851850358610780da46001403000803d10108000c110030301100580d12000071b42204c2c022a170300c55080c64503100800d400c540e05141d160680b40c2c5040c950800c0722007180c80303c10881e040b07546d542005644520205407003e580090490300540c039082007090340f9078440380500210701c007004c609031640e0f296400250b0710020b81c0c22604504080c1c4d62060030300903802c21050350101504001043d05202840800d282100c8040190089190f0950900025810000780035084903514001c1c080c00b1075948000e906c851000000d801d400c4130180001d18038107001d801941c0721007000080c08070083d0750f80c00c0091054102c402c04403950030080d004120 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 933877949 1250 933876699 933876787
    0x100c11030d050a0f031806061502071a0d020f0d05100b091309031814040b031b01082a030403080c0c0d050c1f0617060103050601030609080906 63
    0x10282400b511154070f04210240f040e641c07454046520810151501c9404e006210b200402d00403803072007004089010b6060030400c0003440c50a240080c115801984100b010024440910b0720070300556071500e80e2103002c01d000001902c5600004c9107602c1c00003409100c0002c49038400c2d07101e031a44c1f540f02031031a5207417214181c9512501d008150f00c0b40749980c80610700750166001c00c140d0b5109017460000a01c4040c50300446c425180e04c6080742d0242822034283e1030500f4020384101602c1180500b100044441252100c90310000f0f540307042016200000310880000503032000d01c00680781c2d500b882d901034018003004039030045500320f00085042000c215003e0914082e10070320032103600508495200043c0c1102c06801406001c0360b10300c110344414131400314511129000078001800401c50504101001c00030488000500700e0707a42c0481d0041001c2240811514150707035102c2000701d111406d6052400d40b60064184090f80640000340c02c3d900c0014441004240040c0010031044103504080c1c448 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 933879199 1250 933877949 933877963
    0x318010c0518041d16090b150318030f07080d06090501030b060d05012315030a151a04020f090f060f040303030b0d0b161706011d010e100c1103 63
    0x2d501800703400701104142c074081d0803e1000c8a181c4154482c01e001e4050b90340e00e010300703900240d42040200c850500c0160460700500c003198405480d40c00e03030b0402c918048911840000c1c040c0d0031070328101c00030044004081c42100d081142c2802a5911031001c0e045c0800709a12007040c00c10000e24140001503000070901555040303d412004401169075080180f00980c0022542140c0c255031356201038414000710350314180e400b82d64940b440f502c0c3c81c01105401e0401ca8201001c0e109922035542240000e2100660100300c400d000c4010a85c0c000c84034403078080d400320034003041d40580003003010403000d08403402610480d03000b1280c60105003120014407410b4440e02001582c060820041070003c02d001c0c1d0006a404540030304803040711000c54488048414041e13401e0b03120681000a0540300c036601c14000044662607902c02101414440c0004e0100c6516904c200c240030303c40900c0351a20780c0201885c400985010303014212006030004010515845040111285040000341d05c3c141c0c20005818 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 933880449 1250 933879199 933879217
    0x110708060711190f15090204060902090108060f0f01180308030103060c0f1d190503010504050703150506031c0201020c011515080c0a0e0d060c0302132918060318010c05 74
    0x1d404040d1440e12006030020107030407140121760701e9061140c01a15544600350007410f681d60f0060301c8041c10000140301d810f01078012481f4110205c20782c543d56880603182100080d09080894022020550100c1401041d9102030a152408400001070241d980c220031015511907079003103002051420280c500c218408000c002c2903c1d5070000c8803090800481f4003900340710500351a0707641541c442c0001c2c259401210219210f412070300041042002003a140000c10b142071109108514060002c0780c3d88903000202d000d00030040c0b00b19081a50700030b5049859002010000f403240b01400100303400004068800c41d001080f80000000d00a44585625030041411162452801d14058002c55000d900e05442551110a000218000840910a88865210685005d80c549105c079501c1d20b0040c103990300c01003100810b001c11800b5048145500100880e0042005466410440c800c113200c4d1140d13402560400c00000c22300110150020030701200d014132070024441c480030a40c040764240144086 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 933881699 1250 933880449 933880463
    0x9031905030907140109050616030206010b120a1e0c0c0c151b03140c0714090105131d01061205160e0a0c0302070f03050d14090d11070806071119 64
    0x2040c043c112001004c12042c8005143c06181140c13101f00043c01940421103142d0a028411040810182c06202450040c0039948495040c09802c00c2c4c860007501d0010031942885a85004a0a6602142106941c4407101d6001082401a19000901810340039003090320a09811340b40000c00009940c502c02c10b40350b01d030342c2c0c080d050300207801010284114031004070140f240d002c0c0d0810980c07400380054070703c404a510090160500e005051124051543c02e698010040e000c018000c03038603044540c48410520700e00010b20003445140780034140fa43c0c5982c1180a508003000050740c2e070300b1405c5640c0c55030700810a50b625031201c1e00710400c4007071052164058608014001884000d403962107003c907141c4030b090140c600b501a03628800c1803002c061044000c5007002c200d000080482c0c0c4102c803080c03000380c5c200406a04001320364503540d0701f070101408204501c1c202e251500080500c414002441c26104540041c01c0000e80505130005640c0c06601038441c0d0504400c0a6502203c2c0030310240d00486 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 933882949 1250 933881699 933881713
    0x70c050429060d090b07030c0201020708040e130507061d040218060f0708030a020316020610091113091d0a0b0115030209030a0302011a0609060d051e090319050309 72
    0x440e0035060074040e9030081c1d0200c0309000421a114030350203030702c54441c443e0402e001203181629018046030141c00041c01160b10610440b4009030602d0111416a18140801070711903980c00400141d00e909440000d200e8040c214000038444d41044104007101c601c1c1d060342c43e4110044081c007041f8014244102138080301c40c0c0e60200107003442c0004226019800000d14900701e00f58035191007070f03441034507a050255400002c10401f84c828107204180c079070183c4041d144038240000507040100b41c500a040d8484e580d00e07213400403403584500302c07041c907030341c5000c1e403883c2ea035171440c0e91300c01801c04080c8001c01c030b00209200714039000007041804406070f0041450520380d081c0f19603d10542ca201940c442450343c00c10248000e50b0f010045a03141c14443e84c00850007416800742214000b6a11500a0082100b444005525135891707041c2c0d804024000380006855640082103001420b0f542e0050300c401c0141001d00003a408007200520030740051442121143d0404403003110325100403200b009060b0481c0b8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 933884199 1250 933882949 933883001
    0x203060102190818010512150f03010c08070e0f0904060501031e0f0b06010302071a270c0d0f080406051314031c0e0a08010e0106080d020307030507020301061a070c0504 74
    0x81404102c0c801c06140850908047d41d15014100005031008001c500405603200c1580c0740003001440341060a4002340105100c065014021031340103400b00050040e5402849400e807105d650f42215854000c03c00007642c00c00342044401070001303010035204101203112075217031040c22020201d1640c0d80603a0324510001035484500070a000030f00315904040c0c00308801c1c00411407128072800720390303001d1000c440c0700c0c280440070b41348030041c02c0382d031200005117400e0080e01b9401c0402c05441d80d21003a104aa42d00d00a0703c1e1800c81e500d4a8940101046c60105005c01d072680c0c002e01030807020030459000700c5900e85a0101840503480c4c0d0b4800355040d404809000c2040302d0300d070040c2200c03625604001c0c404a0201002841d03040b2203400001090b0741d03821204013040400d01908e401481107001514280119080003501d80c071a092010303045c030030005822800c644095200324020804104840c8072624071492103821580590010354046145c1ea90105651034544503e80f0707201c00c0c1d10310081d2111005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 933885449 1250 933884199 933884227
    0xa060b0f010c1505040614070e03010f0606092c01230103090c0501120902060a110705040b0109030308090c0d0317070f090510030902060c070602150c1c0e0f0102030601021908 77
    0x200129070b0315448807801c0308907090000d0818010003980c1c89907188000380005050846146100850031075042c401e0800c0340d15041084c0fc810340b61002e1390781310511000b04c1c008141000890940b0140341203000002882d1303512007400d5181d0821707050309a004013280c070f00460681e10340000c0900703051480c2c641002a5070041c402c00c3c0a00548190210700a04ca42e000141550003840c04200494120758540c856504140049800780008440801c5038080210000304080e610740402818007441901180d69104c0030400d0b144014401004905800e0143c80d00600c402c80d40099250511204070100f4811402218040c031002c4d2155203e01109103480c0401080003070201c849403d0642e80c1c1c2c207220260300d40314010900701c610310000741003407840e011000f46056071005510a00700070b00801d10202082910451300c00501c0400092840c48010b0240300041503502e048860600c10f842c1403a4420b80103402842c4030300000d8099980c00da1102548424a02d80400300414603002000204401400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 933886699 1250 933885449 933885451
    0xc0306090111030c2b02031b04080615010c050a0819020c010f18080729030903160618120f05070804120602041a0c061e04140f0a060b0f010c1505 64
    0x1940c4d100406614001c40e0f2030b517400c01c00c1400d08007460700007003045403580200b000a098040d0b01f090162400d03107858021610740d4805444100c1d004c0300050a602d150703204902e1340a6094001007610840312961a22030f1490f4000900072011041801d0002550781c00401c460300e0245040c0c440460103c1800f1040311070940a1009072070f000406800824140341c01c1000602130701845100c0c0545034100710160101c0072108134100e03030054040041001005000c402c5e00d2502d10b0560201c242c8061901e0240050901c580b000e400403d40ea441c06014003110400810068071a81c48004510b02520030480300d92145a4001d00b1040701000100400307062001000d001e2400340100600b001c0d260050140d500b010f00c5d202d00314404c000306425801031070611200c3e400202440c4e004014030303410b402c5140b250b90018009071480da50100d10040c43c400921410030140b90034001c1d2a00e01d45940380c042c005010307010341540100c0040d0a0140c1e02d5001340030038001c00740c2000450504500180c10078001d050 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 933887949 1250 933886699 933886717
    0x7080f04051204060207050f0303040f1403150708040b09010c050f07080d021b010612170a110f0706020c0f0105070b09210c100605090a0e1501080c0306090111030c 72
    0xc54200c00c1c1400303804082c007600180c01c0d00e034041c058942c80d00342003090400c61a41040d00c2500304010402000706000803d100725040180c010741000510f4000900b000209800c8940e8000703a002004211580295001d00c0b03584151075a484503181d034003030b40d400c9450030388950012807001c0055a0304641d01d400900407507840754034114604031070200c01c082641c0111000d500c03933804807a03071580440000c1c0907413006400c040c2802c860040d40340d1541c0301c0c04090181101d000b0f94000821b072644a101340484545500158200c55524418804485d0307a4803c61068070010700441a91031082e1401040300c2c0e11294050f0748550410303015882c0e00000060240048540d481508110415040d500b007100d5014601001e8850300e85c6d88a4002c1400c0407a0006a425030313514084007400982c0d124160707150050a04c1034002540c4008002251810190b0340312a0142540b4400000302ca6200180e9100f55190603000d440580d01c40c0520345090b00c01040703222007100c50500000362003c551001406c6c50074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 933889199 1250 933887949 933887953
    0x90604110904090803100914011406070c0f1505030c030f0601111504030305010608060d120e0a030803011406071104050c31060905010e04050c091c031707080f0405 72
    0x10380784a00081c201c807211841180c8203800030040159504000300010020981e43c84144180328246400301c2040c5014003960300c0c085030f4000b00002607101d020589001991241c0040141038503048214141c07402803003240e401008003034180315403501c15016a4000c5014500940c115181d042c109010544002c021904002043c024020350b0328007081040c0103503021810b80c1c0305500f410304000b02642c40503000a418017001c04244400c07525490b4003141e0882d08112421402c2c201580115403d100c10380c0026070103407401c2004024802c1640045d4101e070349910300e0200d10001d03d41801342600504001404e2800d16460380e40c02d6090070380240d944810b001c2c2c01c1c14503010b40000301040d6600300022040c4050040e040940f88105400308550107401c1d40d00704450b001e858800000e04a0f402680700a01868584001c03440c1d101140341a1404014000c10017038040c08905070000311040554000c0d00010b458403000c0b07e03c11840b4504c103000b0720283e5a400010340e00c03c5201c0600c910b01400031078440c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 933890449 1250 933889199 933889207
    0x60e030c030a030506090714030f15060711120706091514070302300a1b08040305030703020723010c0f05030d061e0e011205010f0615110c09060411 65
    0x9100d05100404111409460000f050308007001442440301d002401c4000340301e80a40900200102c003015258003020b443c22504056445000081c0f14001d202c1c00103030032440101c0c00c80100000c403400e1808500007940c4210f4005503898606549108602c02c2c0d0011408040081c000f62240c4904844000c1c0982040320164029800c502543d52000405800582000360300e40600c00322034541e900b06400513040c503a9296413603c03a0041a2040c2009041403001d001038002415420210029405402a040c039481d00c1e40c07414419140d170f02640d8100c005019059010034015600b0b07891142d4840d00fa40f685101c4515000151884a400c940a60f4414a40d40e41d002c0043e200f00000d021011401c2004609640b5049040c540c1081c6030300b504428202c1800e0500a0394500520345046840210012113143e00340e00300b490040c0b5255403030603285030920201043c2141c01d21020042142c042d03945c81c1c01b2814a0340525200e1080d40710035076000110078040303120f9160941140f044442840700303c501d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 933891699 1250 933890449 933890467
    0xa02010e0601030605060f0d080901120908040807030c080601031208190f1a042306150d02120a02120403030f06090e0c09100f030206030a0608010c09050f040605010c060e03 76
    0x60300078242d00450720162100e04001090410042464040c0e10513500e80c003003c1c1417941c56100600603446802e04004c1c840c0300c085070041054000b065501e030842d841ca80d43c0d5031200390b960f407960b0305401700340c0713422001c20b00000b282203000604034100c94004440d801049403506c4211f0340207601403c2c8509600000001705c10307004191203a09001c510550300000c941c034100c0001c4ad00165509240791007649490b0403040929a4681c1c14210f4298605409a8954aa00004903400075845550703003c0b50010030a1450a04a03500801d40400c1507450519595200b03200d00040e4480c10441c801103082610128001134060741000341e400780c101d0004075905403109051011a4003040b0500c078640e006503203003070303203424188030b0680c1002107d20451101c5040c280d5011950004d84030003809071400000191050752203900a01c0680484030080c000d803140100010079a10144c0509407140001c0c412a100a2910344076000485406860388000341c1d50760340b00d14004040f02003200701503010800c84051 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 933892949 1250 933891699 933891703
    0x50d05130e10080c0312120702030f0d0603030e0a030f06111902070e10120f021512181c0509040f02160b0901020a0c08030604060f0f051206060a0501050a02010e 71
    0x4454000030080c1e030001d03480c0c01c2200345050300004c1c3c194007980004055112890702402118420b50038413180d848141c07250482203245200342c00117848040c001084d0f1105000d001d4001508803400b9559149812948800300981c02030980700051424081042d00400140c403500030444900004100c03d0600805050404216004d000c20f00016003020798140700c280707801c690003a0041d402101030912503003031118050a4048041e0003810b030021141c074a80456551101e920003055040d44180d445150601c103022000300c041d11203990440b0f0642072402e890000042070f00d441d51480b081e0210035003a05000355017a501107030515400a0300e0306044000110207000408001d4014001d800c03445026080c0451030700c50203803003800143d00420422054a511044000c8003a4000a149a880d264a000940204001d500883c43d5400d000400600c1c03c402c0300c2148100d0314240c4041c0c022000040c1c1d042e84407a42212a00c4c2d00c0b50721500284441e51141c0094507510856000001c3c5080078030101034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 933894199 1250 933892949 933892951
    0x60a080706021501090b030a15061d06040e011103061c02031c080a0b03030316200105091207050607050f2502010906030903140d090609060203070905010804050d05130e 74
    0x40150707001070361090300700c1030300d1020314010301940b1700c10000f070030000f0006503c854a8103005000c1a0700b000d050050901c05510290081ca840007480000041027030100c00001d80c110740141c440c51a208001d40c2054040c0120910424550320180c607540d00d5004208108103840a2a04100d100c43c030358000584082002d80c0034503460034032034a0b54403542a802400d840f001491381c0f01c00e40c18a07402421580300081960f80001c00c0e61410f040210000200311900036101c03c004c8034045c1034074a14920a0f006602c200e0240f117000c5c4c10742c0ca004408a810049911038500010202e40c00340c2d000130704051041014040c0e0880c294406858440d04c8802c005040035101d040c030401c09100100c1c03404642e04078601000031b220700c0c1010b0040382d034142c074040c0009020703044404903440000b41940c40240e15501506165a12040422a28105d420440c00a402c00c0380c161000c1040104049903940c01484010712860303124004081ca005d03416011034498001015a030421103034000003048010b4075420746 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 933895449 1250 933894199 933894209
    0x20f10031e090c05010507050703060b010e0612041b05090a020c0c0d060b0f090c0306120313060e04051503030d0e01020d1d0d030209011413030c0f0e0601080708040b060a0807 77
    0x2055050b22030608000201c416405541071140401103017000500200e0600708880d00500000b405501010050341c075944418082648480000368002003084810241c5000d00d0040d81e051312000c1d0b849007201050f00803401032951010000000660b00c481d00e400070958400c1034003c1d104c0860380d50020a41700c1d8030034003080303400d942c4440c001ca14a052809035401c02e0401116400018144000b51801c41d20014040034050b00740e000c14003c00603410422600460138144c3c4a5610955815006140a40480760a48601d0074034011680840582080341c21040d0300601440c585448014008001e0800450a5025540078448100107101c83e00c620992034085044039005100a1040a410200b01c844924149481444210710387e9034861001d5410183c0010320581c0d4280c0c9181d103d04500c126403004080d00a46180403e04000801d40b03c41214000038030429280ca400c1d006440001d0110b905000262010f800030380403560800100b80c01030380140c1122181030310780c2074103420300c4260b03040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 933896699 1250 933895449 933895451
    0x2070510050a14010303030c0c081902010e0a021804060e060a0501030201031811060c0106030b010f1a04081b041503030305100918061e05040c140607020f10031e 71
    0x12a4858690328000c5070303841224a40c007048507155078400042c4018042c080074003050741d01c807a820f070464004c08604d003c090b00804a26114050100c0f207032031400c06000b800c001135081c010580000140000c844201c01e0303000704ad2441d03182d607048051b49169001131080d1800c6803503015600711030b241404043d028909580b000f00d0150304600000d0150703000e0581c4081c2c011007001c851404528461501020316004840641e540c01c03070714007444d0140c03040d0313000a080f41001c4800051000404803038041264035201c00300321800441c0d09500b4180c0101d2041040c0c40e000040248151403030440b14200340540100001380c2d006607a003c0c950b4a8919420850210fa600c00512803080d034900c501d8001400d541d070342070101900380c1c01c86a040c0800c40c80c00a20180e12513240a0681d4644020010907280101c02000346151600300fa0465400d540314145040f0b0141c4031514441c200f0070304030b0707800503005047d8404404a007005c0c002c514120898030010155100356100c10041010798441202d042030fa4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 933897949 1250 933896699 933896713
    0x40602280215060d020d060506010c02031005040516180207140a050114010b04260a0b0708160302030c031b090307120213060302090f0a060f080d0e0f010e0d02060d020705 75
    0xe10800c0c078202c00340c8082e104000b50800000180d554140380d500346030780031078045041e4030f8000050b2000c0201400003503050260700001407a000c0a070b40444d10443c080e404844440301ca80880b881c94050502a01c0e10500c422020400f400d000c580090030002d04c50f81c004000030a41d601d0160422821202c1142e06035182c0340d80080426908510310301410b031001300b0074541442c0c80d001c0c00c51055100300395030130b900000303401c0580e51000344000c41d102d60b0881c9803100d05281c140e03802015a00c0c00c88401c600741c040d1200c5034061501c01e2098030f02c0364000c1d008180c0ba58540c0310406002c0d4020248125140004101148460310240088001004016041108404e80388104040c24494401e03071903a05103400f1080000da516028940d030850300d4603018060f161038003001c881c0541181d80000c0c02900b0709030000100308400080407511880d040e500c0701e40070705403107040000b072000d001811800624010000030b00d5107803d07042420b1b164801404c2c81d2601c0f00001c0c458080e03070880c190660761500040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 933899199 1250 933897949 933897973
    0x4150917030a1a040e4209011a010804020913050f07031401020304031b05070f0312020607170a0c02031e0406110a0c030b191401050301061406030406022802 69
    0x801c0c10f8444121000d0003480e40b000074055841050303110100709101c410f90900e010001604c42155034802d50b15420340018005810f80d42452802d40317001070b60350f1801043c80c0e400b45d902c11501c400c42c84165190f145030b84a03602009259032010b0a81e0101042a8400d075001a50400403040820109000303003203070703918600313103034007401c0078500f050645900401c01c000000341c0c48403844d04091000d070428003202580d41855031600f80140c116561034401e01a011050058a0480f01580c052681c219003c503900d0032001c503000e80d070b0103040c1284240c0d4040496006203c903040140011030510442c3e08000312400003071a4442e03508805102134000103024000c007544516000aa000303100b0041088000f995502c4039078602d0b92001405000c0ea000205403645910280c190185c01005400e128140b025070252000a0080c8905880707980703021400141500707101900d1100d100018079041c19503403503858950181d1b006410a8608240f0082403080d0104084a25041300c4450340c000c0140c10402c0d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 933900449 1250 933899199 933899231
    0xc05031303120f0c0506060405040309030c14041b0210020d02210108010509070609212009060d0510020d060b0d06080d08090a12020106171c0804150917030a 69
    0x3e09250401c228480b09280045400081d0b40c5030400342c141d4000620b580c0328102100c03080466040104441605c0400091040040e855000400340c01c40b42000300d200240e1010140c010141c241c140540c01c0030450040c075000c5640a400c19500c03901e4054039220300c1c6800d8800c0d507140b4510031200205900014401180248034440c0d100707820100410aa50070b003030000d07200480c1885520301049104002500c9038060034005c1290380c4d4482e02c0a00c84284d4000c00360380c40c000418140b4050034034500010020701d81021201e01454200000d010034002c00e5410701c0117507102ca0307641002162560800a40084000010034201c0101c0d100010304500b020015070403e0900001c07041080030a0b03082c80500440843d0440e10750f54041c1c0900780c0910000c0c0240c0c0500011307071000c6010704a19078000c60591000c18001d000c00110442c2d561510011402510561826907000d041c002158a5003d01c803e555400a10180c0c01200e00c4040c03400c01004074081c6520849000194030340303411207010714450b1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 933901699 1250 933900449 933900467
    0x507050f071d090a0b0a050601120b06041a0408061305010f0603120f022104080f190807051203041208090d1d1914010f0801050a05010c0503130312 65
    0x500006415002d140030319240c940e032a021800100c01e44540082600604104200e41074254854042e2601d807604000300e40041c901150041c0c0070590101072101c1c49a0036200d4800200c0b40207114909150800d55004c02402401c09403080d141c1d0208000719800104000d2240704198421035503101e01c50601d0058207481409000240c01c9003024414400190f1081610b00111014a040300c1001c41c03400080340b82809061100c0e0241c00d40c01384c0030002100350300c0248103903108202190321540c0c04070000c984d1100c90302100c0042003511040d410000341e4450080000d41d0080c400c480c0e01d1403030500b03880016801581e089940070550a00c0502c9150480096136103c002c0d40b010740742c03104400c0c40c0900101d281d80560103150380d182c00045895511b810816840c000380300d100e00850b5440e108890342c10342000013424085212400e5000c4101d01c82c07401c80e81030710710280100500c0d80c0380c600191002000300340c0403680c1340014440110f40d200c981d08010002d50142c0044021410394400181145074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 933902949 1250 933901699 933901723
    0x712060501051c03091a22050a1406070f05070f09020301090b0d03020c060306150d09050c0607030507112718010e06011a091206070210090203100911060a050705 71
    0xf80c041d850102103a0800d4460080391940011180740110792030152515101d03454207010410220700a414420802c4c50002003503503070946a00740b140e5115844039107031144008034540e000604200640004804a89022807907104008481d00140c480070b8048080c1c00e5500a92925507002c001007103850283d0280d14001103007650000582c1c80c0640b4025228443d04040501483c400004204603444940003c2c1040e45401f5100340c86404c0501c1c424060900c0b4079050780c035441014150581d61403d41c00b19103100d41d05807501303451b00495588000001c2d86802c4110ba1000070945222001180001c81c0a4001080318944d202407800940caa00c90117501008148980c1c54403414407291440020300506480d4060b17a41a03050038903500301c2e802403061104003038100d150461054640d08000500c3e41c0a42c3c0304d034081ea1180900a04d9400403104134400295140c2d118061510a02c04258451300c10036004070700380040503444101051107580171008040005000040240501c0401e00058404d88 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 933904199 1250 933902949 933902989
    0x8060a0b190b12190905061006020106061e030b0604080109170a12020c0102041d010e070c080d0c03060801020a0c05010b0603010803040b0a0e19150906090b070203071206050105 78
    0x190a20351542c80703602448081c036820500c0e11003c5403840501100e1194041c500807401d000c1c0f08014134103a42c84410a43c1d11800c4800700701808034000d4010f000d00c0b01520300b01c0d07a80303d40d00c0c88130400400c81c3c50203c0341c0e0002803607a81e005070401a1941c0000b000a828078500200d100c07207840c0360450060100380d200902007041800719202b180d60041510002c010081c10160b103510210056600902ca903501404403a2881400c43e107001c1c0c1c903102a14101d40e038000c80645581d95946003030b100320f48140c038000c005600400060000030321903400361036490764514001941c6619181d24600320b83c4400c001f02c0214407007024520801400340104000c00c1d074107481150865252483c41c0707a80b4002c0740030710b1500000214401508520a1507000d640c9240105201d407402210801c10a58003107074041e1039000c40c9501c1c4040081030061400e0000c581041e5904c003e1246092103e005580000030201e0741401007240020325049203507402d8150038010240000c0350f500d000f0030411ba403410b64070084014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 933905449 1250 933904199 933904249
    0x21207080d2a1403150324180c0603071b0b07050408070923061c0804050405010b0a02060a20042d0308030106080406061d180102040f1401030608060a0b 67
    0x3410848083c0c80d08034038510f011a01803103405c0c2c0001d0400002c84174116481c00004042442081198011401011568001000300590b0320302283c03280842e00f041782d0080c200b0400701d04414820300c2010f4604103044c0296850404954030500302e000c05680c2c00300000d0000c0340502c00d01c1e409020000046c0040c08041090a01008400164000710354070b204120382da8400145e0607458030080f1090f04444510b100d2a14140b5280c5403455070091b015a600545c03504002185040081040f078449443c01d8004040d00da40c0d05401c0000780100315020400b001240206001048007034018201070b040803c1c3d900382000c141850924615428080c107500280303155030401c00300314280116410754950f0315145125585074100036014240b81d0b4040544212502c81102c88070081980440c09082c86183c0d00301300042c080011401d030300890003590000086034804001078142144000080c404c10b040218072140d44072429030505100301c94004c44d0035181e034643c4500d0303c1e1008045040401c03802c030450b00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 933906699 1250 933905449 933905477
    0x905100c0306051c05010e030d0c02060f0423031908150109060c030e0a180c0e3c0619020601120b0c090111030409090b1303021207080d2a 61
    0x2084c40041400c504a0a80d10002051000a402403240f5561140803240e890140c00040d600400c01e20740c09200501540300441c021040100b00640038a8201103214019000360040040030f9102c2010518030b1300c000c1160012600c1580320b0700f000e034001916a6100e40c6480c8444440090030030150078100106110140001074119646401003500741c42d01080016280b00440d1001c4110b0b001290400b104100045081a040d00182c02c16a4a40d641598540c03101003371010400c0d43c1480e00c81000e400421490254100e9010003c80e8640e060440810303002e120b0220b070301c5074001c030700601c0c00d00450944607007503c1c0c0410005004010740390410002c48580c0e10740d0000b0000c080d04401c0c030a01c00040b40182a03100d0004001d01c41e48002c01daa0352681d54000c00302c014611410101c4014044400140200034800c40209071941c0503000b8060907880350b907030208103a010319022a4012014084054510302502c5050040055016229180e1642034190313014804007009640400c0f0b0002d49201c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 933907949 1250 933906699 933906709
    0x609020d140c2205060f0d0b0a0303090512100501080d02060c0f0706090317090d09080313090b010908010609020d0b04050702070314070b0c0106030c0608091f09060905100c030605 79
    0xd0111200e2030340741c102c3c0b03c10003c401d0050043e038443d6501040104401d02d9000c442401002c20200001040000c25004018052a22214480900840c1a9103020030850403c04000b0400441010076100c0c0502140c100c0001c442081c0c019183c15445103910741100c603010011681c0100c00b41f80502d0a01095a5004c60b0134483c60000901b401d4686c00003400f003500800c1507400c0900701c40c2e21440d01d40352800c52140c0d0348680d50b010303500013980401e0001d41e0050110899000c1d5900000310b0b08503d007442260710142410b1400241001541c25002034500400c0c8916005005544000340e070700e0b05002001c2d8240c40d10f10316800e01c19440c1400b4004119000a541c004a0f64800e0b01414003400000c0701c14240b0a40354003070101c02000140d0310780380d00c0f010741c0b1510a8138813500c41c91040d5521440200e07040e1070115224001030b4880003052120b00081c070201090740e83c0d242d0000c12001095030f1120151000640e0407201d84d4819908513070031803403e000789030500c1020b00d4100a03d03868440018 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 933909199 1250 933907949 933907957
    0x303040c05040c090312020a03081e0c160c080718062402030c010e160e10060518150d0b0616020d020f18070921030e0102010f0609020d140c 62
    0x7500c40ca40c1c40b00d5410540380141400c8000b5500643c2a0001c000c01d50b2010f900d82c00b500c032049000404500000b0150020410000b2036010b242c1c42240f0706681c1d1641d4120103a01403100710074109140c0024000194a14000301c0c050035058014100d900c2c80c203d0700084c100c00c0c00e00003848450802c40c0070f220841036101c600200161444d4600500c06102c6c1060f81584945030b0341d403009509060f18500300010000e04e02c41c25481100694504c140e80d8808030701e40c0141581c01141c0544904c804111492190000c0c0c5030402030005404044000072002481e501000d2961100d0300c2000300b8000828240781c0b203440c02205055030107900d4444220680b48004011620007403040008412040030b41d01c40c0c00d50040c10b460003030000a00c5100600460113a424116a40030007d28815800301d1441c15511800f00d4800d01d1001c0008805210394054611941d18000c0504540d41d50f40190228070050007280002c02000c20b005030b44440141e010402d40f01c120300005c0c00010303010b0901410a20550840b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 933910449 1250 933909199 933909209
    0x7020a0f0209190609060509151c080910030506090603011401060302130f030f02030f031306270605040503010c1b03081902030c0a0909200a031e09060506030303040c 73
    0x30b10301d83c1c0c0d52018050a80602d08401202c080c90b098002c100d034241a40000142c4008441e000b031581d40300714402c005030102c90346542e04901a10300000d40c40801c500d1a00c5054410805241054407400119007811402050940002d0301c40050100070305005500e2604118203400911400411034140c802420041c4154030803d640050025020300791212440043c094621030400103503500e003070002041110030800e070701c240559011032180f0303400081101d41003a14180c0022107149080c00940d00840c0740a09444500701090560884950501f01038000e0400c0380c45081d207440c2481d09241c01c441c06500742d0010300107000801c0504058561204644560601d054191940d400340e12147d80f0701b21402c074103201741c008824410040e0f149000b0b40800da10760380e28004216502c40c81d000c1070361920140e070b02c80110300780094604006113900500c0004c1d0340741000301d07800425500d1b01000001c4281100041680c41154a003084058098103801c240304900a60540c10a07840d00807030341e5654420 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 933911699 1250 933910449 933910459
    0x1080f0a0b0601020109020a14040507210f0209090f180f1c090e0709140a0e040204270507090f1e09020a0b0a110f030406170411120d030507020a0f02 66
    0xb802a0380300f50004141294040d14003000d0039915818500c400310707100d08441c0720b58106800918030a11803402513182d040c02c00c01d0005441c2c14901800000c0ca03400c80034011f10f1b9000c101000050307e038441024012002403000080c2c0f89402108200c00f0800c1844010280e00001c10910440c20002404103c41200d51041031282d045403074103607940304c51a804425200300e09420000840e801101d1103080b82d0303050404501c000d80c44000c00001e03d0050084003540300042002c100541020740c03042c4017412220b68072340c040300100442c80c19501c07103500c42107503907500049041c042c40d00140150580944501c00a00c0f81c2c0d141107400302556020b05c02c03801c071a00e40d180340740c406540c2d0307a0700101c0042555041c0aa0f84011451005003074030301f43d0b0142a043e00c82e100421510b400004115001c8076050340d074141031500f103175800f00d01c030070b8000e00309640c494184050310403d99107040c510303640140308c0c000070060011803401c042d080c0e405c0203080c4d4081d9042142e8280120f0070707102e14200b140e541111 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 933912949 1250 933911699 933911701
    0xa0806030307020a0f06020f03190815030f030403020f0901081213150302031503070311010e060c0601080109050f010915020f0d060303030b04061e1e080a0b0105040501080f0a0b 78
    0x2007455401000b50207540141e80c8000007401c041540d9407001550101d60a50700791156220f4081d65a20480c6d20742c12800300c4c0100c00318030043c4603003d61038000c0d9080c0031a6030f040109900207440d141242c00060303241d03000000c2c100300310315042d45009841c54054403400003540c94010b43c0c90701c4080b144002da040d1100001c2c00000101d60301c0912002e00f01c0d0400300b0100d03071244980203009400454014040c1c21034403900400b1840c3c005542403c603a03000c4200003070300861b00c004403507289415a8007a00400c040c8075030090751a0078011640642084030001a00c003620b4100340340303003552440841c3c4e0300f80d143c03803512004540c204140c040c0c100207021025964007020743e801c0900e4800c0b84191000c1600d400008020564144c00c44550144110740c14010591545254910100d80b110300c4079180315841c4003003145143d003664001040b90455203d103191070b622504a810030343e41180843d500809640140043d1810784180c0f07000d00851b4006000e400404c2c0721080da0350a00304005004410240 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 933914199 1250 933912949 933912961
    0x70f0e04030c170c06040b061f0315050402030c07021f050a140c0d020d080702010c1e1110020301181a011107080a2006031b0c1204030506090705030c060a08 69
    0x1202c2040d40b4212040300c582c2d158903484c0c0c0039031905c5007503030304440d4800001d020038658030b40b00c1c108640303828151080303126400c41803500b039000305403100c5d172901c0411700d00d98001100c1d5034a10107144581800542c160340c607080d44c410002c03040230076108608000000740501d0195648513056403001072980c1000c01c51044692035440c110b009000000d0220310920402d011126404170b0b10141c84496600c40c1406901c81e20300aa00780c4154003403120003d10188482281c02002c9a80f02c4c02e01d0004e81005421085000c0744030b41010280383d000e507081034001004100c240700034494103c0d00c4095260400074812002c10860405440000242c1000260003e900b9000390030321030b0100802540d4100d6191141c60302d002121014a0100800ca1603020040c0011034149482280e11820040c001240080d41c40d51091910350004201940d8522400002000c20b0f481134004001441c0100c0c0286030031b01c1c0070034900e4a041c946d034100074040d800240000c4101e849400688000d4a102d082c0782103e80e48034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 933915449 1250 933914199 933914213
    0x4030b0f0c09040905030a031d0c130e0706020d090905012d0510120b09010f120302031207122315010318081b030702030616020c21070f0e04030c 64
    0x1c80c0c0c0095001385422412020020000014600450aa10103204094103000313019900c1e50819404206034000d52400c0b1110300d4074030115260344c0c0c2c0c400c000140e10030905c800c2600c0c0074866000080903a2050380c81440980d0400707228001000400c0c1c060000c3c1d818500300085071060b83c002403414110080380c0e054580829403140d03010b0b0001805400200d040e00b00002c0c05c1240348032018a80510b4002051000c0c2020444141603c80a485800100d40340003602c0380007440041d000c1e01103000500509450705022a0f00c5409144555603010990010001d032800f01c1343c1d0b452290041d12543e071040419650140380c043c0c0e01c1110b0101211010705007100680150298550000030492081b41e030b041080030300c1010307004500820910300313200740c91084d4142c3d0fa03108403800698550702c10000141551a0415541d40f0b102352032068481c0007a500300032407002d180c50075214a580e8101c0ea207402d88000c04020240040080c00c004051366450701c48400c8030b03c50040c001404001014401400307000300c1c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 933916699 1250 933915449 933915457
    0x912030512090120070b0601050309030415210212010303030b010e1302180108091b0f09180c010c030903080a0c1709030613030512070e0a0e150604030b0f0c 69
    0x40c009100200d1611180c80d60003040c040c9820401c28062941114085580c0d2069910046d03100c200d40c1c02540328100195000d07040100400042d120030030010400f0240341101b08440c9130703180c803104403880c01c51900d451168040c040d9402248d105008490078040c0c1c005400b0704503501401d00280b441035600048400291502d8465004034400180021052803903004110040203426541c110b00503120044a05c5031007034480b01d0381ca41c030a500131401402d148964150145005126102c90300b14000480c043d80c10484100007540700041c502004140140714805c2005402d2810078920f4425a801401c1031880f40005003100f00003140760703602c040c000c440d03501400c0d0b00a200b001d04450140602d0010364824a1180e000c0e000f0140841e800700004803482001580c180c0b141c1c0c2c00e0107002c0004106182c0700804040420003164908845910741c000118007038000596002c10616000403450308011202054034003036107003000308101040c8a41d44440e040448185100e8031a2102c002c01700386801 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 933917949 1250 933916699 933916717
    0x2120304090e0313171f06031a0406050a050c07030804060f020403081305010201020405011d0f100f0e0619050d0e03040e010302010e040e0c01110f0d2a0309120305 72
    0x201e485074002280d000040a000340e00440c8080b810016110710200042c0b00303107010b00214a90001b1015120720b036007155440e41c10128903100284640d52a11031240405103050700d260905545010700041c4100780c082e86a01120b150018007403820942c4008006114081000e0100510701b00070804110581d0051441482184425526103480c0d0401201c26809210012025460790100046650060080c2c404a810586501c0103003075203a4499450a002e4000d140c2c1e000ca501018841150b5444200891100c816600c038856840718880242500040c2c2d2002c92180c003050015131101c8503c80810840703460303185003083c2c0304e0141d01c80c00e2028000414038210305000124010464900d0540c89504030f90003640c544d48440482000c0c4406ca40110101e0203007504450100011540242e4600c180320000c0c100700c0781742d07405c0d0400541c00e00b041c20100800094503682c0d000c600c032039900021010704450320362010b0185090350f400b400c48a407500c02d0b841c9240c00000c80c441030501800c01d48000305 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 933919199 1250 933917949 933917951
    0x2010201060f14031005060a092304111507021c050f07060c06051305070b030c040f08030d06060f02150c090603070f020105013002060c0f0705040b0405040506040212030409 76
    0x5469100d004403042240e1000f0b07029114003240d184010342140212030040c280030f00103601c01414950104060009018040b580c810881d2403a900352644420b0705100d0741c0180040707051400f61401b001070706c0440d6050400100424081c03403006da038441c00a504030040d0b80c005d842c11680c05140c058100402901d50619601828000080c41a04801100301003846503400b00300c255624403039501100c040344c1c0041e00c2070b40806800d10102c00a44011764215140c00500750a1a5603000140450314180c0c12407007942e0400b188110301c410b000d024070f102620940c206410510f00c0000006c1d5030390701c0414800031800d1114003084100c24101c045030240c403805040155289401840034000705a4030507150010741c601400050413000c1d071804100618450010741d1250042c0d400b001c88014801401a684200c017002600e03404a01040408407034074002c0050586589040100000c6442d0f92034020b0040c0d041204220008002250b16644168115401c11187d0054a8407618500498100c1e00c11a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 933920449 1250 933919199 933919229
    0x9060612030f030b0d0b06011409060d02180a0b030406020a090315090c05030609030a11030c010905100b01140d24080a02210c060a140406170f04020901120201020106 73
    0x1240d40711585018446040d24107001e030700b00060500c440c5c88032100c8003800150064003c181d4035032080311200f0b0381c5103007640c0c0c40b402c0441c5540003508582c003900a08120950000b0217418a01d242031082500441c01c840e084651490010b0482041c400244000c1505a0018646011500940e00704003d1034015002010305440100e0f8000200340051041d030ba5000303280750005c0c061500142103881784103410b000d14241200301c001614100c02d1414811050701041c082e4200241091154005550003030700184415516180c80c1c2048865541485042040d01c1311405105501c2c2c07002c640400314401000110f0717040c501440d0303410360302420811544607180b07440014400760000d03111081038000c85990398040030070301450807082481c3c01e03044086d4115030204401894030402400900486083c0000000c565080081c45a4415003007480858900c00400308000405842541d01803072130700003907510342801d400040310b0800510640c81c5c0e20b1064400e03a02164802e401c04402403100a54052036 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 933921699 1250 933920449 933920453
    0x723150d05130b0a0b010f050702150f070c061404121a0c03100e150d0804081015090c090326370807140705030a0e040e0a051009060612 60
    0xb40303070085000395200e0300d9803004900549840d02c2149100307030050311010400a998401501d02d5040b80d01c00341e0b8002d26803070702c0c3c623041c034044401440084c25501043da0344840614018090704030b540c02c490104082d0061003c0c14404007421141a22604461078050031000d1405100d1182921000680001100184184030464102450250019800120405481d0000b1084440c0704903600c840000c0c62064030501c40c00e103030320104060385c01840080e01d044c4c4c40301501b0b498143c0c110200070707500d40d5402104903a101c99841400c05095900000d00c2000301d00a0001c0401c0c281d4000606200a100000c00e40b01c1d000c1c8901c0c0200c0c0801400b003507150002c01c036111505400702844c0404601c141c0300488500c00104510040c0a256601c0e841641c2e11107540c1100d0000b1941c032154030140041040c4000720f802000646a00714141d40e6003e0040c2e054801c0c0b0090f1100f080d0003240710b60006c8040d40005c0c3c07004c942c4080c00303052800300090200c0c4a05001d00a0580342d84070070350740050b0000b0201 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 933922949 1250 933921699 933921721
    0x6062430090506150612040204020c1b10090e0a0e01180501060504050f011208180d060c02100e030d1a09040f0c0f051f120510080723150d05 62
    0x61580590103943c1a9541c1c03420041c01e034050604e0156011340c04020460401c0c000100740780d000342c0050801410100c0242c4100d24003007882080e00c00881c04886050071514000314600e0309000c051510000700740c50040b00402c00300018200d034a440e51512030710082c220007507000d411600840f040d0401d01d031f15203091aa00030b144a0050701e000c0ca0601000400200c4d06826041c100c0e0100300e010107000416071145207c0340c005004c0030041260b0580800744568800c0d128000f0140284000201c1d601c088030702929205401d0705800c501801c3c00c0c541d1001501c08001d894100441540c081000b0318450740203070140b051001090f46c041c50f10804d000c24001d454034032004c030174465000129500d485a02d0010390b0201485050751140010180d1424104d0049803001504c5490070708903820100d45005005940c000c541071a1554940c000802584104102c1c40c3c0040c0542c51105164058045031141c1b00940410f09502401ca0715482e81c0038238682030121940d00c00400e00030417060400f1603610b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 933924199 1250 933922949 933922961
    0x1e01060306030c140f0d110901170c0d0b0601110f011d122d07020a08010516080f04021002071a0a1d0d06200d020706062430 55
    0x40d4000d0004180841d2034103090138510a80a80103080184480e80c1100b006210b0f65204000c4070b1030b8407140310300c0015440704480540a40003900c4036548000405130200d141451600790103100d20040d640c440702040419a180340c1044080c130b4888001640c019466140030350b4040e082501d5172820b115903441e086090403825490f14101d058a590300304400d50301996004000b0307074240e09030911054212804030886400d0101141c000c6080c00e10b00281c00280b8201550780c08001c1d265100d0040100075101c0381ca6102071080c090510030200d040001600f20500f000a01c000e01480d2020401407805008009420050809001014811a09800d885001d41021003000081948101c4c1d0000d0091003281d07a030140720003c1d040350f00c507074415220103025045081d8842c2d078010a1023640c10301240300e8001490030111003c1c003d80e03a045d0a241080848034075501070181d401c0b03422120503219541c10701000c0c040f405850400e10046441c0110341c4448040c10380c3c84002140c82e10700e03028811064102d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 933925449 1250 933924199 933924203
    0x506040f05191a060a080f01090314041202040f020903030c010903021005070e010810050d03030212010509010e010e0919050c01080c03090a2003070e09070911030f1e0106030603 78
    0x14075000041c0049003070405108600040410348024202c10f8200c100f04901030f40850020301000000d40d440042c82d080407201c0c004004965180c0d00617000345500048440c217a010b8a148092605103005020040407442c118001c0c4100c0e19443c50f02c0b4104a0340c2c044e5160a8002011b4a0350358041c210750500800d00302c0812400344c0900013024151140912074070340b01e000c003611001f44040601c40115244440200f55030358007449030001003000d8444101c01040ea91190300c0c0140c1d900643c405660810505a218034070803504040140552007007500000d044603124116030300d00313442d10801a41400400f413505803071960b0013101d100c1800300014030b004440d64207884000164846030b00620043c4001c4401c1038040c0d01a00c200000120404400c40c696800310708042910b51800f800681003510a600c00802d10820000307105d00c90100380082001000322620400c0b8603e411480101240402410b01d8041d05280d4002503040c000101c5885c1240c210140300b035110740c0c49000260040069002c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 933926699 1250 933925449 933925453
    0x216060e07080c1c0b07090906062106060e06031308131d0f371d01020304050d0c02190618090e0a08071b0621020a0801170a0506040f05 60
    0x40403040e800c1c4100c0d1100c0d140d80e04813020707060301d0150311601601c08000d8120403c0041203480095059814810000600361541e244240079504c1c8c0c1c6241011840d0320004000e035458840100502900700886c02c0c111407054840d29100d07592180042d143c05001e01c8080c1c00d0b80000119502581030100210060f5000080100b1038038003032981c80241610215285841600040c0c0800d00d52040e02e64006440640c60a001c200c6280080c00080108a403801d401e19158a990091505200080c0740b00642c0d9000c100031802c40c60251509661881c04034030a4040c008089586815501d43c15050b070421851806c00d244601c0d640d940041c58010401c0f03450207490120702020400d81290300031045006c49100044c120051142c44441c125404207070100e4211040c00708510880c410045204028401600c44600b41d5440313802101c0780c035050140c410f400070310400000000b1074012064505440b024103c980076625019406403510440e0003000e4641e1150b403041204201103c540da01f580351044003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 933927949 1250 933926699 933926713
    0x5180c1306032c0d110a0614100522050c220501080907030f080c01090c0e07031a1f0e060f0d0605100c06020c07030f0b0a050f07050a030216060e0708 66
    0xc803d43c82510010303070020030b60824800c029038030b8480c182c00780d6095084030503101c08105980e100340c2160f00e83c08000901c030391040200402c0d5140703107842c3e45c0108401e03100c824140040790780203075150701050514051035607200d01141851541d0415240c0e0340c10305c1c0c025000c11a13040d08a803034140c3c12500c16a8001215000001c00451011810f002141c0c2d105412132032142c000d40d5895082c3d00806000782943d036944034080041158039006e1002000a00300440b428100100000c050315070b0842222014a20b022104180d0b40b0340c8150007a5080c4d900c2c00491440f60f0a030b01c111499002c186015a00950200da22507007540700500900c103000c030300301d810001c49a07a041400786058410010101044191000e440815055002002c0b110041e030241c0d650292203907107001000b030806000b520300302400c2c03081010307904031031144c25001034800700351001c1d80c5450301d8010007034800c802d5502c04058010400c5503a10600321035000400703501c10028004c40041184e070302c3d80c03291103218581140c4034100b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 933929199 1250 933927949 933928001
    0xa0303021b030d05121906170609010207110105130b0301080705040f0501032f0a06031a010305091c09081903021204050607230615180105180c130603 66
    0x22568183e0ba0380751166810404070b00d500d400a204020010060030300910703214008001c8602c180400340284040c21440a440c51400d18a0008004c1005c4040e0703104000e11008540300640c0171600010034a40310303070384035109845003601d11101d038012000d5003408400032a81c1840400c04800342c07001950100044a0407031400ca01740c42d400e02c40542420b100751320f003003544500c1480084044107031000d034103000002040851000100f80d800700000960f2041c0500e00e140600d4101ba0740c0035401d02e018049030605913002610340180c400d00b200441d88802403090040d00540da94001441510f089e03034035003c1100c0000011030f0821000718018087d002d000e210644c92841660141c3e07101501440c10001c02e5a41c180051505c015454040c0c50b50f031011030303619003040211510441000317012502003015202800126912103c00c1c0d0300b40304c01301c1c0051060341c03240c1101074104450103044041d161102c5110251910400b840035401404c1801d01050064040e00503040060030408400542c900340307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 933930449 1250 933929199 933929203
    0x80105120102070c06270303170132030a060911180f0103291302100309050a0209041b06080f1003030507110112020d05060306070c03121104050a0303021b03 69
    0x400b1008044184c6240c0c18010113205941084804101c45140444c24031054003200c064003680e071080b0b0000f8015402e0908044441524500400e04036031020640d2100b8910a9803c0d20340d80050fa44542100e4102015580c080042607890758204004016510a41c105419039510401c52940105241c120321036503810740c2211103104081100203008141d00319a181030f41c65009407414161002c4034004403c076140044c0c1c80340c0c06810840001d40c0317680c4051051000c8244214048020306160002076004150042041c0650603070444880c07040e55584e141107400d6040310411b100c2c4283c2601c0d008a00d443c0c101c040320340170700c0501700003d900d580c070740b22001d51200040c04020000360342800280005842141408441c0c881410a40544550440c071941243c10520b8004000c0b515030050188909081c884141c200a840c070701415804500d840c0540541c020800007001141d58502a03004159080190703400b405005100741009503070b9080c002c2d40e0700800000d040c0000d9039440b03520407078030340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 933931699 1250 933930449 933930457
    0xd150e031908060324061509010c0b040f0b1311031f0e01060801020d061706060109030b130609110108130c0603020a030204031b0f17030409020304080d0c080105120102 74
    0x1a006200e1154200c8210840b551040541000e0f014410300e0075071800d408000d2a0406030b410f074000102c5461405030104003508060748148400801d00704035110a41e684003031904202604a03006404c6510f031454000c42c940134512000d8903030342c080018040333070103100c92081401700d0181220960b00c10f051410107443d6424001c1241010350f441c0b0004002d04c0894000d48141c2006400000790556150403481c02d9a01a0840c5442c1a07502e0f2400d00c0004001106018040c03d0f10005068510b44a40040e001d0030540c00302500e0f080d140c40025000c0504d1030107680b4510ba00043c240b003c1d05052800c030000380707160421580442d4a610000300e60141c2c81d401143c04036000000300307001c00d01e0120103400a40c01002c0410415408200c04800b0440310110030035000c10301107100002c0c07450442d021020302c400342c000494000300c001c140d01003040c000094805039180c8010060352074603280341500403845507000b10305140b0f041501070000c4a420403141412500c0a0314407004d42002c074130105080f403003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 933932949 1250 933931699 933931717
    0x10f0c140a0c0609081b0d110f030d240303120b04091a0723030f07021f0c20070602061b030a0e0705060d0515040e031206010e0d150e03 60
    0x204407030820200e03e10390011081030b4010040f00c1d2a0070401d80b407410002e014035011402170303404140c1108031541c0c0044044c1c800c01e10f0340054a0100c80c5c881000c0e80f20b00c0f40e00c14945480f6203904085400440c040610308165015401030305e0300302d90328600a00140d041c0c450294085142c68000075150500d806211200c42c3c0c4242c400c10741880155040d80514006410343c010480d0131032107003030507240f0351b440b961034800c1d22500542c891510044100354100d004003140704540040d030410480348030400d0300007200e014112001c126440c09980480324140c599040c400e82c0c0402c40c102c0200070401082c00c0056030190790a44860b070381c80005050b503000b000c081c01e00c01c0c081c0400000300500e80030744c00b0f1481141d4441c20340b2401a1748000140032508004284240d040d81c1c0c070280304006d0800e0501445030301c002d0741c092248800645560b5180d015070350b0f0351407d800c100342c0061560781c400c1c0d100c0e26140000038001d50151100d4140b019428911b08844c1d81043d00d00820b03800404030001c04d60301d40c46 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 933934199 1250 933932949 933932957
    0x504060c0c082a070602030304141612061407050702030d020c0109210602190219082b0f0e06010506091c0f02030106060e0102160308040b090102070305010f0c140a 72
    0x3441c495659601d9a58204440c0f0940804854801188400e220240007040d40c1c0d4002c40c0c80e810305092a282c0034040124034030711580701c40307a040600c0083c0c0000d48200d41c0103c80114081100381883c40140031010b0b0800c1f90030417000100143c0e20740120240080714003d5040b558400300380041a84c0d5040411081c50125a000000b0415143c000c0e40c8022051031808908542e041f0642d200702c103a1f0001c020b9038a89a4a280d42007040580c10051800400b10005800000308401d0700e41c00b10610a14158414410340c00820b4131f1000d07c80c864550941d01c014104014101040c4e40b090018070311002c84c400705028100000031f1a01e002016036071500f000501c1c111080e004110548010350b80c6550894010041e01c0002000d03940a100c4c1d50000c107070903140d0700c4c032080d0001c00083c104807000e803203102c0d0740e0130250062011844900a41e4152007d8080380c0d50b503082c028005038a06030213540001d00c950b0801018443c0313000d960300f0035104450b042d143d140310340340c6071170303060b01c076401030182d400001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 933935449 1250 933934199 933934207
    0x705130903030204080625021207060f2c07230103090f21030c050705100b01090b0403140f0a050c040203060607021009060806040b0d02190b0d0504060c0c08 69
    0x5a02103500c840d00240c802d080052403c1d0383c5004041c1000402c5440c43d01022200030084081a02060310300764500c920301c05010b8030221455041d644e4000c2000142c180b0340d656000396007201c003d40c0711151070300f41080c030b941080d203407641c0300d030321000c0c8c0184003024038091100c001410143e080c003681c400035804000480c40760080001100145162a0180ca480c0825004c030804100e00342c200041020500d40b940401c0c080005000e0b0949642240d401c00b0840e0400a500c0810404640701040342e035658800309000c1c0c1e4013401240d01c003800d500310100d103910010b000030400454580c2500d01c0c9140c1d809444d4030740030011215484459040c40607286030801c003282405845c01c0d900441e8001001402c143c1400119008102e05090a0704010041418054180070180d003081e01941e00000c100c1d0309005084240004c1905031042c9d50009003d03010051611040f030380c282c807214000e40414911113850b0080500800040d040c181c40968095107010810900f0381d104032224080c01d81c0140c5554a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 933936699 1250 933935449 933935479
    0x120f0f05032b0b0d021e0a030f0c05270a060503030f09152b150b03040b01050405010503120304050309090420040606051c0b1c110f030705100e030105071e020705 71
    0xa1003001c0004003680c205280c0c0c0c0b0306d0041e035a03500c652024500807101c40032802d40b00d207410760060f580e60b003201e0f10403480204460541d00b0719002d51080441910086102600c1e081c0b00ca8002c0d10403908090b40c0360102280040c015400603000c1d00080d4011200014846000c468000b080d10030407170401d00214070314002d29040345822502081c0f4461001c40024110003a001310300042509810010000c42d00105000611404032035060140a086808000d0307949000c0010f9aa17100c10226910600300110004050050500544402560240c03100000b0b01d41803070245040992495180508049524403038064282032066100780c2d0415141c01c1d14105180800d5000c10401d41003220344d242d00c0300001c0300d8540300c24201d51251011030351110350351000d914140c03c41040840c00304c3d0040000500c0c0004039038000440d001150429140c06520349030b00d65080344c100803502d00361609982071005002405610060055800411104140110f140401d0490712840b5520545500c803074254113401c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 933937949 1250 933936699 933936709
    0x4120201050a021906020d2009150403020a030f1e030e040908070606080105190e071406070b011409060405060d080306010504080f0322120f0f05032b0b0d02 69
    0x7890034142e00460340c003245a041403013003894010398121600d170780124a2014041c0c0602980311000c001c1d8900004c1070208460150903030103142c001d14400c3d03040e03182241c68100d02400301c41c003840e0050603080000351030341849c40030b0034802c09040b1140012500301101001da01c100c0c0c41d20a66040d0383d400c2c0010f03070040800019040d080825503400c0e104104e801c001030a0b910404000300030100010445260400481c0d02c00300444200708000da042070b040d031011a00124020041d516080381d9144a481010b021034100d009284008000580442c001f00f80e00040400c1d0135401401100e00b440ca6540e000140f009a031030070741b0b030103400003480c001410020b4a00750265500c03100601d005402c2aa60398241341c0b820313409013850f030300e41d0304000f81c10990605041d0165601c5004a4080c4e000030b49072003201c41c0b04100803c0c015068021003a000c0041000811241d04155007200440e40c8901000c80c40340c0d2182c2c10304031018120110300340141c0c10070310213010390088000e004000085c024423035000e000d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 933939199 1250 933937949 933937957
    0x24081c0804110a05041b030b03030c250b070f150b0d0b0601260117030705120705031603080a0f060810020c01020408061003030212190516171c020412020105 69
    0x59404003c4490208207601d5910800801c031140240401c4004e0360608050216801d00060307600903081045107280075040041c03115441454512070f1400e000d03500d114400c2d05002904106441c1d407000640d8410300090080c60f40c0303414050444e40711000581914030048031000c2a4040c0c0007000d5040c820081030804850552000041c1850780204585000c80f162081d000840c030000b201604006001501c1103004d81c2c0d408400513401145000382a0311040d503143d1503540c20110b00600043d2000800c102030054408808212600840d14032580c0703005080880100c031441d040d1307464144401c4410070b0b10302401b000c4910032320250a054a58008001c041c0d4090425100b603036400300000a013080040000340d1084a81050058449042d0b28000f4240324144960180c0c06c10188280036803501002d03c0c9000300511030400d00d54400c0c031141c80c44c10104440b0300c054000301c5400a090110382d60807004001d00c90742820209041b03c8561405402c0740a2030103114039040c500c070707814070055018400078 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 933940449 1250 933939199 933939233
    0xb0a03110105071a010b1b0609150403110303072001060e0c1806040b0702010f02030a0e01050313050615040e0a050a03030b0d200f0f130f24081c0804 66
    0x10b44040e4544140000f0b01341c000303038440c002d10500060b1145c440d422002c0010b005840b00f030050705880c10404045682c52690484e1111042c4101d0046010140128050026411994184c031b44901d090a00030302442d6149400e081801514001041e8260061103100282c039441c500c40506910b41c0d107412100c50300014410101c0c01c1300d004005c011030b40c8000c0507000422900c80015510402440010007482c100421401598802c1c0320f108991a00420944141002840d000b0f803690f940204504c11210307452800f40840c082d030b50500088482c10850310300b010700261070602600848c0b941c030b0356940403401c0300a010707600800a4034001901c250440300ac0081d00400c9181030b0500c1d0f0311051000c0001401d00c540e5050300305500721660408080450000e00c0c215040c0801e4000203000c190f0022031407441d00e40080e43c0d8200f0034041c2074150700c1410501d49100e50b1500202910200c4c100000700344c0501c0c01988226030b820700f18202868080b61300070f81e459803140240d0700d480d03584ea2003d0394101d500d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 933941699 1250 933940449 933940463
    0x807080115181716031e020d0f0606030506010b0c0c09041a0a05041106040b0901030908040f0e0910020c0d050f0f2a0601060e01122301090b0a0311010507 68
    0x30410402c00c042000c8064a11100c03c41100d210040c011440c0c0681c0400d8074007521301981040010519003402c4d090445040441585492064800a039607855600c0e8001d040428a20984061100c164085401d89105a00702d40050341c90300c0000d442c9018014651455500009414a00d41000342640b07400c6407144e4443c6000c5d42290070000018001211007244250366001000b052002c46010180902c2003a03c2c21440c0905112844889104042d00e5906254440021a04101c0031404076401402c02010b0ba103150383d1505904c1d111154140d40f401d54a104001c048a064906071080303540b90000720b0000c0c892a550f40c181500c403a044880f02910491090000c580d05d40034540050149060080c030f510021000045ca180c90015201000091a44001c0041c02120f4024440c10400349007400d060103003d40f03142e03001001d0001c081c2c280050110803d15100c1c14814180b0243c103840300d500b02804002807003014010364400303a1202900d08410480751002c254000c40041c10310900842d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 933942949 1250 933941699 933941717
    0x30b120a11121f0c0e06092e0509011d09060909010e030d0c030f0b010906030207020f0a030f120314011203021c0f2304030204020a200a060501060807080115 69
    0x4050f41030a8107030b40c07076404080c2d01c0c0561480428643c4204905240b05040c00c03405410800041206c2c0d0041b503480500416140c000d034401d101c0b00301c003218445809902d0000b40c0d4012450000c205420a00916002c40c550040e9062210420805c2181c0f4100180c45010982d0b69a0204100c901c806021004207550b00c010207030300c564060000705070701032072440081900c0d00c04500090884082d0000c0c50140703450410390220aa900403022411203e041c5001360311044a4000680e09645c0449015400248a8000010402400c00c42c0400e00c2c0100441c400c520700408040d001c0e20a11103400300041600001070100d10b50750701406035114003d10484000c5217481074080101624100e601c4082903100c510001030651080414074080c0340703446043d007007921100030701200380201d02009100720b4020905184581c030ad001d4200c0f10514003410b00d0103050000b0f100644910741d105003a01e500e824000003082d098015200c140c01411140d541c5681603107440c00c0c02c0d40b01d0104100500802c01d0681c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 933944199 1250 933942949 933942979
    0x3070c0311010f15350c0402040815180309093607080712062007030c060f020906160c0f0303090e060d020310050613110a030b120a11 59
    0x4401c0800c4180606400502e400801060b102c007500c2c07561110700c0d6a0341445020f00c04041d801c8405401701da507814000b07074103003111074002e080c08941104203070814404500000e650703030006408194103400c03440005064035099018015440c550118021560040103440c6081c10240303c0b159106020100f440116810307103040e02005c0701415112003144074014441c414817201071084c440200860802059543d144c807221640c2c450f2075a801500c01a60750000780003501c03110701004418424031041c4c95031560103140c0038106000103441691005d14080114503001d18a10840c1c0d040c1000805407402d203242c043c07003d90505526841100c007100c03150400244140642c0f240d5002c1c5220b52100351802d414558580182c0100a1a4900c17540814801c3c04c00f5132008640203540ca144940f011503a9614103011503c0010b201080815241c5862507880e5210b80f06409080240020b039030520401c4086020001d035407000844103a00350f0040c00305040010704040c01c0481c094009413414213101420 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 933945449 1250 933944199 933944201
    0x605040501080c12210d0e0708030c0f06010f09020c0705040e030a17040b010e0c090d0c050f04050705031302030a0614040c0605040b07150e0a0602041409060603070c031101 76
    0x2a40035440c0c40d88400000400e500c0c0491301d080c42c3c6051000100120000f08a505c40020030301e021000350754400180d20010b0f1207050b00100320600c2120121180142d4460110b030b500d0740079405511041c051452040a80c0e000031442c0d6040b14810200b8044031424054440c000b544043c10001c100e228009000500741c440c0c0c015205030102981c007958a600382440c010300010301c0d51883c0142d0f00481801c10001a40780300540b41503440c03c2c140405640e40743e440d04030992041c189500d0f03100710418004400c01485a8002041c0c0b04262003c88000c0790fa4800c2c80191001500e410012034004e000103000c410000c5048080d80b4001821900c0c800c2c0c068842c9803c55401d000a5403881540700b041005005500c0441ea004090624005103803d141c0f0100c1032150041c032000030441b14a04000c425001c0c0310b5001901502158025610002c04514000b00213511034401c1c00c08502988800c1000c40c40c0090100744680c034058521442d45e600c290048449150349070080f03050055482c2c4c820207003d02 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 933946699 1250 933945449 933945451
    0xf081b0706141801062402100e06070906170123061626030c1305090a0606020c0427020103020f032d0c090427060f0e070f030b040606050405 62
    0x2420740240050070540000c01c0c22803c1c001c0c03010401d82c1400010070906142e01003103503204020f1418000b0710300d8804001c0f810489140d0080c00b005090007903420f01e0b00004150140140c840d6140c0c0b84596640d1a4141c517581d010100b4004200100001000407161001c926600380c00350340880054041880c00140084c5c2200c1480c1c6c0c40070a2411050080001c2014139507524400e44c08407100c89800031a075401c95100c01800d0a000d44804039164030000d20058055020705401404070845180c4013451800410903486040010311403030a0003012414a803144040c2403004c143c21008a1a0011f070b01140044441400c9040507800c01034040e440600c1c03070246025802090011110401e1810314178140c003c61560070110300180d030248003461035508100e8625810558020811450030200e14400785c410001e42c07810001c80c0d11180d001c01c0303019170240d41c02d5603905e20100804101d1000c03081d0f4598881c010031901c89440352050001c030708000c65960b800b81c4612404207040b42c66001040903944 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 933947949 1250 933946699 933946721
    0xf02010f0e1b0301060f0303120f05040609060c1121040b030115030f0b060403150603020916080c0f0f0d090f0c0503210a050a0e100c0b070f081b0706 66
    0x1140349000e41941400c0e42c0700828208500034403d02d420005d008146141912000f014041d0b10703e100c824008003900562889400d10104200504d070500b051002380861202c12150f00d49040203100369503002d680114440c03e400c100034101107100410041484038140c44503000007500340400111511044011070280102c00c2404080366400b0402a0070b66149040340410141400b1600209441d080299000c903500300d02000c0c4044010f02034403000741100d800c00f0390810300d00010000d40b801b040000c035406451541d1850666660f6003002c8096004440180c1151481049200490202c42000e40690084210005160345080da42e00c10412640c1c1d000701c504a0848100704070a00d01070001c2c45100c0c002d1000c90a05204501100c2c0710340c0305080d044c1d01807000124000c1901803040c45010b403000d401070000020821700c2c0d040038081010a01048610408401c00940342c1442542c1c078a52509941c1c0359103142d512520071034014010b4903456204014024803030740340820706070300030141521 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 933949199 1250 933947949 933947953
    0x70e0106170a0b0d0609060b0a03231b0922120e041b030e0a0c0315050702030a080402150909040b090618070519051005030108010f09030f0f02010f0e 66
    0x700d80c40030310086002003001101d503103044440201500e44240c0181d1507a8004000920600303286061070003444c4030700004c0d400c04141e25000c0204001000603a052082c101c04811403541e4a610b481c0c0e031740803074107000204808154190312080c180007101e00e400607107406440070440502c200075141015801d0f0140c98030202c00d8072a603249a0484082e80c15040141c2e0188055500a00003003601c0f2020a0141d00701652841059243e07a0207004460220b0740c448183d81c1c40f141d0b00c2c14480e00701d010000300244203510305000300310440d000000700d4203001e0003510380c1c1a59030b607235408109401c01c1ca21700c0801007503c20030088200e65186a00c0c0780c419031103014068428141150b07040c0c9054401004081036500c1e44550780300c50840012024100d802c1115008070252281c80e0160500020f940b2094008000d000000040d0350820080d505842e00007000308860000700d0482415940c1a040180208100c884900500c40c85688140f1944026000118031008941c10444c1228202c080504180d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 933950449 1250 933949199 933949217
    0x314030a03050114240408010f091103010209090a0b060910020d03060b04080a20150a020105070e130216080318060907060801150c1e1e0804050f0102070e0106 70
    0x903076054824507014000044003211603104001c0810a03011884160031022083d02401c803100e4240340007200c01500784100240504004940d1100282122503001ca0701c003044401052243d06052090780e030140401002107d0b9074581c810540014100051020b400420400c0124266141e0000c4150414102d5009000c0d110750766200400f122459006480051001c0000700300a040000707951090a40105403110002e8200000c120074400f16440309400800d003020b066217001d0043c014110f08134051300280910355a03903e084a030410302c0700d6a15485400d82121500f142c41681c0540018080074060800c009540c0d210085160000c6510f01103100700d005a1106448040c0290f540010140c0d000306846070428001500d40b600c140150070300040141001b60141f8810717000c480b403194001e19095144a0b680c50b01440c584408801641d00c0140b40036444902516000c0d056942a00a0325443c102424070003003000c002030304c1d81030b03e0462140b0580803074886942d070781141c000c04003501d903445c070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 933951699 1250 933950449 933950467
    0x10c2109150f02100f06082d010507020d030902041e0f180c060c0215070804051005092b06021209060609070e0d0303092003100b210304031403 63
    0x81d40e1240c803400c100b000107811104040607000605040208400600422408400804c0c8801820103901c082414030559441444040311118100d2012402e003182c15921009810300d01c0c00d8420654950300107900550409000c40d03c40e42c040a0190310017000807842c18920301000b0100000540d001d441c4070b581d4600380b04880038610409000701d0664071100c803681da65031940b54251003d44102d10502c4508075442c4110740d5503421418950081420280d04d60042e0b0400521035001801180d0040a80d0410f12034036074050004c0d6400020001c0040b28688020007202550880da00d80499010140644850010b41c403800507000c84036202c1da10303a0117441c040b41c00d1340c43c3c44400b0b040030703005408400901204580c803000b00c03030404400351840e1a540413680340c00c50080400d80405816011840b081d4108960340c1c040d0003400c940110102c1c0e00c075014000040048401003040d05a1006504440c0c03d140405100f111004240c60b1042c1c900b85550b071f46070076810303207260a4001203a030000070354100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 933952949 1250 933951699 933951719
    0x1b0a020714010f05031f15030b03011805031b0c0a06020307060b06070b0c0c030f03070221250204020405030304060c0309120308070c2102030405030f0102030c0405010c2109 76
    0x50422007407070802c0ca5075881c9034028101e88806014184603048000c40010740c00101046d80000300b42c0146001c02c40c8000f003100900a0446101e051b2103035081c4031443c41e00201580e9403c80c001d0700140510300e403c0c3c20110440903600164001c440902139800e145106a03180304005004101c69005140c1d00e83c02403a041b411104001841d42c400c0701c00340030000205080d0380500d941300306100749003542c9050005449195001b40c00090301112400810050082c0c4d001c01c060107040980900305c01c40281c3d24034080c2150250003449038501101616020401c5201e10120b0b25140c005800107207426110404682542d1043d081200403403203511090042681c0244008010b009031f0b961001d44008a55005258010291940c4204248a1010f80c1481449445141070109504007416a004000c501940f40d40262085a12034010110000003046042c002c59100700540802e0601d0b00b030074030b0015204e1003a8640141c84900c00484190130b00e41c0d10a00000002d4115100c03c40450701e4810791503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 933954199 1250 933952949 933952979
    0x3050705062503180f06200303150f042a020a020d0f02012105070f080f04020d0f0b090309120c13050901090510020703030c02060c0d051b0a0207 64
    0x190040c4000c0200e0342c0d2030a0100d104038106005010185212440c604040b24903044201c90f280c0c5001804c0800941d4240c1e6440c420229402906c410b10501c0e06505801e80703c0c254075841c440180c00c00c000107041c1c040e01511169603404010301200400f0b0049002c90100d0301d07089101000310052003121036040048034004411135038a84014600d081d0594041543c1041c03443c001407550b00f003990f410045a000da54800c1080c1a500c01f01d402c2d62114981c05c3d4043c1c5002d45a01d0041b6a0080d078040003180308112403072084803d080308450710f031990f070f081c007903500c050700e01c207440c81016031252200195134a41a2401040d002000315183d80c60030003001689220150307580007c2c0e02c4414003030035585803041b189945010f00d01000860f952407521642c054031200c940101030b8001c901b171a494101c0c05501510b11940a540d01300f0a6141c0500c060741d8420060360140c0b400708062003520051601d81d0801079022240c440358180030182402c403088503030003600d00b81002d030f0840c50082c00380000e00c2c0201 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 933955449 1250 933954199 933954209
    0x1e05060a090219080a061a040c0909051305120d0e030a180e070f030e010608190b01052e180303050c01050a15030f0f2a121106091503010f030507 64
    0x403c440742d140481c1540d4410300980000c0905450324054a6084585405104100c1010b03109110000000a0080c659201c900032088864031300000f240210701e24152030b174599944040140740d800075140914087c2d80164100d5103809484140c202400d00381072014210166560b118115103400b540820351901101d9044032216800744010400300e0365100503401117403041420009000c1c0c032140380103409051213801207902d0784076000c2140800040080c00e081e0385401003403410500e0b600e0b1030420840080703108a88541da41034030b0001030820b03044030041d065103072142816040c0742e101c006601c0078070082d0750098000c20004030340c1d4006101d00b80a0701e0750080c00c1c0301c0d080208030351002211822010341c3c00042e0102c0c2150a442c2e08111010350b00b501d0700f50700828041449000003006d0840540d0705200e4014100400c5400944070801c0c1400100690b40294404029030011301408030316040013403116445252501010000724500c030042d0302801c0c5200c1a038903994214202076141106035484 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 933956699 1250 933955449 933955489
    0x819060b0d050604110706050421020c040e030c03030123030d080403020d090302150702010215010b030405070f050d140c09070f0315030f0b2505090f0108131e05060a0902 75
    0x21642e0710010280c22681d205a00200001d0962279900740f1090184491246890303103e859104086080e0700090041c0010782c08640c00d0210001000805890740111701d060040c41d44240014081944011610110400d0602e403140b54414800006403500a00c10300d18400300f2030780800e120905605200f10803803003180f81031000400d807455000c0b40585c074102c46032032a90311001c40c03103c045a2080c001520031510420451496507110a54400c0780d81c020340381242d15102c1c1d00b80001d60358441d001da001c2150300041564805140603142d0f009295505038103550171b1b001d010600072203a510b161071a03004504641c0c0d07003962840918005807c44005003042e24605600c0001000020f01c0d43d10501c140e40d90103840030420b510b510003042000d000c00e2000705098507500d001102c0302c641c02000792030070200803101502d0b80744602005403584902515846004c00d0814650808500340c0009102d0020340040344d84200282030f01c03010305003101034460360b2240d42c650443c141540341c021829407480b85103900e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 933957949 1250 933956699 933956711
    0x120a03031e050f0402041109190518190510050603040f03081305061302061615150b090f030c040f09060b01020303130f061103090f0601060e0a03030819060b0d050604 73
    0x10f003440300402c00500080c421501c1e81e404a1100e040c40707050324008140a0004c0c0300b2184900412a5000424000d407401680d49503410710140a10350003180c0910141c107854640800d14502139805404010009500081d08010028080d01c842c00214403450107650111841d25091400404804000d011070100d550380c500d8030004102c021a19030b0704074032140d4009210398223500c0894054094954a43c001c141508002000c0c0240c61640c84240c0350740301d2040000c043e4501c04c000907440c940c050b1111104060000c401242450f040044015800908692148c90584006010b84035902c10b10300030fa03601c0f0000303001044064019281003890034009507040d468480250314082001c108058241450080e0300000d003c1540e0140e00d808400000d41680d0b4a0302c1000c46036200c640400407405440b540700000341c0c0a201d0b5000c130700d1444c1c009102100707140c6161401c44601e007019000d03190340070400740070700d030703202e80603c00d201c003c001c21040d40b0303114a0b1514a40382103640080100c0d000d142410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 933959199 1250 933957949 933957961
    0xc03051e0d0f05031504050117010c03020a081305120a120f02040509040201050319050f1816050d031b03091a0406080109050a090204141803041a09120a03031e05 71
    0x1d40c0c40d140d06200382c41e149880340d58410300d001d03907407017910a804c0d041490032002280200601c04200c1351200d00c0c030001c0c401150889000c8003284a100301c0d160001d00c50b2004645440b0700404e500b00d4071030140048400d891b0f00880300b000d45a0001485002080944250155040e081d0180003441c480e50302045090600d03001c04901d003900002c000a0401c10008009842c000e20000b01c03020140400303038204014a014801c8a26806080e03541d103100b060403660b410868000003c0c10328180101451206559140000b0b01100451003001103060100c101044200118550081c0803554002d94455175841d24040800c801d0b40126100b086101404000034405641c101906a0440301207100c0024650307200d282841c014898820000d40c0720f401c0201036100d40c43e00d446054007500014006911641c1211030440d0b50f41300382c2c4601c100d46400b2100700f005000c3d450018040003203002c0c01c8031181012400b501810020fa031003040300403d0b510b00751f4a003003001c903180d41c04141070b40c12010030041c1012 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 933960449 1250 933959199 933959207
    0x140717030408070e09030f07030c02040b060313031b0515010330050906040312030b040c051e0904060e010603020c070608070c1103100f050402030609030a050a0c0507030c03051e0d 79
    0x113000c0c40030400e1034130010a031269010002c4424040c4c900c1f81081c2c4070019890300811410259800768440c03810840410380c2454403d040303d00884140241c1c07812440c00c1d94096403864031510322031080000d00d000034000b0550910005001d084041ca050f070256040d46030840c1c1381c2c0c0a400041c04940142c0000d0350b0341c508503420b41345d819411410210385641f002c0000481520450300020122014410103850141e01500b0001c8403420450b03090016003841502160240150001c1441002d103589145074501c1c03207803004003c0b4407400390022480c2c81d15100510300c4902d082c1e0155001135030000d00d00c0b0b0f41b2031044c0300400140145140082032800d02c6a001004030100010181426070807204810300c558040102084103010800184005506001004000c1000311000e274000d01850001400c0711001100b1284102101c1d1504e42c2454020b44089070641080a421035246c0305944012010560744c40384c0307078011840b401c000e01c045942c90381e8540d005003c088400c0c3caa0b0740154807591256400c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 933961699 1250 933960449 933960463
    0x60901020c0a030e040603060c020c030f0d02070e0a0609022205010c1101080907080706180f0303210b0301020d0207030f0c020901060302160213090c120b160c140717030408 76
    0xd03260540d1380c4108000010000c0c07165501c01402145030002c5070300307041d401242042c0c00650850568440c002c003032400503203039105000d038040181c00c0030b201400180e40d08000f0300e3b0402c844580004006441c0e18816081760b02420404c0496400180c14403100c00c0e40d40e5441d8081d0800b03282c00401040f80c0c2c0c0c0e49245414081e00000c0c1403220f0310000a0b20050200310076002401d1203030482d000c0c0c130b0b900c11014028140b6020301030b182c0301044c075000c46c1405100d0030038400c582d030565036250010b03084c000b0411000c6a0003011959a5102d54040d0050381d0240042e0507000102d0b04016901c201c50315020f04401050f00b040018003000c40c1406003d40c1d0341080b007a0441d441070401594401210700308000e001d2010200940c0190b07504c0c0034214000a0707a021200c03d03481481d80201e2075407134403030056503842c0200c0001c00a03a094000500d100003401061201040e40b81000080d886032507440c2c010369500d503065038a099100003001c000b1031400c80c50400030510030034050742c03516040c82041c1d911019 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 933962949 1250 933961699 933961703
    0x40608040f03020c19060f1b14190b1905070e12011e0e060c1e090105210402010e100914011103040f0e01140d020f0112060314060901020c0a 62
    0x4030301ca01490905000344046803003c003006010744180038048142240c00110fa001c0e06c40014600202d144006000d9003038100b00794240507942c80816065900c14180c0c010594650420340034030281c0360003041c003005e840d1499910070951074140785050700006180e0b41080c070220402906040501030b1b0300c1d401c0944603851075425035210440c803920380300107805445400013040c001c2c6030701c0c1e606030b020400031b503c202c18540e80d000035151035840349a00d101d00d60140420f44a8103203100d0f0403040004500000a0884a8041c14500e061241c010014850000055902c1c3c6404204504210842d03030300c01c94540040300100c0300b0342c440c400c100c4e100030700c08507690007201e80111085602c030b0f110382c2c05400c03900c168500020407a0b5072151161002e504c1e11a4500c506003605042000109803195500681a013100d400791001c0640f004c02d1b000c0100d00355001c081e44d411700410400c4500032003120300400000e50302030b1440101300e0301c640c05041c0c130345040103241d10500e910510065101440100718620810307 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 933964199 1250 933962949 933962963
    0x180b060d02060c1e010501121e030909110d06060302041a0702040b10020a050106150f081503161d040f0311030f0720030d0e30160b04060804 62
    0x8441c03020408034400c501d08150580b10b02d0708500e41181c909800048603400c4080207104caa42d039030100c0e9201c48080d8400804020108807401302c1c08046c0d4080403241d90003440d000340d1180e50f81030a075003224891400c0000340c0c0000502d100b650b006c1030194500034012847c0071454030340740c10303000c0e0000320101401e00440317074000038988155542c94016187c80c00000740702035400310203018065130350000c5200440341542024000126201085000300c1c01200c1900c0381d50115a132a642180e040000410b203000f0b0b101d14113440141c41c0c50401c103208201c62200c9522234802d040a091503d401031301440140e150204400300800a5640010110141c0d410b0510b002454843d4615038114000c10b464072030440c00c081003000511110540010310a1000d50018124040c800c080c1a1100e6100c4084c001252105600352901d061481d00d4640050031082e941c5010851140c041c0a0749002c2c41d03105445130302008414088503101509030000349050385a01e481c0510b8440d000c3c5c941301006002800c84 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 933965449 1250 933964199 933964219
    0x60f01050a0504380405010509010f1e0210110f0409270c0303120e060f090a051608061006020604120e04020720040c080c0c03130608010306180b06 65
    0x318010b00c25a009000320202000720340c2e0440c2811920704c9070610080c840c203161440d402d191541042c0c103c0741070722010703592207150240420041d16410794044000c0c0420944940c4003a0780035074920309403200c1400343d000d46400c90700001c4180980e082c00f903400324135450401a42c5100718a102c100d8044030b28455000c00c8a500350344105040144141540800c1502c103046441045000390303014080d64071a840c2c801607542d135103030f0740000c480c191510400d650f840789000c260702034104858280d2003107100d0111000c514640c5e6800781405009881c070400d8882004c01803160350703014403000e0b601201c510031210740700b403030850002d69032900540081d05041010040b51a0180310303940a031074441c40504103559030f03851440c0585054102c1c20036900302145240f40100c051074030740070340c0c54000565030f0344034001c2c0c9078401d900b0031070360000c0e031900001c3c03200304504074003500349500c007000618180d1604401c9600d50705080042d203e40d0381320600c40310f6039400400d001610500c1e4140d082441030b6030701c01d05 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 933966699 1250 933965449 933965467
    0x161119180e0708070812030114040b040608010207080c0d180303031e06060f020c090603070303080603030d06150206160f0f140d0b0a050415060c1532060f0105 70
    0x24840078145008034007425401042c1004001085800ca6441c038089034280702080c01501c540c0c1c0002c2c041c0c0c80c030004031850410042d2406411080c0500320040c03000a113680c0e102c1141d401ca81c480c0c001211440c8001c90314036881c5100303010401134000345003400d207070350b410804c0d0078203060119004c024103060395140d2080c0415480b545041c0c0450340004100901a21024054454200006c010005101d540361013100c81c20120400380c000e04000d4001c1000e1401d655040d50b44440003030920b5003501c0b081c80700c506d8002e00c03400b80750018605842640e111044c500c8009040100040000c2100d070120901160515485091002a10440e1900541c1c5903040e410496080c2005011420f21074404150907207031200c2030f402880c41040403500c400f050b40e0343b0010f10040c1c4200307800110082030a00c108029060041640c0048079203c2c4240c8100034006030041411140750203000b4183c41c00c05e0f1040c000002c400800c0c403201d000c02c400c0d82112032600f10001407218240c0e50480307040050104142c1d0b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 933967949 1250 933966699 933966701
    0x90f050a0b0607140a08030a05040b0901060b04050f01030b0603040807150e1515090108070501020c0f0603011a19090603050702030909061203120f27030a0e120316111918 75
    0x1c0e407040300d2030755a04001c0d4017400072740410342d41500d284000c10b01250200340305206580c104d540710301c80703d818189400204040c01181648041c14140c48904201c408d03a902001184183e04c5045203c6d280e00c80790400030071441070800c500c4e100c0c900e13040d034841c2d06440005084a4a80340340107000c0c010740d5444400104c022011003040d8014900400205401402241e8501070350001c0e401c588014800074104660640d03506c4074150024410030040c08922203107103008a004006280c1c4900c4c103902c2c8801d440d01c0c9104000c0190001d400d0520920406e41d150084e5031304090301740700650604840340c000510250016043d24803075500308610740b10000d009c0c020382c0c0000b085504903c4c0ea52520380b445605480d801c0f0781144507070311040798413807038130510b484200888000c603402541004450441500c0d2001a200c0c0a0340c40b181c01510b045018808100401009020721040080302c3c0700c03071508034811141005800d1207000b064500c04003102d1195030035000c44141d840c00508219200600b48 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 933969199 1250 933967949 933967963
    0x1c210e010e030d021b2a0f03011e0c0f05031906030804030302010b0a1208090904060f020721090e13111315080d0509090a060510091d0c030604091704090f050a0b060714 74
    0x7c0d40550074280c003402c02091103003100c5d25141c4500c206001e10741540b034044946034030044003180401c005202046800c445410303200c0e0342151101000840d1030700c0b5110075074550020391049005030744807182142e00d403c00346c403c0030007001501d00c41018a03500d44c0c2c0700c135198003d203d405802204202d000901340400b9410260411040c418119606d02480c240305900c0c030400e00100780c0c04144c5d40782c0ca6058610035102102202d200e4030340341806840d503240d8620504001801a181c0510744d01b4a96410380d03c80016004070fa00c1c006000403000056542c20b5811001680041c050350000c01c0380b5000c85070440c04403090b03070a044840510700d59551280360010b0030b030342d042181c11802e40e451580c540c0f0340100500043d1440f55050945d0401d0b0301d40c0308500000d046504c440650f0041c8045185814503400100c22070780b24404040c941076441f01c50440c0ea410550040b06925140c9504c0c40b1039203001d20800380c0000701a0414030095414402080310341c822054003e00c00c8420401170031000f10144a03032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 933970449 1250 933969199 933969229
    0x120b04030e0a0f08060f04050604030809031c1406190b13030f0b04020909060103030f0528050301051809120f070b091c210e010e030d021b2a 62
    0xb145129101c02d00d509154001d8018076405126600129544c03031800c071140d9214541c420010030350382d078450741c04071900000546030409510091003510700145004c41447d4a807a0300903400a2100c0c0407000034100c200000d01040d0140d500359646075002c40c81501c56a00ba0f0b00f0169000b50f450b06071400d501c4101c007181d07002900302c29030040d2000c200030020000b6030103a40200d520809c152558445562034000030b1200601181c000c03000030403564041c601500402110000701e00c814208020110a4041c0845035180081d80000050000b80360401035068940040a4481078038940910b0440e0303240c0e000441102d07441008285001d00014210450b04069400001d8810b41d0034100c0d14142c2d07400180b4000e24903800081c00515402d40729400543e1112040c0040400100002c056603004040b501031400880d501c0e404170700d40d0000100000c02140d17040f4000180d0381c1901d640d8107444060004912a075941081810401e071040f900360305600034410010444079050704200203020b0381da0321000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 933971699 1250 933970449 933970459
    0x3040803040807050f06030c0405100e18042303030a1a03100204030317091e010e0a1407080f060109020d1803080f0c0a02030d050a0939120b04030e 65
    0x400b00c0c40600128001e41141d200791400d00d2140800d00c00c000803404216040418a07800b40720410003407403c1c10401c200c83c0340c13900b80800c41c00011404203101c0e00c29a05140440b04105040c0010032482d891000e01c020b44040000901c0320803918900e480b84006000094926249e00f0300b40400f00f2038160030f90040000900b103910700751940c6226000307500a40b04c1503002c0f4659409034008501c49148040c0300710040d82c060320075241044e0400c4c400c0d0421f040c080d01e0350b660312100a95150b00401c0b00103903031030007980384840c1405d080c601c441c9091401e82040300c041d000400c5000701e6480014015044d504400d4001d0b88803040702488800074021426100345524102c15010245600041018040c00c1c04404244090ba0f406950716658401d071442500107903c00c00103003c80d2441d99210f1500080c00200128040300c45071907001c05c0d0a100c1c1d420142d078881d03001c0b1880f480a14114200e80d402c1c0a02e02e00784242e440c1c036080c104000e00d512409008101c8071800201094400c01248402c0794000700 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 933972949 1250 933971699 933971707
    0x120f03190f02120a05071401050106020318040e0706080c1201060e1003050106080601111608010c180f1a0c010e010f0e0a170a0903080a0c1a07020615010203040803 72
    0x145503018000d012109002155080030400d050900c0400d1104080414040040c40c00340e000b4012078099214203010340f01e4000d03c940e000e41000f0280580c034028140c5131300458407109130042c1d80328100340804a9611540c640b00344005d10303000100b0f1a5003184c0b444d00b0103555503611582080c1882c0f142032407001c0b0009116002055450f0803002c15a9114020740d401d02c6208400c05081e022202d0030b00452002c2144040003608941c840c044410384580540300791100010160070210f41d10311140c21080140c0d454050341420150310240c11640003000c0e100c5055110301c2c00c041500d4080c4c1d50300072407003070341c400b001482c10400e03003c0221030322b00c4042c2e03008201420a0203052030081c00e58100d00e0313030f070f4600700760a0007001d1800207105a10300b0782282000c1640040c1c00310755002a40201071240c144000c506001003c01d20080c00b0380a81c40c4030b0b4031001101300d013500e86080c1490011880006104c108010301c0121640060642c0d4400084541c079480c034580760f00183d00e940155404540c4a1000107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 933974199 1250 933972949 933972967
    0x40509060f130f06140f07120b0604080601080c120318010309030509031c0320090d030905030a0b010e07111b1212190207150804020a03020405040605180d0e120f03 72
    0x45e101598000500e44e1844440d00d0b002c1511382d1003a01603c20000140c180c4d00940d0318000d06900030307030380c091001309084d00e011342c0c0d04031290070034400b680021110340001210305264100140c040a909400d00c001e9440c0c00310b115585c0c121040040d81d2541055070310032011381058040c00032165120001022142d05d11400003a25502d0601e41920b880000c1c2032206060160b104400c4003030100c4d541038a00e07814107003101c05203c90790050841c103408010200704000f03001d4030b0510080b10f2042c021600c0501d158108005c281000c030b400b0f4910000c114004240e00004e5402140c5903440b00524030070003280b030000c0710010b841c1c03020520030000740d0b00400300c031085010041d50040c0120300b800031800c10301d0302e4603201c2682c860b00c0da072003075102075a0010348164403e48500c17a030a45c06403004018142c419120b4000ca02160000c440451300e0340e03601c40c05d200021042d410b0010001c0800d1004011004140384010403000d81070840b18059004000c2c0480032050520000c06801030000c1240d8891320310f0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 933975449 1250 933974199 933974201
    0x30b090c042f090303040e011206180b06120106050a0602100f05060a122105090414041e020112111306050a05071e0f0506060a05040509060f130f06 65
    0x40d80d51003945003021803481d201c10600b0201c2d1042d0206089508500e07041c90b006220340c400110355a00d070004100200d100b000c105501c3d40a40306181c0030709a0700510307150a10803113010202c00011002c41c0045c120002e44c1038010594046820307150181c2d9650000880340c050241500306580c4143c45820120300c113540094025404250b00406000420004040b4401c50b801582e0300790308901c10f00720034448082040b0041c42040c3c442c9540c004d40c031404414652200311f801e040c0c40000f40380042c0e456840d103401e0040340c400d040f0450111206041c80c0d0b8510340b000400520f8070f502502d00c0b40b201825a030099103010b203480c000c042c06014240d001d86003030f0060342c88540c401030748503440300b004100980300b401501c00400280d12410710b02022520755003100c0e1000f00d1507507482022166240e0005140711001c101c1c40d4031600052040f420100100211085642c0109004514000c02c110944400050b100d401042172203003e00c542d1200d022480322482d10b118081c1c0114090a4208100696 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 933976699 1250 933975449 933975463
    0xa080a300f0f090c14010507140a02120d0c02010f030e061e0106140f1812150112051b0d1a1b030408070b07051b060604061413050709030b09 62
    0x8580c1c04004000c4207800120848841c440064a5012038074401e000c070401d14100034002410504000b0b0504285a45002c690040401c004016401198034201142407070303540d21040220110141180c1c0300740c81c400401c09000504c01034100703e050490344030560702a0b4001c040b05007006054038850726140030490402c50b00e040c80a07110944032400091002c1c8a0380520790b00c030220028080c80c2c1b02d41500d61002c2d6400a0028000d42500ba1b4003460196688e41e1742c00e0760300c01d03102c0c01410010203115454514003105901040400c5003d4041d00000348021404050380301e04000340020141700d00d404160440e11051009000c41030f245840d4007840b04c004034991288101280301d000b031483c09884003c0c24003003640c00900c2c1c20001d020113000244820243d9500c9811403800301d0400319880f10f40d03010612500700204a079040007051001750f007841e00800700504502c0c00190706024021010960500000c9121040707903950300c0111791410f02c40c502050095401a440b00b055041075a4084c0d02c48403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 933977949 1250 933976699 933976721
    0x4150e010932090403050403033507120c050d0f0605030f0f07060c03090b0c0c06030a0603030801051f1206050a0308030f0a11030612150108070e090a080a30 69
    0x10b20a040c516903803801452031481982d25583d0705003131501c3d40e5001e8a4036410607500020395018800c900c0c2c110802c0012010220181c4000e2800c00d040640c00500300c079a10045a540a90604403001e41c6940c003c401c980c3c40124480d0b002552203010321400009003c02c0d009a0751501510915a00c0349400040c0403014181401c2070300e04c0b590346d0b4442178403154068407000380801d03c103460400040c407195002e0245990044103403811a580c5c42c00003000b40c1d10844000d03d500703580d2541801072540c051145805008d0079100300c2c0245801c0c1030b81a48810a0003404c500f00b1040060720030030480d032904850000c18015110409040d00c03840d00c5101d6070022500c03000141100000996025490b00820008181c500065859921104c0a1000f0749440ca81400d580c1c3c450011000031207000c2c021001c1c004d10480c000b9001007800d260200da400c04003e0b000484587c002c41084000c1071416003200c0c110b45042c107290300a913583c5800350003014080040a40074000108095a1000e400d4201058181c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 933979199 1250 933977949 933978029
    0x6190804030f020706080703090305090d030810060509090a020c1203040c03031706010e010f0c210201060611150403090504091202160f0b0a0522030209060604150e0109 74
    0x14502e9038049944028034865100060418000300d456180203501040c5000e000e8642981380c04903003800700d81c217491024000c81c009106d81c0100603541c00c0c2101c940c0c0103044e0130f1030300c0c9243c0707440c0c00001640e544001d41840754a070360020b440c1e21316802c00c110f040d04040d100710344140c50349064182030310703030401c188419004113000d640c0c0100002e07904a1420310400c0b058449600402c0844011507191079404d485005200441400b4000f00702003d61402030003220750051a201c000c0600c2c02400d6500647c04482404665548400c40501c00300700d24264460b207034540183c40d51503042c1182d204941e80d2045070064a481d644c8070501800300345500010f02c0903000c8a81c050303420300f0a8100c449044c8183c41803c100c5001c1030141c0342c0301b440145501c2c0d0961902c1ca041a06011810080e90031689042895407a042d604104500b4010a2030741d0100d000c88080741403515003d0011810401d02003011b00b000403c1140c1000c0303a0140c21181f02601c0300d1080c501288808032600700c006000126010405 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 933980449 1250 933979199 933979217
    0x7080606120a0b0112030f170708220c09060603060e0a050a020d0c0203071115120a090602040b03010e1b07080318060106021617070b18031c0810080613020619080403 73
    0x1070288002d232000b0000c011000c00c69642e0b03e5811101400e01030030b08070408240f80c801c40f1031107401e8020b580340c0300d0080d001509003510b881804022200e40b80d0040080c1814404104804032569850aa1244a58502040a03070b00d00400300000d110700110018154500383da00c0d255070754004042c111991107010407244400d48441004491000c1d201e0743c0011000402185544500c4108440d4021801c1c503008a05500103a84040aa812580050b400c050000c401040684030380440f03a5044a101d070300300c20004410702881c0350544500d61001c0c00303202002001c1004104042c5449507100400e00590b030f001e58450740000e445540c0010518800181c5000224040364401100b02e142c0032000700600d11185452074050540d003101e42050700c41c291000360702d00203480c00d11540754881802c3c9410101102a104003405548000e40f003078042d01c48156041c031000000254803504820302112109140090b40300040281c421a40900278002101192042d51500800e14a01552082e102d100360 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 933981699 1250 933980449 933980477
    0x5010b0a09140a050606250b04030c030f0c02010e0904021909051506091c0c0f030809040501061d0105030a0b040603080403171303030804060204152007080606120a0b011203 76
    0xc2d01c0003517034034541c81001000406071500e030342c0704100d44211101000600c11000c0d078688070100709045030107402182c0d42040d0b4104147d1b00240d0196410124141807031054200d4000170070b0501000798290141102c1d402060030355480c003802d0045152240c0b4000d14081d15541c6600c0a00130a0311034030142c020780c0b05004054544001912034001020b00214801c400808134428681c407110000c3c0d4800f1410300e4003203034045116001c14041c1d4010540c050392040d01c041030000311101640a2803c2181010f0883c6c0c2d81030f0802c03110085800d0074a851a01c0e03841e60456500107280b07100724070764001d2a010b800070401501c03034003a008403405000b12035482c11528a0203130b201e100309800c1c0300c003804003400c0610010780a07440454100e802210b0050070f0a40387e400c0c040180349505031560101e00804080b81e0702100c0000d450f2140b895100280058500d4850707103541c0c9040c040c2c9290b200d640c655540f0180b02c6020080425480d801403521050b030350f0354160700e8141940d41c2c0c03801d0700020035030000300d40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 933982949 1250 933981699 933981701
    0x90609030914010507020907090b0309010b0a12080d0525120f0533060408210a020c011209020a1e05030102070209011512110d0e010e1905010b0a09140a 67
    0x103402d1810b0311081d00c0d00c5119802c00404000c010a29414816581004903c0c00e4841c0301551140c65400000212105a032041140300103403a880310100710401c03403c0e040000ca500d81600c0c8009004480416030b500d0300d1340038021246202e2054441c484a05900c0e9101d140c0c402201090601e19040400c01c070000300000c3e0082c1d1b14121002e103c5015034118811920605408507142c440ba1401950845284a0300060050340f05034040600d551080c50030741d040c4a501e00c0ba03000351103030f00c0d400e184c501404040c1c043c0d00c40318400d07005414098506111402c00e035090304050601d0398010107401940d5101c101c042c003e10340c0e025584903050311040000c00e850405108507443e80d50000e1007490503a01c0c0204031202480107201d0070b0100321001040d001e0341c01d41390080403150941c203540b580d190340590030000d0880e0080304080006a040090500d02032001042580082041800000f11010071303040c218003420700300e182a40c00801c140c500084019441d40700c620f220b020403001d540f1903140c481c0144 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 933984199 1250 933982949 933982979
    0xb0708091002033a0b0907180b0a050a02061e3903091005060f2103040e0a0c030203070905010810050a15110f0601120311010906090309 60
    0x82025104220505040c603110300c0d003903000041441100d203041601c581c4541e05820308440803103804510804041940380b8882d0a0026000010080002c080b800d80068140c020150002c000c0c024602400f140c5e01502d294004050400980e080359203103900200100240e0041e48a1401802400c011a601001c01e04818007040210082c170b21454030b58502c1c0064028181509048000e10b014041d01215000701c01c20000300782018016444c0c1c0f41c441314560400c41c1d117840b1240c88918000800000c0e0744d03040b1034400040000c0c0c82c02d0041d00003080c0d4079018250008041001b6100c080740004030820619101c91003103c002c00c040c464080302010503002d0380429100340d804281c803103005000a510030300da150340c8185541d680b8181249d491001c40e0080980fa0044660b0030307026413030312081c280c00c4240b2882120b01c050081110200600c1469111f51040c011004d81c91009601c7c0d43c280b52080c00030105412441000f00900d541510b400070080c00c0150040380840c841070310000303450030311036502 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 933985449 1250 933984199 933984203
    0x1a1209030715020f090d150515031507031d010b01090b18041e090c0e01050a120b0603010f061d0c031303030902131503110901031a07030905030a05070308010b07 71
    0x14810240b24690108069000003808004624041c02821307920740d02c07948003a6209001d580b581e0044110801e00005858004218a062086905206000d5100064201e0030050703001201001c036220018201d0143c00310583c07000322946441500f01070040194404884a5001d032511811191388840e0783c2030714003908030342d442099134060900320b5a04140e00300f8203c0044100303040381c841d404491110121482d0010603104222000301c14071100c802c446095026210455000707180d03030b1400a8120241c803500c58001d00f02c026900c00328442d41c50035081a802751070510350a00c401341c0c854052460788102203406042c86081100810400500501201d0080310106540300c1d4030107464900703401809249c58100d801c00d001101d90b007c0c070700315841407440c0f0035854095041540d00c0e5040c440207554407090000c1c40750010b030300100006001c400f0580448144600046440c0c0d8030008141c006010f10f030380190041c0000100c03c410145e1110003080068426280c205040e62208000c4003540902400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 933986699 1250 933985449 933985463
    0x501140a05010e0111012405120703021c020a03141c1b030207150806030d1b03081906030b0618060321041a0d0507030c08011e1a12090307 61
    0x10701855100315000044500181000c43c80c4c4000c420740c207401c50740c6100c1e81a01c4034040110a0303020403060150a0000c0400311020884600301d041d940d070b118049480020311650600031051540c41030b0411005510360001d180f01001d568900300000030300030124007035426000744214202d03208000b1094148010195581d100100d104400d215124000ca01c4142d007980f048040c001070600c2c0b00c0c040c0050084503951058528280f440c05e16140422020121003400316540c0c00024004904400e85512030309031810395801e45403400c0b10311640709032000c11501caa09000011043c80050b4a400e4000c0000303440d17400c0c12458610b0040003008040e00e4050341604840f103680301c3c0341e90200c05081d40c1074801150a1800c0da588912130007440d0546a020b0f1080d20128043c26180311502c100da501040b582424004d100031a0340040810805000300509030390903281a01d42000566905006000540d44a03001400c209512644982000d01c8207100890004006810220088141c0314030b02d6110341 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 933987949 1250 933986699 933986719
    0x806091306020901030914010e0d020706020d1404081518010e070e272b020a14160603060e150904120e0913050c1504050607110402030c0a03050114 65
    0x501c24019500c82c2005904150b00d03010724402040b80c03211a444e0481100d800003175000f0420078490b0415010001182c29508054820885550003098480700c01e030641c581041222080759244503580101d8000201912541d9020030b08001400c0860f40100c0e40c20100f00ca100c0c1107150355500781c8058482d00800350b00304210410003610401030a036000340c008082040e190f90035420f031041007103054400103c19406182c40b9810b0151105a00fa0010b40c03100143c10100b1408a01035a01c0045d8a80104401c0a170044c0088d05a4203121844d03080240c07582c03050300c060741d60350010081c02c0580603e031803400044d004221040c4055482c985000b02c060304582d40750b512901c51310b82c00400048a070050008402548500e6070300e07021403606c10030301818152810030301c1e810080d00e010b078841a0140a000e50694000000380000142c1e01210710849502d81d035400c0c54034000f0440c811400c4095009800481402550700310000505002e20392a9010031051ba030301c2c04d80d041c4244401c50b52a0300004040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 933989199 1250 933987949 933987953
    0x1902030706022710090e0a090b0c0a0305061e0d0201140c01060515030907030b09120301090c030e06101a1210210804050d06180c060f02060103200d0501020c0604020108060913 77
    0x441d47c0e442225002c001850303000342d44420700e144d40c00700c81400000b50002804941ca5406108083c0c0000b001c0d1003007103000302080e910144403804407500902c00c44040c0d2007502160321440d4540c0c00804030203c4161918a62054907010f000c0c80d00900d031280d00c200e85640700da8043d10b41035921a9942100900c103040ca140c0b6001d0000721b01800c4840907000c3ca400080382e00310200019802004049000280d41400ba00c0080849280b0030244010350001c0303042c0020340714450007071016164204041c2c4c1510030704110001c40c074440c2c6490744888007060710070800c0882110300594100ea00d5012a410343d15090b41d80c541036000030940c000c01046050009010908280e40103007582407064500150784440103003c01d02c60f0300340c50300031500380b07454900521003658080714850119515000600b041c0d4110341e20308101c10440d41941385020009091a0f54a544401c041d40d2001d030010021592030082a58107520b4000446059000c21a00c00c042122801c00b40d0710107104280f0100350300700d02c400f19 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 933990449 1250 933989199 933989219
    0xc04021c110c0a0809270c0322140d0930060f090203070801020703080a020a022112013c090f0906050112020303190203070602271009 59
    0x1040900380605018031058a03844420810300c0f040d180500c42d081d8076603030608108010700c01c44019200e1030b001590b000e40e0712400c04454041e00000c000c0180d40d02ca6966081e6279811030820203079141c03502102198081480040017004c291428200c0503903007042c0c07440710245c481b01c140e84540101010003ca130414030103964031b0740707040d03110035005248088007045d241e07841512009518410b50030703610014141145000c20500c00240a000700a50601e2030903100602a180014101c040950700000d41242c0c1070b101344040c0c456030074040001d0460b000b200f9460412034110081800b501094907001250501c10b00e0003403500400105080d0060480081e0004600302c040d04406038001c4207050301148140341070142684104010034002980d5441d0308080c01983c0c0181c1c80305100d01c2840301440c0c0503072404021a001422542d18640b020080c1c20b1089245104810b4054003080c404201814020395202c80d400c00345100401c40200c00059504100c094a40085030b10080f4a00b00c10400034a611 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 933991699 1250 933990449 933990461
    0x3050f0f0703120212121009051306050c04030218071106190c12060815060d0807170706020a030b0102390a030807030c02030d140306120123090c04021c 67
    0xf24810384041c5541010142519040901ca001c4d1382e03070040d0104000d10544800d08802048018020720003820030004480c0e040070080005440036840c1c0780041c5c1d041c0c0040040f10300a550151071030904502035000140307083c1c0240c6d40a07000940c64104101d4a1b0700c0000c0e0640a00700e00360b03500b2807080f0300d00c9540d4020010000c0420034020f1744100d0064101e0b0a101e00c01c010306103500a0a4550150312011007000d1008003228403c4c8007805009021500310000da404031644a068100c0b88540822000f040b0301654000520203400024545107460b07041d004210003034000e8080360f58440200d00d80640302011010b80b0641c10705440d8554022160405414030b4000c000b41984020a45980b140c0640d0741c4650026004240034100c00d00840c281082580c04860351407820751403100c0b00c1c40c4081c04510004d0b01c414800c24001816110b41e0200b90311486184e40c0801c40849141c0500400d02e4030720208807181c400c0d81c001c0940d001e0303503170529000b10b4445c860040d00c06150b08444100309402001c07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 933992805 1106 933991699 933991733
    0x106081b180f03030c0a20010e03100b0d0203030d090c1a0d0f02040e090d090518010312110d09150f1707140a03050103050f0f0703 58
    0x2050049040d818002c40c1c800b84480307040000646180501c2c1d03041c11190048000311010040d5016286811040804840040f094140c0064504c054040c0200360990851841030354240e80d030350700030842030070010281c1123040543e0f004645107421910500c20344c0e90351424451f090040800d003c40041400105e680f42100e11152100802c0c01110b445070400c0d900c07141c00026100c00358040c0da000c0c010b115009021464000041c42da1003002242c0d00300810780490020940e41011100c00f85c6145038560398160703d03461599800c2c080191002c0080c100008101140724103042071240900d280c5842d9994010241807004031115564990001800c0c41441d4034150b900a41180c040d40e2140000c10340400c4550705c0351001d0358481020210f040c407030200002c00d801d401360503a1095040c1c074010b03012101c000c3c1d024041141d0720200004a0b10040e03210307800400000c0e403070000700d2003050 = true := by decide +kernel

theorem cover : BRFrame.Cov 933812949 933992805 := by
  have h0 := BRFrame.cov_init 933812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 933812949 ≤ n) (h2 : n < 933992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
