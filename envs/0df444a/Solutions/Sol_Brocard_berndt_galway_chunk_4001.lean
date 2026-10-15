-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4001
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:17:35.634974+00:00
-- url     : https://prove2.me/submissions/84ab71b3-95ef-49df-9aa5-f3a44e47ca7d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 719424460 ≤ n < 719604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 719425710 1250 719424460 719424463
    0x60806011809110603040f110301060e040b090a050a060f050a0b0d1b0b2a060708010909020a0b0a17090321060d021207080114011a03061818070b0c 65
    0x9100d481d229800141c010b000341081c40c003c8050301d40340c0d500300e200001800b041003e0202c807101614002c205259110010b0400c2609071091485204082c40c41da201003004030b03607010105030f0459034800c11900c01d0306c0d056454500300400c04101307440a982c3d0781598481318105014842d804907200354104040c2c2c004200043c64900010780242c600c510700c100c0ea400c15080451100d000e0301590510503221120310308024603008296840d1070300c102c2c2c0e80459061a01000480c1030040040341c0b28440039a0800c4101c400403c40040d080c1d9100c00340200004141c08088020308520a603542c43c08006081400e4003200315401030003441441e4810070110b0300074800c0c281d83c94481040645007039025150100002d01b007040c1d40c28043d40c4054480d2031400700300d50004840048503081c00080c0505c085070b641c008440c0c0d009100303404003d812200e410300680e05e441d0045900c44c6005043c01c01d1000440700d0008504000c0f10071007a06005c1c1001268200420002013004042c0d41d1400e5291400040005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 719426960 1250 719425710 719425739
    0xa08100b0f0d0f110705010e0706081f0b070309061b02090c13050a0902040302031b060a0e01031b23070503161a040305120105031501051504030501060b0703020106080601 75
    0x54080d510045128042d05089421100c4606286542480120384400c60a0200d81c041141120030758030b0200e95155001003c10080d04990b40c1d07440c0d0744010b42d01c404071030100304803007052080b40881d04800810081d450502420a07280a643c40086c483d0a00b000580b1a44038000882e4050650400d075400503500c001036141c2c8013500080d00c03619100400300349106800f007508096402a903040001c640100707603034040c01c201c0c1c0c000c808650118403582110030351640070000c0b16410003400c012200300d10f4010103401d00d2491061600007544008580c0003140180110340712030003d24401d02c40c0340c4084c0c7d1459100d04900c0b00c407640c01d00e012030f5603680384d64910501302458401b00034070780c4800c2448140c079441e0316818140300111f0f81900e010f00c1e0017800d13a031001100300510040c000000c18181070016040091103101d80709140f4990a204c1048000c40030819451780b4000c0401000c00060780a00aa000518000381c2103500c48415140103402e468003034112025aa0041c40100448040704c1903070f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 719428210 1250 719426960 719426977
    0x1409090a060c03090f1208010506210c04121b05060a0c0b090708030403030807200c010e04020d020d020301050315040308041203061d0603071520150103080a08100b 72
    0x1010b04660409038003401c69498045c01211404c0494002d00c40840110107800c80b46540e054110b0383c0710030400850740200100c0c016610400c07158540c050b404100220340012947d04400d05080d690120003000740ca904608a500c000349402d40c2c15129040200e40029010440b181d506043c400c3c1c40040004030290009008852240041400c805c8140046406010f0440c1076907034480d100d0401803c100c0c003d03100000003541b100d615914400d503e410308803220455030040d00703210095900460b02d04d04013840d01030f802a03003080501d0900000744014000603400b48000350b00d942c54101010306100071042e00142c0780d0181410080081d901c81d0a0355400307030380917165056001150350228000c00c00ca401c5805100700e20345001c490740c0440c41c00188120030490448154a8a41c2405200900e000a140010985084411443c0301850300300701211103005003213820002e0606500c03004500c007a48191114400081d000004903402150298001c0d0440c08018286181c04501c010303902c10f4929 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 719429460 1250 719428210 719428223
    0x2803120c0c020f0406080105251806080702010e07060e0906092502010221160207061209110310060f090605030714040b18240f01110f030a091409090a 66
    0x3c0c0407540c0d82c4d6409034000d480004001c0103c0d18149603100020400d04074201020403005800e0000a40b01d000e401e2026075070b042510808518100d41a0340341e60007e007100b81076549030858000228010020403000705269920f0f8040c1c852a10b0600c003055030003502241c084d81030b90381084503400c1101c85c0204000403a100608402030b010038100d009000d0a00032050f9400c4940c0003200300c00c0001c03401c50084244d24012600840b410300c090f640c0d04664816140443e502240002101c40960312818840f8016060010300c02d800b00c6c00282818070f60a04011003070385c0c66406110008242e100400a4403000c00c00300000703810403001039a03c4904e44a402010071704003081c907038192141c0d000602003a0000d407410b0926861036880d44121340c021211010007102c0003c42100f2000800c0b07a4001c08a405800c98528002440046a2900304400010010b20070100b84010f8010208014117030f00c483c80d50f4083d541400c1a2040f0010b240c50641e840c0300c0c130002c01c1400315400001c110080d5003a031003034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 719430710 1250 719429460 719429479
    0x70c0b07020a030b0406050402100201020711010e060d06290711090a020d14010303080a0c140c0708070e16090506090d020f0301020f0d0e070602060708092803120c0c02 74
    0x100107254030b14590801403001c01580140001c22072103400040c040c61080f40c42540d144441b81c001c80c200d02440d0f00c060407071800c0d0a40b48c081035000d803a402e424280064000d0740340c685180c4084055891703d90080c001c031764450f8104802c0300640840e850501e80e000c00d1031403a10b4a07030b032200010034800c0c51109101c0c81d90346012851059199040315a5044808800c2c00740065030000b1000210007440180c0c0031902c0318000901d169241e10560b01011090b4890714419182c070803c01d2442e40001120344d60900c00c41d080465203c1c6c00304003a070010442001c4810242c98040419003403018010080000e10010a0003400180c3d50541640c80c10075060b0765a18a41c000740c00000c1900c0c1485062940551000030054800c020f944001c00040203140070502c2090041a20150307076001b10300ca28801a04210041001c1911409100750040044011034001540b881020691483c0140988420311000070400d0b0416820101c2117200b0b61403400e080001e1a218200171304010364941d4000c0c0700b00c2610 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 719431960 1250 719430710 719430713
    0xf060711100b0a030c090c030f0204051507081303051b041b0f020c1c030e030316021915050301030302011b1e02010f0203010e010503070f03080a030203091912030c0203070c0b07 78
    0x100300300645d04200072004280c1d0742c0d2071050040c600d002c00c160019091044440305503149000300c41c200c45001d0304032072040d0141c008008003500681002c0361580d034200516031500601c103441e00f002d54010006010000a000d0a180381c4006074400c01d4041d07410b1680e618070b45400044d81c192040198105409146002c06e0105e0800c40b01299550744075138051a41500710002c03400004d130f010721035150b006000680b101003568038043c1015040c2150b010b01021030045c01c01c64401041000060801d5078103d0700e40c0c20885503c41c41c203c040300001c10200c0100285942400350781c007040e00340503116504041403100182011800758090355406941412100814401d50004841c03940d0403100b1926561616400c4000c51000e1083e14442d1107180710204000d030ba0341d0280001c4a0b4400b60003850281444c0c0150049c0d00000c00d0303405c09000340c0c00c3d01d100900034038003111440703032189045101c520f0703403480050105d8400c504841c003154018007070780c1d002800044502d030a0701c00350034140c1d4480209 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 719433210 1250 719431960 719431969
    0x503101b110c090403110f0102070807021c080429071109311205191803020618090a0b0f12160b0c0105150d1203020c0d020f060711100b 60
    0x245406150000c0b0030b0f108201c145503000b20141d1078110f01d2000d440102c003680e400d02e400d03801060409402d620080000c4030041c0743c04810031881c0c0041ca0f210f8405a42140c4032030007036402c554082401c03844002000010503014422080c0d103840400b14450034200e0988803100d09825803100d040c015101c2801181d24001e980d031101007542c0001c01d0000004905040400c140a40c55100320b490b6018100001880c0d80140e042d10000303115508078003034a01d940389040f00c0c406001c4504090440c2c44000210150b150840189015800510794400303403000c03d0140310490038001c1580201d280344c4140034403d03648204007451526011204080b0b02284019410300300b819001d0030f0f24260303d40e0740001600e505120b025090a0600740000c100f507607518030076560508072040e070b1103a001035030006a5002a010041c1d48911070654070b001403e00c9980d000c4140380c008003a6203e405179100115248002904000c05503202d101c6207070171019018169480da42d00c090005a900b5520785850040846888 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 719434460 1250 719433210 719433223
    0x3010b060403050a0209010803120703091109040503030403270b070503090d12020123060103020a1707200d050a050d0b0a030f120306080d12020909100503101b11 71
    0x1001061550748541d24075103950b030b50003400c0089010301d10800000403024408800d03111003001500d8017094a9662000c00c40c018075035000125007110502041e05699110541400d22861195005660ba410181030107402085031841c04040381100c2c001110b00c00c1100403c40048900d11030040d9111103040c58550300b940152606190044030190041e020710050724040c40600003590000c1005906203c001c11600c1d170f0204803070358107900d01008221254070a500400003a00035103010a07205075000c42c84400e07400c056a003000000e2030a04100b004103000d45ca0400f04004d2034000303240354041080040c5c500e000b6030207100300703001010502c983d445510b41c01c030525406004181148040d01c03460143c2c02390680040c19608183c0c06a00303c040640284104402e850f8a03400a09403080c50b224111081c1a41c0d0041d05d10344e076024000c00f0380315110410307480e01a1045010210304a0300700000d051410b6076202e600b07a0346908201c0b1a150f0031481c41d1824986156525145240f03040b034940d00f43c038090 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 719435710 1250 719434460 719434481
    0x81b0c0a03081911100203071b0b040f060e0105070306090f141b0f0a0f120504030c080307030b03010f061509031104050705040e07030917040f0e060f0325050a0b03060d020301 77
    0x388050702100005c0c558020351090080d502c515500c60f2084111200400320818003c1201a04c4401701d03010403413a0081d044905d201e08801700d6810a6043d044e425654280c4064020035141d090a001d415560300858640c4080d5a10800600280e02c01c210b0b0080c401500ca511522002d4038400744282c40745040b03654a4091403812981c034182d001d001003100d0210065400000c5000c6090207000041d40a010300135a01036403540341d001da0f19259054581d201902d40c005040d034429402070291028011400d102d485940001089171071303d1075178118401400003200401143c1c40003031000070100480280d9809040c2c1c0d0014069413a142c0580c3c840c03160741c2007030403021032135030030886030303550503084601554850900d40c0150005031640c940346004900410f6a0582c0c0181c2c18400c40c0c0d0811001940040b00500c840c411f42e41c03003004242094000c1d00030a200c0d06170b0360300190103496458113034001040160b5004106900d0148042540e00004d400144102a2a070721362083d590250000500d12 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 719436960 1250 719435710 719435713
    0x80114180705130b09010c0209070201150e0901060603200a03180f05010c03051504390207050906010e060c102c0313030f050307081b0c0a03081911 65
    0x207080002001d07005070090746180c1c0300744240340310101d006003000c401e458410340c042c3c6038807100c040c0b00d43c00c002c0290b800405a6045659034072070840013041c600d13024001040c5050014580d424082012400e48289030801014181440d015844034100e8114085182c03240341c4031940c139029081d00c220007528428150840540100c001003050020a542a5940314869030003006035000e818803c1d0141c0c0c0040300c0c1206441d40c20389000c0d1040c2041d400a54100d0300c007680842c42c20182110007510403540038482c80b5008a2818103e4006404000303106c09070a0403640c125007450004e000810483c8010f9116004d52004074211a03071443c100884620761405240603c0404c0050805042d0485c103140304141c2034070040300450754020040221020400f81c15844c0903a10705644404407180c0001d80100e0703043c4410000080843c1c10301007d042c0765102c14800c5500c4080d0414202e1501c401844c07e14030840303600703000300000303626072044030b440ca1800c010090800400c40f000b900c1541c0f80e01c00090f445d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 719438210 1250 719436960 719437009
    0x2010c0b1e01060302210118020d090804090b0a06090305120714010c030f1415120a120203121602070e07030e16052b0816050f1b01050a080114 63
    0xf900d815801825800a291550441580201c0001310311040e00784200100420151211500d03a030603500200580c0c044940013041c40c0c4407503911140300d94070035400508019500c0b08000541e10341150614000c0c075061a11070380301401c5845880e10303483e01050b2220010b0b000103204041015017101c002c107984146001304503003040444003402819020314260000b510703000320342c50300d441154004d5000e0440742c0c94060b44071b0690000d01ca58048500c04400720340c801d9040c0c03000024001071403103035200d05990103961580120a803c4450000c003800300d1510060400142c1c01150b070026110003113032504c2d082c2102c0d580384c502058004004011000c0514001c0184801150440202c5002210710540b40c4050b000015030f8401c3d58411948090090000e0390301559000c5030b9007001910080745081e130707030010411156607071a02e401a29041905560010750201c07082e0210075650727402c401e03c2070801501d016030130500145009814000d07044070001e041d103085415140c400b600302c070300d2640710644e041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 719439460 1250 719438210 719438219
    0x30307120e1f210c0819060b030709050a0902030c03040f02040b1519020706050a0c0201090e090a03020d0f0c14030706060608010e07090f09020315040513030201150302010c0b1e01 79
    0x144005000e00d8400c000d154042c0004883e8052045400407522641e4098282d1540004032400b88130400004605640b1050003189000c000342c002e5000300038a07150944840c1c40d04ac10f010b21026258001c841d144c3c8107008011aa021007011243d0080d0700a0045420b0900e600c0001c0040071291035258001382107100300000540068020810189500d044104401000308101c0c4e481600c4d000e0b020000b03e042c0240c9500c1d070300400310807101d1881410314002250312403102e142d600100721440380250780400040c0b0b05140d010f0002c03050802c91450840002205260007815484c1071f480000c0505241a50010071034078144103490010354002c805008003517480000a000920a0003000c03480e17400c000c0801c0c8428042da40039802c0791800c011507041c851820084c0d200030f41008180046a18020303402d800d41c2d681d24425a0310842320344081e190720030010308009084642c05218030b10a08040d800600141c2e8010205404c3d544d4409910031240d034410700008040c15100c50b0702e26121140200204 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 719440710 1250 719439460 719439467
    0x20904021306090b0f1219030e09040804060807080403140c01061203020303060a120f24111c090b0f090312010f17011415030c0d080406030605030307120e1f 69
    0x704c00715000ca070810580f0094004000d90315046206d0300c601035000d030034a020703059103a01c1c0052011380a400c0801021001102103502c00504a808454600000400344540b0741c02034595600805a40b40c40c2c3c800e440e1540e00a00f11820210010544e00004101c65001880c250400c0010380b603d5101c4100800041c036010b175490704151501e5102c0d00b2908170200d81c4018400704a0200f0b03410000300d003100ca4443d02e501a0443d1007500d50744050424000004141045001d180303401107802d0845542d8800d505d4482e1a02103019920150a50402d00740d407000c80c07552101b0542180355450b03911000d03207841d000d181c0756200e040b03a207112140b00e0800004184a140032034034210b51200301408418044170103950308030750000d0b01402500050360080345806910b03486c2502a038102900310785462031202c00280305c10000100440d02c3d214001424000701e5494040d4074000d101c25002582422000c0d030b5403818a4890030a80006c00030122a402c1d003e540303178007103c00c920070821407484210b07a500e08001c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 719441960 1250 719440710 719440721
    0x80c22061a0403050105070203070f110d1208040605160e0603060109030f14070e0c0a0c081303060f0e0705030d1404030218060102010510050d0b0a06030803072a02060702090402130609 81
    0x1600c031313540380c980010b002900100c01c03101406d62042c0c14540e41c0003150307030311003000710f0b201d40e956000444034008a001403000f0400414a01441c0c0b03c007029440e20307291200a4905c020704c0340d0000d201c5030b10134118940e00001a0500090102e8500f42c0b070703a0362000100c41018032580054002e02c0d04896a4080c000c42d104400d0b241c1c11040156800c035515000300150290054503a00ca90b0f0744108400361115103e0007824114912603800c051400819107100b404004450b0416126190f4030003c9020785800f134801e000c0440c01c110080c0001d01d2070304001a4403098424140c0b0140036254408025906021003110301840c1c6c010001c9402c0d5030781007961542610101ca03854055841c0002161070300d04030010803011108001c1010031447c8850f40d658800c0740c006030802c8441511100b02000003081000510311440d0607070f548903a00001d0b800368039291a502601c054070307008100700b41c030b026071280c1c82101c480c1c80d01526070503a282c645101107403c40640324440003840b07181603c01300d1011910b4020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 719443210 1250 719441960 719441963
    0x120706020315060316080c031512010608061906051807080a06050d0b070e010801050a21150c0906050f04060c050a020907230c0d08040f06110a030501080c22061a0403 73
    0x2e0046e0b5580302e0f2024080c03032005035100c1c4628660125a60131500d80141c82850500c00d000010401d2942ca0494038a040c1d0291101c0040656a102840301c5226520901000304403c85591440504621010040000c00740416040082800000707050003d180c2040008050142c8484440446030400071403c40c6d003590714000203141444504840d61083e254a4142c0b117004018400082c540580f03000c0d0441c8003418190280b1041014a020580d1080c08074540010090040350502d07688400400050345904060140a418800708800c440000c09880c1590000d007002041c028082c00c00500c0c0001884d0300941c030040d00020405e980e9403107030800005440c040c912418181c41080444414003520919401c160b008400b002222407080301e800c4c0e04240a45025400181552100c6003562403540101440d030000198071000b140d4107104090040004801034072502c0640c80025031f9581012618160240500032441e102c1c845030750203940208a241e460200100c041d0941c40c2064116100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 719444460 1250 719443210 719443217
    0xf0603060f0a171c1e0503060109090e060915090712170d1d0a020d0210030b06030c070312140f2502160803070203060705180402040b120603120706020315060316 71
    0x1d4070881d139024107480a480c800c07180c00d0300209040b44008944c9500003c0005040010101e80050041164411a0217210402010b42503d03d00b51944600d0700c2c58220004189500080c20000050404a02041a030302d03509a420451159030900c0c030306543ca8084005800200090301d150b901a0f21b03402902790017200c1c412038102c001642055610b400784404c010350404155154880145001032060301e0f00041030900180501c408004107500780c0040340e811445035030001d13140c0140340d0842410a01418040c1040c8550301c040c01590a0486001e060810170800d00804914589c5201005141041c1003101c8001200c505c050000d682c0c05140420001c0a4540c40021840c4030010045620090f00500144004c1e110304104a8807076000040070040142d1400240c640d96a41e800204024200b9000030b40d00c0e42d900b014207405080010300254480d07030140075210f810f001084242c691240e0041c000503101c0d500d00c03100000f44604070600300c1e8003100001c10051000300205060145010940c0d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 719445710 1250 719444460 719444503
    0x110d0f080a0903240b030706021005060613060203070b012102011b08160b010801020301060e010f0507081903050a0e060c0901112b11060105151303030e0f0f0603060f0a17 75
    0x7804c0c17546441f024010b220068102004410b074141140c2c101e242c1256001d00f5140c80d060200c41503412034500c503000000140c00c00503000301400307100c48695016040100c0c041e603448517544180343c08a049408001c4c148a880b231b00c606035060100c80c40040d01c41c2c001c2102903807410340002502c038005524504440004c0c0030000842d01c454140b0940781641d0341600c58070062600c1c0001035a03404040304149081010402c5943c0000b6400300c05083d4650380149070010090030160080c065840003050f140007a40380901240e04e241000803844e4101445030309182d603c200c01c0300101c0f030b441d0300380041d10010301c0b403445107040740c0003d405104c607202c411038001e00e90340c00244012a40310003e0180900581d0221005200ca450501165941c100620100500d0602558110220910f00c0d40c000e80200f09107800019440c10003400d00080b42d68112841601d5921101c002141d9000c00703409a4025064450640e071603843c1c888000c0043c10b8401d0b0786484155006201c00d81c0c946080c84070000c110741c2c44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 719446960 1250 719445710 719445731
    0x28050312090d1202090303091207090906020306120d0e130e1c2006073605040605030a0c090e0c030f0a0213050c0316021216110d0f080a090324 63
    0x784241d4405d20740040c061480e1032260360070027201c9007035a140820280150b0600003030310344603442041d842a102d1140540c4034a400f6007080350241540d081e0f903032546c01c00c0115005aa50200180d4001d80d0112200620180010940401491b8000a48410b03110315041200003e01c90300078150341c4040ca0361000c2c130780e80e9040255400342c840441441010ba000300c0100d01428001e042214050144641d64211400406a80c2003240101058201d103140c0c10041407080b8100b501804000d0081580280707940905540d440d07d06061620030f00e4815952000b01c0b46210005004104802400074221101c2c0c60781302d0503090715054194000c074030035068803000300003104241c01550300c1882e81040340d50455846516a4085180803c10396085006050302c4040e1503281801410660b0a42c3c0502c3c60040001c0c9803615804007002032080c4074a41c00e01d281c2d000101d014240303603452940f050401c2c3d00c60310070349400c0d105081142c100816581500085d030007034103041c3d40003184c90200d030030b800c0c0b0a40502d0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 719448210 1250 719446960 719446997
    0xc010306031a091204140f09090c01180b070312050a0501210c080d020c04050f0c03060118050603040602071a042a081501061128050312090d 62
    0x154800100680324601d2510745502d401d401c480e03808030710751064500700ca580010180d620f03402074002c210746143c2250000000c3c28052480000503c1c01d5034891010b0034800c10f25940c8000c4291034038100620030140d840340c3c0142c4010b160041848402c1261115002d01d03000c0c0480c0425040c540d0400e02d050700003200c4010502a1340c1c103c8200c6442860840c211803400e0700e080c400c2c01010745020b0015440011041000c1145650014043c0d02400310028520b0410040d6040986201140c0300202d052210000000048a4010b00700742401009042c1c0e200c01c400b4a00302c4c1d41e001c968002008800c120901c02e0a40041c03088a1048041e203405010351541101841d206540c0603000e0048000c01c0400d024680620000e2241580300380c10041d0364454a084c6420b68060407010b080c0c40010040100c0b0307421031080742241514502905030002103070110708410f07540803084140c00c89042c45800c24440d060044490303a174403d1a4004891800342280345d07403580d90032009000100021140224040c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 719449460 1250 719448210 719448221
    0x1104050a031a1f12020d020d1103010b060304120f091701050417130b0c0f0609160e0f041b0b18030c010302040e0a1a0d1a060d03050d0e03040906080f0c0103 69
    0x41c21400041c2103401c16a0048040308600b40403038000d072105000f1b1000d039480c6030449aa6520032403180c43d00d45060028942501d8000c1d40850280c0002c1c014403002030001480c10400900c80d2415000d1020075000454442a2030b90104c0d0480362200f54407021258103421140c41603018111454150360711003081604c0c0d10609400d0481a02d003503000f0700080d84c0640040c020040900201c40081c0385070304040341014000c1e80e0580d41d5034014070b00741e202c071505844200000c240c0d41d404c3d2040f9252420300194982300003000284840c0103240d81e0345084c1c01c8880000064441014034544640702451030008100c0030001c10742c46485403c240d801c1a610a002700c42c01d448045a0703492458a0f07882c04030b4050400c030020381c14002c0c5c50b1380e181c0c44152039200d002e02c00709020f40308841d8440c030308c038a034070307150000280455024400380c0d01c1030310100c0d1300541155060070700090002000c031a001355503419030003076401c0014682c0c10100300080214000a03d9004440b001041d565401203d0005508840 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 719450710 1250 719449460 719449501
    0xd1d0616080c0a0c060609020c0c0a0b040303050a1b0c0810050108071202130902091f061b030c030c0212030403031202090d021005090a121101030b010203030a1104050a031a 76
    0x602c1044640e04052040d080d180c80980b040b5070101c1c01d940c81c0d015290590708110301e061000d41c06801044124500310400700e0080c000400030601d46403c0d0385001f46035200f04c00c4c000f010311100c64090750540214442c0300c003403680c0000b00f0904ca161207540e85903e9410302502c1924260400c03001080c1960003040d6142104c0c5581052480902e850382442903642d41c4ac4282140750340c4c0c42025802680300c411031a403140350703003003100da900390052003007580e2188054111404100380782c0444c40c510074403090008a0180c040c18140603045c0213141c11500070003050002500002d170041c018101500010161050703e1090311a58881f042c0114030004a0041c450959070000082c0000750140c01c1180500e0868a150302d03041340f602c00c440003c120081c4c030550040802c1144e0320b00c42002c0c4201002c40401400c0246030520245007200d0000750742e80400b501481100ea51559403003000c84100c1c08440007400c0150104100c991780e402d000c01c44100242d900349101c000d0070300140740c50194612226404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 719451960 1250 719450710 719450731
    0x703080310050438010e1c0b07030c090f1d0612010903050a09050409082b0207050a0b070302070f171b0303010905090303240a180911010302070203060c0d1d061608 72
    0x4410003400c000301f5030030100c150303a0004020014140400d05c1d00c2c070301502c1582c1030744012551800030000113004003425131050742160766411003480160b09a070002d81040980021039416500e40c1c80000e440c62503482041100d43d8a0706015038101600000600481c08c880e4645a400f0b583c0c1c0c0043c00250f403e03614005006110800c481e8000300d0440c2032080c154180308065500d0b81100843c040b0883c1d10000e400e0b81c0300c0e030040c1030350001c008209240d2035000001740b030b0550910459039165238a0012100e80105000d14011642e034600703c40c0e6054440000c105031200c44040b000104030743d22070740b081c000c0c4d40d003543c00c05000551502002040b6802001542d68034801e4491982c142e1900da1020052164440910f10002460b01500c0c00030200381044090f0002d000c44540c40c00310185840047c001e410b05005012a802590b8003081c250750203010300b00c1d1940d544242044101c010711409540e402042d94134000310301c0001000840b00d20a003008040445095200201030755000b83c121080c000e403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 719453210 1250 719451960 719451977
    0x31505030f03040e100e0906190c021f020f040f1511100c0e060408010f1407020a060f090609150f0504200109170c1c0302070308031005043801 63
    0x404410301102c41c1d01c002d0f4084045d0665880703001100c6010070595401101d82c0c4258140981c20340344030a07190318480e41c81c10130054008400000b035200d0b8812900074140c0c0301ca91462041200281e012076448181e080f0701d040d40c0e9511400f06000b03c01040c01640313030241d401c4a54015082c00b52151200d8081d4a000420541107002802c60140555090354410050707150300b40942611220054006004d410b0000f145862169403030604450f01800802d500050710010300c04400e4010503082314081c0c208001060702c480c2810300c4000741c241681700070011481c0560b103034240540d2188080300450384050900880000070040810b0311019140034103403158020600b8905544c0038021880c0500c18103000080640e60b0780141d06440360402004480d0b04010258086460400e15406040c180d2142c0702c0003d4002d40c80c025035400d50f501005142400000201d1000c00750708445000525004000340301c0303400100760010742d00c00381503c2c1d824101c006015407204a418881100d42400040c0d40d000c04 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 719454460 1250 719453210 719453219
    0x80325030e0d0f060c0509040c090608010504200414120303010506090402031e2a030112080901120e160608060d02041a090906041101021c0f030204090c031505030f0304 74
    0x12180101c0e030b03080740d02032422001c100005030309005481d80200319454490315000d403482404142e032580784d100000c1000c0d107001400221b40203854941944c500795400184864034808851000e8052201c1c90400070011800061a0a6009040b40c0350b1400b5220510070441047e02d0b16500d003c20301600b94004424802c0000d1414280d01456200001d445c1c1c0003007d0344161124040300030155010941c04400b007140546070040045035140c88030142d403080f0f28640c9481040c0d603a44003543e000801c0301800040c040040e030b00c540c1074051903840b071a0b400c100d07402400143c16039410300403101325280b45d20201300050982c01030000c148900070290041e008421142e08000091030a0150304285d040548000800c6440300c62540b842001c9040c000d105e181000d0400d0040d0341d5000307840c6411540b102548030003400341e000198041030341a0800e14000380c07084c00141c000c0e0207260021404986402d19032008036606030407001e5504401240090050b80b180181074640c080020400c8065004200c01c01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 719455710 1250 719454460 719454469
    0x108012a050a09050d0b0906060a1206090c05280b190e01120f020408100e0d03050606070605190b06180607020609040e030c0d0306031703130804080325030e 69
    0x442d0010038a400d5103900d40754400100c80c2507084409461152201c0c1c02c0284c2220200491600805e048400000003450154035240e12110303000c008200c10b88501c0c00740100102c455000c0301400c1c00800c3d400d0019050103880458041020241502010b0900001000000d0404540340c1c0584e10710490180400c3e0030084e0340802c05020310a0400405107500d20604802e40f007906200046410056550340c5055a81da00d0301c03c0304503240e0700c1607242002c000360310400000c04c0b24540f800340c107022270b0070f5641c08002030321070240e004041c2a40e0305000410541100c0e070310900903041c0302c8c000d003080318185000500c405402505844641e074121a441200b60303160010140c031510344020880d03460040c070303480418141d0b030308030441c00316036031001c41c4d92547e0aa0a000550401041d0701e0304000503071464488140d001c124501d0203403142c80001c00724001003410000e4403145500416100d17a12561004000c4d940da0004800764020b101c200603464048280d0550309030b001c0d8040e07990380c0000d0030708002c10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 719456960 1250 719455710 719455717
    0x3020409050f0f0a05010e03040e0f0703061d160e09070e0423061c21030e1c1b05060105040e1c0914040506100f050d060e0108012a05 59
    0xa4810b44506202e101098008002c81801d082ca094040e00341c48181d0325090303081d510194800c5245410900080c4000e1448101369540074481c041000c1c102e03140c0c0c0a040c0c1c0100301d0b81d000b0010402c0e030010141c000d88620a0070601a4900420b5103140e190425070850b2076620611040e68401c1d48040442c3d43c09200e0f100b45004000c0050000905801909008804103911101603442c4082001004030901e08080b0740d2081c44622004840f41c108503a444402176160003912800d51106000d1040407030341f217030f4040e181d2401d40304101c480c58069002200040e4800318280300c0001c403c001103205800f129200c201580783d000009101c0359080c1010000642140d00c020b540030703c610080d54012400b4024000c206c04260303110790103100e0520100c07001088250701c0301c0303003c0d0307003040d0a100446e2143d40036840c5190b1030307203081540b100d80000b04a901c0d110b0301c50381c4500b8a04004010880c3c0c1181e110050403603200c00000c1040031502d42000c5800c210404034181812076001c13001c600a07002d44002c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 719458210 1250 719456960 719456963
    0x6030318060806030a1131110f07150b06031005031e030d0c020313060503070905010309021003050601091706010e0f010e0c130f08030316020f0a15020c01020a110c010e090103020409 80
    0x4540d1214100070801c3c07c40004090384200a42c214010904100e079500c54800400030a4034242d250a01c2e0100e0000c0b2803040302c10091400740c082c1ba4901c0e0909540d40025403000005040300e9481c20118503903246082d4034000d00c0e120340600c080609804904441e2700e80b03440c0400d0040d504010a403004000105400802d500c01c0d804200020403459816030340c400040d08003611882c4e1070b0300b80038000811801043e040380e41071615001301c0c2c6c4050b80c4c801040c03108103001e41c500856265961401220705201650001c000000102c0740622258004142c4505035501d4524980c10b5030303201900711010810038402c0c0e40700380820001144042d020306000f04400c528080d80103a03038950700d110040e1440d0003948410f49940000c000e001d0550321010003480c2c00501407000b46450a5070441d00c80c0c440d0001c0400414034000b000800c1ca2201003601a1030010204030001c5454004485d03010700b17904480000c0200e607002e010301e074044a40c00341e90170901c01d600103000032005a0850f03080c04000e092100c030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 719459460 1250 719458210 719458219
    0x20301090f1a0a050d1e1b1e03111f020a0303050a0207080405060c0142150e011106070206040b01080d120902060d050106020f120306032e06030318060806030a11 71
    0x1100e008070341d40c60300c4103074425200707c0800c0382c61a0a000e182c2403821140d000124040c2c020701c13015072940c3d484241075040e07981040f03080311034240301030010381104003a0801d1000081540d840c2c890312a000b140c0f078500345019440501c80c1d583ca40704600100d00c1040c0000380140e0317050105002605181011340441e00a040001a561b48001408181080c607010310384e0b100d0011040c004003011880e41280007110410500190b803d0a0100851140450301003a504002c0303500d0030405182e110b5800c0080200139441901c902d402c200030000e465400445094620800d008000a035400d4009289a08100c0755036130004015072000356100a045000f80070382c0d20000501c00310421116503c2180c0c02071040d90014a140341d03801d0302081c20710044251000d111001442049040c0d00d02240c1070f101d4a0044072200d6103423191003030840c0c9505590701405440ba191a401104054200c45041030b070154401a10ba0302d07590b40c1c0c208403409081215000e4150f00110214800103c0300002e035400f1950041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 719460710 1250 719459460 719459483
    0xc0c0f060a1107210c0503010e0c040b0a0b070809010e0105040602060406181e050c0d050a0212031e0a020705040513060905030d0f05062b030c1104020301090f1a0a050d 74
    0xc0161403104003088000c00e10b50003a07652010030440021000c006c1400fa40240042c4003000205070701c40c41000703840d070301403912000e100005076204a515005058141d0446071203030440d060042e02c94101d00d050501003260189006160342c011002e0b030f000c4900079401403c0a94445d50b4800c043d06540346203c207140c6440b181c4000244041d1142c40414594204a446207030490a081c0d03d8186034080e03071401030140c91940004241d001c82c1c0782009503015502c0034450314400544629511400208483c0c041d000c400003510840450001c00b030381c1e0303010b60840e402640c80344100b0045800599280b1484da08165104001461035048000042d0049050300e040404003010300c0300b80d5000ca01c000309070759a15001c0116924041d00c0c0c01d01081d6800b0b180c80e00618940070514410301d150340002d010b1184140450080042c2a1840100e40d14054410354695030b58900c1d0030040d20f0000c061041c8107003016500018011960500356101000400c040c2c002032425043c02500d0400a505503018400340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 719461960 1250 719460710 719460719
    0x140304050a0303020d02120f0f1e030108061801060b190c080f041a070305040e04050304080111211b0904090501090f0210030504050303240a0b0c0c0f060a1107 70
    0x4080081d0b00130b4015251800c00b40740000c0c14006144075010482c4014001c0108104400d81694040c1c0c5489a072550b98014411401c0c401608281c00403007040300002c004940020040b880301d0040001c80740007500f2150a001d51405c0e60b185000381c808035501031041c4101c24100359030b0b001c003102c9141804e51031030216813500358059210340c1507a0010040020100410000d40030049000702064148504110480c2d03002880c9218620030840000080c2c0003040a205091049600806554008000864052055940b00e0300080b0038020301030003205001d04000120b92100f0300c91219245144800301c1192802180d50b0083d041d0650040d565000800000c2d2007403141c0b0030000e01485018404031001e104021004031a26900400c2500341818040040d00010a803138021048070150401031a400100c052010f0007400d0300c1c2e60140d4144400100800c0c14401030400014040c00d5070a50403404c01400704880b14440c0d003070f4204800308008051503100702c3c3c00b044884100d43c20b8400f503079680d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 719463210 1250 719461960 719461969
    0x204230106090602101401050405040201050408010614100201140106050a110118170a0e01050d0212040b090d1404090509070e0703020a180506030f06040e0a1a0f011214030405 77
    0x240c01000101d0100c0400740f040c80e804020104540820000c188800d625001d07402452a506204a501454480005c9003c6a0003801038030050488a00204481981c0d04500c9079400701c0b02c035411380114414500701e0011881070103021503490805050f101182d1070550b04131402d5000700ea0005c1000014451031406d42801e005da441c04484400e64180d82e899a0301b0700000c52500e55003001e03200c040810500e0781b09a04190f00c0c042a803401d0034416120307001181110064418400340780d2080ea00c5208000c1000300b1104018000c078a0034048a52031220b2007001e8070816450040f11926140c188010403500c0c0e090341119502c90344400503100015550100c0c824280c109490010108ae004030383d40300307a00e51104910041c202c0562401d18118038001c0803d90a11018182d03a07580341e91100010303826220341e001059260b03008022070f40440058201000144410441640c2010361000403d0190303c96030400c9058500302c0407001010101c81d5184031180d01c00f0b1142c0b00d0540805d12002a0690302e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 719464460 1250 719463210 719463281
    0x50a052e0e030d17010b04061b050a080f0a0306050909030d022a0d11030901120c02070308040f1d04020913051c03051806280b04060f050a060804030c0204 68
    0xc56407113800102c140e915074010080340c142c00558072504140010080e8a40c020510030908040c83c400501e003194604145040c055840e0018200c1c080018946110001081c0200402d0040e681d0800c000e0340c0700e108124030020709803904142680f051081d020080740e40d0380105102d0200c41c01d18210105040d0322486031541004505200341c10104902a0240d04140305103440e003683c0020758a0202e08000180c011091f4a2a80380d91564070384042c85010b0003041300001840c1c22020490300c4680c0c0310301c2d10400800a014142d0600701c0c502c42280c455114525250141b03500a00101041e5500900050078050705e1600b078509100319105c00d0107098856101c068504195034022845251008041344c501c14074980c11903103075000904000e40300c00440d414800c0c10101301000820701e01c07010140700140558030300351035000f4544003002801d2242110b1440446400b42c0710300060320f50b10542079403a194212400340104142010740001498a0752080345525403d201e00600000201c0b180e90b40d504 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 719465710 1250 719464460 719464483
    0x4060602010e0d08130f05241006080108060609061503041b12020d0213020c07080703120203120f04030921030306050d0f060b0f120304050a052e0e03 66
    0xb55107440c101c5410b003092100003400560303410484401d00f401c2d9101481c02c030049801070201c2c41c200a08034200301d01845070f28080005440345644071904580c500c1c64020f82a1285404403440c190000303420b50003440304904a6203014041d2445a59003c1072007444a002408540e0200500000b00026203140000e180201d00440107a0301d8283e0000f240c000d00d40c8075800c68481c01c00704048800059a85802581200307505940d211042200162848064007415504e001d51303014054020403007000010740d1004490041c80c480700400450b50301a6141d204002601c40340804060029401c601e1109000d80c00ca03100307292984846907507010880c1900480300d110b14078405030071100c6050641c513014020103040200e803944400940d680d0f07601505c03040100014556900c403055005507980310381e40001c1c0498043c10b0a5070491454280329141d90040c003615214240c25840030030182850700300a500405141c1c0100640102d52a5003070092105001401c10495000d44540041e18248852039001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 719466960 1250 719465710 719465713
    0x102040f1d10050f011d03070810050c040e1506160f05060a1a010c020a05120f011116020f2b11100c120c0503120712060503062404060602 61
    0xa86268400780c00c0408082c100c00b4880000e900148100c0e0b4882ca000c81a410b400d003000c20155088103141844c002e08031948503410700500c8400200100d000c1121810b50000d09410005039950111013006030165002d00009507240e040061500c081e2070656032000c65005000c0c80c10890000818020b2042c0ca42c02151400810511007042040c10060700b900b180100800b80300c00c01c50003980710700340d55458040a04020b030703070100d080554840f42c45c14800f408000e0301001006c01c803440c410f552086001942d80a0390310b8000700f200c000018a06aa036001001802807016001c1c6408200f044025807211540c407070320800401c01c03c42400008445e01c10b0240304450708048803818182c900c2052080401c3c000c044000d507400702540d10407040304413203621103e0421031130400d5100b1030700c0d400c00c0d28004205110000d140c0e401540070743c0e42d42d0b200c1d80c911f581d0030a241070340c01e03801c605940c194400c403170701030703022201007440d12200b1420b44c2c00d455070000282c242c2840844c0003d065410990011016 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 719468210 1250 719466960 719466989
    0x2012c010f030e06010b09120643030e060109180b22060f14100b0a0504030b07031d03120a11160c05030d180e06060f0310051f200102040f 61
    0xd0a2616000b801a234441010300303410304c4c240c030f00d5240c0f01d10b5841e603120704031213600b9030050380401c3c8c0b00751000480002550800c0030310034080c2c00740003002c031281e2641062003220300014404201e40100344000e0200030450700c11849640d070704405030300003801d007031107411003071126002068890125420725800b0340d0307001c01d02800070307100101206e503c0301d0546560010700c401c114414085800d0f0208480c800314a081d40c42c10300c90380440c0c460280e84c000500c10000142401078540e859000081e40f40d40c9802d07041d0540320301e84040c5541f0b00c1210281c2440401103000520201d0f40f03076004605c426030b41c0008501d000340c20030039964140c0002d03008850a445125040c01581010407036080740595030300303041c007002a64071b00c03041000030a0f1083c4030000341f00e01c0001e0042d0b2900c50694603e42d488020355a00ea0400070080240c0042500030300303001e0960300c069002c10705038900e0301c000001c285031600f04840300c22020a10802c01011800c404541d020000050700c0c80b01584a24000c08880321010319 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 719469460 1250 719468210 719468227
    0x40f090812041e151104090e15100b09060901020f0303040309081002180f12070e01081506181e04120f021f09020f10110c040c09050103050a111602012c010f030e06010b 74
    0xe05040103440c41880e11701c220300c1806440c034bc3c0011100a5842180c4240d03c491110004034a40710203044030300941c0c0004000d000030907801c2072641c42036501c81e2094a40805070f01d07004400b28040c4202d400482c0c000311491090314101721510782c0700604050075440d00004001e24103840d00351643e00003540707050240d0041040c000240200721021a00b000340b0312032070400302d0004010b45075206440c107031103400364003050b0b41700d000411050b410502589131017402c1c03a041c03d01030551806508068003080000b00d52200f298404520212902030000110a0615240c5803240007404940b20490300620b0f01d00b800703540d681c1da00e1803100f0000e07540c8d52008040c40c010b541d11070500d0300c0209480e0240741040901c05840380c00c6200f800503070b9400e01c1c001829642d101041c901910b03c8a039a226800000101d00a54a100345200c038a00c41c001c0e21480c4075400b40141c90301e50240c256017103002c200005900d0060641c0300306110804401d42c0d20340802c60408262245081400c20392050a198800041c038aa = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 719470710 1250 719469460 719469493
    0xa091b11010605100f1106011401180303080a110c01020c07060212040b04140321030601090b0f030a1d060a0605011106040b06040f090812041e151104090e 68
    0x4010340300c0200a020941c9004003141c24a01010621018041884035181070036100381030641c120410030341164990b594401e0040d1038a80d103111558005200180e10b106100f9890380c04100310b90f030503603504042d40d4a90341900c0060400001c03084c0401000c015038450344000b4000b610b114540100038110003443c00034082c1c606a40000543d01683d01030000b0840c1300400c4003960200da282c020100050b40902000900340b00c8100107200700c505109032a54120780520024601c20002a00c481440da03450789800701d8980940c156080740a02c0420010344104059004900307581300507106d002c030301d4100d890b8007400c14800725084107190f6542c601c20011136a0054110600b03030720390009800a400e1035103c50050b490014441c5020340d4540000c00341441056000b04049030300b048030191102821102d002c440355013030350140c40c0c0c150000342008070320391048030410700715500c480d41100c0c20034103010880143c8060180a0080e2a06210000f40d01d2180e028150140f42c4030740c043d08201c0a00c600f40f0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 719471960 1250 719470710 719470727
    0x30618010f110c01060608070c02190803030a140a02090303040311060f0301120515070c030c14100501052e1d040203130510050108070b0309070b0c060106030c0311180a091b 76
    0x1b00d0800000e8414803d0054211001e0424150103581c0d5901c1081e00b2440c0380c0c80c140c0264404e411a100010800400360f205a100e06201300c280d803075180294440a0740c000a03400341110580d4590010002000001d081a41c00d18165901a24040c00d0010703a00c0b012260b0340091b4414107600c0003074200442080014441c1400c0c190322310040c01c0d480e00f40f02c0780c0145110441d21004081c401030401c0d0b417091281c0c0c54000c007458501c0d80d044070034105000e4000d4018040c2032081602443d04805162440d034105c009100580005200784c1503003502c0c0020031145010400c20210b80042132100700300740c5403107d0000318031420a1028070344004580c0c0c40c24900d084041d50410070f11928090040c40030fa1400b082150455051140d141e03100d03142c1000b5103003407990035440450041c50018010070700200220b6041d049460359203042140f060500c000754255064585a080140d0b400c014600c4580c800c1520807422140c00b900f10800240c45400c080300300e50700d1080000b541c0006091280440f81e200028 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 719473210 1250 719471960 719471969
    0x90903020a11010c030c021306180c080907030f0b07031104031406061e0409060b03030c06160f0207060c050f0109110f04060b0409021b1219020606030618010f110c0106 74
    0x24180c44130749031001014880d0b4080300038850b45508004c20350404240d00800098111848008640300c10b40202800905802c01c40901191054000542c2d115000c5942d1080702d422004904200700389540d112a10b0600401d11300600d55551002c0c0c841114120160019602c5281580c5c1071070303240310109180a9000302681c0c41512036808420013092000c01051499100341d80c041607060342454928043c0082119694044c400401c1e00c5d5038500001807454021044d030207540c94405000402102d103808891000d02c0542d00c01003040044a120300e81c1c017000180a0401c2c2da0111803580d0146081da59840415900405001015026850b0901d40305050280c100d134208411850b025a0400b24010341c41807048203580850f10103210312424061102ca40d0f240c02c103980750042040c2601741c01d904101c86d8030100b101140e03010022103000181c03a0307000c0c8900038010b0078569995403034286110100041038402c0d540f5134103c01c1840c001800396000c5812600812038a0b0754a1188150071070302194403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 719474460 1250 719473210 719473217
    0x30c05070e0f0603190206180618040606020f07051e100806040b030309150703170c070605102102040e03040806090c0d12051809040b190608070608090106090903020a1101 75
    0xf14100541740241040c402c9030303055442030f17203030380c0c0c2c0548410400301207080098210400140916084145105822002408640c2082869213820003260303240201d40b00f40c4010360090350140b0030341c502200a0240c0c0f40e00c070f1038001d07040c42c0540c01041e5101d207a90002d001052490f0f091101d03601d040c3c0a1000e9501040d40110b05203141070001860101c05072004000010001a064052510503002040300490900b03d130016400d0001500029910202c3c0581d0420314050101d02c88502004d544412540ba07000d80700d840c6001e1345000c40e0320080204040343d01c40d9070b1b0100c0800001007030000d070004110031005495545050002c0c1e0381480010808148a82484102c000020f2615444417006c201c551900176155105250204010940c0d20241c5038425280070400007001700100d80640710311903d104480c8100000781003039080c1c42640c0141116a003201c1024000c5c54800c541c4194005285400031400343c0d07460801c1d40440307104200541c0140c2101c0f002d907081c04441c083c0741514240a19 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 719475710 1250 719474460 719474473
    0x918050d0503062413030b0108010f0506060702010f02010b040513031b05030f070312061214070b0301050d020f2107060e10050c0c031e0106050922030c05070e0f0603 73
    0xb00003800b1201000b400c00404d00315001c81c0022200840c040e281174448005050744015240c0c1002c0d0002042440b40104130b40c281000c50500f5030700c60042a00901c40a00040e04103025a0b0065880030b0b40d1881d250119960b03000341c000d031a540e03030040c140983c0c000e034010060404c0c503090003041500d01c0c494a00c403400d41c1c0300603c00003810000c104c9401c0201c0c034000f06d071200d441d4070382100c9041c28641812002810445c011800c241851000410b01d442116420400a1040300440d100c241c40d1107040b21a0400380010407550030601320a41c0000c0c401030111480054650008103080c16451000c10034861044e910200f1280c10004200900383d6400d040d80c1030390070240020318241c0745086910810402040f9000040c5d001c102d01d903900c200041c140d0b114510403084060345011460071800342503090401c000381c203042c081c3d0124003480014503245503000d48000c10f0000c0e8140702c1404c030700708121a115600031a0060002c5000703810110361140d180c0c1030403c03407241d00c044081d0aa0340701e41c0040c0c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 719476960 1250 719475710 719475721
    0x1020c030304090b0a09060303050d0e150a0513080c1c08090a02190b0d09060f060803070219080303040b102310090506040b090406060507020a090f060918050d0503 72
    0x41e18100d038083c01d00829031904d10008200c1d4980568030506403d41001d1000c0101504000034120300010080c04100d6000d814500d95610760440115849091030200030850038111904026401012000703a8484058255620103582c2c0c429440c1d842d2a41005602403110500c111040207005001c6ca8040e4990900c2940c3c161601c1e08040024400c0b03d1454064420241c03184c0000000d0455a401d280c880142149030700c0503000103082220708520300301c0020300b55105031050009495800d80191f080401a500b40304440c59901466210404917560000700d894007000110310035031255413030941a0403c80d604100b916055003200c61075003007202200a88608048550b8101c5004450741c150001419000303485070581c5800481d000000090089000041e9400a16041c10143c8082080940d00d010848407402005002075211000010400130060240c1052070a0b0030369500004139160b4070064541281c3c0d0441001074080c0f07441c4400c006010f41440300980c0103516003071039032651401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 719478210 1250 719476960 719476963
    0x5040c0e030303150d1e1505070509120f0601030c0303080c1606090201030f060f0816080604030f02010b1009170703171e0d090b09010603080406030b0303130f1401020c03 75
    0x3484039901303079103440440e41281d4031400c2d0242d00039041000350310746960451184a4808103408245c81012690080340b8540190344640c900c58941c550b5054204002d2004102410001207440707174240c8581c2140b10803090341440b285001b18400c079007448180d450740c41c000d070001500429444c5038a1061280d84810400c00c42c5051000d82d1021001901109501c01a8010f0501c1c031901100c080c604440820949182c24555044c0c1e000c071021521181482419005541e145000760b034425000b0601003400640580a400c02c41003041c000491010389800200c1c8803000c4c26040100011940c140130424401002071804290704043c000e4060241142c4030509010b0000c40c450303064040c00524074620800020040c11542000b0344665580e9500400102c041c00c07144005951a4060b03002050300010140b00e09401c40b035104e8230481c01c10f40f42c0780080d402420600351803030b018002000f100c43e0040040c2d1005020b810200d018030701150074030003481e20200300d01803500d05541c010b5a003000d140d40c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 719479460 1250 719478210 719478217
    0x2090f0603160f1a0d0e06090c0d0c06180b0a02060402040f140601120f0f0504030801051009050402071a071e02010b0105030f100503030d1b050f031b0f1305040c0e0303 74
    0x2040d88281e51210a03032400304c042d500c580100d03c0c03040307440e0104400c20b6030004180c007406050704c80c1c125103002000b0001c00c0115802031000400c000c2a104040201c5802000f49841c9507640203034918400d95034640c0c0303440643c0044549001a040038040000b1442c0610840000d4803e1a101304602c010044590705601c0d40a4540c03814002903500540400a9981205109600000003030182501c0c0d4440340015080a6404402013102c00001080505100503082106011641c40c0703407800f4a4403050000a600c8031406540d102ca8003d9a11808d07000101d1042c05003401e540d4920032070b80721007030031070420300520003030030442e4180b40711000c2607030384003090341e40020400d0313030700030050311080044034011016521668140c0000724241d002c1000a50044d600401000c00c686c060741d9420a0444d00c5103c0c03210380440342d600900200301441000d24540000700640c0140d1454420003034071400d0f50f5040008142e4101102e00e9081c80242003a0084030045800c50401645e0b005000000a44901 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 719480710 1250 719479460 719479469
    0x10e04080d2c07180c08070302030402030c150702010906030209010507061d0105040b150307030b040620131e050a030803040c1d01051206060102061303020a02090f0603160f 76
    0x140c680c04521031042a0442d070000c002010061050140e008a500c0c03929001e081c850b1509940c1d203a00c031891484243d0050003490003d1303a80f403640b595100c182c2034000b90400390003680c052048025100f196210321a080848440120540d03403203650b80c0c80010407402d080c0d0040c0040500500540c2c071140d82060a891906900440201c0c0f034484e805810303442c059052003200c042d5801c1c4000d101c103010840082038004c40302c104040708816001c100303240d81c401151000410a085032000100810000da005030b009861008040650400c0101c08907410b8001800314041c0414603002000100404c2c600c418a409407000300d00710191516001500726021071002500300b510000c0083c04001401d081400503040c03500000c0e10001000b0010260410300740a01402009102da000c4c0310745000250152140030164003c040c02c0d40e03082483e04594485140441c10b500c02e050080e0300582c3d0340ca451034410348412603480a0352415070101450000000c0300b070303031300300c1485001441212240103030081900c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 719481960 1250 719480710 719480737
    0x120c070f0b18010e06160c08030c070507060e060a0507050a022e030e15040312020307050901030e16350309040c050313032a0f0215040e0a051f06080906010e0408 71
    0x100303080300087e501d40400380c0c4003c00e81c0034004200a5003071440c2028261890045003183c0d66591a11000e8503507003192a10f403a8404014010040180e100d20300800c1941d101c1e50507240400490384c04290100300c0e408000074000e5920721180d007550050350032a000d00d101480c2c1400550b1208204036111180c1c0300d001548442020002030a050040c1d280c1001861131035000c540c1c0345050f140040a0790401c2465900103030402d44003413000200068a1041d0700007601540311072510300320110152881010400340407030b80020400c034685444882c0042d0345542074014503039801c0501c08001c202c0d5400d103405001d01900b80180111000c2c0e8000c00d04111780e0504055880005242c03111404400c040d94681d4840101340b003410030005400f118a030414802c0c3c60794a584035a110b40c01800b4010f50044020b41510040020005007290300481c1d0420280300540c80e110502050090502e41282c00820102c0c036017109204001008000300c80c010984081800d04a04150751000040e00c44c0034040d1031003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 719483210 1250 719481960 719481991
    0xb010509100302100206070206280c03060b0d0608010b01050c100c090e07050a0806011b0602030c0702042a0302070803060f03120d060611070506120c070f0b18010e06 73
    0x30503075115140409503400a2101d00c0c0b580b07000000964459003140c4540050050310007280f001d15a00c501c107031748001c005002810050361921482d0040820241078070406454400001d800d021500c0148007144900001081c29400c1c40a01820354800d400ca09040008c10403065044003404200d00c240e50b84e0b00800411414854041156030801a4106450840344c0f641400003290b0064001e040780000394440710134070340c2e50300015103030020701d240f0104204e410021480d00242c065402103503c44110910035003031034019004a03084864010b400c0840c003280c5000803035070241407454104155160318082d40303000314035551800a40805095039018500b0808101d005035014418003c800400620702900c4140e0450070002400c1d00d4070640010500304596030324103040104040d0182e8402807e0113140401440030a03151407001040350350b030101c00340000c60009400c4140340c10460302407909050749040c07034200d00c82e1080b105082106980e250600402d24981c2c0403450680c0090242d441040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 719484460 1250 719483210 719483221
    0x901120f15020d02070506060406180e0f0f03280509041a040903050d110408120f070c0902072901030303230a060e0f040b151309060b0114070b010509 66
    0x164000c0741c07a424180c280045401c15200d003a80d8058028140075170121003860702c41e02c09000455107140103503140d4407184441c4189588598000340c0c04083d81004844801e803032070407594203100300c0d41c0480300c241d003002403800c21869640c501651411044854590803000902018055100300c502d00c0d80180d032640100d0284001c401c0070700c18882e00250060268800038507000380154005086401800d1804400c0b005009081050f1000e8500d172100070410114007404080b05a04003611005d880c0604000c5400080c007410a081e0040258900141c0c84018500e0002400d40e09022441002519902443c2c0600400140c0c40e04680d01403c002501c8030203506021340380714002440e14034403a000c03414410b40e060190700210807100006402d020300d8840c9050f8503c0c00c0c800351000352608500320f0218032210000c030074507a503002c8012f04d8004800800120402038a01d900070a6400541e142e801121950b004903024000006440b01645040d16664440c003c600040c080d1902503640d6000056 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 719485710 1250 719484460 719484473
    0x90c081911040305150907090b030a02060d0605061309050f07021507053105010c0804030b0c130611100c09060509060c0604080d110a0c080d0f0203090f0c0901120f 72
    0x2c02944d0400243e54401d8002d4401401c440d2054880131590b11490f48001200405481080c061000040c050a44c100c0540c00304a0b80303801c500c8001e007a40c0d50300c1c3c8000409545001c0288805101200c00160003880c2c80700d06d4085a500500100918009004101c01c0580c041a00100170088007518042ca48a081d0201c40d2406005c0408800c5004144140041d0b10081d8160ba9516880220100f10740d450340d00440c2d9203000440001c0013802c0521003480041c050b042165845000300d00ca850078014941810894188160f01c000040760f42042c150703500040030702c14021a440b101c441031100c41c07106440104907201034484c1c44c003008000300b140e402c241e5a50040303905802d4030304e085070040d08003410072001c00e50052110300c11080c07804600e84d1101e8100c005031040d4000c25281d215440001e61103c4c803a641c020300c009032a241c4d40340310ba0040040c5900c0610700a4a8101c0209204000300044516025440c4000c600c200c5101d401000603c0b8403441018880758011144007111002d0714000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 719486960 1250 719485710 719485717
    0xa030605030f010204171506060a020109050d03050405060906010509010b0a0302130303020c01020d03050105060f0c010b030a1b080609030a0f0c0f260a020a030f111204090c081911 79
    0x650741406a00300d4a1484501500907200ba1401201301e5030200b200d10200c6a90b500d403008000c48406855000030706203140890141c090003a6900010447c1812940c0c1d0301c0c00c06031003a07110301c0800d55a0303060009100040140682c050b481e040208519410302c0c0c00580392060512a10001440015200c480184282c060380c0c2210003824444080302d8503480d010352110160100c507401403141c030501e18031a512901400d412186c028280d2072600c28911103000e0a079002c008601150f40d240c50741c803002c5c0d80701080803030412409804485280409198800281516540140000c0e070003c42844280603002c0102d40f903640a0303060900c00f01a501d9003d9400c0e031040c1c1c2c0042c11071402c8001c540140400a242462110082101000001610012000c26000e40d1481b0703001640111605000203000d20303d4003107502424246000e000000703600c2c151074144802d0040d288241d0104041002100d28000d080030328401c0c1c240540640b030602c4c140d2000c481070301c019448480c0c6944e0316100b0985c5c140100c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 719488210 1250 719486960 719486969
    0xa0c1101260702060c040b090f010c0f0506100501170612070810020c10020403053408010f0b0a2405190c03020f01050c0a05070219080f0114070e04020a0306 69
    0x107095a0350181e2160756414042168000054040d0000050810102c01c0c101c1d820340d403031802d0356414240c08600740706d503034040c010055040c000111603280108000080418100741702c0c000070020351405958910580c1900d0340311a050028002c0822110304c0181401640118141c1301c003a840300595910360300c0c0025590200c0d2140c01403000501a42145400500c6500c401f10304651403207200707841e40c0089100d80c0c4006007030b07a0000100003250100c0444a00321007045a40510b400015203c4050130100f11507212014a81d950a03865404401c0d43c05a80500c120132601c04000c946030602c0080381d6400c104000307141d83c3c501180401407600520a4a41650540d0402c1e480710342c03503200c00303000000c0101007036000d4881d01810b122942014044c10744a14401c400c1c0c1c17824005a0b203020ba40980069504903841540e0600310f2103500c3c175103104d41004041040040201d00d45c0081010308560350100f00e401080700c00da081000264000e86400650031040e100140c0c0e46040c124124000c08144c1c10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 719489460 1250 719488210 719488247
    0x30d150f090c09140f0d051510140603010b030f07031e02040302031209030d0516060501090902010206180709090f02030a0308101706060111010f090c0f0b04050a090213080d081005060a0c1101 84
    0xa01c006401d80d905018152075402cad100040c480003076020020789000074405d00c41c4540d01040000c000030f07502d0882e181c018002c0e0030046544c60410494007075104054010310074081c0d02060400c03c1d40b50411444049041c4910f0507890080140003082c0c80ba50104140d50a01c40005610301005000711000003080350001020842540c681e0301c2c070741c043c06005000381c0c01845110046400c40c111031115540c41e400010042114a19040c07420019080000d03040c0c61207030b0b10340340311b9015071070900c8015020381c4660b5030604946480c14030104e04180340d8005000c1d4010b0200b106c00d42c032034000b403080d4200301c0900301055070038100e8034018050001000c440840303078180b42c09003080080101c6040c00f900c0781d00b5580303034101d503e5a401040d5070046104145d803016185000b000341086030350050040d421550040516a41c55040e01403034115440c030000002005481040007048a0140c4800039050480c0c51515107008001c00805100a5a101820000304c5252922160703004010140341003c0440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 719490710 1250 719489460 719489503
    0x3070b0f100509100302010305060d0605040b06030601060c030914151801030e01020c0a0213021201270209030d032a0203070b0711030d150f090c09140f0d05 69
    0xe100c403400d4a09890001450106803004500c034a0040700140c82280c1d4100c003080014a10340044002e00006170001d60400c0c0c00c0200c0801042c8039020302e0344598003401e00b00d8402d041031410b241c175042d17051348004208812800f080b40042d0340f0900120440d03a846104240700d007061400140f46101e8020343c21044080080c14102040503030760f4a6883e18001d07202088120880780d0081e09074801e6054282081d0000d96046006140400300700402d812441070040c1811040c0e8200503c840082c1c01c00c0713500980c0c0070060690061a031003403d91070207094034103504103a20003000c65500c1003080080000d1584400c801c0b00401d104400b041c602901340110903800412400029469620050040e12000c04100014072aa400b80e080e540c02d0700b031810019464504100d034043c001702403040c8080300c281000744000500801000b0108045e1006690004071092403800c09001c4110940c00300002240d0004030308096910702c2d07101d010104084c1d660041000a5161643c1464030119014000c06404d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 719491960 1250 719490710 719490721
    0x10f020c060f061207030201050304050102071e110409030912171903060f06080105010c15150503010e060f2a03070c14030f0304290f10050a051509010203070b 70
    0x74915004445181540c002900e402051001c580300941c1802c0c0140c0c4441010001944100029a8014061400141001d083e1756607186409c031540040d1416510203035141c401d11071060199800da05084a0402c540c203056900030346500d05034414000202400710206003071041100c440340b400030b070307115403290796175400d400030840e2a5a2205450000e840c00001051444125100c03505582c09602da10b0700741c1e032800c07004644229041e04210744000780c10f80610000c004d10300590500d8504075080200841c105024542140e2281040304050743c0410140240344d861a01d03102d030031408107043e001c04030a408009a0545008001802c031f401c40001c1041240c3e9444004a942c0340d00c5a510303000909115041942d0301d0198000401c0705200c00c001050001d80031f400600498080310403013a501000341c6900d0110840c00301c402c0500c010240b420072001d4000340c540c201c0901812140d071103002e42000c1c003040c584901d86501031440c100c001200c4595a00030801e50310309a41c08100202c503850b00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 719493210 1250 719491960 719491963
    0x50108032508040308090105040f09050f06030d0c031b170711150307120e061602010b010216030b070e0904290f0411130c090f0b0405010917010f020c 66
    0x10300d8007940d140d008030348801d0758058500c1400074026008140d4504140c11034a42000b540c0c48140391506001c8100000070f4007205001c01607005240d0030000042030b00e440c0d040250050030042c0f02510035040b040c8002100c5c0d4104a50601c0d103601881c2960120744c0700e00c20014040e1031000050044180b0340c014100507401030000340b194900c113881d115000c0036400240300d500d0b0701aa1001c2d414520510000d04c07240e20600c1d0455103208120700c013144c140c0c071000d003490500b601615100d0f01541680360101e0820740900a21800c0c500178401043e070120201c45602221001c0d000041950b9800804240283d11a40401855800050141c2c48a05040c6864401540070b6040c4132640ca0000c3c1d207050450460303205141c810440350000440755910382d65000c0c8508541c1e0b800f07030750080c0d1050000880400501c50b01e1458051515014192401c02c4046400390f42142d2150714440004c00c828400d50341e001d1180412a40c1c0c00640b42c3c601d041c0ca04800c0d0240c05c0c10094604210b2011412090504c0c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 719494460 1250 719493210 719493217
    0x190c060b4006171009030516060b060406020c09010e10090f140c12010e0f220804091d06041106030a1b030c030b03010902010509130603080705030903070b0313020906030a0605010803 80
    0xa01d10071180b00c841420400c0060744d00286000c0c1c0410340034800f6048807441c88c404034014500c503031030005034080302c0000104540c12607080030380140d0090070b41032402d080c040b030b0082c0900145541500766103409003800e402c3c18040d014045645481d0b04000c2050005500300000320045451481c0031450711525501e8150001c80b02c2a001d000384100011b001038564071034074041e140d080c08a6103143c1c1d80b0341880300410700c1d0072801070346c602c109000c00022640d4403000e00042c00d504d40000c11340040900c00300c5042d030000c0c40e0510b6503402c000c1c28480040c20280000328880d42c00d940e565100d03038550f0074080c010110700c00080701c08180200d840b6000f60b0b00d680050b0508645403810041c505e440400c1c14202c075600c800c000d01090f03080203000c08a02d401461042081c00284010480303030384131369440d1a90f8120460850f0785900c0410002020326051100d0b4010b81503c280290841c60200c0d0700d80e80c8036140d51800703400b5123001004140144c8062140101c2d013034200005100035607454005507079a60 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 719495710 1250 719494460 719494499
    0xb01090516050c071a0c10020a02070f081b130f05071106040201121104080a230a0b010311010c1a01080c0a0308030c030c190c060b4006 60
    0x1d800022100195014100740d41d40ca5203000002d19040b42044018040d00b10110a2070901003414412140702d11410000701c054013840d800c000d42c48001d005806843d081a82e088010307507400080c814401c6100002d8105011080010f50220010700880401c0b24946410112206107050241c042c4c0070320b61070340000d805010755a840725402d51001154507110502a64002d000910f41c0440120308c0195410582982c0f50a00d04c40e45066581c1d210540b4288150381c04582525020038008000306100d902c1404036040800584241c619558810404900500009250b4101580d00d41c91a911400720040b0042d40242880c0601006214022804800b40300d03100140c80380c04002d400030b040c40c03080b0b1030440f41c0c4500f100f410354484440b03486030f5400050071030484000601ca40314403841c0c001910490030005ea1114000d650301400c00d002581e03150403442c2c1c001c00c08020b0300c07421000c1002200440b070030444d940c030442030042c5000c4901c507035950081016050130144003042e100c4101d003c250004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 719496960 1250 719495710 719495731
    0x10030210170c0702031906180f0b1e2a0307030f0f0b0f240703080403030b06040b0d09020103111b061501050403141f06050f030a0c0b0906070b010905 66
    0x10b585503410445a88190b100003501a000398411004807500e0044000d1013600c01c0c40301151580b0b1700e000b4201c07150040042074440c4030045020b01f080c805000c1c0c1442c0c200a403c101501074034480107120210940142807088403d0190000d00c0f041284264540e0030812000051952402d0068004020b0890301402034612841c100203413200c1740b60b522480d882000c014220764001003400302000318504001c0b0344001c40414a420400300866002d005000a41c0301c0c0d03e840c1c0345802c1504004003101d94110070b030ba00030841000103005c41c80c140e03015282007910038000441c00148510049003d41868400c0f1001c0940c042450b9810b12580304209900d43e00702c90898060390f031001c0c500300c200303000c1440b400e020032001c00c001d0020403613a5240e40e9402400c2c0040311082480600c0c0c000c102d980c15040d0078907040d91201d040c001071808401e00131004004034014080d5a5058850303990204081c4120003031403600086000b180d4560105481c0d5583d0811900002503a5410011000d80011038400000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 719498210 1250 719496960 719497007
    0x60712091506062007090b1c083c030c1e040819020f040507050c0d020c0a12021e011407060506041103011a07080d0207030c171c0510030210 62
    0x11300c5a100c003504006420004100d03051a000f85000100042c202c559045046216401041e040c0350843d600218455864244daa4010b403810358001541d00c80100110a540d501c0c52020106840e00350307039100406c0a0207666915105805d0040d840f40c8603000c0031156508001811040c2d070580604100c6c0c699400750380c0d450700030001500e00c02c001498000d600036a40c1e542c423405800d0a40c0103aa0100181c2086450000311000d4240703010111a046401a40300d06c201e03041c9800d015015200404960400061160281d400540c10101080551103003964640341d420b5183e1040c07005d9109032021240c010b1760794a290411b00b010b820704a580502850411401a08140d941021a4100d6032110340d006150a044011407138181e0014000341e480d0b00050088487ca0010744c8024613820380309895484010449180100141c800b004500340d01104c140019003c1c0850018a0300f20b01ca00181c0c0054203030f07501c140c0a005d02096400107900480325089400d0374680040360f601282c02e070002c01250 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 719499460 1250 719498210 719498237
    0x24071b031e2009010b1e04091b05030403050901030911060c0a0c0806090d08070210110d0615120e03130b0a0306090204030305040e04030e030f01090209090307020306071209150606 79
    0x600d402d0101919800910700d074010004510414040c206800001050203404003100e414410550041d41281807070554501c00c100c2180c8443e0f0300054042e84501741541985060f85010349140996040303103040c191a10480801c01404080034a6881c400604294071100710010340d590351220544211081007103040c0100e006000001c0741441404010004c01c05885010030459842e400549401d06610400300e01c0114105c82e4019000c081c403aa9007071a85855691004100742c58865010007002d00558905403609030b848a802402c5001c088008158490b0006a103861849111800d20f4045103110020904a0950b0004d00d000c0010369001c0c0620b60312008031030228410703440007d011031010481002804000d01c0d0150388203000342007091344504600f02103130038441c8a0b040d4501595540d408201145407d003001901b060a1200540c01d140c51540407940d030341c101030030035810300000501d85881d01c1c0181d0800c030b103541c0c0d2180c040f510f8034500b800484040c101e103000300c0d400718000c00c800b0074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 719500710 1250 719499460 719499503
    0x8030705160e0711030903030406050c0c0f13091e050105271e010f06060203040609060c080d0b060c0f1c1e030b030102090411040524071b031e 63
    0x507140040d8580042d6290060265502d4010907030000890001784100c0010303a5050000d403000708440d80b501355850f61041c100c01d080041015543e031140c51003040d03068036a26224100c1803030007411000000d95100a081a14001840d456001c0c0205a41c0030144100281900424024126030740d0009400b0203040100d034900c014004c4d020050b62200c20302e07070700c10042c0d00c0394820b9450a4100004841d0305040c2c500094591076080280541d00000301000450751000c000001040e8900d00082c503440ba03565401854440c60040720701290700c403072541441c2e54800c001c54189120307080071644020350f13007165540c0b00c1d9070307011186410542c0c4850181c0098083d000359034841200e185140b01e40c040f4410103600a2001200b01600b5640c01d0000850341d4a4901c90b0b101445000c0c1801c40d112803400007048030801000d040c006000c0116540e14034051042c2003510b500a40c84003007030030952189000e49078415920f51001c0d010500c1c0c0180203910116a810740518503000d14100c4114299405040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 719501960 1250 719500710 719500753
    0x16060603061b080403050d110c010606091208040504050615040e04230c01030911040c050d0617060103080a1205010b0c151014030a12082203080f130c08030705 70
    0xc40c00b143c004000140003911030340061403040711030400020386024401410b022900710090541d00b50713658105c1801100e4120b8007400040c1010144078101d405207949910107800755101c2e03140100d450703401180302035a50404541c03245190b015001e4942d070740c5003061a4000c8040d141500c4600c2d50344141e103008800040c88502d800c485c44010411a500c03040110700400c000e1100b51116205403155520303c4c2d4031806801e0f1540c0444d514151180c0b0390a001000b1241c50707a102d0520a13182007140a040c003000f103050342c1180c1d0072554a5442d03044660090356105018142d40041e5480d00c40080380c1f00c2d4a100203002c5001101d400c40701c4115002c0c890030303050302d81a580500c410030002410012410b00c80d0f80860001400741c25900503803820790700d080c01c00c04240c0e422004115003500f00014070341c107000c1100110490701122880340001ea1000340801d40c0107030040c48840349050018601544201440c1181359010040d94082e03580c411a403622908100401c40e15030140d0391401a40c04200700f02d9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 719503210 1250 719501960 719502011
    0x1060302030705180a180b01020106170a030f020f03040b0711040b210c21060c18090a021303081308070513021b1209182502031606060306 61
    0x1c3c01c0c030b0180d68102640b4460500c03071030564008880180800d2402d858180c848599035034003004039011a0311000a07080d0744440e00300070044410400c1519084400152100d016501400e0a11510081d0300040b0b09004040c62683c0c201c2c80000f17400070f04640034900400c42c40c1e0041003180c8030a007840c81044196480e071000c1d1030340f01c45404034118507007052259400d0780c01c240200310b518908803039011501c104500e414206c081210382c0955044e8410074031007242e000708a20305183c81e0030804030000101700c29803580382e402038500c000001e00e04401981194000071503603024000700f603900c0ca482c49060384403044014020f99400d1001458031000030341c80041e201d00800c40007843c600140104001d41001c3c01c413010507060050800c90810040c0400c40410344441482c03603448200754284080c05250151650940008000300211030549a4001010b851403801b200002072041c1300480c5580600004001004a92040f840401009600650440e80304880502010300180e454583e0150800c1c00d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 719504460 1250 719503210 719503217
    0x15020d120c14030703181401110c07060807171005100302071119030f0501051f03020d02010e03010e010f0603141603032102030408120108010e0717070506160308010603020307 77
    0x2c941801000d050b01440e03000c1c03002c2c40e00042c54210700c00c80981d0340700305c502e0a0b02d004041c04a4403052034030038080c00301c1c113400d81803400745040001d0005a654000b940700726004c01c42400e0104504503c1061512501d40145010034000c0c100711413078900c003c00c24402c50380309802c2d080b28103180314000d000b501c00c89500085004075141c284001d1003e2a4610160a0003084400c413002c800281065800c0003500d01507400000e061400118064075000d0580e0803111009110004200607940ca40c07403031981c1c941c20300c0c09502c0c24074414040f03805410b03624060021542000d540011001e0380740e000c0402c4030f010301200c050b561003400803c2d440c0d80780884900d450b05141042440440e000750741c1d944180001031b400c104c0005e401f0748010b0481e003080ea401c4400d0b0b4800191580c213140040304941c094490840200010110850807a80c0c42d8010700c10b000b0441d40700c25203140501011301c00d441c01840050100d6940c0e204002e48607041070710a440c218041046d03003001040840c440e03c03c3c0c1e841a0500d85 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 719505710 1250 719504460 719504477
    0xe19151d0d1808010c020303010608060d0b2413090507380705030301030c0e0604060f05100201020933040b03010909081317010e03070807020d020a15020d120c 70
    0x1c2089031140141030218401d100912070001e0441c001340304081e4465180e5014503282c0d41401c1005024030350240c00a40310754803264408001c543c0010045030044100c240d96085002900d803652900b668585015501c04c041c03048070600c40307400340c0200342c50910540960310b03070f15240d51006c101c1d0b8100c4000c2034501e0035000410890111800115011151001c86090802c1459941e07186150300c02d8008a0b81d407580020200080b0b8110580550090b0b0111018403409040c0114501c901c000b03885070790b2181c03026460000d40c0e0380c000c1d8100e80343d40b41c000e0070302d0061019040b240e956518808030240c0320720040306628181030100000359826108000d01162942c1d1030b0070803c0f40500780303d0005685c0d111040004510b00c0d400540010010a0301612064840c55400d00050131604120f40c1c151150304100803410001d01b00700304941781c07a6811100508101004c3c004500380c40c030340350408403c00d50222010720710716030002040064100340c0c0d03484040c4c030100010b01100b03a03a2405d090300045841034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 719506960 1250 719505710 719505733
    0xd0606210c020703060524030f060a0c0c0c090902030d0f080c0306061903050114060c100e010219030b09060a05240d090804030c140904060e19151d 65
    0x240c00801281c4480c0c412a5009512a00c40008a54041d603090041108900c414002a001e8417203950454400f00c0203003200c3c4603010110390711460002e040070311490f517406e41c0ca809a4000e100400580c1e030000c015405080e00c0e0014030004005078041648031380b00303a0420207541032045a060000100ca640c8540b82034031080408040c40c1c00142c41250300080a1201d0a07501c907040f02210950412941c0215465140400c2805030344c405030030a501405041045c075204540c006943c02100c3e50420000a0400130704004074020300800e961042d0500d00010500c0340750b41c2c140c10261006604a441481d076440d580104903100d0850b1007a590000b01000180c0d83c3c40714100d500c5034100181c004d1052501c00710700c580d00c0499100300e8003254075000200303050040c42000da007248043c104074460791441048a00008040480c000d000802d0192148565406600203011002d40601d60740c071107101000643c54070340c40c80c601e5030096603145403829603030a1070841008445031010403104068100401d02 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 719508210 1250 719506960 719507027
    0x9080406050d1d0a0b06040e070e100b0703091d0403080c0319150303080901050c1912021c0506220209010201240f090207030f120b150d0606 62
    0x10780489a289a920f90340c0c90001c0704280c811942a460b6030002d8004002d084c41c00e00001d0101a040030f0007149001c035045140200015217400f80c2d004401d01102c55501c91400c106540e20300e40060803d1107002c90500109a0000c1c41c000070390320324061211140c031000603103121030f0500f2940500003810380c1000c100c0c2c400c0342d00c004540001102c8944000d640000c030141068034401401c007903e15548440070800d02d9400110a6003002042e0000d000c1d43c24001c4e80c03502c407402283c9649809008200d190100745001c0d07210b81d0501c0189290030364440b1010012801c0c1116601d03040a00c95040500207104c52902e400b252408a4507201100950441403840c2c1c0001e40005048a056640e5506181076140040b078801070415101d20240340301c0d904052190450b041c072a0311840c0c1441c01445048006a0410302002490060f80b9121260f031000e100c038000a02807080d06290060079074030170f62924611080c0100714181c428102800f4403661a1802c0300d81520300d100c907081107001030420100b11000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 719509460 1250 719508210 719508217
    0xb0402040911040905060a0b0103060812160b01060206060f010507020d0611070b04060b19080c01030c1b0f03020d0e0d170f22050a0503100b120f1f0908040605 70
    0xe0b07440c030148400304801160845207500800d0750154130040030003248131028050180100360070b29040c00b01e00e00c1d1800311a0380f4030b2441c42da42c000301404240e044e002c4070782204103082c413900440c0c1c02c3c10ba942c2d24200a902c68200b036031203c0c01848242c103c94810b50260040312461580580b4404100c111601c40134001d0900319014a60908100003d8001c5401c000502c0d0186001e0500062507030341316010041c64080c4100202158690310307900b001400408110200c0c80c040c03e0070301050f01c0002040485400300c01d014614803002143c00b11406220107081d84101c1c107842170302101c408041c400c00c1603400c01e0003101225881402c007141000018007551b5510580c5c825480301c903060408545000000b03800440510307003a804400c1d008049601244400001090140ca241303010700e051034082a103030025185500aa2a03c400740d0907481c1d220f244803524100c600000f0340b5600d1b41d0707402071640c95585169849096030b2250004d0007440d00c4501c00c00030303650b502107405031034140342010540e8185c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 719510710 1250 719509460 719509463
    0xc2205070504080f150108070312030902041413021206060a03030c02030a290c03040b0a0506030f03030a0903090806010f0e040c05092502060609131104020c06071b0b04020409 77
    0xa014400014407010800242079112030344006002c03144900040e9205e04001640060007960140c6020404200100c8640c030140340307149404910604240041030280602e00125940460070908001d0a6802180702110750307407084844002d1401302c45034241d5200f1b020b490069010392890001c00c002402080c103c2141d91000c3d040e120a00156281d600301528440040c0049841004072880c2065205001c0341c1d010740d51122490450a1584950401d036100800c00d000d543c0d41e4001040d640e0b9000c100060f0100c14110441c0d80c0c0749411411840503100403070085000c2014100007083c200008074400c0e05881203488181a001c0c07800007201d00d080c00c050000c4d80e071000101c030080388503154030701401e105003d08201c01a0040301100b608500d4407580408034219046903040c00382a0b62002d00b065040400359298034504071a40c1805000c035841d0f06070703555000b40300048581404c800824080c0c032034141521000c2e0140000d0600442260300204000c00b0380b420000010014542a0700100c40345 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 719511960 1250 719510710 719510717
    0x1140402150702370603060609030f1b140a0905061c140111090a0e070e061809040c0323060f070903080c0a0c0f030f0609141e0c220507 60
    0x10307000600b01c0781d5040030099400080c038440e94504d000050f20030100b00100f50510b010001c2a2400b80004d21050840c040208000c644101741c3c0c0030300c508200418009921251500e800d03d680c1c11219002d4488200014080c0c00140c500040b03261061259601c2a90050302c10000005409290340c0702546840b1300b2500e80302c06040001307a56800b4441c004203010a030040e07964951045042100c045410780c4208121118841002400d5600604803000d101082e41c0480d1108045841145039200c03009000b9041500c03441004180000d5030420000c170f174041e44410100125080f02c400c4000a02003405946620040100340440101000c040c0d00c0400da10b8107580c0c0689035540c81d084ca40c072410003903501d580400300da103082c0310501c0482c0004203801c43c001e245080c80d540e98507012000c0c040313000d40100d1b82c45520106005e40040d20384865003210342918103419050098a1081140740d041038490302c1644100403ca040816607402c55101d00b40303081410041d14404403000c2c150040404040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 719513210 1250 719511960 719511979
    0x5130f0f03180b0705070e010510030b04020910090905060108010b0f0a181701050c030601020a021909050c04170c01050909090a08030c0a02060604092a1a04050301140402150702 78
    0x300998101207074043c04100b00042d90f600c0a50400074580420340d04600451281030f0f0040180e9a00c03c060311940e513416040c00301c0c8024182001031b00a0041c40d02c4030f070704424404203100201d64803180c1401507400402082080f80c82e1400119200882406107007c20402005242c0e46c001c411005490403049070315051100318144005898030036110351215191206054082d94548800e004d01d03a40082e0240f502d07070540c904200001e5a8643c41c0304064041c200c2901210314800e510103c44014080314032041c003407030a003030a00c0b9045034068424a00c4c004c10b0303c0290340001c40d011441c240e00300340594a883c10030000c4010424003001c00b510700d008074818403203140c0000d101040903511412003d014940c4400c48440d01a082c1080108414822883c141841c00010400400c1d00525800c1510000c0d02d54005d441d03541092086412640c0002145860721800f004110000c00955070240e000303000c1010003642801d444002a80c000354000b540c1e100510350204100701501501d0300042c1510b02 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 719514460 1250 719513210 719513237
    0x70f06060b0304051b011b050c040905030a020f070f031101020c1002010c0f0206010b0d050c0c19020109050d05100507020c09010f1d0c090609130e010603030305130f0f03 75
    0x2210159071080500d284040200700500c0b0080c015108005d01000808286108820000300005100441e07000400c0b11580c14a05004040020304608480500100091227046c2001036403a04000d2103c0014801d04149c0020702e100440d545007140c0070340b045049591300307603620400d640c8032900e2210f046102e00f20941c035050352002800088141e40d03800010300003103099001041040d5a0303040505640c003803401000b0707000c0048201d91003082c68800004407603e90f503005400e03e20810030403403068494002c60040030325100c6441110395100b600c40241d032503540c109000d040c0b00c1000b0042c01581118520440104458100d00c1e400421071066401031302084d0009020401d007a080250101650303401840140b22400444e4810784c1601200070b014540201030320810722601050390f0003001c010910402c00c0e143c54503010742520b9500e5040c08061603032040c0500a005521041c0c00107418280421148007004070101c254507009205004181040e4550a000b039078230382000c908010301034142c0e01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 719515710 1250 719514460 719514473
    0xb061f0903080711060d0f11090607080c070b040806010e0a09020d0318050a09021818010311010c06050906060307150909052a070308070905010e0d02010c050106120c08070f050105070f 81
    0x1002401070600011f503402c08048140889240141311040c4503820841600c05544040944400d05e600c042c00c0f41c1d40381d41c54030350380b801e09519a101e40d21108002c04c0c049551100820f07900d040e10313142c41065686a0380c00c0c80303590966103000e00294100c0e004200d02c10100c1d10408159a5074040c1e0300d0058010799803440815044c80185d40100c42d015408150440c601d03100c0b182200c0d9411044440110f06500907a0500c110281840000c002e8900300c5d583c005203901407800080815000030742040949844078030329072900c0c81141c0444c480c0c060301001107241c99201c02c2d01000301c1c04079596607880300d04100b102c20042c01e01501c8138041159400d0f422002c00f00c103020000122031982c0180b9210245890041c000d400060101401c0c802d102d5001d1040b42d0340010040d038514000ca440b400b80020600040c1e404209002028029508004002c51003500501052508074070450340e01c0c504543e10400192504800c0c060150769451021080005600c03c20180a81074090a510b02c90381400b540e402 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 719516960 1250 719515710 719515717
    0x32301090c03140402010e1c020907090608090628020408030a050901090e240d0609050601210c05060702031203091027060203130606030b061f090308071106 69
    0x165101a2500c048070075181d072600a21070491500f8540003102c1c1080c1c3e00290410307040700030090182010a03d0449074641c0f843c0126061600540f04800310b0402000c02010b03400c40b030007007201240e140070205400300400a00607100d016051800c407040706188058030f9a01442120480079950203000104d6011000d100400303003480c850322031a50310f003840c10014000403039560100d000c2d0f000c004d0402941a0500300b2883d80c0b400003d48028214554200294081e89218405850246408070400400038005202c6060302e9a281c04062084284a00c7c0300030700c0f52030b420040c190f102400d0200518142040036002e8544018140c0300580e0076107a01141a8204a03540c4400364000d00c0521714441c171600c03074503080402d14503a8500b40c0034071140d801000d9000d80c0c0014005980080020b248904841c0c0701114542d03c24402c0c40000c0e540d0030501800003065900901c603203c09466501114464255641001c1068441402d21131035912040e0340c2d86c100303050642d0150340c8035040700402e941e440000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 719518210 1250 719516960 719516969
    0x41e1401170c1e0316140307021b060f1201060905030d0203090d0f08131404090b04031d03032a06130305030604090803010e0915090a200603010621050c0a032301 71
    0x185c0c0400c0103050006004507549401c0d040500c904000f4408581d41c08a04600d40051400c0010741d05618080465058405c60140740803000d00411030503600400064120f04a0309160b554483c019100c808060720364035450101c1c00980e01c00c21055500e400e00c0440d9094a030b020f400082c1c44107510752500303085640800107006c0d0080b0707803403418462294008070000c660f94040c0c40422524009580d80d0541000280c03001c0e080c400041a8518120300f04022440101400350540352a0040320984803044892080540030300c0d900f981d40c0d079195403400a90540315032040c80481d480c01d401d5440581d442d90000d01144d4100791581c4482e4041910b0320010342c02030000048084a52505580071814103100c403a4003602d0440030020300500480c001003070608207811907014504d8121080c0d071030300f0803072011b0703c029003010011000180b0307141c21907050030000e40b289140200f2030039429413000c12540c0c11280c800039081c041c0113003035800d4801c1d8425207036024504082f81410400408091505009034403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 719519460 1250 719518210 719518231
    0x1c0e0312100e09060f181c0905031002030907031203022a06360712050a0b0a02040302031009030e041a040c050f090d08041e1401170c1e03 61
    0xb040107203028244594810b241c4406025242440e443c11440c84801030000c0075040034075a42c640c240d94050011003864520010912244c4c0191400684044003d2041c04d10038056480100510300d2a030080360b100d451400c0103400c03034a0640e9114012001500c400108142d400c2c07104041c5900400300e505a0310086c226440360701c5502e00d0300d45240ca00c0c020700f041d0451800c000d4480054040c00f520a40c00c002c50100c0400b00d1184180051a125281d407000e1500d680041380401400300c04941d03044102d004a0205d1810b6440c0e4201c10260303c00d44c4402034055000c0340b1140d550b206194000c0748070501c203207052200700b01c03011700203401e072500d2529180e45041c007001c40307900910346803013006004682828098145101200c04580c039015898003c0e008030740250004007040b02c43e504480240c203d0010030f52031820807500c641410344840c06441c000c042c0004101c946903000301200b0580c0c0740c80c0400b4405664a241e102c1442d5000325996404800820380380c1c01241001c10040d6220b40c049a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 719520710 1250 719519460 719519491
    0x90405071b08070c080c01020a03081b180f0a080c0904030e030102190224041e08040b030103020f090408160c0f14040f050415050c0d0903231c0e0312 66
    0x240b4100440b13a560016020744c1c0000e5402c0c40c541d80202c1d100c0070194050410a4090f640cac041600700460128403a10741000f00000c04645511503521404072070603003070320b01c000454000400d000c01c2580c1c500800c607540d800385102a03581d1820005955001c0e21900c2c04201010034000071900b0381e00100d840750424079501402d480070300c1d0304014002040d41c14064820341c003d4214079a02ea41c01c00504064010800c1c0e0500b19a06641300b0314500210703070b004807151f5582c1c0d640c3e0218002c03074000f07010403441410b0404c0c071100c2c0c901d00000b8150207160804482490800389040007002c40f101d1400880e038040d04041c0014481001c1d2220100928860000150581400e8104001c81e241c10140d44101451700b01800301107004006820421892140c00080c0ca0301d60b142060110701075030f0518508141810b000404140d400709280040c0d04428010b01030100d00070a0b16243d41c0102c00c4d140100c0718041510f5800041c154100d1f0001c807450b030090f2450000940c41c03503401c0c0c3c20308885969603840c802 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 719521960 1250 719520710 719520713
    0xa030b0406200a0c0501020f131505071203150905010603020a0905030d0507030c030e040504030e0907021b0607030509040c0504030b0a060810270c170f03090405071b0807 75
    0x28042d144030042d422000e0b04000807240b003100058000c5041180411074100841c01c10014254100c4080c140480704442c0c407400d5400b40c0c150310054a005492100c602a24030b4840c50303000e8004d0344e00090307100061288001031424101d000b010041486101c0707014507a000943c03508207100d2903020704801d58000d6030710701180e0000742412105c1d902040c0248c1c48000a01c1682d035012056403600ca5052800702031403440e03401c0c200c0b02003150290b0746a01518160502080540209040300009030940f03880120350740740c41041e81c507058200a0550380104403960615146008402060007030310a040c528140398609003c80c007140c1c0c401765404045000000d0500078000a450b0f09a800021008103001042c280940c150301d620980400301e54160303c0c0c04035100761542ca6480c1c80c507142d07101c0990450580c043c0c1013000c002d251512031f489400203192108104a0f0b4081200300500c800c44009502d051581c82c20b210003000000d11001c03c01015802c42c0c1d4511040e0003414101a000e10421611100103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 719523210 1250 719521960 719521973
    0x903070b0705060103030e060f0408070302100c02090105100203040e100f150906120603060c030c0909060e0c0a020f0d02011b0f0e04110c010207051b0108060306010e070c020a030b04 80
    0x11a080045460401d01255001440014515040d00e60500e031415421200c04007040850051220b580c080c8240864086007020000030180c0c200c0340205e03099003003a5400c001c01e641d44a10f1440c040e422805100050060f4140f08901c00101c0f6507500c122454282d444a00000c800015070703080e03100c00c040c644100320b088003507088140900075840340b018200f624140060072842041c844c60040c0608011911341c50180c682c000d40082d134000100703200501d110100280280f80400f100070211345a840c6c04200508588a1700e010758200c1c2010b40050f4481c0e09607101c0c81e801c41001041103101e0170748842c480d100203000c0c5114034403043c0c002240203c84003446940d4030845202c1c9504001008544d0603800d688181102070504007a01c0014210000c00601c0c211803041e01d2490b030196000045610030880c0010b92030b94110740000e100100020180700440720143c040e1240e44d8141d20510040c00011400704407035400c0703031207810201002001540495040d1001ea44180d07000b8550004000a1060 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 719524460 1250 719523210 719523223
    0x16210305040510110409231303170903041e090e0d02010c051e09010c0623131101050313020d0c08010b01020706021c090302040509062205072c010b0903 67
    0x60360303c0a005100c110041280031307010740d204030300042d80c4400c1407550620704402d245a583c40d08203400206480c00358590415000e8282088000130005401c000c004800c410100f802502d031000910303c1c0c540b804d07081c3c2807401505900b070f01072000d040c0d400283e03c8041d0301c2080d0030700030210048e00f90007011307031006400c4501901540c4107010040080a500ca4140115105070143d408085900d528049004035000d0f0082000142500d02d8001000918a42c80721009601c4d140c4180d01213041d40c031004580a64035051000806d00240b510310003603158021006154444603d00c80d0b8010300c2c1d129000034008841c40c1c641074a4950000505000b500030038041c02c01607400a0004088591424000030741c0e60200c1500c1d80482c0f251404510140f5108451007002145c00510a0085050030f12226469501c1642c0c40c030490110840812052004501803030081070300a03004e840d645141824a0b28092000710712090074110080b01184001140d900c1140601311440c030203074071400d191b828103103042c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 719525710 1250 719524460 719524483
    0x818062e060e1806090606070819020601181407110a060614090a0c020705060a030e03031e07020727110c0601060e0d08030c090607050a080c070614162103050405 71
    0x1603001080b80c140c40c5c200c0100d420000c140c900b40c0c0d07500c2c081d080c40b04c094000d5441d09821a072155070113100031035000a002c2e050b2030dc54884213130100e0302c0102c010100d912001131041040c01c0b040004603101d0141c1c2d00809a4500c8400740c13022001540c0e070b0582210301c03942083e48410980b080130740145c00c014450700d5000c640d00200704020344402d11301a5444100d449940d1103114001805403d0b51700c01e8200307035031000d0000c0407a074403030030000c0400c1c0d403100e900c042c5c2c03480740d4104d0030009152510006400b000c48005912191040380f9100c6100314410f202040340c40419203c41c2058581410300d00108083c49026014040b103504042000b804680500601032045110b007100c0c2c4041550341084981081c0c032000c4e9140d4503030740c0e030f00410070901641e4000f4000703024034034118052000d51402055019143c10a5554041c0c6942c415100c10000281058400d48140a500030201004108503a0340b030252890301210301c01102d20303001d03100c1c0220303003900003c4e106d5043c801041030802c202c0a541 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 719526960 1250 719525710 719525749
    0x6050f0f0103050c0409050120270901090c1b200103110d15030b04031d10050a03091a1501120e0a0f1104020307030c0818062e060e 58
    0x2540b454503002ea460002811035840745640d88000400c0000951043c42d40c41152aa03d032526140000d528a40713801c24081480e6a81140c0490003a0303640e650411510400000d021146917420100440001c003c40c102c0d0901384a407104119440c10301250321a00d00304e101e01002030141c9030184440c1010405003140386d040c18100825000c039111010152610780740007030000240c0b0380c00070700915820b40007517001900d66685003041c80141a40944850003100c2c002d10351034108801e0307400340090f0481c50f0303080100041043c0072005010307200303070090484180212042034055140418540c00700030700b030b240d003007654050030307405038455810071100441d4a6406208100078000481385daa1a0040b0f100e004002441d590b02d40000c0041045050040c804054011510307480c0c5000040c00038429a400392000c44e81507000103240d0758412418012080014016240319100c10300c4021614603220000f031700703c0880d40302c0142e89040443c10300700281280e9a40d0803640103403000f8840540340c4060200310f034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 719528210 1250 719526960 719526991
    0x30e0405070207060509031203040b070801080f070b071110031509060f0e09030d050a02030106030501050d021302090f03120304110a0b07030f03180c03020f060c0c09040c030b0406050f 81
    0x690340100e20f2804944140c1440c0742e4a8210b0300010303040c01e0380b0100030450004044140000e1105821400d4401c803039988801400c2e0344c071001035980d920001940b04106a102c0c030424420840310b1030203010824419690038400e00c03420300c0080c42100c815080c280029940780c12000c5508000e4580f88024280c82c0c0c0100139050034101e1031f402d0440da84c012031989440840208101c28010070480c0c811494025080103141040c10003032010b94002c0c4503c10000b07003003078004140e51030106110a003c035401800503114000f6040107002a410858059a00c810f00c0000d250710350320203001c01d62520302c900450070340d0707881c0034500b000f03821203001004c9000340441002803103080384880450381850740604140d8507103141c1d41c42c03c03030107811031041d00a0428001c0300503008000c080100c41c0152403003129803030950f4984030244080c50041103401c1850b54040001e0340400d0070600a4260081c2c01003008441d030075200c1d01c1e0000c1c41760058400719503184d0f4900c1004010404802500d401c8606283d25001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 719529460 1250 719528210 719528221
    0x6090803030c090a2d0614090108070e03070314070807030f06180606080109060c030e0316080417030409050c071a07030603151a040b0901062019030e0405 68
    0x1a6030000601224460b4400a28515582d9900d000c01c801003003c5640c01c181c0380200c91000c3d210585d4085003004e10052901e000ca00c940c051803085409008000d11a41424111401121000406001c3c0802d011240441b241d16440900404010b103014840b031240c202d00035005c00345007d010364414501c40e00311150900c001030b10448041c80554111501040140c000700e01c00390503c600c0d00d0000c3c01d9520705400040d4070039040d002134000301e004140421040104080075016100300024014594104108070010f02c10b0070030003003244a00410501d411300f500c90414404840d80182080346560001c45c08000b4140503020301030b80860745800c02410b14009645003401e0010101d2880301194150700081c41a40c4254410b00055400c03400e026040145000e92000506420700c0300e100c4a1034088a6091a04050090550000000c0c00014840e860108112095008189810401c102c2102090b0070b03420200711150004200005541e0207400f40d00c0c2c06880c8401c801c03100c4d030245050404000c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 719530710 1250 719529460 719529463
    0xf0204120c0510080f070908010612051506010e0d060f0e0c120d05040303120f0c1107060801121e0807030216170c01030c1701090507090f140f040e010e0c0901060908 73
    0x5803c400141c1d1740c1e8506441d4a0360581d0000c00030342101c1001c1d03282940c00688200f4140c1c0408015000707609961900d202e2001110000f581140d0050210ba402003000745242030100d113121015015040c0000c803050240f45030000d41c0d200c40e1400c801680060740041b220305e0004d070031601002c6014002d00607066070704805056800703144000b4050201d110310b0401c2e08141500b220604105628041010341d540c1e11001d0100b0014a90420180c42410808254980a510f03120705940c0c400b030780c900c20200700d9507a90f094810300aa00a003103010030f011140000d52550003601c20030b4441d0f005042c424094034406400034803180d1101803c40c0144590510070007010941c039440c041c013860089600590303a441581d19441b581110b882c1000700c40c00024015075961710103070048112b550b411003155500c012039180200300d4016402840030811510241c1d19100780c40707107402d0401400109440c112000a01c2c00c580c110b00b1f178040350b600701c00707003505213403401103011800351549051003020700e81000c0d00c26 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 719531960 1250 719530710 719530727
    0xf09120a11041802060c0f07090e190203070b1305011407032309031f11040b0f1e030406020309060f2404150620070b16060f0204120c0510 61
    0x10b0049907120445456041031000f004083c1d5005003d440e554075207490041e55900c1c104400724102c1c00380e04d4001c5140c103244d0080061510151004091200815103c0004104107290480e41031081210021b043c091400c0604460421b080030315403e0392800340090883c1134000c0d24000242d00801614000907003090070038200d0074001e060780395400c1d0104500c000f1441484a02627140c80b98401030140f244501c04a40c0040120000a01403000d400340090010300460240b011000c00510588104c80101c0d001741c1a050f1040d0280b25940070006149011a0320680c1c064560f55000400c0140c170034820828550810454201c20807203203080845032003621181c541241d0720109140c840d030303400c0e0713103a40100c0440058902c2401406569103005801d42c000011503800c5900ea28048031000300d80414a0f104031082c01c0d100c00d1605000c01035003880c813854084120303503090703442815001d01106071015002800c40704007944251006410f0010345020258495881804a4200594280d500c0f00c0c65 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 719533210 1250 719531960 719531993
    0x1b0304031703060f0319050f031e030c0d3305060a031e05010e1609060e01030c05070b0a020d0b030601080c102003040303080a0c21020f0f09120a 64
    0x159510b0340c07a100d0004441c15003040141c0d9152003000d0404282e5602e480c01b102c40c061288040f1f4040c0c08e407a9081d1034807400b48201003208400c1464400c008100c5000013507070301c041c040d40b05602e0000c00000c07450440e1901020b003480302c60316864450300e83d2010f0a405000d0400060144400b81c500400503645101d0f024600040644800181c00e0011501800b44001da0030654140b00c01e6858046210401904403409081c0090b51014240e449000d5160201610700a80e0f07090100040c00b401900603010310036034001007060400854000c1a0780da040d8500561603854050b0340d40d10540e200030180c2d200070150714801e4018100401c00d401c0c001400f141400c5042c2d41d500c234004d0084030151200c0700c0c0e0035503464040000d031507141246600800100700340e078880d4540c1c0e83c1586070000300e030341200d587c6203908001c25a40803010035403002c2e00b08034043c41c0140100142c60540c0c0c204001d9103e0f0007048071340c1800303080883d800c1228030b400000c06440c21265070080100d80b0041c1c460504554100d1380 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 719534460 1250 719533210 719533253
    0xe03070c090e100e060601090b0f0a081e04050d020c04060815040f08070819050c060601111c0305150d150506040209060c0a061b0c022806051b030403 66
    0x2146161490500c00683d0300d50410700e042140800080040d516600c0c225803581c0012140400418000ba0b0b10094965030381c008a030b240d051803c0000b081e5202c090140c0743c81140100001c0c030b0114494400c000c0392140748a200504003604d11020702900d040d410342d00d95880395003000018030190700009401284580e4280e0003101c031b902e581c1014011a2a030303241c05089503500241010038072280c000241f1801070100700011040c068598200c64038084e4040c00c07032254001070003142196205600010088503900e003600c411040b40310b04035a16030002c01012020039203c400304450b040744c030300001c08060025a19065400b00903622010103603101d820003240c2c00d60303a07008244035456581c19034121410103015281d03103080031401c280e980e01681c00300700e034402e04025400013914611054111240300c1c580720b11528000f16420490300880c40c1c2c500501c0d840340c0d285400e8450b06010460001001c181d101d60760750b511081c402640c1c02c5004003000c6075541c42040f00700000303000d8000510381c80f07541e5003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 719535710 1250 719534460 719534471
    0x2150a060503032206030203040804031211010606030606020c0a060824030d030f20031b280206010603020f0702012a0b090106120b0a0902010c170307030e03070c09 72
    0x148200200465004603406200202d10194001d4000c003661000b00c0451150500460b41e40c4000c40c00e9100c107c0d0014201401400b0410000e1100c03110b01c03902d000340f820070407240404001600c4c00c4dd1910b6000d02e0000f5180e01c0200303d11a01030080d414018015210b0b841d0b003a0500c20080e12004001d440704c8004041808404420303000b001d1a0483c03010002c098030854110f40340020060800d60310f840200350304d400180070f0101d00720700c9501c07407011541c0400340c20344d541c42e1030306022214038080c1203040c00c80c20050f803d07002c4180031003400301c1058514123090303002450348000d10300801600003d050502c1000700d0041c0d0042a4107481019909280c10039001d601c03118800d020500f0302e10301203d081c0c000c600c0032040200046007a4483c09004008002d882d5a901c0f440303428030800300b00580040e038117a0228506056941080e201c8600606141c0440121a6101011b4428404007030710100d001100340702c075a0f54507005165941c03103410300941c02d0070901e48034041145500c0c802c1e4000c060382d84 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 719536960 1250 719535710 719535721
    0x1050309150912070606090e010e07030213090503040803031e010321091d060102161409090f0a0b070f0e1f0311040b0918190c030b060c010c030510060215 68
    0x1000002c080c10b0783c88580c292101200d01d40000500a01d010f01c40403203003072000f0441d200e041441000b601d901000014042545986c00b0702c840e041059809180c100d0300c0340410f00c0440d10800040004100f03090055a40380380520801180c241c0001003108e0385900040100040b40d40886003407540400d60351225401c40c070b5002c01b034821520707a0340300c5400c0a10309215490008000c00c480382c842c007000c0c0c00b42c2e030900c0145c14181e1100d9185015840c819900d0200043d624100b1010f610380c0400020100c8010048802c0880d140c003030755803c102c920044803010001d8140d0704c4802482c12007140d041a00900302c0c8000010840c0040042c40b4041c04980d00101100c14440d80003007281040b0400415950b030307203441603102c1d16440006400c1c02190100341c6004110520003065100340300304104803500d07207085c0c4210b4000d04402e11a00c0300b00b548030000341045035030b0704008180b00c4d440d200000460015840d0b0140a907200209644000101580100501d540114008010441c0c00c0040d800355a101c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 719538210 1250 719536960 719536963
    0x90f0108131e060c020d0905040203070f0c050c060f0d0e060f04020402070516060203040518090c0d06140708010e06010306030b0601050c0a0b070c0c08120703081504050c1305010503091509 83
    0x2c1240c0a41201e0401c0000d4400a8000c80e011141a660382e8803070400a443c1c0c42400107a11040e180c2e080041c40743da0b4241c02c2c6030310400407510341c60712400540d00440e0056001030400d400c014207008000c0000034980381c1212aa00c1015038000e8050050176440c41c10040310100900000c0000e1700940d000540300013008824000c0f5030078031340d540e000e10189580702c81d0025030340d821600a00b4080c1808402000000004001d1903205501c25001004410300c003200b03010404a08407021141551103441002c007421000010f00d03c0352000342c5d120042da43c94821a800b80c0507001d44014181841c14009002043c044041c1e85c0d8000340030708080d0380c0c48205c050b450b0310380080348401074044100b80c420310008a81c030040842081d400baa540c40200368841c0d80054445010081410070030000b00401c5000a00415200e40c0c00040707400d002030f074000c1500c0840e01b50f6900710f804000c103030800980080d0201801d4a0301000c0c080a19002e41503180048401d5911001c0d40344d54142e4070b9880000800c032900 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 719539460 1250 719538210 719538263
    0xc071506060207090e01090f0f050f0303160f08061509061b0a0201020601151e03110d1d0c0609040b040615032703050a1d0d030203090f010813 63
    0x90500108215940c80c0d2000391156144c0c02038807503050038041c0c40301150a050149030b080981000e030804210b02150744400c0200f641c06003c45050260b03400082250070180040d40c41107401059400100081c00002021140003850036428483c14100344840707030311202d1c201144009480b480317554450850000612500542040c0e43d00005000015204e801c408660f94011510030f808642003030342c032010424501c1307451841c004005036081d00e040c104ee0f116018001800c081702e080004095140441d506440d0740b00b104103412207a101d8100e44a2000a6080f00411981c00c402038194207011000007015842034140c5107200700d4440c00300d0a240c1d0380e254026801440d0b10100c525203003220003409030190441a03110710552105090741140d4103043c3d018800354030b81c140d4840745420300a00098840032040c809190f5020f014654010751900c1341c104e1013880500a4004540380c00990003005080c40042050604114035901480390828490740400d400359440880c0d82401e900d0f00404404a90 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 719540710 1250 719539460 719539493
    0xf0810090609140c0702060708090607171b070b090f0a0e07080907050109030201080609100b0301080f0f2b05071a01090c0c02090a110d02220603140c07 67
    0x3881e06100264440d4580c0c0100a43c0c841241d10f03000316136a5a442c40203d0007a0140690010340412a00000800b1700004105c403000090081d81072518545a0f031140b008505c0c01d0040c0da040c0080c011001d01c0c00b2400d1807503c1d02e1110010002d4905101c6003202601400c41c2086c010200380105c0c590942c0d6803103d035405041d05902c00e900a1604203c001d051040c19540c015542c050b00401082035482034420300e0580b5011b03100c510560301d031807017803144640004102201d880142100800c2d040b04500c001c600130b0807100010241140b60807001030601244031940340c0d15a0000004140104d040c4400c4411142d120007100195200020140c407140b10b4100700511100c20100e001c030000404240355030584102c1201004181011201510b4501c030910001e5440005400064484c80454002c940c1c04e80581d50480e0a000b4a14104001e80c1c20112444040c41c00d4808004080008564508028006450b0500a48842204001901ca8050024001d0750000a108801c0c0046001300c0c0c52000d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 719541960 1250 719540710 719540729
    0xd03022e020c06070f020a02100804050c030601060809240703051902040b0a030f051b2a012a0918091e020910030203030d02030615270406060f0810 65
    0x11034000700b809885580460780d59003c541d540c50030103005072000510a605030345c09001003c400c182d00400341c0c1e2860b03002b44202c0300382c890007000d0a21500d06000690082000b031b156206c030f82c02c02c100b2080c01e09540d251f02400c80614500b11070b190783d0603107402070380081446c1000581e81e1205943c1c0303078640c2d0149050791042400003070000f44440400d4024460200140c1d02000007608458000c1c1c190781c415034091680110003031600901002040041c50f6101c00c00c4d02020160500700000f4000040c0304650f06031a035547d000d25488480b8541100c408442c114890304030075030010401030000f0885010780744003d11008e004030585c1070130b6840301101c103420841c0070b04c043e1108942c41c1c0c03203a00b002c0c00407401030120801241d8661700141003141600c0e40100518204101007002c800290001080b0940c400a42903001351000a450001d14141807421882a041d04203049104803210b001040e040c025850300408100056015440e40e504022610745601c9540b12101c2c91300b550003036500075080c007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 719543210 1250 719541960 719541967
    0x9030a08240d080406030c0305060d060b01030e010f06080f03030103021e0103200c07050604051e060409050903070614071e020c13140604020a02061b07060903110c0d03022e02 77
    0x600c85140013a00031105545c1c2c00340441001501c2c110306503030055410680003500c0b00c103c8800240103403ca04102103061500042c244400c51604d402d450400424501e069035600e4144015442481040b03103805681c0700546c03440d45190f001c41e40c81000c030080d00300d22442d465003801c0160f210f41c0001250342403c01c5182542c0040c00041001c69020b441100d40c0c900c1036140004283c1001c40603641180c02c0101750000c580740900d0344034183e4643c0000d55a00c10801c103c0440c01c6407031481042d00484400d0011915a181c030714190f41281c2c00340744003a0344141c800701085480c1e035200a14110101020500714050003101c0416450405408440c5a005042d094081c0303c11103070b540a0603c0b680e4240c0b030709919881d0360091004a11400b0074040050b0013050000d03100c1c0301a03519412038010300d82c1c082407a200c0107840e442c003201c000368001c40c001500d6a038481810a003c0003041c42c0301100301d070b000c01c0050389681c020356101e8100b00c0540703c0340040140c403101c00c2c0c50b1041c11400e601c40c03074900799513 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 719544460 1250 719543210 719543213
    0x303011806080a081903060b1c110c01020408060a090c12030309050109211403010b09150f0d060b0c0a38071412070305100305010c0c0b09030a08240d 66
    0x1145d400103913050f0420380042130022081e42c032a0148100311041072541a20b80084242c84203500a29405c1c2c84020944907d4100094011080180341c590720800c001030f01c8a04000049040483c041d150743c94150401c03a041c40800c03805c01e17240f011580c000d209411801860f14050340600b5904d0006040f035407070005010107000c0d011203659070806501051305020b502440d81030316444502104800f4100e024001070201100101c02400304000080c004102e01c010390bd040c800e05d500003558a1039001001c0354101c3d4003080c0740100300c0541440c1c1c8010303081c510510007955441c80c10320005051081c0c6450400e00c000e2122890045005d0000c20200d6043c14014000c0d0f42603c0c2130340c20710700181611380c0204a8017095030030303909603803840345d1a5180ca0700d940001700d02401c40900f04900f181c460080010029109114050034181942c5604454412508001d0401c602c0100707900c020ba00304004d64140542d20004107035228407040c0c0c0304030305840b10030b0100d0003100366a078046d40c1020324002c4910 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 719545710 1250 719544460 719544473
    0x501050d0b030d0806120f031b01060f0603020706050601090602100b06090d0605040b060d080301120314071112070b090105160606030c0918020d14281407080303011806080a 76
    0x41c441c1c80305480310b503204500c10301442d684041f441500e030000d400520a2808401c0f84d1250215890100000071540540343e01c6801c2d210021130340400c02081d400210311741002468020154801000d0815061040c5000c00203500c440a12464059250b03032842500090365841d4183e07552040013031309030700c0c0c07010040c0b07020001042d0a032005d5400d05c20100001e2841e141460481051a13405483e1a0841e441e05004040a03492030604405004d0618200300c04440c02401a2180702d00540361000480c0d504014000f860000702e121048503001a4010b100d0502d0040031030707030445020b19041d81c0c1c511001520312810180d2690042c0400e040c11000402d0060181c8101d050380e002e5441044424480096a094020043c0e40290400c081e04011404160003001076150b2000c1c0c02c0a450b000195005107622042e5070b0b200182c9100003800c00501400780700b500d042200c0c0c00000c028181c0f507080c60302456070303030005100f02d50134290b8148102c54070244a0300480010306406003225410800d500d42607 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 719546960 1250 719545710 719545727
    0x31106011806122303090306040c14010c050d120626070f030c1401020109060e160f030506011a13030c0603051e0103170702120a140d020303010501050d0b030d 70
    0x1100d9051200100355422400c2d101c50490b5809040076610500340a1915036130600c1c5180c03030301207001c03d010324401d6413000d101051003140300e07030b05401c040c81c00d0807032844a40c0518181113040103011822600000c40001d03103d80c55480900300b40c2c3c0301c80c1e0709001440c0545020f0b080550100403004480c603134402000d05201100450340140c45680c0c0d144c3c5c0c01280f0b0089584070141580c2e850740010132010740c0c0080f05148900041c8000f26868200e901c40b001070700c80b1401c825205074440c0c04c600c16200b18081d8000c001c2c0c1004004555940d1868583c25034031001801003001100c504041710428004940c100d6a64400c5040040b02450b036a003040083d854a920414012900704000109108140091041d007011a240c1070000c40e429911001d00e800d0b01c140001c02d003110100035400c0075a60359180305124102c0c1c10300600108280c1c0c0f0305407949c03070110761500701c0c141c0c401c06090b40f9944d004400d8a040d40c2003840c01070b071200001c6190310090328041112035098004c910307450381c525912440c1c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 719548210 1250 719546960 719546999
    0x6181306060f140d0225120f1704061104180609050c0a020a0f020a0b0409021b0d0804030e130c02031b0c0310091109070f0905010c02091303110601 65
    0x19010101d80b00d01055a044526608400b01d6030410081c01e000c0220030343c05480c100d46070340140c44900317240400a031144103000c14151803d4005d505a50b0340740b80e002540c00b9100000d803900350110310000c15445582c8001a000a100f29103445010a200f0001c1c01a40c00414034405100003c070703030841c8142c0051540c0c0c040c600c0b105061000150400b0074000490b1000c0b0110303030091003228526102d01d101d2a01d082001c0340d01200b02040000e4502d1800068009004040d00050341c0d020480e1645100d02c1443e2000342842e080342001d0040150025001c907803054050808210100d5084000b5100c2001e030982e0a451034a80700150011716070002c0607041c01c1d111001d41e000140969400c0507070300c10b41020541e1741584640d02000c2050060f4100d00350562240400040301030302c80e40042e0b000c2c503084031020000741c0c228007105519980714030003000411081c00c00b2442101c0c2c0740c0209221040040001141400c0200c40d1010148156052031081d41250261490341d61070300d00b0103039401c603e200d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 719549460 1250 719548210 719548217
    0x4020c0607080711060c1902120a0906030b04060b0703050f13030f141f0c0201020c010603030e011409010806061819080f0f060117160e010302100215060618130606 72
    0x4201390880c4000038880d0183c03041c803005a0614948010b505c0c950051b06103030008600500d101c0c001c000f0401406050070050303584030300d0320301401d02030000c08680201100620490805074100400c0306d20404845044d909490001e540703070504041c0b64030034401e0708500f00419100450001c2800850428404002e10500300a18a100560100c90380c50000440304850080fa0f440182050341103684944070510385130001500308110a0096421215182e0094020552100c0e80505540e840016424901d14040c5070906103051031000070911f0f10010034541c0190310015805140042100090840e0130005003003034210b6030710f941c0141e4910040c0c0314240c000c1c410341d41c503015441404600c050704410b01034020b003072036860070040e049020701d001000c0b100c0f400b0741004640080ca510352003801810046d4800d134800d51451060101c620f802e441c00c3e40c119000564000c49541181030160340040080b1100e540b29080f002003080100d12688005070b00032004594114299450b402c0791017255081d48 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 719550710 1250 719549460 719549477
    0x10504021e010206010618240801050a0308070813031401061a070b06060706020403050f0f0c0d0503070f060e010e1f0608070308220b0d0f1e0b04020c06070807 70
    0x1d80a010401c5a070004502503040040140070aa00c15a01035440c032550101080241d5a0b503900c0d160010142d003d00d00c480004444005030150f00601d0030ba004041c1502e400c640d1510715141c0705002d004451004006940014007080380c009080071860203035800c007484844018141802da8020500380c0320311507800c002036040b00c4072950101d00f500c9500740c01030b1200c482641c0c0c000800040b071307000140c110343c0311b54280804000715100f04520020001803400404200c0340a0300d82034500707802514414403a0b02c00c1300c02c65000410100c1504c09059020040035845902032510501412220081808075071130300e0041d00d00040002403594000380d81070f4140400409034424a416103500d801851640d60226104100103250381c0010440154420510070303500e030f080f20703440c04a10000c0d48600c5a090011404840d0182503200795414204169003c102624100043c11880656180d107154669170352000072109032a180c040300d800324003c3c000c3e1480c5141a8101034112034041d10818009410300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 719551960 1250 719550710 719550739
    0x4150507050c0f0f1c0f050f120a0e100311180f0d0206030c030405190b250914060c0109290906040f03030e0a1511031009050c120901050402 62
    0x1034401e030301443c4015100030401d080910901880905e02e0301c43c2117421212039203150110b2140e01e1042c604511070030240c4080c4c546031000f1071034807068410020419104110030080c1d680c01403454040d22505441c103801d40c40c51600160002c11040b00040c2500340f000841040884006039039540e802c604685c454140303007984003800419900d0359002034108004001183c80645920040c42c0e00c144100304588400348014903141c40f96418200849a424100742440f10605903000c41303a0340f204a0851034844d42c12030601c0204039602038803440141c0b000700b62000e18961250302c00c5881400c4208000c1c080100d079451300881801c4954003200045503010a40c0c0310b80d0151101d0b6074040c0401e60000c0615442341d464643d0b0142e0844000c505041e030718034003044030758420300c4403400480c003c50784406a00100940301d4140c0d01a810341d624980300c10020410b07000c81003014032080d1040750000144a95070204205010300c140089402c8070b0b001d040030030107042c02c15084a80315601c256201c01148070304 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 719553210 1250 719551960 719551969
    0x3080415021207030c0f0c06030504201011010603050714040b0303040305100f020c150a06080a0c0b030702190c060e0a0e151c0305040801150b03040305030c04150507050c 75
    0x46440c07030740c142e00040100784040703845060a00304150180704065034841d056030361002d07400343d81e50005004c00d840328204000d1000c3e40140880b2602903161440407100359078009600004402c40140a1205084600300b80c018250300c42d101842e402002c541d03029450b003104140b6000c1d00d20310703688540c2c28140500014103010040e02c0440364040d004001081d070950110303010349070010f500000998280310240500d0802c1180d581030044d001c01c04000ca003040c15207881505c4990f00444801d900407186200040c0840d1a4030382204d031900030180e200e03110208100e040c20b041c1c050b07901d441203a44c01001709001701224000c1c22248161240d141280700281030001034849846014501c48030080042e80c018045000c004011074010021201000e02080382d000050001000b0f8000400110b02405810000d124880d8005905420340c42070901e00041000a8400103100900b04940807001c10095176000c4140c40103440ca900d013030700c0740c0c400c1c40f080145160890441922940f040c00b0010780e05045c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 719554460 1250 719553210 719553223
    0x806061002010c210b0d0602090a08010606020c090a0b03011d06090c01050304020f12190606080307050319030e06011205010c0c02062d0310080f120702040507020a0c0308041502 78
    0x24191200c1c0d28104c64913001d41c0700b6400007a0713a0010607844005250b816a0360f03100100d21148228401a10388030f810041c0403616503140c020704190b82c540202803180b90b40011300c0310003182040b540c0f00f109548401400010700071a00d482034056003000c118104866420325003407142c103c2a000c0b52048c0d69900049940e407a0941050f40c0803074005c20114016040c5403614182e12100503000307800c0c210404002c20310700f8803c0d208141e441c000d00485c45040007214020f08008050000056041c0b2081d511103036204e10454030f40324010724500106405940c040e8009400c40c1030000c09441081da0742e540c82c48000e14074000304886d95407070704100c100c1450091420820b416005003d10f4103010043e9620300241c4844d505140041c03110405261a000c03291009500c00d004103078198030071500d0300302c40500d0079003003035916107054015005481c90385100005850b207858040301c001c6030710340b900003040c0d042c07400f039203070190491164420100c20b000c0c403840100704845440a01d28824001c030300080740c0380c50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 719555710 1250 719554460 719554481
    0x609140708121206120f1606110303010e0a020309120409140a0e10020d0f15030b13110409020f061b300d0b0d050d030c050f12041b080606100201 64
    0x3e954402180c9581008010245c81e25080c0f8200c91034030005480c003519041409004802e5010990403c1c484240d10070300c10018080c40400443c03c550403d04e251070901c100030f168080c401d40c0800000c2000000b00b1090100010b45403600d56619101c0070301c0f1001e0a40b5100b8240840d440c007002c50b080c03080500c60030303003c15000c0300500480d102100310140a54098020300940307548405919070b00d814075100ba40743c1500f29102400700c0f2440c6240c005035181c8000c161070102c24040402401003030030303441c035165100001c9400044215107072000454951200385180d40010020424440340342e01400d030314084042c0c0070120380d08014905000c0702c09507070042c2481d00c0040c240c0c0c0149400d0784040d01400556204c4c84000c0380c031020302d402003003203c5405107040e145544950350700c18589401d4495a0400c2440d85080b5252080b9850403001601c0790b01c800311040020000005d0900c0822103a00070f511380100c4a501c0305503910145141c0d102015207003540710703410090200e644c00f4014400e80c4040c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 719556960 1250 719555710 719555737
    0x7120806040510080307060b03030910020c091503071401050f0a03150b03070c03050c0708030304210201060b0405010c26131e4a150f0409060914070812 67
    0x20602d47d10240176118003140e0f00e4061100344103036001551000015403071100d8680c0248000403e0408201c1c034a00d0140401076444104150203420f81c50228815069944283c0080f40900f11000101c0700c82c070540360b041440c51008144600302c0f0350f050704800b00c3d281c80504100d10103a11840140814841030301e0006c00318080382131510009010300042d14030100100d09544045a9620200e401c2d41d104440403106841d8000343d10703103140b1880b0b48203180e407c080e1000304000c4ac00d10901c42e100d4881c500800e418480c0020707005040001c613084000012401c10a0b19060000340d01007032001e60880741d01510b503209040000f0402e0070f00c10f6030184410048001c040310321032404154003003281031403071854844005010807284d10040d08a041d4084070f1400c0b4003d0408421a5034140144405420354008030f85801d110000c982c0c400d00c0e0010402021100010443c4031841d1010060110b090001e003d8882c2c04214a5411404a043c0080b0f402d103e00307070b0300c1a00d140949043c10b44034601507440203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 719558210 1250 719556960 719556967
    0x4050a12050c2103010513110a0507021009030209040f06151e050414010b0705070e0403023f2b0b09060909210d020c0d02100c0206130602071208060405100803 70
    0x6901e041c002c087da8481404200045444507a10103c9099218402c80d074085a40060144214181607103140c1402450f807400348030140c19a40014042c80e001380c405808110940003000a018031a801821920a050b07a1044203070740d68032882005014000c02401281e0100c00001010300781402402c01c034001910a01c46283c1c2810b0000c58190031903036080e20944602200425400c1000c3d0865000798020703001048400d0300d154209040b1030742c0701c440f400348980c41100c501e502d05c4030b0322040c907800000b03828513512080050180c2451109002038082c0602600c0001c0e9200912584850341c0c490042e15030f4280d0b6980d1209002d00d070641238620f171909034003115010400440722010140c480080d102c0c500e02e010721522002060341c0080e01c05a846400904c0c41381c03200341d0104003000c130400d40d881c4103200d1501e8030b18010b9100c400042c40750b40750102c1e071844902004601c0d81243c8071140c1c0800e110020007068a13005064407021a0800e006e03d140401160840c5600801c3c00203c03041d01c80190725 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 719559460 1250 719558210 719558219
    0xc04050603040f08250501060911310306050a0f0c120908070b0103060e010501080f0304060806061605074101120501060e090604020310060804050a12050c210301 71
    0x1158040840d00356506039051040000320301e0f07454070307040f5660303104078510190010505146c0d08542040e841002c055140180c1041d0000c6008259480d041610b00c0040020140b0344000c0e60348201841c21002d20848514040b01304211944482e0003038605020401030402000e0002d0704440c800400c8801103a0a07403103080461035180c10a2818a125800071405c00900d0765030400007517070a80085800d151200c1300450107910920905004002240060242820980030b890f141c1c0300d140030700c000700060f41000481588a800440e5001107041c140720303221159900304280c82d41c61a00404001c1c85114075034941e58600380c0c0450a031700d90194030f602c02038044101d00b030101076000741e03903241030021604040b10f4071425480f805009002c0350726084001110202042000c0100806c0944100d02c10b0007440380680321440301030151245030030150b2407510b0324103155240007400c0d20020078056100ba4841d900c1540607024001ca446e0007803c54059a491040c1e2003a0040c0c150714008109600744010031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 719560710 1250 719559460 719559473
    0x6050a081018021c050102090409060c030507090f090c03020f07110102070b030910020c0a1506080106120c050f01020a0c1212020a17090112110301140315060f01120c0c02090c0405060304 82
    0x680c0d207817092000500c2d00b0022408101940c4803540c0684000d550b82084070b084d503826010392540080245440034415080c580280f94014440c0900700510766940e05540c07516000b03504546409085640050b1207075031920700600e003818083c40385801400307000b000154600f90070054038010842d150241600d110f815101000a4001c0301701e00c1090b00c03803440090003103601e1032030310704403100d0544000c5181c81c10109030341d01b5981d20350700000c040b0000b004403402003410340d8090700c1a03690031948420340142d8400100e01c1d1500e00c0390003425480740c0341400211030020818810003544104a01414100d100754242c1e00c0c0c5850902c090702d061489d1050205452124000342614074050501c070f0708104c2d1030407041044400c9840d142e00d0041c1d00100501405600c00710540461608500400d000f00722951040c0801202030403403406240030941e00c1c401d581c020011207840f84c03039140c010030030ba020300880104ac4040082d001e0380155038000c082102d00300783d002110240c9502070141032542d2150754894 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 719561960 1250 719560710 719560759
    0x80d110403110f0d1b230a150c0212100b0f0d231522210507141b090115081003140303040c05010c02010e0f0406050a08101802 56
    0x503400700744110701800117041d280650503880f0a10280c0700309281458125103400090301d2107061020382083c222611603580010070f41c1580c61806201b000c041c0105016503100c16005c1000354041906072200c8490b00001421010f41581c541080c00103d5220b018490318440801080ea00a44030080c00700c003148420b407000c0152020300e075428561507521010a8204140907056040744290303581800a8155503000c0707a200b448010f50b441031603a115036180288617040e00a4505100c17002040700f4a024054415a070784960000d10b60171a50f4010200640c80c0c0b0640c0081c003e188840c0d16002006090010340a8183c5528418050f6403840001c0c003525000e000800301604401c0499020000a05032400e0643c03011000d8029510390800340340c00c0310b601e881508000c0c1000214004d210141c0e0388440000101601540c0140c008501710300800c000c0e0986800064000c191340800095078800010a440031023040c42c420800240e0400510400460b0900040e500c01c426100c3c070911540084801d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 719563210 1250 719561960 719561989
    0x5071a0f0a02181017090d0c0308180304090204080d1103041202060903070e01050907021501050d050a0b0f1b090609040507050705070308040303110d200703020a03080d11040311 78
    0x762010250850000324500003605100000404840380018203541d20300ca402c0d0801d482c86c0140580d1500110000d298058103c00502000355076000b05006a5110b003403524160759103402d0fa03903103c1c0c64042d2180a54458410703ca40e52180311580c0c0c41d858400e9030609001d19107107015614080ca006e07040d2452100140c0240da00400c20442c001d1203a0b02000000e005148000380d6402d50340c50101049111040100010b066402601414001e0b41302100d10905441c0111240c2c2c1b06034990b0b090251501070000d0000f400c4100100c288a1341140380c0d000a48208807080d1421400c61001009914502070908139a8010205100081c1a89841d4002980c0f2500300d2918900b049280d0310341c01d14164081d40150382c40000050144141a4842e108081d12544d9200500c080802d5040080a030307a003542014039221100d41d811881c0364824442d407001036400030441640b0340c1d120309212250b40e001109000c080c5103403240e4000444100b0080d241180c0e007080040d5400202c40c41884048010320b0f4a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 719564460 1250 719563210 719563237
    0x140303100315060506130f2106090c03020904030306090614181b0403110102010510060215101502010b0a06030b0d0b0c0706020a050903010b030609120c0f030a05071a0f0a02 76
    0x10114085d11450064001640c00c2100620783c14a41021400240e00e240c200c0c0c841c140fa400e601a184c61502511f100030f03668042c000103008200b5080580e8042d0307150700002e45c01400d036410f21040c103a042e0051410744010200411240380da4000710000001c80081443c0c2040f80c1c1203200c1140081d55114076400141d6030544540794501400008041c3c1c0160007c0310400c21102c07140059580c24401c0319444400200c10200c82da01380840699169512080d03003071003030f011900041c500c01540812100070101d0901030b001d50400031030041e001c2c2091403c03060046103070b02400603206100e40500008828060810b80340489951140c041d02e100060800200d240308100d0300c1c0c000b5005100402c041030640d40c0b120b8684104a040500703403940030a00d41d1290303103d0014000d5030b5201117003c0c0d445101c3d890040381d84200c0142c02c00d08055040c030036280140008180f02c0340290b044002410010b114a0100c81260900c3c40290380e6000155449030b14000100c00041c441700099004004107068000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 719565710 1250 719564460 719564471
    0x1202090a0f030501050a051b07030e0406141305070509060a0905060f0306040b0a030302120714061503070605040f170312072001200304030c0c12140303100315 70
    0x812002001a4803426009102210400603c8801c0c442d8030382019001c2c1d01880380741000340141030006050280b004a0140c00070303204c1c0c1054000c00d664150303501d010b401403003156503070000089207080303000080d402201081c0185214072400c4c400c0358070880c0680c03111410401e01200307010164000c00410414081e1515011940b0359030040075141040074038105a590346441800e01066900d403c600c180150b04841040c000241c001c9481c000030301c5400e1840392125400e062002680a000c101038019024841c28800c50760050000721160360400e4007290660703683c0d10340031205842544a08252410034040074888030000084500711884201c007184d00303042c980c0131500d211550958000010074107030b090890441d0340000c45680d4400d0800000c1015401d40d41e10910300e8880c0a01e14800c006000000404141c01212a02e1002d41c00c00201801d094072103181d03595030301528005031005940c10707100e64151403002045038841c0759809800044c291855894071840c00740c18001100c026100d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 719566960 1250 719565710 719565727
    0x50f090d1b0308040c0f0902030a1d0c061c06150e06040320040e1902010e01020a15230705031e042319030509040b06070f170717120f01050d031202 65
    0x5d41440541f0f4140001a138074205002e18604803000580070003111056403074611005000800c2c2d8031034200701603411030350714164081c0d24040d240312044101e245a10b8803501003280765400f03007110010344c856210500c8450000c01009000e010f1341c80000c0144000301035400300c503101d003054010081c0d400782011603a09121050603007003181c0070032640f0700d414141c0c7e202c006560340305100c00545402070001d001400059203c404001c08401e4000e5001d54584441511b108004c1050500c0c101c40d05a01e20f050781803810703005081e50300540e1300740c00010740d8510640c0c986010b111110300595120040d2555545601d0b0180b108514802d000d011074002e44007400381282c101081500c5082c0705e540c6041d0b41e09220000c100407915250705041c010381061081d038000850604044584503044290034502e5400050040003034426504000d0000688000c3c00186e6405803024000c01000700381c0d800c0880c0e032001070140040c00240b2516911440f5a4820004a4040c0d000b5184114058801601e0180c02 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 719568210 1250 719566960 719566979
    0x9100e120d0519150512030403121205061516020a15050c01052203051b0a06020405091b0a030e0a050607020a0b090c030d0e040f050f090d1b0308040c 66
    0x4401907410680311020001c0038400780082c00c0e0804003d4408008a1141c4401001078040034001e0f240034109903011040d6100701002918021a40700c507254140911007200284450f01003407030380005900b4400842c51a14191490050003d01d410440c2e0500300c40381c954500d040360300300c0240d802800010000c5920000000d602481c3c021503100c090741ca080740e4010600f180c1d40288200807402c00004a00c0c506588121080221030305403401c503448190407d1801002d0302c50b59038201c09441010003240802c200f603005481201c0c0121403044243d03851005a100d511360785044100d01036070400001d0407103070195120b61000c0c40144101c900c0e109944e540c09241440c2a1044409030340900c8240d0304000550b1a8294052101009044c04210400100e1790710505a80b0101c144510861800c5443c1c07515802803914100c100c00911442c2000c2d00c54400c5c04005a4040405006241c1010101405940c40e01038071801e00050110250040e20219008080540212104ca401100000c0d45a0300e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 719569460 1250 719568210 719568217
    0x12050a121e0503190501080c010c1b1410050304111203130305100c020a050304181e0c03050714070206090a030506090322050919110715060b0309100e12 67
    0x103162161962800c2021400700d400da04840c00304e424a04010041c054514046040c040414080c246007840003081c0c0340c9400c1040c3d1400b00101501002c5000189071140c1580a548a507800d0320340082c0b83c0980001124284001c0760040e200001108044c040c505026502e41c448003480c2098a040801d070300e4184d44001c0c2e4662098070b0b594401051140007001a1060342412251400100401c81c4a691410303241d0056229880704030711220809000e03c0d2554000254101808211a40021500300d400e00108016400d010001e8500300019100500880c0010600d059068080d800c03e00541d01700200c40c0e121a04461700f10800180000c001542080510301944480019503100c49048200c44048550b1908460040c1190f0b0380800080d01c804c05c08a4009070080b480600d80c5141d030070144081d0000034240141000001a030740c0900000c64018031030351038440014040c070396a80c4160b401602086d242c5050b540c1003070218505a640301c1d40142d0140c0c0e10801925110032010520a0440e003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 719570710 1250 719569460 719569517
    0xd112503060f09020a0608040213050106020a0b2404090f05030a08010320010f2003310617040f0204180213050705090418020a15020712050a12 63
    0x4450941403007000081d000e0240c41880c5080100000b5403180c000660b0350782644105400d100207c40800d00717540300c081289115001c1c0401c24001542e54450003541d40380c111000352524a00c542c01710b00e0b1b920000035083c8400304804a0000721983c0c5504100044c42e49110458002c0500b000190005005102030014199180c48420343c961441c18414400008144030039101d4122041601c0c2c0c3da81c00c4285c40ea4403503000d107011081e040c41c01491142525010240d50316a00c03002c02c84101e196804a103101140343c1031b19040c140b00141021030500300790366010703a2010416100b00040f4910615002d60382c03181c002c00d45481c1544041e0045021030f6005d450f4100c0413041e07078502806500345448042c001c0c02482004000358031301141e00510f82e02a01c41018400c41d02d03040a445100010011000180d800a040590581e81d50040d030b00f07035005c076403200005401000400928142e0382c03410303004900c0c0c106014048900c1550b81303403c00340030710058880a1000c06103514000d601a40b00e082c030f601 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 719571960 1250 719570710 719570773
    0x3141c0509070501020d08090a06050c1308031306080f04030309030915050703173102040213080c060c10270302010b01120e0a06020714060a1e0504050d11 68
    0x18104000241030904200201b01030100c803c042c0300000c0000158400c00a8000c1000520360b00e400a540216114050816820010b041008100048040010b1105200c0008400b261a554500c1034800c03507021602c0302e415408400000d130100f400303a003103004c056100e8502442030700d803609001c1144c254407001904c0040c43c0811040100760f004407241d4000c0c0d880340031104441c0340102d85082c1607400c1400c403580c0d04180d080e0002260003e0105510516401401507496045031111600c0b4400d21340b2901109208a905501c01414000c0803259551100b50280188814030400300300a081d8244590004004e540c941c0720b0090080d00031310300410300c03079030001c145461005c0004040c68141d1040090080c81c000350401600000210302030b0891344680302503181c46443c00c09405400c40340001816074050803040191000c440c3d07120780391007452010403003410040050b04030203c61080707800a02d41d600441070949154080c044880d10410301c8412a41c0d03000b480c1350521401c45d00e000c041501c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 719573210 1250 719571960 719571973
    0x20a0b07030f030218100306230306010e04050319021c081501030c021005060d14150c0f090d0213020d0c1103090105070b04140a03120f060303141c0509 67
    0x81650141c0ca10400050383e29041d400d05c002e043c8070f00d8074a03a5010a261203031012001a086580c0250013601c002d03c010003c0c45540c404039600c108001c0b038100c60f0b04c2d20a000c1c01c0004513008590080050040d60014011810074007041c0045100c010124502d1081d0710400480040403410345554401c04900780d075488240d810171442c4540d0714951255054141800c080032185071076030001302070714850109900801c0340e88881010850a56203070302d02800100194111207100c07000003540024686491003086201c0c0d4404c0e514032924003810195010041041202d5030701460050303a000407007400100b030381c034658114039020b0040340c0c0802c4500e043d4545400c100401e4039004950703018400d030110061441d004082c00020715500c42c00030024013074030802020400f40010ba80c400702a00782440110791f44003189040140180880da0700c0301241c02d00f000d08c040249032490080302c00300e035450381354902d0808120800d15078540180c41c20898114404807500480c200c240240e60242c2d03079580161030f0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 719574460 1250 719573210 719573213
    0x90d030c0210030c080c0a140703031e0b0a030807080c0616090e100303080c0c030406020304180b09061c05030d0507080903040308030a0b120105161e0215090109020a0b07 75
    0x18115008000b606052902e480d0340d2440341c01011041e40b2000580310940d5070600c980303050340d03413680074070754070100c014042210810150540d000e000b00c0032140030581484240d000c07025050301c0b51194116001484400c0800c00100031a003e8a0b01503c181008d5040414207c41180f030141e00b191903000f45400c030a088040160001101c0c4090400055005860b00c0c0484fc9a281011030344001000c0001603000201c00082c5c1006842045030350006603581e81d0340d12000207580340c100d030150348102072048030075138107080a600c5000744105010380014011b940749420000755241802002c60b5101c82e026148000030800d1004181e9003031004000903007810005002040c016006000c060f90742d104020510225891005882d4461250302c0d0200341c1d490007001045010f80d411154120b136608003020300c80b801507403c1c002d240502013036480c60202d050200d001d2466444414100b009a0010403984294240d181d078155441038000c0300105851701558003158184882ba40b00103038840c000b088860 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 719575710 1250 719574460 719574469
    0x30c16140a030e19050f1009030507150f081e070e060d09170304081b03040b0301180e0d05041202060909090312131703040507080f0708070f0b120a02090d030c02 71
    0x804c0082821a0300e20107a09080108044039202c08113036100d07550081842c51640e04c01c0c06803101a41d0302009858210390354030071b4901a01c4030000c1d490042840348001044003442600301900c0b60119a0750300d402d0204082c490041210050440d401b0401c80158044064a4420080c40c0640703020304005020159420411308488411800d1144114200284000b180c0240c082d104070940310074035410858080080d107840d5204950000a84980200c00090445008116a00c41006003d000e02540041132442600c8920004030762011070014841803041d45117484040c000d49101422030380c5400208800074000d000201c8070020558000201c6a1003114441800c68001034015400f80764540259651030340084540c4240e5204000800042d051150800070000101b442c40103460a115028004a403982620702a400316482070010001c0d0b2800c000d1240c50443d4546d9504905144403000c4440750500060001074445800340208411599010300c1ca00190f8801c2d121524200d44520500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 719576960 1250 719575710 719575729
    0x9060f130c090c1d100e1509090f012105060c0a020a080d0204031a060312160b0103060e0706051c0c120f0b040501320a080114090f03030c16140a030e 66
    0x34010312400e505e00c8595508500200240c3c0740c106c904100340c141c245280140390141c22240395100c0540b4061048010360480703614184d54071103124902c0c0c41c0e082c0301c0c074003100d001e2900020a01d6003c03400185002c0d40c440003402a040e0307a441512141c11003600d0340c1d4501c1d040b0340c45c898081030380080c042042206035010342d500207a41c81c165241c1c0c0c0c41c203000060348034071680f00c80e83d614642c005816401400203490361403140398440c040101c9940c4905042004005a40310309120340b0a442e40402c04900500555040300c0304560507100c0040d1050303004014260714040f410620100340c0e018011300116001b41041c0001103c0c000420200c1c0c0800c000c26603006031b200602d40c4015080d500d050309000c145030003c002c1181840424462404007040e1044145c0e0b102c20465440c1500d002110b890109200d4000e15000044509040044040548a1005079004081090100580d416030301c5620441c007041401201c07040c2c8200754480c0c507a41444080c050407000521200900721aa250402a5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 719578210 1250 719576960 719577017
    0x70305071d1306020711060d062610110f030c0a08130f0308100f061706060c0d12110f0706060e06061b01060302040e060f09060f130c090c 61
    0x501042c14081c014100c4000300940c05030403503800003202c5d02880b1540000c2070145402905040d0b46240d2110fa200041549006580803101c1d1070f405c41003080c03030b8495500c0b080c00d24440640b4000c9541c00082d8001c1521760020080c80c503050041d14150b28218001d11703c00d0012400c001d40d5420308003070042406d00c00410020942000e9800e04020494212110040560509001049071030303100100500810340d61003200919500c1001046080e8807100ca03440000401256138130a850301420031042d400780603403061440c0e011500405041e0302c1040c103d41e003a1448400060107030000f0560340d03034641c0968205204100c002540c1002c01850b481601e005041ea090076480c64140503000600c1ca21030b19242607031394642d510030565420000c0d4030650056034014010000160030410441e00d808e4101ca516841d081c801001911554012444034880d114400d242e259958525481d10b581144082c0182ca0168080c01c0c00f2030212518485c1592030030154441c040514002d045030780621403402c62 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 719579460 1250 719578210 719578259
    0x30618041b08070f090510210326064e0a0308060f060d0e0106050a09020405060301061209021909150e16110105040308150f0f01030b0d020307030507 66
    0x3c04001c0100c20b144102d0079a58040c00100c1c0b683c4039100b18155490b480e03000980d07610305000726a107000d40401c41d480d14141c400e0700e401071031104594003502d02141001c10038480d100100c000862034601214500180142010040000027980410034002c40d103a001c201d000a9a11440358920400320300c40201c240c40c00070040c0321110003640d000b070680d04040c2802d406060f2400080a0643e940c0e130544081c12071401c0104041e084060350f00e400b0f0013032031061900440c501c0c10f01044000050084805881c000340a1501d56403800c01c007110001d03041000f04242c01c0d500c0e1210360041c1d540c2120800c2410840d000c0c1104282400c20b001c08076441180301010901c071840d800c0005801c0174038815401201001c1d03a60746004103000c161010540400b10780394a51810007000708258100c20864040d58882c2d00304040001e189041c04245d81c0c1c0d02d908641d0144802f1547c00d551f40c8250001ca081c0c07040a001200307000d8166000c01d262a10700e0300111115040703450180110a00802c1c3c0e8400a441043c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 719580710 1250 719579460 719579473
    0x6030f0507020c100c06050f2a070f02040b10030603060c111b0307080f07080705180f0603120f0d0b090106050d1515020f0d0302041a030618041b08 65
    0x10043d40d10811588160301840d403246580c41481d009480d81012141c215400307002d41d00c0c09501d48409030780103c50150303143c10701d41d2802843c8102d116040d110001c0050041e85040700380d80f100051614161030803a030054584c2104151038031112030030071000b286500c0210b603850851805034140d4041c00d0b203001c04c02000407000700e0f00e500000307002c1c03542401c03410b0041c0d06400034401081c01c0020640040c100fa11620602103611180002c005044403040b400f81d507101e43c2c46104000c0b01e23520900b10020f041140c640450b507030000d000100f0360005002421102c180f015442c3d01d41c1e03c0d82240c1508400d02c44046811b9648040c0c2e402a01c00d0010200d1741c401c003540c1400c2000d01240100b003c55803401e940c030744440c050603810500c0c880c003800311102030b0780411814000095441c45200d91000083c0504050742004c540240240c60a903442800190143c16900914014580005042c65440304410400c43c2c2544820307108580180d0240c0302036456203440c810350b05e8070840e10768042d000960084 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 719581960 1250 719580710 719580721
    0x72a0608090d1d09010609140301050c042d0602010c1103031e33120105010503100c03060906031109070c030f0804060902121e0c1e0a0306020403050706030f05 70
    0x1050300c00d060142c0e8148800e801c03090000740600c0c1ea00d10f1050a40101c50040040380c071580045050044803061005103480042140c02c1c9400c1c0c64058801080c9810f0074007040c03001c3c481c0c0030404040c0d2001c009405019081c034850644014041d944178401507555844080581e66000e201683c0c05001d0340002d6145003819628031a8400c6800c8000c1c07800c0300d200300407a40340316103440a0f10701c4402032014000d140c2c4003881490018444255000d2045090300131801030510306000f603e0403504003e0103411741e21031000031345014100c13080d902001c060760780001203011826072140708003560043c10001c41d0a00301c1c80078004140405881d08081c80140741d40c50b0f000030342c4203102c5142040346103018242521149069405003001500c000c5d400018952508510980000c5021201c0180b1800b00510301143ea2803d03214032074440e81603000386a01e2041001d446000b10740448001c805464281000d0350f070380306c000172038219070400c448603000355104004080d03060041a840034040c1d002001141400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 719583210 1250 719581960 719581963
    0xa06091a1204032f0303060f09070905061e041707060c0b0118060302180a0b0a08030f1b07030f0c06090e0415020f1b0f03040e0406050c072a060809 65
    0x2031008042003a03000c0142e088000c0010485500b66002e040c809904c40c44d12003940d1203410403903000d805152464500f0b8054504000300f240520507a07101c40f11801d0400003170040d16408004d181c00031108402d203140c0002d140348028001000650303d402d418501c0e8231422800e01a255010804000d940c085500100c0d5850f1001811144400f0743d80c041382ea5086001c802030b18035540f0283d8810b8400c11080c03178203e00d05a01c50310401d038488040081e40f00310320401108040c1030050f6415680240041740d00d2051607001054100400e0181800362400340700d52500e4048203400465600d18900120010081220380390030250466040000c0e0160814400340c410300350040000d040c510740d1010110b00606564100c4a10700b42203016903545030080d00c2c00d003400c9641507550007100d1090110452a110020043e00c0c169801e0902004481d15583c883c40c018241c082d1000d0780204080000385c0000b1507003810004c0c1c200003d10b110313060118071583c003500a450382c2d107c1424000c046d010400304040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 719584460 1250 719583210 719583247
    0xc0e0c0417010f0905031c0c0e011b0210090305061005060306010e0d060507050c0712030c30030c1b020f0607060621052103070c02030a020a06091a 65
    0x1501e07000201001102111076014041000301c943c0c4040c54134100c0e1091040102c0104490340e000c50300302511440c540f42c0c3e1000c941d8090000800910307081b141050b55071040160184400d180300400d84a00f4241d0000b48a00c162030400d1004684804001c0040060070301c84650b02034802d038500001a40707484003203501c41c4401450581000341d9000003142c25954100c14811080e003148041100345081c504c06091644803884405092107032250000d10036a041d00d4503031440760325988856070118180c0d110300e0341b124070001c1202d0801d07860840e10800c1c90b03040190424000a03550100704500c0044018040c042d001c04184d200700114081c41c40981c5076000031881da183c09641c0d00d503a40c441800c264000b40041c0c5c0002c0034403d0034001d1100300c1912200140091341c000c1d0241c5220007030b1541d01d00700400c130514034181040c078103000250095018290607018903001400382c1d41e0a43c140ea0015100c210585c0040c2c01007a403900b001d1010400d0070460301d159040c206c510f40e03d003407034090200b6001c02 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 719585710 1250 719584460 719584469
    0x106060503160207083c031305090c0a14070b0901020a08060315070f051c060905070f090311010504090c080a0e0c1e040b03100b030123181603030206040c0e0c04 71
    0xd0790201c44000a0f0009414204010b8584448041544090602984a50019420140703048c0c80410202c1d080c44c0a46116015410900959285c0603521805036101004405540040351043c0440320108020400361403240305c0c00800140d848038280d801610b0202c000c0c00341c50007070307014941e0203001c114100c81d21a002542c90400c1103140500b03030812540ca11842402600076200320502004e040102d40107501581c640034070030301140e52614000c649005690381c5039000510881d50410105070b800030354642c2c040061500600e810f80344c00c000343c2034820540650000130303840020807010926510403400400e2848000d868040c0d6802c002415011a120041d903903030307494800003902da0743d450b407180c41110005410342c1c2c0003120010300c2200612a012115020b5400e110b04000b164038480e940341c0640300011b000f090a9201c5100c820780540040c5040d43e641d00ca84d100c40d11540c10000031045c02035100e80d00400d40c92034185000960400130381e0040301070803800c1c024814210502001c3c2d40946 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 719586960 1250 719585710 719585743
    0x30601030b0f0a0f0807062a0f0b010b090918030d020d140c0309160303090603020c0a020a08070303021212040201110a080d0c080702120406140705010606050316020708 74
    0x80c4000300181c0c078480011070499220504100004415803150704d00002c840d945c50503141403a603100e40c141c584214100e03100c03000082111004094030b001640c0c802820b4090b005407880c402c0540e8603c5400c1c50700ba00110180e08002c2110001d0385030001c040c540c0149102040c0d9001c1c41407040b10b41d524019081c0e004540b54005c034000300780380e9465020040d0215613120096250034190b035000010360040e559100b4900401d800c2b4841420346a56800440340c3c1030740c03003d0007d0f00d08807040703009410803030103611940a5008a440503030b0303c0c40d6045000d00125009450410b2035841c01a00d00440142c1c2c000781c175072041c020240401003050f03181e0327402034080c24610b02001c03280c481e02e41400140100180600c4003c140f55100c11001e0307116180131074040e2141c51242e15005803d030794820b5090b500c20184007042000303004951042e40322804500244a5241c10060f842e42c2c0d00c2d01f51503035900301400295011007080250411203002200d41c83c403d0000c2c041507814a0005602c48944c00c03030600e5103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 719588210 1250 719586960 719586971
    0xf020c04020903281a0105060304060c02030c0115050a0518010306092102011a060306090a0b030321060102060601050f0403030305061323091b1e18041e0803060103 72
    0x1503201132103d86404144085109098031460710582000010300d00d0950700b95910490051804100101860517518024500c50035a41d44d80e881001400070502198110b01040c094003075008401d0084a101c0000d1007220501142000c05200b414952503000f144a40d40b0b002c0d003074461000321040d031410b69401c4100441e45060608080d602c04549a0340c00089581d0030440c203e625a041d0f2002d0103001074081c0c1c8001c0c07022040c08004050000395251789d406094034001c2130b07403021250b000c031b1040c44000d01504d00707101000c00318100d180c0c02656403507903020500c000c1103000c1d0f0f41840134a42c001d03001d082c0381e800e00068014102480c05140001018541e0381d0010030380c203075160b0710004051003417044140119000c8031900300951b407212058001c410038503004142010b6010504090140d000f02c50340b8030b1010400c0070001e1a283c070724124080a200390a600085484903810240e540240c4114001d560a1a25201c800510f136403400103001040c80007450b0006600000f12a044802407130040740e07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 719589460 1250 719588210 719588227
    0xe06090d1d0d150b10090e0a090b060904260309071a040303110102040b0417010e03191d1f0f0302070206030f1503030a030e151b0304240b100f020c0402 67
    0xe05013110321941c040190240e0500b2a540b1a01c100c041c2c6140b039414043c03989a10403a2401d0b5403180d0401000a002d082c0000c0c083d00345940a25803141c001e19680c0d2014401040040300c40f41c0c02c1e500b202e8904400410441982d00400c0a0340042c080c640b4418200340c0000c1400b01c460042d0b000090800440c0c80d40003180b01c10940540e006816041c4402d941c0b90751380c1c040d0001e015148401d260455013040a80c00c4020700c0481900d82c000c181e00b120b0340d030b0a0b4442c4011a12009816a10b0b841007494804c000001e4445a00310549400d400c1813a8040ea442041d0280c0700f605005440c104160041120400607154941034940010845c00a03d94a03242c0c0c854030b4072052500014590184000309043e529940d0503005050b0715009001a00c004145014103085d00030012078241e129420350548142c4001188401158050b000d40540703407110f080e00550b00c00e000c2c00700c1c0030800e0440c5c4513041041e4070300e407000c03c1906456040c03c200c4010300c1d0a5030040c1d20b032044a80f1a038461342c1d020503041e5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 719590710 1250 719589460 719589503
    0x1060c1506121209240314040809151e091f020105071d0319150f0917031504110903060112061b0806090a0e06090d1d0d 53
    0x360403040c6030103000503515001c1008a000e1071030800c3d101030480d10310900146000300321101c180e07506907a0401d0f42e1400048801c0051604140c030200709655800300501c8552541c031514080c41c4251015a0340d41041001c2100741c20607a8046a0b40c41e2040108408a403580040194598031021180d07442e409154005410a40d030840403401441b000c610304400341342c2c10f500061040155440300c0b40240c603000b840541040310b00f00e54941542c0803d0710390400403944180d0264a80c0300380c60740c3c0c0100d0203500342c01341a6400740c10b2010100782c40f0900d104c100521f000803800701491400c3c9490840c0303040c4449a42185051010900403a078800030303800009404011030b0202040a01100da095a407100022003100d811305040d15454506541041d003941042c4624401c082d20340d035000040d48903201000b4040d24017030151891155100e503844640442403080b5446100000043e00300007040c00d1029001c0c0f400c40c140b00c048451015a00c03a5145d0341d0282085040d504115085a44e141000262 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 719591960 1250 719590710 719590733
    0x512070908061008010c09210807020d110a0b07111905151b0d08010306020a1206080a230a0f0c0b04151e0509060d09081801021e0601060c 61
    0x1e0010b0b0081d0020000e11056143c07200c0300702c480d20b1008111a1340007800071507041550f40960011602164200c2c1c080c0c0b0030894000591341c0c000d20209143c84e11560014080003013448007100d0002001450030b844c0c1ca000c0000f00008d19803121540d00c1c01043d90703507031482c00d22907000e054410004030606881420307400911601a03c8041c00c0c40b0004181c01032902c4031782d04042c90146001001c800d0604c1400d07000300384d4503411400ba464040e050703400e40d40c45002a405c904200402c004015084070250035890084d40c00400d001c502a240394903080c1404100d04120328a80b00e04002c043d9158120504009010105c00b600507440da800586a442c14a075002031903803040985240c00f04010503950220b00e0000440011343d220600b800041c5031b0301c0150070800034991004514180a04c5125003092001800503461004001544201f03c0ea540d140942100248841966800c0e902d0750455804001e50009100b016040c070405119500301c455a81d07405000302170420406e00d50503004c001c41c00900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 719593210 1250 719591960 719591969
    0x5100e0c0d090b0c070b010b0430081204061523030c0301022107020a05030d0b0118090c09050315010303050a02030408070e06041d1c11100504051203010605120709 72
    0xd0f402e03414540340810b02c3d90001c0f201500c10131900c0c0700020b07020200701c040b0790465140422000c0b207015501f1201c2441c80042c07504c20022194480050005410400101100f010010010703100c2e003080d050100c221030420101c00c03d091f01c82c80301800440c07050020910840340f0b06480702102001a0f01290511001e8900349805600215030b41c00c8400c09a444507100141c440200c008640c0c4100089a0b00c1c1c41411019189400420094044c0325446d00302c0940a141814046100c1505080a01845030150b10400308242c0d5031030f000c981c21758011225401000101c1c010912011116010703000120188002020700000069545000d4020301c180e8005028100680e480c00ba40c030902414040c1c0110f0306244607525180c2d21210300c403003142a101003030440d2001809521704d078014404040d07140500d240184090300d41706050040040107400b44060819502280c2410300740f61251034680000001c251212040c001840309992290a46000c1c02104025454076100c41c03074141d8481450f80c10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 719594460 1250 719593210 719593223
    0x20d0f110306010822120509031005152713020a090b01031404110d150c0e0a0807050105070b0a0b0904050309190f1a0c1c0305100e0c0d09 61
    0x880d0018018030300246102d05020b0300c1c0d80281d65034403115543e804085107410205410810922400320707008141c0510381200074200546003900300400070f850601807030076020352140c54008010380403214401c802c0e0000007e98000504002d240060404d809101c9031082005940900040755050300103165030802c5d4025010b00e10705900c9540d43c0d0060000b10f4065804241809004943c068002444274850794105414001d2030518408104110201c2c0c0400e0354204e41980030365a41c84118443c1c2c680c03a00300c80e01c07540024070b07656043c0401150550b020820917000810304105030b0360001c0480c1c80320f40e070100c0310728082d40c0d5000900c0014066102019001516402008104480003000302441c2c6c01c225040006c1c61450060100002c9140c051035604458008040058403100500700701d200e250103804c141040541c50f2814944050030305205003802030001032005c2160076211701ea4100800c01d182041250408050000c0b401014227030f02e006850000340c50b040c035803440d4000303014640d1002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 719595710 1250 719594460 719594471
    0x18020a0e070305010b130605030402150301170705091b0a110a030801050f221104050d0b070f020d090b091f08060411180103020c070b07061d1f020d0f 66
    0x84003000340308085890310007181ca0840040381d41e0400800342c071341c0c2d61078a4901c0000a41810001c449540000e441260001e130702e260a40038094461002d14081c0c10302686019981c0046000f071890604243d20a6000308030001c240040a611981c0c400c00d20385400078450342e64080e55808544441c04e030b00121a4900500009608144d8002c5140d8101c40d002c841000740340d4121010004251940d01301c2c0e0402b000360780900300a50103d500301d0004144150341c40703810300d941c943c040340302c3d00c810075011181c071201d0b1010030201030341010050b0064000d5100410300150b040307001a1181055005400d405c1e00040b803072568031b5445002078800418481c031f8084840d611a036028084400540d46e05200f0b41c145403190360000d0800c000e030b90099060320141e01e03d0b80b0010340150000c1d4080046a0201e000f03c4601140101061008099040c0710f901e0003d0040840c40c0308200824003003440d110303035070440c5031600c03203841c004103003216202c881d00c100503940c00b14804104002c0100e8420b030302c06c1a0414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 719596960 1250 719595710 719595719
    0xd0b070f05030c0a0c0f08180a0501020c0d020f21010603020117090604020d152c030a0c02090907030203390609010f02100905010615051314040603140c1005091318020a 74
    0x1230524600c1d03001c0c01d40f01601403688440c016070701c461401d10ba0743e420a840281001c003518002d08081c014510140620350a0f0443c181c1c110301c04281490303d4400e0b691100c80400c11940e01c0344860070252020070801d031a80c140a0000e13a201c500240001e84100600241e80090100d03098511441c83c036441400c004034210780c42114104614001e10115030101000000e03120407000c0704952801d4000d076102903014240f5820442c1e002d0020f010305289215142c004401030f10100302d100041c0c604034080c1d1523800d10394a40042d01c1000400355140d01e80007a000b0491644038442600c40359142401c01c4554440301c18412480c0600e0462803c40c6a410540104103100043d031042c01594030801d072072807605555180a94062080c11088000705540030010401c0c10806002c0450700000140086540c55803526844da480d00250710a0322180c00012000e07801d8070305100c0a5030b02180904104e13092608100000300a09018002121000d071a141d0040304540c105501011070740d40141503440740380e1035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 719598210 1250 719596960 719596987
    0xe06190602010e0706090b0d021c02130e060d150509150c0403020406090e0a1b080a06020309060906061011120c010c090e010803190e0d0b070f05030c0a0c0f08 70
    0x8428010114043d07a035005c07481c144aa0728403020b40b6040c400261401d20040d1460009501c525008040c1001480040300103860a00040103460180d410444015003450a0b1110000c00501824455141014040c0000760305041c64614027552100c00943c0d6584d001409050010f1281c150001c001041c0c10419841d140780c1c05482981d000762000c02c03495448090100441d620411141000e9001441e4500007804042a002407440840031804d812640ca10780c551805a0465003102c52680101c10010740c1203082112681c014803010091000d41445400b02c0c0462101140b00b10400c074004030069104041042600c1c0380c0481489400e139510b40000355a8000c18480c0d607040c0004809000004d101001580c6050580300035402541c640401603015200185521050b00c0c01d210302c4080405455881082c1c0954880c082e0745559142c1c80d280000900d511034004044092140a006101300d00c9005070503901940880d0904c08200c2085081809094100c900001c207809000a540c10b0724624 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 719599460 1250 719598210 719598221
    0x60902042a03181a0c040312052110061412190506010206041109250909060b16080d09050f010c02071d0a05070509310501050a0e0619060201 62
    0xd50740e8104020700d002c405907040c800708050b0141103a44500c0404d1114a8500a465081015542214645031b030729a903220089500031400000f01318081483c501c2401d081800347d1150005000c5440e035407500e80785082040c85540030f030308104401201c441c041460304c401180c1c80c1034440e0503503e9281c9045540c2601441055040c00ca842d8100f002040c030035400003d03128003c07903101c1d501d50482034224003801900140201203404242d0b040c0400040c00964445050b610030490b6038034020395040600f0302003590310303560158101030000c012841c0501000c0c0c007904001c2d80d1140241c2c0e41c070b9101002c903002420300c11704041c101e070080000980c1d030a41c0540c4002e1075543c8a4081e01c1c0342c107a407608036611407c41030701010281d08461001400e03c8d24140d0082e6840031032400c14a05045011000c03890014440482c0001c03540c6000c3d210256510880e44081d24901d1002d05006560405020420300d84152140b451448051008504103a564115091035074109055555400b607440300c000b4080d24 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 719600710 1250 719599460 719599541
    0x30712060e01020c030a210c05070308090c030309130204081f0c390b0a0e1203012612070b01051003050f15010e130c2a06090204 57
    0x52600c040d440c070008060003901d0f080304244014504000c240380c41502c1007040e45805c02c1400c1080c40e00d0901d100c1d100d120380003407200c0703a90703840f615107400385000f411030300d0040c0103480c281d4001e03078840c100307a0750010445004600035200222420004c1c03144201a0003240c00c00c0804c0d001c2c0e4ad034030042d801c04070801000807505801c824401d1581301c2c8003e072516200fa0b00c04003400c4d1441200306004840d03407130402e0140100403107041000700068464009948060303400701e151a4448030500c0204c50104040b03004a441c410b0240e144d9450f003420691041d01c0a07488a031500d000c3e140c0c96a03500b4091211081c41c0c903078596525a80c88035850711000740380c2c00340a03242c071075896040d030144100d1003845950310503200e440d0b28408545540440c02c842c080f108031890b04020100b1603145031510f40d00003240100069040c00304045688600c0030b070032040300c2c80f03280300d048003030ba1090b10f00f1403914221080d80e00d40005002482c2d400c24004a409040d0902c5c525000300c58407901c01c110307401412004000f40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 719601960 1250 719600710 719600723
    0xe180c07240b09252f03091c030f270e060f040b03060417040b072103180204020c120d0501030c050d080a030c0e18070807030204030506010e062b020a05010c150507030605030712 78
    0x12230000c83e01c41c1040660400103070019040041086507940902007a00b8642091440c0b0394920642140d110600030043c0c10984010b001c1c07e0500c806414640301150841c0301c2207505220401440b800310342d45000050002c4c1440c456100303400d502c0c5507110700300d401804842a4003a620122414000c1d03c2d403000700d94000c41d151200c225203d600c0d01c07911410b01034130070400822800013480d808000c003030b40200d0031030681c9000c1c4480505404402e81c0c02400f0906d070301c0402150ba5890344c04d21a07024199503100c1c0c4e028040b1400c020f030008142c2c004a806403140d5080c001030003104010100c40e00c05401d02c3e40e0340c2100ca03a0402c4045040d11403646403164410b5903580701c141d030b60039404801740d004a200c0100103502580041c401c10104505030707540070b60041d0420068132011504e4070440b881045134644200c029210400940c101100d911014108c28240380e01690015964000c0d03800b40160603003140360356080819140f620a801440042070000e0445d95425250342d0a000084890601211034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 719603210 1250 719601960 719601979
    0x6010902030f15030309061803100212130f020a1707150e060f12010b03010905010605070b1302030c041a010e180c07240b09252f0309 59
    0x22005402128403a000841c114455501c80c01c6500441c10181061503a15002c10f102005007034030760070042c0481c001c0c05208440154100010715090240c00c01160302a00d00411064800100f400d62094110040000c01d02581501d4101082001e00c10b10f8000e511500846001030760542440340035544409003010754100c07075a240441c1280e0b0000710012001300e480d140f0807004602c4c00c1c80203006190070120500c0c0c9021070b2105180d8144409070000300c1c01c800048014481c1002070301c16140900602d0078910b26003419034807604140c02008040d1400020058034003004c6450500000c802240b0141c01030104464a8061440b0845000314090025003024803007050b47c0380c00c0da010014070030800480169910390411350a11644115015524041400380d00403503d490b42c24081c280012401002071103010350030400036240c2015210600051014a8054070101a6507400b44207015900f0100c1000a003683e02d4080c0d980207040d0000605000c201c4240d0341c80b03012009000c0e0f1002158030300345 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 719604316 1106 719603210 719603219
    0x604020a051b0106031202070b12090f060412020d09151103160b010302011209050606040c02010b040e0618160e04020d020613030308010b04120f080c0a050309030601 73
    0x4461390740f8182001400030500c0c10403a0310b6818405040340341d00d0030445c80241d00900f41a40340e842840000b0401404042000c000440c003100c09076007103840c1a050086085195400c030402500588410f4441c0c00d03c030b100c090381030f10504602101d5411025038110340c00d020300f4240741c11a2204006801e00d4480d6200c3d60180e40f171141c6e5400c040c0350306600c00101903090207041094401e0070201c200c0300141d800b143d2168407036002d6400141940400c00220301501c09845020342051034042d1941882401060441c840e0040314440c00b8510310300c6080590b65178200c030203100b002d09050300c00d0040310080d0805540080c0000c1581d0010910b5400090031a4004d005804490022690410401d50425201401047c00b00100c40c141803a00e42d03c1c3c1204283e03400000d00d68054038140b0410407071144140e0303640302f4020040b2140200d4500e0010350700c1c0e020074010361103071241c9800007c = true := by decide +kernel

theorem cover : BRFrame.Cov 719424460 719604316 := by
  have h0 := BRFrame.cov_init 719424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 719424460 ≤ n) (h2 : n < 719604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
