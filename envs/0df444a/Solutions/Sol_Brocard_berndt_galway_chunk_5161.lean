-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5161
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:56:52.465381+00:00
-- url     : https://prove2.me/submissions/b9429e6f-dc52-485e-949a-fa5ba36a36c5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 928057553 ≤ n < 928237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 928058803 1250 928057553 928057573
    0x30b0d03140f041d04051207240b0a06020c04180c0e090f0105070c14030711010f050708130e0c0316050f0c010c08010501120204051e0a03021e090106050c 68
    0x3070300050000302688520441c505540c0f550440c00036400b1100181e0307a404640280f208002d810008603502e0b08801e18103030309295141d00c80741d8130f10b210910f8040340d483c02101c1d0307014500300d0790707000c0d607080c80d401402030306002d0329001c000b50b0b0394001c0d0103458050343c07031304c0109005445813101c0c000a959011600d0040d40e420200c02d9000f8150290040407640300e01d45104003640c50a000d064414a4a0350381c0c0141c510441c203004001c0701c031140800078540c02c20040302001c5801c428540c01c143c83e003824800e0100c00305103411200be10580c48041d00e2410041401e0380e02030789038200c0c02c040b0745550025080546a001380c0200302d21040d07801810403500d5140c4041000d0045000e44a0310204280b541c0c01c0c40355210440307081d100c0b020000c00010300080018001e80da0080d04c28446c0d0b0030000000c5050608041c00301c0c2e1080b0003034001d080060800445209140e8620041c0300185034081c1a0700c12980174030b200e000e0f080314141c41d820f105000718800494074500c40c02c140c0e07840021110081c081980 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 928060053 1250 928058803 928058837
    0x3050319030204120b0a14151905060403200102010c0912020406050604151d0d1707060213090b0d0f0b0921070302060109050f0c0c0705031c030b0d03 66
    0x48060100d81415000c0c080042c00c0404c03020102145402003e0b00742a03840c0014091046400340390300303451100c00f80703801d00c050308403001810301240c1401c0c0c44600c00e2071422505440c0d0a600c0340d000c581e00c40e200050110070000e04000e0390310124201821001c000200300016826210414844c00006000d114100510414000208a81800035000081e20381d03c0b14003203059039016401c4094413900b05100c0c907120750f0b4445007041400d00911241c0c045214401c00080c203005042c5800707007249416000c00e08814002c1011200142e5008404654900900c0c2001c0d481c0310b03441c45070700070305131504107000003504108140005283c4c1c8001d0b064030b41e456507036400c003168201070300e004960300c00c0320100c0b1a100c1c0c55801200b4595844e00b402921640a85402441e0040580045010505040c2407142c0301c80188003840e0045040001075444070010b0034942c0c500500d552000e5030600c5250001c0104c54989664203484400c50354040c005c001005003405500100e20600400080405400c00000e82c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 928061303 1250 928060053 928060087
    0xb03040813030602070b271c030e100e07090c0206070516020301050703150b130504110c0109080d05010b03090a020f010e0901170f07030519110d1b05030106030503 72
    0xd040e144040d01c45607100e0700c0d401c040385c104110441d407006070041070042d0340f02202d6075070142c47e404410854144207800c0200b52902100080042e03006800e105070703001140650094409a0b0100c2c08a403000200781c00608080c14a0091844d1140502d0030042103400b20340c0102c56840d085a0024011a04e801408031241d174031050140b81400c1070100c0043c01a81c00707000d003074041c40c140d03030700480c281d07140310f20300000c0003559403001603052010015071200346185100442125000c480002d01040c41901640542c0b041d01e902c00519403801440c6001c001500c4084c01140070800020407003680c070340741c1c1041d04e032101740c9003444503a1107644c9101c010f180c481c02c501d00e03007001890000b030480b5144020502d100f8081c0c124a21041040624186402d410082d0050002c81e610007048441d02c0d540742d943c1c44a01540c012810071040241c92420310003050300d941d8005101074940340460304c09003800310845035504904200b00c00001c20000b214a01402400140c1c0e0700030000c2c43c6032502c650343e909400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 928062553 1250 928061303 928061317
    0x203041a090d0b09120702031b06090603010603061d15090a021c0e010c02061b1e07051b04060518040c0b0c0a030f05030c1917150306100b030408 64
    0x103031200700000720403600c03003045903840c00d480b5800c80c101c0340c02d2810b0034604100d401c0e80c240004810501001000da80c1c00a00320210464450f07080034258041008100c40d80700f0001a603400c08400000000c6059060b070140017110190f0070740c0441c500580c1c0038003d074488155900820000030401003d4245814040c03d0340140410030018900042013500005c03441d0f0503004140c1c243d5581c0d02c200501c034020f0046445202d070702e1001c0c04540c85c1150b807042001840c4500c0100b40940424500d11381d4041644e50107082c02282012521014545002655890301411807041200107204030000e90a00b4000c0a081c0c40000b0b0610107407040060009040b1071000784241e400c0c80119500068503104140207003038506510024002c3c0c3c030748a08018090310802030311070003000010003c10101d841d140054511011001c030300100850010035044404808154984115070006424081d190414141c1700c490781c00305509a680316521740d825601e440c501d601c1039044807501000084c0000e20014002e1483e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 928063803 1250 928062553 928062599
    0x705120a0c0c06330b120405010b0402030114190e13030e0a120209070906090501050a02031201170c040614040504260d050112151e09120905010807020304 68
    0x62051140c0b100c0040c2c1e4a1120700b001d01c9a1008013184581186605064820120100740c5400d036240110070401441060900790340910b03800301080030018290000603800f40020400c1d034403940c4031365011568440700480c04d8803810070f403a004100300385400800411030758000c40e08000c958403800d031500000b928070800c0301000031070503601c0344e0b80c0d132640580d00207040b00860000d01c038840c5105000c1850740180c038850a0010380c07001004035a500c841c50005441084c0391407520307800d018800303920310b020b54003c216403114120004501c004548070712404009c00b0b1001c4603c901034081c140000c0341d0381c0b8000c00301d00c0c0d41c1d1100072404606045d04000d800074460541080c2c0f031811200e403008803c2c51414006850500000c0280d946034442c000c043c09001124004161070300c50783d030384030a480c0300c00b80302d800420b490f041078186042d0010160b001403051480c040c400782603145043d0250044040c000710102c1c0780640003140d154840c02020b4490b0120341c0003945400d043c01c51102e07a000c0400300c1800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 928065053 1250 928063803 928063817
    0xf0e010518090112050c0d0506011e090e062502031e0c030304030807120506131d0d0201090b0718090923010b0907050c030f091201230705120a0c 64
    0x15600d440d25400d000b013a030a60440e00081c0c031484d00e14240400c882d441c610410782d44448401240740401c26034110b1b1804400c1403d400d0358902518100b4200345d20281d0132500c1c11001416410000c07074500d200d03134941c0c42c0108104002a0701410726403616480080180d005000c14182000355002c0024005074014206040c01d61035000b05144d0380c41150b08400050560702880340072178011004183c121542d0401740003500d050400318441806d000180b0309041e444100140600c081d50300c000000b11504004c1c0c03440301c0f03104600640688901c44c4115000010340c40024102885002e6071426125007078082d04415140c0190100030307040065003a91100300d42811902044000c2070702000918240001060040c00e440c02c0143c080e074001c0251051060801503070325a00404801c40300e0720b05000c858142c44a5038100420a181846076a510081d0310700307079681c047c003400454040450151791203a80810b0340c85000803030322809100700b0059424405004294582040d41080c0c18110b45450081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 928066303 1250 928065053 928065097
    0x1f0302030a0b03070807170114150a05271b0304080f0c031305030c01020c010f03230a06030c0605090102071202040f1104142d010207080703110f010f0e0105 69
    0x213401c289140e404040c0e1680219070801841840c40c00c44881800031800810013900da0311035004489030000c284902040f01c21120010b280e803115030050180002030804080c80c220350380412088544014006c6585a4900020b440c2001c65080c181402141010030b50641e15590b481030201d40060007002d6407080d05100721840400c0030806055001000e40c00900c2c02e518207418507044c00c4946032002d045400440041c0c0150760041ca01c0070005070b8500c3d001848c40304540000400011082240d41101c00b1007060080090240e0414002c0d030f0b001e01400b1144580d03c4000307442c903103d50110140540c21841e010441658400c00440045c2e0000d8008a0760480c840d202208860b01030f1040340e03030b1010100f81030148400104580b01300c00310a4529030031110130910703c406000c00151801440e0001500f0416099101303001440042074000204c03400300d03442c2c0c585110b58051100e0104c2c00b40c0702070407040c0050341c410803440c82e00c103007e0340350f4813516150380300111b0b102d6004840c0248804c0f4410101 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 928067553 1250 928066303 928066309
    0xc2d1b06050c0a0306050607020d02131e090c170c190803131404110f090307030812040201080709030b0415110d091a010e0117011107061a1f0302030a0b 67
    0x2841012110140b81e603503040740308007404886aa400141c05904244008401a20394401c0c0c2e42140c0c0e0125017003010702004c01d031118007900d5404e01c0a030140000c54600c440b292103c0d0071504840b403280345205d4a41da21050188000c40c80011564081d41c0050041305090404c1d90b185c8001d14211011101c2c0e40c0d032260300d100e00c1d5070700072200175540c0100f403a0204030300052502d50070900380c001c40c2c091080300d0300d1080c8508940502880c81e00000360003da80b1104e5502080500010f6a00c210150384920001580c50307980e210860b400e82c0403034101c000082c180e40c0b0600c1d9900035030381e12403403440f910749854681109200030640d03096006c0e652645070b110f0414100000d0281105e28030341c041032000c174034505114185035104041049480000c01408403440c1c01031f20606580c0c6000700d8608203c54145100e0260000b0250308401040021b88041031064540125019800005400b40065141002c0c403500c2d41c5080100c0301c0c081500081c03201c803103110350003d42d0802c007100d4012a0b080c22071000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 928068803 1250 928067553 928067561
    0x4150b060d09030e0102061b0901320c060c030c0a030906090b0c0a0306080a03020c060a022a010e030a230703060c0201140c09060708070f150c2d1b06 66
    0x3043c0d0100d01a03030241d605030b40e410407906920290107000020303112002c25881c1090301804440c241408541799110009241c0d1200d800c0c0f40c1200b84481c81d20000c0282101d80c465400291003c00c9170051200050f0828800c03000c0320300030014241a24a07194452008800078011000c0072540c05031038141d00320100d0111380c075031402a5088566540e40301c03402200076080341c406601240454209030202400301c0d8012480c91410310041d1880e945d101d07210031040b0305200403411038008500900700d0128003040640408400d0a000ba01e0742c81502c12a4010180d44507404070008103d01480280d0503c3c10041141185002860004681007030b41c82c0d548000642e60080700a00c0140c0d518081d0041d141210b0003410340200503c4030062610011001040d81e601c0790583c09440741d440019400c01b0021158042c0320a1904401071070f80090620801002400e811901200060341900b002d07205440748140001c4101d5146034200511481540d0949100c80c0c4050412540c01104044030301041031805 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 928070053 1250 928068803 928068821
    0x30a05100b030f070618080709021b0102030f0a0b03010b060c06070239011202120910020c07050907031b020f16180e0f03160c080604150b060d 63
    0x9400c240a6600e1400c048407500560240700382c1c8218003e07490380c10080b400702c0590300145040071107000c0c850340c08002180300e0703442a00c2610400c2c40c0007403500001c4e400707000c946194504c1c5415000000e016035080c0d02050b10051b084000da6000700302c0420465102e060f031110007400104900d00c0d00c0000a0490300300100303a440c0c5412410030000401e505000051801a4501c140100f1000503800c00086450201100207802001001d42c8101e84c040d41400030018803400c4290b51340c1c04003a4004403052015150303040c461181c050b4000e00c8001600035a090483c0000090100501d440108801100003520040526940d692005150001404841c010540e0754009103018442100d0261509200040100400441800602c480003581c0c1a0b00d0303464541d0031020131000c54021416003803400d05152504144000688004030090a50a002d04a0302850b0f041d100c4603030320180c0f95150a02154014888041c2c48250f84104c00c60b5800202e803013070b001e01241d00300450080301000f104c810003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 928071303 1250 928070053 928070063
    0x80a1a04060f050a060c120f020c120a0308010801050127060506030f04120e0112202b0204060e01260a06030b2a0a030207060f050702100902030318040b030a 69
    0xd505215504100c19044d00802c0c840c900940c1100c07894480c03402d00701d0088804000c0002c22040d4484c4140f082100311040b40001784440a5444d0b807a410075507441c079241085002c100c1c08400084d00402c184149812a410041d03009240c03004a0300301c46c0c03000c11030031a040065030f68810101d40764440f080694030840d00c2c400d8104150a050a048442d0020307003542030104041c00300d512000d6603000c0a0303d415041b41407004a14005444140e0301c9000002c0010300b2804c80104480b8100590401031001c095031040c240480000c48034004010b078440d600451020500b10214000c10f54811a0b10070f50800350110404001e2000d201181c01d010b5003500d40020075501c82600b481440000403140e0b803c1741c148090023908402030100301e622115089240c206100010561074800b80c081d40444000c241d00980c1088111084241b141c001d00040c1c0391000188a10400e001301004280324081d020780d00100114102220a20301c07201507020200d400c0c3d000b0f6101d41c04c0980b00d44017004902070003072280d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 928072553 1250 928071303 928071329
    0xc0109050c0108130809060307030902100f180b030c0c1f0b0f0f100e04090f050f0732040204090e0114090c012102040302120f0d050901080a1a0406 65
    0x140700014595440074260029600e640c1c20342c1e1001540400454100110a540e0035440e555492820f500170f065000c00030b07421810342d840e0540016030000490380d4000d11a20703103241c8081c5040d81c05d02165424003030460510b1041000c038400c0c2085401602d1b0398a00ca80442c0c2d1190480042880c01c0140101e20115443d1a00c1e41d40416140c41c07a14000000ca064036240080070fa0540019004520385101d8001d001130000c2c0f144a81d2295000390300c4617604102c59000019113450b0541d52001c444907500c0b0399009202c008240d040b070441a415120a000003010f150746108a9070301c540100408131a94007035420400000c06000d140524180d0344141000020344040011102155050061000905400c80405500355a03080f040810354040018005100c0d072101040e260000e01c0740d40c00c0690b002041c0011840324a40000f0b00780103100728402610161004000c0c180c85900070041c0d25400300705030000003a08070340c0725446601c0c020440e00e24203090003085c2d00031070110740d50ba40240d5000c0c150 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 928073803 1250 928072553 928072573
    0x150c060403020c12100905120c0a0c0b12010e0c0706051608010f0506180a0512060717040b010b091f0e01090509010f0b03100b030a0209011e080c07080c010905 70
    0x510003401c43d44816200c00e07009401246910b621461408001540c0b0b55440c192841071000c100006071106800b00d080c25070324840304251503951091304601300c0746c5000c05840899540c06880c1500d218680030030f800c6400340d00344521180001c100400d4044845024070042002c42c6160281500607141092a890030310151000101818016003007481c000b980c02c1c0e004c00181d1147c0c81241c81407181c09045502407280c0c4d900080b01d0303011a078049948203000d910103480c00c000114845004803581d4495185140c06414103400e40d47c41203802030001090303680100542980400200341805d4010b00c85041c080d2041c0410900011042514000401104441c900c03942c004046001404088038032202c04d6140c0b541001d0a50094042c01c0340410b07022010440030942600b09002802c0310240c0d858691a004424a0094202c241310760300042d2400440385401c0843c3c0c00106040003241d41c3c24510742c4d01d00b001d5000c00d511603441120480001c0042c181e00e840203102d651180c502c514003401d10126 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 928075053 1250 928073803 928073807
    0x111804080a020f0d05120609330307060201150f030503030f06040f050a230c041a0714241009020a120e0a0615121205071b090c020c1e150c060403 64
    0x1400500042c000c1340140180022104030444041c62841984a80c1d481e0f17014070031281030b40309c291401d00d5030140309860010900d19019001a42c41100d1005074042c5070b51340d0345a15402c1c840b03610010700150010400702d0b903500588220180c2c001d030086c1011548440c0640c1050403101c08a6003c24083d545a0120403040c40c1e4602e80d40c1c1c0c0799040310740d5420034184075801000e03e00c2a0f00c03d9911b41c8050100c4d40903085820025600f03515001110044000c1b00d6010b01c503168401c4800c2402000207044900400500700c2d540140074a2070304103600074280c188903c00f8025031043c03c0c09002d218150301c05c144440e40324098103003c240f01202a18140c159032600c58150b4505880c4540364090b0481c080c0300c030503103c850210303005400c03c41400440e200c040701a906841080d801070041e02420400342d18801d0f0030070b10038045641680080000ca03940510407605c82008201e1154000c203c4e100c05c030684031801c0102c0d5a0000010041442d4421a0345d1240701a80700b610810901c3e008041040309040d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 928076303 1250 928075053 928075087
    0x206070c050c09040215070b19091a06011b060902030f150f042405240f041e020a180501020115090518030412111804080a020f0d05 58
    0x52400d080054000d82180e8800d034865400c6022507020300c3e42d4030001400e543d24030501d0701c0b500310102034580da220710ba0b041a1100600481d9064500240390114490400017807052880b489c3d04010a101c042c045007844050050300544280d040080014802100181c2a0848040c0e241715180000b20307800d4501c10f00d03042c0001d020ba49900364000c0200720140080415220b81d00000c907403568911962203140c510440486403004460300c0020400c1a03455207400d520040c001c45017500c00355181c400344401641030001d400c0701c1a42180c503100c401022410650000c102c81828a4640181c58030940408000c98000115040002d10054a2101003084001c4068080c103020b10007030001046603140c00c0a08101803007141032107541c45000a5400020700c070044c2000c0541e0059990300d648d1443c0940b03056070560001e0781c034104261001d10551415140114250004001d0b0310b03ca41d0701d540301c842442d045a80f8009c258060840c0007400c40c6003d10442103460703020385440c0e07250404008041c0b030390707 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 928077553 1250 928076303 928076311
    0x21210050a02120105060a110102040f03051009033c020313090b03060105010509060c0610090c02010608190201050c0d230a02060a0e070f0e1618120606120c05010206 73
    0x740344100302000d03c038800403000138103440c025190f0a59a00d9480c1044500d0000b061000b121940b0104020a5914588424508aa00070000c81d081d803603c4034200d1003150900b50340240410141c1c801071084046410039110780c200d130000120203003801400d0154200c20f2220500c4d0050304001000d19a140b25002424060b002d00c1c0d004200705400000402d942c0d003018040e1a0500c000030884c10b205588202c121600800a8000d4071200c3c20003044610707101d035003400b03044000b0b0b00b0400000b092910503c00ca0741111410701c001c001203034086a07812100d901c0b041e800d9041041c100010300941d401004001084035055645000303020003002071500d5085101d001016010b01007150142c2175074006a1544c214180c0080080c0305403401034428500085e070380c42a00140250300f0300040f050411a00c15200d060300c001e5110034603158050480321003007240100d203210f0f03108c1601880324504580c0005070380e91049500058640d2241070034400a9400d071030071201400915001d02455905000ca2504 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 928078803 1250 928077553 928077571
    0x1a0f0f01050f280f0c03031a04021606051614070f05060702030c10050705070b250201091506061b080f0313030201060e0606160501180503031006050f1801020a02121005 74
    0xf40b0138804003c4c008a00c1100140030107132505040311000c0070b441c11402c026800207100b1551032042c4410f260040e00c2c011000e036000e43ca844d00040841200e061b404015000c5661001000100c0321110702d0244c00c915001c1e01e900d1550b01d900300001d00104015801076125800860b1035801911041e881d10540d004d94659490602c400e000c44c0b2900403055500715588051070000707995600c1d0180342078400305a1107141c040300e443c12000ea002c3d01035001210140c02441c0c0c0d1543c3c00d20140d20343d810340f080c6100b50b1000824100c0171001364251038141c1e001c1c0c04e114840340d82c80c202800403811503682041d650590300300340b02445401010b40910031100100340344130201c1c1d510720304400015420b0090b441c0c41c55220400149660402c50b0030b600c99900007201c0880c2e9180910513041c400d907250011204610034013668400420703070600420030fa410410998046d2442c2802ca64000c4d05d00203420596507066100784c401e071500503600c2841782000e101e942002420b65a00d0202c150042d40c1000c0c0180319 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 928080053 1250 928078803 928078817
    0xc0e06030a0c05010c050c04061202010e03061b03070c06090317090105010e0105040902040e0d03020702240901110f062a16020d1a04060209041a0f0f01050f28 70
    0x4001a100b091030030071503109091060380789206092440c141611074407030a51041c503001003c1101c400030110794803c00c1c000e0340d58608800043c4141540d5140680f0340445070503160000c06d4401ca0f50b42c1c01580e020001e468011240100d0755102d03c15940b01420440101d1000800300f554000d40045495225042100038045545001c40c81c680b070010600031103000b00d8030342e4015419510780d07402c03004208200804940304120b00740c600038025000040101c0c81503038180c000800490740b144000010901c0c0070b00652500240c04015240584a445200c2c114000d04908105e1010207004040c4901404c94130440c13000e620081c0c41515002402e051421070f0424030604002112842103400f8041d81504d8600d0ba901c054240001c541d10191242e540440e402d000300b008025190f009048030081c159418485241966800003219400420300c80e008141440c0d01c0070146400d8a4150650700c06040507450900304980c0315045502000908080c1034070551608800703013152034040c01b100718a1914035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 928081303 1250 928080053 928080073
    0x4170a0201030c030525181e0605030702060109021c050a0e07060c0309030b040c050603090703050c042d06050409050c030c01021f0b04061d06041d0304030b1b04030c0e0603 76
    0x4c84060340d8600c14121b664101e0301842c00b40980d0782d03801d440603410b44450000380c0c4c0d805140294400364420314040303c4202000210310380690300750303401400079030003601c8940c3c00d0869820080d08500405a5071040c1542e001060076400c0c801c2034000d0080314404902c22581c071001c1c17403400d00c05902603001c0000c800c134076401013a4031050000a590340f19140003210784035410045002c0c1080d8100552040002042c003182c00000aa8102201c0c480c00640340e148a59800b00002c40300382680390102c2c07600d03c00840200891a03c82a04601c012200005800b41c413000840e003100d080340c02c22103803a40300c0d6440c5011440c0c02c0100040c2c00034244010195280d0340030340864504044942e00300d03030176290005012141c0e9035400c03034009403c10a81e01a5510404540103007008010f07666030b40603510b04120000c2c0c9070b01400c4144a0503084100540c903152031540da1003030003800207005005a50403050b031039400f042258010701c02140150045007a81d8185101100c1170640500100e20960000e4040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 928082553 1250 928081303 928081321
    0x3030512101a030a0603060e070f150507080a090f0f1a04060f0807030b031221060a06050702032d0f030c100b011e120b06070c05060a0504170a0201030c0305 69
    0x282c0e41d1004401c111601c0c0d44610784400080c5c1001e400080074541000d48448014200041d0700049a400965584685946074400c0641481200040001034402c00408000c03d80d03030001450500e86925183c0c0c815075070384183d9048100181c01510351040f03050000c200542107914210500207482807444d207443d20300354014004910800020003800068000034042901070390006446500140548407a0511071003481c47c140d00a01102c840741ca245642004126910710b022440b61390041c00000c80181440415a00c03600b124204907410300c99580b80081c0c0c0344000050b00074031405604407040d814440029182012a0321006100550080c004070703484410000e00e01454220082002603000780c2000100d8450100102121820061501040344641e1004414584c1482c039402000000841d07020000369206500c00984005a10b0805000d03030f18240000f840d041009060241c40c0c90742e03409262141c001112454807503900006912815940c2500509440546601d001c10880c0360110710 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 928083803 1250 928082553 928082579
    0xb040c1817030f03040602211501030509010e010e0d1412150607051614030307080d181b0f0501080f16021006081b040905060a0b03070509010303051210 67
    0x295032031061528640c4800810610483e481c0101002856549140c00c1c00d002e400395101000da02440c6400400f600401804500918014401090390700c2d800340c0302800440107008050704581d1036542c2d800051800c0c240900c01c02e5140704a13480508030740440c810300504600c0d1a441350743d42c400010485c001030030381140c0c50f15600440480d05101105140d0003c10a84d004204000b030182c03054000514584a0202d11a0100d808681c689031100d04004140358a83c001c07100c0042c0418001c1c411501008400d030800030840c6c042400303201060035541c07195001c00454140300c6244100040d02401107028034101030001d000b0a082c41c4505e400c1100500102c0303000185554200740c0d03130745204240c1c10302c00e000303082c45c0c10381c004000e011040d00c17507003869220000b408059100b80400c421900308d60401d8000c0322030154000016002070f0b6624103031400508409008a030349401504e201080340d90701d0150036400b842c003036620319460700b010f01c0741413200d40c201504400c14a00c00001c20440c070b14400034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 928085053 1250 928083803 928083809
    0x3090807140a060f12090f0807080306040c0e13050402030f060c0d050f070906181715091203040b04031b080904051506040b1e0d0209190501090b090d050706030b040c18 74
    0x100020340b400781418110011541100300910b4000002707a031000f44100b04015601405045070100507080f400302c0306803111480510802e030481c080c1f0015544050840d4071165000f40080c068070f08107410506da15050410840b00ca94055130b0204030240b68800a11600b60b2003440c4041e00c040ea4103140d1005404101c0350302c0b40004004011004500709204040c4503801491010b0046120000c4090016144c0030340507036860081402c140058041400050502e0100020b50340c518595110358036900c0316408024015028030190013503e000a11203000820b045c070303000e0451076882e6031510702040107071032010b084403c0d5540c0c55007240315560344490440d021150741d917510035501e00c1b000f402d01e410942050320344000c5080104200468049030f0b001808112000c45c0d4510700d10400c408a1102038101d401100d00168441e1014040c9107807a100906e144000100300c0c0c800417444e0b0340c583c0c2c54104a6040350000035101d4a05d0461030405005085001002e13082c07020720b1a210070a84100701900e84 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 928086303 1250 928085053 928085087
    0x110c0d050109050d030c050d023603010b010e0a03080927040309053001150b030103020f0603010b0313110d05160f0b1206010314070c0308280903090807140a060f 71
    0x1048c081881240b5001d82c0d0f101c0c8000406816520ad05c1071008a050400f82c8883c001d50a00742400000c0d8858100c680e40c500b8001d0942c0c3e40b95003180c0752054a0b4100f220425002038054200c080546c0421080340c5c2041d560140030344892810380b800419126080d403146006051003c203032882012400003050480780300e030428060303505900c0b4030300380501034411050354118002c4e800842c1c0d0a82c4000154180ca0080c0e40c0b0f00703012950f01c400c0c80454071091245560300f507801d10200e0101d034218401441a1401040020407400010300002c8000c618010219000c0c1c0c8071916644000300200700c2c03c002000d0300b80200d185240ba0261411080c0b00d60504580c55000040001c1c1160b8020391000b13055899a4100c6041c5180219000c5c0c103401510806034040781034030f400140c1c4103856080c0100103d446c8441c2c0c92241d1800e01c242030281c08100b604409000d062003021070000820421000140019944c0d11340568495045c81400d1805400c86010840751583c420920750700020024240c19100b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 928087553 1250 928086303 928086307
    0x101509050c031f0f080f0f06040305040312180909020f030105160311161b122f03030a0c0b0a050708041b0f06050307180303020d110c0d050109050d030c050d02 70
    0x5800c10400c030122078000c4500035104c44008503000e01c0015130305e00c0746104141101c15000100803041d0f82c9081c102c4000300010000c10003440022010180a000441c03a401c1c101040c49a42c05031144800e03654100c0c450555403241c0240561408101c070054a800940007000700d406c00c043c040c8890f00d1035006800a150315171750b0940768045413800b2540943d418000d416204c003018078151a650407802c0d040886000e0b42d2001244426000c40c66000c2181d000100f903801048103110218801c181c90500201e6031101016a1300710f0710148001d00791254280d0350745001c52154905141d00e110098084000e1074541010090b86a801014241d005074112546000305000316000042098a580002c840b0440d00080012000e4105000c4d5002d80095142c0383c244480d280325030110501140300c082c006078095074922041c540101c7c0f541006a204030199a1084928404141060118102201c8a81d51615018103116048c4032201d01d1103501d01d400d001486226074014414012135444008850340 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 928088803 1250 928087553 928087591
    0xd0905090114010e0d030306050a24121d0304150c05030a0302250c0512031321021513120b150d0f1a010602070f031203020c101509050c03 61
    0x20306803102e403114001744040c24a050500e4000c0180841d80f00c1e803401071610076008a030304202e50109601e0420030b8180c0d6144940c400c1421159640d00c2060031000035520038040d001070064103045109041e0300002155030340e180036005080c100c11123403481c0800441d24004000240c0c0403088400c08001841d0143c1c542c0068113035610312056409124a1001032078804600300101da1541008442e0203d6120250300600d54503591a44140c044806000401c500300780b28040784640505010940301650002400b11580800c40103070464001c0d8403640000700d05056032080030340a00c8040c20701510258400740f11aa15440a8040039240f896030440026240c1111b40300d02c104000d01903040041d480d100b0741c076400e10b83e01c007882c0440000004180d000003c501035000280e0308003160440002c40340d0380740c40c0d80c17a08940011031403229001c0640801c0040b400510800c040681150111000103005000c0d51045090403c1e40e40080040c9040600300085881841e0036260b00500b4440741101d2010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 928090053 1250 928088803 928088807
    0xa11040b0919030b0906060909060703090c0f080615030730080a0e0118050a050d051e030418050f01050f0415080d031401081c030f020304030c02030d090509011401 72
    0x401000d03003031000c0c0e00c2e900c0004207012401c009203000d42c000400750b070401d0f05c6d82030500c240e0354001c5074207078042d520401c041070f20b5612a511040c880d5008034542c01086840f00550300300c0e580d00394860320075540135000340400e10710401444403080f402100103240c45807510f40c1c1d18032002a4885594200103104545602d00f560803482e452055034041c103116a13910a80300041c00090b21403200c50300260307680203502000c03040c0d460403106803400140b101502c2864542008500000044100e03414040c80380b25119004607543c040c4c601d0310085001c2c40c2c0300c505150b4000c2c1810004024034070002e081c5810700c150700055090b010f040d01c806481c80541c0a0024011902801020784c40403001880764a0008140714081910b2101004a40e418016058042c503080e55502081c042c41d041e40e0441e0b0a001400a006000c23480000700c40d00300820920075070902e502c100e030012070341580802d40e549003203400c6280602c813600c02046903050801003a41000d0100d05041814081d1045100755020f00719040e078 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 928091303 1250 928090053 928090069
    0x3060606043821150306010b1e12010302131103010608062e23090d0203150c030a0615080c09040b0d23070612050622090b0a11040b09 59
    0x10416014160307240003034a012143c0300d9010310490351102c620303c003090003070010481041d100310004000b8010780e4217181140681754040100d044a400c40e0750b2018080014801c05003500305c0c13410b000401d040d851401400006405c50380200381162801d14a10b1038000c041d001c1e2419100342c3d180c540030f19510003000c9010201e68144004403d1103581c1130415083c5081403060110350705170740d0031483d407100c0072019400390320007611422914014400388201c1e092a600e40f080c42400181165400d02c0c40040081c142d0b10300741c43c030640088000003004001d481c04d0080350020a02c0c1c0c280da418011080400410a00002d0528601583c0002d084620750b0341e585c10109001c00c00800c0400880c4051401098001c0010790f040004400314082180d00c040c08603007007080358a16110000114840620743c8010840100401e510082100e05610a0821a140380c595001c1c0c0c1c01780000c91a0040c1400484c1402c018400c011490812420040f068907103802e68044880404e155510b40781d000c8000381c026 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 928092553 1250 928091303 928091399
    0x311030f06040b152d10020102091f17100303021e0d08041b1205010609020c06130609200a0e06060702011419050711061201030221030a020703020306060604 69
    0x1c1c0e40c4540078041c0c0c28007102c1c4101720140c0110f40ca607140d03502c00b82040e402d0b40581c0342d20503400200300600161440040b004c070300607800145496111001d0031080c0c043e0868050341c80c2d080e5011880002e00c10190100142080b010061103c803034a00c00c0c0403800ca685030001c400143c10000303d1004102081030100c88a44a6014070700300f6075a69480301202c00048521200c21707a4190300701400040c5206851084540700010000980701a584411151340740b1916104112811a5102d09080110344401808144d50344c07111540880780440350304000749015190081840300c00d0a01c284100c030364444044402071035080c01d2001121510705d60301e44140c042c802e4803000c0d6101540c802481164820000c000183c0b0441c01e000f68841a401402407a014084040d031035052a2001400503150080c80307018030041407001b880c0c04403584624a03003150420501000560301102c01401140340900c580c5510107010750b07000e810f0a1030401c01484410072050490903e0340015201145032860302142c06403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 928093803 1250 928092553 928092589
    0x905120c0115050a061428030605131e09061b0203090a1401122d020913140a0b19030b01030c0905041203051f0311030f06040b15 57
    0x210030200388103901078200822030369000030b0b540c440400d65103031400c0710742d00381d03025a920040c20024011040e201940110072000d55005a40004080406840f85810445a00395004035210b40741005001000c0c5c807541d038800055040c07894501004000201c0c02c4090003048001103002e08160400b04002e001c0034010090b8102d0b521007a401107500000101003561040d5000d40c004ca0f0703202803410709001c003400d95500040560785100710001464024420000840d0000f4003004140c1c11000a13501c5001d400c00f0226801090b00f1a49151904805001c3c00204506100540c010050221025001031245a00300da0307950908081340c45040c0f13050819100c4c1d508030136106443c0e09101c0e10800091000300c60684510b0780210724500345000d818001e66201c800d00b40d480000c1c00301580130301402458032051250403070540100d4400120402c004500856410105400250605041850f401000c1d6030560043c400d010008031003180c1c3c40c0e40498100a018134209501000909580c90148805a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 928095053 1250 928093803 928093807
    0x503030309030a0e010507120c08250c290d090209010305012f1b030f040603020706050619140310020a0206090105091903081b07080406081509010603090512 69
    0x941e032900100401095119464070401070b0305500044500b44034000009000310720801c0c17008001802012500c00152007590700301d0402d2154408070045401b000c10302120248400e01d51300911040d1250340001d071110340d401350301d00a02000040202d00c6081d219004034040040e801c4019400c41c0e010740a0b09034000c04007282941d6900b0303c54040d0044aa80315500502503006000f8841804945d00c4c0080103180902d0401c0400b0b0070113500c4240c44503031060940420008144200c0450004102800b4a500e0050b01c0b01282e04149040721001001580101d512440c84040c0300103d0701c91804079000300390460002c1032084003107818001c4009910642c0c900205450780d45a801140c01c0b44210040030080090b40e6407045039039036811030804004116040a000400481e21034054180d010f0b280d10810610500030903640c007607685c040724050350540d01c0420103000240d404202150401001400e0410742c000400010342c40345070611510701070503a40d080300010001c0030700c1807080d070f8050701d0320707240e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 928096303 1250 928095053 928095061
    0x204020406210c080c07020102100518100e21090a23040606120903031113081504050c0d1104050103050d0e15031810020309030d0c030b030606100905030303 69
    0x500b80345000e0741803120124251460031210000b5120f00403100015a407a0000d03500d802031003070300e6640180742c140d0441c001d080c1c1410107070285005040c01140951014402c0d0716246c3d000a06109190162120076800c0c803a0030303c500c040014027440800d0780c6005143c0301c48001240490a40b24a4603c55002006560002058903605e048280840100082400755943d603200f000200c0e9003a028110205a010840b205003075410f0703000d40c98840c030a040c0000c00e2150055002210b4211400c0c010601c2c41200c811301c109402441801d005c24807078409007016040a030303502d07a25001540f4215000b061000660414070007400103d1ba0b40c150041c1c410010380d61a82401921181e82d41102804510105000386050030041110b009440704400001e00319101d04080480034561252112411711031904100007031882d80c8001d40c001c10441000750380d40c490441c01401602e075200c200344107041ca8415050200e481c0070410944c000b0702110810080c1004003002da032640361503000b940e09440040300b04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 928097553 1250 928096303 928096307
    0x15170c0304020a09020a080411060708040b030601200a0f0312090507170705010806041a1e19180510080106090501051c050a0f03020114090c090f070215060d0204020406 74
    0x65008070b00945250100d2501c0740000302c01d07031040484500004a102000902064000000c10b094101c001e11451410300240c544140c1c0d90084e4020a104c2c5a0000c00e2000a40e0080b0301b241140c99074200003c0c521144d2443c0544500740c03000c018040d800020120070401d882031200b40c0a002c1d041c41c0401c17055100341840c5a49650500800e45800b00245801c0001d035400580c84040301c40582d0358992176500c403814440544426080b01650200d8010001101e0f51a607490300000300f01d50400d07040701c5c2d02001c10040384428041104503d81c4120405010316400c80c1d110314410103481c0004105901c400c0711207150300e503c56201301d10303035464aa4042506507080d000345040360000c5031a0b4040e0b82d448020b50100000c2400d00415903070010880c0000640f28102220075140203000000311200703244504010014100c03000111074101d445c03844624030784484010b80042d00c03204407424a10700420003968403030262640071032500a44c030004101b507a40508042480d90f01130029903c8035a10280 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 928098803 1250 928097553 928097557
    0xf051b030c0607021b0d060b04020f25080708070c17010f0f0e1f091e0501180b130507030204020a090623040303140c011a041d0715170c 60
    0x2000d0003a9000f04111510006601d40c500c00304003094031401103050200b28000c003140d0001c582068450620160641d500c1c0301604880310b00440b4a5694881c070051009880030f00007015408010103054140414070440c140c5401c0f680c80320080d43d03203103060700702132144888a50103304400030301c0098070050001074100210b006003a40003444103040310020001610804c045103007060f48030044212848100c3d410f6051214203607500003501c031565407103007011480307124134201c8484410388504003008424801c80500a85c06545008043c3d12030355841e14051014200d134000002a270006400d0007002d01c280d10046074020000c564a0314215405001e000ea140710b401c3c08500c03a500c417207801021501091008090030500741d49410b003556021b03680d5001d0840c0d1210404814090034458800c00d11416200355020311582c4445030040c41080305880103440e00441048025840e83c0323580000280542c103490030031007603030990701420008494a01a10303030084032802503841808060341c62a00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 928100053 1250 928098803 928098817
    0x1050c0c0106140303090405041506064d01060b030f0402150307170a1e0605030c0d110d060e071410090b09040906180503031e0108030301060f051b03 66
    0x1009215160fa55a40c2c0c1c900f01d0103400025401d034008000001c000d10f850303802154403511800d2510b40500aa9054104644d071075045000807805a81340c0c00942c802d9160200d5900043c034001354071403040100b164520301001022001260116203401001e802c00f90003c40c050280001c4068a078074110001c4600d1010568060b80200b440608004080184504584c0302d003005843c1e044020304030480303800d00080300904100449540744911044c81113040800c0b54000c40400020480317900704410141401c1d59800202d1160110342840000159211120128000c046600608e249100c2c20018090100e103041c0301c4450007005008600d5900c1c05020109100040d98201440300e855042a074054106006204580e0010702070f032841490142c200140c0c1c01d11400b000700e6144100060740c40001c1c2007040454641d0408402c1040e19400013500b84120300801d50414015403401420315121311044c010042001554003180301032030b0140d42110300c2100035034031005071007010070596600d03900600 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 928101303 1250 928100053 928100077
    0x1107151d090402011d010e0a0312090e01120605090102130e100e040803010e180708071712160602160f0203010f09021f090305030a0e030f07080606060d0e01050c 71
    0x4224000c03401c281001c68400d83e41038607860049201d103980c00c0c4034070703001c60074a504201c080303568021992030703880612004511410080312041e4681502801c4400c1a03000800d0f90348104004110810343e4190302c1050f06d800c20f100140b5a15543e04050192003000c0c9420440210318800044807031000049901c070f58804000200b805031264491101c003042950017401600303080c0010301900c005244110303041203d0404040180507561300351420f00a25a02200c895048280c00300058114044900a0b4038023400140a0b001049120312207c1d0195a201c00b840c0c1101003c241c04001e26941146e89c143d4010350030401c01e04140ca0000316041141104134025424000380360000d040600954410960040074600030703120100b24520406001d24003003040045504000021135010320003000004290b90f6600406040181418901102c6c100c1c1404142c0c050002003104000100b200741d007080e401c036101c982e80c5031041d5107036020f030526620641a0354038100c14404210030b04e50040c40ca4450340 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 928102553 1250 928101303 928101347
    0xd1503111002030301030b0c0f2b1d072105030d0522050601180b04230c0a1b02060903060f0a110f040e040201030e120301030b010f080d110715 63
    0x407a030202c0e20b80c002840000c0045800d00c01250b5840d06400180100d070311100b00321402c24045420307002c00041c520303106000310010481203510004c0d480c0601b0f6a81c0315025a8010680080c90001c2e99903d040d204950240c1ca01c4041c0300c5000301a040f0441000350408110b0b51101c058054060003460251003214031815030139161010040290700d01c914a83d013000250001e070386422480c054060340f05100000c903664441a4a0146d911881800e242c03070080448031078404104601100c40820251208a11610502403562243d40c8110b422003803034501c0d041003058000e6480422501d00612401540c18000c00080002c0340b00504181c510804000409101040e440b140002c001d124480d0b200913640310070001444040004244160018410300d40003800301136540016003030403600350328010079079000401001806442c10055001d0f0034084000c1401510b0016001d6031106011800c1c0c2c103205440307519401042c81800540020001d4400715a9214180500102060b00b103646820b028030503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 928103803 1250 928102553 928102579
    0x2715020129010509040b032401031106090a031407030b0a0b0306070302090a031e050601030f060c0314010521032d04050f010503090703021c02040506040902010807050d150311 77
    0x84040140e08210182c6030320b131600095400b404041e0110640c0d180c0c141c440c8220508284406859401140c540040c0b04c1313036154110f15003841c582c0741ca01c0301148a40401c5c03041ca083c40d81c44071b820b4001c0380c0d07002c02d1045041a80088060424210340d0001d000c41c080803080104182e40b603001301d645c0b6082102544d00a075504503080d0200c1c081e6081042d041480e42c0010320015006061554480441c03903040203004d8510740d1000d00d00b07d000d81040b100d02210714815010404c4601646044610782e040901ca0100340c1056040c841d6014440c00c0d21800a941c4014108147e41440e2a01c0b03962042c02eaaa85007001f4461080c5d4115890020700c10496480a0016441c44601501c080e260014040c220b4030424000440c0e45800103000303000540600600000141d0715450b941490a000c8c0814805000090041204a45c8002c1a940c00f8904214850300141c0c0e000d06079603481500c42c10010744500200c80304400400b85010740d0021511f40340004020701c06644014884010200d4a8101c2408 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 928105053 1250 928103803 928103861
    0x100c03050f0412050a020712080406021203040f08070f0f110310050f01060c080d0c020718051509190e0c1002070f0515071a01030c0501020a020127150201 68
    0x40854000c3c01c050084156411a14420b00c002c10b03c50300346204032200c0a4507810001c0111580d480116007401001800300300042d018800e51220845003502c090030351809880c0c1c440340383d6141038000c1509030300291010800000c42d07500000c10b904640c0451840300f9a00c1c20500130080800280c4c4a03109654540744628024083d0030b208102d011082c1003140d19041098803100c094a0f01124090024816600c240d0007920cc1d50540300010303070042c4447c51400880440981544554503c850300b4082001282500b00a030710a507ca0309550b0b0000fa9070320021001c1c0c070244400c4408030240d080c5205c0401c1080c00203140c800b82002240d9044200950100c140e82e1910103115905005040e82d80411080c0b8000088151004102120303178074080041e079522101e007000101d41c3c0c2e0224420710040c0300b480030840681015140138001404680300a400103400810091801010031913031389204612000e4a40c101c10083c120000d1410401514001c064068034103061100011104200d045424803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 928106303 1250 928105053 928105081
    0x6020c0c0301111611030c12010b09160e010e0103061a2a0604150609020f0309070816050d020f04020c1b09070f050d1515020601050411030f0a0e100c0305 68
    0x2e98690808030b60700c205070381c44405c03600840400740d5240c000e402c1c1801c0340740c8480d904040c601610a00008496482c1401c1164403000a090710000041c010f801c4905e8541050000382101c0c0b090803d05000c56800c1e00403005060550040126117070b90b80c0c2c146034118904005007841c2640c0e8400c0c01c48000d000c4400840c000c041042000c0c40d41d001c1c0c000f20b00800c0c00c00d40c05801c101030140d008501152a0025101661b02c10403408010301400400c024030352030244410006800d14002800c131250a110b41180f400301140980c078880c604e203040e1107085507038003407802c84260030141c000e41d00c400f02c07101442c0d05c0c0c0c1d42152a10300210743d00a4124840d00d0001d071080d1213200940c40303145800b11000d00803180ba2304081c010100d82036895101c8814000032110800041a0100342800d04d8042004001d0401c40103900c454025030a1028480041c44c104c1e0a40b0b03401910f00c1c1d2250800e90383c4510b00006010004e2124200d4002d070070801c001181e242d006030704a15010344061007035032a132501c0d5940034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 928107553 1250 928106303 928106317
    0x110901091707090e15010911120c0c0604030c050c090c0901030b06090a1217030c0313030309020a0305030910031109012102030109090b0f0f0c0306041104090e01180512030a060306020c0c030111 85
    0x100c0c60812800514040c0c9c50400d0f07404c072443e01102420180600000c80c0380071416181540454403c891030410010204000344241c8425150b01945007000c00a42c0c4d0f0a0040b072a44505054440c070941141d51224029104205402010005442e079920080340c140c400d20101681e40b0000c072582840503002e104220390240e4072900e0321a20710765590880007062140c0c071000310205034940c0502c90250755001c19441c050750144018603511b65240040100207007808515109045c1082a504202c0d00145c0c10380b102c50038282491070a203049580407444140d8400b003c4480303107101000104444149a2014018521a0030800c150342c0300d010050110103011680d98007140040c00000d4000c802400141d90050b1000d030010401103032402c10742040390099044484200d50309e05506003201d00900920342c1d402e1101203c0310320300c40745d52503040d166060030450354600c0710f00102090852120782e10680007907400c800e0454840b1030601203152910b0041c003440f4469802c140003070b580211044102d41d03003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 928108803 1250 928107553 928107581
    0x20c010c03170c0702101d0406060c151514010905010c0b071d0a03060b09150916020c1c05010b330d1103040501110901091707090e150109 61
    0x3248045924200c2030342e60041c0603a141d45028022500140c40c3d021032841c03c2c00a68845500c015002d00700042ca01d0703003040380c45100c0c5003030200802600d500041100d80c41c0303810449898161241614100242c1512941203014080485c0f002480c9141c412184400381800d82e11200c0941e9610011200e045d00040c0181c013070040e5002042c21a4000c0304442c2c01506a0031001304003044c0e10000484e0466298810354046840300001e180c245001c208142e0300c02017800c0700203000010000880c98481c001420642d0600c4e8003001c019000b07000b04800010800000c100c0c1da003003080c414000190090b07100c400c60300d6600340b0090805900d031900904a440b4a142540040584081040c10b2070015810030907001c41c1041020402c2206240a41d00c86400e506002a5481c20285451400c542c00742e261442c000c1400d1087e0b03100d0344c1e801101081241c5507120420151007103004160f060011607444140c6603490941309060761440400c0c810115401e601600c038040c5c0c1e0b074240280688002d00c0040078 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 928110053 1250 928108803 928108817
    0x1401272a022e0c0c0507060f0816020303041401090204060b09180f06040c0c0b0f040c0b121501200d11010209060403080c0a080f1801020c0d0b130b0412020c010c03 72
    0x45403803620b6000c4443d8101c40c0c03030b0035020900c0d1a26042e082401d030ba0450b4000611a401b500c80b501e03041344085402c0400e11140d01e1450005e900000d4136800042c1c0004c20084030310807910b003840002d401c00e0451940007401000860341d1000e4209482e030107144035501844042a0f9030a50300400505284145d00c0b18025402c5540c0383e60400c00106001c02014091080e818000d802040c0e854580c20310440c0a800031440b18201420010710940e0150f11562102d8020801804921034007100381e500045480711040d5113010440050f210842d80c102c8400ea0060000552590500d00003082c018240041d100c50004003402500d06081c0e00c90303d10616004401040200b00192404008110121008060703074401a60350f5101c0556074041524495840d8000c610f010300b034241c0c00c54075940444240000c0001420401c003061012214140141098a0140001c4c0400e003ca10b01d034000c1c0307540f080609946140502c2d003e04080900704103440180710392038001079154014003c00341c9203501921000307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 928111303 1250 928110053 928110133
    0x20102070e0a11160201140703140f04080a11090105041401030803071e05210402090604050c0405060a1709030a1d0d1203050405011401272a02 63
    0x8410031102500044902c0d98a4000f00c070301203002c1d0064405403111000448051200e40001460041440f048814480d000c10518000036000210b0601000a84a400c0c3c0c540c010030011484901443d800380003140241346100301000340d030329001d40002c8821903c198140c0d880e0030a0000f10b56604501c0742421042100510225400902460307000103241341c6441d8444a080308000d0441c03c4405d40400b0502c04940e000e40c000219043c00202400b0501d010301514054000803a00c00002d0400b5002e542e41c0e002165070014640100d40140101034600e035030baaa900c1400502da410184a9144280580b101040a498001c011a800b5100315661000d22240c0c031200141c23002d5805a034258082d8075102d200000030030100c4202404101510001010700d0181030007829107001c0d844203100f415240700140030300c18445090800320f002c1200740008646d40e000740e201c020a62424014100fa09000303150009080f82548000390070a6907003503410040700722030844003421340c0d040c107100b880c0141c109003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 928112553 1250 928111303 928111319
    0x4050906100306330303020706031a10030e06070525050a0305130513020d0c0207081b030c090a0b0a0b030c09041e0c0509030c0109080706050702120d1d030a02010207 73
    0x4a1100303c100082c1c4e0281c9800040c48101c1e20381c8144024040880701c3ca8100300f07040e0144070b07403001080c0380e0605100406458605000710401c0d11880c44c0320342c1c90006d03208481d41c8268405029414a1021210310341000007000d40690044100345011032001e1141d00d4600c168100c0445c03030030b5404401003c0c0040203540607241178000448030f5a40760403c0b01d000405a40301c1c042d402c00d221255100503603624000700d0b41f009442841400b1401e640c84042c0c20031240300c0019802019900d50801d01e10a0480d03600000d0500d6900301d01036a101c591482440010740407070b4008486030108841000b129541c1d58060102030204030740103075000c0303001d00007120641000e0b04082600c240d1a01900b02041c450201e034030454044002c00b0001440124120b40c15081c05c001d500d0980e44242401c500d550310307262940740d807480c4d14020780d801c0000c0800c40300111349a40f000c04800400c8081035a4a90401d10300003403c21242d80411032004541d0300e0b0034000e904012071042c421036010ba000e014024149003407 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 928113803 1250 928112553 928112561
    0x206090603040807080406051c1401090e071e080d08041a040309080a0f060b0a050a031b080304090218040605090a1a130e060a05091005060f090405010b04050906100306 74
    0x155020750f010441e80d0300146510b030050001d010140c07103c9440c1c540400903907648600361001c44001c00e2902c220f401e080411009000d04441c1d0349800401d49000911006040510703503800200704807810025034400444401d142e4094451100889010035808101140c0c0b410098030060141c0300b40e6401281110718081d401d41d4068000d050020401e5030b02c00d50035140440c61070041d01e0941d8441c00e69010040d45016050032500c04032241080c00d0306000c00185074601e944001031804042d403d040403c0800c050980740240007440c140c0e6280c0395070ba10782101940c4601510306a145540c034105013140f8181c801d040c146e803005403148a042d91611502c2d0020115050480040300e403c50301941c0503500c001421031030400350b200103d103140070150b0042c03030a0005481905841c3c1042c1c100102540009110512100c015401043c65100d00c030110314121101030113103030801c20300d0040105116054010301240903094408104c19518605a40e403141e0303065442c804124641e800c10800300c0c0840d04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 928115053 1250 928113803 928113811
    0xc30190f090302090103030503040605091c0e030109080316030b0d11010503090a0819080604140609100810141602102406020d0f020106080c01050c01150b0c0c010c0206090603 77
    0x4000729815100c0e000a14000c1090340101c2c00503100000f00b004001190007007a811038440300007420340720504c1040b1100492685a040c0070440d12035514845036030250804005136810080541c0e603800e010b00d4042401c0d00100c0b030640800e080080850039070a004403032120032034100500d440d0151000700112200d90010341601460b02c03c80d900e280c0401c48502c02000ca1030100082c0b000c002c0305850000c1d000701c00082c510b0b44a540b5101102580a5022103216440281200c028003680d030f6810100c00116282d402111280c800c40034649161110b1303510140080c4070500013905c0a540d0000940301080e00503400381d005810001c0780f43e0500c1b440350407280041c480c2041407945540242c0d1900400c00c9940e201c1e01c010303845007030920501034100c6010207001140340b00030b1010505003110541c0ea1849518001c0c100311000411140c1c651007940644104a000b0b41001125030796040c00000390b4020400c9004107005258000d001503010b940c0d02c50606501414050400c0c5c441e00801c013060f00018 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 928116303 1250 928115053 928115057
    0xc0c03060c050c12092403011203111903032d0b01030b031506090c03010b0a0e011b1101082409090102120a09061b0e040509030c30190f 60
    0x300626542c10070500c85100c0a41a2440d2a80c035020000100320300240004060034a00c0004c00c1178011b403a100800312410369550000c0000920403d06e42110b9a104030b101c4041d0754004d400100d500e500086040f21580d5001c0e0398180014014a074031818200c221041c07450b500313040c80c2c0c1c1d4071034540215008000107807814100051070080308000700f82031030030354204d500000f2252020000645404c102d82c40e01305800d052504c0c00c45d0b040018056061044100c03860601c8002e4690803c50b038440c210800b06094440e100032001c640d2440d04c4c4189107855500c150202d0310b050006181c511408040a11034801c1000444c0461010001c1c4854808050580c8810707540801046640358000c200050281c0026903000640600311309002e4100d600381044102da0744070741200b5440079584a1300400e000c81c800c4600103266101c0f9102c0c54514810b0075203c82450044040d01c20700089807000c00145101e4550780d010305c4421074100100d0714894240001c80f2a82d419102c502000d02c100901c00b4005d6680c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 928117553 1250 928116303 928116307
    0x50307080a1e0e0706080c04120c0306090807060b09060a0e040f020d0302030309011104140f0f03062806081c0210060f1e0b0307110709050c03070f0c0c03060c05 71
    0x900d030b440441d241c070300ba803164903211a125040d0200400441d001070089140c158a1820302582c001c040d442540701c1c003019040e203802044144a58614040002c5501c0709042103604514585032000e90082c04060ba0f07070f03c1c078200a00030705040c17030200944500300007403803401c6150400d80344081180b009401030710802240c0310641d0060310b4806908113064004d0b00210b031289421401a801c2d9003103041c42614180c81403104010540c5880b442462000c4102d035409814850701c00031a5811500c0c1501650611032141884404d8280000203089407540700c508451070908080d41e8401d481061003034290301da002005604002810102c4a0807050491042ea07040e49001000401511075035001440c48a000080070440320070184225920910030381c628076443c500d006000501404001c0102c018454002d42d00c01c03282c442841290b0103450001e1003000b02d414040c00c079503041d800c01c4644030081012060341550a6007c2c0c009040b0b110307070203001031410604654400000d80004c1603140140641 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 928118803 1250 928117553 928117571
    0xc19060206150f1905060a0305090d140304030e01050d09060506010e010801030530120f01062105061201090606050f18010b090d05010c0c06061508010909030c050a21030c050307080a 80
    0x29a400516401f80305950228036402c003c01030b80c0c2086d0341d6043d4a0240905503002840c61250b52054a41c000d4250500c00115170030400140c0b030a10072000c101070351a10301f0b46900c0c1044600e03400b1500418003a03840b600400c40203030054400d00f01c00e00001c1c1c0f86621006e48840c0c103050702c0c044d81980c8042103400c48200407030650342e4042c50700907240380d0201c0c6c06040d0400044554050b0424014156440d1000c2d0701280081d1000140307046004c03c0010755100c4001811030b0f2141802c55007400b2a07035000b040001124107151006000d18019140710302200f2811a500d440c20710080d521135244032240300c1d4140d01e000c0d1558100c0d031140d0350241e000000600c0010100340f0a101c1c505502c1c030f0540b10b007143c5030000e01d40001101da06400c91002c1c001c00e44e41c0c28802c6039000c2501810740d492080e00080801080c2800d90304980303054001800c51180382911340802c00c1104080040f40704400c204c507042e42c11520305506031004442800c0c00500248001a030440c803602d4600d030041104e010000715840 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 928120053 1250 928118803 928118809
    0x20d26071109070507020907080402120d050c01060603060f210c06020a14030c120c03040b0f18030c01050a03050a1e02091c030e060a020c19060206150f1905 69
    0x1058000740d9100c03a03615180e1410342000100160b020390b0b40c0c5401441c052440d4001154011f000d801841044002c00000d01151640c11204801900440c202d400303c0a0315400204554081c0704012013650a1400025103a4000d01440055070300b41c0710440c136070b98100b1140b05c0b130181d01100e00403d01180042d00c0004526500e824001400d0140c0c040c21034030000e401c0210b50361401c000e0340d0303445500030400d84502580c00f007400c0038a656844200d99850442e0702c00b8a246000343d802076040c250001410320040241280188080340c0410b400140008010003015142c0202103003080c0400d0040040d00001e502c80d500c40e0398070450101d4006294084000301c0c3e1004910700c101c032045550f00042016031071414000050340c42014103440039110580350740003021a902010f500e8043c9034040394550003a4000d100035460800050000340c0007580308001120124400e105560260207104003060b034100f030702000c8401c076240c09003805c003503075003003600b070203a6484100048001c002c01110003251907a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 928121303 1250 928120053 928120057
    0x904081303060903050c01050708091218030106060f08070801140402280e0411191815020c091806190605030307060225050613020406080f010906050c07020d26 70
    0x1900a03038030b503a06d5680c402145821607001502490a000c10201008110140014200c1f082818007080544030b8000e01d100e04c035001c003c520b4003a4503509241c0e01080442c1c5c086440c1003030342060382d5441c225854551081d0340d204020b0190003041e40c2035142121041c20282c0081101804200d840003500b50480c12000c1c180101030035440000d02d5440c940c4403075241c94010948d03202c1c00300c40c06070324100804525600007c000660402804242e44030b200080c1402c000c01002040405125003030321002d200c0c029182d12401404510440780d06d0042121481b8141c213010041d85a50018030752030301d80d4012002c5071481a52020034403900c40c0008a0641c0381803020313007084c5120b4140544c40d6076803201040340b102c0070040c10440100c140810b82c00803800c004cd0949e003110b0910044034a181441c00805d001d00031a4115040510500645100400c415880221402c0c020701c3d08000030780380c9418012036803041000103940500030030b80d0700300454204021003d408603030098907583c50503580c900d04196 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 928122553 1250 928121303 928121321
    0x1104020d060906051507021504030804030b0910090f0b0907090e101802060f0c030d060803030a051f050114040e01031b050f01090306050a0e101a060405090408130306 73
    0x25515541c0421205100d40a0900540011145c0800312035808001080398000d40101034454240e2100c20030f803001c0781c2d1080390060354100040c1c40e6a551281001e640d52081941e40c4d98dd144110341424030b1480c4640716104040354008c000840a44060711048403d000c0a0301100d46401855000203001249104070000b60a504020340000c041d403694000441d580c02100701c0c03044540dc440400180d07a034008454000818950303180c0c0300c1214040b210300e18014030300144015032502da40070840200000c01b4610030300300c0c04400d216540d9601c10803e205855020150b52102030000d06102d20340c020a005980103902000e22414156246555010107000b0b900a030f81035015010074121000742c04403950080c200c2a6400c0d0718501800000802c1e02d1044d20003e44030613610004101641500d0b040009400b008404542d29410316102e1031b0010b1919104130203024443c02c0d10b41c1e0b001d0400205903030442d00002c0c40444281c2d101e40320781d08254054038810341c460b1030100c0e001c000110a84151044 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 928123803 1250 928122553 928122577
    0xb01030e07260109080a080403030605030a033204062a030e01090b04081b011106040308010918080307180305030d0213060c15020a09090f090201090e090604020904110402 75
    0x2c050126094803440c20000c1e06038003000d034108550140482c26800490340d008100385041070b803a9686040850040c01c05030041c99050007100b42000c103140e0712450059400400320611000c100055105030740310700304e046520030400c00501c030802240b401b03510105800003082e050300d5454094030140c42e0303591403000c008601054014110803030550f032140c8194083e1004107005440c1c0360400300e540395145c111035005402c48014880c0c0511030b910509882c003800c0b4030350007101d002d402d047c5005040c8035024003501d54aa0700d80389080514840c08185461600d420240c03803450f544540b0b00440382070000001c3c01501782c14050f4004006002040148008014040010f8603507100b0380e400c2a00c640e81e40e01940800c01680c9070030000c200500c02410381040c260746c0059980942c2081a140300031281d0104041c1c0d860180c507240141100d4011005151003640c0341c85a031919034100c800d00c3d0380103880c918110317444200010014240022801e402c9800b6050b60544986040f001034141d030302103201d43c92 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 928125053 1250 928123803 928123829
    0x9011a071a0a0510061707030e01020316020d0306030305072303181c0b16030605030304080c0406060c080d150504180501110c031e0706181509020f01030b01030e07 72
    0x311901c1d921a05420000821134800710300e01d0709500030300d0356014038030074180001c1c2035000c0b6114501a6010141c8608040300942d1285020845a8070701029164200c001d030280e1444411607078864442c00301070b04d5040e220541000f1142c2c0326034420b500c9500510035546200d03c0050b1802008001030820303121540319180d98041d22006011040411184805894842c1c441c04d0740010000e2040341d900501d100400417040024003002c90141942d80e0103c1d8050000150108010740c010405104c1c0303040c01e0f80c09100c520f9032002e0440e843c800c03030b200281111800b403041c45031300b09a54200d1615005c1288850026580301c4002070300703c544218413000f28000a40121040050a000d00058188147c056900300103800c85c1058591041000c900b4007170714401d0074001180b0420301651281038216508005540411a200e8014054034805580c25201e07011900200034641c02036590305540a0f000410b0299210015405040c1c3c02d01c846042c0b585034045441070182c20084240140f18881c260f00b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 928126303 1250 928125053 928125061
    0xc0303030f1005030601030317070e09161d010804080a14040b03090f06090c04020a0215070801031b060f030915090606060914060a0e0a2409050f09011a071a 69
    0x150302c0c10311035409a8003d402942c01080400d4104401000307400139004030024642d51400101d07071108540c80c0450348503440c0320601502c1004c10640f41c0d0030121130b03202c070300d8292213000509220044900720b85000600c44030001b00000c44c000050b05004445052100100401c03080720181a0050b803c5602d6666011041180755013007000610291603580c2c0140129041c40a4102e4882e0360110307000f4007a58001468190480c403c00101b5001c200c20911120300b0b0a0020340140904800c2c4400e40710342c00c03e08981e11503034020410302811100f85845e0025a105140400d0b000390480b010181c0701c0700c0f41c1c12a000144521402005002c1e07110308070008680c0e04000f00076150f056581c000341e507134008200006c585901c0d20000c481c080f03c110f0a210344610034220001d5030100b041d402200348021000f011141a5580900d004081d0314140c0720610076986580034440c1e00c401c8c440c0d51a43c0640c442c00100414108500c4070381d615180500b4451170302040741c07500501c0b034501e145100c040d418484200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 928127553 1250 928126303 928126321
    0x903141f0b030601060e0d0c090903020d0f02030a080406022b1a0a030b09120d02090a14060711213f0c010902040c0e150a090b0c0c0303030f 62
    0x5201480008200c403103a441c010070b0340c03103505000e55010320006100529143d503407a00320200c8568890520039115860300141d0020301080300c4103c1c094410071556864550040c075522810996a500841c10550107000403281c80c2c5c00030f4400c0c0c032200d5003007042030079071134103c00c8aa03241c07020324800c4031180c401e03d200c40044411480e1903910270904203149507040e96036400c1c681e0450342c00981042994407502d80b064148034501c03902c1d010001000880c048032000540103402441d070708491191041c0d81d646003d0042c405190b10590380140d04011817030014200c1c03a41c103400c0240c05861126007032456152422440801030005103540d1004648404004a0510585030048140218480510411002042500000754803000c8080114000c035145100f58801e20b50603400070b00a11040d00440ca0140c202090060303110300400041c0c41030703441501101c00302c840ea16030780d0751010141450800f0a040c103800441809140d401490009900b981c0c0c10809140114402424a815410000d02d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 928128803 1250 928127553 928127593
    0x120919120b0907050307060c050309040c09140d0b04081b072907030207030f060908030a0209010f180909020d0f05010b19030308011a090a031211060124090314 70
    0x40c1d42d0007980000028401c94030041582d40c2101e01d2030400c1d091b031103020710b0a28194040d06c2a410b801900c2c124540442c02e0f4000b500348203c0d4a4260801801c003144418401c8e03a1f01d942a0181461800502040c0081d50715001041584100d000c800d540c01100c2003210300b00045680a880b21081054000a0503542c444641c2045000d46c5507003403521001c2e2b43c010303490364100e2101601c680c1c248a0008203015a13600400c401e00c0c0d200d842140d8174940010b50310001e40003508100d00064221661040c41405000b589201000300c00e00111b80e00c0c4bc1509801c058800180304903040b104c408424400268000b9941e4001c03441030f000400d0b00c20505003401044050200c49071900c481200c02040401e8000c01404d0540d01c0090804000c3c0000d1008030b4030b1842040799440d04400700501c00814041c030300c00700441c035050315611800d12030103050365640d54903c02e014040c41084941494401000540440c04040a2504010a40039034a8440204031000d01c6003012681d0070003440301d0499004044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 928130053 1250 928128803 928128811
    0x50c03093609191a0711070b042301120507020c033406050307201b03070b04030b2e03050c100309030e0f03010204050d03090513020a02120919120b 65
    0x1412000e050f81e1034a82080b40c911a10080d40700f44070040116800314807841a41074003055020484182c15580d0301581180c0d40b003407294480407000400c00b0213042403251404011904140c1d20018848440c4540700c0c02800c3c058181000e42c0703e0071244030150307201031080392604503240d001c81c2c0c440c603450081d076803106158000c403251040c208407050215030342080c180e9403c6601482c0454000c481d03100c0f071000241c50525800c1d050310414100ca180c42c07020010702400c0c10400e400303940700307507546d40041803080c040c0780801080e0102000000706191500c15640c048641403000c00a604100e50501c00064600c80d0020ba6240d00418801e190a08103c1d4412130110110316041003041c9403920b00611084559024030f05c10b0901d0705580c81295425010345001d8003008003101c11107050303490040e026415520036240a41c101e0004e4100351001c602c02e030f5600300303080e40181002e0f816074016501da541c8880c2d649540b0021303580150842410046107800684161003a040c00340006091444444c80004c2c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 928131303 1250 928130053 928130083
    0x1503050d0207031e050a08070b1b2d09090916140901090504030c020310060608150d080307090906120303050f0925030506090a0c06050c03093609 64
    0x84003c00010b00b120000603480111415682005045031074100d0a09009000c0030300850b20105842c000c3c0440e00499038083c03101140f40e2140f100c21900a08000d000700815034005101e02c4244650b030803899581c5409052060451034900302030305000a4401c0340a6600b002c1c142d11146903014a5050f071580000540745462210005903150000540c03158014010b00380d400fa00c91001c80c0c100b6029a240341d5003264014141e414184119903d08000d00c2180711b800009a40c0d080402d410707100f0500369170040140600b400035004c0090302d413115698000b5100608000f00410009808005c611030000680340031184c0740030b2034071941001401e640010385086101805201030003c000130000b004400c4040c6840e443c0300e51282e071400c400080200d80d0000c2c0c002e020b69001c000d03808401080e21b11040380326071000ca04043d1260400c030f036103018150030b8880c03a40c01000100001c2c601201c00c0c034440062240038010b00c081586040c80c401c07060846042081c4406001d2152440c81440701d46880e020007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 928132553 1250 928131303 928131313
    0x109021c020637030209010906230a09150206012c0106030e120c06070906170708060409021806090105060708030411040612050f15061011010f1503050d02 68
    0x1d400065551203003245552600c11000c0c0003030381e0003408186519500e444080d4009450920900107000703980000c881038005800b189003c146a40940c522171241070107a0302c8040c9070030b8810350441059001a40702070a00c480791070b0009041448200d5580b24039100c0d4058802035162290011400030007480640750442c944e10190b5540d1103242c22141150030500e0042500036a20f04100e060a040118a0818110005070320485d480002515401030000d90b481604056440c0400c940c070400b01120340c01c0b4032480700b005c540320031310800f130712600321000400c0069424501d80c006078042d03a08070000b01d0007101180070408940b421600d55801040240e80403440c104150395401c80b10701c00180300070007402448485240301d4650b13a0004010f8032104004a000f1000c40c20000e81e5a4400341c120601d030712802d0b00d86075080a507885858000c62014201080c4058002e1b81503e04074203c0c00500965941ea49014a110916000c1d80310b1041c06607100c4030615055040607030400d80c0c800c40180540d403003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 928133803 1250 928132553 928132609
    0x30c0c030215190906020418020307051b15150102060c0a0c0b13060c05040e0901090f11150f041a0a08040813090501030303020306010e01320912010902 67
    0x20561070351403290801c4000e0a035884406100e004045400100505450840c4d4a410000503031700074410359200346045a1804180c00c0302409a00c012505003000420078807403031021880c02d20340301d0000200364060301d0121030b00d0b441d26040d000c002c440009406c000980000100c0d41c041c410550080c0a481e12603140001018029140c0002080003c00b20701203d000241e0703200c05080000301203540004240806079141e03a0040c010b41160081410152620011030f030801d40521640c0d8600e9440401e41001c4103260f121064491031108010380c0001003402e0044200031068001e10440020341401912507080c0902400c13610050a0816821001003242904440e000319407113a1095202214036941c054000500d00622895030290041c0e030f081200110400d5016009144140000c1e07840c48121480f0700c0c01100c4580300c00803072411400b0102200012490480301407040d0144d40c0900d40e02e010b849201103a00f610f80745496103502d96440720719804514108485103612102071441898043c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 928135053 1250 928133803 928133807
    0x3061c121101020702120609100921180e10050a080c1203070b13150212060906211005010602030f2d130e10180e1501090606030c0c03 59
    0xa40d0322014090240d40710158000440c2501100c8625074007800d000c0f40f40e0b1211141e01e5403010292034400180c0608030601d80540c0d55032181c032046a4100700041280b8608560803010104040c5505082040640d07400c101804401d4118000705004600466145001034007880144000d4010610804902c4410080b511000410000b001c0080b035000c181c4c40c0301400c2c054550311562100800351400c01c3c0030001d82c0801c40c2d282858460107803200070015024100548100d124a82c00542c2445480010444509104501d150301c004054001c214200c1e00c0790030010310311180b08052460707900c6070154142507a202e01400c0c5c01800c85000950629800e01d6880a4500800080d00e5410450303e00d4060300080c9004000d0f05c0310540c490240e0343d064202c0d07030000c400105000700f00100704100c01050803c5910105001201c01810f60301c4804494105464040c2229404612451044110a540491440038014003c10061800050a528218000c2c06030381c04410400d0600151034540c1021035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 928136303 1250 928135053 928135073
    0x30905030403110f100801090f0212040b07051c2403021c03090317090a23150403020306072001090206042d0801020c12030103020d0b04060b031203061c 67
    0x41e6104100714003c1804002140c0391404070500c4a41c403c849400c80400c49801481c0306040e02c111000a121130140da03200d0300c060b4031410615a807101c5900300014003107003114140710b80001080ca409480c0c400f080801000c09010300e024482c038550307200500d407038200c450380c0200f24981a0312900d0b400356186400141956003c284800540b84034004941c0c20103224a510740c1c051984580d01380662000c4510040e0f003604088001409154600c0000c1081440c3c815a00c3c040e04122214100c070312480030602030240310100585400a1003400007100581e0240003191082039a603036040803001ca124080d0b09211034541d400c82090345082402009a20390100b110151960705901400ba03002c442000711900b1502e0f0f140e414002041341000c40d40d10010b400400203144031104032107019541c40c5a603052880207100083d40950800e80c000c002900e000c0d42c00394024081c090004103032144c4000b2900703001001080394424880017040004503d00614070711410b0315400d0130880510f0240d0390b030300504 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 928137553 1250 928136303 928136309
    0xf05180610110109080703030605030c0103090c050d080d02070f0b0a0c02030f0a0519091a04122402071a1312031d0a140601080a150b0a170c100309050304 68
    0x40070b00c80500400c96000d400140c0c6a0754410301441e0344400a050060042545010303c1e4484c0c018849400031543c802d024944545421200000444e0301e0642001b8130100400350071260703450288145648480d2138070180410343d01540f62448249014603001c4021341000f00b0701d800080c9400c0c0300344150b076030003c00c1e11121700040510355510306144400740c500703018070f60503e150720050401600805070300040c039108035421900110307030804004d11001014010f90107039410000e101d4a80e540807072016003d62010307141c00c7c682d04107107001c680790500a0364858001601d07800440b10200761081401003889500c034424264009515106540720b840040301d01c0c402004060b2554021422070811603512401e103100c2500310390612010f803400020510b40703556000400c1c05100000600c0c4036010800841044c3e2118a895001070344010b02c5009201003002c86821001105010926800b84800128030092200080c11820003140810444c00301e660000c2040500385030030300000510000c05d990a03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 928138803 1250 928137553 928137557
    0x20a0305011d06100c0b100602010e0f061f030c060e1005030106020c19050406120c061b06020a09051c05010f06140f04020d0504030f090501020703151806060f05180610 74
    0x12864413800101c940009100300074040400070700500581450300f4041d5002c890503a002031180302a0005c03402d468081002c058695074000c42c0005080e8008a0010041c8140000040e00c815899840b0fa0160000e0b980004c808208080704503105868071520100712100b00740b50103480c5606180f0300a444a00302841355018402048045a03428083c82c8410080c4c40007820070803019540d40c0c0c0d00d80d00081b001d00241c2e50180c1585012854500c074030648504c20300e94003541d44100b00247d8440d00252301609009003041060302c03000c01c0c00e03502c0c2c0440e606411584001085080304505045003141c000381c1c0b100b88140c0c5450380401542201c1e45005022090880c0d00101c0380c104100401c010f4410801484882880c0004200805410500d9070600d90601d9907229486070701c4d00016a0f4499560101600604461403000e086403619080350030441510410414014030558480081c0c0d00e0b02c0d0804510b031651010248a40c7c20f0803001c0d0305105582e403000000c20b05100001c118500d640d801e00c901 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 928140053 1250 928138803 928138819
    0x12050f01060f170f010f0902040b10021e0703060606170a0b13020c011407091d040812061903031e0e0f010e030a0f05100c0807081f18020a0305011d06 66
    0x30300c0c036014041115104503d04c0240041448152100014094201d040340315502c0c00e002c0b680316040800585281070159001042201c80c040034040c44c1c501d809541500e035100352030b00840040d07d28040c0d03100501c0030b81c031100300841000061070701c080c02c0240340ea8081481c01c561030100d0b98a42c03081045600465034016070340e5804c1c4e241103000d07000300e519102014802c50180500a81d0140d50001101c02d441c2c0d002c1c4582c2540e0401700c0d4600000c0d24050400c0c601400040344004130f1440c03d5400c0500108902c0c05016040248402d1725034940c0300b80c0100310780c00d590550000507201040301c0c2d480f15161002110040c030307001564001007400f0341da04000c1484d03801e8007507450810100b001240c02c0009400100d00d50300e001c036555034054486403425030034288642c1d8501d028421081c00b075044d03511000516600c0c3ea5451070030b020590302813001c00280303030702c00151120100000c190301d03c8910b81c05640c0c0c00d05000c0180c1a110180c0c040c801c840303e0400c0b00c140c14103040009942103102110918 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 928141303 1250 928140053 928140089
    0x90c06090102011d071502030309121305101206080c0d1b0b03100f0b031e100504021201090509030301032103020910030207052b081f12050f01060f 65
    0x3c1c01040c1d200c2d0542c42210b50081000c000c000002032420465000d02846c0040d021544070481e283d003c281d40f01d00441d07010030180c90424201001401d0400d121036101c02d0b2256540c00040c2c1a00c040d0140440441c818604010300d280301c1f8010407018180600041c904111194003040f010301c00e816001d804540507001c0106562220705540c001044004034164480c2000c11810300ca04525100b46140707155410400103c042c0c0120a0b40d1288208100d0101d1050000c0041256014010800c91042e80090070106640d43c40b84050035403141c9280117520b596041181c0401250405041e880441c1d106000410000d04580e84c178022101c9003041940d901000c048054020303004150f0102d81c8412101c1c0d0864242d5410341c05840020f0050781122a0300100d02041c3c22604a82c410048100b9503035a102241240900f10300c0d60051182025015901d2030b5030441500030059800942c180005e10b080c00c0140b01c0100284034940742090000c12809261500400e042581403144400c40070002c030300c00f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 928142553 1250 928141303 928141307
    0xb120d021203060a1a0d0e120f07020f040501090f06080a080a1b1e05100b03030f180a09060e09030a0c031d03100f06080c100c0c090929090c060901 65
    0x4c402400c642426403807118000602ca411a0002410040820b02d400c41101c80c0030000154002c41001148102e480c0c0b4208101c070550030351110b10306030727041511402142115100d9110342c1d802080c502000080114800f001181030751010317842460140d0000b81081c0100c0d40c81c004450f400045424201d01140e080404c201042040100140c8007402c04190b804941c0b02c2c01068860162269094a400d00b03441e00d0030000725180040380607059482401450340942004004040c59100c001004856155110018411110b240c010341710ba030383c80d12020081030040300481138002607503d02441c145451204000c01007444070001504104000d103a140800000306d011050546019094940761440f0f001a00c000c0d14002401c038402c80d203400740000d1060300110301d140c0e00340c0006000b114000d1804400700c40c40d042c140016900e80d5071214000400c030700d40c3e20070003e42503c940b49031520001180078403240240c999200f142c6030780510003006550140441c0b10386a0500407075405440e88501c03001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 928143803 1250 928142553 928142569
    0xb04030809041d0d0c0b010602011802012105090102041e0b0d0906021213050d050a0c0b2203020c01080a05010b161b0807050a05060f0a030c020a02060d0b120d02120306 74
    0x2a1002c2e40110301c03602c0e800617408410f010752280200680e100c0750740d03100030072401c8541060300b059001300011081c400540c1300e0501c034000300c100c0b0001c041e0216142068902100c00554051625070740c0041c04001c08220403c02100720662005da22400c646000040615032003194030186280d6036500c0e145042000720350507a441500500682c050601e000e82d942c0c040d400014109403840c1c8520a00c52a030a8462000c43d20201c080c0d950b0203005d614903650704004441c02410400d04a01d460090819100007045a03a130814020390040403852400000900034045c0680329016660030031005009204220007216043c0380010082c81d079202c0b2034200700c1c81c04c613001084144100480c4c1030001c6c84940003d9440b096038021580220500c0c0d640b81041003038800c9415200e0314640600c1b07804d00a0307001e64454104076240d030040da845a00d440d030024050754070403134400404503546c40c0a00c4c1e407820012a881c0031080405c2c01040010b0350110301035943c80303000295040c02800003001402035115510 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 928145053 1250 928143803 928143851
    0x10f050d1104020f070311100e12090a1e0303030506060a05041e2106061e031209080d080a0506011119020a0e04030807170f160c0b0109050702070b0403080904 70
    0xc1e40713884185624006180c200e000701c140c1d06500c08d441d001d00c40100d461298614034013080e4010585c2e2046002c4400f40e5800115003542d001a8031140080c00d4406603105000c0d012505081c55820b83c294175000d02202c1c00070301424081d200a0140444071500001154140c44144891840526008001c084a1649034206a40942000d880b5800409520303000e80040b601c01d03d07040c081980c491030300307401100034245d80c0c05440840240820210391811a5525503040c98030384182100e445200300c83c501084c440c010b80014808004000e0b070418a48a069049542440d2102d4880c1c2a030300003940d60700321208441c1c91044024684421995100d120400412226a50420300d20306802c000d8503410040714480085000c1a40101110b8002c030321142c42402c400b921550552a40241c020340c080803184624103118070004031401141104c04a1b90003041980000324452a102000900380420f640c03140f00f03400310074802840000e042d0001c2e42c1441c4001d4500090a80242d0030075004102c07058 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 928146303 1250 928145053 928145077
    0x90617150a09020903070b0f07080a121407080606070c0311060409061203020c0109080319030b06030412021e030f07030e0d052505010806040e010e0f07030605010f050d110402 77
    0x4800003072252010f802030494102c1c02c90036507040b10b98030340101d855403144898000b8060301c200500c00006080102400322103c1e00d107000b5107441c0490148a0032260010030468034404004104400c080d41300ba081e41e80200c00313540460511400d90344091003003426000c0140000c403a29503100b1030f620b410083c1c6004110140c0203011407561440c2c00c0c4100b40320708100b40c005015a09001c0c0e510750240c0741c20701c200ca003440d004501d040844103107400300400c5090a6001c0540f5100b004010355508005140102c1c016201ca00c01011091000380ca404040e80b25070070a10a00a400e5210150100c155640200744100c101c4d607505540c58220b07200c00c480106654031103902d03440d8074180200055210385201020384e80241c0704802d01a500c5100c0190710900c0e0008130321600281ca18140b0703410031409030380714200103e08024001141c1c0d040121038a04034a0350303480410104240000d0303026035801440444a41c40c1c03400e007030102040e0071500421003c0c00d240c0d440a051a40c0380c4895040b103070306045034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 928147553 1250 928146303 928146319
    0x4030c11060d062d09050405100e0d030e010c02280c151202040b031311130e1b0a051009030b0708010501021b130b0d0f0b041209061715 60
    0x2c100000003411280144409040b06010840f5000c03650f614404040c03160107081a41c1e6132402980c2805008000c10840700340c003402074401540805402626816100351b07003e8180c030488500014112260f80c10080040d17810b1042d640038840e0007107602c0307014040c2521450712407080000084080000b040d40204181420f0800042c03c10340c1c211070000104050340c403482603005c40105036091b0302071809014000482000412a102c1c0400310001046124001d0225100130103c0040c0d130400c080080071000a40b00c0707040c508140010b014030744000403002000007410343d421011600c0041e040c0100f600070700260f000d080700e8078042d8801c14001d543c0700c00c00c1c82241c9031070580245007400a03c5a1405446400c3c40042021005411004000c0001d420044a01a650405400340107031041403500001c151041c07501150b010850060806d00914014038540ae00b89458010005a600c0c03041c2004101001401038550100350300811820101040d4000d4442e200301440e60b1994129041c3d0000344 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 928148803 1250 928147553 928147567
    0x10022a01091e020f0603070f081005130b010224090c0d0809060c031b01060e061012021e03090d1e0207030209040602090315010303020105010801111624020c01180b04030c1106 77
    0xc085100034446050b0b9031270f5180380d2501440c0b155154090b01031294070000c8100c601c0d0702d801403684195402c487c144121840b4880d244035015246420701034000c1c2107200d4208001d000a0f003041820b0031920103030303041407126006441d01c6502d8001c984070580309039400100c80450540030002c3c0d50300d800303440000300111454210f000c1d008120a1090128214003400090030310b150120b040310015000d51a42100780c54a8480c82c00258000031000100c8081e2501e140007014124024612903403090004090120014401405040100710400704580c1300e04210124160302040c040100c0340e0559480000361a149080700103400390b09140c90700340c41074204000003290b0140900d41240c1c0250001c104907600c50040c2c60a0351001c601000e818141000200300320300302d602020000340e000d1050031040c80f1121600d24020480107100c0000c2c1600818400b11125080c4200304850741902d003617403c030030340e103664000044400803c06814404141c14400034031206808040141c100184043c7c2d032522 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 928150053 1250 928148803 928148807
    0x507080a051e160e011401080610030c02070f0602012009011e1b050303061302032206060914010303120501060f0302070512030c0c070509131410022a01091e020f060307 74
    0x130b000d20a1603811007901d60f000d40d0075402000c0b007900076000944400315506008000741c1c0589a11f0f50702c0000c5104040e0001003801c40041a080a03007895800469070140c171510400440c0e80c1110600d180c00340c20480d0020716a00300c0e500a900181a031075440c12032109990a03100040c180c844642c0550072101c1200401c00080300542c4503282c21101d59252400490315001280411901d500140203091441c02103500d03d03014400f0110700c5840302068840c1c4400440d0159240742200700070060803400140708040c1c12a00020512542601c200425850860000c0c2601c61250b0580c0c01e056001425000340f00c1c0601201e030700c640b002e1080d0707550390521407014146c40c4e00100e0081c2803030044890210711498451f103a580139007c2c0c1d1922585400507a103412502c4c1a101c0000006886480c455020300b0109001402541010303000181c0300c1414081e580c01f0a0990101a0360540d15100f602e00c0001d086481034900c00f0501806182e10801038404980d174680410740180d4041404001c01810a0b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 928151303 1250 928150053 928150079
    0x20a1e212406030c080f06010c140d030518030703080c0705160e180f10022d04030213290d020616060c110a03051e07030207030507080a051e16 63
    0x6100e0358003000005213040003200c0000d4251010030200d1011804a00d2030362241c7e504070743d5a4042c94591110000042500c1d01d030000d14181003020980f11400c101d118941d080788a40e01d03d1195003d549480034540d40109100c000806d98411a60081051018070608210a01c000f20684e039900580c9501c60038900c1e10600d04030383c1030614400380c03c0d452032040b80100e11003200400340801420864503c01c00c003000307500450500c034401903008801d2076094107510707202503030301c4d20b042d1a09036901e0850042c8007800d00c100c83c82c2004d0078200344040b000c0d02800d40c003006d070316030323203202c0000d020340e40d00b000150241010100698001000300321840941842c442c120025807050608001341d002e00b00d8141c2d941410804010216044011000c1c00b10740914001c107004284800c400044000301e291700145500b040d0b6040d4016808540300f0710030040100305420103020760200502c031028265848036a6142001086103500b40d414810700d4522400300400c01a10503603042403403801fa110348101401c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 928152553 1250 928151303 928151309
    0x5120414150619121709031002030415090f020d03121103160201090213021309020304122d050d140414061308070b15090703020a1e2124 60
    0x251210728001014000449080000c4594042a28200300043c0c0c450a184142041d1802403001081041b000a80c0e0180301009010f0310111006813039083c035040c45150070b0311240264002d1031401401074081544450b42145069048030b4202d105a00343c901242c0448000031100843d80c02c04058503a180500c2e00614400c0100300300405040031031200880c2a01c00404c0d020303400441c0310441e240b0400c80758000340300382060b90350b500c400980c1e140c800340304070307803080323a007518038024801111500d03c2d0b008140081824148500c2180709420b450002203244400c4482818001d00041c0c4014441d80d40e003100c1500c030307400200d151551a003410125400c6013940c149c41c40728081c45000034000360015482d6008560800801800c020722565020000c0c1e8000d000d010b29020b8140030a0443e07030300d4248045c410012039802580315084c29401404010b1a0f10740101c0c0710201d012241042e0b640411960000c517140103020f0080e002e0401c0c0b40700200a0b4071392074200010b6108140c4040b000c0d4150407022 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 928153803 1250 928152553 928152559
    0x50711030a0306080c09070f110c06031014040b060d020901030608060403261005010f030f1a03010e030909060603060d12031e0e0d0503070207050919060b0a051204141506 75
    0x34901440030003038801c06c11a09000400c10b40c03401040518880e40d22810b0009116040707940c0800604001629508201c3e0169680c080310107040c845202d0080d054103c42e9030948051000e03502e0800000d000340201c080c0400860f0340440d00051583c401c4e0060303001040c40b5001da500030308141c00c5c020081c070300300b111660b181e860042d8240490b020140b1658820f5203100105403c079801d10004566203258035482404040c1c94049000c3c2c00704080c89001c1c80410002c483c00d4000100500780f5080d1202c00241d10026001031010202c1500d490640c00d50180c4100c0d84c255881d44e0b004005507041002d03000191280ca840001c0482071501980540c20362070146016400d072802c0d00001b0360980d0000086150903411016201401500a20145030400c60500641d100d15882e40c01017903131440122224421184e22048031403070140702e8810740018003400100c1c10700c0c00710940006442e80c03045041100c01c11141000050500490f01003078103c03101c0d8030043d01c000e042d50102c03088050a081e11a41c0c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 928155053 1250 928153803 928153813
    0xf0403150c050a3e060402101701180207120203090a450e070e0603030301030b01030b0402060702091806060901121713081b010512010504050711030a030608 69
    0x90624042d00941d04184456601c6040804803d080101440e8019000d1010340a404803a5012240701051610b0150114030040c1020324050040001044148a060083c015503c045400b904034541645056840348ad0070803c104203407140d240000e00c50b02c2e101030f00350150901c4088940f030740800208000c0c00304032004e40d1000d403188030000940b008a14400d110303031a50121440040c0341c68840c0c030026044044a20442498000c00900b565045044030039250004981440801e0001c0309054100c81e040d0021420740d070455131903405098044c0405014a010314002030110341e9400111480c40758003030918080e030b0030100c5522600110840c2c10130840c0c01018001083c80c00c041c0607050480700d14080c59803500301c054841407490500c5404410b1503d2080001e5100c01545070745003c000c0107240010a03195281c240168507018a10f028241040002c1180c2012400b4841415040d51802c450024a549a015080d240f520b0115000303041c9020206c3d00044c4550180d125070110b403045c5040d60 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 928156303 1250 928155053 928155071
    0x1512080d0506030c012f01150302040e1b0d060b04151401032a1b14061f090b012f07080f030d150e010f14040b01090306050c0f040315 59
    0x1600c82110406503170002c5c110003030205a040d8940d4040d58800c0499010b0300b101c40d90400b00500f074070340c500c04031220b00c0341d407090420840c105032040e19480d503c0c0901900c1c002c00040442e200401009110600c01e41d44082c0350402c2c001160310211084a00030010000d04140d0003104501d00940e2080c117003040903800303440006501a00a10801121a16003107500c2c08141c2d83d00c80c010040482443c0400030148100000842845c003e9140140036800152070443e880126070b18040c4010450018241912818030605e001070015a0540d0942400804c104100000480700c890040b18501446040b0b5000802c041300c560300100d860b107400000780e41485880d0724800e071341c0d002c86200c5032141e940208a03079030000c8100c1e4008a40b06e111210140502991a54101d8503510280c001042802200804200d10152444400c034502d00642d001e20006444200180110b4101d20010f84441c2d1100e000607000a5044200c5104011812040c1d80312510b81c2452600e940038041d1000b2424500b9004e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 928157553 1250 928156303 928156309
    0x30a1b1e03061a0306041506170a02240d050c0c1603060605040204291605010501050a0e040b04230318031b030601030609020d02040603111f0e041512080d0506 70
    0x2416078900184c02000640c80340e684264000c05071040b2030b81d0265985402144270742c4001081c4d50010102c1c40107115000140c010809c1021031656007000701e1840440520901c0000819240d40d0307001804001440c3c5d07039040f8031300c0c040d100d40e0321100b80502031000c90320000e4a0003d042801d89001e50f81c10030039140c4910921089104601901400811011641120414007030007000c9000c0d46c0c03a00f09003480080384101c804094881e0302142c1f0313a5100c800600c0107042c09154000200b901c00c01489140c203194551044142000e031028140603400c0c44c0c0b007000d00c140200694250403d1108481d907c03101c0c44c3e03030b00d41c09500031240d0034824000c04050302030b55440307003035960282080103010b080a40d2031560340c0b60051104020890b0481455009000940d480348100030095009450280490384a003082000b44201c028986110811030ac890046803036002a03828105031054400044840c1c041b841045045040c1d482901c1c0405410074039020410b0030805451804c210180c20321198484000b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 928158803 1250 928157553 928157591
    0x30209040321051b160507170d03060605070602030717070c050609160b1809010909021f120c02030708180112020c030304080702010c0c06031d0a02030a1b1e0306 71
    0x851001c0c81c0034a040b018490a1130700140f11030759018841e02e404102c1a03031418104045540f04622900000440741c603c0003040c4589201184c50380350822000e42000406441d0303005200b809801c081c0d021001a0004e809240c0c441e04c03101c10f1105d080024136000300b00030301ca841030305030442d0702c0d002da203001c10204140004c00c5202d01c010741c140000341c01d007002c103410202d400503091481402494490782c06640c44107010f5a01a04150318041114103007801801445100301820503036480808050320010350f840304c010141c0d4604000301003900c24203440d04038a1400380c100040c000ca03500203003505e4030700c0c00041c03000c135145000c3e01c0e04101048000d201c041280a0600e04680c00d8104200240019040c2ca00400c2000d10504080401301e000e912414000460b40e0810000300703540f0001508a503000080950001c03480030010440c03004aa03001c00c0d140c011100000b081ca5110b850350305000f822481100001c1c082c0e01b000340301c46000034070240c2883c025920007a160035140807251003203c560101c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 928160053 1250 928158803 928158811
    0x50303091905030301050105030c160f0209060d020108271002030709080706052a030d05150d23010e0610050901240e0301150b0405120303060a1e03020904032105 71
    0x4060f60450780380030300540305503100030800d041c0c05004001d900031920640a107280094080c0c2c19102803007805105100a180d0042c00481c41040031001c5580142c0e03200703c40c2039209071142c42500d001000c00076a100c148807040c81000c86c90040240084981c090356000d944102c0c0b5a6662004071a52420400e07240c14481c082d40002031820440100c0c800d00113140c1c42c00d10303103105820b010800c1106031214115002461001c00c0c568540c4140f03c882030b500d170818080c0d41811610301107400035545d030b40021000b42110005070a4607500303511030003035020752122780100b8001d003c0c4d65891500464035007800160303000c0e00e0703c03442401002054035590703140142c05502840702041e0300220200001e4815031401882c0c0c81d072642d01c401500c6402c10b041040c83d80100050b030380042d103540c2000c00308a06040340038040941a4800d208015480da01c80101500700c1d10900403c1203881c1c0c0d544015151020b89400c00303500b08e02d1040902c0105540611141103002c40340c00003225503010032002005554040d1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 928161303 1250 928160053 928160063
    0x902060f0304020d0c08060a0e0c010c021c0c172407081003050709140a0c0801030305031504110a0206181f150b13120201050f22030503030919 63
    0x4000a030100ca40c820003075400500040c80c803840344219640d1100700e1210703a04015440d80001081c442d6401440c000c01164481c000040c0c804140280c000a05201c8a0080a4401c40d0140480007440c60400e240e8150190000c1c5466038044d294070034100c0a001c0c4840c1d130340651113003004130f219592103d6100758064010841390300050315210411140340c8000b030002030700240140c0000000030405c20100d401008500740203d00d51444441200309254020061043d82c0c0c00c140c0d08910032640401d2440c192030703060400c15225201d100358620a01d41d80308410b9003140c0350007803200750103080101030034502c6103903400c80e60950b444102c0c450b0b003002c0f4a40c44e014180d22100084a00341040e00794810014000c0c10001103018840d03880c0c0d003262000d0340c0034070801e6000050f01c0680728510707190040584049001c98490a2107070b40020524424410300c21541c040c041510f044101943e00042c070381141070041c20008503203e0400399207a503c00e44800d00c40b481403c480b902150581034440d1b420503082 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 928162553 1250 928161303 928161307
    0x708090901150f0924031814070e16050a051606060e28050702010f060f030b0c0414090613091b050d080702040b030328030606030e0d0c0201091206020c010f090206 72
    0x42e803c14115041c080d424a8107047e200c144030540c40e01c2110307034010300d140220a2040301a0005da0202d040c85455005400070b40340000070031a108070500007814145032246401d561721303000c11104583e28042c0014102030344d41801848000e001941d04041d00356210380305140032644a6005407170050b18186407011361000c0c0104503405c050040d5002540c005003e00001c51a81659415842200d0540d006152110b642d20300600601c000c0000f040d41c008511100b840c90a42485543c0d00070100b8000d26521034030401e000141291141032a0350040011540113020011a905d4248500b007004400803040d025900f00005e40c5103001c403082007159401400315441c000c115003c3c8005007440c203c820390540300400c0500b0540055072030024074520395a6030b0800303925040000405903040c9a200704109420140c80c50302a034004150320713801010700c2c00c05904007046840141c503520303880d9111085020088809006110b1142c00401c0c4100740341c1d001f00818403082c61050200c7d503030704401940240d82 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 928163803 1250 928162553 928162589
    0x906131a04081b10060504270c0e090606010815100302070606050603090319020c100e28090605030d0813170708070203010c020705090c0708090901150f09 68
    0x1500c49569081401090350300d1030b025007a03c0d056112110020401003543c481040e07218012810302c14140545022030782804800d0f0303c4032400301c6940080780f01585d546003200e80301080155007031001e030040c182041c00012528241c1113090303d83c50120b842501083c08500098001410035041e5000400c004260780c410000d081c00c1203000790000a01200d4095445101181d07540d221800b4512451340718008690f070752100c4100c0c0c07489000701003140381503500c620800c030425070b242503040c45180344a28101314017604034000101010000c02180e2401c196002003001045041005031017680e280ba00103120036540c5406159031820b0501c038040004880001050000e084616501c03142c602481c00e2410002820b008800158007504040b5542c1c1c40c0040c1c01d00850400f1f014040c1d03010f0290001d03004080ca010b001c2100040300900f0b4030745900000440300100080b40066075120035018100304d03441d6841300c3c401c200b1204100041030105950554207041c1ca44200000d8007910f402680c41c100e0488 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 928165053 1250 928163803 928163843
    0x30c0a03080d1e06090506011205060f010c11090711071a040e09030d050a0203040212010504051b011101050408070b1609090c0507050d090f0605090f0618090405010203090613 77
    0x10703c2c03030602028060f21507202c290003d81d8000c0e40301420503003000040500f0100c00141070b00c5d03401c003085c0c01e0450501080140554070030bc1c07a1140d040081c00c01407000604d600d01441c54424001d947c5501c02e0b046e1040c48291580a2100c1401c4070040044440e0380303031a060180c3d10b034a0384503041007800c40d04200c248002d4010f100102e0b080030840702101c0c00d0040c0b0134101c0094601c11203541074400e80c040704000651800d00300c04681004030700002c01c5181455114039403148442c0301242c0241900c4d50003001a81d1240c0042c401340200b2600800403030030246010042503110307a00588040000030301003510900250360714080c1307a03016218000c0c050303d044240b0010307101d1038100c0c006111060000700040b0700705104402c00c99400f41d840c050344030304110740c81808480310b401c18410013000380f045000c581c86440f403200745c1d072034211185900c400c100101d500c2000c100f0184039410460200030300c01000415000742d405203544030199003440d50784140350940074010b0304002c0c00018200d039401450072 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 928166303 1250 928165053 928165061
    0xf0c0d030512010602030c0607031b0806011b0609060b0301140112302007030b06120d05030405151306021803030c0c13060b0318030d110405030c0a03080d 68
    0x203109090007030402c9002c00d030b01c00e03004409070301c0400580c20020b43d180c05000180800d643c40b02a03804d04020304c0202c00e40c202a03c40b5424101000d000525011560f03ea00440304152902c00c515460881807a8030700d0501c0c054100d400c401c48040c0d04001000c0380e40e00e810b001f059a2141e000c942c00e00319a1800c40002c0301819102030542c0c01009a4614090204500e00302c0d00d040c4010b0281d24040c2402500010b160711030404a0020443c1080984038405c0b00c0410300d4811607030001c0b43e0350710a80381c60700001d034010080542060a031040320140201c090f00040038611490090041c3c1e844441c403803001c40820720044580315007400c134503400840010f5150b4060200520344041882039102910b0110b0700e180d1040d40c04099950102148001c1442d003225403140d1800381c81014840d0614000c000741701800068810251040300081418045004206070f445a41000f5800d210303050140425014940c05030107058024000d118118101d401d10030614402c40e5030202c00e4a00c1e2005041444c0d0081c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 928167553 1250 928166303 928166329
    0x110c062d1b030a09020f0d030e061305030f0c1305091e010e06070504053f0a15090b090609120a2601060f0207080d08281505030f0c 58
    0x101010380c180c50703034031007022024600c510400c0000082110060040010303099600360014070032040d0031003140010354031080c00340c400d42c000da40e02d640714506e54a40c6002c42d200341c2c00c819058400c01204c651442400955500074135004e0310740e00d0030140c0741031422094903000c480f0516580c0c00031404005080300007803e0a040c0401c0030001841c40346540055040880664039080020404a42480103181044c5040481040070109080304036480114949000305010351003200c080002c04140c041c202400440c448590100c2d000d03a2103080f942025004000644003509c4044060380082d62108000030ba09001c3c001c100d00030101403506080c00d54090380140714171020010390006010304100400500c1281d22090303040250b856040160060860568040032401c551018100300304445011070384c008012414901480e85941c0e00d9180702a089803040040348056a490f2400f026214640c0a407112420104042052540d030b50f040542e1141001d200d6111a0000107601c031540c41c10620100d07007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 928168803 1250 928167553 928167571
    0x1050a0b1923061314010c050618030c100c021e06150a050a06080402040b040c0507030f05040e0112030f092102031002121f06080a021606110c062d 65
    0x18116002c01140c0c0d02e400c05500c81c4121000310f0380501040c3c031012281e00e00c00e0428030300030320618210303180c00d690b40e01e0191880080c4020f0045400c0c10b03113418000c40e00603803170030030407030701c24440501420340100711103140031006020b43c0020126040c0c40d9581c1d8889407209400074185902c404003001c01c44401100e000e507029000080000d20307510b403601000c0040c500c2c1d884482031031810380103010a0ba4140d0021742d126519200d100030056401c1410b0b5030b60190980381140644138440002e075254031803a000300c005510303440d00000d000343e0f4151201c808a4400d50350f20152110030b04051340c0500b01c0740100d070580d00380381800300d0100300011681c0c90a64002422910782130907a00255040ba03001ca0b00202440881c5e07400c10007c240328000e0781032480500080070342c8817860040002c000f400058060443c43e41c000450741002c40c800414443e02d1030f088003040140021440907005650300001580c4c1660003000d000850340380e141c031040c11440c00d0b00100352600c0c40c10b9a00440c84403800030a03480c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 928170053 1250 928168803 928168859
    0x806060603100e10091506030f02030103020616140a080403440712030b150c0a02040513052b0305090c150d020c0c0405180a060c0c02030102070501050a0b19 69
    0x148000c45070050380c5548080031b5981c400790342082d40081c20744041010000e0880c1c0108010030050312a642142c03541084250a02140040340c5803180203205942c100c020203118601c10382c0140200b201c02441100e109420b035061401e2803500c8002040485091040c1c0300340039081c0c1c10b1102d030202407200f61800100080600d4105540e460311201042601c50b4000250750325180310785030402c4540042c540180034000307800c281402020b80d0b80ea45407080020b0050303031200d01041e129401c45002c1c158590313215003503c900440ca0003c0c0b105103174028412640c0f145241e04000710441c06441500d002e410303c6001350410400e04c00c1405052000100d050f0345c0010f003000740d40115101031025000c81f95105002d03212040d0b41104000035284040d114405684400701450000319000858444082c0e0052010401c20700090f0161514407081034003075003550000420a04210b410b5001078460314801c8000c10050803c04144640b40030711100d00041c1620380e0100740300b01801c0309100896500f001803d00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 928171303 1250 928170053 928170059
    0x100f050d140a02130b03010807030321090605070828050411031c0923040c020705030d050c0f0a030203070b3103031d071703070812010806060603100e10 67
    0x81d881200031035a50102c5940480c50100006040c2c44520040c01143c07071480c110f5050040310350300e0b1100b6200040600c05072401a00010700c01e5240c031861a44640c1c42041030f10a01c3c105040982811111500013419201c00076441c000340e03080d98050000c03007141c00e5001c480d1141712000140006070056424405203e81070401c0e40e400c02c5200441107520324002c01030304d181080500440074030707048041c454000040b050751034019102d604444400c2104c0100d500d00141c902641021503e800140c3c040c0101046e900005401c80001e1401c0d09d132030000c0341c4120300101952920b81800340c1d402030050f0402c008182c0401d401c00394440c1c10104450000205168800c8610308511f02410118030610400250206264041c4104040544056183d17401c0b1411402026111901d900684010900d0012940f03203201d0104156400c3d42e500000c820750300c0c20151800c5505132824441e0103440c0c0f040c14002501810000c0c1664051070a500807000e149042c00782c0c04c004c10400418070903841201c21000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 928172553 1250 928171303 928171331
    0xa021b19030e030c0d3005090609040b030d0c020306090303090d0c03092411010603021311090402040b0c0d03090804060305060619050a0906020a0f0b0c0c0303090c0f100f050d 77
    0x500c0c5e1492050001e00f41105100500c02d5212209598400002102e684030f030246030b41000866a1600d41150140c1d0759084d4440000c00905030030071640d40502c030700011001066040022000e419000300c0840d07000da5150780fa020707664801201e4460b49a0404115002c10b07034003440c043c0200600c28104501c8041d25500c0d029540b4020040c210449008010046101034000040f214545030050003441018103540100e8012801250b160b1541c95a5119080c0309003601d4050b0350110348018415542d484e9a90050380440d00b11145980180c0900c80d81511004d0280c480c480c0c00303541c402c485904151a14034190006c1030010b100300e0b00608100002c2682001c160b07203080c1034400d00d848641e101c1e40840e01c01403a5105135040b480c01c0d07601c03080021000c0b400300d41c14019840c0e440500b1303404540d074150364810340d40914080100b40d844040300788014207002290414070b450301964061400320fa588108810348040b2950240803501610b07281201e03a10035001040d60440007080861007064407001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 928173803 1250 928172553 928172569
    0x201031808161208060901050922050705030f03041d040204091b0303030617070b0c07080723011d151606060806090d02100e10050a021b19030e030c 65
    0x164041401a0145078104403400071850360f901511310b01040ba51510501160b07088006014581c1b041802c000055400494210842048200c0300600c00c0031b03404918200340d0720707045805090321a0107440680d2051401c004155011180c41c004403c030042c00c141c0044034003442c0540240e80140d10350869001180ba41c1422201c40d509501143d800039186080003001c880454100d045052009110340300002d100090f0a4103582421010598400a000c40c0354a030508a60080599014a0b08001100036400f051461200e40c083d035010b00c03405854004607030b040798000c108021118520303280c4a160820441c44601c8422041c1c2c482c1c50600e280d034060040b0103c11904540441d01e405003030014100c14400903401c40c13a00d100a00d00200699806919644c0c1d01360312141c900d0350307044c2c200380008041241c0c208102c0341820410031814032052410103544903005084114030024000d03030030b0200002c1d40d404103403101e4410145100180c3d40890701041d441c3c002903414441d400c8060941d5a903c14 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 928175053 1250 928173803 928173817
    0xf070f020a1703040b10050d0206180315011505030408040303050d09022d040504020303091c02040603030e1f02060c460206040f1202151005120304050d0201031808 72
    0x1400d90b101d00c4c0c2407521001c1e0110003899140500f00034002041283ca40500c041e041c1f5030304803000780d100c0241c4042c00210010540304640e2510a14501c10700c0602c0070030b000e40c180c0e01103a9400c01ca0b4030380382030180c900344070070313140108020006c10003040828801c60180640c1c0320311400200e8441d0f80750300024904c6443d003452091310400002442941c40820f100c0e51000d000036903091059240940000352640140c29481c0d00807508040c0c0c0300343c0c54a9680f8241055903008000300320058487c140101308031a044c104c240900e0881c0c420300000541800910040a00d40e030003003445a071281e80f241c5007604004c090001541d2880c1d403416500c0c51780c00c6613605d0554448100d03000d21010114a90000c070242c00d0b55410b5400ca02c5c14840401e00051f55101580e4000e00c94901c4803443c1c0d07004074508500c007050b5800d0040400c003031026805614a01c101100e1003140c4200c5280807107202e194823441140f0485901c442110844401540684c1141c1e0100d4003441c005000810700b41c40300f080e40d0b80146 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 928176303 1250 928175053 928175093
    0x90e030d06030c09061d0103110d0501020a02060717062b0f050c04061a030606360f06040b1e0f030106050306011d030c010305180106080c0a0e0f070f020a 68
    0x500c080c441c0e40d030301784280700c0201041d20105450f0704040307102000710300042c04041c0901c107091200c24a00c2e01c0d26148107820550001c02196502c88440c0b009441d480141d40183c00100c480304500400c03044004050b000c3d0030000c00c00103d69242c0b981d284000f42c14070280d80203000c400352003e000710b9900c040f420031131802280070740329450b040010401224060340110482026106036007080002110030740781e1088050b82e5141d03031010080610108000c02c20b00141e5910140344501d110b41c0d80c00400c0c003254450680e00300001e00c08031010444280560700652500710710a110341103070701980c0700c018020b030f032a4191110310f404070b900500309065009800110210780c0c000b090108950317100722625090100000c42042008640c0002a21040c2c1140c0c40c50415480d84041220004006241d24000742400c00030000d19942c0e00c0754680706c8074004080d0b84594904100002d0f40c40000301d40c0c0c2c1c81081c04010360365059885203810340d07083c40c0c51701702541144076040c030079400141080e18200340d42400c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 928177553 1250 928176303 928176323
    0x509040e0111030705220e18011e2f0f0904060e0a0218011b03140f0a09060801050103110403060203040c050a080c03010b0303250614010e01033e030c03060f07021603030207090e030d0603 82
    0x12f030100000e922001d02c8288490310110100c03c4045980800e07284aa110300070240d0340c6580c002c0c0001c0c042d003c41d400c01000a20424188660383d201a0300410f08122040c0034080d0461608005540c0164408040079500c1480901d06000074480e44001804030070130041d01c0d0400340d140445031045d800042c07440c004541881e070284407460300018820f0040c2400d1030300703008080c05035440c560b45010318400101181c1c0c001c400704003004003200e0038102408006c1c0c50b041d00e07207599001c19aa103c1042509900a51a03d03181c1e4019003008402c45074080c10001841c4101307214020040c00e42d0072075280c150b40c5c095503001e41640440417900701600a1032041540110b0794118100f901c00c06c1803200d1503080d01d200000d404814401031480c00005914110059141462800042824606003040076603140c005d0030b00b0888100c0c410300d1003034042d032a194201d984a80003c00c40401c2900345d0300014000d40c3c803035070007000001c100c5c0d004581d40c89049010f5074140781c00710722100d080e40c100b5041244c41080c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 928178803 1250 928177553 928177571
    0x109080a0309050f0708211c0204140a05240d0c17010905070801050918030c031b0a080d0b0a17071502010c0509040e0111030705220e18011e 62
    0x4100003092101c101800038100c3e0034642003a00ea80c803170030200325404170000c40b62203007480045041521003d01082c0c0e002d4234100a03100c80d1200941c0503006107180d41180b80d045c0d0640742409590081520805060344840f1016414441d110340c1e824140440c040030f0400102171034961a0203502e4100689413910951400c07103002e00a9901c40582002c1801807401c1c0400c03801981c041c1000741110070544042070592200b840038190f03008480a901c0c01d0f4440020703556403070540080140300b0b9a10f500400c825143c28a00d001e80c59240c40c200140492500348043c10041c0b0055210009002d03004140b0400240d03035024080c540c070030f806c4540025030098402000342c1c440138103c0c0a451503403803000704041c0f50007a00240c5a405404003540c09650741c0c0752112640c16003544801d0303003944c0030001c0907100c0c40c018400030329552140340740e075150200d034450340c03c58254010380000c00c1d165031308504400341d078410700c0352000c105180750410500c1d0349036401c404014641100a02910f0b401090104541603 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 928180053 1250 928178803 928178813
    0x4030f1b060302070201051206030c030318090117150a0b12030a17270709110a090b0f0a0e2d010206060901030201020c0d051002040612051b030a020c0109080a0309 72
    0x12954090401c2c14010014400141e030312104648042428610483c0d594807010301182c40d01890303a10b115054840081c45407907401c0e0b206881030282004542050107aa21540c1c025800300107500030b40b40551000f021025401d04840303032194018039141001038821110030024261660000922903190030008030810740507070090b0045000c3e841107140c28843e0130110144004030116011100c011b8511545a505a0310700380070440003424004024880a181211254605d9112203a8080425040c14000500c03200c3d40064a8200c400e0401c800d007400c21aa4003511301800440310a079201070704110084000c18081159580b405d08441502400c2452000191170440050500342c425402440104010f07a0300080b00046ca0000b40e64028810b03809140441c40d002941c040300f104c890002c900410802e601c0200c22198038641c00c3c1c203221a858450503181c0b550f00038241e0a0300d0070310820000b403802d403843c0c00514040d16644000a111592a11045d1444e00000d1284000945900002c000d1203 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 928181303 1250 928180053 928180103
    0xa06110301091a150a180816061d1c0614191401060c0212011416081b1605030d090c0e010b0a030b18070801081b0319060204030f 57
    0x4960804244429180000d5100c0004071041c2c084e81400698641c03440e106100000c1441e0301001c244011a4803110000d48588100c0458040c8400c0c01100260b42c600c0b505014524401c030b4070902410682841c1400841d10701da040941009410641400c0003a031075200f106110003018002c1800750130910200310501c405102c100da0312600340002c1c0031501c0d44450920381140d5003030904c00340d003003c1c901c00310303440702445035414699528205e500300c3c4111040c0b1040c0e11031603615048144017003c0c4142074401640640340b440c103884001043c508403103020002081e440310b2080700720310700c081281c1d0307407d29540c03101c201c0410b8103448464080c00c10202c842a0303000360040c503c28025070345c10030409411074000d51450341c040548886c190b00058640a0400c41c140000310300c60081460007580c0a001d42200303118000003445180c102e003040c16003250326a507421380000c01420140ca90b00c0c0209071800b4842401351029079003017200000003100300002c1214503104101040350325842c07000c0c4000701 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 928182553 1250 928181303 928181321
    0x8041e08070f030b0c0a09120f1a010e040b0a1d0a021008060102030d051504050103210306052d06031614070c031506030204020a050c16050102070b0c0a0611030109 72
    0xb42d107040c1400040e01d0901c80325031200740419078a07280d075001381e4211440902036001c4070300000841c043c842405840381078640d00c10b0143d603003184110700707010505c401c41e0310034803030722190240c3d0b08046000215440b13040c2c0c3e00484521400b18a410301c841c0c100d284482c5030080380703038031f0f61280c0709070400c504089400070911105030500f4000fa28201001139100d2107021041d1803225510030000d100000d21040c0a201d40030301803c10080c42d0307100d14241c145404c024600000c0d584030344504500c001e1080c054101a41d0b0050710003e2a10360110900c100310200b0140000c459003415102400c43d20741002652044512f102d00c10085071060401800100c00401d403c01c01c0c80080081c600416a01c1c40302500f00c070761280d84800c5a001c158131040080c801c0fa040254400d0000601400e410383c4840030707240c4420b1b600155441040103001740c0007202d03114440c00d40560000301042203c02141d20282424030b41010039100410126500c02085a03106480e401c401c09000c4010300104596100b10780311 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 928183803 1250 928182553 928182569
    0x521240607031b03091203030515030a03090b090f120312180604080d2009040b040209090f0714040303080708090109030c02040e0316050a050607051201060c08041e0807 74
    0x70344003840d01c0052001d0024000740d110b00c00561640010140b140750134400070f10784842d140900740d400d40390040181205507044408020350032081c00304e900d80410040201d5a054035410b80ca1131900102e42c1560b040320445a5000712518841d100740d80703c241804502890600141d41e03289040b04001e000c040300608200d076480840f80401e120041c0000e01c140c0c000341c002344515213403584410044084e00c808000c00303500300700d080091541c1c01e14506c050858034030202d800740140300d10013090204902410b02c07860790045000700400c800311243c0b0b0716650070a0540c5003040342031b46004d502e020507a00c00d074411800900c1d141d0800c0051039000f407071250080d40c81d5009104010154900030611070000202900c929030f01c0300304404a040800c201e81604d0401d44003a00074040d203040c03a94665850b420240c8890241c0000116068820012a40070990102c90311860f40d0070208101c0b61030b22301401c00c6035079071010040458141095030448007100e10400f5009046410411618104502036005d004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 928185053 1250 928183803 928183807
    0x181d030301031a1012080d0213170d1209060e07120303060608010513110d0c0c05070902030601050403060b060409020d020d0b060310090b0402040f0b2106060a05212406 74
    0x44e107000b2a011140440703180b50308000d16031400e41070600c02481a2009601143e00c0041c60469185080d1408000c4400f460301c0442c2c1001e1100c20075443c3c0741440e8602c3c0000302c1040f03034282c543d61103500c40d0040d24064180054001071010b5074500d03100850700640c1507040d401d2406800c160b41030141c44c0241003986404c6915514100205010090000c0d10700d81c21a11403000e4100d204a10f4152009044100000d1140200d21503000d011146200c03402d96250242d000042003c00e2540212402440c041e96010320301451038541200621241c48605d61080b010000003a0280366030015010341c101c00040140e07101d510668010458206480d000e014000600406c48100b40326800d01e4115140a41c010130211918030004001f40305980080d02c110f2004c00011580c0d80c0c000028125100003e0041c854001d410254000340007811a1015405202000030314086841107010b440f00c0640d022001d001d2a40896150540601c11507803d4403080c5e081003441c5030f10102c407200707044241c41619054 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 928186303 1250 928185053 928185061
    0x507170709051e070c06090209010b0c060108070506040501050f0f03010923060105270310060e010f050312070224091003140f2d07030c0e0109181d030301031a 70
    0x110a00f00024200c50034440d80460050610102e6004140001d42c010700b040003940e11090b03a444075130086803d02605108800020820f480300180d81e40a03a20024001801d061900004480d580d218000b81803021000788007000244110402441c0038284103400030a1408407000d8410344020141104170140340b04400b40070300740c2d0708281240c40c0310110701c000c040348406003680f030f08004868100303458141c403c0b4200c0961400840d403118003034400d0b40d01c5030f40490340c0e00c409008030184540031701c0344e1581018801c04040845c950041008510250031460700f801160100c218002c04400e11840007480060014034030300d04620000b5485014ac18100108800143c0400307103000000c0480c1c1d140711012000c40c01030400916500c1c500300c0c132165409101c86070060054124071081c1d40960110f824584440d00941c004c0c0c409025460041e5202260f0500e00018400005440ba2011840d560303142900c0da0201d070110303a132040554101c0c00030b60b500c0d451880d0450006818124210100c21058140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 928187553 1250 928186303 928186351
    0x90515040e01360f060b01020d1404050103021308010c030b040b0303070c03020d03050c0a08071106030402130c0302090604120506010b090d03050315060c0604050f28050717070905 79
    0x20122003810090841a10b00180001c00c1030350b003c1e180984580300005543e03007004215004850500000e90035901c40d100c48542c00c0c1c5940175010940300c00407000f884103100e503500c43e0b8080d103500c0302c80880400c0100d98840e426801c44280c803544c40b00281d22a11145103606207400350485014080e0000d615264040d25141c5c1c10384132a000003403081d0380261118090500c2001a24420f403004025139003e4103451070040c1d042d80c415281102c005000005095051038480152441650045c01800c609042c02c210f45004046000140003410303401d00c03140b21349803560301c054400f600c0003031b00350030344120181016440c1902c1640407500440d030412582e00e260300d503803210495482d45801c00d01e440c0c0e214a0071a15141000414080d00400c0118480082000c00a5001d00450260059480c224550109551206001a40c042042d8042900d01c4901c402c2d41605030041c50042c1c050342c2c8825190316011109408801d812106c9074031652080c410f03000030b84a241e4020030004a40e00054400d1640 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 928188803 1250 928187553 928187591
    0x319020a0f05060a1139070e040510050613150e0118060503061536060f010c05030a0f05040f080d02070915050409030c0b0903030117010b28090515040e01 68
    0x243d400381290b01b10250350001680c0c021901d0211040042d644401d488030745d11944408110317020341d03540c49000d940001c400400c0c4604c0307026203000790880840001d00005100a0040c0c00c650000c80800c240e00014403600380e400347c502030020210702c040081d003022142026503003140c200c2c910035000031083c002c08500803440c83c9162042502c00503e40283d1030084101c50081002907a02c1d00d180c8840550840c503080308444c440d02017210514211015030004542c0c600305420024035651080040403500da0248a41001d4086545000c51070036403520852401107803141d1058080d0f50091411141040d0144006800b610170050208071056100340e0b4402000514030442d03018030350f01c1c03031034806141c800c2c1d0610190a800c00e8001045007031500010b81d50794400d01c00c1a0401184008036002d0f18410f00130303603440d4000204114000a000c0b40c00740c205012000e0010310101d0420000160780800d4000c061050b803030401d4880310a842078062000750350717111040c000c50340d1400101041c45000410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 928190053 1250 928188803 928188847
    0x10605011805100516030309031704030c0b060f041407140a02030429190e0f03280b090a02150324030709111c020405030319020a0f05060a11 62
    0x324044600700c0c4a906440e5481000c3c1c002c0910403801703840c60241a0940c2215030185e00c41c0c1e49000a901ea80c0704203080c50b003002e40d07000f8002140a240d50011130701c080b45954122038004c1041d203141ca20303040050101d6800220400079580082c080200c420303008488500c4108a034000140f0303203003079000000d450748510b000300c0c0c84e030000143d00510310391040b6601b618003040f8609140d079130707100188010324440155442d01c4002400c0751440221410014044040000060014216904900803140902c02902440b005007111020301380302050b40460014082c02d9206d01503c0c003042140184901034664024410301c2d90410402d10003000b040007580d094855400e03080b01503807100d41c00007a0a05416600c8415140d0800c01c2c0000810840c50040c40c0d1802c12201c0070242c1058244540268000c07442003681c907810500134180c1c07801d9190320034025000c45106541114031650303241644003803002c81c2554145d000c2c004001c0f20f90308030b104d5030700c1804040c155217040c801c042121075408178001c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 928191303 1250 928190053 928190059
    0x15020f0307140c1005190f120902030111120a0506040b09070c050f0d0302040603050a0b0f0d030e090a0902013f09170705070902040b030c09030f0f0f010605011805 72
    0x14020b0740b4548024070403c002010300400340481d40510082c0241160005803420a0100421100190481c09080801c501d03421a40304d4212060341c05c10301c3d20081c01c071000180d80654a42c01c1b5600050347c910020001d40c100600405141d0078200135080c221080100044c1c09189052010121680d03504034603580410f41381380a020f00110742c41d00c142004000c01402c2d99070b11074121068030898141d0081e205881c0156030810a0360760340c03644102507078014400b0355042205c02c441142070741450094000d5184c00703410f000c4905468070300840c1c40050102c030b07407c04040d0b40e000c040b0b00310f41e4000384442580c04030310124400c0210041d20017803c00100340300c031034242c6820050108440c0494010010150304812190060186d00301004030320345c040c40c0101d409002c2c902e40440c00070014805d5030240d5800300c040b58155903a400300300e41107501200310207078148207030001c0c0580e9013010032010710807034140c00191440c05688d180044c00d40c0c1e002c1d0041814080500c4414030201c1451410100b114012 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 928192553 1250 928191303 928191323
    0x4080f01020f250b0c09040b0603100924060201021c051006051c021801110604030e040c0e040e0c0111280f0c0608160e01051602030c06070c15020f0307 67
    0x2101e0841514040450060401c0060420008401c001d003001d0718141b04180c03401c2c041c2c2d01004c000c2140e2484101c40e0020910540713401800700e2102944441130a407103900d29684205100c84c208085100c01c0d50003a40181c4d000200b1209a455908000700b81341c40c209400d11003401c0246d08926450b05900582d400c1140124030b81405400d41c84110400116080701103645620407404403141c18410f203080760100c0c0c0800400c4061000000d0320a106035010ba41d00041c0d140e5136003c0001030003d100c2c0e94003c0141d01010380003180c8d901c0c07044041c030740c60647c000c04807201c004002401c0d9010214003081c940d0040c07040f810707041d90380340716065070081e400c00b140715901201c1c03504140d41040b8800180105a143c40003180480e08200014069a50007410060440707042404881280e82d4001a070700003038040c040030400034050704419199071720080c1030b1108040704102240490b0842d00c0180c981142400d000c0010001c180019080f02d5034600c050600c6003050b00070742d5940c1c400c44a00030810106 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 928193803 1250 928192553 928192597
    0x30705090f04020904291221070b0a1d010b0f010e04110a1d040603030c03050309011b05040303090f061403090309040903120510050a052101020f04080f01020f 70
    0x30b541c2c121145003400400400281c4054003521118617103001a501000d045030000d45840d01e0021300f40941020303451f0003490100c81401c5081400c1c2411506002504014040b1000168500045600c1942d5810000500c0c60158074520080240c60301a4185039250a140c82c112741c0700c4080c91403022000303007019900c86030550045001415942e019060062000c280b0f00b40c000d0b8800c1c045030f01074400d41e0032402d15a03074080030001190f41520004010035030301051480002d0058000d1030b403103901c02c0c0000505401090541840521182814002a80006086c0100741e040340047c1d010301280c5005181c21401c011015040038000d03a4400706180c1d0100001d0544281002191a110030143c414003d181d01845c4c0139001c4400e03091030150017402c04000504030045030001c107045031070041940c02000d00d0141030141a150700c40c1c80700301d610145108d00080003170074001410b4a030100d18846d503440c1c2c40c02078035601740408020b1007082079004116500400b9522001e80c1c1002c1200d40000344038080c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 928195053 1250 928193803 928193809
    0xb16021c020a02040c0c2a0614160318092c070f090506130506090417040306091505180d20010f05062110050601030914100b06030705090f 61
    0x360b401d0003136101e03040540660b8456401005984018401c10400c0c541c041003500c44115042d090040f08000c1c00c422108000740c0b481402e1820070405980035181c50a000700300c14002c80c254030350080d408140c80c1e0800755615031002c52800000c0ca4507130303000c0182400c003125140e00c0c0c40390b5060490740b2055800d448440703c0014842c0600030005808050510365803603804e0009071104071201440340540084000742400e00703000b0302d4441c28000741028166038a940c0d4440c03050003940100c0f04007480501001c0000341c1c242c41800c1c0b46e00e004134070110f18400300d0841c1d04151a0000c0031590780356100b0a048820391000070781006009003500309610610401c140d401c031a031948116803a4590308000e00c001d600200c80d07100b80c0c0280e5042d14001d0501c0380d8042c498814080020b10940d5135131051650b01000d0402c0d50281d07404c56030514020038189851b40300c449034034601c1100080690441445ca0745601428801d091290b4001c1d104207083d85841e000140c5140a03044006008803000c11000000c0d039 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 928196303 1250 928195053 928195063
    0x12210b0310270212060403020c03010c0c08071209090c02030904180201080c071b090c0f0e06040b1804050712050906010b0714070806010803070b100b040302060d020408030a0c0b16021c02 82
    0xc080800b00c03085c03841c2500f4000d640b0f0300e1402c0d0aa01035403801540e20a418841c814184056403c480c80c41d1a01200e540c440082c0005000d02c034040054459021800203000d014020030b0308016401503841d000c020301040100c5501c41a003c0110b1501031107400182d0b00807a155901542c8003050640740c1040341814851481d001001e00710340e0b40415000300310755140f41d202000e88c4281e9034407001c480c89118000d0756a600007221440e0300ca074003440204024a41180240a01144070811800003000a00800d05a40040d102c240200d504e820406e00e04521600c211580101036100408065250070070518241c850910040c0014200d08280c5c2c11003181000080001c2019804941007580e4410780c064694001c81402ca5603078031044007141081c2c0a01c044d0b242a1420314a01529140c5141c0c2000380c0b5602619854010540a200000365204103101070500d0209680300c800300b20300c19192902c24803a009001c40c0c4244c85c81100c8490341a400200b00e41d000c05030503451452280d1140003642b800c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 928197553 1250 928196303 928196329
    0xc06070209131a2706240109080a0308041a0f01060c0812010f060f05090a091808070c05091312030c09080a0602040e101212210b03102702 61
    0x10343c2010140b0664108000250007000d41c0a81c94101410261600701e4403684203841a0000429031901404007001404824842e410141000c20442c1d0b5580b203910f0410903801810f07408141010100414003413281c041d03401d184464000225186489007504010070341c10300500301080720381c2d03008408204411048134004550711109101d95039548585091040e054058140001c1e44100500078040c01041038800400004080c2c982150404880c40d00510040b000b007407a0045035010768000c103c20000a291490091010300d041508190621006d2200509038110104100203500081500303000f4024048030907203404100400038034401c40b10b048194224020902030711040c00c0401045074000c0045400ba005803003115900e021000e0f8405409100308060003017401504000515850760f010000260382c00d20614803d07000c203086440300302d00b004140500d5680c420001f002d140400c03000000f850020024804076131500c0c84120b4408000c481c0452086d000001c1400310359603440038030740c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 928198803 1250 928197553 928197593
    0x304080a0903240f0e0a020906150309100b120316021f020a1a010605041503180f0c0b0a0e0f0303040e040b0f09070312050a030b04020a020304080c0607020913 70
    0x401d603814541c0007180301c442143d28841d034030f0000c0040494000d40203a0120f50184000380251403d142c00b8898001001400c0c0c681c400c103014880001090564091130107520304500030459099160415011100003c03a910700c6005101c1a000c1d0240c8001700315401d141d064081c407581d684e81c6101041034000c80d5080d1031241402d04150031100c9900180710750540e40a1580200e1640e0040c8840d95003901c28040c00c80041c0c07080005110100c0d441541104c0f03d82d15240c00100c9141d400c5201d82040340310403080382d0a02c0034071580d6060014046c1c1490291100002441c6807045c00381740a082c032040d81a03028000c0321084000c40071541c041c0142c0b8024a680e04141101e80742903e45020050800c48421a886a44002040103414002003100a072640f0071812210601c0340031301501c054005c0e50307404d006c0603201c0341061050b480c1da0000d802e510816030002d50310340e4280702c5100d05210b41402e000d0300600060080501598480c46025085422000390b0002e09c031035800d043c0954681c021241c10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 928200053 1250 928198803 928198823
    0x190b070f08030112060f0e0a0201110f1c020d031415010e0a03060207140102180f040b0a06020106080c0108150d05030d020301120c170c011409090a05070306050d080304080a0903 78
    0x2031000640c2c4d050841452003000100000c0d400342002c0c0003101c00d481c50301d91203940002d02d5400154040c0714400f06940100d8100c591180d03d0100280c42c0000b5841345078a8039403410b1740c00703002d250100040381e401e12860070240000c002d0110100030722030300104081144254014141041d034040c40b0451400c0402074070b24045140c880c10030b880a9401150308403031800c03680801c442e03c0e0784180b082d1402030103641500289100505e040106c0501c3c1d0100c4a0b41c807031350741c030002c0c0daa69407a49404c0c40180100c4d0000b05a09240c91045800d14149208c2c160600021104000b610081c50501c6982c040045498010b12700c8207052003460340c000c0815880803176200000100e40300c40d0b888001d40a0030301c2143e42002c0141ca070414032070201380344411010a1f500440da5008590300547c44c94041c5800d030840c05003841c69400010f01c0c00101a00c0080f4840c1d1740744107010420b5410700445000d070005841800d03900d412642c421905110003800548240e0000c0f5440c06014451450074000f035400c823425038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 928201303 1250 928200053 928200059
    0x120d0f020c010207020a0506130b09060d0e0d1107120b070504050a230a060c0209190903090314060606030106320a080a0e0c0f1906090e0105190b070f080301 69
    0x30b4001d50003e04140c3c0304249004000a240c07500e68100e4944c03842c01d0000c940238520f00f2806e00720a400c101d6005074040e0b030030b000c00320f1040400c0c407031080c03040e510000622002e0342c2e004000c0e011340c8000400380b9094003d00400d00130a402c4002c07071034002e54802d00204403540d0301c000444007801142c0005601c861a4500098401280384040038120503040e100c1462204101c100a62022684214000302e10540c000d18003619046243c180d2210154410b10804d5020250501c03c60303546c44000c83c04290300e1312040c4240071070741000507827503801c4100402044c241403000541c0c074081441564100805070f540707440e002904002440411004982c111926601044600100d03000364030f00c080041d07145000502c00e0340d20b42c020410001d0b01400640900244135060150a062000c1000d811912420b0001048140441d511000b446c00c1d44e5200c44583c00d004654549103010780c002d601c1030648040601c42210007044401c122112403111658807043e40c0b40a40c0e007500d00c00c80190596078088000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 928202553 1250 928201303 928201327
    0x30c0c01051003150b01140d3305060313120e0d060f0b0a050f010f2c1e2b0c0303020708010b03030f0d05071407080a110f120d0f02 58
    0xd003050700c0c41420750f0b9000203003100844c0101d61402e440e540c00128602d049540340c10703003031008021441b14503401040038104017410692100c00344580180a4005882c0502c6158004115802504085415520f0f40c02c003c1040140c0100c4440040d000e5845a110504c003d405484081c500e1200504413a170300300d505003031035001002e20010100c0c1c00e50410710051801c0c5410386801055447c001d01c00c5007600b11040c0112452a080f03584102480345407503840e0122064261030130032582c03e000e0b4074140d4984003401d02481c0c4185840a030b2100d0b0510b03014096a58a00783d807241810704c403101500d403a0311a84140c1c61214044640034140080b00030001c010315a01164510540d400e040003401350f6034100043c181c1c2c0b44a41030b040b40c41d44005200c1d03240c0c0141240c1185030881210302d0400c255203940d83c0c840e050341c0c1c0540001c4403100070020300402d030386070010324400075000f03000061720780e016200c000e950700d801c0071441c0340160f82e000280000c4862265400b54102c52400601151140300d00e50304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 928203803 1250 928202553 928202581
    0x61201060902250201080c0d0f060b090a06181203090302060d2705030414030a080f070c1a0304150e0d0306031a01030c0b450405010b0f030c0c0105 65
    0x1c6014801c00f07040081c2d110400042220b6095041c0e603120000c6e03640c4e214411281d00402c02034140e41d0b4458444102107003c901440002d0413040700b049552704011001c101c1d4440e02a485101402185009950000300c0c264000b012204a03c084e05641d41052034100c0c3c907404503410003503011038049100c900c01541c6500444088031b481c9504500e40c05280d41821a0f000320942c010250361003007209001074210308144a514a5015084a21008155440d21071a400c020114048c4d84004295501484a08510300008141700b00d40201409038994070465035100003800070b404d5039400210484542110b17402110b42c0c409542c00d5441e0707001c40c40001405064507100980d40901c074168407030207036900c011205040783ea222014007604c13071801082c0f088941044400e40340518029008105c903c5445054030020b0f141c079140d004150450350b0401255001000c0518081c03480e16005012201c08541100c4c0b44603495640300752684d5840094240e144500e5450024550038141030052032141400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 928205053 1250 928203803 928203817
    0x70807080310050f0609061e0f0c06060a03031e02250e010b03160c11040207060203010501110d0f1427011103030f06010c0204150b0c16050901060305061201060902 72
    0x40c0c01400d81d90f5401c001c079548592000c958452800c00c54100c251518100405035030b1a040c40308051080c441c02d520fa04c07a00441002555410001581d41c08940d0501c5019401b01045455458647c11910300800000300a4049003032045902a103950903802040a00d0082d80305450915106a02500400e03140e00306100b41c0307030b10411407000401e022401500f540d104081c0b001c03071503522800031802210000c3d41540301f5250f200280c00700d15060b44490004051141c002c00b005a900d51410000502518400400c4c180b40d8001c5054101c03440d5016002e4043c21010303207450020349807840300c40e00d590321a2140c04085c070010142000d007c040c0d44601805480c3c4262282c8460600e5110115180d01c801c403480e0100500e0f24000440a6004031102d042690000d4400101c4035101d4480142e107080b160890540703076901250309130b144402040a100000002c2c20315003d518509000b0440d224810f005090525440d0400140d1a0301e0702d809104201d0740c070030000d010050340c072200c22000754410301c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 928206303 1250 928205053 928205071
    0x1208042414041113090b13020a031a060a0b090121021c05040501050f09030a12020c0f0703110105180d05030c101a180f43180902070501020708070803 66
    0x8413401c04905200d11030342d6031842c0c010100d40040d5a4080740c03210401c0305040308070381c4812455008004112001501034820040300c404005508046041044840c1c2130b40c00411134002c01c00c402c0150f03990080b8170175581044402c2204020b00d40003a41d00c0680559042090015000c1c1d46101c021340103500320b103010364081c2008000e80d484a100d80708c00c01a040302c90a60940c0100f0205038410b1080701c8904420754441001400c04c1242401d480c10485044800002640300c00e00510500000e00040710502400f400c00b2803914500811500203604c015900304e204048121101d010300038184100d4490f407680100b07403088405880310703c00081007080c00c840c514101e800c00c000c0c014100180200f07858a0f1f5180c110816a40d03d4408039021500200562405074940b81000360510800c0b007a0004507030803089180c1804110030708003e442d041d0f483c6200400c07100b800c0441c80700343c1d81c9408c002500e864150250307548031103060040c060710404030020191900000c04074203200c00c40c405940100865 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 928207553 1250 928206303 928206319
    0x15080406050a0903051903380f010e0d05070506030403090e010f061205070c020a06030f0f150b03100e0705090102010b09191503020603010b0712080424140411 70
    0x40c00307100045882c903d5006000c2a010013040c40444240c0022900c114404d14010500310f008440c0f50000050444040c0d401c1803c0b44804400041c1868040748081d0f000e6031039000c1490320400085c820208822005d01520403c071010091042c00d01949000c2e090250906940e42881e1030020110340c440e2042c0d007e1100300400100740d065440b241182200c80d540e5507151407018100e0420b00504002c3c2c683e0007404080c1072040d00507142c0ca5031881c01003149440c001280c4503440003120513140681c2c2d26000861404074101592801c2d24100c1e41500c1e0f40f541c0c0d00e038880e6070315403444101c10f040350804000e0b01491810812000e500c036000341542e80c0280d00a000420041060150034102650740301075502209441c02400142d0303070b028625200b01d5054100000d0707940d8000c107019900a07041030080d008009007200038000714401301160000e0a151052103072501e5120000c006031040c41002a80800703c048500c0e40840da00040c140340c07800d5640c4080e6080038038020b4200001c081c1141e02650304 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 928208803 1250 928207553 928207561
    0x50f0f15071409040b1008100e01030c0b0f0f0c07330302091305390a03050408220e0a060b092b0f0b060a08030912071508040605 57
    0x1142080340290745689400c014610841d038004116001103503500d03003080e512180841c803969262016402001ca5403504001410503810f00007920707590303030041a40c0450180042001645070500c1c28110b404ca064440e4a4000c0c0704003400c40d92060040030300b03107842c01090346070b5185400b01d050301c200da20200000001360076004080d00320805007454402103241420303a5020050080e0006c1842c5100100528169820700009000310303201a5520103901038500c04484401c0c1e00001c202d00c5076000074020b59070140300343c0b03070790000c52103041c1c2d4140801d922240030504200c450000e55501010b0300c00310400495a10041307610b1120584101941c92103c07801040d064102445106d0039120a800719030700d000d002d032050008682d0111840070401504180280c1c484c08641c0600301c89500c14610700340040c1440c20503403600b00c0040c1c1010300c95582e41c4010001214004101c1d807580c00b00350b070301b0340c100110f4000c190b08000c0e0b03640c0000f420802035040700074032a44c811403144c45584110020441511 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 928210053 1250 928208803 928208833
    0x21042004090203101d07030b0f06061c09020d14030703030b01230912010c120c09060c03030902150a020d080109050c12190207140607021f0207050109050f0f 69
    0x103419071000c1d4041d0410f036810341e00c00415801100b89403840700100320254009041c07003860401554002e81c0c2c020040828055401900381e1019041027040b911242800003003035040e090850321805821105540d00e140d6801c546440310030319460f94200301ca00080c05e00040403141c59074410101140003e240548007845580540d4044001034035019410780b50a11f0068454210351180000070b034408699501d229011201f400740020044541d80d9400440494501102c1070f107504008900c00d21072891018803030503600038070a550b410f415160201c1e0203005030021901203401c100c13421224840000b0082202d540001c2c40c1984988a503803440c041d60ba965203220100c4205840850b41c1640402030052090210f407074064000d001c6454005081201201e40012603101001c112a4861030040704c00800380b00788071045c0e0201182c0003401514400101c0b10380fa0020b050010004154041504401c0c040e00f54000c040310703a03100c0c04444c030312001c0300c18141c0d03246550807000400c0e11800a104103401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 928211303 1250 928210053 928210061
    0x2e1508040219081002090607020a0807060207080a0305030601031e050a021804050c031803160c180203060d02100c150b1017040b060d0b0f090609010606050f21042004 73
    0x1c0d40a409413281c844203480110281d03001d80200b5a00400901920f0301680c0c491b03005400415198000301003c40c64107601038140b955a03032120505400c40b4102e01c0103e40c1000c202c0350f11220920300000c002904d400c80300413104031642500000d5281204104400c4115801081143e4211000c65400d40d100c5040000303803001204c0d50300350a8014800b141c40c3c00c608007241200720304008107803802d140e550500300042c028070f50341c01d41e84004080b07020001d000b450b00d04076030ba155030080258514640b62000c90b15201440320024000c0e5058000b8241052040020704c024a51210f00c111640d48442d55400c090100d140c400c512680c1043c02c00c85905000c0c800780c004110900128401640d1340c1d880d581c081690082219402501800c4404000b4910011092040c880d6107034044040c18440351aa241510050214145a160100a01981c0c0c0c00a09031030f600341900401d665600c19000001102c0c10311801840313000e42c00403062000700464514030114204022228145070020181084161 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 928212553 1250 928211303 928211309
    0x10506040c0507060504081902150a0e06130c1503050a0c110d030207110901030303090b0906090c060706020d110d050915010504090309080d0c0303060e2e1508040219 73
    0x841e508200640000302c540d040350341d002d4040d1f601c941c240008600700541c100001022400103030130019580d440c806d0001c0c0e0140e0812080c41080001803c0c201e04560f440340d014202440303c50104411000b0001c0c4c00c4014000703031000074001c200052218401030060001603401904c11410050103c862905c00c0c4e09000c8804800801045a50030703181e0268000d43c8070346001d54601d01c401c100b07000a512b95085080c000c5203e6600003450200c2c07800c0503078414401806458a58024009004c1c0b90000000d401e5004802120b03490350b20002442e0500c000e10880b114884c145080800214a031070018000c0d0034040904a130500459848000003500c03070485080f1491403c003c02e0040c4100d040c80c1d408a20704a00c00d042c0764190940343c4284a01e000c2503d00e0200001d0340e841c0c80201016410300408004040b000001401c0d824281003000c3c9804100c18481d981854103065200352880c80c9d0092402021884c00000c00c00c809000c0060982504039403c0e801050002810800400103d6440040b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 928213803 1250 928212553 928212557
    0xc0909031e0a0c020904032706051c0b0a030803040302100c0807030207050f06190b010e03060406330608090a0203100b0607150b0111030c0a030c0c180e010506040c 72
    0x18a44909100d481c5070445100d010410400d10a40d0006859003201c0c2030041c2e000c1e8441254520045c0d5402003081e002c81c003c40a544907505080080c0350300501078031214110b00e00409192658444000000c001880080d548400203140000600000c8002140140d010b0741c00e80d03010361400c085002c03d0300d080d034900368000b50031900019030303c2c0d219601411615201301c0548a0400038420070070b00c1d003103040d82c0244080c1c14080c01c000070381c60a84500c0c00b07224070a081605440e844000042e07107a0200400c0a8801c4c1e495003440c9103114140c82600c501c6104180720201408100c1500032914283c502508012460010118007c2c2c0b10018080e503080d58010b0042c04490b6030f00100f07274090860f482e40250407550902c0003000180c1d40101c5403c5800c8500b400203944140c00b030006010240060003804903420410018800b141c2c0441d04042494140c00c00e0700b010a00e9141400601c0843e92001c0700300340b02c6c0f082d00510310000c0c0c0c00081503981c2d00340017400203880b41d00410080b42ca4007421040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 928215053 1250 928213803 928213837
    0x1050702030a1e110607030f180203100f14040516050d02031f0e0106080c0307050109061d060f0f07060615090e06060c010e061905060a210c080c090903 67
    0x7003030000e94403501c2024015103001244401d180b07040601d401c40c03c1c1c8500d4046070b2158541c1d2340085035481014200d4009416010440002ea00407030b0700d40c40b4022000089580321160b1085144094201c0441a01c5101c0201114501401d1040c2c44240508260100c0900360700700180038034011510400c0345070010058000d5200d041540b4410104540c2c1d0440c0203a00d688a03201e0350038003881004000e0031424064402e032071142c0d040504102241d0405814000281400d0151a80c4100d04101d0421856514401d600314070b030002d10075000d00c0c2c1c190207400707170001000c1492101e03075405091007510501080c00450380b00c400d280c00d6044000718000c001003134501c1c01c110b0f80036200c03000e6801080240c0381c43d00c2c000035200f805082d6030128030b0b1382d074040d032214051020a41442c000d00482d00c0000300d00300502d040c03810000d10709070258843c0c00c0c2204a000b080006208100d2001d210341a031000200342103503034030940642c6a001d84050b852003840030170300003100c600001c01160340e04441100000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 928216303 1250 928215053 928215077
    0xe0309150c0c0919051605030c07060b060d141e0c071703040f05060c0711060307030b04060905150117041707080a031d0307021003021b071202010201050702030a 71
    0x20420303401c55061608184908401d030803103600d4159400303010b2000001c85103807825004030f03890181c400141103944141038400c640b81503140c0c09000e481e04582070501499a910860410f00040d150103035a0b568000e000040380e10720a29650300c804104000c8031000e840595030040b04520a96000d01103005c604a18000908602100802411f22038401c0b041c89a92050709100e414180d0401c44085400343c180030150401e02108000c25a40032030005029450142c01c0e0f502c05400e400b020404074003030f00c0c002c004180243c0c000e401c0350100368006081048201d03610356912019210540304070320220f03020300c0d1801e60b651043c40d60026041011080c048591200e55903019030340d4280b910010005828040540001c1560000f0a03a80c211540d010889044100c81c0d010043e4102a1041c0705034410001240162118141d0340d0001c2c0c5103040050f180e03c5440704010124125250000050051010114209810392203120740c25000b07a00803c0701d640c2d40541039a4900c0348049400c0130810700c522903 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 928217553 1250 928216303 928216339
    0x190f1d04030806090912040b0901021c0e040f06050405070f140702060306270c0703030c0504121101050417070906050d150c0c150507080c040f0e09071a0703030e0309 73
    0x340d044038082c02210b105085071071b00d03010640c01540054100c004002450b000f5581e04111180140c0200c0f404003042ca028050007620038100e5070000c50117141c03030b108208005501135000c2801000d020700203001c80d20b80410000d291134401c410039800f01c0c0d036030404408055010300070346100b9503024bc41b03107140d80c42c1c4000b007042c03005000481c0342c0000b240c401c0d80c90101c442c00c5440e90098141c0007409880d51200e00d00507080d0340c0151841010802d05210412113002e413004614401d0350420503d10900c1100d0004076210b20130ba800c840079202d80003500344000c50300010000b0858408a00802c410358503030302049003089000d000070f00509030034814170490701065402141c0d0b124040c207040719401d00d50b5655205504c0c0014800310305035503c41c20003100c19082021030b9881024819928505800c1451009681035140144000055118000b503521101004114060300e880c5030900c2c07811034a4980300c1c3c030652103550100c00090800706500451030002003136401c1e10000810006204218100d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 928218803 1250 928217553 928217569
    0xb0609060c010905031314030118020103020313022713020105120c070f08030a20030721020c060612010b011d011205090106050f0d0b070509190f1d04030806 69
    0x1c801035589801c541e000801c204014400d036000c034041c4144091800d140114501001c6002c80d000364146441c2c0c15051984600c0c1884080d42400c0c01038aa846070500212180300e241c0000390801f10340c1111944841c920000c00002e140d0100001c800c56441403420111444918802404121f060100422040c41c0c180800d43c410040c4104908068035525151510780b1500b805a90120f4000203001d0700714003500620f14903e1400c0104e41c201c40d030190701010300b071000034200c10811078581c01001e820200704070b142024541d018410741d29042902d0340a81c841c082554803520503040001800d400365810300030302002c11416100c40c4040d041003410042c01030710402c8000d040081c1d20100d44800c0c441032051030f00070383c215000041c0341801c0c042842249405100000e02c01c20302d00c06d410000414001a956010b4003034504941c0b20020280450050301d9107014000b00314180000200300e8481d41d0300900d003200c880841242960a0b40700300309851540130f550185c00034001d04002429801c10080d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 928220053 1250 928218803 928218817
    0x3010b06030424111b030711040203070201090203030c010e012301061209050a0506060a0911030a09140304240801031203110c0733020a0609020415060206040201030f0b060906 77
    0x3c10308074000e215240d10b040b00c0c8480d80e00f804041d03000c0303801d00c0401d030320303200c85030600940c20b008600d07184841d12507000700d010b070000942c800c5400200184520703200303400000042e1381c09001c482d220800d00603403a000c0e0581c90024100ca61818641111400055500708140c040814034550240d0070540103da91600a105401c40d468840004400113041001200c2059001704054400e50519a040106803049580910a000d00b040d0ee008001040c203800c0301d421010314100020401d2551400403003180b007a104c0340c584d6001c080b90020700300001e100446d503103400d9010480b2958a483c00f00ba0f0340d1520a000141000031022000700166000b5400a00e10f41c0e07a040c160340c24990724940700f92a12040350040c0125446220070410b840000548039004142c0201800d0010002180025510800444c020301000d85800c101d4066495543c042041182c1c501180c41556031100000b80d540e1005035812030000340380074025803e910251180034100540140042e1414103071008000d210b822041c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 928221303 1250 928220053 928220093
    0x218090c034510061512150b03040c0b180405070c02190501110307121803080414011701291c090201170f0601050c0c030f010e01060503010b060304 65
    0x8406042c818045500e20000074007101c2c54110b40d2100561241c1064180c00c41040d00c1402c15005110f80d1510141c8404000c2240c40c0c03002c90030309611800d1015080c01c400766811002c030383c1c6011480303100c0e420055102d1405605002003072692403a294440b07106100d00f418446040c400364410034905900320300c0d040311251070454000c0041d0b4000a00d9015076404102c001811020100020750700301c2e06ca4843c1c1c0444c82c0203142049400d80390100d88250305a5404100310315501855000458600e054014540010105488945541c0c01e100704101110403a40415400c0e84201110860050700038180e40e290790109107142500204980d000100b05100a440d9600380068078001c4095030b880500400820310205183e0403d000151862540c1c4680200714428141005240c81c40c00c5c0c0307015003100081c41d18683e40c15190011a041c103041c422042e5040c02580c812003030400341508a40e080c03000840080000307507900c01c1058201d8420100b12a040f031820320024011507205002d01030070203c41 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 928222553 1250 928221303 928221361
    0xb04020402031e0f090f073f0c06080105041a010e06071a040b0906100621020304061a060702031509070e0f10170c0f01110d030218090c03 61
    0x55080750211210444600004d0328005080000703450042004903100011794010301000742c00c1c81412400504030b41c00b83c1e0040ca0b14442442421450800c401c0c0803805201d04007044400c04d4584114901e4581c410000055100c20000c94546018410038590718403038542c1e201442c0c030040041d50220000f000c80c55100c4400d00016010443c902c110604001034a20321001301d24251410b0703401c40201420b94902a8805030821441c06107113403410f02502d8181c10003409034071801480c41810319107442c01040f801e001000f80300401502d90000003200c00740340801c0a54072481c4080c0000f034000d038040650305a0192908401550046000742d0f0404220400d442401d6142c0070012207200c4242c03800201d10001800b00200308281a1100380a040c000703c203400a00f001a12245d40c64044642440c402e1101c0070060034168000c15522a08110910681d600282000809002074001c4500340c4601c205c3d0710403a07085c034901007a58134030594803119454210b8903900c0da840390b030214120f0900544010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 928223803 1250 928222553 928222591
    0x200a12091d0a0606210e0c21010c03020f090105071103010c0504080c0603161b0b070306050111010b0102060f041506030f1103010c09061107050607030306061b0b0402040203 76
    0xd10905000d045081c06441000c5003003000c1e21808490559204d4030410001c400c0b44011290001d40c801d4082d00412004102040c1c3e60200c90f00341502e06400d0742e4000030002008620000c3c0e005910580c24800303008002d6580555002d0741a8400c1503003144682c4000c00640b4010340c002d0002c0c146050182486a096000c8030b0082421114100101c501180010404024440041040e44026201540c0207800d40c00c01211500e9001900f40000050110000031406001c40c001040d0111580100f03e540e42400c00583c0179004000c140550744c002460f11b142c1c04007000050040c01c026038011fa00500003a552500c050304020409042103c02814003941d154203044d803805444055802a200420310030118500700c000400c840300c00134000d034180b2410311442034001038084100c0d4142c0c10440c2d201c10020b0041410210943c2100d44e102001056010a15a040d03100d0701c256611511800443c0d011200542940c0f0749120f40101400ca41c840010300500707054000e55001300b00c02c039484982000e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 928225053 1250 928223803 928223819
    0x203061b040b160b0c040e0103080a0c06090605180a050c09041e1b1205120a170c0301030615080706030908160b0402031009110418020306090607200a1209 68
    0xc0700c80f11481ca0840801100c2c014415189101034004407501d0300d00740350a213017080302011100c0511024001c0c8201040303001440c0d00590300d480c940c80d440300041102c0912450410001c0c113080e150345560b18141002c1030740d03580780010010b036001d40210041c4a4617000108000200134010400c0b2000740000401050010800c8c1c0400c071071502c100207120070340540d00440c03014154694082c4030207603400190940801d401056041d00d5012900341d196030b41b10341e880b05a881074504418822503490210400c40c00e5501da001641c1a07a100c3c40c1e06220560502c0449007400e40781e030140785050b800c0b4a10400405000c0e03800680c4851280f50240e0620142d080744010f0458045019a03403400c00c107003040114502481420161051408104014400c40d1502182c44020103460750042d59151459003d00b02041017200500da801001c540c968a001ca410545a08054882002207008050503170544442c01008400c501441d80040c140b201e000e40705c41c0d5440c41925401014801e0204002c59420 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 928226303 1250 928225053 928225057
    0x9070e0d0b064b0d0b0108100209102f010c020d1d0405100305071d25180f0b04030516141014030a0905190203061b040b 53
    0x6030040d110700410345090014422080004401d0051200f0303441c2c0c9507008420903000450702d103850f010008481c0c510006a88400d05032503240380d648400c41d41e0708001041001083c0a0590324124281c0392400c1120901c0381c20b07405180b5074290f102c40207115004046101d82c00d0b0345411402046000305400400703c80180030045607a9155159441d01e400b002e15580400031041c03801d07080e140640d03203007400702d60307907848007959000c000e2040380c0f940049240f1130740f00d80b81d00c0051508602521265580c0302d4a00d4118400208440260008500042c51407040700103191804c540d04594810308611901e01102d048546a105101801d4001008960800f50400d00000342c0299120f8561351420341c10001d140c81a4000e4480381d035140d00000b44021020311818107140c65003070b1120003400c12198801c3c0c43c001c2c12440d0382040e41802204000a03601c6a41104803014001c40c00c0c3d400038a126902d8031b56205035800d000e50140c5c402c0000c50300c908003851b01000821011415a804c1c02d0b140c1031220030607 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 928227553 1250 928226303 928226329
    0x1306140a0b0906090c040603110d05070504061d01090501032a0207090e06130f02010c0501020f04050a0e0f0f15060301091413050a06151e14030d020c09070e 69
    0x200c0d0340c40d038080245040c000b82c0d0035000b8070215503060044c500341e02000300354851401400d0803d612651456800c420f010152081010480b000f481541752190009000d03400c03911804002400c041c14040044501554a00c000700040c1d580c2800a814200154060300d44000040c1c0415041180140300b001202e5015400c00404d5000c4c144683c5490061415103c41162905841e003208060040581e0844070050f825603210000c1c11880d00c00780016940300c8030344480640907500000e0b0380755900300300d02c0c01081529022161a1078190b102c01c03010301c40750001c40b040c0002045410124020052401e841c07a40701002c0d16040c1caa8170f07000310101e0000d0b0004c1e80b024019544500700860310400240e04280d01009054100c004440303d0745519550302d100000c00f0b0030301640e4450280c10107850010308009001c0100030140301e0078061020810001d12481085502c03a08108461a41d03d80816485600b500c507500412907030752910100480c2d20406403800040c07004622059640da120b0603880944 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 928228803 1250 928227553 928227571
    0x1003050307060e10141602010e03040902040519120b04050f030c24040203120a030b06040803070201020d0f0504140d170d060b070803070f111608011112130614 70
    0x283d202c0e818007032030041c00c480d82c501c403e41800000c0300c000204810107a80702407204202c40000c040541e040e40100b8100540485078040000c010803020322940082c002c4030425103140702e4181851881780904500c50140c29040d9135459207040210f001c03488602e801c1030191040c3e41e402c5601e43d0312a451540b000500b40e5441e000002c9070030b02c81841c070b581043c0c00c0b000b040001d07a141c5420350019407156000c0d03245503020440424002e10483c0300c1d9020380501ca0016100aa843d82c84001850340ca0704075032000c0340188038400c01e80e0001d81c071032203070350300c100c2403d0312070078141030070455501c0c0321859000741e41c1e070403641444031075010071305a01c41a230001c01d032000f80b19503840c0801040015582c250b007180c603030f0300010080c10000900b10400c80f0750042c0245020001e003290141d048480c20703000d0030030900f580318100304c03030002140b464010b500300da511800800015502c150721507524010400041d82000320f0900003100719160f443c241045078498000012451903032414000710710019208418 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 928230053 1250 928228803 928228811
    0x90f0f030d0903210e100e03010510032009010b0d020d020a09031a010e0c030a1d01020c070f08070510020717070303120504050c040e10021803191a100305030706 71
    0x8280001c00380724000134110280100c103100c081450141034020b44440481c022445680300382c0b602c5124606028072460010000d101c0c070306080e51100c143d03c0c0240410b42d0640011002e11080c180032601d0303001d5030880900841c509078030700740c810b0714035402403068440d45070303001c00424010a841d440240350341485600d404500a0650810303c1280f00b9202c0d04640b801e09600041c4070141e40c03210304551100002030303d02d5407903a61003c284040d0040d402a4002a42280a94402518190040c24041c0c40400c1202c003c10365950100c60b040340300d80b06503002608900340c1070145040440c0c84000081042c0101c40b03110f6519800c4545000e10210407251a8225540a03c03c255005107030031000b00382c0e4103040c811810551602a02c4081801c0c00ca44036968520002134525810b10002e001c0b4030018a04640f19840450303003109051181700240c1c1f05e03028180d1483d0340482c039040100c0585410164420344103100ea04040b8510708050880700041105400000011344100b0090917203d1080070045 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 928231303 1250 928230053 928230059
    0x1005120f012405031207060203193806070f030e1003020a0e0d0312050726010f0501080426070c0612060906080307030c020d0b1303020d020111090f0f030d09 69
    0x11842c00390754004a10903000b040310044c030200c154080d01c07400e54000c600142e81e9100c511001d803124050803c041c42c81400d2410007000c01d00043d1200313070b40c038680a0141004c0d411102c1c076800610038080ca501d6215205001d4070000c901c0c03452210340c0307451084c01c0c101706a210040004541010982c50400081d4000521070006640039440c10002c00046d9080d4800c442182e50280c42d1310b0f008000281501d0b07640c400a0603141c41007504410307410045501048807034405aaa02c4100c50900810045440000d07002030396521803015503215681000d150a080c42e00010101e190000c4410074890140060101e00040b56402c0903000c001c1049484112000d100c0d81052002d4a1a5a000701d1038245420020002203101004480a4561503d840c0e2a40100381c8005a0703000285071003d4810400c40e01000301c543c809480c4c4c075105030b000f502240c00b0744400100403400c0c0c54440348084c1c1c02240074824011103050500209a0041004090200c945503440119281c501c15082c1d000000c0e0350346000f0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 928232553 1250 928231303 928231361
    0x19050c070c060e0a3606030b0114010c03050c010618050405012d0f060f090204050306130503040e090f013308060c030408161110081005120f01 63
    0x1e4002d01c51801c1c15142200000d0014804036540d00c5106208003c850440342020131325242d5450220420a50700b098400c444140c1004141c203000803120a2182c0c4000314014103840700007055244d05030350700180c0c0099a501107070302c0d4200030140784a940d00c0c1c2e880400e40a91a00405981000f1901c000415142030f040150035210484408501c07903a00c0702001030303030210581650004084074140800c0d28218002510300a00c5107070300a01c240c81c040c44000c01c1030500c80d0010412210b048013146c4503600e0303e0b42019040c901f1a07d00520a610401040080c1c40c040c240b80c50703202199a0655081c5481c0a103484e096540311021b054080800070607030115843c01407140f14081c9001b00f0882e030180d0030014419507480b005411182c842001000142c2040940d6045525001d00f0700d10b0051000c5442ca8204503441c120700100e4402d00350030011291040c030904489110f10281052400114a45010f0100c3d83e4000c540105070350007000e00900d0340c00300034002c00e802e501125038640e0076441d03507a6070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 928233803 1250 928232553 928232573
    0x304061e081e1e010b04080f070b040e070e0d0302070314032a01182004090b0601030c2a1403072307030212030909060a1d19050c07 58
    0x800240701d528414000b046101581e500003140690b041d00c402c58403107a00d8000402200303026640905064800481d0051807100604101c1d070108007156400159005032544560b014000c80090100c280403c00180740e030000302d16003000f00c90400c0c0c0010611240842c1002850001c15009a4452082001040005a4810203005c4400c8c040c500301490191112109803282000340c0c400310103815960740d241d07029440b80a01c100c00b40001d00380c0d2003452603d0603000400c2c4c4000740d242403810b04c603041c041c10503014540b000c99219801040c55560725006500a00040e43e90303138100121040c8590588034202e140e00c0011200d40c17402408a801480e00c9101c2048180301412950030501000000a28605030a100c0d0414014a00702d0204040181d80c6015040e81c00603600000c0c2c032000c1d082c007683c04401404030803401d0350402c0c000e6907900d041c0045410184202a88007201e90540c0b100e846441480c6038100c4100c101d44a9500c0100074820260744090b01e440010319000190390040000050f2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 928235053 1250 928233803 928233857
    0xc0308090f151204050c0303040f030b09031c090314220b1305120f121b0a0816031e0203040e07020f06010e06220b0a060207050607061d030406 63
    0xb84082c18a0202c2402c0b08040c0510121050500740b4100070508110702071000360a42c2c503024003200e46499032240607200a500d948403d0304c11040d0280400c84030000842140c0058056040c1c2200036044418000020b1081c1d003c10b808010b40300c1d04058000c80c4032801030503144420742c88025004100220103119503056030000711200020001c1021500601885c10122442201c205000745440d403401c41c20440703a08404019030055550078000211000090070800000a042d44481d0911402031650360140b80170192088405124410781070f000303001011003031840384c0b030700c0b10286100440742000c5c49071310002d03031025800104c2d050040035170042c0840d9201040384010850401c0170f080c041c0d10741406001304011207040000281581d1a50a030400d40311a221403408910307c2500d030408010300b00b694031244151180d0f04c002844520004840c016540f000f822a07150840550ba00801401c0180c246a8107800da011649505001400070340300a150301e440384580d00e030340100c0480300446041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 928236303 1250 928235053 928235059
    0x5010b03010b0a1a0f0d05040302010504120f022503060219171501120902031e10060f050d0c0510020303250503040b0a1d0a020310050609040f08070c0308090f 70
    0x200100304000134801d20414244400c43d400356144464444100b25106030210b451807681003006000405030f05501140c07265002c8c0006440134695401e0803102412002c1d09800180c0c40540e6005903207680e40900b0b00910300020360030000c82e0740d035515101a600241070aa1041d200f80440b00350f9a90020b01c0143c103600c0c4541009458501070f403009490080c90390041d41004400e03400d1010503003166011400d429001421250b4441c490044501082c82d6242254114010084030303914502c058081d080c151181c562000d5805406c000c01d001d94412401002d48072440741080c00280ca4550a600c10308452081c4c1c061a581c0c54002802444e0404400040819842c1100d840801940c05000d4a4115501025514158071075034903410140400c1d8102c0c14182e1507038083c8200890000940180c014800c3c0c06451960150088007030445404445c400d0308a406180004e00041075801c44540702c1d8410740605060160781d4854840d000c6598104484101000841d40480d140108400703028840c12 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 928237410 1107 928236303 928236319
    0xe0a09020102210d0e12030c040618060504050906150309070512060103030221070c090b1e150c010209060721030c080403051c0905010b03010b 63
    0x41801240544121452803070303103000001810411440f1154464141402000b11001905010201a0440c0100c0c070462049000f070398040d60144040303d02031a1580d0800102414032080d1150f119510800284104400ca40c007404860542c1d0056a004c03856844a5011643d07070101031b00781000601c40441003118800c0d00040190894100302c82c403a01e4101508180c54072030308280400b60050b001011481e060141030340b8a0000150354800c0325203001c1d12a2198044803015400210500d80c580c3e2801c9503e01d0580e0b908202c0c2c0c3caa554580865402c28030004005501e100003040450390f02040d820b01e207000a40c191403c030580903000964486451800c0007454041d00781c0340f107000384d90f84100982c09209124400b6500c049480c4c00c51103880319102a9210f41000703094401c0d884481d0700000000baa10f0142030303255403041c0004203030071191400701425550642d040034080c11035 = true := by decide +kernel

theorem cover : BRFrame.Cov 928057553 928237410 := by
  have h0 := BRFrame.cov_init 928057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 928057553 ≤ n) (h2 : n < 928237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
