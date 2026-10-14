-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0585
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:35:27.754027+00:00
-- url     : https://prove2.me/submissions/0bfe7d48-4c41-43f7-b1bc-78e67b1d00a7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 105035971 ≤ n < 105215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 105037221 1250 105035971 105036017
    0x3110604180509190c17011803110618030901030b01030608070303090e060901030c0e0a20070c0608010f06180503060c03100605190516080c101109030309060a 70
    0x4600e4804542d6042c44801a498400c2000404003a00700042218000403400c01c103050803210790a050001305000541501e00400c1c400341c051001181c0880f0034020503410a90b541650300740c501c184c81c1641d8496207240602c81844680344443d07001003080f503140b0342c06540440b85411041c94002026074540005901d4025039410503804155410001c0000b482d112000540c8240c00703032041d00c401d5245540304903166840340100015411404000391344078010340e0003202042040060342099146081e8600c42c1070380201010b90342c0c2c0c040040c0218003140210511412a0105c0485c50000c526007201180c0080171111404803244002c40b000a99a808000680c054441c00f290030781e803802c20b074003c454003031419400b010500c14144034800c200c043c1c0e06501005e8035003d060150341da0b80895491940305012010041021201081c010140c440005450030000c2081d40704110851000301550f0700d50064011040e03059204000120007410204082c000451090802d080720030040c0510f249900c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 105038471 1250 105037221 105037259
    0xf021006090e06010510020604030c08070209040c0e0a0902030c1c050601090213080604050307030828020901020106051c12020f0607050901030501090b13111b010501050f06040b030103110604 84
    0x20b9110940d04000c1030052245030300400301202c0e004544d201301725000e501d5140060026040c00140080b107070510a110b0b0488580d031754024203050040c5400d16041d00290850b00a0440b105100e20008540300800d12501c100d243c0c0042c003c14000c4241c500700541800d8104100300300c7c2c00c0c026103000002e2020000180680441d50700562500380c00da0400040c2e4110703900c4811180d010b04203010100d1000700813110165010700d8a500310303a40f1044841411902d020981401202100c000650f6090340da002e040051402d034024401607a42c1c000300b140c10180b00d914005042e80c142503100000346069030180c112030041c0140c1e01012091040981890070807100300012440004043c2160740e4140309040c003502c0303101d504202d034010180101d244a5441800c4000c038956450510308420006801d9880f803d41c1030b28144110385000101354080c0c00c0c20300c41c1601502080d81c1840c01c6140079000e54080d10b0454100b1070840e882d6860305801d070035022242e140c0004c0100004546140078100f5070301d144e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 105039721 1250 105038471 105038489
    0x510030e01020d1d060c030c07021203070501051f0305070504020c01061e090f0c02030a0c06150b0706051303021b0d0206030112030e100207060c05030d05040f0605010503010207020f010f021006 85
    0xd10340d480b034a040c00304c032400d00b444071074001c0c50800c07201d154000280c0784c110030005900b0380c8035099840459a00303c5000445001031001140a904003e41500001c0c42740b02d282030300902503030f440d1100966034a45404002d2403900070101c10300c4213040640c00381c00300780d98450001ca002603980c03501809ca07540c0d201d0075600401520400b84050003680c011000c121000310030400050092000081d00c0380281170b14402040038254500c0b05115482d080210301115880b80d072600c0c183c0d9003007205119485018216a590304040000e80c00701c0030007420383d10043e0150054010a602c050b095004c0c0d890910806500050700d2500c0720242c0c4070032000d0740c0a0030505801c400b14241c24100601080f40e0010101c0c447e500702101c0b0515581e0124400c01100c1960a040b184440c03580380c0b1500f180103a550100c407042c0b07008100010b001000000000d198017440c02040f490b601c50040c10300f40e228055019400c44040c1c070304810300303500c5803a220f24440300d944150384040e04141d0004050b181c0b076520a0140b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 105040971 1250 105039721 105039731
    0x180612070305060307060c0b090a0b010f0918080304030c061e09110307050a0501030f060b0c0a031d010e0f03190503030610050c061609080703120f03150510030e01020d 74
    0xd69098801c0c190003035001c03001404418a0107000030302d076905211005225001d18004200c800784100040007000c1d62004003452651b8460740000d4844a1610a4041c0e1070309012180040d0b000d480108400d60b42c10802092440c1d480751010340398001c401d802101d603240d80d03030b00c45440321002c0c0c61542c00041d01460040b48202da1810404048078514044902ca9042044200401d0782c40c034402008a81d020701300803402c4103140308200010b0005501c0210115800281d114070030002082d07140f6064440e0321810922115540b5080b240c0c45a0080d540c0031032021a5a00020701e003400840c184110005d08031820520b90042543c42c400b00200119103d074008020301416190903205650180b440d482c0050401451229082d0341c1c40001d0110f07240e0111501005180a114a0700301002d4040001103481443d03581c41d02c5000808203c01c1440010800c10399410b00c94402d010b410300c100c020308810341c146400d0600308040b601001e401c0340b040c5580c0703d26002040c1e0080c00a402141041000022 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 105042221 1250 105040971 105040981
    0x915140f0a031425110f0a0804030314030108030d020d021911010c1b0204050601030605090c03040302060f0606120601030f060803040e090610140303270a050303041a180612 76
    0x20096005003c0b224454494282081d1031100008000b130a0581481d00031070701c500c01c02e500d5050008800000751540030704607800041c8200c400040049900c40d42c7d41e1000500080302e000361900080c01a001590010404c0550344081500500025110b14100500d04070100d481c040c0201d03041c0d441b40c0007280b042c01c803c005d034030030a01c01c240384a011410090010010002600300b42d10003560f00078032071a51a00414480d0340f080d4010000303400040c1c805940c42c2046804031489030001c0303d007200107108a0700000c11407840103140070b001e41340180806042644004002900103401000181015611199003c940b8510b0040c04d00918820010f140d6031820f00c000301d460741400800000e02603000c0004c3c0641800c01c3c250300070440741c46c04103a501c03205640c0002411807081d03000c41400304070010945d00c1840c02d0f901c001000725004072181c206155640302030503120700861044410740c0444c01d0403504103010300002084109003a807640303c0300e5a41d5a001441070740040c060702c1140480c90003000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 105043471 1250 105042221 105042251
    0x3040b0c010b010210020405100507051203091f0c0c082d041707031707030311070803010501020606010f080c090109080106080d08010b1306201e07060915140f0a03 72
    0x70715008101768107518050424001c600f4003d102c00c0004100540065010148035052009141900300ca401d502c1e500d040038070645c0da550b034075880101c555030702e92041070300c20022a11071505030b1541500d60500101041c1c8a40d030f0705410201802801411366070741d0711b02e140c104005c20b00c401c002d04003c003904d42d4145142c10098045c4502040400e60120703105102080e551210030780f942c8460072003196622130030305e0100d02804042080380c0c40c40d40d010411b407040060b20350103503050701e6080c0d007112250b6460f50700458110741d24134401c1021810f050042880c0d210075000809081030107040940721155034020041c00c40f6003035071201100b80c08c180d250009940d4007100044c0148000304010f41460060700c0081803002403032040005000e40d021185c101038140800f0000d03810701413400d81d005200d50800196540025240307520050040010120302e10b07004980001c16a107a90a00d0010396032001400d41e0030401d243d110301d1162900f0310480c01c07116210703070041c8849909039601292207400302d8450 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 105044721 1250 105043471 105043483
    0x30a060b1305040b0109080703061b05031302040c020f0f0a03020610062703060510030c08030a05070605100f0303030b010f0e01080601030902040e0a11100305040c030f020303040b0c010b0102 84
    0x88900c00c0d03020071415160181141c10030054507811500010324a40a02c010785038242c5561009046018428000050000f00d038000209000e40c0780d041c80c841c80e41480308980510040324171800070740c070009450026003015030208141d011980100d0310b00d00e0344940304030f00c1d24501c03050201c9180c0c00b80440d1400c040d4144070721500300d82c2c8030b51120026806c1c814017400b00c40e003056800014420100b1800508654218034a00864010f04200070728140882400c40480c001c2c0005c2d110380740791040006d0100c0d0b000080700d40c49803469070b41504001840e600c00d400381502501117039a5152980300410700b102240c0c06c0c0c00c010344c0729072030001d24400184009040c2030710108400c8103100b21038810002d243d0b04169410352100e42403030006411f01403440010300404d145024001c861065003510410402489000650305408880050200b11410421800d5807001c46004015410300c40f8208000707003040b48410019032000302600d0034140c890b52280204d804c0003002c50110f82d19a03000300400d507014080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 105045971 1250 105044721 105044729
    0x20f04110d1d0304090f1b02010c030506010e060f0306030106082b080105010c0615031b06020601050d05070303141204030e1201050106140c030f0406020a021903020f060f0909040503030a06 83
    0x1c050803a954001581c0f00d0040b0b01c54124041e4603900034003c00086d5512200d660100054200410212003600a00070302101354500c001c40e1405011030115800380f030300d5440b44c01c00105181c0c540103142c60603125941019002030307011341d00c40c1341c04a05210b041c00020b52011418082d0f542005800e18030003103c81e082418102032001020040c400c1d640c1c0490301c1e5400d10340107a00030405c2d95840c034649023203081c00d500240246801013004001c40c0e403c0003c07002280e091703a0072150983d80760781c20402d07000780007000200b09030300c2100308000007801030b00407400b9003800c1c0582e01e04041c46d50a80080c00a001c4904030001268552a03143c0c500c0c00705040032000c030340c10300208165030500c6d0000d020250b1251085004100128403808840c4003041291440c1c150400e841b134865a03510800303960b842c0881d038100c0c0725090382c544120400c0c4103c00c02604994004180c00340748800c800500200761320103251103541180400040000d078840780016805648920021030382da02d040181141140c081c0c0d00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 105047221 1250 105045971 105046001
    0xc090504050606010509010c0209161404230315040503030601081e010e15043e190c050615130b0906060903070315020a120e030a0309020f04110d 64
    0x3030101207280000e56680c800c8007030030501c0d591640100162001914600000c1d402822441040008207201d5960000103445480d15500070051006082c150301030b034042c929a40562070000b110525040d208103c006401805540c07611824900b8440d80950440d002d0300c1980c40041446620351740083c18961010021f1304904690031164401c0e15440d10601c80c15210414420100e0107101c0030251010f4a00c000400401603280c1040381703801718081c0e08402d141700c2d100c0910443e81c0700014016001c00f00025100305031400841c0034030300400c01c0b940748801e0100480c01c852040060010801540507840e94411482c00c15814020400e030444400104200b90741000120b90f03003511052441600903800701d07207480d1640300c104082840d03c016070384042c20003089c5081d003440340500750f4020b050441c0695102a02041200d40700c4055030301c24801e0010079802002028259480383e8044803200348010303c60010744000c0c4001606881e2a01c15104190b0000100948140b04038410240c000d48112 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 105048471 1250 105047221 105047231
    0x7031a060a0c0f0203010e0d090306060509060105040303030e210d0b0418110d0c0e0f1e010e0415020301090c0e0301090b0403050c0307060c050405031b03030306010c1a0a090c09 78
    0x14004104415400d40204903243c04400b8034110744d020340210b113655580c1011030b01c0703c2280840041c004415480180c603040c0c907000c004211403e041c44132510965040c1c440b24502071031030358200c00400400780c18080c1070144101c1d40740410054141c008441500120035030f00e0b504081c041904072038403005400c0c490741c0f411640341848000b500821141d1504014524000340500703021410f4101903c40003412030554950110310010203101c95402240f00d520343c6a1940c5c1e80c0c1c24102c1544c1144100d03089020742010040040d01c0d01071028540c014400c038994451054100564010781e0400c0e0800c00b1901d80f14294802c0b107035408110304822070b60880092180b41f0b0240c0f221013240002400c06000c002001a00d24106801003017160100e56004000700708401008a00074100c0d0403a000d4140b282c0103055034944140a800d444400d00f4400070051032841c0c540c10015034108150031300c1150382010b9284041c0c1b08080403101e2500c0380101c4040425503408a1608220032807841d007007d1038280c940 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 105049721 1250 105048471 105048487
    0x3050703080a030b0306091e010605040f0509190201050702100e09040c05030f0109170a05041a040512010c090608100320030c0312120a0902031009060507141204060b060307031a06 79
    0x48c03902c407010706c6041d131940790140304140303d002d031829401094009081c9100028070441c2540150301c02d50042c800e441841046514030714250203a0340000e80051400c0c8035003400f43c5080d810300190040c060420302015203146011804494040b50f050b075901c4a07102041007641002c5c0f00501028007980f000b00800001a40e44d21300c60103050441c003040c00004a48041e019000b00304450242c40c2c04010f00031410001100c0ca0219405402490b000c0d020b9035084030180c880c1402515a61146a2200340805040c034030201c80d2580011303c03264111003090703c00000b14001000340c00c0386681110944403101010418149841c40416805029501076103551014002e2130080e56089609400700f0a2203480e0349095601a0520303c1000e036140c080e0441030034080000740c0c002c0f100c1c0382c4950810f200a51b03038a0401d80e1700c00030240d10601c0ca88010401907061203140d80006911911a21700001d5141c8031101091250f00202c40f54000300350358040d425181d480c0070803240914036080b42c4991410b045 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 105050971 1250 105049721 105049723
    0x2100207050121020c0307050a060b041406120c0a03050c03070608010e22060203091f02040b0418020403050d02072909010f1e0c0b0f0610050c0703050703080a030b030609 75
    0x405005920240c81c00140c0a400340c3c05a01160800ea48030f0040360f850300c1d41c9080c00c603200d40d40000112015442c003000014903003001d018050311007070401d454010343d0ba40c1c2001c0c40f0800081115a07d042e00a01c1c040d046a5500d03000c0000241d40100c0050446021200c245881c1003440d4003e04188403000e0700400c0360300d84064916512000e0428044407996185000b280c0894a03094000c00107400031080140b490301c002102d20034010748001c520b0b000074901c40d40e40b0484c03096010307038001420100814002684a00d4080c0805d000c0194010b00e0580d80381c8403d400d140080300481c0040c0c2010400b0000320b1204201401140c101d180940c2d0152610340d4030038101d10030b4440c0181405800324000304000d028104144400f0805100c0c040d11941c2c00400170101220791904840410b010004545034407107a0b801c81d071182101400306651444c2c10102550141c10100a154091007192030100004d40c4c00c0c0702920040d0310802600741c68094100d405020303140440c0080c0e02a41c491002c015510f50 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 105052221 1250 105050971 105050987
    0x1f0603170f0403170c0114221e030c0c030c051206060108040b0a09060f020a020d02121204020a170309120105090606040221040507050f0102030f040509130605040c03021002070501 79
    0x290056031900c032a0003203080d01c40c1c24005c807148003595518202c401c0c011586d00c040483d2140c6000d041c0020141817184484003010b041d007101a0103143c100380340340b00c0390b0100092901c0e040c2c0079080290b829102c3c1e81c5e030f4505911aa03081100c01c446000760402c524100303107158410382c5012034041e220500c3e207080000c1c0703080001031000c0d08600c3e01c8400308601c04042e90080000c241c100e40c040c8080c1d00d80154140180d40030600150051041c0c0344901e07156440130611450b90301c044100c0900e007a07500c50981075180405442030382d100741090320011309188002160441581c6600c061070702c1e03600c800200107016883d100f40842c80e074105020410b0f2020041602644008202c0c0c006881c2e1070410203030f070088103141d040e640040e01000e082c0401d020b400a0704504036141118440e001d00a080012a00d03030150305515250001c080c0400d02c20f500e03040d001103602c0440761802001030070203511510190340007594103607110245c0207001c4c019401d141d01182c94103005400201012440c1c078000916920b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 105053471 1250 105052221 105052223
    0x80c0105090d020405100302130603080910183210121b020f010c0201060806011710050c0c0105010f05010c0f02041b0f030605011b02010806031f0603170f0403 70
    0x32000160200190352422840030000d90094001c001e94070749081c1c20810711849010503841f4040e500c0c003904146200d40251010780350700105d50b6003092500000c0c00790740080124207105004070040d2130306503000c400505400408003010b030540650034101400c40804000c4094811a100c2c000c2d07a000141c072001c4400c121000070b803410a41d209050506140246038101c6203108000403c2c11103041103600280521180107040000c018141e11050240d00300c40b500d04c0b0b450070725041080100003c42c440c1c0b18580715103881600380e40010300e00d603500c40308480302100c0c56036003d007001c20030ba80341c07032004d1182a001d40450400005100e05110001c0d01036140700c4002090034100c83c41c09400c5403201d40201d030b410b0204104050103821502c40242190401d046184006860540c0c0000d0540c07243d49002c05a00f804541050098074070b800454200d64020845d03038041c441c81d8240c84030b84c08210006147c0e43c80301e81c400030700c1c0c60030362920144418482c05a03105030102030003a6481d80007903000b12022a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 105054721 1250 105053471 105053477
    0x602030f18120706020a0218010f0b0a020109080313050d03050702100e01020705010603060c0f08040804030f050c2805010c0809060a0c050303090307020406050607210210020408100b0a080c01 84
    0x109180200141c1c0c0801c62651250490040b10000074031300b80c00082c4008200e1007201d194401c00115071802824680034801c10303105241c4090208544603000c3c0040110000600c0089000c204584441007940d0040d103440b80020900703c046d1007400070034000b00b43e1018a5240c103000310b007081c881c025078450f0410481d2200c03d96404052210340d0095048400e00c0e51312500034800599a41454001442c2000c03203140072803098414002000d00c00c12026101c1c1e98412032a9081900719140c840a03070100d000c1c119041c1c4903220102d802503945030401091000514840c0007132803c0e402c4040c11907400da5101c2c2e4140802c1c003007540001420b0304241c070822242a07c0072034a586050408503003484a40714081c11a0000200703212840001000601486009035814044640c2c0d510500141c4d1164a00c05804401ca0991980e0003504509801e40320420702c1c0b040748e413440940c5e0128412a440b40c0d000f441241d10040d81250106039074001c090094a08a44030f0000502d844105038a82038001015810 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 105055971 1250 105054721 105054757
    0x606040f061802030a0b09011d0c2206091d041226040b010e16030c110d0504031101030207080f030408041d070815030d0c050709090c0603060602030f 66
    0x404100d03034003100050540c1c00b1504120541c42115400950080e41d20140036400c0845101c0c0d1030400003021812241070500c2108860017078a8503440554002c1d001d54501e002c10815100d01d104903004101c0704040014010b9052490001d002d400801598010180503201091007031069000780301c003e51103500301304020404446403004940c014645440d402112081d40340415004c481500342d54030407445100202e44503601c440314810055002c907100f28406100c1c00013204a43d00c6500200b92004a07810150060310441e0780325070a2a518070f00540000303401290400601010000c5070442c100b003801d04618056041e1074040b50741c490400c200348220800000300d42000420000c503002070070341015038011500c50011a4240e0041980c80304000340301580420281000327914a0625000002c0040c0780c1c81040803070545500c003249906031194090380c440041c43c4140d90041c011013a204549820f0240d04040f0050125446904141c046520a200250890410300c0803501d5860032038445c1c040e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 105057221 1250 105055971 105055991
    0x501050d1103010b0409060807230a05030318010305130803010302190510111b01120e01020d020703020705010f0503010807090b030c040e030a1409100503091212010303090b03040302060604 83
    0x2000d001030000407100000000000a6100c04140c0604146d8168040a01c1070568511149645c2c02450040004600303058002207228040c28501118512014004000c00d80c0c0e07030000241580c2040303c06803030420710707030480f52000d6a15220719940102030b2024240903d189442c4c00303842d4041400000d000c1e65408840d89601d0460302c0e001c030001e244c0140300c01d03000c1c1541d24006001e000880d20109103072059440a0042a0003800e0006659030181e42e0002c100d0248011800600039480100e40295403c021b00c0100707005a000074001107020f60001c02d0203074541000144a03407116600c1c04104802440140305032440070a5010884804e114045000c5040d1030000742014050042c00e9880362610310040d0600502001404103104641c1b1010b6525850808407c0c0d030b4231480f840a5402907510510300b0b40c2c01d0188000c0d40d00000b007003080703490050540314540d442d6840034100c0c644443c01c54004200f099840a90322001d030200c42d903c1c90560905540c0691344100140080740300d9611600c00030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 105058471 1250 105057221 105057247
    0x301021801031116030c0c0815070e060708070f0209071b062d0501030b01152102040b0304050c0411090d020904150609020309010c0c03050d0c0c02060d0f0c020610050105 75
    0x424903078544072504d007541840c3ca00504807444020085500da01108000100780c4000329170401e10300d1242441512030398030741d942202c0c005e038842182a40803109100107004200c50802505201c0e103d00f07031026080766640100224814002c000c5408c2000a080310388050490b40d500f800059408600851100c481c41d012402c25500a880b140b03420314640380b240140340c01500a5030499000b915212126603c40c4d07496100c4500203079560300403800c241002c0c2030407180c040072a20016440c0c82c005050a0702c07061041080da0090340e00b914554009040c10580b482c241c41401d901000f55840a40350298030360102c2c05042e842da00103032191015000240c2809820903801c948154064010844d058480307001d40020b4100ba2400303100b41d8600a00c114020740140c451464003074060302c480b03081c901551420b001070032488103000c0420200c6031403540144c507818040e000000c0054000300384407480e808203c00b11a9555034001c02c65121b2000e00148240c042102d00c20780fa404c1ca8900e03076aa2080b40e244e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 105059721 1250 105058471 105058477
    0x3020f070b041b0611070b0714010c1d04050714130503061603180f150f020708030105010215010308030703020d1805070303020d1e0809160303020309040b03010218010311 75
    0x1a2600d5405401c00c010072000e180070001003c02d14060060294844030111102051280041482c0d03001407000d01510740c8200c058010148101c440e0068440041442c0d425189025150004500304140340d880501107900740700070b84c40c01070302c0403c298501044010000c48059051400100e40001d003504280c80c0d040350304c0d003c0c00014084540604040b0a84072400d50300d8039040c80081d207018000c141c4039928407449044503401004a90081e03006c5d44410088604e07030545104002e5691706560018102030000d0f05086005a00c86901c80d8540000a0300388118605003013a03d40000b80140009130b206020b60b40c22508500d801a110310040201030014000c038031140505500f034082e000c04120001501401741c91199080daa2901c41040b400d0360300b144142041c002d0440f13180705102e1218803411a00c1d0340030000034107c3c4e0464000000c031420395985900300768016040080c5121036070511f07000300b03140300c04164001c51074021603100c08444c2410300c10000f410982c96400c0c540441c0050419 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 105060971 1250 105059721 105059723
    0x3010c02060f15130f140708090f0c0303030708130b130c0b0a14030603070b0409052d0a0b0120012007030c021c05060c0a12020408150c0c0f03090a0510020d03020f07 73
    0x280821801e001c1030223061004100c800c2e401c42e100b0502d00b03111452001c01c81410700000a401103007075031076141055406820003045c10b40e0500f82000e0b4034021594000f0b07602c0c041c81c1c10f01e4082455480f1410021a8a40c4940090a40020401422845a5101040100b110240d50320140c40751031300e50010303080081503441107009803008100030a940a181c2d122038003803d0b4084507802020000711103503401d807044500e4100c000c140000002e01c03003015504040030948052600021250684070303440d0100d00070006000641e0f40d14000400b088114072001e0940c00d0300810641d050650980d0014050241818000c1c054006039400c05114084c9102e02d85030180e0090558075245800c07040f00886800c02c40031500046d003a041a00140e00f0207101f10303070640d10500c014020040d10101010884a0081d00c503c10580c0c040100c920921070a01c01d14071401d00b03002c09155a10004001c02030001202d0b04005e214418410340174840c0c50300080c000313070342051a040150329004030748041502030180d030308 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 105062221 1250 105060971 105061001
    0xb060108180706050c1c05031306020f0a03021207050c0d11011104030807030f180909050c06160b0f0f0f040c1503050118050103030206010b07020a0503010c02060f15130f 75
    0x2a01088158110f800b41c101e95405c0c0303044403902c040e40c8002461030741d8211054408504200301007201d048110b041184400e008000252404142c0340440120ba480f0000b8600000d0b0b010a09114040004682c640c1083c841d1a21354149141c54000d0340e25030407030620708405c0c800c41d040c1c41c0111046c2074001d08544038140269a0300c0302d640b42098482540025401c07800158620920194075014411111200d9004c031103602d2840d0030b0504500003440501c80030340b1180f003000552200c4d40c0c2d41300014020740c4090b403825141e243c0f46142802c1710340800760000c0701d04482d10080000034502c0340009940039070b460b00d88481399201c500b0844100101da80203a255484190100684039405810050403950190204504015400160000c5800c02c2c003004006030058401004620403080c058000d050000780a6030003555103600081c215072101c0c03201f03005a003040f001c004c2041d080f00d06441d1b01019003042805004400d50000c1c811503aa152840c0754181d4401003105500e005510118000c50281 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 105063471 1250 105062221 105062233
    0x9010e06030108150f0108030f070813090e010f02120f04030507080a2a0309031704090501030b01060e010207031a13061e0609110306060d0209030d030c020d0801030b06010818 77
    0x31034498490040d40413107140341c2c07600b00205510b0114110158101c50302c21002d1401d180184050401c075a0200105079100e080074418102a04210b0800c2d0340148280b01001501c0e40d40304801e036003503a032404100c0c2421441445013540c1c4031003001d03515600c451009480c503c0395449140644490248500c0580700520200d03d0141d12a0032200400c1d4aa402d10071580c440c280340c510203114035243d6500180010302d192406c00c001440510948041c4501d5002207050a45500585007111000d0b84142d82c40340d1200c004000064201282261000702880a0800c45040d0b8560054107454140b146c10560004000110150b029802003080301c0d500c00c4040c012034032040c14444540d00403445180e040c61030b02d1000a5070450030b214801200200700c1903141560750308001c2040e190001e480c0c202d101a000c100040c040d503814440402c114000361400aa0000c14504c024034150115404e2014880300500503c00310308440413540d4410001d10742141c06a44001240c80407000b000380c0c1c00583d00c119 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 105064721 1250 105063471 105063479
    0x30b0405010504031404080307060c05040b12010306060515040e040f06051302010215090c09040501090602040f090506061c0c2706030f0209010c12021203070507050607020a1709010e060301 83
    0x64000c2402203000360780f1060701001c100c0c54a9246c2c4200d100b0703086150700401480c0006000c0f500704000b203031040c1c10040d0401c0c3d90341c3d01182c015404403250307004000e2a05c0050080060314030840703000d00025030b0710204092628000342c0841c450b6000b0307281000da0030000681000804440352715000e600c040c09201504112950059540362030f1070490242c0500f1402580b00509800018460a0644020050006044140078001d803020300240d0701e954036035148101241603400204018007444080e042214a880704020440e000607080c140329420800032131400ca010313410a4001d950711040f000502440b1987c00766140551402d9034512010707020404411f601c0641300d20f1088411946051042002c40a040e500300d00c60340f84071a012603401c00820006c01c6107625401009200c500407280c62079019020b6180940084800900080e000103440703003013101c24010303203803c0085400200120690f039500c48002c2405084440d20444c800301e0503a2580e8030443c0e80b4420b040004e082542e6950311 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 105065971 1250 105064721 105064723
    0x403241802090603010507021c0504170705030d09270209040c020106170109260708120709120512030a02040f0305030d0c0c0510110c0105090c040513030804110307030b0405 76
    0x8002050b8410840340000403254101801102c1c85142075034003170004100c0e142c0f131842c01e000c0350001d12400c1010a21002c2008800d035003080419415020080c4103640c07074403003018034040c0c0d11500344082000b10001041495a20441c1c074403011400c1c443c5000744469013075010003d000c1c1a070550f505c541803001e8016001e4040d840282581d100740e4190742144900c08101c2d090700c0040d50020110030200c3d00061f000c0740e000311440c3e6219440480c1900d00f01d92522081e40c2a001440c25000c041c001400f4407440a400c0f0350207900030007980c0c00d80d030ba158849458a80d11400c04014000708814001b00103950070490b54115400703020032601c0401500d0f102c0c21300940c0c0e500031200c5207804501d0501040c0210740104e00e100c400c19408030080c04031900040c4000040d180001003c08000c00c2402480c404110a024043c40f0b8141003000b0450f600c00c40e130030071080c1c807000307404d41c0d03120769509a0001c0801d82c4495199845a00013040304201d4040c0b0313000c603103480700580c4054103000d0790030706100801c28 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 105067221 1250 105065971 105066011
    0x100903020103240b0306010c08040807050a17030a03090503040503101a0312030a090204200702090709050a030206071509200306060d06090f0c0f0617060105040324 72
    0x4000e0b42e081100d43c240180107400400000e62001050b20704000801c14980c0031001154040c0741850301221380300d41e5039076074030301d40e041604441c0c09034100000600ca41e0400c07002030f100800010180b103c0b02084501c3d000c1d143d1040d0788501d410151200d4500341071000030011100203110240490f40085c440035109002445042c104003a50310010705184d15a10340080c4601ea85040b515006103140c4614100200808002404030381240c0c40d034075049425244d0785900e1040303102030101c440d500c1d8020310400020450003403803401801007030030050002c2e0f21400c8001c4292a410b07a03002d66520154100604858a0900c100c0c01941c00d00c841181040110808c040038041c94040d074a280e40301c481d04168580c0e901719061508246540d00c0080416155044080d038140140303204000043d41da103072040360b0840f98121455198141704100021a4854030300d03004a441c0c5640e02d5101d0400d540001d00702e00c00c0344005007aa041b10b501c0c41408080d41d55011041094200081200e04c044002460045c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 105068471 1250 105067221 105067223
    0x50f060108011d12030720030f0a080a09240e01020414011115061c02121605010206010e0703020307020f0a0f03080903090108240612010f05060f0307120b100903 71
    0x1110078060070f2003507030000a51080d00c145000e812411581c03000c4044401e4641e40003050059041500c8000c1140807d00080031064440b80c0b030180d50390b101d03400103400719070003070400c20b003a40c40c00021501003031400c2d0108007140d0800d90b20040020081041c44041c00541c8168003c2d54400070380050740c6090b600c0c007262210820f80700e81c00c02c4070f85400725a80719441000310480400508000410610f804000001200e80500c2e812034183c440307402081d807044080301c03840d07040d5005001210319a024201d1500041201748010001907041ca1203200880752b000d402d90041c0340e0044041010395000b40700032031003010640708541041200f410030602840c080c00e0700790007084401c07021612054000c0101e808c100d0040e100c81f41c02d6107a01f2200000c414100522501c01d0701c0758240072000e80c1d1a4401000e400c050980d56101a5051441a403680011036000510034042004100300c03094812081d61340c04034030741c10480b03005180110b0040c040c21980c4603595124090002c5101a20b402c50b41200c152 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 105069721 1250 105068471 105068501
    0xa0209100302191d1b121909050307080f09090c03060112020307050a1202040506180306010503010b01211104031208070e030709050408040905010b03040b1302090a09050f06010801 79
    0x4110901074214000d001c5000d0313244c4042e081040300c40380f20941058a60005030f07003036903240e2002c040b1368401c2503504942c04d8074824817110414841d04401c4400d0380940d40080510401400209580700b40e42d0340b04900c0024000c500106601801140500c20345940002c0580f600100d8036001c50f01b9000780d40300b169401c0c0441c440041c48a1800c0082c8241da03c25202074a54610341801d2200548100ca84c0300d400c4502c4640810011545494500c0030301800f002d0303400094a4032103402c0c201424810160031240c040d07803400d10841020380e40001e003c03280250040031160042010105607020f0007143c40800c223503220001d000010007080c034000c81c1c00c800c10750340c801d80d40f80c441c5441140e0030200c403520180c1c107a03c004018040704045600031900306108022407803034103940e84440010b0b184260f1000e030300101e0120800c403d020726040720a50110030603261104482c0d0030303400144000000381000000607030794848181000310400c1002c80d200a004112b401940c0c0d5024600e019050000005e410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 105070971 1250 105069721 105069739
    0x10e0a05060705040e04020108270a0c0b07050322090501180c180b0c0c03070603060303020706080601080c1b0115050307060203031312120903030603110105091008090a0209100302 79
    0x282e441001503809490b83d0340c070100d02030384964004540c050009072013103543d9004414541c40107546111540300240301034003d44000710180c105480040c030141d0084c10184020494000003820110841d02004404c683c000c03138140544c100c0004070030642c0c0000c0345452900c400402c0ca0f01c00268005070b59080d401d800d010721101040103c840c081118a40340607055000c00030700c14400315001911a00c0610422287c0100340040042d18228607603115001190342c03048140300b415414050b4001605450510300e195003010380000f00329403002048606004800316412130102072545021241d442068024032480b00448154014492540700b080c2c403074401c810b4002021800841924801c0841050f4141101c5181c0c60b0341e1003841e00d0303440150811994214541441407180301d0740894500968002a890b030441c0f41450001059001640c10b00038140702c445110740d290b9188030360058040ca821038464644814003454080880d8000b5031000c250002c000715103e1244216007140c0c022200c500c9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 105072221 1250 105070971 105070981
    0xb0a050c0f0628150501030203190603080a020114090a0f02041803171003052d030a0f030c030902100c082a060a0c0c110105040905040b0711010e032505010e0a0506 72
    0x11941c5004d1418103160203000d0420866001350301840c1d00040c008a115802c80101c440c803000c42e892508101c80b01140440e12070b00f000d50921810200060822101c0b80c9810701b01202030b41c1b03840c0e410300202034001403250202151965003014100c1c00c1140b01a4884000b103260243c006020307520640b40c8141e1540c0050100b5010f801c00d04216038010f1301801882e00030843d1254040d030401c0c0d1200c030000740d510010f10120070410007441d2403002992641c51000341300c4001802d403401c0c461100200341c1064445400f603503851115000c45015801c00e000400940d242a28031170044291000c03400d00c60703001c0c400c9601d85909010308a91106003d45089680c1e170b644200c00c840420107413000244041d502c03100060b02c0c90804065003501410003500341a525450300c1d0568004480444502c0c2c1810706101c41550040c80380d003011b07040d00c402444504182800c07150383e4011740e106070160814800d0480d09042051a083c4452500007000b8031000c0c81e000b011564a0501da0740c122454031603140024 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 105073471 1250 105072221 105072301
    0x61207061202090402070f0b0403030b04050f190615030b03151308030903040503100b180f0705130902040b03010806070905030a080a031b0e190b0a050c0f06 69
    0x602616a00d07241d41040110300d48000d40250003c04a143e0026400c028a01c0811101200b42403064071800010f006e600d09490020151a8200000c41c050b81c00c10042c8030b00501c100802c581c0c00b0700c001082d182128800e043c14405485290322820012800c900740c005410780c0364208403400741d409d404880c444e4404072074002d50350b10200c600003200d40a0302c50620015503094000d640040d01c1320300300d909045e1505c0000782080c444104503040c3c03665400180003142000010002c900203800d44810380c0c1e141c44c4070940308150000307007284100800001d008540490842d00100900b80d030240c1103494030740321140d81c82c1c6a4428040c12007940714680000380401d116807200421740d00090060320140000751789903226900000913038024140c840c40607080d40d500c1c41e044c100c1500b081d550b603101020fa0410900c0016120500d406501d242c160200b4803c5c56061401c44010000610f86030b035541e8440c00015081070b92110b0410340034024903007031180984001c3c080c481e4910f442c603108024000c0c490155 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 105074721 1250 105073471 105073483
    0x91305090706140c0705040b03100f050f0610120b18040506041406010b070605100302061c0e190b04140706021b040b010f0f050c07030f05100b0a031209090c0201050612 74
    0x10110b075803041c4011700047c1815048282503240140c2190300140f41e000508064405a0038a50a0503079100704110885210801190f0080001d41d400780c540c1500150003410484c00b10324000c0000e03207034180b5442c50303115560003101018210854812500301440c0060703c440d81590b044d543d04606811408502ca40807603910b041700c120b1400d0914000f03041e9241000b130f21000309208945090710a001016803160001084404204c0c89492031008103c20f81508581c05000559002c0d8440450404606461064010241d81181004126a81e0351619a610207460b031112061802105000602c494000071034006040c64032500452041c0084207010844a0035440d8600140201d00d02018907405003016842204e602e2504a1920341c4500240b843d02c81a940708980310b50402c07020405100b003d1200c00ba05241d0058144411030700e9100103050080e25001c090062008911551001070051440c000103042a410911410f0b4400d00302a000b00b8048a4480c00744452a5000200d0080442d070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 105075971 1250 105074721 105074737
    0x305150601020c1804111002100606030b130908221502030a090e180d0216090509060105060d0b03070e0105031009030207060c0305040b0301080d12050f0a0209130509070614 76
    0x44e501d034048054008041c00303200a40305845003880c0e5258440300351102c1c69415900c1c4025002402120b04003090001114025800b2008040c034104201540759900b15000b22280803644002ca10b0302c0b098200504144569040341e400c1000070ba04000c0e43c039032110603045c00c540203d40e01d1030000c84585810b070f031240719106078640007480140040c010000c0022401d900f100130b080c0180c48440d803d002c540d10b86651256048056400709110440041c0d4155141020f0b00ba020300600c0181041d4880964a91041c000c05124820204603442d6040c1540d000d01c0306218002d0495188a603038610010314074a01b0b001c3c0a0107405110480145505d0501030016017a50550040500d1450706400325400100000d084082010070080040c07003002103030145002e08070080182c000c03012081c1014291034007901581e4200d1b8141400c1100c071000040545912a40b14040036030ba660f52200040c090140140700380c80341e90302c2d09088c0100030b00001030a0090700e03441c7c1c84983c04440400505543c5003c1c83c20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 105077221 1250 105075971 105075979
    0x706030204080a02090403180f090c05040f0504020a02030f190e0423090304030206130608100602060f07090503060f01050f121e0106031505040c06090602030d1d03040305150601020c 80
    0x2000300c0103041c0701707884950181c0a0b14050194120b040c01300000080c080c1d2000c420703240b480000b885266034510a01e1200308240c02c003103180910304a8a00b0030070316544a181c2c4120740c0030556840e554001c0c011120204031720101642e49a111400310741c0782d62000c10700140000e5070502411114103040c4903440d0724940f076404250160403448208590351200405081460200740800130060303d54070041d041e0040d02d0b244880182e07081040041016500a00c3c000b00d41e4100041000041e402052080c0c05c100f50110082c0070395140541034494000690126030948200f0f000c1105500c0c2d03d8000c241629000c4a030500301c0059281040700005210311020701540003600c4107010740c0001515041c01c1d4001e18000310f500c0d56a40c076840e45a028400b46a494607403594204010045803a003224003400036410714000785410b21704000d60b00d014401101c130045aa0749039503440ca01546e044543e100d03402c001169a500d07202c0c9070407070300c400072281004803501180011400e6503002241d510b1483c0c001070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 105078471 1250 105077221 105077233
    0x180d0f051c122d0b1504030323090a09020c01110301051e030a060203160806011404050607050a05121305151909030b010f03051b031b0414010e010305070603020408 72
    0x44801d0b00620140480d9103a40702c052007421031070446000c04489080d504040018482c208006025100f01004419090050204000c1c070000e9007080003180c1d0103805070761281038161840990b400301c1c81400403495100031403010000f09100385030014486074510a000f0702c01051521401c1034540028010154000001103104420200c13007800394558960040c216030130300aa60321003100701d0703005071a0500c180d200c3c20071084070300fa04103000e150040d10a103015400c0a03282190280b0328021401a00d124100c002a40f000303001c410040003d40c25000800d5a00c03085516040c00625448514140c0e080c800140000400b40741100340728144441407003102d49440314030090340400a90704800e04007406000c0001101003482c1100710380c068800404580c49044c00c50800d50301d440d50b81880c01c07604032040304007e90a1f44020500100c081c00704904200582c4074400001c000e040001d9103d043c0c0300f021400014524a40e074000c0b0304817405407081c0c2d1441510740c0e004505030302c941d025441655002c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 105079721 1250 105078471 105078497
    0x603030e010e060d0212061f050403060b030a02100e19030b01050f13020a02010b0909030a02070302130f0e0303160c03210f050a050403030b0117010506180d0f051c 72
    0x1051410b40541c0020405450516210241401c0340c100d002e01082c01c018820800049040590714107001c290440080a1100c0290750028250f100d00e01009040d5510b481c08103d144c0c90070020a1200e80d03006044d101150412840141180800107115115480e546166610480c0d030034072000c00d40c3c0c0c0010410070306030f09000c02c0c003d6403050115155000028001100002d1042d84080c100c2c60040754000f02e40c01c0b001108003c54603034043e003031200301c0d081006011101c94001500a04982c0d058070b15002040102c019030000345000052200d0560500031003154076080032006600c030b2004440842d0745c0500740303003003129202802c50f0011302044c00080856941068004107044045201c00e000c1001d0b00000260f40655005130344104007240c80d00144810150036001d00001c600007031070035000951001240d401a00c0c0d040c031030980910310014400c021460715640c420400903014060008102c06450114681030000b8010303112801400d50039101a6183c040302d8000c0c018a5031014885515 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 105080971 1250 105079721 105079727
    0xf020a14011707020723010e010306180504031107261c030f09140604020a05040b0d060b0307080a0c151b02040c020f010c0e030609010c05031305011e021c0603030e01 73
    0x7003e802d001c20f600c103e800002c1c0003144d441c0c245802c518501c80f1405106d92090000d403103005400d10300d60504d41448014404000781d030701b400d9545450744201140d2030311541800d4410a89407901c03170f0210702800300c02240c0b040380ae40c0e0f00c81e059416001098a81e80d010410280c9902c0040368202c281480c5d4001e522100307104c0e0304640340d228024817002520040303036550181d50710702e03c1c84084601c1c1c00a6041205600d809003001d0010a420740741480010000c0d4000740300090001001090340da940d1145040d2074404200340009040700c041201c5910350541051101881284146c41d000c9404015002c4140e01c0b0f80101c8103010100e0b46104031242550342008058203405408804610030308d80c450203031810900035888070403015215100c0e481c0004052508140d030041c100c0c4200c0e810440c0c05600c6540c1b01c0102d9030301c890f0384039108924404a15207640035050030b80894462030010040490f0b4001641c0c01091030701c44401c0311401c4113001011840580700d15200141c04129203029900e01540 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 105082221 1250 105080971 105081017
    0x60307020c0114090901180c0306050f01030c03020702030a061d0c0108160201020c10060f080a0c030201034101140f01050f0f0c0d0306080303132d0f020a1401 70
    0x54040366040c1080302d1034002c0703108107100b64020307a12100c4a003e0000340151f58070030803109040c02c2c64107000176030606010482c1c40c1144070009040680d18072456099902c2607041e2014268010f00781d40d20b5541504040000d48000307a0003c500b03440b001d4104001d060f0000340480d101c8d030180c45000150b6281c50f1810340c0030783e01030080300c1555000c01001ca05014140040d5242d000d44045c0010240e08040300c5a18810150f0454402ca91002015001003100902450202c1e582460003089040d4220074001c24943c1040800c13000001160586d041d500741c103200320290400e103042c0507416a81c0c84800300c00c000780184103107821510780d40b0011803a510560081c1898030700d06545510b8801d41421445155000c12500100358014840c0c40c2c9007554903015990007000c84100440c00d508080080e0840c01e1074200300142000f0198100c02c280b04058080080c040100768890300d000d90031403c0c10119110205001c0740f02c1c0e803d83c0800701c2c0b410030141104c081c1d07a406139100140719030082c4240311020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 105083471 1250 105082221 105082247
    0xc061608161202060405060c040e2a0304030c02090f060d110a050a08060a05010f0e0123060706050604060f1d04021207061d03010605060708070309090203010f14060307020c01 77
    0x22803080c1c504001c50403203241010108040d074000c018902e4a402c001c0e0030040c000c1c102c1c80c030303480013044208a0381540902c00340c0c1080100c41400e50303100b141454005490382d109240c041241004c000c22041c95000801d26a4443c02034500c00b182c0d580e611444020040101c810a80c41041300b02c1000100d2044034080181e5100901010301050b1074100090090049a010406980c440707000c2000d000001d0241038010201c000740a40818200581d034855098140030f5068440403131200c40c1c05942200fa95070001c00c00180000741c0d00e20250800b10040c041c22500e0502582c1002000521021201c114908940d440011041e040b80301314144081c0640191080c0c0c2d00600401c200151440140035010040c00c0da61120075507580d24112280031031114260440c17281c1d25001c41080140c403042c0444540b107501c1030103565113029a1805642c0654550000b100142c804000030030150303155144503007aa00c12003845030b11082600200941c40c80111401c1005812006a0050302c1d406032964010038 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 105084721 1250 105083471 105083497
    0x50f0a0f0309080c100e031303021201090c06120c0f092612030919030207030803091908090312040b09060f040b120109110a02060103030f090f030b0105030c061608 72
    0x110801d0303d61603950b400c11001046142c020000e0000c25000c18807031185400034620195091030b0031034082052041c2a4840a4007522040035403100d21a401e500c203d120320703480040b0035009a1102001040751180708070a0140a00c0d0519410403a80074240f100046046c0d5901c0b4134a59080c0880c406628080a0000101024800602d00c200030240000da0040d503500c030f030a5032a46030410085240c0b440e0f1810450000f4140030f050000300340d021440c41c042d241c00280103030340da440303a04820f86413000f0340001c4241540e070103028000701702d41c10000b002c80d100d003201112440004061000c21521030351280510701c440801101c0094200a409070400e420021308841c20980e559440482c20362000030a80f186100030001400b101855204001411a00107001d504085600d00042d544e0f82040c003007e81444a00350420303241601c2455100003802084130000141907480ca8442013556007800354038428011002015154186074060f6028030ba80208a01c0382c1d10b440d030f1250402980200880000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 105085971 1250 105084721 105084731
    0x1e02030f16110109050105040614073903020a230a060b01030e100b0a060c0201020d0e040b1513080a0c0e0604060905040f0506010501030e070509060a05030625050f0a0f03 75
    0x100e182c00380300b00c40125001c0e03030010400d4070b010720302801200e0401600c002814540820312802d01d03408807103808646003010405002c08064a00c00352812241d55461a022620799060000c05a0208030b109041c1c0c41105091000e0320750051503048140c00d52070b009200c0e40300300c002c03101080703017030300320800800060500064082c2c07000d21403418070b40d0400e4a40005a01d444400100c0d080095a120040c030191409408244940d40000d464440c1b443d1000c00300b282d000618901940d0303e034025480100000c018900d8000300d41000700e101c2d04032804044c440c035120000040d101c0404540d48060540c000c1c0c881c5000c0c0c0c05c0940c030300d0888101a0003650019a03906020952007c0e520409001e04e01500c0b000141c000c0394a0b040b0f1400c001600301074101420152002c00e07549002640030140d81d0101ca030380b0825602c01d008110740948543c07081d549481908207100d010b18640c6104440498a60b50206895180c04c4080e100c520030220001d0495030200301001d24a84101102404001d40d0310340414 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 105087221 1250 105085971 105085997
    0xc02031b01023a0e0f0c0102060601120504020f09011706010f0510050a121118010f0e0f06120c2101051005030604090c1403160e070c140304030302011e02030f16 71
    0x41144c0d51220b43c400300d607000320200c602c02070302082802c5c1001c009100404803841c00ca80001c0c84800000300004a40b070704d66000c101103554403a64014100806031100c5080d613902c1070030b141c6802064100840b14010b00c0008281e035516003620406540002e0031694910300d0001044640b6444241003004000c40019288a000a81c0c040c0b0041c4600d1740900ca070300c84c000d40039041c00c44110900031070f052140d40b42c1042c007403580129400c1a1070340c04607034000b03529801801181440c411041c0c03c00044c1000ba0400020321b00d00b0025103c03020401e01a8800c0c4080341c0b024a0790ba80c000e0150a40c00389070594600706c014450380046510940140c0040740001c210355035803100f0340c096000144000080c403c104098101001050281c0071400b007a00300c4603240c07151055020a014194400300304c41004080140424842a6840c201030f5504403560341e5640d040081c0241800c900c50000182800d4035640c9900142c02640e005e018450000311158581d00d00c61100b041410f0702c4901403002d602c000391 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 105088471 1250 105087221 105087337
    0xf06180303070507031b06110601030305160803100305010506010c03050904020a0c050d090303020606010e0109050f0102070b04080114010501050315040b13021218070303090b0307050405040c02031b0102 89
    0xc00661040080c1903406c000762841d0030000c495a00901d0410000302e03540c0581c0040040e400b0304507601400c006643d10846445000d804420000290000b500001801041817007181000102d900035002000f0507121540119000c00b540c0c50058001001408550f5451030158001c100c2d4048c1ca06040030007080940d900c60601119620a20209036045010400d0640502c81564041c409182010244010000103000300200b40201801215003d01c0c4190b16402003001c803014003184800103468a9503521020b0107002080c2e4208004821031000050b594000c0080d24022080c0405503002603d131030081c40010800100c4151740302c41440c00759081c1035010302c001c103400c0e07208821142c910720700b00e0074100c6100564482d205545d0302c400010404207a0000d500d409480000b8440f507980d0b203c41c0c1d41210580500e410065101d850a1414100d82c0d4002000709080c1c0c142d211361409000e84c00728a00d08134002c614008104e8000450307405c003566001451502c50700e40440703844004000c00b800107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 105089721 1250 105088471 105088483
    0x2090105030103150b120c190b042304021303060b0103141603060302060c0c030105101d0703060305030d090b060406050a0603020c0a0b011511060408300412030b0f061803030705 78
    0x1e07941d4004203c2d02c0b0746420046d60200000823000c4440600da441c1c6184d070b102d20320842c804c0c01030441d44100200c0c4e201440e08405001454004c000355110000701c0e12441c401d1149200864245180c140c140384a9402805905000464034401c2900c0c2d41d40c1e000600c01640c0e115007050101603031032401100595650000e050501d60784001000b0043d8035006050844401400200e441c0c0c60f85141080581c05200c1100d41c01d02c404a00c4070420345800c2c2c015405040c1e2500001c0c1180404117444115002640c0080340d1540200c03041c2000362683c4081c0700490310580125900104406402d00c07680c0d010340c006011000007035007266001303505601c45180480080e004110001c44070381418002603841001d07000e00302e0080c8068030300c40c02c0c142e841540f248900d10440412030718402d4101c034040ca501100221094565420a40d58940752501c6040401040601d00101c1c2ca02103c002035401c3c05101e1051080026001902c0c29000010180742801208911035151008100c1100003810901c0740e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 105090971 1250 105089721 105089749
    0xc02130f0209040c03050910020702031509011a100e1207030c030501020903060c0f0904180f050c1c05030421050d02011a010507020f0d0510020c03030a0f02090105030103150b 77
    0x40182ca0340d50b030604000c203803401501d80c08105070800050041202d404036528000c881141401680c81c030640c404a0b081000200641c07c00c0100541000480b0310190408803001e492401202da841c01c2000030004407902c601e640030000780f401c3d0120000b03801c0100c440004c061548044401c81603880d42d841001201e150800c0311030b6500070891306801c0c02c00300720258210110f601054140344c000c0403924594083c590a03d44079a40301c5451080c200107868007860706a41280d034500c3d802e161070600f903989844420b03400c3e000304a40840c108900503600b0864400540c032101a43c0b90074500241e040081c0a15031001800ca10340c800114001395040046403031000d01500042212541c3c40c0b4040541e00c2d03070043c064148407040121000513950702780c07a01ca1050088540c0b842c01851303820894907001140078820700c0203100044034650b00f60000055840751081182c05d1100001ca516540709074001c081107640424801c0c001800000da81081e0f81390f0390415400d0000725060340400007001300d041150f13 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 105092221 1250 105090971 105091001
    0x1107030302040302090a0513060504020d1e030815130e03090315010f06051309020a020c0616020f030d021e0c06070303090b0f040b13110a060503010e010801110306010c0213 76
    0x70b400c10443c14982d01caa58481c0c040d80081145140c0381e01030007202500400020101940c91002404550715089940d094581042c1d1a150f540348840001c000c4280c400b402394007040d51180042c1030b121007031185840c85e20300680b00c0e90901402c0781c0a00b0203020383c0300003c000ca0005000e000450f45082000c0042d0255030310039214203503d03040c04040b61420a801200070050704019141d51581e40340008000c41c2c111f0100186c0c1d0b6044c8050490811036580002e6070b206200041402c0071001180c0d20b0a6883e00032107581070308500e104101540c603054200d103900075800c00c5240031200001200d40990029004e010749a81c0c001010025041e41d01c1b8100490209540c1c51703c0e0030500c004808100d0b440100240d500c19103042c1512030345000310b4001e226200d0b071110345503000100010a03c0d50305089501070b01000846844200c0500950030034000c10080d6075080c000040c3c800700c14041c0005e020341e5a5511171030754072000011144010060010380c2c0103d04084101c0841c24140304056800341d00071 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 105093471 1250 105092221 105092227
    0x60b090d02150307030c080708040807030c0302010f140603010f090b0402090414030c030409060621050a1107140f070e0613140f01030c06090b090f0414090105070201060f0806070804061107030302 86
    0x4001500107603008c2d000e2420048030034100000140c1e582c003140e6140341c25040c0420080520b103402c0b400f4040d902c0c100084103042103440b85000130000c00e07a03405014200c0003480040418160b110490344060000340041c100c0c0c6001c0f5016081140700141c1250080c050003403a80d480f00215072650b41b0041844005610000d400c210074100e51160034060400c510f029001c1d0350f2140c1004001411950525030207540d50303030100301d94404581c0109600300c5504209c54640c04a030619596a041405450825002d11890550610b0000c9406c00940311145244001920340406001c0f085182201100c02e80e07a6a0001d505071905070b81ca06481080c030941604840d60461a000c1113001c102d50140043c000c0d000300a21102d00280f0a1b034045560a65600b030b48502c0b0700d4001000760131004850383d06200410b0601007000d6040d003015200f1841da800030720485559140101c8984117a100d00c180310703004080400c2c0030a110301c1055800c540201d802085400a581554110398407819084020a82c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 105094721 1250 105093471 105093491
    0x1c0b0f030316050c0607030522090c02150606030c03071d0d060903180f060809070f0308040906050a050d030305090a12020705130e0a020d08070f030c060b04060b090d0215030703 78
    0x300700081c410b0070140d030500e04015460f90050054040c08003400c20754549d0300256104070504c10340800040400c44803d0141c028281000b940722a001e54500e2408103030b190000d1801d0920400301d0b40501c0d0780b00f02036403555031404030864458051051324080d844480303110120790b940e009100301c030340d42c055000041c10120034900940032080014051842c20794402c0200142c04100e4940301c00c603080c0d800c010440d0b555146030b41c1c0c20409540c101100102c06e403440441402600d001520998250100c100419602c8a080181104180c03040360303809403406004a0010b4842c0d00102e4000e40403904507100c10040303982d007241c80b962110342000180d1101008228521380000303808190703e4181d030200301034002c840d00b054441d0003405020340680049441c11041184182c121081143c10035026a000400c42c1307801007010108100c240c42d1a030828618071020b181c940306100440300c1183d50780740b5007001001401488401c45400384e9102d03084500b502d100c52072050045100c0e41030341c0d6000407140c0c00303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 105095971 1250 105094721 105094723
    0x50f0a050706142707050f01050702040905070609060203070c061407020a03120e04020405090c0703021507030f0608010b0a051509030601030b040303060611100504060b03031b060c1c0b0f03031605 86
    0x70b0f0404a52249528024840404e1004a070100c15100e055900140e240c1503980161a00d200d880c0b0000e420501c3c0541010a000010800394181c6502e036640e400780f03a544810807a681e000b80000078201509851007003044a0042a018820218030000c607400c001c100d030006908101260f1058401d0410701601844290b4412064280000c044508500303160804000c06c21490b07006191104a21002400800345030007007040d00000c1041d0038007103843d03207440917000700900f242101501c04503043c203202041c1241c2c103002d140756044018100c0d8000710f25003020003810310f40604000120304000c100c510810f031028803509000c0d50142e045110903041628008088a03803d034040401c00500e2008030301200404241100724000038130010407140c84d02d0400f45c008042203403025030315100c0050001101c615685a07003076a1000c003400c0e5001d1342d4450b41e00882610401c0c192541201c5c0e004039034811940980e11441564501030130101001c4000404245154880d8a550800c1e04403d802c840403c08 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 105097221 1250 105095971 105096001
    0x120b010503010f14010b090111030d0e12030123011e230c1c050d0c020d090f060212070602160804140303211b030c04060801120201050f0a05070614 65
    0xf000500802c803200100f00c52181003d010300804250701e80000700b902c01e0768070414030410086402801d8954070511030140c040242510742c0e00021500821185d61840c43c0c24400352030403588544221690b030380402c0148032a0011061545062210415103815084980e00c000040300760b8948640c1c2c001542c80d640f42ca4064510314441522240400036084803a0020400800d00d14514001110b0720102640641f403501410b000f08071071600d0051300418041c0d0010381403080c0c41c055103070000325a4039507100404c00c0c02180685005a8000d0111040c40302c4620024403401d40520001400d005a00d168584c031903002c100192945040400d0500012030406400452a02e0440066143c041f010981c3d91501c1811134014040ca035695000801c0422041440340b021000580c0d07403070740ca103000741c83e0304500d4210340101d5000480820010600b0540d0100711074100303070161a0942003030141840d031510350703000c245c1d0a410081c0501a1000140181c02502202c1034031801e0050b240c0340c0302c42c0c81d1b5a520 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 105098471 1250 105097221 105097241
    0x10050c130f0f12060e0a120e03210d0609020c010b031014070c140601030302030a0e0109080304050909070b0414090c071106030a060812210405030a0315120b01050301 73
    0x1424001d0304015224001e0000340032624034000403100711440c1d0401500030141001144c4007130040c00304403c1048100c6003550000855515000c0c0719000ca2020b040e034030808109002071a00c1e90300345801d4014029005002844ca60700700102c0c0f02ca448180350342c00e030381160000082c0381e074440c20002d5040c80c0030b00c164800c1c1c00c501d010403c0082803820040c41000c074081c08007814410f0030041c0c02d05020700f00d001400350103508812a2125696840c00968036442216403400003205c0142c140400d602c10601c2c20100c4030900c0003181002d0500307041051007030018140c00e99a1203403840000e00c1c1c0e0500c0c00500010200200418886d40c0c2c0035040c0300c482e5000403c1140c90304002c2021b0000140f03010000c507160341044c1c540074cc5035030314105c0b800700600340d54110303000e04d1241c980c0c1d80a0b407440e81e90051880c3d0310b05a02c81441c80b51b01c00c2c540f90f2070803802d9030014843c1d0014001001980c1c803a070b00c106070340c12840e00041c03901640c0300c10b1070a8810850a05580600850006010703030706090007004458 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 105099721 1250 105098471 105098489
    0x1b01020705282607021008040c09140a0c02071703030709170d030c02010b030a240b060a0c060b0a0305010504062004140402090402030c03090c101b0510050c13 70
    0x120b42d56540c41030307100035114071159802d5940c0800705482110b00b610b03c41e9501600d260100428114054004c0d20200ca049500d820b90341d0300400c506600e4044d0204826440d58030950a0300e9022065001d05030440f080300451160040018111101d154591100b6248501955a03810685070050401c503090b000601785d200801c1001201c2900040c82007442e001610f0001508074211900700c1c090441ba0007420360500c15118408144002e00c0101d81802d84072190b100c500c4000c3d080403200740c450340a625035201205025940405000310790704910680700f2540002d080d4032003c001169040e0a8000740e03003c0e950707030041000f0080140304045c0441c13003405043c140039402e800e64580600ca1130003410b5041080140392905a10380350150f071720401004005548a01d800c1200c0900c0d90022030b4510300500c12400d9800c06814107000080420f03030103070f80f030b904641c2c0e060f10351f210b00f40d4429000310350b24406d050f6049104da00034858a40500c209c913501d00c1d40e40402100d141c611540035000744403c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 105100971 1250 105099721 105099793
    0x30b0906090c0f0105091818010f06050603010b0c0f0706030e060f0603061f08010c021f050105010e1c0204050a02031005090606041e031704030c0e060310021b01020705 74
    0x55443c207200341031000f802d20382190340f00b40100c04240f08000000101c2d11406250b020311090f1070000443c282c0000d5010020807848600b854100c05450b40743c46190341200c404c1005008015a200c010b1030403c09400840b060f2942481449140000b0b035882180004e0361407011020042d000d103d81a085560b040707a204941c1045000a034032150058945c0c0b201c1e145070029440d91200c0004000010000c1c02c008101c861801c0f4406511614004000c0005001400705100c18039654811309050700d04c1a51507c221102e01030030710525017944190441c110307103a010307080016134071405041d105004030b550141e140d04100c6806107141c009500454401c101003420003115440305800e6900b12829200c075100e141450010394415441c060b0030141903c1351180c0761602e071020320001032048a01c2043d0740c603c01e81d564408060181c000340c4c1c3c940d03850f411134840400c0804280d005003245554901c10030310000401c20300d00d42240c0c44104200c1d0180c1141010f0588180400716404145580000c1400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 105102221 1250 105100971 105100993
    0x10e040203071d040f09050307050d020303070e040b1c060f06150c020d030309080c06010e060409110904050304211505041505040c0504020d0e07050303040b0a05030a020c07030b090609 81
    0x4501c5011612074141c80324034a01903140f6964a03004a0007160090808000541c030b14181039469900c01d00e01910f03103200701d100350071140d8400401c60740305907459621185090709204c204009007c12a59040d405241450071030444445001c2d6042c51038072406002034402030050f6003205071001a842104900c04038180c2d4140c0ca500549038601441d81240e01e04c01d41c65052406500030600488050026040071548141c0b1150000d5120b040c0d840c03407250b0f4161581e8120411058601c5208010852002c510181e103c6040029410f40c00622940c2520708003501c1b00c00e03c4507007407000c0340d00c01240d2560342c00042c01d01c80f40c10445007003681014401e010b41e181035201c500034140400e0300520f000d6540c100241c00d0109406410018000041065599550002c0345c1d9014103d020400e043d00c2c064003a00003502d107000011102110078401d641403c10502e01000d45407501300405207000b00c3d80030026080208003e002c2e18000c0d500c2080340c40080d003000d1155924064005280c6801644100b121207 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 105103471 1250 105102221 105102227
    0x20304080a030305040c030804030b0a060918031d040f0c0806030a020f09070e030d0e030d020616180f09060305060705120109050703020918060112090b0f0405070e1005010e04020307 80
    0x1030794032034060401090686461402c0f10882c21107601c045d140403000324001c010041400080d0b030043d0040002401000d40311107400b0300701e4941c110316120050090240000180c042d45170360000040070840d6003a44403015000ca0305a90010480722861552001410001a006000c031a04000190300404c10841c15a001c21420000301000303500c1010440e001030102c602c1046020b03c5014094140e60b2945104a0040c1641203808013043c864050351003440340c0c90348006115480b800c0101c0c0404014200c5610039541a00402441807036010202c1e000b0400340014000d5800510f50480001002451410000e003480b002034001d00c1080000c2201c2d440d03400c400d60b045419203c825070009044e4482c1c0800368000d224a490640c0c002203000d0b03140741413000c0840d03881c0c4182000c0e2211120701007028064001c44004983c0103120003000e6000c145200e80c0c2e0249154071500c0b5104031030020b501c40c0c41403441e8410840c2d40300c001031701d12380d818045541d00c03900c4440851001d407400d40c01c6041c038081c05 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 105104721 1250 105103471 105103483
    0x11040e06210a0803010e07020604030206180a0b040503041509060c1b030222180201410c100b030a020f04020d0f06050f010801050306011701060306060e04050c0102030408 75
    0x10078410008200ca01040c004110a40e00c0c64074400340c11104a09481d2600c1c05254200344100c9048910b4200000d4500c0d00104a8a1046a0641c09400c040da0f510042d000c0e80c10411316542c08138404ca00a440000d0901402940900e000b100215100e92400c20544042c4404031081c104102100408014040d00031583c040c4003540141e01c1d00c503071400f940c2d6590182d2481e90000e903002c0c42d4880e0701e1244124841e0940d00000090700d050010080d240b80344070390f2600c150000dd000030814124814074800c0c02c140107080e0920348001c3c400411303101c1d4915040d042104e0100c00d8030a000a42c142000008111406858a1496051010194100020381c454190b8080130340522490801c0c030080d561954101d0b0500d040b802000c00070703401840c10100003406517000380b60082c01c0601030207a05600417120709040780d8008008144a80c00c0040d0400a0303142189001642d43d224440032001410a01031040a0309468806040e50710300741c2445860684030342140c0b410340d0000c100503c04540080b0340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 105105971 1250 105104721 105104731
    0x10020d02030729040809010e0402030114191e15020c090a1a0a0602070303030f05011a07060906021918081b010c0b04050604140105010b090f0607140d0311040e 70
    0x582e86140780a0341101c812032041c4214404060310f190200b004201054014121070310007aa2000705002034031081c80308a200a01034803204040042c82403009182c44000300e640e8001032900403008a650380782421103043c11425802902d01000350920405a1081006403615030601c01010310050a00c089440c4ca0f0340039101510f80c58076010300050100002c2c99604200c400545040800b660390030000b910b032000ca0004600207070400340c880e112001180a8103060b81c01c40000b450700d15020b030143d40240e0344210011955961200c00c8130020903c075102074150550b00303143c44031007900c14001c01007220014203902010707490b8038078003800710000010300c40098080c1d80e000d59440042c00c10050365240c20200005003070002c84420401002001328009028900c11108062030f1420442010f0a8a500f405600321120082c0044111440c200094003020070020380072500d410540d807100c03c031005000d1400e90091348115600005113926100e44d070700c64102080c095003000e080901c9014501c1c40030301 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 105107221 1250 105105971 105105983
    0x10603080f0c011506050a02010e0309030d050a090e0a020403060501080102130317040305030309100501440616080c0723010e061303021c080a050414100b10020d020307 74
    0x100a000c2e07041c00d501c41c0c507001551149a14100da40c580004000c0d50103001c11100650030081c0c0c002011400005440800c0001406030440030302d590011502500507541113801c10249900c00a0310b402c0080b00f0743c0c055051420007680d500d065040403020741e9010b84c0104020303841001040d003040401c040722810340fa40071500804480301589525841e00440c0c101400d240000414040c0c24140062440781c078100d00e50302442280c0c2d9800310480110180b4100c2d14001c2007403841600e6540c03244240c801c0c40c0c0400c03440b5024864840d4140362400c44100c0d0410140310701044882c0c0c0c55500b0001a503070007107204030001e151103410340d10f10307540c040e10701c8000032010100d0b8194140c0590a401c40e0401c0242c660480310b05190181d102090941c45920075005401081140c0244400700486000d0103016034486030030380e80341c5504c48802404014402da503000c2c111114401c0b040d07404e10900300c0030851140041140100c0c4c10800241404034000103056511006070080b4050300401900c01040e0418 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 105108471 1250 105107221 105107227
    0x50c1617091818030a02060109050709240905040b1003050604140702250e06060d0912090e1f0b0c0c0a060c0303050709080303011e0306022a010603080f 67
    0x40089051070081d800c986620900e06406441e240100707818043c45003800200000c0000380c01c6100c20b440c1e219240d000030050308000010b02040c2c030260860b41d0402040d1501c8150a03940c4c02002c0a82c94130354048014111508003080303150f0f60300c6103804010b440c0803181008080da0000c00034901e034001000703460906031070f80d0008600b60390b2a400036560000ca030040d03800601d00350b81c000b03437a03210b981c00f544180401405012008014a43c50b40d05070f44020b40981003d0310303000300304001904007103411a0750f503459248050020314142000100c007109030320740711201403c0a00040c41134034028062a4140896400311180070a0640c403002112501c00f241d039074502680c050300c3e0402d24800900b6410020040c070018545900003450707030309940240d0702003209072600b14003100c01c50304500c00c00500d0b83c41840140948040d8040c202170a07050701c07601c2500a40c0e2a5250400d0380c002900c0b03c0c2d000c40202003125400c2803100c0018880c0c03d6203100822514ac1036a96000e024000d43d41c0e9071601c10008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 105109721 1250 105108471 105108503
    0x30906060302060d05040c0b0304050709090807050111091c1a060117010b030a0507020303040b0103020906060705061314190b060a05040f0504020112090308041b15090603050c16 78
    0xa03849400a103401901940d581c01807110701c5000b0f442d060364100c502004010740010141303000c406503400395900c000034104661034060b0351400340042001c20b0360810403c004110000310309205e0b00005035220031032580c0300c815800c200301c0140083c001e00e0b100d440c00503190600192045000c155111110340e682e840c1e545401004948900a02c054988024080b41c0041114204000614401d607200314040c0419039500d9000c80e1280001d90700201700301c10320001400180340c8541c8441d480302c0c0c06007019082ca245522001e190010541e40010118521303030754201805001301d184160500c000303008180d01503480f50007082419078008040c0885a0780d401241843c4d441114080007031100030000d05c50085a03241c40001080706580883c080b800c1035218961300401c5000b9071000c1a00350f00c0d103180950f156210000350b018203c401d41c10256034220081102c0101108401c1d1190950fa03501386030900b40000602242c0002c1c00365920341800340442e43e03194001424440185074400c40741c410f41558 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 105110971 1250 105109721 105109733
    0x10605011b170f0a0e0406061d0d080919050a08010603050607080a290111010506010903020d06090b1f09060b030a0b040f021c05011208070209040f080703170a0c09060309 75
    0x11800f46110380c001c0002c080d51000c0e0301c524590040d01c01102c0400040b540d403003041c0e800154401c202c0600c40d1001074585060300c3c0164259000c280208000d40c901a86400000d2101c21714196015031300c043c5250174070030703400c0130a4018090b0103400003c121150450b1519669400020038980400c0401400180c407404207401071410075051414507161500c00350704840d42500642c40d40ca000560040041c0302c010414000d0a00542061b11403114050035030f000c0c4441400d180313009550940d1554488800a040c4442c40d510804414180c0540310b00f80c40300001c1c0d480c41980c051801c8a00303045c000d122034402107003280d4000c40350300d070b00061580418000c10068070a90741e611001c50b00c00300e03a00d001d16905800841c04240700c624100030303ea80303c88000b240702d0300140c0050700b994400d01c50440181801c0030300303e4009004c0d403a82040145980d0340c0011660001c0703000c40000e4000600300d020894041c04484d0422020941444160041d01c2c004040544078030a903000c05481c0d584000034095 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 105112221 1250 105110971 105110977
    0x615200a020d0305030f070f051c1103070908160806010b090d0c090e1009050a03030b18130209180a1b08060408090a0e010308030103080901090801020c0609010605011b17 75
    0x1501500704100b0800a04000d0000d13081144c406089104450000d8545441202410403142440c0c403402e0070318a000e22441001c0481c0d00200c0200d50340c0360602810440c040010b1403084186070f860550190405124a04000407500034400422a014003403142d420049400c606540c001400c458991200b000050140111b441010305200180c90001c2801c4000303401c200843c20b1810119041c1c04110340401045929900b000740c00f5401c0083c2c000c000900c00d81049c080000000c00e100c5084410304506403040c07905455442c16040354051310740c01c42c10f002c2e00da01e86c05902c4080d00000c45500203640d944411a400f0010041080c014690328100c4505400b040a4480c0170111f8070107203814504001c1031f07404000850311560207000d00140c18103100903454183c961000350242564039650703030461280c1011180a040c094121008600c10000f4409040c07240c0c075003001070289041003c0707160b0841e105500068100301c0c0d00500100045034419107011f449904c84940c001c01162070300e8020440c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 105113471 1250 105112221 105112223
    0x90209060d05071808070b030f04031808010b090604021908060102070f120506010803270a0e04030305150f0d2d0f051501060c1e1e05010615200a 64
    0x24a44001c0c00000c1e1360000290007100340c3c0c1d10802e02850f844e9100b0317654842140c4204503c8900810000382060055840660424428148044008004c2c47c04010300b200941080702d403a13640391859881e43c60a189415041803081c0c0b421890f200400c4912080a2410f1031440140200e0501107002c90f4400c00041d0001e05a44031405400c5866031402c4000c210030b01c2c01540c03140b007254008500a00301100300e5039140c10800b04082c0c80b04090051042694000400c03d80c040d1004a001901d45484603e82e48120300c030f0394001590f8a0089036100b40350300e00200b10390180c84950303440000d03030b29081c180c8102180c0000d0f105001000c80c62000d02034000d04c002142c80245290b000d40300b0084601c46c04034016103e6010344080c00140b00103002105400d2154070b0000e198201490046120300900c05201e034020034888407114441c0c0ca60401c100074220100d408440009400c0c000d0100030f03c200d4002c0c20640002c8110340301040d0000741582c0c400f9035140400a03440740000011039003041f41030121 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 105114721 1250 105113471 105113497
    0x60801030818120307050c04020903060f0403030608070608060102010e010b090112050709020f0a02100b0102030703050705010e010515010e031b100507140102041401020c0d0303150810060f0f0e0109020906 90
    0x10003e41000f0b0307490b0f1308195022100e6104840c80f04c0c142c1d05d03150083c3c4542002c0603005068981c0c88140c10481d50344060030503014541e40d0390010034900400d000f0100034100a807030356a8a800c02100090864440301e80316019070340742070f528402e640e0320860711604441000c01c055032651458108142001555840811b4071440003c02e80c0f005c0f0104070140035165041e0f001e8540c0b0000480070b6205030f8030203210260060704200460400a80500c015040340d40c01240005a40000c90700483c0c21144292030340c0c0540d41044485400540c2d20031014181c140d0187d020b4069032144524110040079142c825910441d040014403641d20301c5442950000b94001d402656060360305102d2900030751181c05400c880b9900003003490455400081c081c002584060109002d10050791401c030700400c2d040d06007040c0c0312a092400981e88104005030748012510050000e038061a10084d5100303000310b50f00a009418014404010f100c03a0080d4450458202e00030151351040c2c21000120188038000c3c0030064 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 105115971 1250 105114721 105114739
    0x20d140310051201290909060103080306100905030a0521040819062403060b0a0e070e12030a030515030703020604030609020f0402071a0612070501140408070608070206010906060801030818 83
    0x888a1100c0704401380011340706c1c03140f69218501800c1c1c9034002400081c0c61000c0400c0070500030306021b1605031203035015103000e07902c080d11500001e0604104400554035584030388039801e1400002040801c2081e401d664440c82c29107041607160b1034075000310144030980143c101050a10450360082d0701c41c10300300c04040c200a21085a852118205408240c030754902c0c14000407034906004860b002915900e180418103503540f80021100d41940404040c0c101824045c0b900c1f0440080010b000d00c40590344011645281c081d420341038150340c11040700c1c8039501c4400108050703280d0004540980e900043d01181c115a01c1c004140d140f114014051f4220b4030005901d800d0200516000e01001b40a40d000181901c4940c00c120300714256682200c110b0304520010030056018030103c021032900c009840d4105561080f41c0c4e8201102c0e0b03444207001c60f4031141080040c40d4107204e800d01504000b80d04001c05803c2100c014140681404000c0038080c000683c4003581181c4082001100001400442 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 105117221 1250 105115971 105116021
    0x4061a040602010b04060f0506090a17150f1b0a0e03030a09050102010b0910170109080a030212070203031006030507030b030106080f010c05030114040902150703020d140310051201 79
    0x2055511511800d0015440d04080e035a02d0b240038040c100407140198003411049003410104078807a4040c0807101d9100d01000e40000b5504444107940788c0140703c403c05000341400d01018503e180b05c000b041000c1105550007000314940001c0301c0e03c0103400e5812091074a40b0603a010a46599100b000302c50b9140c40701182456009502448030010f60b0000e0b8001d10074034401d4801d01aa170541550481b412900c0118148200ea0b19802c0744008968407a00204858000d900e42c001e82c1d600c01400b54001079000909000320844408c0308507002311080c0700540c074502d040d140810b4010098001d0704100340d00d039001305017610720a4000462040c4024002c010466840e15440c0d0340e5818500c41421035402c1500030003d050041003564102ea4440d0f47e0030280769011410040242010351080780c1c0600702c0c0e2000404e034030544014005503886900107181c0c149034000d002c0c1c0314156049420200031010820048088101c9440c002224410b0310115400e0074160002070140c510029003c0c280f0280020043c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 105118471 1250 105117221 105117269
    0x200a030213080a050c2704080901030b060301090209120624041409070603060602010b061902030f070c050112020a0c061a0d110f03011401030f060b09010e0901140106021504020406 79
    0x11a411404607040c0c4550842550206c1203c9520011203020300220700000d008214440018500503205250000b40740c0714003400180715030800c2c2c02c40030100742e000c1622a19030401c00d21303150a09000384000c01d56840d108030000c40c0b81c2800e07016009000c03042c0001495580b00d07a0454080901c086e03480d82ea00e07144c00b6095030360f541e50728440c00d40082c1c00d060b800907003d801881100c005800140c01e2030701c1c0c100328040408008003403690042c01c51008100055892040c000a405c5007480303102001030886c5008001070414184072000f84c2e4043c81004294000c4c0e4114231100c80541c1e2042001c20b02420b00000d0b0304101604100642e042000c4808800c204a0800d10b84030a40c0c00456201085008450505080b900c58820a003180b411040c01440410702c00c20510180c0c6100c0c440200d0f405010101081d0300200c00c1e40900e01039442407090004e070030820301030003040001904040c4000e40c94000001d540b151011031500f440c920306d6001c101036481e42d400c410302404885400140307203202000c0d0781b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 105119721 1250 105118471 105118483
    0x1020f0d02130e10030f05160627060c0f020307030209070207030506100303050a11070f03030903021e0609040209150c0a03020d080c0a0302030703200d200a030213080a05 75
    0x301c1904852020481c9801443d40c60300501050040c0c0c540b00f8215030707601440112103081502c040c45041119080a0445070020000d40403030b07654882501d850103903290844442d250944000d808521081c0710466101000c41c04964108148051001c420b0012900703010312600042e4003e403204082194258000850354103c070312482c1245c08a9446c01c21542d0384a03100e00000b800070328200311011a040c03003000d101c140100c1140a80c0c0c4801d0b9240b0714411070451541c411400301d5600340c070400a41c60a1403403882c405c0301000855000202100c00200984211039160388282c0d40843c80b2540c82c0c641040c699003400c1c02d80324807a500c4007a2030381e2a42d65264400224010705c00e110f02da1003900c1c800e4100364000c010006c00d02d4241680060242c010b508003c202e03104140c0c1e198490340c4100b425440040f4840400c1c101d183c2e0368404040944162040c200e200800841c401180c810001c54110840303e50401600d00161070302c440c0b005402c034402940d84800303068854045501d007845804200 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 105120971 1250 105119721 105119737
    0x60702040b09010b03180f0a03030b01090b13360e0114011e08120a140c1005070e010e0303090d0303090b040b0106030506012f010609181a0103020312070501020f0d02 73
    0x742006c2c401d00308658558920b0150038035032240d081004c0c0701e4002406900141d06005050400400c149c0d1104d100307246a401c202c0c85444580b0007500c0400524a10001c3da04104610548000f10100d003142405030385104110f000c0300c8503555054800c1d00740030070341c0824031061650030001c010b56502c4203000300c07034008258003948201c041380700040ca000d00080c4120003014582052070812001400a8450181414402145074802c0080c076980c64018000b0400030719180c0d100140b242005040203240c10000b1808038140030700701c0550742056034004152500404111040503650005140c02c6000c3c0a100100414204003403040c03000300020701040c541030303441594040000c0d5864500440d44109185a40c0c0c170900f40d002c180d452000c14020310956800c1c4081e00100310f0319910104a811034503080203a00102001602504c20410700c4291032841c50100c00480021b5410f60300066251601c4c0380c456182d90000003000000c00c04290140d40c0640b050240c45030704d500096400001960010362 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 105122221 1250 105120971 105120991
    0x2040b131802040501090308090f1315080c010203071e02030106030f1101080c040308030a09140703021201020403050304060804030c06020a0807080f0c0a0f02030909011410050a0e060702040b09010b03 88
    0x44600d0304101c451003600c04903a0165240001d080ca15114628a503210100c0c158000146030703804120b50b124400041d50481500c400007450400524503c80034110396000803645410144482199a034000107407042143c200804007800c2e806100712019440381190000e4055080c480c00005110322442c000d0b1600c0c1c0a06841020040c096004540280085171234400c4181c0602051020400d0400a5507101300050400100581603407641d00805035201c01d92103042e4800c01c2d09000710b00b41006500c02032400c2c00000e41c10103065039a11602da01682c01124100010301c0002400d051080c40704a0070250006003c550703801ca4a10010301142044a0000109926a0200795541d00c3c11200510031030043c1801410b00054443c02c94039801c00911900444c88280050007450b950302405500070289011000d802c000d01d60280085070f003a00502d00d007400818000c00d82c0e455007201c40d820007a003040f40c08559900b01803000400030403004000301d4000c4010000401c02e110707060011801106c80c1d40d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 105123471 1250 105122221 105122249
    0xa020f120c0625050a051606050a06120804050f03030f04140906060a0806010e0a050312030405120a0206011202040f15031e15020f1e071203140403110102040b13 71
    0x81000070101a10304200c9820454240d1101c0c3c459204a000d0700708400c181ca030191810002d00800345a8040c442d0f000d607140380ea80c50501c130440f2060311401c001019401d0703072500b0b410540d4807a0045401607200719030080303e0f960200c00c0169424011104202600103061b616540c540503201003214074454203d021b80f1038000802c04c1c526191301039600c00c41c056941e841495550fa0b00448613220320464403900068042030101d09994144a40c02e014802c201c4d006890b494981005440e001c07254500d448110420001e0401c15540418000e06580030724048060341c1d201f61001c140140500e145810005290952610886614000303202c21607000d001c3d40b8190050464820f608141d6643e80141000110403602c161240990090a00c020010400c58180401913040710b07280c2102000c8400c06460004036901005149110078200807102e00c3c0c00c201c2c040d00182020003a03540500041c3c1804140004225401025012100a030071401d07101504c52820341c1d42544c92505a0141d500740909039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 105124721 1250 105123471 105123481
    0x106030b0c090d11030c04020f03040c0e0f01030f030c021810050301020f1b010605040207030f08010b0f0a11011d33010506070609050a0b01080d02010605030d03020a020f120c06 78
    0x2402e07a050007200030942c03c840a0650368070504e888070b9550ba2600f600460341c841c0541e941d284040c10401611629030b50b507038542894200c52002d040d800403603c07008002e060040724003041000d141526813040388081c1045490400f9501c501c0840b40096004011002c1d400e04681c1d11002e860040da84a500007071070039202d200701404e0b80103060800d81c001c01e0501a0070139035240d14092410802580c0000170781281c642012800342d90040300150041800c841900d0f20040d40412032a004204800a09003404800c810043c484d100e411480c508210410b43c28904000c8290b0056007555245402c29058040751141c82e40c6030201040009642a01c0030082000510340215507504043e041d041c5818981c2450704101c42074200c17180580340f0599450381c1340c0010700104051142d4034003440c85031209600d0080d940d441d000d4140d690714116414040200160f840020b41400c00d0b80d014100940c490f050700703404a162045500c10401070344100ba0b818864000c040c0b0041c003160b03803060255411541d0b8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 105125971 1250 105124721 105124741
    0x80601080402031020030106170a1e0207031e020d031508060112030c0c08030315010c110411130321081e0c0f070c0e01050f0d02040b0616050106030b 66
    0xc41d00650103400101c0400001030305130f4084205e88001e11015003072403008050190064000360400004240030307551701070711251024103195100741240024010313628948030140d0305628440e40a44074036004200b000415025007005450b810707040d20b540341103000000d8000c0d65204007046840c003280c6810030403001102d400e150340c0c081d202d21200400700c50b480c158200480c038140c61001d03000c201c180b00d0f10f003001556441e81c0c10010000940259102d00b441c51584034210b14448400f41030101400b04039000a441e55403611041c5011140003032208078918041055119440c20f12103000d4000b040841044485010010b00c0d82c580840c104c0842842c88043e02ca11205654100071000220720b120039600c1240c440540c0286061209820450464030303403041900003c40031605c40c002068140a0001c042c5001c40c014481129038801c41c10404020508245640c1400303405152142420f40181e1138440c21180381c10852108401c06c0d12203820101e008010f00e000c2220080040b1010803c400305c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 105127221 1250 105125971 105125987
    0x50a0905030711040b0d030201060509010509090606010e0f030a060501030c090203010e0a0908090a0311100914121504080c010c021c03150b0406020109030806030102040b070308090709050a0b01080601 88
    0x3600100075454005181c0360341210700303003100c891903009448020000d5180c07242401d2280041c840d40002c98014201010002c4a140580085001d206100d00f0009001f000041b070304d4100e002800c00e408910707898400b00d6441d1000850300d540511880d41580c00b0000642e03c814101d80c041c3c074460140c261107105c2e02082e40300078030400154200b0b44c80800c100380104e1348104079641c8604503c03450100c2c0704004c0707000d00c4810341c41918418001e240d140c2c0181000031809450380b080c0d2401000b820f05007183e514458100d405040d02601c0500c854048603003040101c01d800601d14420780c6031500d01480c1164056000f40d411200315400c0048125070b5900005200341c11014100c00001c2c4c0c0010140110010183c40f207480100c40e00b005000204217594a00510152809a00215000c071140c1406032a00b0006841a4000d82c41000704102c0442042d00b91000b45900d440c0400550b02c4d01000e207880c04255070002c0340c2c01c3c0d20b013104740040716400d0b6111114003102a290600540c1d101401911480 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 105128471 1250 105127221 105127223
    0x3110903060708100509010f05010314071e09210302160e070305130609080c1603020306010b0a110102040906050907020613080a030905030313050106050603100b310504050a09 77
    0x140c40031001c01c00b03030307406104980d501070800581141026590303800148000400c0e0300a0f0007041c803d40c01400a5645400b42445105c1c00782801142410b21203401801c2d004112800681076150244420449209200400c01400643e1070000c0006192482c2003160007c41d400328058071444a80d548141c880586400454a403241d0b045400d0790340c00c00503000303404003c0400300f500f4810022140000d626100700510f050080c203082d40c951040c240894a840d49050742040604203a80081006a0780090410306440c24285074503101c2010b0f4205a44034400d854842c8100d5001103804101a00c1d580e00a03130496004998104550300c40c568103a82311401a140340644a41c1c281d0b20b07030085600c1c200108890007081c58005256455921114110f800544003e0000b0301d0740c0000307109110090103a02c0240038121601441c0d42800d800c280807100303047c0300321450803002140d0051000f58840003032007410107020020690121a0782804030040080c01454869490a130109500c40294404c1100d02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 105129721 1250 105128471 105128473
    0x7170f06070516050a0b01051e060706150e010602030309060106030507020a110a1a030a0609020322020f0603010303020303090f0303060d0611090a030b072c0415030206130603110903 80
    0x3076200d1120440c0ca65100c0c0d80481c09004000810b9000500c017048021529801024403808650404c0c08001da40b20f1280341e14001c04522150000160b50303502c049601540c0d01902c00114070840d42c07840d817202034881d40f003400d0b03549901f400043c4040c1c020004520441180e0107640d544c3c1c4e2a00b00a80407034206465050050b40081c0d021350000303809401b01d640d94503009000c00c40c01690769880342281185490140e4000c0030100901c005e0f80c3c0c0c0c46c080d03200900035601003541140703085803100b09030b051b00c0e11641682c2880f0050030404e5458074031700001c111202400c2d031550382d82c59090195403980160b8000d0712511030b94805e5400b804011040d03e00805006041c00020142611102c0180035505e40c1d014140d50204510f1042e07a03500080348000314070402c982006032810640c05488ac1d800c41e8009a51072800e080350b141d100070b18104a41504008840024461000d2608801c0100d8a41c200a40013440041d0b03c0e8441c002c01d098030b900f210801d41d0b00f485400c840c0e10103111140103800003e901 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 105130971 1250 105129721 105129733
    0x40510021e07020a08010510091b02030a140c0102070609120c03080105040207140601060f090f0501080408030a1b030515010513090b0d050a030306140d0506041502091207170f 77
    0xd050301c81e8005102d01400244000b101c00d0701c0301c44e0365007112000c2e100e1140f0002c80007002c000c21034a500a401d50401c41e20320006204140d000040c3d101d104800e214030030010300c05003004110b0000c1096a03020b40a0314021526003246242000003089003e0059034820103884200f84102d02c15698240c00640c9913441c902aa460700c1c0030300c4041c0d00014403c544c021842480e500020300c3c01c0180c64000c09040d501c060907900107041c00303003941000380c00404622040050130b1005907005850030303030404da101070020394aa0fa440c09280c02045134509007103100000407031041c0d549501d03400685c02090144180681c01e03d2890042d2560300c03075542c40302d00c0500009010007041c02c49034030031050820f0150985c0e90790312007507498900780956134804902003a0f841d58244002c0c240a032030803050003015100c00c030b03025003141c070b50580d11000200000c00b41d411002125640840c6034058464212010b00f4416450004400c01900c442a074001d56454231107040f20150700c604002a404050070105000d0301d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 105132221 1250 105130971 105131017
    0xb0301080c1e01171504110702180f04030c03030f05040c0f08070e040807050111040611010c03020405010e0d0302071d18010207020603150f0a0311010e10271d04051002 74
    0x904200805c0c01034903000344280110a80c41c0e60107010080b0070314a0000340d0345d01180c8104501c3e00340e41c100d40c1c40103d1411041250355040300b0701898100b43c00d814480c081080320f15080740036002c484842d1544504144c18401000b03081d44985c4195440801902900740c0c4403000c0550712040703403090040034404a00483d021480d407200800c0070b14010000400c40491b0b11203c007026612660040000809400c054080320b8428801d41010041c6440c00358070341031a01c0c0009040c2103c0c00324652290545030383c881c0c2014020011500201070703d804d000701e82d4030a00c458a0200e2401c44a90480d0340030350054100340c20061003160764250340207005508584840d81d4828004584440c015001203402e04c00304e02690364154080015131241075403440c1042ca00c0b00060070307420207458803405811040000c410355a0401c0302d1400d00801030b03426058014090244420134a07496011141d242d11041c0202034108032102c3d100e21440c043c00440700032419283c04a4100c0c0b20307106c0070066003180001c3e084 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 105133471 1250 105132221 105132257
    0x3020903030706020c03070b01080106050d0303230a020705060105030d1b2603041110050d020c070b04030308060117040507120f02100f020c030a0c09020708040b0301080c1e01 77
    0x18010028080302d0500d882d5076501d100301c1e800008040900d92012410000b00f0404030f400901508044c40240500c48c078160204100140700a030003820f040d1104440210200d2101100e6a401603401d11210345040c000301c000000d5120101c1600c16010303d000204103810000346109080420755903d400410401411082800d1042c8003151800a910380e141c00e44038550050448809040038003568909280c500b4040c45031040c0d840a004400c00b2410740000c68001c0281c80204026480141c0e80340c0c03917802544c0c00d00c04160000d550008020a001c030503d6442140c0c903110702030a072691940d0845a68080c40f0545080380d0040065100034030600c501d45032491340c0340b4100d100c0c40b00c0380c0000000750300050f00800c3e0744641d0702c0010045542100c2c004d50400c1050324582080c1d01500003ea0315446041c0038039111300031114050b03000207858042004500888005000c01004a6240d507141c1040c1500e445285400511940c140c00c0d0801820781c01080071455528140c40d60024031305c52107000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 105134721 1250 105133471 105133477
    0x917120703050a020a1b0905070e01080604050702070503060c0a020106050102030313030c1707120f05180904050a02030f010c030501141818031606050a060305060103030c0c030c080105040212010e07060302 90
    0x3608601950410100284010300c004071010300110b1a00606e03420401000304451000b068801000703011101c50311140d0f000090b071a0080302c15940482d05546000042e454841c3e0795004030341501c599410400500e00a2010b003140750314540c000c0c01020307500c500480c0d803800242c1e00314503001c1440140307900290040e1103145a01d4803400880c5590100c0c0b41484415410210055a46144100c4440c007001e80c0015110b894540d1802d10760700388103407482070300b50041d24080302c98004c0c0245000700303051020822071010a15030003011100d510b640c2c1c40c5680e02902d806d06d40b41c0d000c2403c143c0081a5140c0c05c03402c00a0a403c0030f00307803c0342108456540b403d444000f8040c4406030300004070b0203014110610040c440c406000080020760710a920701103080340c01c000e0404040324907000d400e00014070040350083c1181e40600c2d00c40b071402031900340b1445400d0240d01c001d18004803c0c4000803000303019044603114034002c07a141c0d00b11001c10f03540c082c240d030900500c1c3c01081e0484142804174901070750103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 105135971 1250 105134721 105134737
    0x70c080f07031407030f020d0f0e0d05070312020708060f01052b05250b09060f0a020309130509101a0d060608060a06030b0a0b06030406050601031b091712070305 71
    0x45a0008510601c1100b059400301d00c050340040c19560591002d19010402d00140c8c1000740303807021491801c0360b0000e2110214018140c401c94865540c001482410015500619006052402e6080d401003000c0c0d030301e0b0494407410029009150024071400d0f00d8080744c1c2e04954000c1c1c0804481704160303d4030104141982408401030300c2d40da000d040451000c01101d00441c142c50203c20080b0350055032041651450340c081c0308454400c00400219480364002d6402900c4035032525615900c0c0c4000036403c6005040540760009003600007100c544110340c00c03d901402842c3d040d0381c07010307003124154010b0303c00c2c1c112284801440780150f4602800e1500d04920f0903030140e1b6000451503110403031141080029247c03803004948500d01401441b00c0c5000168201c690702808101034914840441c40d10b00004002070048c55075440062256406900001000c4d20310301c1110030240145800502140100e02480e200c04040c80241c0c2d1001900041030f8080d0f10107a820a4200a0320395021280f41d800209 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 105137221 1250 105135971 105135977
    0x3050a02092509330804150f06050f121b0303130828050d030c0c020d05101a0306060603060a03150c030f0515240a0c020306070c080f0703 61
    0x12000b000c450b8803118890900c2d03881d503a400c046030700d40104040c81400742a40211070040c10301542d03502803131020b0351100c2010181401c400f80d0783c0d1401d184a03038421503181c40d4211820b201d0307440310702400e603802001907910440e07204c44480c09c44401d102c03c1d020400c00443c85580800104c6256104c0c03100c0c0c000706118010126450120381c07031503041c8400e0159010800d6503001900049520300441003400607540c54030b520350800c501e5034582e203a641010284a9013031543c3c074006135560611a690182102e5000340c03480404c03200c03c1c41c040355580c419941030b1103101c1c5854545004200020ba00500402c0001c1c000c000603164001001a030b54000340c1080c0c0c0c000c02d01d000000002d90584003100102c4192607002a6050b40020041c0030f0b40e402c0001d0170031443c034040801c10310680451410b19000010307111606450100c0e4459408a1165a80c5100000d804541044100c0c0d004003120304480c420303020b65000ea1210707081500d580b21103800003040e035076091000c011403200e1003002d0450503000c2d01d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 105138471 1250 105137221 105137251
    0x60d0320010c1214060906130c110d14030708090c0d050606030c0915090c0c010c0c0c0b04030804090c170a0207020a0b040e04030c1e0c060305090c0603060607050304050411030f070201050103050a0209 88
    0x1d4140308584000c0c41c0d030000701d99100c0801c07205141c24040381459050074103164104c0c0441c00141d41c53317803000031f00240620450001061f0000002c00c5a0800c1c070704080e0034450742000074240f8075601c80084403903521030b2044000d40360483c10007a2446001d01007080071400c00c2c0044400b0030040c40002454996007640c18810300220120074010070400300d8054540410325451400c00140316040c2390404e60340000700f040100001100034049070215450140700007032011140c1001c032182e02c41c0c01510031440040c60180160550b4030b90043c040544202c544012007980c48c0c03ca070105002c2c5104911503001080c0025020a00503502d850740c0901c608095415a00450030b04c0c841c40030010416900106656001d02445401d840340c182c0256188008110450062002078800d110042c03040707011701c030003007060420001c00f00192405407038002c2081c4181602c4014503000c0c0e42040364204c0340414810b001c69400c3e17006100d12030580c3e4100e0084c004d140303a50340078440c50000150000080b29490 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 105139721 1250 105138471 105138499
    0x7060902061902070b07020a120f0501060603020c1902180c04030623061f0f050c0106090b01031b08010605070c090c0206090105071403060d0320010c1214060906 71
    0x3550003842c4600001d41005440800007100034607101c2203804c0001c0140f010410b240150351440d405d071080700c0f2545036100d800e4080c4d03d00704c42c489114100c0200150709040000c540c0c1a0950050004010721f003084404035070505004103080045040d01940000114040e0304907084d90000007680010344202c01840d0943d02d41d11321702150030562160420003000103c14036040f819924058000000700d8002c108901010450521030700f03508040c2d0140110481306051140c010070075544031070b9060b0b0003086040d6480c0290000741204801c214006841d2030701042c01c500c50543c40003c1080c00380d807040040e0b824807005541700c3d88441c1003500c40c00c0f40c050300001d252a4a006050380e850f0f06a015200038106070b281c45d0309407140500241e080c40541d400b00c200685880059950210007180c4400060302c0c00d08048d40c1c40e20101e10700c40880741092400800540d01500043d03016502a0385150b0741050308030b010300c03c440c20041201e01200d1100c02117000c030300e010750700c00b41c200070000c100d15070000389 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 105140971 1250 105139721 105139729
    0x7061404140d23190519090b0a1d270c03010b040b03040203120403080d0501141302030a020409060605040303121109060a021f060f0b0306031507021c050c060702010e0c0607060902 79
    0x503a0f00c0c04d00000d0000036203211074005840102c030300000c2030a000d05a42c0c2803502e400442d004500c8900c04000707013041e80d4011800300d01e00c40030b460380c0d02911b048100e0501000f211040071a9401601c1c400703100c1c20100f05c0750040d1004890480d09600b050300d05050504442604541c405081aa072610a038258000820b80601c000c01c02140301e440380b20303603c402c805e5842c425550142c0c031040201d402d040e0207c000d42c58102c0c5100300b0040c920070044e925940ca02400d8024011034119400081c42d058010860319008002841928085e8407051940c8441003c0c40f000d4079088071180c60b0f40d8000340449030315400c0c031074003414048502e401a113942d0b08001c0307468100d082d454688d00085035181c0a04010500c074006102d07014008824a113851072420601082d55005480420480c0038a201d000414940c400d010b000c8028610303813102c204841070000f0040140c0c1103401800681d001e1400483c4002e4014810310005130320120140000031003c004000c020b404c40c0c8010740b030482c1ca4105243c01661 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 105142221 1250 105140971 105141007
    0x209130c0b030703050106110109020f0d061803020304061701050a031103010207050d1206060c0b1f03080d02030a0b030109020a05010f0504090e011407020615040b0607061404140d23 80
    0x10f00d681c3d0024156142640080440b1810318140d0039a9240042c0171006d030311010306900d8540000e5801000b0b000d860301d05031004020300342e080280b22910200007010141d010005104850302d95882c11f54006c01d820050483c0d005c01e00c16640e015100031400c00000384151025035202e42c00070001418025a5152141840200b9203140c00040d40021006000c40d47c500c9000082e10040c904a070500d4170382d0391640000c550180c039410710401c2401c0c5208104003202250b401446d0312100301620394200308140e40207900296110306544d401c04200c0c0300c142c1814422000c0203900180100d00c83c40c589401500d0150f12a90b5507810808100030201d0001050b00074144840703140000090794083d802815910131602134621000c40d0031600c00e002ca2644007040b910b1a60804403000100103038035900080d10303449424401000e041c10300ca52079a0030072418600c90305c19070040c100c81c1815607001c0212034030307061034072644c2022a0341c078034048120307a007140c001e1440480001541440c000f2a0640004030748 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 105143471 1250 105142221 105142231
    0x50105040c060f03020a05180a0f060f080a02090108040f0602041a040504140606190903060507050d0f060b220e01080624012a060e030d06120209130c0b03 68
    0x200004200304039a40e44000081d0922002d131070118100b054500c4010720501c201100c2004040840e684c02006a540c0781c0030100401502c180040d1041e17503080060700c202e00d00710a1001140b00000003851880641c02128000c5105955a108582d0f4690740c50400c1c0396210002d442c2070380e0a0002161820b8007080c2c905200511100b4141c8542c0742400f080151b490f0155801c204880c80790501c11103494440c1542d1890140d4000f1440b00c00b0310410488088038a6880541442c0c101014003520540007001400300c507903800c0c02802400d0122100350280d960600c100000c05030f0400c031102e00d88001607022400c080c0816104401603588a0504981b00801e821580f03481e0440001c0c07180380d0b0405980003079482401440034401415030000600b014045400303c18080e8541003d0700700c2464a00c5d000071295134440020400c2c4250412100e640e50032520030030742098034040004c54403900b800403240e4a50b07802001200c8035035401e01c44840500ea0300208a03411140b50314003042d540d0310040694403071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 105144721 1250 105143471 105143483
    0x6090f010f030e030d0614030706230c01020d0614100203090f060d09080a0f0206090606010c210905041a06030402190801050702030304020a1e09020919030b01050405070503011d060d05010504 84
    0x50341c07e004d5860b050142501d0828483d07404103e0400885420918040002c5021804440e907400c00c007134050130078402d0940c1d406a5510014a00040c3c40c0303203500c010181c440410b46401ca110004045c0480d10720200340369409a40144032090552034a42078515100002070314160401402c0347d0244281c4250701411104050301040400c0c0b60780c0d0007075080c032a02d0050f10003810142000c1800310b07100d85e80544224104882560400b05018488a01455841203c910350354580913040d40100360490501603c0d01c03a0f81401049541c81c1101c14a00510582c0103120f10326580f03990342044404821546c50700380c8a810440c00244582013031040d80d20a106540146a076072421788108001c400b940c0d00428802c0da41e100001904001c100300341820b90301c42550051b40c0d81c4c461000569180828014100070f02c0e500390b4080100403804103214101c407020341e0b080c0115203a0b04402c3d46c640c0003d00a0903c628500300c010000441100100c0d03400000243c0309499003c66900c48501b5103000300c500341d445c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 105145971 1250 105144721 105144731
    0x609060e06030d0801060806062502040501081b040e120d02070501050f010e0403030518160e070201050c0a030c0924020c04052205070b03010e0108010b06090f010f030e030d 76
    0x803110140348540c0d10000031005403031000054480500301d410103000d00000c0001d044006030454645004540040c407034a54a009070031909064605001401078040340258103040000032882c500060b20103c01c03401c0034002481d400348005200042810301071600380d511030921074800000c042c01c002e11001e4030741d2501682c0c494450034543d094400281c10508040e9600d8010040c1d01e040d15155604694103250214042d200da107035802e074182d41c415103007440c0d020349401d00944040900c035200031900511300400c0503580300e180c207a088510444060030004030401c10343e059a84640e0214075240307800e081c01d9141039203421440d2601051a00840004000050514030303190b01040420700c1340100311802d01c4145414017600703120171180d2030490000c1c603003414904100101480284007601c10441c1c1c1c00e40700c0d0ba640c0c00c0e190650000780314810361540303400d405d00440d007032110807540d0107030015280b945000080c000445444280c2c81042c020583d9030742074060003000502c020580c102c03010380e000c65 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 105147221 1250 105145971 105145979
    0x7030b1003050106050a12150b03030301080f071203080105060a0306080102030a090203100b01390f0219060206010b03072003030a060b070f0201050322200d150b030a0501060906 78
    0x108403600383d001745101d41840e0004210400003444c0c030802c2c640c0c1c8140325941100102900ea00580b031405031440d45808044000b050082c00005c080006c05c2c6090100c80c6141d69036442643c10642c8401d0240c00280d01000500a504002009040c08030481c41c0c0000ca1507a504d85c100e08981090f640c3c41e208070340369420841545800c00c40c2c8503130b0f80d54140c030400100c1c1a640002e801c1c040800c1205c3c601c1901c809507117540c280d001030b1020342e01c40c0c10403051251000c60300d8200c0a401c00c640c4124030070001d00f0070790f08020285401200c15030300303182c0043c00280d0810141e8a5150802004d401c208084c4172104a26050392142140b04070003180010768036424820380d240f080e41d5a070b4004295418040c03165201142d4060540d01c0c9481e0203003820780e41ca80b00c111440341101c0c9900d048550390300c40c0030002c0b402c024a00f40341240740000400c02a11400713010b01008074480368000c02402d06d400080609540a02d51380c03120001040c014202d982e0170305d680c0e8a103420b50780c0d00d034480a0280c0d41c40a0400c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 105148471 1250 105147221 105147223
    0xf01111c020a20030c040e0f120912190602070c03050a05010f0b06070515040c030c0e0a0b010e010c060e030409062304180305090d0804090209010e030105090a0803040507030b100305 80
    0x3d5422000106607881681c450f0300803e549090862405108649070307086403400c20030030701071001002c00a8080e47c05059000c2c0c0310400940c81410164010070001d5080030800602295400035040302c9600310000001584401000c0e4200002c21b0700c88207050500040020000c1040e482c48512031000802ca6900c01c2c83c046040798401c0c81c8990245204200c60302c00200045000d04806125144940c090b48890500082c0c1282c90f400c02000090b0703041002c04c114400e000d1107071003a0680e80c002d108158a030320045644c405002da04501003a07421004400180340d135048860b04000e00c5003100d0a00790350b541c0e040241d50003039020824085a0307200c001890392020840c210424410f503000c0c00900c1c8502c4020007100c070149000340410001090204055a90019044585401c002c0240c0c44c1c50711400001700a500c0000c2c0c1c280443d0021501000f00d0906020b21752082c0c4032100030380302840349921001201c2e40010021101c074090040c020000a14601c0014003510740c81c401120b40605600e011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 105149721 1250 105148471 105148493
    0x1513020c0105041b06020d050714030301060917010207020604090509150c040302010206010f27060b040b09030c09090712060207050303100e0f090705100e0a060323060f01111c020a 79
    0x50b04d444c8509141404460340004000d0240039152600303690f94070241c144100e41598481c0d00e4425404008000500c269004c403a602c26540020300748510300380d40d100303058201e104000009412030414841048042c1d25a44000d52201d00c0e1000e031155108203507026218918215080b6804190101e018000e6503410002c0a002d4840f40ca080d9050301d0820940c000c5000c501501164803a202030403001c0038030581d401c040300600c0d01e210302e05d0715180c60301185005500200744a0303019102c1c00c5c85009142ca80801c00a0054903d840500101c0303090100c100ca89869001c4203850301a001c201050004804000452040d038510301c2c81e1070307a2030a003004113961203000741111030382052020600c4005030b40840e038402290022907000300d518405940558954080100d00d513400080003000143c840d401d40c02c005025803480c000d43d401030403030442d049105c0c0e02c02d40350719820901740c0b89104070950180244d48414030884040340c0d40202404180c1d40101c0000b00554010380000b070b20042040a04050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 105150971 1250 105149721 105149753
    0xb091801141f091e090c0e09210306010e1c020604031406070c08190c060c08060f0d08041a1204030c021306030b06093d06171513020c010504 62
    0x28800c0c2c8060545021103000a09107900c504d0303507103c8082e000c120b8946440d10040840c45182e0312245800103806450b000400ca01c41c08948000c01044288152034045038402d242c1610780762085403041007032101591182c0c846a80103031040c0c0103107015070f0315400500011445401d100151415403d0401e080c0000901048184415071190304002000360342600d13521889525a400e404450300700031980c000c000000940901d00e420f40100003160b1210000d40b0460042e10f441103622407030414000c15444000020344580d505010500004541c101c0c0380701c0d803450fa503028a0800031502001c11207007000b03403000c5001c20030041c514811410308805068013a0313802001007103500d281d07031038215442800a010034800c2c03184000166100c056040d0444218400d0b03400c0d10394091800c0011440c12a510745410411402e109001400e1440342d8041000c1351002c5140c2106512051104103001484001c0e00350700000741400d20110035090310141500c210100e00201e824103180c2060b01241c540f10320 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 105152221 1250 105150971 105150989
    0x30f12020c0a0e0402030106090c0e092505030a02070c080a0302070e0408030f06030a08040602010e070909030215090309030105070801060e040506090c07020f0a0609180b091801141f 80
    0xc218040d546400b400d02c00c40e0494840040075139140c0c40000c2c014036042d0041c1c401c0d1407030001031180c01036000c0c1d107082900c00f081e41c490103162640b810031011200b0009005002084030403107025901d11401c05103820030b0714584054241245640c0b40c9070701c06401d4200d980994090b00e0301c00c0606504100240003410208200c0c005414103446500c2e25103c02848201c1d04004040803942a4800b04074245415401020142c4c48a4648074001c1c003805041c1c020000520a4003130108024005102c1d080c0d59603415002400c11030052051182e40600080c031286084c0414464001252028020584511200d03620b050f039640c1082005040c80004111160080d4030b00001c1050b9512112030064101601d07090864559506100285048440000e03040e00a9940342c1c0010341039401c1800c0e1001d850005c540d148140f144c01049a08072580b080f15103503c240c1100100300c41100c84550303949100e4400c8000304461072100c4045902c0324040c1c800809940c0b5225804400d042d64850034005017108103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 105153471 1250 105152221 105152233
    0xa02150f060d08091909020d06080c03030a1110020a03020307080106032d06120b0405010c020303090703081e031812090a170109050a0318120201051918030f1202 71
    0x2c01c00319425580014203240000405080c0c6582c0c440080f00d00035030602e4201809a00d42800202a410820390384842600702100490460f0011825003080303503010b070045080c82c8102104075200f601c40c0b11403100c82d00466204040c0d105050000300f0751554136850159603414811002040883d05903c100109841c0520003424003d103225018130388a2203491019100c01101000e4008150a40c0010282d92584a4140c101f01500703a42d82d115a004074000c100603810705009a880f44403c6400d1300d1a5002300070103000003240382025100280402d001c6055103500420014411381c030980c0c0810a0500c40140000810b10401241080504103180360b03007000c0680300452400b0080340250001d48006041140389040c00b540b00030b0110342c000007103940d03e10180c24064281ca851899003000b094442001043c1c0743c4c13162058020540c1d040e52010318000c401c40aa1947d80104668a81004122820820000705034030f04880514001d0800030088000d034548880e8290007141c1d80b1040d90012 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 105154721 1250 105153471 105153481
    0x90f04031d18090115030605160e031c0e0405040f11061e07020d0c03080a1b0201080f040f0203060c0903251a0705060a050a0b01020109020f040f0e030a02150f 70
    0x5808041c0c400b01d008412005512081509405031004110305a022913110000009000032900824000d0f0980d0000390303075030405290100d80c0080c0c2c41c0c3c0c00c0358060348060b50050964282c0b41d050450649a4a0700c0c1c004030003210300050070384130195400d948121512840f0010700c00005581c100c2c404040750300340d141c0581c2d07000703020600700c0d000c078040046003021a00030250f40b626001401082c4c0d108031000d480545a1070800015000061003c0004e009584100e0300c0e800c085a00c1c000d00d030740586910503140d030356101d001c40203d00140200d4210b054561a4401618200301580c002c19102403446d40703401880e41030518041d000c0c0c0301c080c2103e01c0c1c1006840f1a140034079900302510400c150704800d0141d400941d408511400100404d584580f50411100c41203c0c0d00481c011140f80c801800b40700da0350801203080e10401c07003020394001e0208480c19090720303103a44030107400e020240b00801c0e4400b82e9021141160041c00110700940c001d100c15200301c2c1c0409110310f0740240d0159502d00d01c1e00340 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 105155971 1250 105154721 105154729
    0x4060e0c010c050c0d05070e0f010806090a050a0206090112151d0103020a0b070201141303020103140708070305061203041401020c0d0807030f050c19060f0b06030406021602090f04031d 81
    0x402c081d13450080903442e098205000d401d120310805407026111221072801c1105030405401801d00c19050325029810200c0e040d89004110b0108590700000206280c0c6e03441d8082092650100c81100e050150303031880034210304014002c4000c0c60b4011511031561511b051101407001c036030041148420482000140010382d201d8a20700e00b40e4503800491900c2d0151440180c92003210002c04148607407000c038107201a082c1648000059034403c1e03a0500c080a00c1c0c44a00706a030b501a1003a03800b04040d41e000070740491096011541c48600100541d82001c000480f0b02c1c2940c0c890341040088e401030240700d45103942c04100c4820085001e980c22024512176442e00001070040701d04c001c04000c0910441410395114205642030b21854005a0302540144400c030031060601e031320f0845219003013513520403c21100d803050071405407000e44450328550759030792030700000e500101a9105603c0c41c045000056100c0c4e00d40c952040300e2540440005040c9810050042042002d0280910000395101080390300d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 105157221 1250 105155971 105155983
    0x61b1d03190501090212060106090f0305030a141c050a0b06090604030303020f0409051306050703020307090515040902070807051b060f13080d051e030106020a12090e04060e0c010c05 80
    0x40614101d503003180740d52070414050f05604201035481440307542c007104003582c00f0489504031885500c2c0e540c030495840c0700c05602840c0520018105801c00d02c240c1c03203418021003880801c0c4040480051400c440324600d05010380696181320304d401d42c0c0c1c1c010045940203c0c411758070410411a0304e0707810103641c5400901c091003180130041c04c143e00403c15412149400c2c09035000303004143c00c01d01031890415150111051800b4050301d90900b010045540633029100b180e0040a540d5a001d6005092100f4040520104500c403041180e081000140c54005072014143c02480340001c56581c0d4a2802c0440c038289110316001d0021612135032481480d62403c044640e202020807000d6110b0703921b004d208105200d103901c400424000d16000d4010940d01000411041c008001805130844003030785030034000e00090181f4000350b4817000c51350340480c282c0400e00c400505640740c030000854507040c80d0b8585040581e02200c240743c950fa403d0703140400a0194018090302840d10303403820b1009440d1141c1e290 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 105158471 1250 105157221 105157243
    0xe010b06270d030302030919020901060509060403081b0d030614040f021306020c040f06120609080c160f0e13080a03180809030111040b040b09060403061b1d03 70
    0x403054074610240340c88030100c108040081c82001c011040307041c0540a07600c101d840c10400d0040c61183d042482510642c0040540c025210004503804d09009980e194450a451540903105100000004440e5001407041881a04404419141c260742c0355180070000c280000525052000902401c1030300700503016000da00700c2d40894089400e4080e10020b20600c4040d0f034641c3c810110209110f600003940d515105000e0b9000c00403100c0050200c0c044a9107401118010303034642002901140b52604007000312402240d12924201c42800c41e50724044400c41501c0e0242c00b20841049950600381500c401400c696458040916240030b80d0308164500703050042c41c07031b140828880c20309403080c0d11039440605900c1c0c20307071050001030400300000e4000440d011300c04c0d800c29030410304e0b5602c644e09580840e1004000b141c1080c0c280701c0080c0301500511061600150140b00c0007020880d61301644000192080d052500800d098200901d051942280c0c281c42a5004152140c603840020341c4100f00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 105159721 1250 105158471 105158497
    0x60203180402040b0a0206060a0803070b0604050604020909071107170a03140c011805070506041a0a02160e04060509190807080409060e1602150f0601020c04110a030e010b06 76
    0x25480c00c0024001d009541021512020105525115a03000180d81f809004121811848580d6a511030b907aa0320442c10014404e8000c0c1c0c0200d502403d05d85c001603004180103101504241504012450624048512100241030b01003120307504081807280e40040c1040f86030801800d51208442540e5030719140000781084812491501c80341e60238000e545903000032000070301030080304404100c0d6542d96120160340e64003074420005110b24200c4100c030101d50304140c22241c00d054142c12081e1642086102000754021600111154258005890090407905440d90501d040500300407084035802450400180e10200d50b405400c00102c9031001c4103944005403a559484501e058142c0c6d00455000e0f41d02c0d2420144041284a2800001c1c0d104240a2000071203c9140c05022652038092050b2003480034121400714101c41964a44a54800010700440d409040200003240c1110049001d8061a480c0802d007078413040d0f03060056a80c5c0b0308907100207210880c07204000511034410b0281030221 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 105160971 1250 105159721 105159757
    0x15120319020109030c0b04032c040b090103030917030702030a0f0506090705030c130609020c071706040c21020312040f06090503060f06012003040315050906060f0d06020c1b0604060203 81
    0x300b5114130702c581980070140022000c0c034070035056103101c0b0401271041540b241b81004101002030818003007680c1201d8041e42c030400c0c42441c04131582c501d254114032070003590104118100150b2000c00413000800d00c906103d007900703c1d040c1001810040c02034501e40d507540000d03100b0440c5075000680034405030070031a0003182104444030748100074000c035404446c450f130003c01c203484090004141b01d400c81e09400380c0d1640100e035040100c0d032160001c5500501410741000c00f88040070010803d000e0071201c1c0145170281c143c2a40009140850b15402c503208500c00080c18890110840c000750f00a0485003031142000c0d04140009454075002070031881c40b000d19000003000c9078880c1c0c240410098040442c0403441003581201d0780c50703501902040d600b10540c50300052848030b55118103031041901c4030240c54192150010803904030f05400e2100c0d4401035044c520004110b0030300c02007401c80b080300020a9002d441d524108031074005000e03014443c6400340810064145c0200c11580319603041d00301079031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 105162221 1250 105160971 105160973
    0x70809060f0c03100e042118090902150313050106050303040506090f0319060504030e010f0e0d06020f040816050103020c0d08071e020309031c051215120319020109030c0b04 76
    0x130100701c603540a0346000011005100502044021078480c3d4070300ea003140b480000710366009079854a0001c040080082c2c089008028400c03542c0d100311030701c9100804070740a40c00c500b04215004d070404d8485240070b081d014101400c000003441101c0050000740c0145040034984000500c00c0d020344007240d80280c0000c408c1040943d8144003590504103601540400c0b96182e090020040404231070450101394605901c0105601815011001309134556900341101d031010280050906ea1040444409400380000f03c507802e5000003400190040c0f00081c0385102c2e04050503015041c1640c4414185441008050138081000c10005441e250500b881d4116407a100c00841e040411008001100c88100c1002401164080010810315070203d040740c516912a51155614000d44800d40c3d012030401c0251505411140540316482610194039159507820b5201140d44440c1420700d2084a820002d4070140e1a02c0d07141e5070030310350340b041c0c4005c000b0000781d682c02a0048108142c041d10107100030000030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 105163471 1250 105162221 105162241
    0xc04020d09210305092d0f060a0b01080a021e0c0c06030709080c09090d140c03040602010501061d0a030308090307020d1209120804050103020304080c07060206070809060f0c03 77
    0x881c0c80d54451541c1d85100c406062003509002d00c0c0b04641c0000b81010042010050300081c4d600e4105c9a814901c3c1c5114019412002c08809102c2003500a0148220144038440140003c3c2c0c85400d040c80085004103050340010712858004146058440c410b10140740c07050200b8107010080a400b002190707032250f00d600c0e21407a010b105404242d10080c00000c11502ca5800140f8404490310042282c5071130048600300001e10004907840d2106500000400d6005442181c45802d500200d40404d4a0021450078050071030344035402290140c0e441700c004000c0203520410200c40d030350a10048854080c260030000e040030b40301384805810882414049a1040c605000301c40c11564000c0001c40e41160301d2a28038104c0000407044e0011401c400c03000644440c841407510380091b4411070b5285040d082c40d0064000307410152007a41d42c1c86084c40040c03021a01040340d02c02803d4107030028112031a00903001040c0882c01040c00c88560400024400304c9014a0b01c0c564204101400c03168590b9100c0381c444d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 105164721 1250 105163471 105163481
    0x91505010f090f090902120c1e0d08040314070803030c121905090609070518040204050403020f1501050906040c0c11060d020f040305330402010207031203020306040b0906030c04020d 80
    0x407007240029401c00151882003030340000122403003502c00b003100c2c0d41044440d42d2154018000c003500040305c42d01440703801802e203a0840118500800c08110ac000d83c0d21162200e8015070421200c540614400c40c510040822803080207004c0c3c800254038500e403407484108035000303a02d407441e101c400c10004a003046554001622812040c0c000404c468a030040c0768a6507038005403540307c0039010341c0e10041654100229030540e01042d0120314511600c0356800d100c001d01000704140c0440c090380080101a0505019480b01c0802e462070580d0194180810003c0c40c40d0090a0603100354a0240c00d074101642201410702c500790042000b41005108a012807040d00c1001290403c4a20008400701c407841a14050000e0f42c4c0034100f10740e02c002040c03e4035020380100c4d02280c41c0302c5043c1411b1541c05100b42e105c0d907500c03034410701c151000540d9a0761114885c1e1400180c10300170a80200401071141418440c0c515010b00489a003511424090080303504c448882200500a5800060b000303e42051034103c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 105165971 1250 105164721 105164729
    0x931020d020d020d090c0f14091305190b0f040b040803150a06030e011104030b0115021f1d010c120c0302040b0c0c09010e04170c0f0105090c030106091505010f09 71
    0x8150760300c40208000138020080b0300c40803201461104008034100150f07402c0f83d42620440322100d9501018001004003405e8024038018030340c0b581c3c0d14070900180041c003030080702600ca14100d03202010107141c061508007000300360034030b4165a1010080803811001d0400d070010b030000401c0350340f6100d6081031251040306070301054000d5075140f000583e069241e4000315204186600802c5903240080307012240303105501c80a8880714000d40188210046490784000c4002030340101d6200c01e26020700602c13402c60700c00908100300d59981d49080c000f81900000c0161100880082109800440014105200128000c10540d90f66803002c5506c1d4000e904440242049400e42c0e5251011001e203940d85400c0d0340502800f035807114000140b00e0070304004403030003941d101191500442e107541d006005a003041ea1b034140305104690090403510750a10906010320008005412144800800e2509507190795008a800c18900000529481701d8040e01105031642440c100e4280342e80914100c601c0c05aa0300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 105167221 1250 105165971 105165997
    0xa0f080403020c0d050706030b0301050103020a051215040c060305070e0901030b0c04030503030a0c020729070201090506031e0c090114090301020c06070c030e0a12060902060f0c030931020d02 84
    0x103804d00900800041a070b040b00c00d207643c28842015840c0038903003070322400e00c40250081c10350b520900c01450700c0348181e18804299030803102040718460740240501c0043c1d40959078502c415000307110141c0d06000fa60381c00100e904041c841c002c86134000c5011498140f001600340000440407038906e401c060103ca0055400904407030300c81c105140481d0042841044410151082c0301c000075086c00d0003602000c8aa0b01c01d0000c108481d120a1820640d5201d2102241001080e0002092a0b42c650b00618000c1403085100c0c042d00030307004040d01003600060034841c1c4030311060082c0c41c405ea902c0750120096101c1038141680700c0f0140300100740a0300408485d00c201b802030704100000d13030340d01420249489000c0c1c0d885103c0c4000650511942c00003d008051b040c0707040680102c003044031038010404541c030140c4218039000b00304a2044440c0c10488003600303550000942d8070181c5c94212941441161a0219070108072141104558404051600082801d4000c6100a80852158103844054032030310 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 105168471 1250 105167221 105167239
    0x31b0b0313030e06130918120f030b06040909110a08100902040e1c020c01050708030105040c0c0c0f0608010801050c031305211207031401120606080d090305120a0f080403020c 77
    0x2030b2400c171020b840c070f0003280509854494103204035009a000050301c55049000001c038040341e032800710303145aa05212031080c10b489081c1c40d0800e0311090000c100400c000e81000404882500d0150600942040480e01c58030722641d05000250020800c2c603110b02801000040c0201c291001c20041c040c81c2140c42b56500500e0b00c0c003d4003e1804410b44020091a0300b40e52a401d01e440c010340d058005c5c190060400e400500051002e4140f0303501a070381d1010700b810031040700240355a03200020f40c0e5075000b51007814144a000c10155400040407409810f1100090201d40350410f50030001d40002001072428a81e500305040a2100038001c940014155029554090b035010304041007650200c3c140b0502502c0300300000b030029104c0c0c45038042ca104400701c40d40b050303440c001d04200c6170352180c0c00681d9034031703520440001c0c6188100b1900d8111580780d200c030860070340785d814a40e0805140d000c00c185543c4040000c4c0300c0499001c081e551041140c4d080040c41501ca508003249020107400d65640c0118141c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 105169721 1250 105168471 105168487
    0x21305040605040308011508072a050708101103070c020a030507090c0806040b0d02010e0a090f09021f0203030105061612021e0703020105040b0a051909031b0b0313030e06 75
    0x7500014860f50182d00c1c2d2000590303807041c07000384e1607040b9449480069800000b0800f1284034006048940302c94080c80349040c1840842811a8440d1000488499000e50810045803606100c6032148005116081003001d251070b0900e801c0303102c001c002e07008010001d9546011035070340300c854401950300103044403191034a50070050028403a10018030041400e4a0002c0c0d450310b480d001c5c841501002405003000ca001c5a40150340c115840d88030668050384180002c1124140c602c1015034000e412070010404903080d0040c00403007100c100c90b000f03d5400d400c22440384180c00000700c0341160f000f45c0705941d40d880d40d10141d51440600b000f000789541800540a041d4035800160700407241c4020885400403074543d5440c3e0390715560fa1000130b0200e07006010420510480e040501048501030610381d141500003803000000107500c032030701d00c041a0700c10414014400c0b01604006080210340c01441181e05051005480d8000105441001c1e42440ca00404040c0b241041070300c5444042e110740d44408003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 105170971 1250 105169721 105169733
    0xa022206080106020c0f100e04020c03070c0302090124180b0301080307061506021207050106030f050618010c09050f040e03040b04051201060302010c020607050c03120a020d210902130504 82
    0x3e00c1510b0061050f500744114616020030480c141071b000078844607207440c030400103a4006402030300710355204e982071212a009940500003403640500c40c045c0700303c1d188c3c11441009075a01c0c0680180031001d4903d60082200c03500c91074842402e440c0b504000b03886902002820700d490640c1d8001d0040c008021000182810000001c1c1000b98440d000500840e44502c0d08688104928403c04006901182c6807000489040c030040044500541c004150b06031243c81c0c0b503100003c3d0090444159101700c04102c52061000426000c0000c51002400f14061403e0010070010907400394511405020003d040c050352503612082101c5260030a03240c40b242d42e008551a16085072103018050031a014100700001010f00c00c0009a0b5816110803202c68010380a200d21504101000c135903d1140701041c040390b42d410006445502e101151041c0c0d2022078040c020304140810b8003102c24090300c40042d10ba0302c888042d240d07004241c40040015132201c18000181800305c4081c9419143d46090140024408 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 105172221 1250 105170971 105170987
    0x907060804050703081206270c070f12111b030d080604090b0702030c07080a08030a1805011109010306080a020907030c0203090a0b0c060705030112080a110f0726060a022206 76
    0x42280d01801968011111200001c5101c42d60714481d2381c07100000d0b036140c0c1000040c0180070b02440010115590b143d468804d1000a84043d00c0403c0244140340d890360010000701c401b10801d110030004440001004ca42d8510000025809000b100e4000901c1030301c4aa1203d02e009800101320301003800d1590019460781c1c4441c3e540e802501517030f5400b0a03661000140c0b0fa0030241e216400a1541d07441c080d030b0b100208104e44440d904408488841800301c5c00c00d004131450303c1c0303c20340200e0340c41c401301d40094201c070b00a60000c80fa54010000180240c1d8900344115840903c0e420086590100020101e0651089089107a8080089800801c560ba0903401409107203000320100c0b501500c600c0001c2d201c0d40003d12030202404c0a032201d100000d940b440151110314002e0034207144020302c00c01e82c2420701a0368030440d591076000d08010400d041c0317889400c0b1020604401608405851000980c3d00c6401c010b04000b0480e03000a140d00c10a507440c203040214030340340710800340200d03156007006000313603 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 105173471 1250 105172221 105172231
    0x30a27060c030b060d0b2d09091e0304050406050d02010806010e1f1e0801080a0f0804180504020f040b060a08060a0b070507090c1409100c06060b2109070608040507030812 75
    0x110580e10541f840d001d8524000a0703245010319200c00140c0140c003044140d990081440146025101c4429948480c01d210a061800c182024646a500f01424041164110b9000d14466080c42d1407010250b40c0219031150051003c0c6003c0042c4014000403d804000c100141d004001990324802442070348219000c2c50358070202f44d03101ea40340058000b00e0f81c80d1001c1c091604c0c40e40041e9840e0340012041ca18040b18548a09681810141e98003111500018a440141c8441e9100c3d41000210720b840550054200e030704850400000c2007010100380301e8000c0580d030701e081c8006407003c105650b403420800700c0200b03849070105940d180203184c62921116070788141489281002000e500c0c00340560108490304003a02160340c10820804104504040c10f40c03604014401c02900744070105460380036100141c501054400d41d0f402c1040b40b03500a060301c03001c20300c00044051080c0002404e0100300e10f011079003d0300d86080729841c0d0381025418610207a0005005000004540c135400d0403440c5040c0c822 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 105174721 1250 105173471 105173479
    0x2180a06030b280209220e01050c03010311010306080c0f0d050109050a03080109060b030a0f0b130213050102160902090a150c060e0307051f02070c0308030a27060c030b060d0b 77
    0x1500404140c0f0341a07000318075420341d000030b151944903d51103e010044140150b8100041400c107070600c20942110420b40d03140b24450f00000052041c0106022500000d800a10342001201d152103c0c990710b4200301c034100c034481d801ea86c00c291055528102d910402c1c51700b01c8003c02420030170340740c0140d41c2c0f10104400c60204501e90300000d034024481c8100803c03100729403242441c580d10110a40014001903030581015a901d5508a040f03889200199286d503580d007400580d9560a455801c910180e6039000904550140c91050486100001c2d103c0403038513500d101607103442c8000f0024110b50b095410060490500f0090000b005611501910123180640b07002c0184101c4c0d260f0782d86e182e101e001c0e40904903621030591100c0b5a12010110310300541c07138280040c10309040e5a1070388650600c42d071040c3c1c0c48030004018001c2c0c0320094803a840502940003504070200202141d190f82c2400c0c004030103064a130b600c0400b0090940260010001180b00a02481d1354004211821006040c106655400b07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 105175971 1250 105174721 105174781
    0x51b10090b061509010c0317090c0a09020c031e0903030a090f0e090a1101020c060a030203090c03070807120215120a0b03010209060409090c0503010c0908010507050702180a06030b 79
    0x30f040074558400300c1850380300c10614010100d40155a504103101e0200c081044115100c600003659002e040d0280340c0c407401526240b141e410400041c0915900280c6140388104108098414008100c4000007001d9500c0c54091141a0000390366000e17030481d00d9050301000628480040d400f003510015200f404850401c1c0c542c59100c020b001c02c1d030032143c00005a104119880102e0101c245103611040140304541c0001c2d041d802040303080d00301d440d044002c65008020700c03035103a00500036141012070a500130065645030080140d40e640723041c0f04a03039003c50107601d10006d546550000c040d1030b9010038040d5070b494480700158050070004580c8400c2461034800550600d140600854088910080840e42400d00345040f007002041c2e184400c892022241c000000e842d1000c0c06130b0424480681c50b140012440c0c02c00460940b20018032038070410004004103001070395204c111825201c071442c10310045541e840d03000c100414140d0405050200c400d002c101002564018031155a00c100c082140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 105177221 1250 105175971 105175981
    0x7030b0115090602120702040b0301200a0818060c0307020340030c0b1b100b1c0804090c02100905061b04180902031e010902010e060c0c01051b10090b 66
    0x40c9601043c0c001915a4001b00034510151234260450485074a0082c000144001c58002800d41600107048101200c0000b180940398290461000d65018407038298891030750b400491000d0701d4060003030038009a0003000c4040b40d0460b108009541d1a00e041b0f991240640b60002071080404241e640425aa100e16030740150900501c0700b0004200ea0703204036000c2402d8100084203203190840c0d03140c1d544e40f00304c01c400e50001c840100a08580c004440340e0010307070510700341c1c2445005c0d40308440c0c80c0d1081030300f00c2d00940040c25501c00c0b141100c08590b000a400c0350501c00480c14168140083d440c841d0405200c042485070108003180203c4604c005801860140420280c13680258415442103420403682064200d00d10b400103100d49100400365044200381400b090040240c004c02000243c0d912000401156040164000b01d8034088515070f0500a2440b60b1640e0780c052444024100503010541c0140c0070480c07035841009445220503203600c0088161900d000f0607141c1825180201820b002c24 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 105178471 1250 105177221 105177223
    0xe15040501090e0d050a0309020d0f0c050105040b18010e10031d0c031b0a120c0603201605031303060b040506010318060504030e0a090c2c011107030b0115090602 71
    0x21036900024014000c15213155900751150703080600d262041c580c40701aa1700059443d0103c40702d0b014407a50712036005040c0d50030200130380e000c0350304514140201000300b0300048141d401076070601040054424041d02d41d0100486509040941c07850708080e001ca03050350700c0d07909500400e040518020b4603007012000e071000342da655500d2070b1206806800ca8032100940403000006200d40200c040d06604400795140389550040940c004240c52205000605000095041c02031200d10080c101c030421882c0c02400341600740d0b01c41d026850903608000c520302000c001e820300507100c1180d10040311000343c070354030b0030800081c1c4040000188078a1900700014075541c003d20403040b1220005100ca0f82020243d43c8550003454043c2c03007601408106244120a42d65070081c6401070f05c0d410b20081150200204c000c0c09040b550306601d810307518200c0310130041c4a03c0c036081400c9404240313070510320702c0043c86916041c54015000035203521041000810101001e050030030030303c00140d07142c504e5070b5a01c030300407 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 105179721 1250 105178471 105178481
    0x21003060f09050c0f0c03040e1003110d02010207030501020d06080106120305071407051e1305040b060f12010603050f061f0b0306130c03060501090e0912070c0e1504050109 76
    0x2001c1d0000d1800341801589203c0d400b040c1c1c02404800c0d400d250102c81000c038080c0381c000071004130341d6a00016050154841d90018541c21004c83e02d45c06d480c1500719640c01484480e08030b4050702400b00c401e0b8240640e8403c006980080da0040021552812020860000317001e03a4081d40d042582070090014401c842c0280c510300ca03e8042c0c0c2c50b00d003405541e594408009100300808599031103076210100d6255030361a0b40e514090700b1050680b00c802038034000d200380041014920980d491400f410400440c43c101e0300103070701100c01c484110410040f0750000380340225020307603030074150f10b890008000c0000001c2d16140601540c0c0031140640e40d0004515004040948441000000c100c004c103d22902500a0b541010000340310403410301c0b80401e50700c11502c01110140001351168070801423540c10050131400340403a088400c0c040d20b00612140e036107204808520745225400218041884400b82d0303800007410041076a0a054100094000b2000e19074101180c402c0b80f400000181d00c580c68410307 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 105180971 1250 105179721 105179729
    0x30e1005120f06190608010e0c030910020307031508010b0103180f030f051b010f0e070b03061507050304060c0201030b01050a020628151409010602030409050c0f030103080702100306 80
    0x4504660700c1c1000c080012802400c010f4024420000406a051303041040c00c0c05001c80c1e94600050790324040036802000d10181c06590994010802d00c00101e00c0030a242c030b0b07591080c0101503544d840fa040114014403049007801c0701031100c0c100c0843c00c3d01042d0480444000700344e074248514020486803524900b43d601c40148081004210800000d0261409011442c40c81c2047c1d810020818070040c4440000000d50b0b540e030b551541916407010503486005503903540d0f10300801d51242040003110380c6110280031280308540504003024520a050111120203501100750f0361626510b1401403e071900000c01240440c0c28610000a40d502c01c20598080d41e1251340100043c2e2205445c05808650310321750000c0c1d07100c400c820070407610042d006510680e03d0070728903a43d01910b420000480c0308403084940f8800c08808004028043e0300200780c50940700710420004151312a0311020360144500000483c10110100000043c0710015014101d814000d440d40e0865a5901504600726840340c01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 105182221 1250 105180971 105180997
    0x9100801061b08070b090a0201110c0d06020f04170a120c020607022205070c2105030f070302090d03051803120d1503060510080709050c0703050a0516030e1005 70
    0xd409080b8091a0080420540900f10051401074a0384610009900464040c80103034480c04000f8115684075092806480300c1d2400380c044940c80c00b00083c641564903e020308601d4021070314984001d00001120002c00485540e84034041d01c54080c1a10b87c0714500064510340101440c2800d000d020700000c1034216030007004103140c42a82c1d420065511007501c1c0d2005800050340141c2c0108029104240c0920219212201c03081690b150186150f091070a103800c03400035014840400c1500301c0d0a0325081060026555500e50360700c1800c400034012454541c5d8000443d00c070000c1890303040401010010410301f00840b20340380c10300505540d505a054084402c10f010804030240380110ba02c03804c00300c0c0c4544070600107283c3d80c1d00c4880039284140d81c00c0c00c642240703420800000b60100600030041036000d0317061216182004c00d1594500802c000542844400941050802c1c42201120910003542030804284032036410010000501d004229008808220280481d40e00030020750701d215540d24 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 105183471 1250 105182221 105182237
    0x90a030201050c190b06120a080417120301060503060f03010e07030602090402160b0f0f1501080a0f02030a05062106010b09040603080409050a060f0608060d030e0a08030910080106 79
    0x1900449081e403000f004416a40900c0c00c00000030b00701016070503c40f44c000c82e0b16481034101103081080d070f0324190040300b02c0c41d800017140b40001459803098400325219124030120f4030103968170311030810354640c0c0765001e4041e000001150b043d800202560103184103580d41c0d010b69007101c0c103060032102d84920000181d803184804000040160b0000e2000c604041d1015040288804500600e950350320001ca5031440030108000e020641c62034150b0b801f1004254404030b500306840755440d044900d81010b030412601c500080e2901c4210380154100500c491001c5540e49090720185004100503a845441001d24000d10003681084400002c041120346010f406c2c1a46818850302065004030742094100352183e5001000c05e4100010b40b0050154850104140c50021108800c03241c1d540c015900e4003105000038003405501190680c0e00800a56940c04142c0c15410700341c1c1e12060320400c103988540e01d0440400c001c14007002400070041c0607078064158144138031064518030001d00440740040e44c02 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 105184721 1250 105183471 105183473
    0x30607020a0c14011d03030c030c0c03010c05070c0902031312080f06090c0406030213090c0504031a16030f0f0e0708120301050105070f0312020a05070b06030d0e0d050715080f0c090a03 81
    0x140300306405c1e000c001001c4a20740504501c26034215003183c54035200701d8002041e080d2460030213000e2140519440d290041c5003002554580100342130350301800e0307019617020000900042d203030104105001d4103c04685043c00304a00d004007020421070341d6030841011031000c41e40d14204051030600884d000c81100342403034142103044000350480c1008204807841d160340014041c1007449402000c5a480c0c0d51355540d80d041d4104040c0002118134904d5081160030100949042e80500d18490100c0034a004960b0745004200e01c1301078a1314210622040346054030030810000002120400c8078400000d0324201c04002d000c03010140001d12400d400b107102041501300082404000c5401c4030301c6401d200c419442c106020a040780c00003841c00003ca03a00180041c144210f00910a0b0300400807402010f000c1409000202640030031b0300e9140c015101d00f50b8140410009000c5e00c0054581462807200125144900802c440c400756140c400115580000c941003401040448541142c040c01002e81c151071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 105185971 1250 105184721 105184757
    0x30801120206040e0709170309030601090f021207020d120e0c010f090b0408010203040614160e0402092701060c030f120b090703060603050901091703060102070302030607020a0c1401 80
    0x3000344100c0e40080d04120114a12000400150040446641e1141d20394207101c20041c2908542607080c140390f000303214010302c030385d00008e40700d05551521700c2c04035080618010700303406402103440d8a4840441c1c8000c20032100d41c00141110002e010703558012038000403421041c04c0b01c1003510900d0240e00308513074540c40c0354095400c4124140e4545000d07803165950740004c2d18650011381082d15140d4001051005100950060510386580650892030320300745200d0100c94002d405c42014140306c45001440c219aa9581c16251403000103404000108554a403044592840c0c0c0180359010f104440003207103c1b84514000c0381d141d90305455200c0079252440c800c0c3c0c0c20516420b6800411601c84d510708905803941404940070360059100400c94904062001d410f540d40146070041c50ba1410110350045a82690207820a045080602d5a43d4440200403820f2282681000e9058070902c2c0500000581c0001c02c580703041d000d00b200c18986070b141c81140d0303056407042da0079074002260b80c10310351b00c01c00d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 105187221 1250 105185971 105185999
    0xb07020303071a041b0b031503160305060103020a0b0702060403081c06080309090702060c04060c08070803010e0910140601120e0609010f0f020306060f25060207050f0604030801 78
    0x400181200e0804003190380d840500c0001e141021a80880d09081c403013001403206a0120455642170b40c030100c0d81c142414000c40740401084520710b81000c081d2500d085d00d00303020b11380e41c1c00e00c80c45018060039100d080c6640d41b03000030311080b4040c10803241d00051220000c0d05548015034000c080500d0145151107a4040c2c1d08500c15400341b0000c40256501140c4039403007070800410510f40559281c00400d0704200c1142e17002000c40d0290b41044040004090b48503003154103840c0780c0d0806000304c1d0300f203082661090003410802010031b40d00000100310040d41c007240600c140c0020742161141c8510150200a44021814028014598001007103007580a07040010710301450038400a070300103881000c01e180507001d80341c0c1405655210641c460410081c011001134210031602076285082000201d60540304070801424a0070b008200d0203642c2152142c03001e5001e5000c00d000d101160300d07081600c000d6110f40300481c1c03148501c107c0c1819400020403000c0c03145801da21100442da1804000c0d01d078001e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 105188471 1250 105187221 105187223
    0x3020d06020f040f0303030506010816050a110303010603090212030a05030105010305181c030c0c0206040905100803040b0405040e0d1211070602180a0f030b010308090d0f140d05070c0b07 82
    0xd80902012140320700c181d024000a04c1603000c546802891401e0280c01c440e0041d00360707810401030b4001c0207004240074081c6003540c00b65240090f40e84010810032615030054915101c0540800000010034540c981c001100f024021500c01608445000c88035550b84900100c4102289040c001040650300a80c0925442081c0c00400c2d00e0281044081a061051011b4540d0760205000680d04450380e06121f82011803d507070912100300300140c0c0000e013140c0210320442045076241c4000034007200c25903000b94000c11203c02100e4449444402d000e58076001070280d58015460004515000304001464580d0040540c6801c80d07500c41c82595000640000511010151010440d8000080e140d100814a01804402085480300340508100c4240c281341c0c04182403916461042c008a00e03045403642c11207600a04244d80c0382c140e0004034070708140d943e0b00500348031075a0200b802805a140000355002140c40166480c049064400392804d00981074050407498091105011801c02000104416 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 105189721 1250 105188471 105188483
    0x312070807030e01050f19020901080415060302030a080334030c050405100513050405091b030c120a0c050105040b0702013608010605010f120b010c02030105100e0a090c03020d 77
    0x1c12040c3c02142980da081d03880e007402001e01401c0002e00032048444040c082000403055103004202c80c0020442d5901030409041c60080201c8903d2800c001d6108030006c6034042c0640ba12041907051080c2c040e0402c54a040441c9034034a0900700b0500005800341140080010341c0021052642c0224001e0145083c0c12040c000200302c08911927803107007a00028841c6d60360790240d4502650010b182402020340c0058003560402c2c09100c01540045084418000390580c401c40c82c0380c4401c001f078a881c0d841151103401580d43c1d960120380400120741126058096a142a040c954800046031f1074444c3c2c0c400c41c026480148806c40066101351502c170b070b042e400c41740d41521108440c4030040d94442c0486055480000720751041200c04c0d800e0003131034010007007400c00344000406508050101403582c42e60380b80351541c0e03a200860304c1e070007a040c040d18950090000c0100d840d00e1203408510354454020568405a01e200040c400c401c20700504034003561141c0c0c282070b04c51856083c02200000c9180444030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 105190971 1250 105189721 105189731
    0x106050a14031f0204081203070e1c0c03030507020301050906040c06030f0b04020f04031704050f040f2c0f0c150310170105060a050402030609180115030c0501090602031207080703 79
    0x460480554060003c140740b0740016519490104403515104420311540c0001380c0610800003501c0c0c01c0140d81100380b806440060300c0450300c0070b40e48080350b05628020080c80c1860004028998000c02030104a8070070303002089541c860010003550780c40201c0300242540084841401058801d0708100034146500e4130201d0300040c084006400d07a00510910020030002040070020701102029500c18107030080001071070f1a040002242000c120700050a01440c2c0342e41502481418070b9000002098010112903408450659842454030b034201b030306801c9200f001e0766148a400c0c00b00e140722030b030780000b4100034982c0c080d00102251504000e104440c041040040080d01d11105c204000c030115004000043e94a0508c0030010490580d8000710700452050042040c651a82c9070800e03040316031500340704030240d6926071031409403103407401210911120240020420840b4401c1c001a42e600f6265620555191503080360b490090310381c5002a00d160714040340000f401900c00d03941014035031402040c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 105192221 1250 105190971 105190993
    0x171810022d0d05040e060409030c061d12120a0b030114010314060f04020d02090903130f0503060105040e1b0114030c03070e030f07030308060d0512030f090106050a1403 74
    0x1081085041c103004100416041250a200340645000d0341142e003081c500342402e220607450f013a080105528002d80e03491141c50306060043c0c21b1031000c1548490184241941801c03000c55036004003560207010710591100c20311141c016415100f005c03000500c0b440007039980c100c10b03070080d001e10b040c02500b5560341c0200c04184101082218043c0d400bc8100c40038581103400c0103031031f1440c014401001c444006090100503031f1105001b880081e0121804803540d21200c0c41503045202d0300030f42c2d0911041c03010000806040c0034151b9001c5581c11001e9500907a40da606010503509512205641604000d6481680b0641000303041ca8110061400503e02c006282d8039010981c420384c2c003c1e00c401d501104120300640d1100011480d0481a4080c2a40f802ca50041036681c1c812408002c0c01e110b40500040c0c02e5441303007543c00161941150484240b03180403030351000164030aa1b0b807070038081003520000b03c0c1d181b01400f0748021507101030510f040491403d00004004400b51014903810301030011492 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 105193471 1250 105192221 105192253
    0xb0124030b1302030c0c0618071208091002010b0301020417060609040201080c1309020706020405040b180705180d0804030c170c010503060607022e180510020f010501060302030417181002 82
    0x7911404515208c1b00c0d03096040c00d144e5252440c3c9600508803400c42041200c0015888000c2d1151458250f0f55944a0201031605031f000d800c1c0fa1521a4142d031001c1000a4007a211989805403e80c0e60415110181c94070814810300c5102140d0281c0411510700c0403401c00c031000e0001305030b110354424030700d9449510703102c0c0182031740d002c4070b000e451040d0003260500640c6403e00c10300c1e0900004032040062285104100301c10240001d114034141b20002ca0446031031038400480c2003031103100030090400649035140186480c0c0140c0016034900102e504042004004c401ca803083e070492140050038140401001111190b000a0104e07400280c248134404c01a101c2c0e000c0d64900e141c500e403050400ca020340f0003540c2c2c01016060844d04000e04032128141c0c61101c060f000040d668142c4a2360041d5040440603072401c110b04038105020b40c40c0c440002901a4140e020710701452140482085aa204825070f20f00c1d8021100b5140c40c1a0019484020a00d419500e00c0b810a4003401079960344198600f580b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 105194721 1250 105193471 105193483
    0xa0b0a0c0507030f0b0108031801030b0a03140f06010b0703170402010e04180506071809090503090901140907030212060f040f0603030306030b0a14041205070b0124030b1302030c0c 79
    0x2214070302d1360a0ba0302010480414a501c0c0034104081c02542410241a0042c00c00c070404910f0905040d40c40b01c45103590b03240d482291000d9508507500c20840c43c0d00c4c005a90b41c0d9030365030302241040d0241c2d030000718a040d90882190807880d0150b03107610400600c8460074900b0b100c0940100d042c0251603060240d83e403a54000d420415022200c02d45035480305080442c01d04078018506400c10403031126641003000341a03500d1080d82c0e621000040c400055141c1545144a02000554003e899100014015202400c4400018002e8030210001e845d216000e6090380140f00030500380c4111000081c1c12070030150307445180820002d10100e051882641094111595500207500181c2c0312003051040c0940c981903581c20804103074041214455030084c0c501d0002001e0700044c5844058040044100e100d4400e48100d42e40241c008911540d4603a0b041e010055500b210f0f801520f41a1340042400d4068800c05200390009445030072001f0362200490001d500003002600107480078003089026220030000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 105195971 1250 105194721 105194723
    0x50c01140a0f0b060901050706110f0f04030309081203041b03020a0b0c0114060907080417031611010e100b01090f0306020405150a0c0609031205090304061d0a0b0a0c050703 76
    0x700266600c031101215080d0b8411056180c00383c0c0d8108010b01c12668803000b251a426081107002036a00041c1d0124900c0d0700c920808408440c1d80402d5601c81e00400d8801001101d10a403030306000b803565452116200c403041c17214050412001c1c0000380102e5521900c80010054001d1150031442d103c0d400138a5903e50768110a198030404114012241403d104000003004407070380011051a00c03200007503010300c0040c40d010270440440c0108041001c04000c0c420020100740d9032503107918100c110101d001800d03549240016001101e003032854201840340d0303074468100101820034a4508030794a030280c00300d001200d04000c0030480000e00701c45020420f4016500c00c1ea809a91985072a0030021062119110000c00c560100300c0a21082d80040740e0303080b06a8465408922090241016103a6440b0ba0394820030300c078244803c00c44030718804002441900c1103070b1a2013009009846983c4520b00d407407000d042c0c108030710000a101c03c04071240a080c5c164103034980030301115071554845044c1029580 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 105197221 1250 105195971 105195991
    0x90a05060c0d0612050c010f05070b04080d0f0e0604140c060c0105060301050105031603120e1206010918030813051c02060702070b0a050901030f060503030c030910030506090403050c0114 82
    0x80340852203400e400780900400c0d072400f50a138560082d4403080d480d0001c80050034180400522034400250082013a00c40850700070f000324200e0320745814032241e2703644221500c8411907e4004135a101c42920b2051080e00348841c4000d200c107568035540c244c070b0341c042240c03255040c0c42510081546a036800008000c1d1290301400414182459010700d800d60307006030050b41c4242c21144480b40150410b030041d01c00c03240c01210900c142d0b00102c0040e6402020401003a40002040884c83c80c0d1703210010b035080c126009280c040080d00800400c9048900c01a080100003500e2440406c09240248050420050081c003e941e0281c14034041c1c4180a21101101800b50700002c0400c01d00640600c01080101340592181d4a803001b10780f030040552041c0f446541c14075580b001d800c0c40340e0845a101c2c101500024040301d50340c0010318002c41c2c0e07a402184001d8450074604502e400c034103129008480c00344002928000880c0c0300ca640c00e0301c1a40203210501e0013507582d0500d0408100902c0c2000d0f01030f140c100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 105198471 1250 105197221 105197227
    0x10f0207060510030209070e0609040c0305061905130b03010e0a0308071206060912110a06121b1709100c080105190e1b0705030a031d070506030609090a05060c 70
    0x7180074400d84100078600510310b10ba00400b000980c99089496500114502d000d4400c85415800500280140c1c00003541241c40c02000d444250b8140c1c2c8014000c8800b01ca00084d0140c0134a42000c04882078080c0d150060103071060716610650580007942d5000c0010700205058850303181081ca00f0100c0902a000202c0a505211001e50045544e24486500e0b0380e051048504200000d804031100d4481c11041c55000341421050182e07180c085131044500030003884d0015500c80c0c0007004100485a004001440c0007001116078800c20403107000c580d802d888490114002c200f81d2601004001c16041031030003200b108407582c81c2244540b603400c908540700c005c5194106002e1081c01028681001c00311046003200740f080d8202c031000ba691001d400d4945400b0700c000c40e00c90364179502030041c00400c02d100121b505640780c0d8068010482c036411354020390350040001c280d815a101514401c0307903003018042000c07840304d040454409500ca020001100d600398800d40d620b62038000211100c0c290000c6c04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 105199721 1250 105198471 105198473
    0xa08130821161b031b0b2502030316052107090605040302030a060504080705030706230405070e0601090b04091a0303121306020f120405060601020a03021222090b10141903020408010f0207 82
    0x802c5a842046402c0070f002c0c124586907a0008e9528800900542034a101b400e02c030303401040c45642268072140307500c20344141a0001c0106501c0b42d18094039000c000c990f4014010030340300d10a4040d81c040383d4004004010320743d0a40c903880000c0c94003030030544029204028400c0410340400080402c41c0c13141000103081007c00380190754081c400840140020740708000e10000c2400084c0007401e44e28a1082d441003a00c803440140d40e45415a07120365400100860005107004065200c51400712228428010200d0385c4c90406841c0d01c104501000d80c80d07a040041040c10200d400d41e0706c8050310500b00140f4000d445070240e0f4813074020002103001000ca50f420842000001d11901c0d0b0000c200f80020609814290744c069100d400d03241c04850111004180540c62100c2c02c1d0003504144111802100304c0d94482019401900080000c3c900400e1107900c00c0c400c40b03100707000001c056400f0424107401c0c19204c0740d107085c403240340c1144441055024000030071007200170300c1aa00b1900c0000303001643c40480f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 105200971 1250 105199721 105199741
    0x60e010206060a031a0903090a06020c0306060409051b19080d1101020a020a0209090a0c030305130609061202070312051005040605040203010602030a08130821161b031b0b 75
    0x80101001d002c0c0040e02c0c0100001400d00c900c0884440a81c46030ba640da546000e01b83e40b41d8020400b20a43c00050140700042540d004141003804180940540302c195071401d0070702080d030310803100040407544218400c90510000d00050071071980007c15101d0030842031082050a14481e400c405400d4000c0c20410036000d0300a034a40115201210096040c03851240c0003035150820094041d001e8027101e4001543d620042c004d66000a0340900c0e01c80407140c80f0300f001001178104250408000318840ca01007640c81c0901d40940491340e440c0c1d09c01042d116010300c0c500c0650003a00c0c04409110840301582083c1200e405854454840d50742200004da20707000c10002a42e209a200c64041c0d8410001401415408070449100102a0030310366030030744980c01c10422100380403030090031071440030428121030b0100c40c0c45400441d03a03c80c8250710581707801a03900203640030f100380c010100720b0811000d02c03441d03030703091050414038000e003407880440306642c3e000462240308540c21207020b0010303802c004214030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 105202221 1250 105200971 105200983
    0x191b110405060d110105180301050f090d05030f0118141f050603060901050405040203030c01091a22020108090304170c03060f0408030a0b04020415110106120201020a0822060e0102 79
    0x64201c42091080f003041d01c940340b0030205881034034100400095004141c0c00300c1d90805041c00030260080040d850901c007000c401c00070030340f2588803d0161914100d403842c40380041e03c0c050050314810208c203074608103800c21a82003c0301c1c5c1003511501e0310f64100c1d60300c0021204034840c040c400e81441c1c03e121000d18100020500340c100d148036038410b200b88500d40e2a03403244503054803000c0c0c60010b215240d60000a20754003440e0f0300710400b0360900e101442080000e00c1c01815003240e51184003c9502c0e1600c028114000c0c4e444c3d07180e00c00503a01750b028099172140d600181c01c00301300001d8a15194541301144a844881c1c104da0b5129885642410920304040140d140d00400300c480840c0d5604041e07448003180d01c800340c5054440c0f507c4003605107a5035129070495006182000c0404200e40c0d0780c044c0a00601070310f00c0300013042d510b070260000c0c3c495030070200c07090303100d43c160301800c1500040e907070303000d01038120614014283e058003180161450920100701c000d004103071641c0c8101e820100009242c85 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 105203471 1250 105202221 105202231
    0x1140d09030c1a16020a1509060b09130605010b0901051e0c0717060901050603030307110114070804170c0a0318032a06030204060f0f030902090a090303060503010e03191b110405 78
    0x51b002888840118200c42c00c441e00441e03240f003002c00c58501604140002d0300004000c1a440120070b802d0140340303034000b207070f484030144113407002c1c4416030f42c0300b0121034280540301c80031303021074001c1001100c0508010084850020ba0f180e0180c244801c58007014642a0141c000d80e108502e0b00c075194002040c01c1040c90740c40313411480248924500320003c2500c900015008005208800d004c0301c0c4818000c0d009808444c400c10000c1d02c180c0f5012500800008081c0c8003550340036480701103003407120740e9603041700c038003851100040ca80e078016070782c00301d0700b40822032495001500c40c3d000201c0000c8220401643d0310503403014407100c03803000c91450300d081d10aa91150f0145072040008000554010300304590001550508508803482403100350301070302040000a5005840200b044825440b40d807040b0030450203035508200c816291f000385800c94034090303e4120f9039032007440130480803040311a401d680901589030030704413031012101d114107081507c6400c503a14099448000a541418410581c0c82 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 105204721 1250 105203471 105203473
    0x609021b011506090302011103070510050402012601060509060403050a0602030405070e060d060903020f060a06090608070b1803100e01020d140723130f030c0501140d09030c1a1602 79
    0x2052921001a11821300c41c44000d0600c010201810b18100c400d0050f504540e8100c0250380c0f080b52044c41041c01841d040310304902182d0040f0700c091800e544070a40c0462528840800c5080c0c0e403d0460075161074009840041d07119804000100000310140701514003c3d100350000741e12401d0624015040c00031542003216109000b10800a9695803101078209254200f03c00203500900c50038100e0030082c42c840d00c044103104039000d00198442940c80142101c050300010440740d62100c1059480ba0058031640d00380d1541400340d2040c80c17508540c0c99881c84c03801411115894a040300d01c2c0309549061606900c1d69501148520507510f00d40038007005c1c400b400303401c100c3c54540400042d009500c10b20b9450b864a2140e0030009000c40081e045502c601c0d0303046440046140d030790145202a6240d800202d0b240e281c0320b44002451f5003d8441080842d50780340300642054031170070b00c060003489000019406c0002e21564000031455800014040c5102c50001030b51030701d03080240f0484680074030000811 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 105205971 1250 105204721 105204761
    0xa020903161a0304080a0c151508010608010b0102030702040b01031b05091503010303080703050403031824020412030f050904020d020a11060c0904050907030b070807020115150c060609021b01 84
    0x144a0012503c2c86e28181c2402141c50301c031410300000c80e1054284480b051481e00315150948840c03030141a0417074000703034000d00030326032141034481c00d80d0154410b250141c2e100703001c04401858a504404030702d01061600280c4c5084541d005001c56102c00305480219900085107000c50508203038001740085134180381031540d45503075002464210300030144420990b9034800f00e02054420b03000714500c4000e40c544226100040e080048045040c00700300944045c442d03100203168005402901c0c2210502c9c00503c100c0764040d1000d84101908071b09880401c034081094107620b5a451000e400417980e03031000143c4074031416a0140086c3c2341284044140d50100c030801140141c0c420890b83c00c10029100071a40d41c0700c42e0010344c41c001c0e150b04020709443c0d414041007905544100d44a03c24030441d0700034446121659007a1804100601825155810401205104600888003000102e12234880000c0781c550b2400120100d80160842ca40d4041c2d9180d1480c00b105400d003d070100d890419514014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 105207221 1250 105205971 105205973
    0x6080109022b05010614010905120307030f11030f0909072a030e040c08160801030305041a0d09120f0302090907080601020a0510090212150f0a020903161a0304 70
    0x100b01c60303030b0002410075261140040c035000d21403401c009016540301009002054442121303807100704404140a000488201000030146496084078503600c4452000d03501d00241c0d502c085490350b506036201c0c0305002041001c41642d001c10401815186c4071485101c0d00d45200300c0400001d41c07005806401000b00d00c2403030b07181c00e241080010492103100c4041080150692906445030000070000301d0380070345854810443c1c0313038215039254410070700420040c1e11814400c0f001d0f59903100c203000c00380c0002c400303220a2015412440ca003400d102d01e0090401d050600d8080c40c038041d115428011101050080039084029405c4001c0d4a0319440c1410154100794100c0042801000d00504401c03c01058501180081e40240087c0c0f00898011003a24400c11051800ca40076103006041203000300c1c210714461640b82d40110303244140c03803154854030030304d500e40d044100042100a00340b07403010740d420020321245607020800b1418000c07582c0349a84441e890100d40d0704120400301c0034040c000f132003001000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 105208471 1250 105207221 105207229
    0x20903060705180405010b040306060f06081504270c080c03100f060e0a020403120c0b0a05092401050907030b060f03040c0b120f0c0a020a1115040b04090608010902 72
    0x10303501c80c00d2440c002c0d4403003185681108403281043d4a01d038016151200101c1c20410080c0184252400b0700c00c240f00d00c1d42d5801101c418111648103410020704580e000ca842c0d414a0343e9a841003000050000c40c0a100f500c09084600d03150504200c400001402c0341b1003088a168001e400074240c01018141d4001a040401d0b101c940c07040000c0340c1e01c1c2e6940005450402541c0c490703000f40171410300b00c070301501d00100240c0007544640002d90703c17544038a01460741340d03101b4406940b00c41d5000034040195280c2d0045040a0100541018154000d00e41d0f1600d007210005034482101000500345142035140c601409412140500910101810f0210804068071400c0888482c074112020300355990783c9900f007503208202c85411a01c241000001c10100070328541c104540180341200d402d58054580c0280c041540c400c40f001c01015820851028010810304c41c2018007100000d4060a100c5410070f038030003441d0380310740c104000780c030340210b41400314003940c0c46110050407410008001c514540e80020b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 105209721 1250 105208471 105208483
    0x30c0109030b040501020c0703030906030e0309060d0f060b0f1b060103120f09080313030506071e0c02040f15061101050103031b02030313290301030f0b060604031a0403080a020903 79
    0x2502c0c4507031040103d401c0040950490381781c040b544068130003079074491400610044803485081c1c0000c0c00e2480c11800d4a8002c0304484111000a20b200d1824202007201406003004900700703221995500030024002112500814407080901c1d841c903a64020004440161070600740649005d501032401400051a41c0c0c1c603502c0000c00d41d043c5010340b15030011040310300784540c0d00450f01e940008203000b801c42c2a0010700b44242c912035820f0700c0450b550000111240d24052100b4103070b180891150b442407074004e490503007103180040d00200d0a40c0e0404001400e0303400c01d102140b01d1000c1e0540070080750780d08c0700c40404000040b81c028446035145450081070710442101c48491214007800f59400c640d070170012184c01c5146008030307242d2a5a00c14845843c1c0340c0c0418141700268066081c0300c00681428102c80c140e961040415007640c0803603c54001c40300c0020030f507a40113941000040040f07281001d600041c00b41c00704168426190070b1600030401100604131846081c010701c074950080e034000c01d00e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 105210971 1250 105209721 105209723
    0x10e0a0e071a091906120b010201020c101e020c0705030f030c0307030e060403061a01030b040c090b07020118090903030c030b090601110106150201020304050c010806030d0507060605040f0b0f030c010903 89
    0x82d090b00e80e0280c000050005040038181d80c21040d82103000220703180c02c10740e1076002811500c010011a610200164240e00c03410425604507000401a6100405580d20500440064141e0307540480a40785c00b107001ca070311841c0c0c112001d50000c0c0c1c0400803454100906949041c1000c061818148070810071a0350f8020303010700500b4001c0c1c00844c4461601d8002c2a24000c640000c018030100d49201c0154030f12000404085000a09108648440741403500607080202100d0b43c4d01011186840e502d1007490301f00400817810031131100e00d0000340d02c13483d100300400b50202c18000074a82100c0d24014040f0307401544c102c4245814403500b09199504c40c4445540b002c401c0c01c03c02d075001c82c040b00480c0100400d420000041500ea100030113011b070b054cc042d6104c1c0744904100c1700c00c42c045d00015034503a07030200d03249a4558014004488528411809804142c3c825000802c4040c0c50740c001805a40c0072140000038956626658001c034941515448081001600a403441000da40c2c0001d21207485400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 105212221 1250 105210971 105211019
    0xc010b19090506010c120c060b060310090b03100c09080105071809020901021c020a03090f030c0b0d06080106060305190b030705120309090f07020d02030301150c030c020306010e0a0e07 81
    0x40050f801c0d0f4011400e094003e035001d0800c04002003039803c06044c0707a8030510152002d51401010181ca828214204da0140d004803628050551802002d14054805003c04031340500410300603200c201c245004058999900c3d413500d1031401d0030700080900315207005180c0c104101110703004103010741c090906082601c00741e075409603854001d000143e14004403525034403250404500c00800003070780484c2500c0500c1c86980c13034003030441d070f038580400c039580e9607010243c03100030400410440c1598a10040c2079910640b000440d005640304d940b1030844210303030302c41004a0380700e20401623880e03013121002c030316814402c0d81005140480c10100f40d8540060088070301540c84400c204860600810503104074400040c040301071071810040ea1015990305452803030151040044009003540003000f07482c10b0750b2100100741c01403078a07c10300311800c041706102034051005030f40081c4050786050240501918040400d05202e00b00402944100c50202042a03071076000050b060100d0140c00d0000d0030080d039980 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 105213471 1250 105212221 105212231
    0x1060f0e0f04180c1509060809070e04020307080d081006020f1002030c0f0301180c0903110607080c030a0816050a09090506030f03070302010b0102061530070305030c010b1909 77
    0x15000c1100110490000e81088407080700084d12182851030752071714800caa99140d211568404050301c8025043da000b046580100b45d0600c1810303042c6e8440d5501c68002421500036564600006041c81d01c030010000c0000c8041d0108200903d40015080c002e10240c801450760060902c1c00b66200e03680b140141039150380000105030b00d9800b113400d40c0c0000d52482080d55032541e680300103c4658454085004005003004600b01e040c90041c20f986d000c80f80c21902000307844900d20704002c1c0b42d50050308120b4000006006440c10404100042c4c03105001c15203070280c0300e0421402c4524040b03060382d005000c00000b00008030509500a1801c0700301ca480362004242d68030b80d00c001a05004403140c00d0030551002050075070515a0540001c0c5030220280c0a540035501c901c40c048183d81e01001c03019801842d801e114543c0700c60700588002c44421644810080d0f03803081001d080c10800305a0003560aa800810f4926180d00f0a02c038010380e510044820b0318591103045440340307180c4154840c203500c0036621 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 105214721 1250 105213471 105213491
    0xd0506072006151f02100c0806030604260301030b10050a0b09060d06210b060301020f03040308130c12031e0c0f0501020f04170d020a08090f010e0306070801060f0e0f04 74
    0x14400483e00140203144c04500c868007203c00a5a6880741c1c942010742d503060090825285000e82009405680d0103005000d06a42e07a0719a148102101d1181d0044003044a214203186840c600245010b54407a0709a0315a17400d090041d001d0b8180780d50400b80c810501d24608200b1060010101c42e40f101081e6030032134642041e5000c0100511207036014803034090b40e50b00c48c80311a9407200e0002e51007a104428200f126111402814200e0065502e0004400340410104000c40d0299101070b5100742c144011010380040c907614070382061042e0b0300c10049500c11240d14420190400a44501101000c1c90414042c0d01c10b203006080c000f255201611400c0031414400034070201303404441d034101c480038005640d035039200d99600700303404603c90420f01c0707000300c0c05c001002d1440851484446500840c070142801814010000c03452041c0000d941406007090034001036450a20403070340b00d00042e0320743c0e244943c9415009400409c182010302d0030080300f036802da11a981c4113110300c6050401601c00040c0d845403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 105215827 1106 105214721 105214729
    0x60207060f020c010305061c050304051327210206071d0a060305090f010f0207020906030a0302070306020f220504060909031b0602090d050607200615 66
    0x43c08440300c00d62003030304626086100200001d42d03569180c1d9056981d80b00428084507240c101040403c603e15110b400504281d1140f40284072800581c025080c090f090442c03029058550481001d06024121030000c00701a45130700701280c02100302c80041c0d41c412040b941140050040a81e2000072250b220340d031030303100901800c2803d1035814050103601825000f0440201c80c400c007271448007118000d000340000004035400041e942d0b1941e0050000c0800000d0031207000390701c02c10303d01000a500189100c00c40c0d030040310041e1980d1006808400c0c40c440c405220381c0c01001400c0c600d014031400042c02d41114000c5508000e01c580d1004141e055580181d0041c003c81e00c113800c1d01ca07800c0190908a50130398803440006250404170000140714254202055070158000c6040260f40b6401a2042040009a68031140440003109845540d040000c08000c07840c40c00110341a402c1c1c40e = true := by decide +kernel

theorem cover : BRFrame.Cov 105035971 105215827 := by
  have h0 := BRFrame.cov_init 105035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 105035971 ≤ n) (h2 : n < 105215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
