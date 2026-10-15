-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3843
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:50:28.169661+00:00
-- url     : https://prove2.me/submissions/8cebe9ff-d12a-4998-9f33-f3ceb74c71f9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 691007194 ≤ n < 691187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 691008444 1250 691007194 691007197
    0x17010b0f10051b06060906120d050a09050a0f03031404060207051519020105071d010c02210d020a030815030a030c0305190509040b01050a0504090506042c010501170a03030b06 77
    0x2480740801d02d00c8408003009010101319240f040c2d00495010605903140c400300300040100c1982010a03900c46040d00d151035009500908d28201e1506080318100c2c0d80d003000441d0b5582a800c03245107440c510500b0810150003040c40101c071070108650508250801c03000035139a43e110310a00d481a400816008100c0e0182e104813030200180c01d44031303140035144020203400b8000564107800001e2489612001203004210407001000707050351081e0683c105034003003014101c100e41b82260845407201d198004e8800800c4001c081041e48e4014244000c4242000303091161300130201000441e0016590032035540100b030544c41681e250400442c04052824100e415008075040752140c0402001601070250300440a041c8603482114240f18410b4182c1c011502801080001004940c044c4014402c0038130700d8001a622a001610002e06121101c0c250b00440d070103050b502c80a41078021101154000c20701419001d00503c00e9945203141000b0391460b5550013160005d1b00701a42ca52402c86241c0e5233a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 691009694 1250 691008444 691008457
    0x60c0a1e0c0801090201021e03091201020c19111905010302030a060f060c0506011703040b1c060902040915031212060b0a030507090806102709050717010b0f1005 71
    0x40551600350b141c840c003500a000a4070146d0140c40f825141d560300342003040d0014885038040010710304021111050121040007060340300c00654007445002e15450f0200140b001a42e400001d00c0115a2507003017075003c0c036502e802414007555108805c80b20524524840c007080b10000c4c40c005079241d0b100004080104072903041401c20400a074000142ea50340206116030f214000c10903540142da85035258505902c0c002c4074495680c00c2404100700705158040a042a500312142126415420a10710005ca031a2a0041741500358080b40900c101c0c590b40c0315501e450148451103405250440d152181909109445182040240d0340c01840b0303182a034101100804c1c815142c1c03a03e80a03501000b41c058002201c41c0340000760301100005000d1000105c1a004001c2c0f10072214101c0c0c1081450415072603410a0b0400c10001102c0385000348090784610803030980920f0180064905200701440300000010441625a061481c010400c3c0d5840452080e00402182e030841d4045181a054800e4018203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 691010944 1250 691009694 691009703
    0x714031b120f0118020c060c0714010606030603060b040504020a03080912010207050c091e060d2301091704030312050601020a12080406050f0403080f06011112090f060c0a1e 76
    0x860500040d50ba0691070b09068801c885602c44c4203a40c05440681207010707203481c01190b030b800365010400041d20301c401045020302840c540d0221040005c50030742502c03020303030188000035514041002071100c44c0c801e0303e107220b004031401c0c41a030038140c0025443c807029020282c2503040004005055558004d1408034901c2c0f09002552244094104070b070315501141c001e6030107001c056001604003003114080300d1001c070b10303440d019070b850b200c84084c000801009035088a408014200001031125100b801c01580141640042194a21840c020343d5031204100000c4c2000003d0000344000b035000307044800c202c0140c110000b401d65803240100e241191807240680300000c80044c42c6030140d405007600703120700c0c0690f0081c0a10788488090603607960044a0150001e00c0b001c002c5006120500e084541042c1c1c14541403502c5400c06920360305102c0c91054400150500082034642c070b04280030840da0954040320b202e410000c0503110251a0203041000521200c0444465000421110364034074581c2c0d0071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 691012194 1250 691010944 691010977
    0xc0319030e011404060e0f060705030405030720031006080a080c0c15040311090421022806050a09030c12091a040801053102031f060501080714031b 65
    0x10940306003a80c02080c0d4007070b917109003040e1040013110000152a800260840001e1040369282301d0119065003003c0d20885860000700300900206503082e04a68640000208041c0d4948a2004040ca008071008a1017816802d06504001c50503001c00c00d4426140c000c00c042d6681d221009489047c000b1000300b07107030300240043c50900ca20300f0a40240082d24890701001144862110070410307049811a0005e0000c042000c44810008010104035120041801110001007490b01002d07402d00c07080c08507080c1c11041c0c0c080e503000d10019000300c5400200f030071020003510cc3e00303850003006034a480c00042c0c03d427100f016500010a1042003401d00411160407a06885028450320071126840341c07242d0280745d030800b0081010b50003030b104040bd8009000c0450000c05000a0840c0d24055041c1030903a854042e51100100c4003900e4810211103944c088800144c0f40c0c1080005400c070580902400d08000910b24520341c8002400e00f26074021180c0a025413581580c4001003520384264079035480810351 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 691013444 1250 691012194 691012211
    0xf010c030504170f040501031821020c0409020d030f170c071a06010c0605060612040c0f15080c090604050310050108010501172a090106020f120c0319030e01 69
    0xc0c5540024019886880354006180092144106038001d00314610b048541c104402c01c4158001c0d17001c95680d004016014010f00d00d9a1240002d00c21445150842141a1417400c03000c15818080038403101c6046404110060007a00882c0114595100040a0100802118840301d0140000c4901213500094002c2103103480301c004a05504490000c50341c9403001540040c40e1030b10306100500c00c110694504102c4002610350300042c0a000c1c00c09900081b04004030b0202140c00314500d4802c43c0544070201d02c040c50b026040701c0c502203503400391175140031f10300d080301d1140d07172000c1900c1d04140c0b9a550140c035030b0b038900b000404510440d440240c1c14070a4201003036201d2501e4001034121a034081c02040b107a0399840401c8541c08041012428941040c14280008000c4200c00e0b59085500320011022442c2d66020800206003a00310a025901024040c6100c010070010a0803506a00c28078600b03195071402c1c12a41c0b40280d034140c40c41c8201001002c10078a109038416a0b04c1c44200c4001d001016 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 691014694 1250 691013444 691013447
    0xe01093602010f050c0307030c0303150306050420180a14040b1801020c070b0309240f01080c0901090902030a0230070308040501052d0a17070e0d050f010c 68
    0x284031040303001c5502c61005030900381c010000d8400034940d44c000745151804542e400c580000c0003600450502da690307820003a03080346108450024611804000031642418140070f404030860424880030782c0c0e0580003a8034240c44038640030030070782c0cad121400201d02d44425410302c0280c410b500241c0d00d40384020040109101d6810780d000d00900c1c4203038000d101d0382d14006c400c509078800e0382c003000000d50002d0020048a20300c000151740c0010103206842c85440042c07010000c800398401103088400c1c00400740810000c1c801c41c450f00400c6298002c0c030b80c54004502045507400148580e0040d0750781c0d0350b400000e544092284607a8107900034802510104200c0d00c03100400394ae0540701800717405020341900075000c0016040240d81d0002e5040342010300d45401190568008200c00a02c150100301c415000c0c2c0d41e65010f02c0c001c00c044401562501100b440c014070320001c1840a034200c440c44d00c00e0040c0340d60410100b120007c3e05994070368140c1010700300186429282c8002c00040c1d845c04e4022650306 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 691015944 1250 691014694 691014791
    0x506070c14010e2e150602071d010b0705030d0e06100f0b0f0a0504030f05010f0b06030f0a0c0c080d140708010303170601090e070906090801060e0109 66
    0x100e1041952803a00c000300304110b8200d60858841d42c0380c540c0251419580c503501d80003850300109580c461030000c0100c0d401039109441c60001c007408100e242c014117101c4e003501800300c280548894500c100c03400e07990001c2041910720600c41c0030700341f0600060300341c2802410f20845480c03d030341d1442400301003d0745201076940e00c001c643e01c0c550001001d0011403109807041004e01111543d00030709003043d414982e100701c298890007407030707040c007204100000c0058000c2100c0c00c4c51901400000030030709884030800003524007025805124490402c2000300700284029255001a11750000141000c0e44240c240e03101e5403410f0025100c0e55002c981e0040f94a059080011806203c3c85081031644880c20300341c6032000280401008070f10016161500d0940c0311102c140d00c100c0500d400c2c9a081c0e900c002040300008147d80e480d000074805002072011a40299101000303101407402000710b9441e10529448540040c015504e00301d403140c07461280e600351680003090041c0013210141000d800d014890301203 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 691017194 1250 691015944 691015967
    0x30c0602091c0213140a0515090a1e0507050a141303080417121b0307080d050907150512060a030506090703060c0e0f010f09150323070e120a050607 65
    0x7400000e82c42c07614070009401400c4140b030300700c0c21220454446103946001340c04018901c40c0211907140c03050142765514944103014090380e41000442e105802c41071803154400d00852140c1e9418071003070259859020044426092072850005400814480707201e980e1b12a8031461034903864015004818002c6510080048503442008890818a440900350312242c101c203880081c100c040c4580e0100d0181c0c940070960310700e40c94050f40d203013129913910b00c4519040702c0103686143d5995404c00c030492400700241d101910340d04803101110705064200801718400c01600d410701c0c0c0c3d440700108485454040032078004d141d10100769002d82c50304000e41c9649651031301c01554154107000d02142e030540580c43c5000f100300043c005840740d900b108010f44a480d02030358140104034040c9c0e800140c40040829041d480611a68041043c082c40020b0b041044c0c001190b400007003c001040c03080d860340040600d4168201507410101c202090110f5a09000401d08090858002d44042000b0ba90740701455039007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 691018444 1250 691017194 691017199
    0x9060231361d01140f040c0b0a1403041101080709180e01061d041703060f040e031c0519111b0f01020a020c1206191d01150905011a0403030c0602091c02 67
    0x2640c851715902803420b020380307020b018642e03814010b00c030b031860200c014516124030342000b02c820a00ca0403c40910390088400b65110000711352045115079110f804203070020100d181110800d82001601618400060303031016030395940e541c0e4075900246c2904600e00602600405d049020902c59030080725680c11201115a4070043c0e4641c54201c04041c00e07280640e2000d080c90030041c48040500000f4061140c1107500e9210500c00d0251512030200c8940113005404004941400c0031031b000305c20848120020041c1d14240700e0718420000e40b4800b61409002c8031011241c0f0010030700742060a102070790303c0413401035000154502035075800049450b15120142d031040741c100b82242000c0d8481209071001c8081e424204c4206c0b03610b90301500030110140c0004240035104210045c500d00715407500c06c0c1824004e02800701008480c00c10b214580c010301c01003405417a244106035845043d4425808028140110f4800020500075941d0503a164200050518140d00d10048a04950488045400c92 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 691019694 1250 691018444 691018481
    0x90105100602031204032c040b040e1005060f0a06030b031614210304180c020c090f07170903070c05040b060d09060231361d01 56
    0x100c4240d000c0210104a4090360b000c0c50130608003c41c6140e0900c800b51041c2c08100304825003207600b03004000c001e400b00e09186803608903103410030103110695034a608542e204920304004142e58071404100500d1038911184001041e07039a41d00020341c1c846800f60322542041d45500c005c21620b42560001911400440441c1c002c04107000b00d07050a103080c3d004881913089024000c51040c106038540c0d0f8248150300349511540410000664515040307039210700d840f5903a90b0440c007808038031441a8840c082c01031001e4104e002081c0c2c04210074100203000b000840c61b0440000340000d118044511144034028285119800e2a143c0e0035030b0794212003001ea40840b00020002840d280500c103000040401500c1242484da8444110000b4a0346480985125400304002038a140304009c0d084900c4980403460000310710a5401c081c11880c0907000548540c136030031030107404011510403003881008192196004c015071a0605005851030b0108007042c1c100482c0f065000f48019000f50014801241d200c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 691020944 1250 691019694 691019701
    0x10140303070519050106210303181212150803030c2203030c15090c0b0d02040b0a021e0703020f09060102010e06180d0e0a030602130f03110406240810120b090105 71
    0x47d158001022001c0380801088403603000a00a8019002003d50022040314007500c0c1d03283c180704405d203001441c0018024001142d085c0910748901140492603c0b8424805800c192000380d07170b444050068410580b02081009885d03116046407540d030310440103c0065156246405443c031048820129a1403030f40e505400420719192242501d0150044a00c010716442c05800b16041d40c4241d56406c403d680070800460801d4041c070085c44020740301d50007840c8981c90386024041c109000a01c031201600700d40010809030360303196400310200804840e80b400079203400340142e004008100c00400c0600821040008044c480710b000f860850103c4c050b20710000d030040084524400f92a9100e44c420a40380c000d1021541640c080c0c00010004034485031020307160f03201c4c40394001a551080341c8408031071080078903078105800b59070020080307101c0c1082c1a40300c14402d210a01342d40c04440c000c002000e00010b9039090700c0e2400c680205101403c201d803200d014142041564412a49150190301300f0011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 691022194 1250 691020944 691020959
    0x1107140114091b0405070c020405090c0405060d110108070c14070503060601022d07030c080c24090d170403110a0f06020a0803100f18050603030310140303070519050106 74
    0x240c483e8182809400b180343e61040041000602c0050900402c200107001078400588641c4112402614200c004240d6413600702e040100ba41c5000b0b0005016601e15500000002d06203001d1032920030007400c20340490713a00d40344119480c84031140c0240000c04600141190142c01140f440c082d00d40960984009964103001a0ba8421541140d1000c0c0c007402d520820040180d1709035860f01085010070f8409007980c81e2120000c81007181c02c81e041079002202003c9031454070b1501681d030340c1b07031041d034101501000320801642800b0b41c84046009095142c50b2030104072b03800c0204001d080900070355586594403414890031001d5100c9030300f03000311100303000072449440041025045801c240d004003824076080e0f54611558101429403070702d45040034400729480c003500d052800a044030a5040700986040461501500c030060700782d6000760410001d000c80f10160640800944000b800d01c01c08504450010070b145121380031b0094580d000d000c0c020020002c0c20030290610ba40034200a004107500c4412 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 691023444 1250 691022194 691022203
    0xa0203160317070e0a03110607050d0908250618080304300209130c05041802010314012105070503070609081e10050601030b09010b030a061e0504110714011409 70
    0x5613a0340840030785400c000090540909600b00301010348168108411551030500e0803075140c90540100700c004c0820300c526081000b0402000407048017103900d031601d003062040d0383ca10300d00403030080000d1031584000900714804000000c201c244100ea9443d035440e86480c6070b2201c050341c4003503482c000f1090210070304000300210590a070010000a4940c070742d4050740c07500000041c005c0312203000007200003075107540314411409031005040790045400140c0c40010111a00c1540842c1710618403c010b01008071031180c04c01402410001c104506440c0c3e007000d51414110780e218660520a4090209840c2d41c0320f503000d02282d00d81400c0ba441640444892803a02d08560310381483c0d54013170108982c405001e900f240d03070000c0040c107000070f8040311b040c0410526042604a42c7d4440c40010a120b8129810700c80c8070010038001d50380800300b142c1900e00c0080b02c031136481524030451300d07405103445803d0710400311a1240d622208a080e480b04d1140f10354042d14090341942035400c078050026250a0004c034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 691024694 1250 691023444 691023467
    0x111003020a20150601170a0617061b0f0705030c07080118030806190e04030c12092612030709232107080a110a1202010c080a020316031707 61
    0xd02503c91074107000007500d6508001018181000150131040d110520b48216060080b0101c0c80040313000c9040810000b03124040c003c1000086c1e015800300b0000e420598262408049c00e0408682e585a1043d0408403078098070601802030b0100080b0780c0c80860002a00d68100c6070b1200080c031810f140d91407901300342c1c0660000513010960b0240001c04606d003038000c0d200949290b00707a0000c59621148907100a01044030200c0c007007202140168240f06d185090050b000d9620f1506079001814540a526103407111640300001e5801d104807005054030a200545200002c4086141ca80c0b070441f8000300070309803c5c8105003070090001151a05815680c1003441021000341881c240c0b01004009600c160740a200500280d0066510110f0620028007007261550f0080c5010b404d0618008100003103c0000d41c04100006542100000140d0300940400b00182e00825219201c2c038400c03500703a044d8030402101c0c40144032400750840800d81c00007000011f25000c043e0705441d5541c1c20400761000d00f21704 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 691025944 1250 691024694 691024757
    0x603030f0d110d020d0203040c0918060506060d0c0521012103122f03090a0f030c0c03031d011d0d030507153c0504111003020a 56
    0x800c1240416801504640450304070b02542c2443c0c40000f01000702243c1001420f07880181d00001448144071f90426550050240040c0411031549908c90700710103036208000040020792903e000a101d07a43d403000743c402c01e94210130188410b0111600080983d403001d140c0c82c5180b10038940400d6180c1440d0745076030581c1e03450781049840e2000c0703807850f0030b8810781e0100c120100305c21142002090001805a502100700e40302070540c10301007410100082d100344501076404140e0500400010b00400a001c3d510b20f5080250301881301e0050070100c4a001069030050005540f0000000c101a0311003000d1100304110344400501c40d4800004440050341e84840c01c0b584c8035080c07503202d61460181d40c801c1080f4072905200b031622a25548041d620484107000000803503450f500c2c01c0c0d500e1403400b0584410640d45083c000503030010056084021144403030b02000c190741d540007404210f694040e0402c1c030507008003290790500c0f001c94007c010354044c4044c05c00207a12100040056000202c880c071880132038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 691027194 1250 691025944 691025947
    0x90915100c080c0111030613020717030c04030503070b10081605060a0219060903020c0d0c030f0602090409050703020307170312070c08040308070c05220b0f0a08150603030f 76
    0x5104044955280e82101603400c44020403020300c04031400d11502032805d9001c418107803640780840c00c001d44021800c1080c95820700400c840c03000241240d4501c100c00d41d02844440e102c1e01d94941c403520300c0c01103400c0104540f1001510341e082c0704140700c0f00b511038103a0040c8030040584550300076880340c00011010100001c4104240324a103450400f0742030b21440c2d441204c20082d1107d0305038058003c548801d03100555907020110a15606004600e07000d48103a8002d2500141507846000d072014921000e03107000c100d2100841001420b4044840e0700c230300144140201071150500380d484d90803030b1000b20b01c640700318800003030406540c0706c1d0f45110030921001b45041c10654400255003c0000b0420004c00446004400c00a01401c015101450040340c0c4251211400d00d06a800c1d841035401071881030710406044141103501130110140703480303140400718481c003421780840c880040841c162680f00d540031002080807000021000600d440340200885d16488050a15032a885040401c5000150 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 691028444 1250 691027194 691027219
    0xb0913060614130c02030918090d090608011215021c0509190b09010b060a020d180b0712021e0d03051303090501080421200d2102070c0b090915 63
    0x10a50301030b1a2000300745c0180c910300580a0001410924103402200ca0804401c007486440c000030024001c680030340d03080078100719003488005800f1000512a08900841c018007410070000805900024420b12500954490b0003142d01481045c42c0d00407003200032890000015480600041c0f250601000716240995141c0d054850150260009040224564032548c0f000d0694503500b00408000b502035015201c24100710704c0040500182e211a4140b030703a00f84400380011700002040380e403401c0c4d01c40c0b1003009081c8143d42c10b81c10034181c07240c82c207040000524405807014004c500419030022035602041183d07200d0500c44400045a54003600049610b0b005218550140c2070743d6800c41e0044000d070030300c0040d039101030410289140c20b5a001075568a0011300b100140a0441004144000504041104944000d0203c0041403201650380e01c1c440200070500c80301e0341111249500580100e1100e074407101c408800e6840074602c1c50145407024000350400106144002a001d001000a0704018 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 691029694 1250 691028444 691028479
    0x160506090424080a0b011707060c1a01080718050f0a0903050f0d0f1404050a03120f1508060106080c0d05060f10030603031101020705060c0c010b0913060614 69
    0x15001c0c4510702107020b02100360311880b649102001803080c10010a0f031402a4a440303000080e0680c88000f804010388032405020300c0115440b41510343c00c1c070700307503d010005080c540c3d614058846072000b900140340000c101c0c50000308005003136072030b00f501c01d0400801010095084401c212007168040c960b80c00450090b09841d00040341030380c06480c00f42d060514000308415a41d1010380700100244d5100030604c082c141c03038042c840a111300c0314140307040c2e4503041e210325890754003111004040040c8800d0301000a000c03588868240014000304120021002c20403c0b80190280504480d5109000000446071702c220122071082682240960502c21140e1190b400b40c200500f0b8598011500001d000d030b161158200f1440e82c84142d03070701060307203861410007911076100b00c07114401c140d0040204c80c7c080b40000030344a401c00c0b0000202944c42190180c564010900340f140e607071348081600103000b0b0190222a540c18894000c4000f008203565030420442030301040d119068000e4404942d000001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 691030944 1250 691029694 691029701
    0xc030304140a031709240d0c1b0f150e03040920030901020a030501090509191406181b0a260609100b04021315030212010b030103051605060904 63
    0x1c010140044218607103903912a0800100003604201c4410046920401468000c0d40340c0e1a942c01c05081000c03020100d201040c0910a000344d00d00703000e4a4644113103a481c40380180c03212250b0030001c940054102442e1030039103440800816146155081203049045015218080702d4480c04402180b030039140040e02c0c00945052041e51881440f80115011031441c1000218811650740b000142d803010071101c003404941c070680080407602d24000c1041038403d03001130f0000c901030407598641241c0c540ca181c204000e600c000401141130150006120ba0503080850404c1c8950b911010380307102000c14128106003036245400c0550040c0708400810500c42c0180c40708100d940c980c4d02c442014440150311900e081015500541d50fa8460003c0a00010241c4200600c0040486096103000780c1d040810b5a0500140155400000c025038207008030390003079044407100540c0f5400b60945682d10500070740c1c250801d00c01500c0c90300a0000d1014100040ca02681c00d0320070003001d840c2000312071414007004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 691032194 1250 691030944 691030979
    0xb01080403110c04051021020a090902030705032d03090315060301200307090e010b0405060307050d090f02011205091e03040906030c1d011823130b090c030304 70
    0x503000d5840398403140c0c0c4881c018031b0301c60f010003254140c6141c13405400400d5110b2a401c3d84001c000044880d00059440c0680c0c3c404480a10300c000c110b5110a000280c10300010f507101e560300d4814050b2040080310652502215072a400d14031101c0f8003d0f0308030180d1a480744411056154000c0c2403107145280e4620241e9421a00117000058849034400d901d4003100c000d03002c00321150300c0c00b0040010540d8015811f0029101d0442106560351400909889074040c50040a21401c0040000f950072403046041d504c1800e1300510a00026070b541c1085c2c1d1201c50f2700034003a070000703504503400c0712000103d0141e140140e000d034009012800306010481c00b070310f10044244989000401c400612440c807801041d02850140842420b4185010f00040b0700c85558010140c000010000401c0285200d85e0300c9100841c4009011506510080460340751284642d40b003002611800c0501410299503c2051101845503d6041194407480d000503034801201400c941d02d07038003c00c001e20555a1042e00c0c10310 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 691033444 1250 691032194 691032227
    0x307030507170f011a07020609090a110d0504021509030a0f240608011803020327060d051b03100326040602030711061606021303050f0c0909010b01080403 68
    0x91035000300540707015072401524403040804103c0c006100b40d40c5c2c0c100c01548000d01c5149003500e45003242d404555140101050503104800c1c8400080b140419038014041103002e000019964a5404140b4001480c042c0d030b080c0d026414900c0021240314500382101c105c014010010403861403a0341e06d42c0c2801051840c121042101d014100c601c91000d034111460000349010701040300307030500c144a801c440350380030b480641d80c40019a90020a801004541400e442225800c0c2c1c01e08900310100c000e0850541c0b080d40081e000154108200003a9000c1c500440042e07030a054141c03121502c03050707107020039601c0300700d80315040b03000700002400501450084143e49a0451032200380c0c2c030000880741c100764000c1000d070b0070000d03801040202d40402c044856000300e03400c5040c41c1030744282001a2901d210014001c560000784044020300502103a801160300c0400c403848403218110981c0c9961007000040d00415074140814080107042c0640c090320a01a560756520340d03565141121140315002e500745 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 691034694 1250 691033444 691033457
    0x90b040621020405090a080f0d02041d160c1707030e06040801061806031208130203121312020f0f120706050307080c09091b0c01090c0305210307030507 67
    0x5041a42100094410507000d0790040c803041c1c00380140829580020906200c0e50004144000000c228034140c03482c8000d0383c203045407a50f0b984d0034008004c0c030658002540e001c0c0b0225081445d2281d85020398440d10054100c0000c00e005e22509460f0480f280c0401400750007400d0f0200103099051028041f028001d01d00000c10314440e20200701e8030b50040c0c11180c0565101c500034042540300c001d03285804425190300308030051540d100c1c40d41002800018200304440c00c00861100100988034444041c2c00406440d1850090204d80010b40d002d82101d2800314050080001c080641406410050b0340180083c658030400130100160300c0c03000b0000c6640000302c4411161030803030401144028001c0364039003596905040d6000741100c00001d1100e8910482002051016142d1400300794101110b107031014900941e412020515008098214081d586404410030521483c250b02c503084a0141056904002110320404460301c0b00342d02901700700c0300410100c1e0105109038090341d44940d0614000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 691035944 1250 691034694 691034699
    0xd03020310030209090d021203090c09060d060c0305060f0109030203071202041503030507200d261305040621080c0102090a1215060f0e10091517070b0301090b0406 72
    0xa5400441a5844480790b0b00c16808842c0f11501004005d141d0760203a0b0f48c8074203526280c00d50302e0385d5540000070341d4000c4200001245094030342d29034800026a2000c414044828490301c0200104012614240f0079182c580d07100a40b5401b0704110800d594002e0094090303682440c4101c03d5850b42a14226045039a50710302a09032905450702801541c882d5072410b42e81d044504001c61245100003040074001c0541603650b150355a4106004a450380c0b1441320010030b030001030542d4403c05a04c0130589641c500190710740850f07e8903003c4505840c070884040042c151112a0001803070800b2100c0d10a025900d50081e010035104809041c00f00b990f400003614014150020407001c0e48aa802121030020074a114000c010f0b01c8100188a1107000c3c00401c0500d180188408501017030b441a146006003030000700750301036020080d0b2005000035030000d11821002c0c1e0010f01d4402d40500c640345090f00003415a41060a010072140106e9150022044c110303402d08540b00010400c80341c483d030f4080d5440c40e00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 691037194 1250 691035944 691035949
    0xa23070807060e0411030123060301080c1c080a1202040902040902091f1407150c09260a02040e030c150108010c090b030a050612060c04170f0d030203100302 69
    0x1400505040000341189924121028281c81c0d100394583d88501c0c10b1001505d1859108800e03641128000c40480111054014814200e00c42c1c00d58600e4200100000100d114040051000a09101507801098803c1030f1100d041c021682c800300105802e10030040001e10301d100e02c1c5840010884202c0040c07034190b403000300d00704980c0264420b002c11900420b1030680d92070100c1d906809001940542440780342003001c018411131000a280815140100703511080c450303031800c4290341260841041105103600780024001c04454450000090b066080d00c0340c0d8031001e11180401c031809500200581c0c03201e50f003088058868858000f201d03110a00c022551030b0800c000030302440e4110030000700194184941c19003920030504110042c1300c19610308000d0041410100d0307500002d00540050191140400602150700c40c14010b41c0c544592018401c000592030014070031140700281c04500300c4900405540c54030f01c40a452401900510b030303141c0405019400860303028040040480405480340e00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 691038444 1250 691037194 691037203
    0x4060506060408010f0f0c0c02030a0b0a201216080601211a12070605030f060a030f031106061c0201080a06050411120f01030c2903040516060906020a23 67
    0x500c1c85007031b510b41c103d000440e5400c1c03241d01d501d90210716104450b40015004a5503030403404400410310302c1a10f00140c00305915600c600403549442c0c01000200e036100300044107e412983e664846590303a4030100ea0b007154100c00c0c880031500c06441e00301c840ea0b500801520048110003602c402005032828092041441c2c1c030407a03810001d822540b46002074a0310500c010000d49644020a40d0301c245814480583c014040c1c030790040d11a541c5941c150b495502180700102141d00081c681d036080c0602c002050b400200600c1e02005000860358035943d039400b00700306030b0307003081507407041c209100744840140d4410400e9580c042c403086404204565074a010034104d400001d20009451008524070b01d80341c80c000d8080d0b8021201218009055045031075880c110740b0281300e11003000d812040c03d404c48004d0780248031500c1d1402030b1515264a80303414904d403a0401100c4c0c0450901e4229004985140940c11420036204164014103038102c09565180e0340c0b062204003615001c1c50070440000c001002c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 691039694 1250 691038444 691038461
    0x20309191104021603090f1a031305150106030506040c0804110a051e1203040609060f020c06030a0b10020a030f050702031f06170a0206070f11040e03090a0501030509060406050606040801 82
    0x704d00b903860140508008044514030b811140c07486c80000004c000200b1440c0d001c04c8400e10484445560b1303111550304025026004400404138042c0050300c100c41902c524030141210151384003401107a4641041104882c516850f01e0013086240300420046001d13820142e01c01d06000d4818102c039502c0d41c0001d000c41b808150150448881e8512034111400c14846054520900070029401c02c1c0c10030b41c019007444038070b02074101000785491000e0040d40c401c001c502300d10100608055078a0800580205c040d03e43c0d0105103016209034075880ca045440000c042203403541507600c149400400c030108480f288e00485041c0d91500c20403070301c41140b101c2010400c41802e003c21000070b80a1400e4001070303070340c61044007024050704440807860141c0c45120441d034065900c0b400c4d20030042940d00e402450034043d840740d075400c0380c600b8200d01040d440c0000200043c1c2c0d000c48000e00b000741d5134401101aa2401c44804000b50800404500020000d802a64118000620440c1840e488401007800c490a00d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 691040944 1250 691039694 691039717
    0x130b01020d022404060905100e0118020d0b040c030605090604060b0303130e0903090306010e18210a03021b0d031104030201050405060702040b090a060f12031d1c03030510050402030919110402 84
    0x102c9c210454020240300f5a044020400589018848031342c00255030440312483c094042c170b030502c000030100450f1034610b00146502510811680c18200141035594000321030403104240b8004081d8040c1c6000004d5444103001d521811058a0402e028035134400d0300a02020043d110170b00120000303540a0107140c1c00ba00c0c030100c442900707186c08400360120900c800304d0708005030000d00901e581c105280360342c1814515244007280e5a81c1c02e0510446c024400c8514103001c0610454607031050707807000f0035120400784540d5018800b14800350b0002500b40b080d4403000b400721300200400c215a00303110001e03082c2103000401c001080040d01000c159800780071076000000d2a030b152401c0c809074000d0302c9140c019283c250000d44900302d6955015220a00b10314210400d0f8070002c1c0c2603805641d4594501e500c0d0a01c40d062300700401314510f4003030701520044d00d2038140000b001c0008103ca050910070740313202d09900d00c0142161004a20b14415400380810305803003906e04551905056120f5000825000713407403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 691042194 1250 691040944 691040951
    0x31290c0f01090b10060504140117010b090306090d050904110f03010b04080601060302160b280c0909090807031202070219030b0a1506030c020c130b01020d02240406090510 75
    0x54079040f03000a0004020344008070755800f0501506a01100752811b403802a03a501c080e02900c50f0041c0d40808043d940b50b0440000080081500c8640c40041c00d100302c0c00b9021200a174032010348003911440695905c100089091020903014034243c0c200e200e070383c4000d94a491038254005044021a4400d8120f441f000c580000c3c2042607090400c201401800c1d2447c0071130511351600c80c81d11030043c41d040003400b42c5000102003060161700e03008110301d0f480030301480e5007003a690580346c4024106044442001c921540700004180149028000340c0035400703400c0318945041c9075000c1d540603482c507103068400c541c03e01c002c50050b240c0705900851051880030901a01d0715520748510000070050400c0b000d0390a10040410350500d40d008541521846e00740440c0c1c07240905400c031f01d46031101003880c1d84a81140340c0008824002d42c44500a488280e003502e0454a611509076542c0c3c500c11140c040800b410885a14441c60010701940c01038401c1c5000304450000e07444841c030308000c2000d120301240d507 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 691043444 1250 691042194 691042211
    0x1103070207060e090103020d06021b010c09090b030d030528091101020d09270203040804050906090412050904060b070b01080c0f030a0602030c090631290c0f01 70
    0x40400c4044010941c0d85050f12046040c2004100407004c107100003801151520704e2402000800d4042d1750200701309004003038541c03140040950280030300c0401e00c40031a44030000401d0415041c0991004040081c0080106881303004d001c9006140042241a8181114441c104050301601000c1990042c030100403402005905125903407106144000e0b0641d880309036407500440e0000e0f4000221885140d201180c194480032070b203c40080943c1001c81c0501c0002080304110392900504180c4405881500c800d0355a407050100100c07064a01400d0340e1503419141d002a489103005190600b4050000720b1641c1ea5070720402d429070040c5004841406607a80107100003c2d04011b2100140003c4030b841045404a5011035111030000f01c0103008a034002000410106c00f20b000c99442e8040a805582c0c0c40310b2036603020780c0c1c2d1519400b000d8210b22510b01c180058402c1e12201c01d082c1c0d04c101c0d14a848510010320790740e071070001b81440e541c007800b018041840c180e2028458480018405800030a120301c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 691044694 1250 691043444 691043447
    0x3020f060c0a0f0c020f030a0803090c04020901050d0203061801090c0e03010b0a0b03130804030b01030311030306090a0e0703080f090a09060b16060605031207060b090106020c0112020409110307 85
    0x1500030030381e407103800c070501002121540c050034615a559050801c0146041a8000f19401403a06a181c0c3e401d803142d91840c40810181100851260400d481074420b0300c0414404c10081e48a040701050000c1c0d421301c0a5050b6070015801160040d40c0180003010000c94044080c2c0c50b484240d004907541a507074011240340d550040140207499004900811504021a0000310301419901404030000c00c0800091410303000400c501a085801089041e1116601c0c90b0150b61b5140c24001140003810440e059402c060340001500d00500c001024400300c5d030b84045075135004001c00740081c01c1c80d00c19103800102042440c8010403410050704030065a424040b02440b040d15030070303482038800341d00e01a4100080c100d80420fa80d82051440d03602c00c00b00c102410104c003e0311954010581c103008580705241100500b500400c150b9201d0901485101c09200400c180700b04244910400340c0c1203490b0031103440d071180000700300252880c0c50040c10540c031345034450119092100303032403010ba5000081c03100741d5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 691045944 1250 691044694 691044703
    0xb01060806011206050603161209050f1204030b010905191a040b0607020d0605090a120302030a060b160314120a0501170601081504020a0e0a091104060305151509010303020f 76
    0x30f007280b00138003680b4075141c0804c0c00f0b8170000344451201590704606200da241b04d80320041012041c0c2e07000340980703079044c140a92140040d1081c102d145c8140403900c0410b0500d182600c2c2100d0700058403041c140e2034040a10050800240076102007800748121000706140c42c881e003c05a1010300b802c3c220050b07142c0070b01045601c100c980038491841844040d0069603441079286006a12100100c2c00f9102d20346203518080c1c6e5184010029480035049008586d0300d980554440d1026040c2480455510001d0384403c0c4507640b910510450b9860354a00440d021300070081c1c181c81400c1c0c075180f0b0f0000139100802e42400c01e4404201180d120001001803000e140a5044425a8000588215490071621650310406001420b042a4800c0c000405569071404d50400a10012001c0380641c5031a10011004081c882000c5030310b0300f8040000002400c161284c1400d4981c40002840819070302103004c0240c0303c0c010426410089401e0501c04c0c251501c00e03880e030085201c0e0700140800b150a501c0306041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 691047194 1250 691045944 691045967
    0x40b12160309050a060c020703081b060f090d0c020118030501020d050105030c0603072a0308180102340c0b03040b070503060d080306030f0102040b07030e06040609050108130b0106080601 82
    0x401d410028200041040030402d2041d0560002000410300d004c24401d07800c20742e0581c0050191034000c00c080c803550030443c0315031640e840c04d0025200c859076040b084290800064a404103e6440740015070307292400380b9001d60030300707005050a081d40e003138514903001d5540041d00100e070581d4000c15110361142c0580600c034003400044015000f404180004505e403804000c0070306041120f030000d0b545051907083d06484070061680d0281c900740387d03181005029018260762140c9081c90b000c0072031580306010310a0f114503018030b0800360754540e010461140210700c0c0e11031400a40e45c00a09850006407101856402010b0f01d018079501ca1400d4144605c0090000b05410300707104003082001050303501d01c001008005d60040842d61070740c80b4100480d1070130003110661000b0303610008002c80c90316071000162003224401e664018400c1800000d10000d03014070700c60b000104618040c10f019540c0103c2d011603000c4c030410310010444055450300340c0c100d4070a0340b0000200d1007620130f004641d64001003c412 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 691048444 1250 691047194 691047197
    0x11041a0f04020f070b07090302040c1707111b0f0406080a0318030b0a05040609151b020102041409090a1205040317070f02040b040204080708030301090c0206010806060d0602040b1216 80
    0x4009082d43d10781c003c0c0c0704489004090840c2a00040c000d030340680b4a107005140c0281080059201c6c204010740002e82520009810700138a40c005000c0302e01c64903114441c0d206041c00760417222002c40420100e405d0446803030354080d04083d412003031501c170707841204018a1a500148103a84560134003a0006c040c440001e0045400007800344041200c03200368540013003025000140c40d5486050520050410a030020b00002d030540030201c00c40900e41100d40441007400c04e1060b00351120009a080384aa846150804901c02a8880c0036207402d8600d1a84040c0c07400c1500d01807a011356400e502c010b4205040340109130042070900500040c03061085c80f40b2410900e40d40b07003100e580c45040c0320300c100b02c0c4002c2c42503441e104002c4164845405450040c0207500445845139216420700b82c9031f03002400f507003981702c1c0340c5500205164400070380303507040b1200f4002501c41c546600062083c031917000038090f900d15030200400101554540000e10528144044c1180785e07042416440082903417643d103100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 691049694 1250 691048444 691048447
    0xc011a0607050c1e1c0507081f090f020d030f090b040b030f04082208060a0b090c0708040e070c12020111090f0409080f071b120f11041a0f0402 63
    0x800900b00090800e00600203c4103ca2030070440d4030724000066103810800c1e00401d146101d0381c004402e40100006103071140e829a84101e89912045d9a00c200c500a1f02020048074181c583d0550816403002c030516000d603414201c45406030300443c9025050003400c60000f004c541c4088065644103a0100290401c0c0208619081c039000c1c15076680d0001034100c08407500c50030042401c00039000e08030340d92441142030401a420308200c0e13054543c01c0700d01c200500c41c095100041d160040501c03460705040740003032141d0721646490151a0650b003000f0401c03681c490303081201045c03402c50f5440c468440c0c4255620010740c210180b5001419085425060055a06004140740f42e92031400c00d480e40317501c081c0da180400303000b03403400138000c1c0c810354101404000c00011306400302c14440c402002c40d140561492a104a0001e00200c07841e800c0d441005501d001026164000441001d40800894007868180c401c4240490005040f2541c000a4190340500f080c40111141810441c1001a01040342c3c00c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 691050944 1250 691049694 691049707
    0x50c040513021606060b18060c030417011e0e0c040e0607030209130f140115080c071a1603061d01141813210c02190503030c011a06 58
    0x9041e02100072036108001e0300410040707041140101c00045150b00084280304c1d41c0e5413403041c00070b1940504600b450480704281180590b041030340c21101501640002149041e2400c00001c02c00d48026035a03040039501c0c3c428542020309800480040002502c9000031900e001c0c5004500d410b842c1c101e0705010700d060040a061a01011030720b00e6108100d410b016030f0341c2c0005030015000700a525142c145c1503107000e41c02480400b0590090342512154640e400380b50b42c130b40e842807000c075142c03580d0000000c0d400c900040361030701039002501030340d481024eca050b1034144c8500c00300461700c112400c0c0e40d200d540c0d0b40010030381c59140c082c41c0c0090040e11001c01840c4043c070085a10342c0c1d41402036111140415200705520745480918070002d907010700d06104181002c604002c04503050000540b00380d600001c5e4000c8401205603401d038001780c16207820440708400e500f400203000300100031842288007800c00060355101440200074000b08900001000300b2281280b142c04c4071110300725401800c003444213 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 691052194 1250 691050944 691050949
    0x30a0b160e0906030d080603070801050a02040801052211040b04050a0c03230f070908030c0f070f080c1915020c0310050405120d0605040e10270809060724050c0405 72
    0x540c0528117461070b00c0328070b9030384880109192000c41d1f071228142d50310b010204503031051a54003402c1503c0c03100307009016540764810030904118403e02900503107150b418004000400d8205040038018001e400414031080c594001400c40c0c0c0308854640c00c071230711082c0c0c1c8100184c0c54480e00b11402142c0213680101c1e5030f2040740b07901100004200114103400b06000c154000c0c01070740f0541c001c04290007142e07900c803035481c40c4680f0740200c0784500e0361911031200c010a41044448840e81521101c500400c601040001080143c407044460062a04094900458601c8151040981402641e0010716028021406140c544a041e007100c40c0020b1501050100145002c5201c179216900740c00d1030307a01e031070b8031807090001084281d110030b1b403080c6400510302d407c082c04980d205a225040300104020500201400107a014a07125000d803058420120300001e020704016184030030b000743c549802c0412644d41e07015620314404120007400e0280400c20768042c05030061640c0043c1c0c036190a400c20745040c01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 691053444 1250 691052194 691052203
    0x1309060f052e1d01020a15021b0d051e0f09101124180c1005070c030b0603060709060807050d0912050c070b0405031506030a0b160e090603 61
    0x2641d4426088901080100c2c1c0311a420080380c2002401500000c4040e044080c081c18080380c1c0301d100749004401046450b60000c203141d076131260850105250034a610000500a40c04000a1200c14420079080c4210340c1c810003100b0344001d00f60701c1d40d6546244000b0100c0d107544c000c4141c00790303100040144e41c0c039580947d400d441c00c402c02038440d45002d0136080c1041d030b1081302178041d1401d14071400d04207034804900c01c802d184281180c02204c0c41d5540f1b40718a01441c820f08000c6107101540040c0c44001e150a1411000814604502d446030414a4968950411101d42d501c01e40e072540212040c050985000d0102903045030341410403a030018500705014200c400014256800c0c0304011401d60b00d07242054101c880880ea000c11402d10501003140d0162654001010b070040078400d0807008148080341404440950304000c0007001d0407035503029400c0c1c1c8800010107194140c040d5000450001d0301c1200390500545808106c4080c0d4400c03040010400468203025504c148050b1043c004203031008079 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 691054694 1250 691053444 691053449
    0x10614030a06020a0912050c1e0a0612110313030201060f1508060a12060f230f18100b01031a0105030f0403020f15090705010e060f160f081309060f 65
    0x800150304c2e01c098013804e130340c42d0155038048030781c2d0088013100c0c2e000c01c5000300340c039201000100c0d01100a0b108200301c2c5000340030220402070f080f0f23081c144240304070f034005c585001c0c2e04201d420000c181b14032004420025500300380c0c1e00a2030b581451494204043d0280943d0f00945400303c803100c0c499181681d081507159020b0b00700010310114002040c080c3c1c4988440384041d0034600c2081c0c158100350320340304c0004d2040300203502c1080c3c50440d01204a03540d075204401c0000c4034142045c0251119864481031301c2000e40440c00c1e40d28038814509001070140181045002851400104440400d00143c280c0b0340e90031034034114281080300c68480380c0c0c000007540d821403001c00b481d04040c1e9403441c0c01d03403510164101441c0b140c4100d1040000302e842090f940e5100b25200401d41d16101c1d5640d0041d65a141141c0c21254004402d0040703064007085e0030042c01341c02004a401c84903035420343d25204071100f1040810b50340e6090000b186c100316040c1c480320030014604848100145450410312107100b03102ca0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 691055944 1250 691054694 691054703
    0x314090f100c030617031809010b0a18030f050a0b01090b1507020411032d13020913020d1203150819020f042406031b14070501050c03010503010614030a 67
    0x848942d28010f100e6130000e40600b10541446800680f0340d980b055982d00704030b01e1000084081c048540381c60170401800c07812580b010043c40d0402c10343c0d10066581840001200345490380740c900c00400724800d880d420240c1030240004e41204c07111070600101000d4142c214016103800c18016082c951186900140c00054800c02d06841c2c44083c40054083c1c041c0c400701040e019404810700205a0000342184540441181c0788000140035150f00d00b048072080302c1d5000004541a003080140c2800c0c908980d1007001041c640b80700d80210b50001d4641c6001c0c01003524203689901c1c0303e046c290b400d0710451410200d80c800407064249400330441e40c1b20182440d40107c074102410308021901c408000100d0480001c00c00d20030340c2c0800403004002600001ca04034000c003c0c4a0000d8918003d12403080401c1c0c440200d034081c05017425050307441110b8058003452815082001380e010600070701c9054080c2074800109940d82d4903003000c141c203481494000f5481000d00310f40100c0150340010b100c0328001d902 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 691057194 1250 691055944 691055951
    0x6090c10020a0c0605040f050306040f06021c05070c020a06020c030a0204270807061107083405010501050a1e030b0c07050a11130203010513200403030314090f10 71
    0x180d4040381010300c1007000501020680b0004643c0a4105001d001a5003007541c900c20300ca640c803820196581016600a0b02802c40c003400e100201c0d5030398005004009403200035445083c02c10300d100d400c448084a441f40040d1640b0540300c1186071000741880100450700c0144051000301001030b0302d501c00080f00074400c0e542c460040d1603100d450396102c010149117a248400c0c014588c00c10004542c17007c0d10840d113840c40d202110b07420301500400e42d0a65500700e401d072800c1036604000400c14852032540c000c4200d09443c02001000368105070769020620031340012030320303503d0718050180003562908582902c1c1007610118500100705040002166001215141182c644102c880c2c542d06c40c41c1d2003d0094014000319030144051001102c03a03140d0180d5200704070800d402114002ca010030301800b644007400420380c0c0c3c280311107904002030030b11001c80924881e94040c00781210aa01543c41140404e0311039503101207408400c00780345c0e4042000c101600e4020b1032004074545600040c0e0414071020754 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 691058444 1250 691057194 691057219
    0x8030c011a1f0c110307080a05060f0f040f0312060909060501080d120f060f080a050705030604030c060911090907080705030f0307170f07060605040f060b030106030c050913091406090c 81
    0x3400c401444c0d50752000383c02e4488840d21030b040e56446203c1d00005803124490840809d044d4507804251912800f540800c440954965643e54042884598000e0741000300000c860b414412042c800da42c000d00e0700c0c1100081c0b00395a40380060030f443c0d050303008041c280c004511408803d41c000c0b8004007030300c0b41f0001c0002c01a80c1c0949044c01880650400d410390410481c01284201f00004c00d4103071580144110f460465455041680d0341e0742c100e0300100010001c100f0390000401c00d411a5030714500c070b000c051700c0d001e0781540811308070501103071a5903069001da08100805141030084501501081d0003609480c281c0c12121960703840b842c9001405d07040e2a0040380c40c43d4001d0f0050340c020002003129203650302c0c810300f01800a0029405010320a603d0001030300c0019502e803154100f00ea246048160440c0e1030300100b0b6005100005010041c000304000c4d80200b596000c4401c02403107103a5000040c08849410003064108040b80c12940c20f90124090101082c0002071203202000c080722051001603 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 691059694 1250 691058444 691058453
    0xb060a111504050303040506011401020c060a031d03041d060a050d020109030807080915030405060403050a1b08040602010c1b08070f1e020910031e06020408030c011a1f0c 75
    0x1800000c808a1440c07003035051108100c0044002c5000e2030003107048030920303601c2d054802e401c940c0400c4446c1c0503030321200c2e1860070703400c0c940050460301346903040c0051841c103010300d45403114503101c003010b60740e400c00078061100100d00c1002c6a4000700340b5022201c01c1c0b9140010481612803070040d10310800c91102c40e0411a8030585034540510f9011401d03607215012032510b040d040c1c12400d0300922801014450790034004041c41a24411a0000020142500e55840c1030350f895002060b1f920030410b1203490440700403990a0149551481a0a880c0d6164038101c0001d0131501090071503000c0140510781c2c0480640d240101c00581604991480d940300400e1400d080d5040300450000c04910214001c116441651028285801d000390380f109030560f110f81c150400780040d404024014603ca0b03004581074461407084100d00f0b445960018601901d4090051030341d00700a01c0b070a484e0303440e000c8555000111a01d40b600c07400081d1400341100025070300d10906000c07440441801c00c000f00c0c49460510 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 691060944 1250 691059694 691059703
    0x30a08070f0c060908100b0f101817060a020a020703030e0f270603030a0f1b0506040506090c0a0608070305070e060d0c0305130f0b1e1014040b060a11 66
    0x15500940181c1d0203940c80f40003800018503482403400078041c00c00384060380d0100c0d0040c9140c0c0a002421110403041c12001c011101c508014000100010840c50400c000c2c3c03a41858006042686140c3d03140340c0707900100c40d180040080c11381502c14010f10a440d001a0005103103020340e03505013404005084024003090070040c45603040f0740d00a840200c5a500c071140c00c01d941584110b0507044540b01d43c0e4810070315540f4031800041c0c0b4001004000340d0b10095100f024040280070f03080141c004403078296202c0c9490700e28140c038143c44079000031050155041081100054101c02076a0342210346183c4100500005001414a01031640f01d000207007110b4030800080e03104000c028003071903d84c1038205800009000e601c1501010a1901000c95001c0c071711100d00c44403c1e40d10200034140d55000d55200c0c01d5a00001d0b02c0d0b02400000641c0d90891302c001c01400d84e10490340c01c01d810348198646918a07071006001102c0d03501803842c0c0f011091464440c002150000100c40c289020071558001129141 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 691062194 1250 691060944 691060973
    0x4021011060411030c0a0612020a0e04051e091f0e0321100504090c0501140c0d0f08070503040b0105090c0705060c0a080f0f01090f0902120d0f02010209030a0807 71
    0xa015080030401081405090403d00714030650466071031140341c5045c002c0200141c000c090200309884e00b041d0407000e0035001841d90041c1840c22201601810300824180c0700d06503064140100c010303a48000401c0203104890340300800380003e0607c85514000b510f60b81158000c4140b100d034407507a408800300320070011aa44404843d461070390450300100c074a41d0700f040a445285540c40c080d000041d1071f00e058090003000c0350b04603503280200d62420b4010341e0402489003092204900500c040003400c41c0034070030f03000c000c103058a076110030a1b02e03108001c1400314014036a4060040a006210200d4601c420fa00c0c1503401c05e844240f120748607145d15100c18010120000c10f02d120f01c0041000f0151210054940307458282c68103601501d03203c02d625600d80045400c01c0340e40c18490010020710149400c0400d4142c0070300800627101c951a004205440300384003910469071b00040d00403190507440100c05d0040c800c50310003141807440b5280061780310511040c01524003070010a100b0240304900c1408880c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 691063444 1250 691062194 691062227
    0x3070c020d1202060109110a0e092205030405100c05061b0408030d2a0831060509061005030d11030c1c03111908100509070e1207060503040210 63
    0x2c08044034000960740c1c4400d0040501d2142030001c92006030030700005a900306200b60726004c0c01c1c01884414842c11500c020002e003c00a040300400c034140010302c19180c503d5008030301542c1d84602342406c1c4810181400c210008200c8464404c02c046140441c403503821840c81c0d141e075040020b908040c03807640c1c0203d800983c043d010001d0180080e040c1940302c45085a85c5000d42c03040b000119482c2003a0080702c204031804646a0000158070486001c0050502c80b0603071025000300b541460300092141407024104c0359030f03555006100c82d20301c0070031545600c107000c18421440c10f4109008240c80d00c004400150600c050200c4403456003805100780e4040b001e1050803038400b5030078980800506e441d290340714004203103001070180c0c070700e5443d0041720900f8000d179002c12240c80034520100e0300c010004028010600c5410408030b519607540c100d2901840c1c15580303c0d0804550760040003020000104034004550000004000e01d17500501943d5000c4d40450350417050b08414841511341d0726036000c800c1c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 691064694 1250 691063444 691063463
    0xf2901020a0f0803060a1701020a0e0a060c0b0c191d0409050d050a110a03030b091006020c010804060b090906010603060509060306010b09030a0b010e010f08160b0d06180218060a0503070c020d 84
    0x4042055015145050310be41d5040001382c1034400b40018074056000320800036408160550101d40b149090a8012010b03052071403803d400d8810b0f00d103000c0b414880c0d1000103510300b100d0b02c21031030313080c2800c16601e602260100035140301031b51f41690719041d01d0300c04001d20101207090300040340202003411100943c00c0554094200f20301d402401000080d403114803a030781901c0822600340c1c0b1010100d0644075140c0052542c5a440001034400c0d20b802807040f99071039200e415641d0710b5111210b541d07016440e8100184103650412001800b500d00d140c110a009034200c204120140e900007a603141120260801140c2e685024804241482032208024107d000f0b00c00000844400200d0300e141200c01d4020089003070b5440c1e03403000b40c482621048034135000100c2c000501a1100c0040142a10341c60f0b141e001405560745c1c1d0822030399911600136442c24a5011a0f9280400550103e4000100c0103c8541c0d142c8030107100e000e0141d0101a00d50010807080d02c000f4011904d07250b607810110380d0400c10b440c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 691065944 1250 691064694 691064729
    0x509010207051e130903140f030103060506060403080712020f0a03080a0207081e0a020d03020306030a020f04023907060804060213030212030c01150807030303050a0f2901020a0f0803060a 82
    0xc00540f104060480007d099a29020b8608031104c040d200d0920a03904204e1559185850b00ca014007000f51a89921031020031000000480040c014503001d031290860380c1c00c0d0841c0b180e0280c10040402c114440036001145c5140c0025801962980e10078a210700042c0ca03aa99420401400d000e46020400003080f4540100000c2c40c0c42006010000d2055080b28000040407004400342c1c001521425010307800b004054005180002038448005070142005003003064111220800c0070310741595021501c00403145c44440304000b2180f21f80042707440e00411459103040c000402407040100040c0000e503020a007040d811170810f22400007190004c0c100792a001d400058a0b40f25803101142c038031158a000c164402c901d19016a503000c030342c4d00101800300a455910203a01500c0d0051a6411071a50351880d10780d114103601c02c0600700750708904800b100314200202c41d0000341d10203107003e065500020041000070032000320036290079032209445899407110000315150b01d4041e04801c0420000310800c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 691067194 1250 691065944 691065979
    0x170c0403080c3a031802031605010806090108061f050607120e10050406030b0612010e01181404060f0e100b040c0c050c010818031210060509010207051e 67
    0x404000b90b43c00c028854640001030650300285143d600000d282010060440a4842c0254044449405091002600782500780e00090420101c1d840c0c0007807140880b841444a540d1255280394481000da607011200e5044c00700c5244d846070002d022010b000401201c001c505650300001740010000684640e45698603840c12000c8080701e201c1040000c1d8000c0b088100c6803070100707191610a0f415486980c6041d08122044003e016070707526460704000104444c0008201592842e4020410b4410710b00c0154100166a9010071030f055003202c800342030680200c2105070200fa61a0400c1d8032540c0010104d070010a030601610400e05c4113441c9010320f0007075100c520703110b4002c00c80e000011181000300400034030f01914500c90040c800f4082e50302c04c0b401c001095001d81011900107440040358160a215005024607591148451909130740640041c85071b90410040d0520140c681800c1540c01d10240000003550741e02503203e01d0740f080210b0140b014804644802907005100050800d4103800311620f0f6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 691068444 1250 691067194 691067203
    0xc08071115180906040e060109091406090d12110a09090b030313170a05060115030f11070b040314130e0c04050a090906110a0f0e060a170c0403080c 65
    0x529802076441d40242a1803184500480e50220750000d80c002820080030305121650000900035500a60350364051440480b040000a00a01c01032002142990541c030305085400307811807100700c1950220041c080076402c00b08200702d15444501d48050110092200d000141040c840320944030f51001498440179540501010b007074130146001484100f440300189a624850b0000009156401480c140801e28400c2c007002d40d20120076044540509041e1903080c241b10080e840001081c00070310080030501e4040c00781c000b03110f00d200c00c204018000041101c0c400d2003110700040403940c81b2000201014007800e5281c903040401d190103500e0f0661400c0c6122054924007070751150750f01610000d601000c841c000c0760280c0340060302c4a01c0310381c42d000300803010b0301c603200f011550507850b84181d041d58598007028240200c1107588224199111500107000f10910303603034040c00780e5002c0201d0101c2e1a00280300c006125007400071a03030380b60307205030a5102038040c540004010002c0041c402c02040300005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 691069694 1250 691068444 691068473
    0xa2004230904060c0f0203040b0a0e040e0105070f0311090f0d020112051f0e0114100e0319140c0603071b02060c0a0b010602010c020c01050705031209010f0c05030c0412030c0807 78
    0x495407021000440802d0347d880c0102d01ca0310700310010410820a043d4450500f03000c6280d0081c1c804502001c060104509444040b0340b81303030001c1c0580060840042e0b2600540010420b400b06561420310b218012505191445110600460031444010304592140200f40c100f015050010040c908007002c400100440900c0800d00460165001003004921140b10604030380004103503414405049052201401c2d00b40005000e0142d0b03103000d101c2a441c01e100b42401c0042c050b04002078800549420000511031048043d910b6014001c1031010383c64600444e03801c2031490a00800d0880d243c0e858208a03c00040025000300b00415100c040100c0000c07c2032000b44280f01303481c4107071f8907960102d088400c403800a40040c0d10081d03003000380b0b50040005202c2e0034003031401e9034a000c610b111211100a03064842e80a940c0d9605241076106400344100d48001c412854034501c0c40c10111015001d500850191100c48485440728504043c0100100d506103036000c24a961150b4070b07410841c41c0080d40c0c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 691070944 1250 691069694 691069697
    0x30c1b03110f060322030210020c010903030f02031017160b0a1b050304030206030a02191e17010509130b040f110a0608160201020c010f02030a2004230904060c 70
    0x3003416552468031106480c0300d40178406201040c1d456040d5500d505080d042019001d5000e072510200b256074560006102c80c140800000c1404110741c9030050456982c95941024280f045c0144005500154040301c11030700e90044041451201e8a42c0b5410452020034441e6640001034002403c401c0602c007400e4010410340b0303103001e501e0710089070b02102c1e80d00c600700030196001004140014075010000d0350b085010840c0050500c021200c1c00c400705180c0180710170100791a1a50303000180301380392000709035102500d82100c0608003883e005a6201060003868450049180010905040c1ea10300c501c1054101e2410061030520b030030040a01950a0400e6850202d004400d4015040c0b81c031400c4102d955990700c61b603441d6a1043d6038050030700c1400c0c2410840d5000c00c50409016001d00510090343c07044000107949050402d88541242d4002031303220740c50050b840924003004003800a89040f904440f241c000709800184401d120301c034a00e41d5050384545224248000d008a683c0101512820b6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 691072194 1250 691070944 691070959
    0x13060e0a1109060406030f0219021510050f0607262113030c030e060a18051f080405011107080d0c0206062d1807090f060804030c1b0311 60
    0x1005070150244100020030360031900800080103c0d074881c2e8003d8000c51000c4600500309161140140381c0060360f14101030040c0c4c0180c00c2440030741c50780c20321642c0099001c1d840080082c58a4003086c0c00f0307020700b02041d200345c1012508000f408603407819528840f2001034032400c100000e0300d0780c05003a005010401400d00b20b0241c46000781c0c0c01c025240d0300076001010b07820301d801000d41c0c045408030001c0104404210310900c085200d80c0300c02000d0a09614507445038030390300c1c400a109890411440d88404d00c0784d080140014180301047c401000421618901400907595504215014260404503007110b07041c0060b00c2c00a004442c00544024410508140f10321264803200320b0383c55006496030790b408001401035415045207139940d00a00001d00300600903002110700040e844a511078220180c1c0c0e00d40d401001440e9504c00301000203081d00012180d078040c01e1440003400d8030760040000b014810304168120070710100c000e20980c0120046079141400c1d1b1203142001c6050f4541008034000c070b41 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 691073444 1250 691072194 691072211
    0x3010930030b0901090509010902090a0c0f02190201110f0712060c030203040b0f072003030403091205060a021e0a0908060a1a0f04180b010311040504080d0b13060e0a 73
    0x11a0280c42e074103000c002c121062076402c01403600000c0c4000340600016658551545005895410381c261241100940002e030352800300d0006010307011074101040441d000078000050450701c0794580070301d0035020b1909080484942040c5807030b012000c1180a800d01c511800055101d007005007440080d40700d404144208010010241c0907400280d40c018101f10f40c410002d821265010b0541ea4403100601e03110200c089c0e00c15803010640e004082e03001e060342000007003105240d0490b50703040061070000e0b2410064440c9444080d107591000e01a003402039000600c00802d02180720010b41a18071840526a4801d0040c07000b83c4540128824896035005050004800c1c80c1c00380b04901d549070300f0401d420312407003c140800c442e081c03100c03200c1c5521075541e640d500d030413240315a100240180715900da01c00a5065007030048443c0306650790300e4842c81c00d120410000600c8103080c1d80144025240200740071460b20b0006451600c8501020000c2d854000005030300c2020300c013264010108404200300468 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 691074694 1250 691073444 691073447
    0x91109010c03110c0d0f2001142206020303310f0503040e1e06220b1f030b040b040b090412051303080910020f0c060903010930 56
    0x519244103020075003890780741c0042401110b10030a01074420054440d443c00b40c80000e00e2500510301c00307895900043d100401048000c0c58206034903161a40503582521114000a08800310306240c801c4102d00818690120350040e103441d00c10304241d420301030b6440d46039071009503290401ca81840c515440082038641c9501041c6c5226101900300003182c2511f15680c80c5e50481c001d85140403034003440708200000d1826401042d0b14011120b03580c802d40301030403014500c0d440c050080d0100744240141c45c0e00f40884002a2803141109031b80907008035840030044009807104109151100c40a801c40f840840d00d83c0d810b0f40308040300d10044404100d4407070658288011510751100054000000d880880c1c08601a00038410401049241c040c0c07400c2000c4044001c1d549596004440e25403002c150400703e45001c1e100000f400c41244010050401a0340c019a603451100f81603e028600001306200280c41c207401c244641c50304005032070718070001c04c18040066100210398610020005c41d00440c043d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 691075944 1250 691074694 691074697
    0x61d060a0503030a05070804090213030521090f030a0b0711010c05090a0e1b0c070e0105010e090a020a0201090f05160510020c1e040c0f09050d02031b0a120b010911 72
    0x201d101400842c10208001000d403070b6548061800c4c0d807901c605200029400c81c80f8001492006244450142400d1441c50185c0c80d03d18050381c900501c400b0030301c850001c1d400140030b0342c4140c40e080f580c00031801806000702e4180740e164500500740c20002002c000f080b03600040031000c0d000e1144001c00010210202c1200c0600504509a0340701200042c00c003c074a03003c41049410080b401c6001c0c3c1c203054560b0040e0702aa02c801040102c0da00019020002401c42c041c02d14010301d0300b82019a49840c00000064050b41c0041c0300864240d40810588205403007580301000b42c942c81200c0540c90201400c100d0351714040c01422210070a810000460301d4146202100040801a0000c00340d04641c0000c2044200c0311803140510b0840381c00f028400c0d9941c601800b03005503010745071180002c0000000406d510a5900020700446200c100980180c90000d402c0c1c840780240b2500c1013070035075144000b41e10008541d229803074482d0101c6410081c0607440c1a120b040301c00e81c11003041086510700030041030303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 691077194 1250 691075944 691075949
    0x1f020307240c1701140f100207050910030b0a0501080a0f06020d1104051026190606050c06010510091806091e0b030a03090506030a0f0c120b04062105010b04061d060a 73
    0x6c0703408500c1c10300a0034110072000c6204006d00688441940300d60105281c90000c40f05c0c0403072000342c181c0804c10b00088401c0c040e0800341c0403034144030030360408042c00c0e40c0380c049010040103801c41e00800014401c40382c1c1501c0e90701082040500c861401c02841000582150260a106090094268049502440c64803a0703000c03d03a0128826580040381035040034800074150701c1c150000c2070140d8020381c0c140c8a110058582c1c0d880c2c0c2502e0f0100c0020561811a05800c9103001c1d0011141c5144826084100c410444500d1410303280002d420000c084013070036655011407805030400071040d03d5240400106079660010010030010244030b0000c244d0740d40c4440d040035020030104003040c447e90800c10021035110210304008500000310098100460b80d0781800300c0c000586804500c9641c0c21719002d05402c0484c03c40c1c0c18482d10b4100003a454030494102c0e02d044e0800b240903903640c1013010030340125200b114000c0003004040e030703140b0075000f8440403102103c0b00c100d089000140e541c0b81c010081000d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 691078444 1250 691077194 691077199
    0x15030905010e0307240e060a0504120c0c142d011b12050a020c0a090b0109060315050f180405060103030806030d09030201030f091403091f020307240c170114 69
    0x1d41c4c41000540c24172a00941007600007507034803215000200034003041020b010b40e090201c00201458130703007040310060b20204502400c0000390400c12020481c8078040101b030300c42e41071030184186041000600b21055510381d03070b1986090240a030b901c41018220186520f5400c0e00e035a55080121a951340360b884004500404458a445900e0402d80c4903074081c00c42c0b10120b0040b1403280303001c000001c4d03d200195100c8507a082d00d5000e000801d50f480f009410040c00300e4102800600845410503c0405007405a18050800716000c5496652200040070310302000071603072013060030a81005511a80240030944c007082c0380d880440d00301d05001482c0060756000381e540034801030640e40110041c160030015055440d03203070922000070804980b9400407100501004554070b04204081c02842004003400045041c94800703c5004641c000c000c4402d8294041c4c8211002000041a4080403103140f040d0881c003440d0030007043c2440c4d00940111140d00446071050f80316030f0303101403110034a4008151140c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 691079694 1250 691078444 691078463
    0x30e25170d05030618090604170c07051203120906090606010f120c0908010e0106080105090703020a0605090402070602040618090501080a140a050a15061d1f15030905010e0307 77
    0xd01d2107106401440e0400401002585205002801c0d4031220074295a41c00958000d20240400c0041641c40c05240d402083d4045060241100c0440c1e222701c03072840742c14000c240d10706010308c2c945000d108407964010b5a910a0b4140d04040b200c4a40c1d41004490201e90381c800d00010600660040c441c250040c8035503074403400031200c0003400c40050403d0250303040078400300e08004506418280904460250b00400006919142c003010b2429104050900b2a0b9600249024001358503076001d10810b4880c20300f4503a40d10310850002c6402403198a0014010760720215002c11040d500c034074031b407100d0035013038001024058490b501c42046450a00c6450b64952008100c40002580c2d0421480c00d04c03404001d0b90308900003600e0b0a0304140416800300c03052001e6903c803000a122a101d40030140030410a45004046800c00c81c0c0490742010b41401100035170500c01c032a0542e00d5012101c00381200540203c112000100060003500d8503c50403078455090000b0030100700c03000010341d44485c2d0000d4898 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 691080944 1250 691079694 691079713
    0xf150901090b010201060305011b0215060f09041a241219020103060f09061701020c03090108150a0311030d0e0d0204090206040308070b011401020604120807030e2517 73
    0x40c0e00402d4100c00040c1075540310307103002020070030a2107012040b5211b201580e10401d00c0540007406d1001d0340d10130501601c16541480240d849841d08d5000000d0b0543e01c02030541c42d1418803041c900d800740c20350070301c100c0010104000f103040300003002c1c05845050001c2058090320000c1004c0480d03000c001031407540c0414246401c448c1070b40d00c40c604950040c1070028040d41c50700300030503a00b00d8030380000d02c215450b590200070610030f03221121128000c42e4004c41c01c0450040000f80c80f84a1058540e0400100c203010034608410b0303001c030b039141c80002030030b11501d41e58924007030080d032906501691183c020345200f00c540a01540b545052040003d1051201c0681d680c2080000d254141090342c1200c030501000c40000c0c0402c000b0540c41c0c0c01501851300a62500b6286902204100760007411908540184800950200078400e94071032582000d403100d5860743c1c0304600030095844980d840d485481c180411400382503071840d203150f401c0c900c05006203031151210440c80b04018031450301c41d070000740c4a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 691082194 1250 691080944 691080959
    0xf03120207200109050303130e0c0703050a0c14060403020105040318030b0105240a0c02030c0d0b0622020f07120c05030406030923010209040f1802060705010b0d05060f150901 77
    0x2c4248058141070034614562101d000c68519042400d0041e078481c6c910303400340036860707481c1413455004480360316a515240c4076a80080c200c1c0582c1100005004050000c001001180d0124031442c0011504980040c130309814001d000c0c10060390f00b90b011804000e1244008800107220b00300740c0303400109409c1e080c0d1a01050004c50010f1800048414815200020084000340014a68003242d9996500322059500405062403a1250300d44d2140c8101c42034a0000340c91140183d0780100110f036100384254550850004001c02c00c40c02c814218800170b290f0501100f9140549411802a00c1c03020740100300310810345142c054500c1c00b41560f8003d004c1002918481c2c0c0010864922426058522011040e8a400c2e200c2c3e65400b03401069401103607a03e217604061040b2428501c3d07080e814003003a103241c803440d800400c0310700f400380c0200e00000b449002d01109410420068501416220500c4103508101e0f884101c15105102c0850140010070104404003000302c03061140100390705210b0340380004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 691083444 1250 691082194 691082243
    0x9080a0e1525050114042102060403200703060608033402060a0309061508150f0123090705120a05010b03060622080115050105030c120705070b01030f03120207 70
    0x1c41e26503407170300d80d1146120001012180118400e8110071019034008002111081945102808640c480f0b800c1101007540201e0403070340d032804050380c0c164148084680c54142521504094890350501d01c0c0003500c5c00c400002040c0ea002441d840400d80b9040020b55010001c5080f0344241001a03800d06030090b14100c00203221003141818002040d0700169180415225802640c0c0c00080565071304100d044018084011001041503a0040c01c0c9013040c5007c1d010751042c056046c406c4511000e200281c2c0c504190515544001045081207103401c0360005c00e00c3e8451503e00d0705002e00c0c100070030400c024134042c0078141d8030456a41b604558601050005540080e05603280000201100e07000d0302e000c080207000541240000032802c9c0903600710300d9401101c59031001341048410402c110180440d14180c07205c45020040c14401916140b40032103076802409006011800e11400000401600950007001c0900c0b07501c484842c00d4419810780201e014000300680090030700e480001c501060fa94 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 691084694 1250 691083444 691083517
    0xd080f03100e070203030a050603030a140306010c0c0801051602061302190504090528170c03041a04090c05040e060f010210090501050907050604062109080a0e15 71
    0x841c0e54440035a1000d140256001c103603041c2000d60030010621042008500402e94880c0c400e40082d0b10349400c0403c01894031080800341040e03c5004804100d44c1d0307104035980c2150310380220640344215124030980e4020f080684080044003207203050f4103201d600110f00544112403001d00008841196020b00c003070325880a01c00310380d8800d00e110100d0303070350344511901030071a001c1e50080001c0205c8581040002450303585141201d9100010f10000581c00d0b2400c1c2d4a90010000103604d030106040c10030f02c4e50140303420500032400c11140303864101181101400803214038030300500c0310f105078500940d028403031801400e012003420300003e0007504020340d1107900c20206104913442445161103410450744882e008a0700d83e515503040c0a11a1000c010f00310107800d0854030b07286010318041c005450285078071460030614070b4041034001105490b40c048550140c100202594070303000240c00901c40c101800e5882e11450781c540600031b6840c0c014080d200002141c844018441c554a001da00100007141d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 691085944 1250 691084694 691084711
    0x140a0f06050901021e01050a0b060f07080c0309040501060c0b0c040501050a0c021801090f060b0910111603060c1b0c06050d020412080901090b0f03150d1208150d080f03 74
    0x3000103440a03841c505e400e00403071911000080d0500b00410040c00b65200441c08903c143c100707200020303518101c030341101c0000790f002d07030f08694031010000030742c1c00c502a4070303c0903500cc0c1c50603000042c041e03000004032180314410840b504841d038980080359018082c2d4041c85002030018014620f101d4000d000e1000030302c0c0014074040c0400940044142c054109030030188100e911440e0710303aa44103880c0100009440d600610500b00420400804c0e02c44014545002c00c22141041030240100b05200a1101d00c00c1c1810044c100303504c0b0708084000d0681071840d0f1000503c1c5e40040081080d11460001007181d0141d80c1c0c0391001d00c0c12204032460b4000c480c14012031070f420000012001c04000540c1c807a1403080f44415190060f00c4005007182507140c0c004d0784030000803c5483c030790b40e00c15030490b0b0b4042c03c03003142c4110721140c0e6804502415a60030000b070942d9140c260b07030100c00350010b40c024410008010b5030711352805614180102c0318100b20b0010003201c418040540e1844100003d07681c0101c51 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 691087194 1250 691085944 691085953
    0x250506041a0405060f0c0c07091514090c1308010504032604020d03030507050c03040f03110306041e0804090f060f0602030f0301150507240c030b0607021e06070c140a0f0605090102 79
    0x1887d0b0b41c41c200303030207588000c240607601c2580e04045540c3e690840010010b019850000482a0001c900c005ca0014005181c0d28000a00302425038a001003003405070401000030002e6140520303010302a880d0184000c00c0c400ea944c0200b071184170300849803611881e03020301090480301956605401900d4050600d0007480380c1401400068030b4204080e10051000002d14003104c0e207917040403801d0410081c0369500031b410a01c20080815441c0700c61800300040c0390381944000205041c0b42509001d00d800440405041a41040841c40c00d034000006071002400c4034101950b4034078060b41d680c4650704110034914400e0004000110200d41800d4000b009070500c00e1506e0500e50720182e0314440c00002040c070011280079083d05c03000c5880f40d0788031304456007820888810304400240c41030007240c10007407180c000300308041c070000e414140c0e00184d0072000c0d010035258411031074049101112802204c4100c007061120343d409103000e01d01c43d000c458689619400032410090129203d60040910905500c034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 691088444 1250 691087194 691087207
    0x41a16020d14012309062701060f06080604051812030a180c061b021c051204080a061b051228050603011a060906250506041a0405060f0c 60
    0x28050144c4180100003d110100314034058030038203d5000c0d01903e015030201c0104100c003621240302c840300c02611503c014401c02c83d420303080e02500403608001041c1d4840f48000803544e801c05002c60080034229814840c6640704c02c6405060f00004100d01041d50083c01c48411401d0036034004d58005070108008103240301081030b240b08081e1191000c40d07841214020404c40b0039400080c45031500b2081010b400340080360b4002414a121040040b04c60704100c4006504100c0100041182c0e48600d9005540f103aa0b15421141c46255094095880c9804c11031182494201a01e00d810302c100a602e41030b00f04807007101c072261080780040c810414582c041109441c0d9040c4c150015560b0890b24a0114440c60014189400c0d1141b0714807061381845040740b04c0c1229603030b120a07906401825030b0300c2c9443c1c541004019046401343c8540048101c07441c50050180074000c206a840b45000d148000c20701c8040c40018440300b44211800381440d04020302141d2150721940030150000810007200b4103040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 691089694 1250 691088444 691088483
    0x30b1021020408030c0709050c04350c010e0102240414030d150b070c09021e0d05040c0b030f0105060a0302070204050a090c082d01061a041a16020d 65
    0x82c010340140407582d20105540c505031104200201c0540001c0d2018066810841030850480c00340303000f100c05071610310100e1610454041711001d40b035101c0c24450b100c1e28506485c00c82d19440c008103420f0004031b14081a4529500000b145292151a00703403013000102c25480b40e03103041d44007030422118800b021181e08400c3d601007000e4030f442442c0d414001000171803d0794403500d0101741c1e071280d03607088010301c44a80441c1000c5041422038200000160340c40000100108510406000c60041c15001095401840400c5d502082c4038500c1502d0724103c0b2510f425101c038141c0800c40d4903d4100310b03240010320944c1000070142c41ca040d1107060141c102450b582c00102681d01c200d51000085070344000380c5042c426405414001042080081d14107038840304004414a00360b0050380505600ea080e07820344d0501d0940c800300042c100e107000c44c002074404410a40340c3d58441d02c52000102d209060119942030b85008891404850314406a01828681d0900110082d214003d0380d05900001009000e02e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 691090944 1250 691089694 691089697
    0x30106121b050d02062d0408031b01050103051e03120103080a090603020307121d070323030f03150d0203030309030406120204030302060112051c050c0c01030b102102 73
    0x352242010114201100a10442911159100500c1015003e14200168403214200c50605c901c03803403503c1c5d50080050302c80701404420440e18406240000f8001508100400a0414580406180c1142004161100d800d903002804050032030b1300200450800f070030005901d076502c221040c0903a410400000c03242032010400b41d000b51107060300015001e41e801ea0010700240500032600b401c41c11400d100400825822a03903280529482e0395000c06d060361940450000c203502c8410b403ca45020392240707003070345462040c0380904004814120301051140c0c00401070f01c0d0040204503001e81140d07924000d000f4009240865035412540d100c0b01ea00c091384060004600c211303800300080d540c99141c201c009209004032410b140c60300c4d01c1484188002076002c0b83c032604480c2c40048564020304542403260418402002001c414018a8040303020313950808081e111031406041696001101c02c0c00540070703207015803e144e501c08081c6080c1d40c0010b000380140c041c0007000030320075600c3c10441e85400040303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 691092194 1250 691090944 691090979
    0x80a0605031b010e030105070816110d05041505030f07120207201009050a0e07110d0f0801060c24020d09150501050d210c051e010f0c080c09030106 65
    0x10207400103540030072543c003c0b1413915101d5068000300440e00c1c00450080a5600160032080000d1407414240301c914481d40385030760652224026500e03501c940300303005005580180b142c0510940c21340956600035028100717991151440c5c0c5401a5150703a400e0048800220903c00e008020340e09102507008242c0c141107005241d0b151215040c02c0300c0b00601041662000e09007880f0030170004103414001038440039070b9401107440c2240300710159201c85905940308d40a130320200c549885040f4001191982c0041e6005c6031030190703110301400341d803962012505140d512201a000c0750801c1d4109501c0c114034000d0301c08000c000c1e0001802c1c5001f514820003900c2c40c80600703032980011585050150405071142034014201108c2d20042480e1540d2001018003400982035030b190130500c06c0500c1c41c4e0140e800070f400d00380e0240a4800001480d1400f9080da2000d1101400303030341ca841003142d001006d5100d07800e4250b08030b8450400c40e6a4043c2c030f0311000d6100b0340f8201d8055403550f1001030b65082c1914078540 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 691093444 1250 691092194 691092223
    0x14010803030f0a090f0b070314060301020f12040f080f1207050a05070b0403020c0d030806030111070b0a0c051c0c02010b03060114150f0c0d0f08160e04110f07021e0105040501080a060503 82
    0x12040e801c9d55030070382c140c8000f81c402d5210307901c108144400081342600315110700229400498a9a139030742410800449100c40252900a000448034100c80c14400146100340c1c0d442101d04460311511821601401900440c40c0031510030410400440c172060f4449034054820b00c11500101044000300f841c2c110070175800c5003c03440100c10300069107000e00030303a001000000011420402903894411030568082d1050320000c0d61a80480c40140c070420440d024514580c00309100024810302c0f102c01442c0401f1440015440e250031000c030341c6400b10300c290481e00c031541d0b8800403e440f00d04000c07e00c10700600c40000f881041001d6044250503a014102c1c00510388060301115100603001340201302d00303130203a90400c401caa00f0410324030710503200014081c200745080440200007030040380040881c0d031030b03111a0460100d150105c8200040041036940e02c2510f030f0000c1c84e10682801e4010704840702185001c220203000c28841948200c49266000000d000017050140c0e07110007184c1490740c0300c160030381e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 691094694 1250 691093444 691093451
    0x40909150c030e150405070b0a140f1c09081801180312120608150a0f15091808030c0319050108060a060e060f0f03030d0f14010803030f0a090f0b0703 66
    0x1000f10b041404240303031069901d40140d00c60728103552036a494040c02c1c00303032915034100865450000e034401d2222078441201c010115549001142c00306e80b40c0e40014490440c0c100d4030b21034040d10301805000342c1c0482c42e400380065007041140c9040c11428003003001c0316410083c4072549105c0303504603d090300e00158000c240c00011034200c0c60b001000c6100b114050f0800c903040107001c00c071034003002070144800d0448000c41c907840cad140c9000b0310000c1c0213030110300110103040c140031058160007201480111035403154204030920b444040c80301c030b103400040b010f002c1807020b00009200100c403000860b40900c040042002442c2003044c050120380c42a0004038142d801079003004a00c44c2c01e482140c000c0c000c8480218150b181c03050001e00c8142d038400d0f10901034102c041d9240580d4401304103a46204203108424400c1b490401660300050062000883c8410254000010751050101c1201d0241c2c03080c805528803a035810b14140d02130020724034119003041016200001041e10328518034000d00725541c001c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 691095944 1250 691094694 691094711
    0x10b0d0605150316050108190213060e0109060e041a0d080705060f01141917030310170307081e0408030a0801060e0d0b0a02090303030103030c0b0705040b040909150c03 74
    0x35203403408121220f4000e603c9041ea03602c01c814800f07003076401c5500910b451091a9203c040c803003e100a0a01c3c258071130341c000311341003071f801059901301026109142d5810454040349001110520301701e100710390226298202882c0c460506412018907100c170756400c030088a4129002c22803807074880005681100303000c00c03000704003c0c00740070094001c1600c115159065040005c20780058502c154403c1c13041c0795001070114021000c16807007005007801d44501d4952900307054500e881c1d40c41103844000c1c40c2e41303400003c91400b5005076075410304800f08000f1400c0800503a134405440e4000700c1d80780305441d20300114924a00c210401840038203c2c444c003440e20749011540160100c00b068010380c080c0410030070100300c99100c2c0c0c512103042c15000230000706aa101e5940c0da078020311401f44041c4d091f0000200200505030403010b0365603000d1180003004c09039900d82804480754011401814000e480400081141e040d10741c004401c1507000b80d07001c008649000d4209800c4480701500c0301c02180c0ca40d03540 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 691097194 1250 691095944 691095961
    0x80304030b060109030b060909013305030708060f10030b0a06092315011e08040b0a0c02070536010f080a0f0b09160f0e070c11060c010b0d0605 63
    0x40d01d4214a00303090410260307085607146c085410004224501610380d0300001031402509401070640241061401008c520a40a4008203550b006102110011030290001402d0a0001d648c00c100e5803c034001d00a20303241c0c035024244034040600901e5440070501c50110100d052000800d01070b45040f08001840da10b8a0415170555210384030810f5100610b10180c0307050315615030001d07030002181c11301500580c0c5c80070059843c1c000802088104040103e1150141900107003590302880c0201110180303a50360b002d003075040d201d12035604001030b0420141003101c0c0c280f40c60b05801148114104c5c8084082c0b42004c900c81001c0c60040301000983c1c800100600c0b400400840c2c05800c2d040301400100e1059180c10303008604110780140840740043c00030326645028424080c0900c06071003412400b940d6540c008184200790f00916203051b0300900407440c40d5016010700007248c4d1303000029620240e20882006050780041c922174600355290009030a032235454001049000e84654400203031801d00515 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 691098444 1250 691097194 691097213
    0xc0604170f01050c19030213090c12050c041707030309140d1505061002070e0606030a0e0604060e070509070e150c0f0307051c05160c0302040207060207060b061c0b0607080408030403 80
    0x305c940030301d0310400a220b05844220700780020b50300b0140340801c030708080b00300171601141d904009618580c94001400a040300a5006100f110303201030010b2050041800310984401c0c04c1e1000030080359020301c1c20042c08080d2a038108c800e2100070810811501183c5030000f040c40030306031403111135940e02c0401c44146026111091003101910080c004a41018094031174a0009403d080c400c81011001940725545600041c41e440800c10940b5640c0c2043c2c40d2a0b0050501080c224405021758003002c10310341851609584107000c0c90340c906000800c0c3d0024010460044054600010420000c601041104011941600c43d08900442e0b031401d040c20800d0030000c55941c5030700c820b1a00031007040140e50040aa6003020315050084010318403510300021281c4850b480203410500104000d41400703015405001c805003c0c0005000502c6c0240401541d4440c4034070700500c00c4000700a02c00660344d654440300340c450021740702c00d1800c201d544a413151070b0040c1d07000d1546030b400000c080c81003141108 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 691099694 1250 691098444 691098487
    0x120b072a052a01030e011b020304090f11071b03060e0d081006050405060a020c100302030a050618220206030f0921040e0c0d1d0f0c0604170f01050c 65
    0x90b4a4094681154400040c441e41100103040545a500c4035414200c00c1d400100240b500c0c2d009455501032180300651640c0203403103141d0040d4a0b050074030b0441c0042d4011425100107110030689402c406941d002030422111a402c4800c0d40c83c00c101000080c840d00c03030111501c2101004040130042488010105040144000d6411400700c20400409030440152010b5a80440300d0310380f0703010198004c0b45408840061079078026502c0311051801da8041c0e001314000d0312138500a0000b9034400d818407090302485024026107822210004d00d0f0f16010080e030610211071050b0040661f83c0a40000340741c0d40080d6451400c40c07000b04140300c40c102d41040303403060303006000309210030907070f90420904401d00035031240c42c50000101001550060f42081150407000c403600d001c01103070421460142000c1c5178004c1600182c0b0903004100310b01d1400003064054468000d040d1032030719040103801c1801c462200305800c0c3d030307125400310303141f9408081c05260703c04d03041c898205440c2d07201e03d8000340d11081000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 691100944 1250 691099694 691099723
    0x120216021e10050403110f030a1e0317070c0b0a0209120c0f0a030807030807050904051005030f0106181802060703081506030402130b0a0902070609120504120b072a05 73
    0x401040000a0750315086c20f22036081114007040313010700314011a00308007803d40014000b440714050107155001c03d085c104190f5003c1c2e0b6940341005100e4594950030345081c0d68020105034601c14000000344003400844d400000d424015040c4401c07500800c0c0e09030b048100b4046642c110041980300742c2058610912900d004561415205181d80c507210310600c01c00e9400f0f0104640c0e980010b2104d0f008000305d502ea140d020303100f04014034140303a40081051f450300699209020f94075a04000b2101400f07810207855a5a1070b920026880c042500004c03c3c50b070130020800890b00305e281e009682c45001400704640661196609850000c0c00d2000654071910442d100311414800d04c405611204204084d004c030880c000a0760020003400a2032012640d0300001e100c81c0006000410049190815940700f44142c03950b00c0c28280b4135506644501070350003800040c1070394002110208903c200b00c00e03040a10750070300d010121550411440336001d1101d030301e07144241c507819010410808106c4c884c2c44000c403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 691102194 1250 691100944 691100947
    0x30806042f090909011404060504260d06060504080c06070507080d050c0f01090f0f0f05030307110c10140310030f0c2103022d01060608011502030a120216021e1005 72
    0x61114a1b00c800307007000d022166100000303010004919111448000100f080004880281a47c0d2109512606083d0140d5040c1280003074414011001d03078044c0d0741031074081d00081c00c0400520105030481030003030394203210310413001543d40720500c1080c0c4422420b580d01691601c0e061070251174402c54000c1c408050303250040540104101c078007150b000300c0d4003070404030a00740d0074100024510040d04020707000d40000400e003d400c50b0022600c1c4800b4a610060b50b54038000c41081011a10100f003540c000704006000800c82611203000441e409030000340e000911715200d84031566640d90004086a6884850a0a110444132400548180c5849100c0c48170440d01c1e80c2d5009443d174141c40c9448116000d074902001d0700007002d546080040b04504002c01c491030303031a00300401c1501d0a21804a010030071801c1000c0461000c8200c80c450407140e25000c002e4420510010000d60007119510f03280d485182e5000e00691ba402c00c401d03a081c0041000310b02c4c140a180401101e40a907905490500c01c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 691103444 1250 691102194 691102211
    0x71803060f022511220c0e0f0a050a0b0a020f0708031b01090f021201020418050601080603060106080c090a0518010602010b0627061207170112030806042f09090901 72
    0x400c859604e0011000b540c0c4d860f900200b0750700402400030b405440310740290a202c240c801c1654024003a0104035000c0300d0483c2e606007640305000080c40713a40149034100100784005e10810390580000c01d01d400d440c0c17048070380000d80384071079500b40103964000c800e982e040001c0051069050b0740800704500c03200c1d8000c00c11440c03680c0c4d0b0b00c04120289000280a020880c0000c0e103600700a40c140e80042c54665000a45100f0103e08040104421180700707000c56041000325a00c2d01340000c0d031074143e80321030f04e0710009601d07101494400713030f0040f21480380e005034a210003194586032110000c4040300840c030742c400701c0d50503c3c1c0b010b8255901c502065005400910104c1d034a401c52030100c1c2e9580036803c2444c2d4607001140046405c41c4541200010f03440410345c144003240d030703101e105131441c1301d585000c041140e41c81d6042c01c0d000841d21507001c0c00291402d800320b2480d01d40703a40312a19084055031848640020440e425030407034240701c060b503030408000c03039041420706060041560040c0881c000300003452 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 691104694 1250 691103444 691103453
    0x1020606010e0118031a3121080f15010f030f020403080c1f1401030b102c0c0406090b031b0d0b0f03010c08071803060f0225 55
    0x44010001810402d4000c800b2810781d00031112540038940d0b0030900381c3d0300c42c0c407810700c00000f55041d00c8442c5044000300004400d20540200c1e8a0f0302c042c800c5050b080801280c0301c088000028100a0300c0506208007014445110011000880355150720340d01840d01e0441174035030318039000404540c01daaa0984031180ca981e444041508119124140000d0f245c142040480003805143c000030208a4000b410101804000941c0140c03244030b84e00044203915000d03d10342c01d807540a45034840703258120005000165842241035802002040c21805d81aa10a170307c90100804080c582000702a40c0c0f00f11224007030708010381e54000c000400a03485c040c60120000d1100e0f40c82e10038040c02400100100d01e0790481d0f150b1000942d604842c0341915001e510605100074007525510720301c2503108201e40c0801e420103019044a07502c00340c6500625a9460209659040340d2a480c60141025a40080002905840707090b0708408170f2400143c58140caa681c81c0d00021000c204001403020b629416070008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 691105944 1250 691104694 691104703
    0xb13090809060c150915150d020d08090d060506181b030c0d020711010f0e1e03120712140309060604020f0403120f200c04050405070e010b030709140102 67
    0x1400142c624503034485206400c0d9050074108120418000002401e120320408005203c0070302e108000d11b0f400007610348001300d80c0703540c0c803450034150014007060414000d842c03c24890480c4901581c41240b410742c1c0c2500040503846c011404a4a4560380d4052140c242440d000d0a003c450113140ea01c0b00030709204404100c01c43e04001410108440000000c07a10280030058481b580704d000000d64030750b541c91038000d0306103079143d0302d90340090090210341c204240b0540590504040240098810701c0c181c8888041d040420b045254151146d402c56a451302103a0004200444c020707500710007510411500101041c0d11000d00500b10b840c24014082103d0000c035041c0c1c0c200000300e800699502025110031000d00855001030861400d44501000c5190404180b004c01740d00c03075882c211100c200445d000c84181b901c00d02015a6800303000406513506060340300e80c1d00140524200da50950b541d03600b441c0c1143c0240c001c7c04005802109100c400d51704495646e024081950030500300302040e50000f540d8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 691107194 1250 691105944 691105957
    0x40b0604110f07051606030e011b0c02040b0a120f02030d0203070b220204111206030d0903081806070c140139140d1b0c1205120301090b130908 63
    0x202c2000500d501001410802c100f50810f51034a40a400f80e41c90318050001c0142c400d40003050350800300b101500901503107514151030038644500c02603004680a0100604a22001035044103141d58040365941c25100803005480c401c010050a0820a00c181401d1000c2044401c080d035105225a000044c0c1c142d81407030740703c01a1052042601c9661080d07254144800c2400303500185409000751141c2144801403800c0781061f598402c8944510341455514500050003800140410030140300145401004040100040d29114081d810480c00162a60321000088803c060508000c0001b0803004d000804048002d080c0180101c82c0080701a031100c500101e60811080c40160241e810b844c40e0a54507441904202d542c4912603280b000942e0b0390003880a540c010466190b40c112107481d81c03131034140880e580325138020611803510310603502011240b0350403615070043e14500399154084002450007084484400308181c1c0f4410180420825541c403102800f40c00c060786400403034551401c842c030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 691108444 1250 691107194 691107217
    0x902030c270a0612150534031d2116021c050f0d090f080c09040212010c02010209040e0f151005030f07031208090607030b010306030812040b060411 65
    0x80c0d0303100c0e00760b10000d242e10f42086240000208100090080f040d082d007140c0c00800004002e141c0f82c240c40181510004030103285000e88940074802020b80043d070400007000380c3e0801040e1030030107803540c80c008029000f1151a1b81d008a51440044c03c140800072061114826218600b02e205c3d40c0210000041c003202070300032075603190710302c1c0080c440e40301c02c3e400076422000351908545411041900c46c4210600a000100441c0c004030310284200a00000c40d00000c0003000140216018000d075500c000304140d0f802034040249060140e8280285002c0c909258001690f500c0d50070200001c50700c100c2c250030019803007070a42d030504000014003103891b0207412800750107550b1008468208100c560304500d803d40a211264003030a540000d22105481c81b445080c0ba07400c110840448455400b15610f001a901c0803000c100302c14041e60141542600c1890082035282e200d4039041183d070301c000e48401400540c84d0410040c4200d0b0743d24aa080380d000c80301030041c941c000340f00d98500c0c020303c20440c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 691109694 1250 691108444 691108519
    0xa12020f07020405130201080903120a0509030f030405070501180b03150f0402040602100b0103051314030417031b060105060f0903010e0111120a0903050d051009020309010902030c 79
    0x1018103046100340c8091542c001d00a10030f501c1d00020045904408000480c0803e40850114502d0300c0040240d803020a007580840d03449596468070a0050280540003024501007040b0045e84441d5210003188114000c41c024800185042c00061000e20000d5008820f00d070405c4003031200c40c035402c046a4002c0390080c03480c002481071500084291b0b521885e85070b885803002400188658011454900f03001802c582088030005000054054075411035825503e9001c440b0300702c00050106043c0c03c0c0419141c41200d08140d00c1d580b12400c20400001c000c010355001260b004513601c4e80c1c0b9411006000c0c20400341c1815450440400c0d01405010300e41c0d2002940440c1d400140c0d1003d5100d003002c5c000c01d000034003024101001c03400c000c0e8040325a445541103900005031075428a80511015a41d16540310340c580842d08410070005c10002d8202c04c203518181800140c50f95007800614024003940c00006076661440c0b0405141000d01a42a4000c121054038211501003c20b00019100512074500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 691110944 1250 691109694 691109707
    0x109050603011b0e0103050a0e030a0507050312010608010503061f06030e0c0a090c26010e0403050903060403021608072114070b040f050105180105160f0b0a0c050a1202 74
    0x60302610401c3c0e00b040c203680e104103c2d40c098a41c0051540da10200a0b00c0801c1341d034031100e480b0300036a10719038082c3d00f140c4e004100c01c044062259004159032070059081e2800d1070104c0324084038406080c2c3c007a60002d650100144154078061089941151406040841e03a82080c03166070000c00182c0300f90702c14180d032856640214002404075100100c00142810002a00c440e0030000030000c054010000030292031403081c00d400e01400d55000390364242e0034021689c3c64103144259102009000301c0c00c10000b481130030000c0c2c4007003040c1402039119401810107005031614000c111003903a40451a1503004200c00c01107e9a0401140d00d4040c003207110714100951350501c2c0c2038502840031500b0562089440010710610f10301c000d803090340c40049950746007540d20001100e09025012600006502003034030401298021002080c06010140a84000d061300740c555203200c20040c5815100b41903440f0030000ea074500383c4195034544585081003400d0284407100100200003030b0f00203400c240e5000504 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 691112194 1250 691110944 691110949
    0x6010e09070507080d0501060e0109061b110d05061501090e0f0c070b010807090b09070f0c020f03010f050a050a1104030303150e04030c1b050616081e04230901090506 73
    0x803250074541003401655a404041741400040209200310000510700900d0860a50310542c0d10300201c039599550b21009000742080c043c0f50030500b6400f2115141202c92403801e640741c11265136040342c003540c05488145001010310000844d8004c10f541080540c0c502480a8031150340171640040c220050389489964003050a0384d0f43c40340d0b400103080350340e50b8000024036000018079101130394001d960034014107240c003041c403a2200702590400081060401582020380c070505000903e580010100380c90800840003103821620070b11200c140d800e44074001c000e40385803c0e0003419040720140000b0440254090781e0001740c1e0045020080815450701d01010300304d00b100725410054410f40c291030b0380500700703807402414030034020304101c480f004d054a14407810450301c1d008000315440a0f0481d0b00c3d082c80c61151a405840d2410101d428100a000c0320701105114078201464404150620f40d5880c1014010b100740c1d800c001140e8800d58981c032030608183c41c3e90005074119181380708007141c80d4a58900 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 691113444 1250 691112194 691112197
    0x2060411060c030f0c0a02040e07181a0405090c06040b07020405132d0506100503060a05010f05010f03060b120108060a060320011b0501052a0703110712060519020306010e090705 78
    0x80e40c0182003010040c9c0181010620b40b003112200d0b8010741c002e01440403800140c4059201c2500c10484850611459082503040b00703901580c40415600341030181400904140c00641002400750307008a2281c0c1103040612610f501700b00d805c200e804041d01c40d5603503255501e0015200c2e40c04410f4405d000e20106040e40071200d81268010f094a003503140c81c00340b100488a2902c5618401e00c105000325003c2e0300103204580c1624911301001149504100040d40c009190603001c1c0c0401d580d48100040c941d900304042c000c800b20800b100407455162040316460b00401521103e466440d144041000460180c12450094045100e0003200428800103a0700303201203800d54881c1d4184078408104200701036005511950039014181c0c0c4806000030076002501d2151030100c000c0c0340c04c2008102203400781800e108546c1c039203011a000c4640320103075064031640301030040f80c50316140d40c1400583c156000d4640e800c100c03440360850551400100090039488650780090249595102144901e4440d80 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 691114694 1250 691113444 691113463
    0x3070e060418092108010605090111100e010e1501050906040609020a200c060405130e12042121110a080c0c090402060f09130c02060411060c030f0c 65
    0x2034080c82c07240c0040b4100030240884810483d1080e03c44000e8a07503054084c000c2d0b4080c030810340c0c2c03034040c507a00303112080e5015848400700d1818418958121010131004011400701d6aa07041000308a82d4103501c502425940300c40400869a08525003d0b84050403c4001c00c0c115441102c001809071100c0c4003180080410b03801401a041c0002103c1c20b000f900f00000d035000510340c0001510001d14061030307c0c1c868039409940c9a10207402c1004001c0c500d0010b0400d00d2100102c240001c810f41060000c074a0660741e03010700c0d007058101050030085903800a110390400c0d01011148900780c1c01da540c0d0402c5a1000c0940c0290360395800b80c55840d6a8031407400c007060384411f4000c03030740010700d40d040122940d00569a01e140b6071041d120018020b04080b000280156409401c881c20502c111a501c0000e0300912240c6030800525204130b0f80c3c0702d080303010b400481841031300500726605203800c2a01280800070a000d01030b4000f0404030002c0720300001100e24a84500c182e458454240c0000c40b802c003414030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 691115944 1250 691114694 691114709
    0x71e060902060a0c030905060a0e1306090501030f0606152f0d05070501180305121803121504150b0f07080c160e040b060904020f150c070609050603070e0604 69
    0x100301000104d4200148100f002e009444140c001540c4000300402e9100e0060f20200240d0100d400000358201010348030204c5180c4e100c0825401e4540f03000c00200c0304264020307a03002e01200491000d20545100700c0d17000e800d841501400c01880d00d6000b60500542660110b0085900081c03c160320300d806091000718030041c0d0554603200490700000741207400c21201510380d54600398150a811448489125110b5455203646052000300c031446140d61100815117007651580350034000442c10188020021311101410706501800c000f1000c03005102103e00c02c80c000c07460940c2d400c40529840c5100e01c00c56000c14902c0382c1e80c5100c400c0600445c0500710f4018801000441c5019a042002c58403008103c0d00b0342c4148801076842c904c10342d003840d040d6800f030226108440801c089042a061072984103001602940d1603200c4c0c000486d8500c00085492140064041510411404240100c000a0a482c94a08142403c0c40c00081582c80013a00080600040c0c052806481c0c0b140c0c03040e2401410071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 691117194 1250 691115944 691115947
    0x1030f080c12030613090b0c131505030448091a1f0e2b030c03020c03210d201306051603110102090301020a23071e06090206 55
    0x9180c20007940f0b07082555281c2c49800302070411a420900340c41450519a0032203000191625641c200c607401e54080d5080c2406820500008107404071003025102804405030303a0360381d60785070500703040580600d06481403c444000000c0d81c1d80404414001940c0304000450302244000318074803140036441a5844082214245980c40d026480c5100304201d01c05016980c0c0f00c24020800454886104680c814001081c5c48014600c101d040a06030154040d90510403074656102000e001d07600c41c40305100480009071102c0d014000c05034144000070400c0da0035801016a41e807101c000040c140651300314082c1807000407800901d10529500a442000c030041354505008501c03280600d60f80d0303c440d044500055407000000f402d14814400c40301c0102c210950700710110302603a01110100740300800490159000d0283c010303903030fa080c4001c00ca0003c8503180e180c803240905130003101d01c0708035400081c505003051044030701081c10105086081154008504150001c510b400c0c00100b0b10000082d400950 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 691118444 1250 691117194 691117213
    0x3040614163804020a0801020f0d0b0a0504021b010c0302041d060409230d05190c0c0f09020a031b0f3b1c020f0d0f050123100e01030f080c 61
    0x110b1884603030156000713407503500005407101c4409007030784a1510203041c460f50420040300c2941b000c0c3e1180e4820f810003001c04800d076541c1d00c006003da800c121046a00750141c1080210f00481c24442c0c208985c001e824298106882c02002c80541004444500c49045100000421640c4c81d07910840c11194025451700026216103140300994524422042c11445103840042c0100e0013442034804281c0c1e45d20174840d03040d0140c6402c6482c07885145044522222009002c562600024601c2c000b400240f400162980780e43c10b4001c0584686000403070a0340007180494040755480000380115000030700301010701506040c1c0303005206c8000480ca42c106110420a442c0c4480a159994845d49040307a480140181d00c44000031a0f150f0b400000398010030203000f0007450f040c140150350310107000d1008200308105a440709803e55550b42103000c280c09103000b030722410010204506404c03c51024844404c2420300f00c144110110600000c0d000300070f183c0403041048403e5045801d000d081800341e520901 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 691119694 1250 691118444 691118543
    0x403080c0102090a090e07060c060b2206090501120816080c07140303090117090304050315010e01170a0b420402070308010909020d0804080304061416 66
    0x40283c00b0040c03140e10240030000d5140383e00e004044010341010054450a40f40c000290344046c0800c40441d40344c0e48036503151406550f22280e101c4c910910036400103040c054031078290103e070065084120700f685402c1c0180304002d82c045100d8040c543c000d0704071750f598807805001c111700d60411000414205000484144502c40814848129500d840452071800b809808064580c0903100320075002407040001101c801c060429a260030010710001e8a1801d500c9402180c10000140d0301500c078160b6000040083c040c01c5000c0500520265141e052010301c1842440e8032801c071a400500f02403e514080f07200303140f0505e000402000c04480c046009200030b00070080e0103c04006540124410b0300740e001d010f003808d000303d071050380d0b040d0b03a1103020782c0c00c0c041130400404584400740c1c1c02c54919900311000a07510700040001e00140300045441e07500e00080145807a000c1c1a0302c40f07110382e0a005a000e0a006111454881540885074030040048410480307003281c040c840c000b000c10311201150040c01c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 691120944 1250 691119694 691119697
    0x21608040302031614190b0c0601180504081926180d270b041d150d060222090c11060f180109120801210203100902060403080c0102 58
    0x240d100750305613000704a101c104508800682d1085400c960010880410340e1b02d4008110300702c012400038210000703034884014002507000a828090694002c0f00117100d44600b80a44885403045598148180d00d8107613100926405884208042111030701c200c014094001c0c5c0e08011402c901d00d4520404130741c83c5540c20b013005015079800800310719896008035400c6000c581c4c04007664864031141e07070a5900780348022500e0786100b41c40d04400000000030807002c0007400244003c1c180162602402a41800b491042103006131840782e25042e0070b8800074050702c440c16010345203604561b00589031075840c0c40c202040b24100c0c1c8605110308a094010801c40030951059001c0d108950307400d401603900312981ca0340e844095400c502c880c00440d0009007440d8954101000e841c00751000800c090806560704500205008410408141043d0050190a582140e002c4d840c015040042401407007503004251500d51500c8840032031038031242c41c1c0041d03441c2c0800b102c00540d8800401130740d46c4e0303a10409034000e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 691122194 1250 691120944 691120949
    0xf11090a0c030c020a03051602010207090515010206070507051b12010903030e070902041a09060c0a05060601080c27030304030813030303051807150e03010c1e050a140a0302160804 79
    0x403030f140640e14918288001003c45400b941600c40510b070110300e03100c3c25417800c21030b81d08904521643c40042040c480d64003906002d00c2002000c070034004486c0b400641480c60041c102da0411105104260100d00001003402c81d11100320704c1524210b0252001c85c14203018021045129801d08000740c2c1090740c150301800c2e01c859200141c5129030380791002c08003030340300710304c00c10314020030040680d00c94204a0f00200540c3c1001031045180054084c2c2c01400c11071036000989150304100e00f084555600442000d901c101141d90443c0703020010410356054086a000f9420f4220701122800c0e00c030b48041040303d0103160030600c0d02d91203103601c01c80403803c2c524600085002a0401012484100076040e846000781d64000242100c05d04042c00944010304645980003088400d03048049240c0f401c0c8114949984e0341d41c0d40074484041c41c441c580010390990402010800100300d101e0010b584803044a984105506c1c40e650384544402c0100c0c043d00416580030384004409207604104079442008008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 691123444 1250 691122194 691122197
    0xa0b01090606030903140a05130e060310050c070b0910060e06040b01030e150712020d02031b130e130506010f030c0503010903080406022d13050906010203070f11090a0c 74
    0x18a68072200d00f101580c08900c4000c02044420a00b1004961007401034900900307103140590412861020b14541c202d0a40c1c0802c01070041c140602071241802e11040d0b15010414109010f2400c141141222034426050050510545c0c030001c510080b005203c250700b0148109014800c0300c3d12901035882120043e80e07003920491500802880c0f550281c002d0310340001010001d420080c80101c107440541100904980400c01340030b01440a8600740e201810900c140b40b4401a16841c14080820035648812249078041c003043c060480c145414801400644480090f004c04603100c1000e1080303860030959008041e03020b00000840d000b104400894120b900820b4200701c0907959406040c00c85007400c41c003900241c0d8550006010640035002031286c80d81c202140c0c07080c0c8600e039820307041007400c02e0000c55250f00006901241c001704a03907414041c11003228203028070309100b00040d40d6031080b03100007000005840009001e0058481e401100001e000c3c4c600d60340752038860817680050081d00036100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 691124694 1250 691123444 691123451
    0xa030605070e3007260c04020d0207060f0504120e01050c03071a01121205090f0d061a040213060311070609080a0f020f060106030f020d0f020306030d14030a0b0406080a0b0109 77
    0xf11564000191001214031200100910142c4501c00302820122450011440d11480301142c0554031a072000b008009510f880040e2144810310b460415140b8416a4125150038841840701040782c05030f084002000070b06092101107001c0005841c18000d911001c401030001203506003d1140e646000502c0449a00656045030780350303e200c0160188010021317007a00c2c200070000314294010002041041001410742e00e0515103040041d50001002c00b045a600c0c1c0c40c0d05581a5030100210030f0355110104070303800c0d400c15280f503a182d05d070503001d8401e810805d0b0325402585014032101d000c0b0752506030094000d000c48229814504650741c80401c40709d000549924401400c0351000c512240ca0103818005001141d20b0400104c016114030100c401105500304100b0586140c0c44c0318485070540914009616458000100743c244087c101155007403044001050205026110869910680003900090030306c1c47e281c0850010f04158011108070310039141403038203000702c07440c00358100c4042e21800e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 691125944 1250 691124694 691124779
    0x301030b0f06060a05030109090c0324050703110327120a140702031504050313080f01200403140c0a031b060f0f03050c1303080a1209020a030605070e 66
    0x50a80b103848130810000c1e40600040c000b4060f50740101d016640246400d223400354803900c40c1483d081303811060012000030100c2828104c03030b40d80500c80e40500641010004400034034038541d80ca210060128001e4403070340c019000700b800c0720500c2403070203c00e046c01c662040e108038142c540d541e402408038201040071245101481042c8500304c801c1c0550140c05403d24030440c050000c8000c1000e04100e4041c04188414001e0b032400802c40c070700034400e940051200c1c0100c440c019007151102540086581c80c0d0880f00c0f4101c4c1440000c51b011030b40e20039000c001200501409074100b04d05002c03070a9115442c40b41c000140160525940b031002001c040c4494810f60b2540c0c00e503100c00008964001140508040b4007549000307500107a44880503080103484d007164224141000079043d0021116290049440900a89c0c081164045168486410040404550000340c8654041c1c80002e00054481c1c2c0065041f40c807454490f071100703601900014489444c100c0218110f010550704040c10340410404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 691127194 1250 691125944 691125949
    0x30103050606090c0d02030406090615050f0402040608160c0210091707061b020f0d051510082a0a09051801090b0c0307200d112116080301030b0f06 65
    0x2084d0094910902d400d2a0030400c0b806917029400042040d40c103650780d00800c1c004114030740503c50850b075000209100d0305080008008000d50381d0894507008620601007400398a4018120517003109070003461003100b05d000401210b140e00b24590094210054441c2031b031000b904240f160080da64192051200142084602580d914041c840c05002820121000c02c00b480c20903400c0b0300c140c0c0042c0c4940b51810340c01010803c1042007030011580c036846820031640c02c001d800d84494000340c1108000d01018500300c50160341c1c00011500d03590080b5281e401c1c00e0395012500d1409800c8402804d0890120364500a06005080841d825078480071185480d8513060418801c50030303d10343c031601c142c00980b2540c0d90b82070700fa0002817800c01031103081801c040301822482c0040b901d003017847d801007600518010001b030128540d031900d0a0036620880035080c05a0040301c00410640e1a002c05035284e040d41c82072038070034403c5490080c00c03002000001009104a00340100d10609000030041e0032511564103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 691128444 1250 691127194 691127209
    0x40207030f05030a0f091103010b0105040807063c1b0c030f02030a0c0b0a090e01060c020d0c1502032d0315040f140f1602250803040b030103050606 65
    0x8000075180403080c2452070045001d1508541810320004030580b90707110f001e08032006a8403d441d07240c603410843c1000c0c54240210040103800b840c0c00740c101407418402a5440240317000c0e60090014111511118400c1d140484040da142c0711540046491282c182410f802100c090050005840c0702c240c40031110320031808540c4a900c41120078071030386980c40b160080c9250034400c90385805988003240214083c0c07002d100241a820728465030720046502c014240d020b003540400c0e64400c0d0107004001c0250410b0b00105a140c05036080910f5011700e182242100b50103800808a1122100c1c0642c803543d80040a40300a0148110308002c0040781030080000c8114848205c0c60224200001001d103003c40048a05284000c2c20100e0100050103400d825200001042d40021008500300403040801d90030301a00020800e545da065001c0c820802525400207a4000c0090001c0c401c004c2c403481903150f03040005040c0350082e80d03115526000c18040b580d20031311054649125070070204ac4035203014034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 691129694 1250 691128444 691128457
    0x160210092a1a0706020702062a01110a05181903030306080708060112060e01230a0501151b211205190c260702010e0a0506070c0c150801060e0402 64
    0x5482d150150001c00c0450200c2e44180030441c1c1c070540070301c840350058546801919415180b2a51810060084c110b15600b00481705903450450781000450300c082002041101d00301103243c90055922a100703282c160317040300c80040807a040a1351101031080f1840245d141c00c281c0380300303030b40074443d1541d1b509015948800c00d01500119410202c01086900c00401c088000588212004a4040103446010313084951030201c0496102c40b0791241d00c6502d1014660541c09030003440200702c0307941032102032028402100710010600c807004e65081000d44030164964011a03002000e12000f8074007191a1001c000015142c07008902d034403682c03060304801402014411042004440d4420201d203100c00080c0c01440741c18400d000c0e004076094000031140c020180d0a40307294507001c0d802d0a200900908403180c890781c07868290003880d441e000140340882d40311380001031442c21402070301c030b0b03424090a0180c441d40f0205d042c00e4040e1a041d2201d4203c6540350480309180c50781c0f810b004508040c40103130711842 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 691130944 1250 691129694 691129709
    0x2502010f0b1230030a050117061b0f120c280c03050a03021605150108011802060721020c01080c03092a15090a060c0b160210092a 57
    0x42c060340c0c0355001c51684a840c2081680f0009024481c2d41e603820200d54020348030139032181d0710b50005002101c11001c8180001284400806117803801e05140c401c000e01015110064190010b9141c03003c410240645000351082c004c04450743c20002d075840ea444c0d00c51347c00422980450340b2200c5940380a03100c00c0c44815040d88424940c1d031001d58048842e039001d005100289542800b8906214400180420805206130000d0a00074986103208441d000141d000442603810701103040c500c050a22001841c203607054404940b140510310301101c10415044011025a0160144030507860b80042d1411400302d007030f291445c0302d484d00401040c4902c000c031007a9030543d101406445401064100c5060084500c940c0d070b0304103851350360004100b600c04c040120180c0801080b0350001d8039001c203050005002c141400c0041ca611035958000e0300070010142c2070340042401f1650403a034001c1c001e268941e031925100f085440050b2400020b42000000c0311003075a00ba590310074420304030050494050300e614 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 691132194 1250 691130944 691130953
    0xf0209061206010314010315051005030304050402130504110301030c0e071b0219060207032f12011e020703030f0e06011202010203040f0f05090c070201050306092502010f0b12 77
    0x103091181e0101600441c1007566030f45444424034500c24540c0c0c0030f50f100e40340c82d04804004a80d19415034a001c1c001100b9004030903c03c101036600041201e04481095901513102d10000c5c05680b60100903038002ca4100f800c040503400c641420400460580c0e20485040740510b0312448100100381d800c503240c00210395400c55543c22804040034400b0018402494566101c00e5060540106c800a50002015900120052003001907903036100100b00303c503100800c1724004c1501d140f030305042078224150152128401c0444040020b4000c2c1e0340121086003e0340868074030002c80f000a40c481c8109800092800c4401e104040d054054034040c00b80c442c0041c009a400c01210a45407c20a04102e0640c801000000380d4101041e2030f110052450080b0009124688801d000424900801040703046c03004015140050380c2000a0340d8002d4400d45114066950b00e0f2900c005e03050011000c0039814150041c558070150b41500b00103041c01c00b411083c401d0300e00002c1445030301803003030400f165036401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 691133444 1250 691132194 691132207
    0x80f0303060303040e0c0720042d1d06040809010e0607020a05130b03060a06170a1a070e180a1508031b0313030c0302010e090106020618030f0a0c060f020906 69
    0x700024400d80180d0750180052400d041a942c4030b1070348120052104400d42000100d00042c0360512413006020003c0e801000d542d448485042d004640780e03600100c0803556140e40340b070400d064669607141c2f43c00034400c482e023505003410607800c0d80c2c100910302800580040a0949207091030410350b01441d0340900a2603c0506100400c06010501c0c500c08503484c0e83d03240b2101441e03408029050099040c2240024071504124460070014041c80c00c540259105081490001c0d1441d110040c0c001d00c03000b004102615000340449241d68041000b42d4002030303c0c5003002c0319098150b00c2c0c500030811044100200d1209004c0060380864034032882d0495001440705a042d03080090520582c24115810f0f24a800040c00b041c0b00540d00b15042a5560011080c051085582209164504013411201002c8540c03408500039a270700c000903c0040c17504103440140b400020104144c510b0501c0d01c03070745203071615662000188a2040414141c0e02e0b1428106040c0b100b4100d84202d0f0405003010307011514046 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 691134694 1250 691133444 691133459
    0xc020a0b07110714031e0a0f02150706050114040b0102030703050c160605030937020607060e07030501060e19090201020703020901080309130c0816110a0f1109060f0f060d021201080f030306030304 86
    0x4400500c03c3c2d0300403441e0200220032b000c40000914180f41b14410000349541010440409004201390b040e020300d2038005007040680c1c0001c2900e0703741d5410710301196103e400c0401c0a051444401c0403504ac1c036100300f40030851030713002000383d446a40c504e070458400101880c000f40c04802d114a07402c00c100d01962140440c2c20314041024200c0c0c1c0050f002d60320700385031981c2c0c400440d03203403030f20030b24054101c54002e00c100b02080c05000700a01c004e10030400f0343e041400749000d40041051038052036aa4800200382164000c0c81040c0056800800e0080e1310740c0d542c10031644941c01000d015104591285c09140c40100b41d00c18500d02600558649017907944444650b6440d44110690000f0300500110b11020740608010a110640c824041050300d1a00c501d001080c0001c1d8110781c51040040001b0003150f6202c481400b090700408948000c40344050001240c43c078407680c0080d8800c01d00004000d01102134540340c29048588160440350352940302890240c4a00081d6112030b41504100410084103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 691135944 1250 691134694 691134713
    0x1214070524040f030515070509010905060c010e0d05092b061e1b0801140f1c0b091b03030406140703030f0905010b0f03010c020a0b07110714031e0a 65
    0x490703228142441c01e038480051030584000c1d6442240c242d44601c401010034030411040c02d0b0000e1047c02c04509241d59100003800c0c05091780102801044040f480d080e2480d0700750401c621800d2000d09039140300486180c002e019900c0040d509008440d0900818281c0d11100d60780c500c51002e440814041c2451a0390f6607001d04101c840010002c0040039544c0c034501c0b03152181800809000420030100c200c0444041c0282c601640640c050f00c01101040071161070f031341c440d941111022502d4203509000d1005000c0300036821600648484400300070000384400000b4001201c41c000e181c0f144035007001c80c0405541c1d00c554007860000440c020380c480180d051200141034007500c00d09000c602600705400101c200c1c0c0c00600140c40e541c0d10703000f0003a454141040b103a1010074050f0002e0003424850706020350f0756106158010100300c034507000070705074501c0b8800c2058449107070010351390550b03a1940403858201d014010310384280500e8292811011451030f001482c0000f80d0b01030300800390b154452700c40c00b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 691137194 1250 691135944 691135999
    0x50304060c030e0f06040c09050c0a031113181103040818010e090a05150f030307030c110a080f0d090e04030e130c0504031e2a0b030112140705 63
    0xb0306840d8661081d8112080c069169000c1c1c1000c0200340e68509030401c2c0b018548254800d690031441d0031b003840401c00500702120380c000c500313040c003045c1c4143c00032841940d80b0504c00e14982d0002c400c1000b19002204040c9048400c000d2081800a641c07054414000e41c031065400074514501040540d203020301e000c0c039005c01c1420505105180c0e411300d40101c0c1e440c9100310381c040303030f05543c50302007040440d119010502203090644c1c0e4048144002e401182d40c0c1d04c18514003605000000321b81000704100d00d41c0207010480058448003050303075076840c12540c40c001280d6040c058064142204a840e00c940100c00458155251511540d2102c0c0ca0039214070020003a256040461200c180548400c58095001240c20aa6035941e985146041c0021a440c50b0b2800f2030080104c1002d0f5400300740e400d5011a1059254079a01319109030300543e040d040d12903540070307450043d004000010084140f030f9080203038501490b0064441e204143c46140c82d45824058542c0c0010a080068410001550031009 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 691138444 1250 691137194 691137197
    0x40b041203050c0a080306031504021e0406030210030b1018090b0d0507081e0f060a020a020703150506040b2d01030b0d2603010b0412150f0f0501080a03050304060c 72
    0xb5005451580e43d081c00c03420f50007545d042c4400014810b80341401c06c045001300115041800c0c1505141e40011006900e8010b0031005010040140d1a503030f4940c0d2100008640c002d01606080340528400303800391081c407500a02c1039071b0010240001902a01441303200c146541001000d6504141c0d05100900d040c0300d4083e0024a01c00500d07001410401004010b060610018130204448060343c410000741483c4c20007a5401c20500102e81c0840014450f820044070000582c513110031840480c601401640043d107a282005d00c0310345030480950109000d54001c0c0c406100124810051012444540d41c40c440f21000010700321820804000b03400300326000500d00403614811000002d000000400710a4a1664421070320340281c140d500e00b48000750407503c0c0264250362401030b0000b42801140f01d0b0b94100040e0080c0c4c4030801c40588946e41c0a25441030040002010a1308004014180000040591031600f0008695070100042400d903055055031901c0c51540d955841c407018102940a000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 691139694 1250 691138444 691138447
    0x20a03090204020d0f060602030921120a030f050c090108150103022205100806010c12093c050d020d080d020412051006060804061a042f040b04120305 66
    0x40c016512400105181e99414034081200312141101008450031540b101e829580200b04210190b00e40000742101386440c0c00c4c18040e0b1980401043d030800d00418407440c1183c2d00019102101a056400888149920306081101d5079035000d02c085c40e80b01b00e604290120702c00b500010603003980c907140f0185514042c5000b50400b2104001c0402c0c1441d4406c1c006e402d450802c000340b1a070704106014400c80300d02850080541e083c0400041c0c00c15105c00030240c03202c1940500c1c03081050041e10410001c000518080048088442044500414000600c0d44558690280039042060025003000743c41008091001c0003105030f080040748402c2e0581114940c42c18800f040d1101c240b4805000100450582c6140b0400c040c80e20a04100003024090500c07890404203022440d440a6100e61195101c0e01c00a40c0c0140344511080c8031f010308044a501c68200351299a030190008505079107214501081d142d503041001c120319190085000d02030022006000c02c021a10081d501d10040c180a800e205 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 691140944 1250 691139694 691139711
    0x80a2a080c0703080d0b011205040816080f03070c02100305040b060d110406030308060108090d080c03090a240c031a15040803130e06040219110f161406031504020a03 73
    0x107a0f80c3c5c0003d400d213040b60340e440b0301ca0b40c610758000700f081c031506106c540c08209610303090780e603420140601480100c0b0114203c2d03011040021604c1141c4024034410b0140f80c0706e02d0281e2004111841244049000340c981d0078080713034818001d0191600a80e0b04c503c80101c140d54580a1007041405107a0694410031003520074003142d1201d1103500302940c040d64952503a8a4400700240c203d4001821a250b00e0340101c11805120303078003800035034010410400069483d01c80e4682903141c00070040340542402031040c01d040d0038604409101c40304108900c014000125090002d5003111001d172010030400202c021915014903000c54006101042c05201c83c3c101600c03030815500e950440400b03c03a082c04038000070701040f01682c030f0171980504120707400d41c5015030303800c5060f0b03140000c3d410303075030601540900303800840c00d0070300c6200e040f00100011540c205910781c4e8a103107500c58610540508128000752080c2c43e040140499211342628035009540b0304140702840003d601c0006084201a901c116a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 691142194 1250 691140944 691140953
    0x612152702040b04050102010510080a02010e0a0504180302060a022704061d060102190807060e030f0d090213050702151009050103050a020306101404050603010e0a080a2a080c0703 79
    0x1d4800b4101c00150543c5550170308001a003161005800c01650b81000131080007a00301c005400c1c2c041c2e071350a10b072080c95481d2120114041e10101d8005c07550103814020f01a0040c0d200c1c80110300314034007036401c607008c1d81c541100000c01c0f44511041c58003207504202c0901c900f40740644501c410000041d0000610340d580c0d205100088907400303d020758030040d07078042c05181c2d0382c100540d40c101c10b045038142158184559035585903208100c80100259110a03c040d0102014070650b28410018105590345240700b4601324010311220404901c80c1c45295aa01c50210640c42103e200d01d4050b001001015404107a1a61310200104151030388040d2071800f04500d0700d2409030301d00842c4154021302c80342481d84101410008000c254003200385107200c00308502d00145c3d0400c200740c141a28005000d0b181d41d40030174054840240c031040780d0f11485e50540100010075008208000403980e50100b50041c2c00d40d501c1d151012018000914410a0000d0001c90000c200420003d41207100f103695013580c0b035030f6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 691143444 1250 691142194 691142197
    0x60b12060f15010513091d0d200607050f0d15030b0a0f050f0a02250c050a14060f03061f030e010b090126030f030408040612152702 58
    0x140324540c0580c5005004240200750702d1504054400d0901303c1c1004013140403000305942074404e540c190303529042100c00d000404000400001400c1054613451f040ba1140a07000303000a40000500d9640801803091000b0003083c0680222640d030b80c0c0b186442170740a491905a00700c0078004c00065030321b620761a808210120010021031181e11140c50624008250300c08403542c84003005585410312041185801c0d45146540e03000e1801540140c40f88202c0c85803281910480b24101d6208003041ca80c0710500222510321000c5483c11180300b13200540361807030754164000d1561441d401400521059118052803000b860340000007909843c4120b015440c03da8070f68014260100c0400c0e5902c902c0c409400e0280544d031084801a5a401036951408101015800550b00701809104034911b54400410080c400c9403410010003051a440c0d062900700001c841d0301911400300070600709546e620b030384005802422011050b100400340540c1c40c1000d80c0381108034246508510481c0700c1c103070354030f0f003000c0c0e10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 691144694 1250 691143444 691143451
    0x30203061207180f0506151c0e06090106061b15110703080a060f0305030f031e0726041a06010504051305100b09100339030605040209030a060b1206 65
    0x84250f2000c0f140d05004011206000d07080d80409042c501008041d8a07040c6508825004032424141d907100c7c004c1016840072030307901c55072800a040580211000600241d8240a031601c038008000302a691a82921080003500b0b02203201512a1032a0000c2564542c0040c07400f041220042689100b1350203207078169000c50411400726210314240a03580c41c9071310440001c3c00c1004003e40a007030454581c1c0355030b800f66a0202d124203900200049201c01c2202a00e41f00010300e00701400c80341401d00d005000e4900507122010805064002c44204c42c99103400180102d41001001c103054403025000300e19124010513070b90621808200001302d544403680038019100a5010003c0d190500c110551411002c0f075110780c1e500042440300d000546e803003008480c201400344c10009100f1504a10205402d01e241c14032155055099901d4081103201c111070501c1b0240d1654200140c58031002007108070b0240e282080c0d05580100d100c2000601c40e40d10092000d100202500d4150180000140c80c00c4000c5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 691145944 1250 691144694 691144709
    0x301090f0506040c151202030c0c0a050d0816090603020a02151005030c030d0225030c0f060e040614041808030406230402060a03090f0b090f1002040b0406030203061207 74
    0x11003c02c0107100d00b80d04140040c1001304c540c40d50290000d20014148502c011810143c07643c000040b4155105080803201441881000c5e81c1c00710031182030454665404131006030209102000241540c03254080720700070041103440c1c0400341410200d04500039044581c1442c01c0d8400c2840101816903074442d003903c661042410885c2e064204404d150814070390b054264065404414450400c41e00031400075105008554840c0780c01e27031103004403018000d450b40702401d64070194201080304000035510105841080d29102d00c4043d02d035080c40100d949503c0707000080844500008841d01d00341d008609641c0c80d0b5070f1203074481c0383c9a4458441c11b0303205aa044510301d07501e0b14803040d078541e1001080001e01c1540f80b65411460250042011361065001c01010903a0300e092910030446aa14045107454202011080a14141c4410307560790210f91001d20462140d140716444110b17042c001c07a405d4a40210540c0c1c02e2501e0300c08141c02a42003d81510b41c0500c07518042400c80c2002c01189008010302d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 691147194 1250 691145944 691145953
    0x90c1605070b1c1512020d080d0209040605030a0b0105010f0201060b040b090f0306010e040809060403050a11010908030a02210f070614220213020d090308090609070f0902090301090f05 81
    0x20045004090085035903103d641032003d031180303e1030b0010f02841140e40001c81c0e14040702080c03000662111a101e0004d14828003c144500d04000660281140c0d1f1419101004034075114001c26030340700e2400d41d0040113800b8140c0107020307070751040c03490406c001d03801e00006c00d4580e111000d48070150450381019222200214082026141056804182c003000350040c090550410039110141303172008001034900c140015070078403d5105c0d01d0446000f1a0010240ca2500c0361341d2420808074140b1151080c0018244403001c80d40c440301104440e990711654005011001d9600c040400244412150200d80c4a050040d070840d06100c0b002004641d1182c18000b45084008060088503074024191116034082000c0e1010900a0600e05218054045030a42c1500d00658045006032090000c02c41c07041c0d050101c404105a08202594000c0b85100140d81c01c0741c0d5803101d860380c0c0c0e400600c42c0400b50302d00c034201003240c4400d03540280031000d00940085001c15440c1c645501d0100d125608403601e902 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 691148444 1250 691147194 691147207
    0x40c020a0b010902130b071a0403110709060b0a0e0a030b072c010c1113060b0403170a08070813020603070518120c0f0103060909120f050306090c1605070b 68
    0x19110081c05410050f4086090000c141c29000c03240b80e2078002d100512100284d0b00007400783c08420281c040507100e0a00340c1d14502072030300800041c0700064408451160000200704030388640904402c1c1c0310301e03140c194284005854202d603003800d0001500c0c0c102240b003801002154107495110b200e5102d603280c207440c04a1059400c2c64030440a440c504803d140040c2070b030a03a17071340541d10301c0d410342e0800c0400b2000030b6408009500550b41004150045151410004030306418501a0040b43e00371440d101c820030000d00311741c4407031103080e0241000901d44000610a01d00030350b0307050b80005070034980c21324201e80f986c0400c44690003502c13414081000072407141c229034105a40060030318801c3d500b1107958421000303030540e11400f0004641c483c1032a40c140d40300503403007644143e006220100041c80f51140c6030500c0300700440c1c09415400003904da00c05480030140074800316805924064144001c0b1303690404650480e8110400403020186800214800319004000c0c4d43e0141200300040342d07a40c00c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 691149694 1250 691148444 691148453
    0x30902060c241303080103061a0a0303110c040504020d230a030309023f030c070905060f01080c07021e090703061e270603080a1d090c03041101050405040c020a 70
    0x401040030f0a00304411000500080d40305410a0440381e0003140407480818a40c1c0325146001180078464000f00d000310000107260340030f110750000c8000b82090ba0003202080b070912003920030440c0d01a420080c00208100058a03100c0f0350440b0f482d03a60b00c4006900e0340c524101c1c0c1040300c044401d07400240c90704018015842d101c07010069502d0011f4004d107000000045085032840700003810008003550400a030030414003402240c11604c1d804013514107080e180e4080c1c10003001e040e9a8140244014080300e4060b500030382c1d9450240030b00ea02c099041c140b0366400c000440401c0000903002c10822024503405454074261b140c0501c000743c0b00401c200303080401d0f01100401e0b08105035204da0309807004001500307e0f5013070301c0c861611701e501c900e0414804040c84006007849030b000412541c40080c01c055526880b41c0c000d0b031300d08603170340441c01c1070f0054104004010000f501e1344013051800f080490001380c03843d1584061840103050490425507120005021100006040409031708014040d50410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 691150944 1250 691149694 691149763
    0x90d17091c11100e0a090e010c053402060c06040308060603150d0c081e0f030a211509091a10031202010609050a1d0a05030a030902060c 60
    0x503618001c0d014100885840d0b03803410440c40c0649600400c48110502c00a600c140354501920401814801051360b03540080740c000c24940d400704909510303100041ca081d0b81b141d011035282020b00041c1e54040c006840407100032490f44503c2c6c003100900c02103000700684035a000b4060090342e40c4083d010b03518181c2806442200000c241f5032140c03004204000c10b441c901012004042800d0b6280100b04801e860720080098803a0814202031140e1500c411580080c9040c0c3c503030700f6000c40300340d561082c000c00b01159a07014040c20140454485a0181070181e139801c50b000c0001040040810025000c0ca90840300208642200840646032000d6009102c245808030b0604000407d0304035952030b1040c0b49080080181c08001c00c5100340c0c02100b56814400d400003c00f506035101d081006007001b65814005180c4113041820311303c000d5450040b600808a5410381d15600031000d940f07481d084203800c030010121403071b0807680f00710240b106405250b01000800b541d490410b1444816090000d82c00410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 691152194 1250 691150944 691150969
    0x1020c0a200901180b06090d26040803031915090507180807060e0102120c010c0909050f0f1909080307030605060403031704030309140a020109060e090c090d1709 71
    0x80e0846801082090180242510745113480313580043c001c1420400181e4034810001200e41c4418000c603050180030040c0c81c0c241c00e000092031340b210800103a9605035094051031198200d03a400500000d0607002c06850000d1256080305000920765092400c11840024242c0140400b296a4420040c0c10768000d00b049101e076030641807030100a481e140c0754540c0c03082c081c09481c1c100000d1000c00921a4001c001000c03401440c509141c0c0c4414014450328000e02103e140303440000c01e826000909c1c0c85551140a0007080c20124080c01c0d0f540e128009500c1410180103880c0708000e42c141020301c92039900c5060f000e030b4480c07030440b82e40e81403900d00201a10820b4020034481c10b01080100002600322500c3e07a00401c0e01403007641940d440303040036401403503a41800303401c644010318030100060010445031401c51007600c0c0d59144580f115405c9880211056449412825034800718000c0400c25000d0200c1d070000034130340c500014043c0d032050006a26480b10700301c42c6e030300456602c065140150261300e0303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 691153444 1250 691152194 691152199
    0x70c110105090a1406120c090306070507020d0609030e28140a150504050a06080406051014280b030412030b0108060f0f0a1706010801181401020c0a20 66
    0x52400040c00120820b071584130750084111014000c916603101c00043d01d04142404000d4801761600c5003c02c0c0b1103a0095100c18820b02072280004e080a001d18240c031419600544101d894001c140e4802d40100003a40e01038050180308660f200460f07884d903000c1019806181d01180780c0d40c0901d00c1d18000384e911600039180b24801c4c114901c82540300c01801c523003141e6005681400501c06800143c4507407003079401c80c0340c1000b961f00d004202c2d190017181c0e0780c1c003440c4174a0302042580e0b28021000040300300e50003490080440c1120808003844c20650307401311141e041200710b01050041c507881c2a04c80c004d501081c0b100102100304004d00030b071103000c0d4201030000d08040c041d06041d08002091a500101207610480d500c0c801d809080e1500d0100b00100507000d8511142540c80e20f51078099101d01840c07142c0c45220710400800c0388101802803007504419405041d004501c0c9964100c540708004c0303d401407541d03080c0032140210600300a62032400b0700448070000c0d025001409017851004010804d070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 691154694 1250 691153444 691153447
    0x10509070531090b0609150a150509100c0c0e040b0105010804060906050a051009020405060a050307021005010b0403020a092a02031303140106050d11090618070c110105 74
    0x101a441c2c1c412880c041c256464025401ca441001500200a01801c001c42d407003490705103000c01300031072000c040b4012901154283c1c282d540e041c4806e4081e0640e08251500102c1c1e0340c40c01c010021020140503650009414143d080c00e8a20000c07440c0b869501c882e00b0b0001e44d60407003040a001403070703840c01c0c06003290b041e1060491502e41c031341c910101f2040c131070a41044503030000501030164941c082252190301c035109100c01d0a0220304a0050601030b030740700843d64080c0c07400003030400461003180c044603405020103041000d0042d0a407200d8000411903800c0d40101101a012542c42d0b101e142e000e8980c00c50031700d8541d811401803001c05030b01360b0400f244803494a6502921000d880541c03a818515142240e008d00704c41050890540c0540c48102c0d892803011480801003040300c101c210240d21030030008001085e034940070000000d0780c0e03006c06040d581407a030090501d03040200c0040e901282c06403008641400700e964100e003040044801c000050006400e480800406940080c2820720034a8400d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 691155944 1250 691154694 691154699
    0x80c0a06201801050d0e0f0d020a020328050a0507080d080601080402130e030c01060810180807020a0b070b1906080712060f0c0f1209030905220213050301050907 71
    0x8072001d00c24540c0c030018224207030070346000c40ea125034112614500303048010f108500710545131a030f0720000c0c921080b9041c000c110345208640c2c40000c02c01811034000b0000c1c81c80f008800341c0d0981007070701c00050f5410820000c182402041c400c01228003150f200d03c00424002c0c0c600501903040c2826411140c080200110170302400c3c0e0380c03040640750042c2d0110b0318803108000c5004010018555403010364058040860f99506501c01980950201c820203415501070a6400b001141150401c0c0c20125551407500400c1020882000c0541059440a84240101a00d4074522007030ba81002e5803c4825030000020408141c2c1d403c018416502801da00c203100355814a1649034076000103021b2001c242c03000d00899400c0c40300a821140b0442071882c0e00f008402400900200f000c5c198211540c0030035141b0203010103503900c500c02d070302056070150b580034031007420582005540241d20031940700590001c0c1d440703280c440303a520041ca0882d1003213030340a02c10361400313080c942920f600400030040e540146104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 691157194 1250 691155944 691156001
    0x30506070509060a080601020a0605010914100f0b0a020c090a0b0f2e05090a0f06180e04200a090510050108010b1204020333090a17090409080c0a06 65
    0x2502c295101302c0c1014051541c580d80100e240c1505d0000181099040c03400000b00d280c125404201c4400c1310740d0344480542c1d00e002003900015010703c10090111440101023010030300c000d028040c15900340c4142c03950304840c0b82c0005d002030400e454842e00d2550390b560f082c03030b507107410039036136003002d4042d41c458145580d0940d11902e94515180000c81000f03450407500c0b011489042240c070745071002801444072648814152850016501800300400c51000100600e4200e481001c403c0b40c4081c01d40300016030303865072030654520380680a6503000e180c4a0281c80d0558070140b000d00034103240500060145403441026464100300c1d88501d060014180040c00840051822151100d10340318405803d5107552010034a009020003411445102049060b2009210594101e802c0258444110115280c0203c9251a12030040c0c000f0509090710442c0c60b101c08044002e0883c40500130800609241c01b529040345035403004086803060780082c04058200441c2d0b100b03240c82600c1e801c80c812080c010038200c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 691158444 1250 691157194 691157197
    0x70f14100f0f03060b0c070303020c06070506060d06141f090e10020f04050a0801050405100b01050913061503091209180504050a120c02031c090e06030304120c03050607050906 77
    0x341c48040148003101101e059000c4e402100042c810200502d54a4000840301501d440785800b04900600450044244510385441999076042e045000b07001b02c0d488d0350040100802c05860304a0f640e580f20200841020088281c49120710071040c1c50491200d101030012001950300d40000204a1414042c41e45100000400b070240c0c91240500580c0c80c182c031103040840703000d158400d65000b07076a1100450700e046d064002d6801381d8800d404980c503401c4001501c8094981014a550024400b4045900d03c0c3c0380150085001c20740032880044d03025100c43d1151854103500d40c040010985070280b2108001604601002903200f51500d414001d04181107815402c80b6913515145d515100c201143c103100040c00080803255002c01094144804084040d11104d10050180c0c800c2c0140100c036046010a014284100701c5a55603040c0c22074280807402c014408045c000c3c540602c4180b10220b0043c21301400c07061664041e0100700c000b40d14518101d032400d84000c00480030002d042c04010481d854000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 691159694 1250 691158444 691158467
    0xb0702120405090a1803020a1103120d15090c0f081602070b0c030d0c080109051305120c0c060703020619060302030c2209110f09041e0212070f1410 65
    0x101c070891180c581d484004007130704400d0a070064001c2d510844801b01500056200c03919072081d0300f24010380c2c0c0c20104054440d8020000030442c00410407454401c21140e030301981040040c82040c0001c552512020700488500400b804042915620151505500410b125900c01100c201d605412402400300075200d1000f481851800c600100300b91980da4002c0c820b13038508408144042207404407201c030090907980c080c41440021403a020102d1861902100c0d003285c076a070001c00815816110003100585507001d203000500c02c0c0210030402200744c1d19800141600c50080e401028181001d80e0004840081c0d0308000300041e00c0c00c4030404c0103072030120341280814412100340000030400180c0c41124a5480001c0c06014a403c0001d0200850b9807180c24480380b054a5214030307503608905200a400342903601038400100c0d411540c0014507881c44902c0b00e5840a03004100c502c2203181e21502c1d000d001e41111040c03002514041c400c1c0950042c4c030842540d001c4600302001c03100440003400d4541040b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 691160944 1250 691159694 691159699
    0x30b0301051605070c150c23070b0d061d090601060c050c06210405010c023315130e01110f1c0209030304080703020f01110d0305130b0703090b0702120405 68
    0x840e0f03102c14048080d42c90801040c41b20894401c00510810042c4045d640c00d50032200119100f0802c13a558480800004401200d03200810845003400761007509a00701980b44502e140d2120303008184ea02c0900500c0d15a40202560342d0913900b0310620755800c08205030880010040c0380290304010071800a444109404165545903841e83d0225082400b1412220080810311206040c0020800d05511a80700382101e0345c25200030f4031040740f08410403070003040141c1c4440c031130074590036070000c60600144d08605040900544541c90b60040707a146005013002c403a21654550303420416200030f000e005900e03007214a0305031a000d900b83c1003d0352805040701c00c010842105401e000f1211181d8115202041c0c014112034440d43e90b117040c10350385c03c02400100d01490301a81010003950240b0307072840c0350a0b04400170302034144200c48120000e1800410a0034145004c006200104408101041c064501c60303402003015001030410700312681c030190802d401c540c4180c41402c0d001184405460554108 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 691162194 1250 691160944 691160947
    0xb030403090e13022d0103020f070501180b060a2301030e06090a0614060607020d0c05090a09051b100c0f0204150806150619050c011b030b0301051605 66
    0x200e04040700c1c0740600c0e0b0415103015490806016510341451078000f100d910071074140b40800611000000c81c12010b841071452061040200c0c01550f029401a11010010a0b905428441c440e02c600c0e003940c0c00d411a0442140300d01244609002115001550107603050ba2111001441c00b02c00754900c040e844041d03002000c41c4440c1c0d58403030b8407a420100e90514124115522070070a00002c61b2034401190048844d1480d00006845454807039200c0743c4103540041845040481d190207009d440c081c060380486040301d400001007a01d641e004202c600803801c4a400003104549403804628200388050325210042506240304001da9070b8546e03032000d509640c50510126440f03803a10b401c525405e000000d5009042c00440c0000301000041c4004440701c0303c00f02c41058860380580341c3c20301346040049400510400c11501074041100c40448400d03a0340ca0404e14000c8048081400c42d08040000c2d82405220401300c01c4c094dd250123240029201103001308202d0034800380f8461180e14202c40b46060080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 691163444 1250 691162194 691162201
    0x60f0327050c040c050c1603020d0609051005010b09011103130b090102120d0e0c091b0a0c060f0b04051005060d0b0333010e01030b061219050c130905070b03 69
    0x800303001102d0a00d1000d8801c1c070a465082501174035030b8005200c00d9005116074440da100c0c2e00d00b240000707401ca176000340064040d060f80391a44000780c0000b00c030a03122032045505110502d0014403a540c002c04022100c20b0312180146c000410048a002020586510903c801402a41010f007881304650b00000101e03a122902030050f4140728032226540260400812100780c480204d4201f102d00050407002ea40800e1401403c11811400581d96039211407124003c01e2580a8600c0040410491070b007031590200c21955550300c1902c00404400800c40d0300c41c540b813812818140030300340c1c0200415507409511424180403480350300480180941060b2034065051340d58405105005600c0b4100c903040311603003242003400ca501e42ca8001601e044c0314829000150400c045011941a243d00940007036682d11072800300640c0c1c0305c4403040001d160140240c078220011090b81a030007281c0c4510044e00070311101c4010029a5020f03514140091405d1200c0800043c5001c180f030b20a85241c03100a94403a00d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 691164694 1250 691163444 691163453
    0x114100201060f09020418050705070602160804090c09091a09060f0d20010e0a15350903040f0e070c0206030703021b0a020f060a121401060f0327 64
    0x2480ea000a00103070050f4000b040e60741d120f0300200282c0300d201c10904030507007000b403901041390022518080000c006000210004a0720b40040c040c0d192400350300c034009820f030740b00e40700c169201394041004140e6803034486501c01d401001410007084108402c1007014548031100100c041c448900e2407244288e040016165581e80079a020100e2010340180740c0c0346100d260030411088040704e4190a60b00e210680200c1c2d611030140b096070020045c1002c201a4a0700401d442502074800100d01400321100381e41900060f4240d0320000d01d020010f850781480e503440b22010b81803002401605003a0070400c0140001d50003080c0600071150312200c5081c01e81c4d511381c0308442c403206410009600200c00824031110b60b9048d0040d01c01760425030000240d20840401480c0d5458400310001d402c0fa041030030400551408038081c005000c8641000882d90f03c6100341c0c0e0080301c5041c000c5184101c0d4901c014896190f001ca076002000040f41403c110065400a034103040300a0030503020030120000a2200401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 691165944 1250 691164694 691164701
    0x4030e0120011d0609240403050d0509030316050405090c0a02070b0c0c01142d090604030606031e0503032d09060a0510260c030d17070302030114100201 67
    0x11a2000700070040d010403840c814440703c3c41c8522000d01c9104a4001c02e840030700100c0c0c041074244c2d02c6440000e00f4a91315008200204004000f81c042c48018080c80ca078203015030060a119618120207503640e45005820b10100d00307400182d070800c101080c402840142ca0b104001a0891100382d1710940f0b43c900110200d280080c19000800e0702000402c121304003120015142204030740c00d88441c2c908440b1030641420a00806180c1c500707482c4401d20203400104072049042092026042591400f01301c0008507425600c9030307000b1240941d41351420002d00c00440310910071442500e404100010a54554541c0d0740000b078580030309002d00f80b408000462000c0031200744185031400403480c610380082c0c8a03440f00c904a0b6204e007041c2c2088001030705021420452401d0712583e221056202c11030454a80c007022214520220710b00c10559444002c3d902081a00502c2700b240e035641c030501d4002c00000d14200ba002d00103500341801030006004055002d02460541c1d401620000510600c401c000c9014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 691167194 1250 691165944 691165997
    0x241b16140307050d0306122003100905060108010b04050f01060e3705010203190302130b0f031807030308191103090102070203072301080c0c030f0c1504030e01 70
    0xd01c800201c00c0c080020218182c0c0040c10f01d91030400c40196900c00c0418446c0480d440104a42882600c001c250407122800d205a840060f040b1050000c044151034102c60b024681615150301610040200c00c1090281661080058a082c0014280044840d004000c180640400e1082801488106441c1c2482d00c010310b200180010034802c0002e1030040383e100300b122401c1031107640000d01003959400001200d541140c82030300c05040300e5110304114000e4101001c00503128890782c07400154001500064101e2581c98100140d0360704040b217039002c08100c551696269900070f40c60410100c1d4100b0301e00c1d50303c010310910503c7e02c0341c449800603006004075031441e481c01c80d010040c0201d00105502402c015813080e000c980b440c82e150840619641e000c010205035807044160801441d500c5004070542015900c40d02c1400c107090640b4450858000d003454175031598011a040c3d040d05410050a4011010240c3c00221400c01e07850041024080c490001d052100700d00c04140b0704c80c2c440c03500454 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 691168444 1250 691167194 691167233
    0x50d02120c1c060e0f03031503010b040c0306050a1703040b0306030c09040606061b0c060f110105042010270909140f03130620241b16 59
    0x9050b44140c1e1403442d88040c84500f69849850844007a50091000440e8011a80c020780110309540c0c5112110035511001101c0799019500c46241459a85a502855035419010345011514074203142c240010340000d50701054004482200b175019a40d4084115421b489004010a980eaa06c070000f0a140043c103030391142d00411280100000c1c440540d01c50310644005607904020910651409a40d405228001500403241110100401805291015000d40d0035051290b0341a10054405085410441e4191b441d0140640c0d204504100201c0100460354116046000d4a803004801004550346d000d0301143e1021003c503d40a000901c0362060080205c0314051120500742c0c6042c03046200500d200d05c100d8449c6900414040340003205072414050707620403010189280c02c0e002c03928541c0070f592079464030298010a00c0758620500400740f1100903040842281a200f5401c1c90002e40b0081420904050302c5214800100c05081101c0502400b0340b0030300c005101a050040c1030781c0e0032004d001c9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 691169694 1250 691168444 691168459
    0x6090b0906090f160e0402010207080601230a18110d1109100203030106021903031401081e030a120509190f03080609040f03030903090504061e050a050d02120c 70
    0x408000081c1551040e64100b040d564a04000700460713564501842d91500c64009000003400359a04100c0c240394440c0c0148102c4a005079540300d610305068080e0030010a03040e5048100140840c0715041a04a4400760350801c40239280000f0504400e070b503141c00c1841251100012107405144400361740d0038003124242000103014180c0440c03100e42c04200c0140c09060502c264016680c00030042d00e0403a0a25006000001d0f606145142c4000c0c504a0407800c0c1a51103d030351111004050f0006e002c1c0c000c2000030280c0c0c040c0244020310f443d11240070102d40c2d034020460355000030750115080c0f4910799000e1020543d6110510040e00b002c4900c9400c1340388194840c0120140803146001c0102e4a000382c480c40150788601d0144803082400720f5004e0500202c0741d04604c0002c0c8070b07500007070a1074005d207000307141103444400040990307190368400901c5007030008000c042c13100201c4507400146400c0314440002c0b850328000ca650700502c0f80000c0c2c802c01c0706030325802a185090200448101006004a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 691170944 1250 691169694 691169701
    0xe070803121f05060f07120c021c170f071e1502090f0d110901060816050903071a16030816110a0b0a091502030f100b0a030906090b 58
    0x180c0c0e00d811054100300e018903900c02107085003115000d80940106108242e0070143e08007030521150b9444180110705920081001c640072501c403240c091103811041e81c91440700b603410b0041069a1460100741009003603002d0301c40340040d05820205c01080caa803918135480b00b400c01e9500c0c0d128002d006010b03229400484400e001a115a01e20b40005445a000d00d0f00421400c0c070214220301400342003a8201681240541040c03401c1c500c44820584241c140d05024840d50003c165100400c0c0d2000000c200290148441c840c01040b002001030b5043c84c0a50a0110110000c0e50b202c400d07204050100042e00c81c0d00124141ca035044400440c0c450200d401020201c2c075008044041c21070f40c110a8440f94065503541e2407041c0c41071200801c201d002071200041684420003200e40c04ad0491200c0360341c0e55414400542043d1303580d0f1840c454054016102c1c5445c80c0bc1c4411418000d0002c2294442c040051001c402c880c0192400041c803490300094408107894044c000740b0440c540944000c00c0031080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 691172194 1250 691170944 691170959
    0x41812050c010e250315180f060b1507170d060b0c0706180e0708091e06090d11030406031521020310051512070b070c0e01080c090c0d0e07 61
    0x914110f04c0c0d0095101c00002042e854102c0607084502004140c0120f0301000c04c4000020b402ca1500550400c031660001e01441d0703203a031080e0b03c0381c07517003100d040e40c80b904443e201d031600883e1108458030a140d000d103480c10725a40c5105001d8101ca902a000c40d01003000b18003d030860303004a01034200501400c2d5a0f0b02c44000c51550749940b88a0301c03000a144c80d00710304c0c0760026030083c03004a410041c4074040e00e85030400b05541061008000e003685100d030b000d1444611401c44400e5420f110b500c07003d000300b81000000b244c100144003000c2030a025404070660400340c030000c100c03002c9a00d41e00e80085c0106400e441101140d141d5400b40c2c80b4610088619820300c191050720000542c07088085808101100d0701d444140d80003103e5003215038407940150040d0b03082c4421010f8040400a007500c440c10307150b2140081d650000301d0103a54003006410144824840403808030b01510b849401403038611544c0000031100b15006000000b851004184d42c3c018155035004400c0d0403441c10300352034906031200700 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 691173444 1250 691172194 691172203
    0x130b060f071a0f090c0612010509040203010906020a050d0e030a091503230a0e010b1c060908030709150201020c062d0f0a1d03120c07080f03040201030605041812050c010e 75
    0x28130125902501d60911541c2c030340300c42211941d070403003510940c250786424104003031504000e0081c0e800d9500c5500c4680002c40340e1004081203030144d01d445c0e0300c45009955107000c68815404500c0c050313004000c1d528905421404180885403213002c161110000020120054510940901d1070509105c03014041c2141e0f45000038410914101b007000312507001c840340f500362040c655442d9000b41d035602e400c240400300404401100c502901000c2070144869030340068075441140e454000507001c10f000d100c5440071004d03440710360301e19200a60a0410300f84801d038076000050319502a110162001700018441030340c17a580f0158030f20035049a5072a0051282c820b000d805c03030304400e10381e180a55070040e10b0480c00340b903000108540e0042d4100b03114003ca03030200c644040d0000314503010511400300040c800c10000c1403410080c01c54070b13443e41407910024090720019006188201e080c080889101a04a81031400ca10b401101c8554542d00050041c0e9040c414214003038519400d0041c1258000350024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 691174694 1250 691173444 691173451
    0xa02040302090f0601091502160b030103050c061c0209040e10050702060702010908030103060c0e1504050102010c05040b03060415120803040c06020d02070605090a1211130b060f071a0f 81
    0xb5103440b42595850101064004100c0d44d02d03021410100701880b100e41c01e806140e0a1040301e00440b0703400440c00040c5410300c80103521074459094008018002c000b418018880e0344007055500c5070401411006030407600100030b60408041c1d41c00b241003480c07651250001d004014200c01a0350114000d0f0303040d10040c2c0b8007211080302500c43c0038080364409105114010049030848003003400c0d642541c0e520405803032180c80c0d903030410990f086914170039555402800c09031418406800c0d52545004006400d6610301d08090040c008140000c20404003098102c960240301107800152044135215854480038040d00080c0c0211000c5140c10100500c0790001c2d070040c1c2c010f10100960743e980300001c170380c0d40000e41003110050700401c030100207181c011400780c00b001c003006140c9405c1035202d0724400c00e0440b4800d41034031001d00c4107650042c80c2c100401d8465010341503110a201810030400411071500c00c0700c4405000d4280000c03084140f0030031000c0390340035000d40050304450b1b040140d0040c80c8001c094 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 691175944 1250 691174694 691174699
    0x4031101030506120318030a0501050f07030c2a15021815090d0201110703080304080a0f0e031e16030c0501110f0613050c0a030305040f05030c2808060a02040302 71
    0xa0101d101d62130500403d00030413000b680154945074040c003c0b0b402012600f240540c0521503941c8100010b14280602d920480540041040364901480020180c0303004c0d150410500080c465229001002c0d80c03018048003820450740050181c00c6c3c600f584186881e0f00514160620100d601a1a44951003041070340f42c00444114180c1d90050b080d2648a204071040320740d001e100c15481074010f5001d6034aa4a07684000390540c1c154130340e030ba03d40c201250320480c0c00b00c480e03007800100c544020b904080502c0b0f44001c2d901c0d168042c02c6030100829038860400481f25020440610010014807003000320b490000140e04100001950382d10304072000030003d00400e408a5210800c005040070b00084203a50f00c0c00d140c00910064443c070307103000c2d000c400410060300c25000f040000b4a42c0d44803401da0030010362196907070759079992900d02c0000b020710003508a50b204c0c0e040308206540c60340e42e103910002d0180440a0400d5004401c20400e0381c03810300c0e40d004c402d041c017a80040043c9410700d5800741c07040340e00a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 691177194 1250 691175944 691175951
    0x30c0c0d0203221404090f050609030304020a270218031e01051308190309120804031b02090f0705070f0c05030c09041a0702012304140607020d030203100b0403110103 73
    0x55001c5940641580607030b00d03407043c41e58800c81d668a002c6d00440392080c010a140c0c00d000d0241d4841e14207021046811103c00e034400000e00045003000400300000f004003000003001c0c01c103041d030b07407107a5101400f01501d40340e41c0103d01f4406080021a00c2d92200c2001011501690050088060607480716034154140354038000000c1e00005034103e2140d006540311200a01e000e1952041707065609404580004160f40c0c3c00c0c20300300042052a4000030000341c1c1c0c40d1442649080e140040503811503513007090f0041481e200200044e1074101440341c0143c0341e106d0880081d079801c0f804031218040d5920107407000c140d00c424407040c0b003843c1c08450b040e15403c0d003d0f544100041c01c2407001002069600501001022001c43c1800c419140400e07042000e038400130802140c1d13001995031803c0b004042c5d107842a400b034203020800901a1301d85c00f0040303d50000d81032502e070070303130010751152484603039001803540001c00940c0c0b441c0242406005858148841a20340780c407804d01d00c100141142c52680468913 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 691178444 1250 691177194 691177237
    0x1404050a06050d0f03030605130504060c020309030d08061519020708070b120907030c0f06030506120309010f09050a090e0c04110a050d06090905030705100c0c08030c0c0d0203 77
    0x45000745001d07150050000e201ca20a160744155084103c500c09404041d610500841c035640c905d180031030041d8204201140c14205410041d04a07481c00400100390352081000c1d50035500d01264420310740b051030520848035580ca030040390b007494007088191910540058080309200b6107400d40b200000095085135000c0d6247e4004c0c1d996040c107806000500718091003284500000307640399590054400e0145d5032a15500da90750b40380800789400440c1c0c0c2d0100d42c0000c2c0803195041c81940c0e84101c00321844010058100e4445440f4450f400040f410021032120b4801501c2c0561035070002000c0142c070141e502030b80c0f80b0500b8010260038400b130945001d40202c0751410b00e00b0b0b010395041021214400b03450211420002d4485600c994400030455880d001c0008003075101d4452054414002c6014542c2c3d481c1d5441c056060a0b00c05c5c41c420350151920300250300881c1c4c0220704c100b609a220022a0392519503e5071407400780512401d140291003504008488a0780c04000342c251902d581c0700e001440705 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 691179694 1250 691178444 691178461
    0x11032d0a02010c0f0312060b04090f02030c07060b01090315050a06171005060406030501090b04020f06041d15100e01020606010203041a0d0b060d060f0504021908071206140405 77
    0x20100c4040d0000c1c0242c034080002ca0240305440350414842d091041c9003a01c1c5000344015540f607079104140000001c203040000c8a181e020301207148205a504625501d0504e00920403401101d001402c80c0360303510509030741079004107264405980c020b115800c58001689a206c082c00b0122155050241031800014005000c52240d605480e860005030442904241c0340d0300040a0007448941e0142d200c41c00007011810a21541c6001c40c010080620700d072030702c1e005001c007515824020324002c1604000400800151a051100140c402c0b480303014140c4440038401001004003e0895003d03082c100c200d41902c1c0c000342d4641940c1000e8090390111790750a0300598403030060b0302c989400340300041005181115018002d001c2900102000a803415001c0040380b601e401c411010403125946000c1403005103034258a810061000b11401d600d0407042c0d1807149800240349402005010300d9501040010703000317000d1040440f150101c1000300617615801d0004011110740720902031031626001c9140d40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 691180944 1250 691179694 691179703
    0x4212019030203030904050901180f1a011a0d0f020c011b1b020d0c09020c060a06090c0504030305070f02120307020f060301050f060d0204030b0a09120e030d030911032d 74
    0x4a400601840c2045c44030800e1002420005250545c0c41d507035241848010348015101d01c1100d40181d00040c0604454640a9280c4548086008000c2540c90042050003250800072202440d1440c0340340d100c4c0400e1042401500b041200306064a00215880c00c50080543c400d054985034403014242064070b00609071800200b403082040000c881511800160a06400800c1140d03c1003995071001a90b500f506801c0f40c01c4207407000c1c0107422070020310404464030700801300078082031a1f08204003840800701410174403943c8001001e102e00800d0300c0313050101d035045285641c1e401802101d12110000d01c103640740d5000c0c0c00124031030781d451120440c40f0f041040549050701c20240040c45030b440c09008116558000505000900d44c00704404400140c80c0504039011310706807400407402c9171040c90b00e6280d00040070103102c00c00c020500104000e90323001400c01d5403c030366400c00003106000380c101a241a002500706503054801c049042d551383d40c41d034542c80c0c0b0f45d49130141c400820203024500d00e901c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 691182194 1250 691180944 691180949
    0x30c02150403080c0a05071a1b09130c0509031b010306120b01060309050a14010b010e31060f030c050109081515210a0314090604212019 60
    0x1441103c0010009142c610050481c00301d035091181c1008400d687d40d181084c1c8206950f000054002c0c02d00030707480440b00f000d8070110441e0044c43d00341320050300030600c0d501d0782d0b11140307103603030b84401e07031007204d1809041100e2030b245000e02503e0a60014050756004c0d16198203a0a0001b89840e00000720020040303081c4030340c5036000d00500b1969203064021406069a007609031103a003d007510032030000380c0011010805240420010450703035610301c00500582c074210f40712030007400c50441c00140000c800303010880301c0c1941800c440c20001015140c90082130190008406410b4244010003448004181181210b00c00d0366060f500645030299680c0b121413980980c4e860304480350105005c4200c100481314030340000b4151541503c807460341c910400203402c00100307458004011100606501c1a5200740700c2c6a411246490480400080b40d2548101d00c141120720300400f002254042506800c135a0b071507000480c00f81010407400c452012048200c01962041000d1043c0308920100c3d6030b0030504 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 691183444 1250 691182194 691182197
    0x13060e0316050603070201110711090a14070c1401091b06050c030409021e1215030303070903140a051c030b0d0c0e18070612050109050903030117030c030406030c02150403 75
    0x1c0c994501014000b00e6040a04108250754803160103c4445064a0103026618081d8115945d40c8040006104a0041c040c4c020700201c4c0c204503020051203440750001d0b8014a80b03107440381ca80c08090600c018070b83d4450034030388032950a081070034052103200d40e4150580171080d40c403510310980c2d0b10390984031403003542d84110140e0424030082012040382d1340607040c41ca0170708002040401500520880760340c0b140c10900d4410460320280101c0b41400136084003030f000190021451424540805064140c45100c01056096080b48020700e2040c140404905207501008489606001481d40c00040d071014655200291410101d440f4600d400000c2450484c0c2005107064800e040c0502c0e40b407070050007000c0410301000400e40c607010b0a02080030710300400e507550303078041d200c450902d2070400e444040c1d000c0811b250401c014410740c5200401202d0441e4000c106400320020004100b03030a500070040b004180f8040402d0010b442505600b06503039148456003a240d5210781503400c040c48040544000c0c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 691184694 1250 691183444 691183483
    0x1509151003020a0b03090309100c03020105062e1407030305070807030c05090f0607050706051c0501031a1e0f01091d060403050c01140c0c060c041406090109080313060e03 75
    0xa2a000d2900446d00440c1130790650340761043c0100800c000b40c17620403060001510310a10401415428486c1341c0d00010f0071030302500300707180d08031103190402295403941d8040702041d5402d907402400b81240c3c42120880340d9400751a925a8140a0000d10080710b501010134000d00014003904e01c43c0c444c03240512000c0c1c88483c24001c010041c80300c100300d03d02c1e0680d000542003260402081c1e04102d00700080126544559960500c1c060b0a1305650280c0c501d810085e04060040c0000303024106070010251480c0019501540c400d92101c01c040850398034240e03000540402d00c10301485001c801c0b410b807605090184040c800a50f146866058000c600c0e0815410490200740000d01c100000c0c01c0c00703014400003286071010070604a6103030b4420784483d1189180010552459035040c0245584000c950222901f003914024146044091100e90184140784c001000c01c0c0503070145003a800517049900032251140c3c0a45040d07112440703240103000200302c09400704030403850005203500e841c00d4049200f0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 691185944 1250 691184694 691184699
    0x114070c03030b011106190609020c030f09010509100f0f0509010c0308060604081219050307090314030d1d012007032f030406090f030b040807051509151003020a 71
    0x4030003c202c26501281000203400c4040080351040011034003030140b42d0102103204e440310000c2e070100d44a80c1c0c404026580140312020540d036000c002c3d81d50080300c14004550741c0d981c10b0012511403148400281e40321a00131100e90301254851100d240321707003d903151002030015040e42901c0901540c09020300045114010200083c407408003640c0002024051a040c2504d83c24403e0501030040410b108881000c140024000d410a00b4444108858140f19246003021301c0028088901d500018011403a40480b000c1c0540c820401c5070440840782c60308102d03d80d0722694440b42c2c8072802448281660a040391001c41d05202d40800c000c41500c0c40c80b440c070340b0703020303607030075107100b8210407120038542c141c8202c1d8207440c0011240602c1d50449500070b550740c1d80c1402405003104200741c20501480310001ca0030310004070941d1065400503040260991a1a15890018900000004043c1d550301420703090200045002401c00110303d40c1d407507040415a2140007541d802c068130320001e0f42c00703010003808 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 691187050 1106 691185944 691185947
    0x13023f0c01170106021c11030406081e2e0f0f15050a0503071d0a0e1008010209030309010320071a0708190510121101020114070c03 58
    0xb03100ea5040160007942c0c1c1500d04c002d40c0806002541c4d40788503d000300c1020a4000e0020704407a582e41d1070f84030040400307100341d0700d0842c0c508607030f011112150f002001d4640708004e60310304805110364106010202540c0c00c0480b20f01510f110002040300340018000e04060030590061502c0e6525059050b05045800d420200070040c00b4010042c07200d51000c2141e801c00b1561400b004510280103d8201d80020400c0300b076400302284200040c5034560850722032181c50072062181145560340d001500b42c0c4545c0075090b40c103030010409400d15602a90105107c040076011015404a030318030740d5100d95014034820b4408458207040c1000440c403403003a4a80c08409840c100c3c0aa00b02030080c010381c2c0b01089074074408161100c00065009a250800500900580a1691851030b16040078164042c0740d00c1480e0040d400c11300c00c07541503508a1403050084640d0fa0b5070144c0c01855440 = true := by decide +kernel

theorem cover : BRFrame.Cov 691007194 691187050 := by
  have h0 := BRFrame.cov_init 691007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 691007194 ≤ n) (h2 : n < 691187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
