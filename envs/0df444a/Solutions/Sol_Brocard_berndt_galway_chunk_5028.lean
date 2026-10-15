-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5028
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:30:44.327274+00:00
-- url     : https://prove2.me/submissions/86ec7b84-eb1b-488b-b7ad-9619df2e8a9f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 904136690 ≤ n < 904316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 904137940 1250 904136690 904136747
    0x3180706050c06010b28030b121504080a1b11030717030a03110d020424080601020a060b1c1a01060207120303200f0a020616050307030c0e040c0f 64
    0x43d140d00610940e0000302c0001a031114160580e00c14040b4240c42140c0c0aa00604802e0020b0250040762401c6104a000780c9440c1602c400011f402c918010007041200e0f01943c4689031004240c02c5032000d10103020202c55072400d10740301e03a6000e2003080c1c0724121220b4010308250500d480c2c4000390300a5002d0344002201324003e0b04002054401014031440c010130803010b443e446481c1d6026004c001d48a1600100b4045080c0e100143d10501c4994400d001c0c0015090901040311140b5090700c0316800340c0c000e0500540880c0d45500110780e01c0b48013600d844406503055190320000c800d60324066580c0c040b14884540f0f03001052081600501c0548001d106940c1886240c441c0300501040003010302d641c5240c59900440741044845242200d0a020f9031503040d28103003460980d1100ea1040014003078140000e0804001502d034082052050340c80a04690b01d0700b07000d40042c001c00358128240f146604040161340e030b03035004070140c41c031056032001d1070070700103480103044058110f07140400c1505e400301035075 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 904139190 1250 904137940 904137943
    0x7080a080610080c030907170f010b030102160f0f02090c0909070c03020d12110307030207050f070e0f090a0b040318050306010503032512030615030509070b0a030f0203180706050c 79
    0x241c11a079003025017580c9450300e020403890031036550300c400d5075802c0b505021200c244010942034079582080009202d212403060816080307108142000070103052203042c40b40803807800282d40342c0c0907200b5004c0c2c03030b0081103540000c0c090480480e101c2122010001d40c00c4000d0030000912074100c001820030030000c0d415580c0c007948a80b0403070141d004200c440f9130304280c5560542c100d22202000403560310b56900f0000001406584104400e640520506003404006180020043d007158503c0c02401400d4503a8244980607440140c00044184a03540386580451403e0303139124051031181d2508034a1802d440caa0300004030150380014840d0304603100400c01618084100d41055503159884003843c800200030407a09000d404002e00941c4034168607d24290b09507022006803051400200e051005042c0114180c9204070b5003503189030005582000240e402d80040c02440f641c034200070401c4544850404100d800498402d00882c035144402015083c0500108002d8801482d149152140014215 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 904140440 1250 904139190 904139207
    0x140102070e0a0209041e0507111216060510091d0303131a0403021014041a040c0b0706050f01150203070b0c0d09150c02071211120307080a080610 64
    0x1c41e4081d4400d0001d5255400b03607048403450a0003c104001400c4055000010a03030035141c943c82241c54500810595401602d214035000490070060040c820081003418040d00300142010401900c10f034140001246030040030300c6180044d02d401882c1c0d00e80001d1314203442a82e40700700030f4a880000c001300b03a0701010088903441017124444924112041c0340c0603a9460401c0d80070b4000444910620080541c04140a084500c4070103051100d200400101d80ba41c50341a20020544048000c0007402e40680c108526402802100a992180d640b001009034950140c2001c481d034a0740c403000c001d030980c2e0940b280ea0242c040f1000c5c04041048605005e95240b2910001410200c1450005564040f105d0112001e140400c82c042c44907651030b203448500005410384c10460b060405034002901840005d50300121503024944080c00d425584814a400d07081e4850540c000200145030856586c0c100b00800859200b240c1c401d0781d84440c03210080c9071600245c502032007451403000641040d0792100c0c01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 904141690 1250 904140440 904140449
    0x16140615120c0d1403211f050d0302121602011211030103080310090f0b1e0a1505070501090b0105150705060a020f2229041403030c0f0604060614010207 67
    0x10f0404400506041c0c004080c0b50031149668403001075060503982c0b07002454400c1048812411515443d0581c44125054283c40142074166000904010515014501c0c0440c40d004c0d005803601c1c1c0040640e50030042e803100c240c50070403048103042c803421541d2141240550000c040b108110840d88000f07100064803062102400c004804000304401203d110415002418030303038403c006501038400740300060a842c66907240310b070490070b40c20700f02c2802210300320080846c000c188000160512102d040d40181a0150004100c000d000c480f001840c08d108840900e07010324814601580360104000a1400e00840000d1440d414000000058400038036507030858421080580c541e9075240000905024410007022070b900d042141c542e190007034102880c140d80402c2d0300d1000801c0c80050080d07014140381680b81c070064041104100d03101241c58800c04c015401030a032490600040d04041c5400c1c100e8420702402d80092041c081040070b07910400000b0701c0300c01c03642101e0401210000c2e4517480180309 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 904142940 1250 904141690 904141699
    0x51c090e16110607030617010c08160315080102030414190b04030e130b0306060609060d0e070b0a030f0c030c02060a200c0714011106040816140615120c 67
    0x21101c0c18038003419050007031020a80880d10b181c6005007000f4080e00c1d262064440c24000c0036900081e440701802810546c000e0b41c0c03203492480c0c03079018443e9404c4003020b44035001c040e030728042e244160a60b0302c0c04400602c080400940c0f0303403c0500b030607007070360544000350800d9138008004a900c201290b10092a07450300032141500560703440c2019680e1003040264158461142e52000d080001e1a1b0f00102d0b441d501036049410b941d6078130040c00b40503c1180e4517194002002d00c01c2e200a4902600724610410f8400152070100744d4802d849080354110b221080c02280e1102070704544060709214140800d0581c0c94180040120716001a442e070b10050030000300e8940f585520308a004000320440c41591203007102315600d0b45018a15074503a047c3d80100d13000048821501c040d6907114038801210720500d28081c0c03045d0380b500c7c0d540c0b0060f54049155a1303001198807100c4d4010401105c51120304d4040803000e0485883d280d603400d161000c04072400b078401d4841d180000241840000c10a1008a0030b48 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 904144190 1250 904142940 904142971
    0x307170705090109020a03060b0a120b0d050123060f090708130206040b0a0207090203010509010e04140a0c06020d2d030e0105040309030c08030708070b040816051c090e 74
    0x280000d0a045035a00500e8101888000000c1c2500380c035401410034132900c1c0d03410444507456402881c0240b140f41d004000203007928490041003071081d072002d040c86400601046450f0050303078030b4038295601d28404c55071500744100b12513000544083d040b0b500280c1100d00318503864207900040c41099014040310100000d00c8000b0f034501646000300203070b185e0007c11035600ca81d920800c2e40304903803121582c00010b0062503c00504801c450082d01d058a40c0100710001300e80c01c0c015841d00c6108014000e840600d4042e006c004405401d00009030524016056081da032400c03e44080c0c075014401c524042044401f15100f2002c46441a8005ca90901024013207002c5e0000d10040780a462030748981c81107540b91500340020190080c000d0382c03c0707030310540800310b1607542c07800142d45a02a040c0041c0600341d0400158000607003040406e680a803240039124107090040000302e8070001c031882e0440d900d0340140700100c2444000c644000001c20707145011035107181007114061415401906004140301c420 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 904145440 1250 904144190 904144229
    0x3060302010c060c1106190b010c0c0308090d0f060b010f0e3001050f1501260709030b190e070321020721061404030507020f062709010909020307 64
    0x45029820201171714088a441d424241101c039903c5040c1100100038500d03048449003654012001c40402a8201c072210041d02c0c515180c1c0c540c2c90b40144089a4400c1120103000c0020341da0078000102c6501485000440403100000507160011500c1c6440c140b080e111003001e6240e07515089000100107090014041007151040c401004c000343d04030090b10b5003014104800100204102441140001012040254840c0c0103503080a0051054010016406203607031154208a01503034000c3e1a03403400f20f03080d99507078a996036500420390b95008220700c0c00241a804501c28052840e0b510040301c0500350403440c1d951100303112003101d0b094a44140d103600922201034000c3c00280000d100714030b8400c5415504a004009941d4110421550345d444c002c24402c07988981e8012034403560b850f890302031800c1d4858081010440c1080081b039401b0400700204003440f10505418082c1c4107084080c0c3c0f040c030510908000050300143c120050782d134501800d940c09650b001411208403103243c1c0d5101c0e000900b4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 904146690 1250 904145440 904145447
    0x603050f13141212060411131a1c05341416141203040804091a1003230603030304032106030803061002010b010203040501123903060302010c060c 64
    0x22020f6503069480200b90500f201c1050003489114100c102c6e000c100e204010114107080d8000c2c658820800208150240100c14040b000041c400d071036400c031181070004002c0e03880c85071204100c080d00c44644072020310000d08201502014114140c001c0070340d039410442d13401c103c80303650300c2e01400800061440c07442541c4a138600b2140b2035070425a400040c286035003403001c80c4a40244080e0820f206400340c07104a9007203d070030780b4010341c0d20010b0185882c3c03818500e02d0141c103014540000c2041c4080e100901a0781c4d40c1038055804540d61800b04d200911102031000e946aa45081d15003410240c0410406a40120440350300582c1030400c0c1d0b00e002c0040706014000c0007a034044926140c9010408020b0080001c043d600c2140704460303004c083c40010b84100d003a100f036841801e016034411f03c814011507020318085203020344900300c00526a90060b404400c00504400c00315070315172121040c11426030f10700e0f100015421003070a090100c10b01d0759000800d8a000200301911069617a81c1030200640f0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 904147940 1250 904146690 904146703
    0xe04020f090d052107031e0e210705010903020a050d0f1202030d0c020a050d0e0d0b150a08070605040e0c070210120b030109050a080a02160b040603050f1314 69
    0xa001007081c8429890f02d00d50b0b40702d0301c444001c6281404020a8101c160742011a417090380d1507035420303503000a00d000d01c003241c420b86c1c0000d1080c0602c1c0610704060b42c6401c1050018000701d50003803800703100024405400c4c00c016401c61410001059001d10150701c600e0030840440c0c1e03080e903500b08100d00c0d40c00c02c4070444802c860010101c4d4812034030203020b90341c0000540030801d070400040000f18001c0b1030a03a942c201205004103641c1004520014071802a0600404040d024015035200203a540d1075103c0100200e03800c03156403111713510607002418144013102c058011007000380003250074844054528003c3d48114a021000035000802201454007a507a4841d8080d058003844410100058a0345e4401d80d10003005a181a00c14461464140507080c030507031304900980300940b0aa04d50810a0380700b000000d0651141a0312041e20300005240340303008041c00c45005440341d040100003170a991001c6d040030454584c500620040c2000a90b9041310309900c4040231a04483d0200d4203401c014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 904149190 1250 904147940 904147957
    0xc120c032503020301050f010e030a060c020c060a03060e0c0f160201020c060705010c0809060112020d05011401061e020102030c042108040f03060f060b0f0a030b06031305010e0c010e04020f 83
    0x78600d051100d0194164001c0c5058403000c803031030081c4424032001121180c06200409505600c0580840e02258185e80300c0034124061b441601d00d01e081c1480440c16550088850500103642d070f020421100c07042c442d043c0d42040e01c0560061406044c1c101080441c011007044102411b00c0c044403030704580c001c00801044210161141d034595882e410403034001d08114a031900400c1030000000c41005004c241d05060716024442d00808260035000c0c03104410680004981c60340d80c5000040d481d1407800c500714000c1015030341e9480045402110001400408140b503010b581c01802071102c0c1c224401c2c26203040d035400c200613802c0b046005844c10180c00c290b2101500710000001c0108010b04802600d034180ca0050f0000d001541440c00c0520803900caa10618114140500001d81c0400148004044c12461481d011410440c103070002404c650003980c0110020301e41e070506204000c000c3c062604c040c444200908448852000081c00000b4009220352103240e001800703001149001d000c1e0307174441 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 904150440 1250 904149190 904149241
    0x31b090501060e03010e01090c0b0a09080a05060912030601090b0a021c090801150311040b0604081207060b491203050c041d13080a020606090c120c03 66
    0x2542e40303602c080c0c03c44015980480c065400d2035a03807600c3c0340050042c98241541b043c50247c49526180c0011304c1508444c13990b00401880c150001343c410380030022480c0031402030010307040d1130411599941c901780d011040740c03015140c207204110941c0e030403116500031102000041c0703603074280d2008204c1c02c0c04c00000751844a16007403d4510f41d03c40e03112a060b400c0e142c86a000700840c148a044494150403640b0004107103802e02080132aa80c20260030010840300007406e00b078106500c8414090400182c0c81c0030590f503107008120281400410300401d01110403e4582d00c020b00001003009541006209401c140b04155112040d41301c1241d500121010015440788a0032501d40d00d01402d00044112101c0002030400c00401e00340080c4400721411252500800b8050858a940043d41c003c402000c41d01007400100c41e541c049089400140001b5002c0d90150040303141c40410404000310241421010350030a1000442034030003034802d15004a0780081c500d071295902c5820038501000c0d451860311a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 904151690 1250 904150440 904150451
    0x60e01020705060f0612030d09110306010311040506090c030633130f05061e0f2a190807020f030d020304030b07140d0221130309120c031b09 62
    0x80c00000f16800d80108040c01003000240c455000704030411072644070300752068000300884048141070b0b91203020014441c1000107041151000002c2c1801400d034415201d1300d09840440d24240383c11b1084c140d1041003283c0c40d044509002c081400c40d07000080aaa0103034480da004090022031158190200c141d10304200c3c000050369013520240c03078110792980e05800e4031a03d4041000360303003030551070140e40002d45810b09002c44400105d41c101c1119a440000f41d50400981c3c00c10b00104004040408c120740c0c090454840c10000c0305020301004500c00700030303082034841e2001d01c0100e000301038006400056150f142c055600003d10751954019810341e1510804200c50074054012001e0000c0345d000355407059640d07981d0f80d41555210703005502c9d81c880d890308100c02c05070701c003442d8054040520000d2100d002213000b0349001682c140e007034500b204080da109000c00100f550125082025181480c080900b600700f650b00c000008441c0d005c01001402034040d405107200744622a18000e0030181802d000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 904152940 1250 904151690 904151693
    0x2503080d0915020d050a0b010c1b1809050f06010e06040b1c11100e10050304081303032111091c0b1e0108150c030c090a150207061e0c060e010207 64
    0x2944001040c1052031700b4400029034501581c40b541240d00d0060310390940c5030541c0e981e07242104050b8100002c1d4171070a100007150945001d4041a01e85004640014030801e040c102203151221007801495141d0000005000c0b91811fa9072103500900b01f55004208105200001040000034544007806a0141220103040c0160740003042070322201900d203001800488441113442900094a081c1c0000711751400e100294440d000a540c824001c41d0302500380388441c0c0e20150744089035882a00061802220700c0b000102c80c91401e44002030005c010070200e01180030480f124000c00d6201c40c4581b1400050038240b00710f8040110001c4d5200210038003d150009200307810b101c0f84950100e41084200000c500c0c602c3c00905150340c441c94103031580c0c8907902e80c0c2241c8050350004001d1071482c1c0c4144000c1f402a1202d9184a0240c80400e403444e9100020a400a1a142059100e2130411031842c4550200000c503251000e002200352074158159200390410034040c1c4030441500c5030940c40000d4140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 904154190 1250 904152940 904152983
    0x8060d050f0606010305160503040b0408040e04030908070b13031506260d090e060409020102120a0207090f020306100305040318080d02072309060f040606112503080d09 74
    0xa1043c0f109890402890311804c0c100703034010782500e100d400818401c1002c1004600c4c03481410307038814859200d0900d016201c00d04202034100584044000c0307141c0000510120b4401c1c40400007074407a8005641c2400e62110b01c410305141c8e107120181030400c0d00402d0207056030702c0e81c000d0800340182181c1c54004c1320503030410b0380d00d5025030010034801c0d006118041485a205400a8044408085040b602502c44400300b20041803000300490541c4280c1502006000d4001c010300400c1c4140d402405003c1d140000407000d03034118441c14046280b0420400c0a00d5031028024050801c0510340010700c0d550700e01d000d480a501780426900841540080062550b400285c8604603980d15030a072403441d41e9907903848819000c1010f0300403c800c206c1b540d80d0207500301141138561018000f04400c8150394400c1c04242100c034980c0210002a0540140c0b60b0100c00c1000718062101340758000c580b6009176228000841042e50000400381e510025500c80c0000254201d11b02071a00200500c41c00341d5510701c880c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 904155440 1250 904154190 904154203
    0xe0a0206090a030c0f1404020306220902030d020c0415030201051b030c03041410020105040b1503030d020d050906070903031d01050931090c03140307080406020c0f190608060d050f 79
    0x103001803046c4001c14078880c1454020781c0d0080f40c0c0980700e050720441902240550095071070391171684660706c0c207440c000f69608115100c4032044c0b03030300903025010b400d030705200030fa8070158800d062a0307020b000c0410050340d100381210540b0094007400610250900d022074114811140c00d1419403001040100704990350004114812800b2158031080e2942204142d003030728000c4030094801060300300001e508103114291a40ba4410041c10781e4508481c1d0340c2a1070490b081980541481541c03042045a1940200700e010b400c002d4904020f041e1303038910f94005003407207803080d04880201a00b140c0c0d144103900900c00e860b4038010085c07907210000e603e1409071135400e941201f120403000441284d00240c940904c201201d6a40103548106090b0031615801030725000c0c0c61407080c5a1108012040101e2280d1010300050021540a03182c0c038802d0b00c0400100101e142e010300e114040c840e1031102340310760180e0b00707500326101810006100e0740e40000007030180600740d101070851701510710403c0d11107201060340c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 904156690 1250 904155440 904155449
    0x504051615120b01120e0c0d060603020a441504150c0c080702010203070803100806151e0a080a08031b070f030810030c0b030403080702010e0a0206090a030c0f 70
    0x4100c032002e04140d1541c140c0d02d25031541408a62a00e0310042c112038590017024960003118100c074031003985440400c500c507810400c19a143d50351020180114506200b10000801490000081c94000c00d913000031031100700d440c2c5d01c01403401c40701c0c4012210640c0c19000c050308009426076140d00480240005401000c03142160742048440000d1002042d070300c60452900c1c02ca9403290710301d288690302d458455000c1c00040c2e0642c403050111100140136900114403800514110350300d101d02d042c00d00d500e002800f03003c130040903451200e034020b02e0720742d00401c2c403107080c2ca185240d65080300440491205545a0000c601502807084220140504807008601032101070b02603a80c03c0c031260210740b5244c018808000d1004404140d4030010911a8220f203800039881481e8043d115626079400b03580c4002540545c1350000301104000505402103031740c5a000e82d55000a0160070110b003616a03c031001742d44000c1c4140c0e00403894071660740340d24400d02d010b1584490b05130b0303010b511628440102c01c6217228 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 904157940 1250 904156690 904156697
    0xf03030903180f0e0405030c0609070602010606031416111c0206060a081f1815241502010b0406171c0e09040201052110080f060a0504051615 62
    0x101c550425101800c2c00115202c040844502900702010101e980c6400b802c181e4081c401406401a180d10501042c3c1c0102009001040c000340341410180c2074550a0344a031003810b14007000300000c2e00480081076406101401583c00002841a059a01c0441000d01d00c0c114890342d2280e140b546c5040040980d101a1a0201c84d035a42e100400c0141096a500bd4140581c105c1241d111032050b0b4a032024000c140341313000104400d40255848400100142c00503144544040700340c200c240814840c1c1d40003212900115100408681200c1c410160541309850542d8106c00348024554800e41c030816180340020f0041c484036548034914030315008a2064101c0a01854075041da6601074850042000301040c0c4504602541f0f000400c0010038000340142d042c0001042140d0000c100b20149020b220084021101c00e81010b043c07607880c10f03010340c10014142e8440680803488410000b22240d100388103803000304040d0303503601e0702c24103009001b206140b14109103100418818041030003c0c1c0607442541c0d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 904159190 1250 904157940 904157957
    0x504061e020f070f0c03080f1c0207020f01050f0702043902100911061c0c03090506040f0602090604080105010e0705091f031e0603050d0c080418090f03030903 70
    0x246454202c2c4120b02c65a01c510104001c01c4000a4101144ca0000b03401800b640c42d0352541c90300c03411041d07406007000c8001103000040c040105642d03040048983c04001c14114204844c950202d419415030894060600c400411601e07144204d40049903078041c1d0142092044940d070100c5050240e0140c60440c000000c441107800c41d55a01c181240003181096004103145083d8a0241000700700541041e101101210b150f11215191680203003800d0300381041c9918a08158102c1b0004c84e080b1206580415082c0102080031030000100700b83c00c1508090108615000340c600700d03009124509945d80c00100c042030001e40607006510140c100c41c0e208460085503501c03107008913100d220b1010070b942d006044100e0a0307022a20101c03a82c015020600380010142c240d000074903075641c0c545100182d102e071100c0080c000c1000901041401b21610700740203d503840c00b580c03441984e0044d409003100281d00b000c18079210b90b81c160041041e15400017204612071006050007000791101600580c007241456 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 904160440 1250 904159190 904159241
    0x1902071a0310140a050904080a021204180b040209150301080105011a0d0b03100f0c180f0e0c090d0c030b10050f06090d0605091e01050106020c22050406 67
    0x12048034801d9902840d402c19081c1007036400402504000c1d0540c0e041040e4440c0030405031540d5400364002c0f400344018903140e40c50001c0007468882a00c02e009901ca40c180000c1028148802062210551004010814286a0010034000d02440982ca40c0c0145a500200b91000d82d0344001c5050b101c420000b070180383c0c1c07200c070600c2c030515500d03691035100d81080060864000d1242d0002e1204036004050316080c2c2000d2102800b0740c1e111030b4150444a17682c0c480000a940c101c1c4107000d4480e440801070700c1d030b580b518a0038448500e4600c0b900d509a04c500c40001c050035040004c944c00f9a000420014492005050680c489a5140011243c8156a1002c00c0d403140440c2c0c440720407140c0040c603d181c80b180c4102440095000600526005128200da8400180580c06840d1040c1c3d2000010101d840e580412070154468000c44800386902d0000140700c0c1c0341d408901001203200075148000c0c145030000350f10746003d01559808410311b241105110401156402840d400c4018030384010b0041c3c02d5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 904161690 1250 904160440 904160489
    0x30215010b1804140a0b01170903030403180806010e010501090b131e050402070b09060f010f03020d08040b030a092a030f05120c0309090f01030b0403030e03190207 72
    0x2801480e00c1c0741c60500c1a070840105200300282d4220000c0d0011900c8071140312601c402d464203440840c107070b546a1803454119644034440f28260048601c0740d0006d82007041c0c5145e120300c00070708013504002109401c5c04044410560980027800404210b91841d070390b0307096030318204100b80a100c0c005010843c00082c2c02d0004400c1c1c540b494400350b55026241d01c0c280e072a0b4100e0030130b87d14480700303000b90310030002d441ea0f00c03840039141c4140031740745450084ca45410b440c0e00705000184204001480e8200602c49900070f0307144903040d40e07415604101c4412013030805c0d90b4140034175806018042030020400000326060f4010b000345621801e60000c14070340c90b201135982c14541070314194015915040c2080800d49552801c544240200140c8100c42c480cac1407010000d0748060700130415544005040070309800c0c40310241d03500510110002c0300c6d0f941941c0e590028410007074400350406444222423901c28006004551304c030924803900380203050541c0e001a40b40c5000d4450007101210610070480c000d4403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 904162940 1250 904161690 904161733
    0x30507090b03150109180f0b1203030a1a0406080d0908010c2304080105100f090506010507020112150f03031206080a0f03170c04030516030b070c050a021009030302 72
    0x60044901c0d065658000c0644800e654114405040001c1510001095020602c0f00524014044004910500e165030210709a0300110b00c0180500c214100da600c80a4022003981d0b08030741c002401040440540300c02d4000d650000b2002a8042d02c0d181c00040e01c201e000403204803000b038540b100d000f495624008503080b1042040c07044041484c50b100b100f031a00700000740080d00505148043d0030192102c00080c01c450040700c1c00c550440d0800023b01c030700e0030300081c00ca00800800d0401d00042c40c000f00001c240b0b0007500c60080c140240c060121064494a0b00000c00f05500c0c103c40601480d03503890300e0045050b9074407059000c110b85501d0344c11144554007504040c0c1e40c0b02c80c000c0007080095501e00040703840f1084150308004007681e2090090014a0110740110049001c00380c5070b41c19401c2140c00d1007645020f02413403010040f0204000f41e02c40b0071b10356121446042c00e0054140c2c5050560400101240080d030101c0d4183c0b095400303d41100d501c00079603000c0d5080742c103c038069a580010703802 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 904164190 1250 904162940 904162949
    0x30705010c030e06130e0f150103110418022d09040902121b040c0314010614120106030203071b110f030102040b0327070b0304150e01050901091209030c15050c030307080703050709 79
    0x11a1486e62300740a50081d04010164208642d042d0310b05907803040c126000c0300361001811082600001c041a4490012411a02c0035510716400b200000d03001520301541d225800200d4061500c030016041507541d0340300c0552003c00c11500780c0e8450085c200d8022071283c00c00110510562401c007031101400d200b4403412154050744500a403084e424141e0586a0a0f400c500010449508004490386d00d1000f0b1003c81c003c00268501589906000d100a00701e0140300c0c0c100c40c444080d40c400003010410300c1d4050110408180c3c0c5410b11600c150010a01a100e55000300008620002c140450b0803002c048003400b44603039400c031050321a0b480d8101170f2900c20600c40e80340310603010f0002c14040780e42a940c08a074007015400c009015840100d1791800e4540440d19655640d6640d035500060001003890400321410505c1e0108120f030540da1400c80b1030ac118010402400d4a851035030b0400760144081350380f0440fa0100b26500d901d0402001000c1c008221075000002e030610010818403030080400e0001d5070b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 904165440 1250 904164190 904164211
    0x191503061812030b030714042c210d110c0a08040e06031501060f03090209070809010e010b1c050c041d0f07050f0d060b09070201020408010e0c030705010c030e06130e0f 74
    0x10314200c411014080d10b00011f0741e01690f50040403114480c2c9210b55019070416403030031074005407504401c9051800040010280303003c00c0040c03d03401d940c070204460b0b13924107107600000c01020305164005640544c0101c244503108142d035000a100d1890007500441e00c02403460702c1c1541e208420b150320780d0a400e03105080016404018800780d030007008207842d888281d1600003100c10103900040c2001750107594040c04201d00c80144050310000b0b004150300820048024041e0040c0540461802c2c1036101c801540c6009100034001045003d019030706111600900500c10030310b188001e5000351b564042050342c0d070304c0341010a401d410230201d048000c0310401080d100c00500e400c070034090001c0e0b405000300c640c0c951320032141c2056500e0400c0d0b03c3c01038860750300045c2c4807428401e0b61421070303c884030424036649c06040314a0403580d00283c0c03041500e4007031a148844820b01d00d0150f4000c10b01c146030580c001c6000c100c09964107400c0210008881c011086100e00752151a5458041c4c03209941d0a0f030301 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 904166690 1250 904165440 904165453
    0x60109090503031b0d060605030105010f0201151809142d07180f0504050c031e0715180b120c03040201080f06120307051e06191503061812030b03 64
    0x483e5012400c41040345410448140b502051716500c2c0d0803200a03812030004207101200603c540c0d41d01250b05440c1e00301c2030008100060482800c071012000900c1140a0311448030304401c07202032140c00c20940340d07510005400400c11124034035a2a6a1491540e440007410200c50004048a51401c255031080035406405072608008c0703a21034003140c048001e03420903110078035025441c500b4800c1c54451400760f0041e060300d0413405e00b01800c050007001c03544800905401c0a05c41c1ea0340c0411302d5070407500d0031894060364810b165000d84000001c1c1360751204441008000140c928840c00090000d404c200608001c6940d902c01b00e01058002a540680050000c2c00001d0803403544a0303056070050030080401e030100310b002d4080c600c0c5912854040712160000e81c540700c1484003a100d200d503508a40b5000d010586040d03901c00a40c11260131803601595140c19000002e448005140c0c8091b6801c05428001200307541c3c1403054210221900319000c800805800748104d20071300c20340c41244d00040c0a00f21 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 904167940 1250 904166690 904166701
    0x140a0905010e062124010e060c010e12120705031306110904060308040311060c0a110f0d060903121e0203090313030f0b010602010513030c0c0e010605040806010909050303 75
    0x114502c5444541c0d030803a03420032030305020030022101505049802004007020b8030b008400040100c188200b01c0600310182511040907a80028401c00d62400580300305d5180c2c01400100790151801c0c252149660050f102c04070104100d010003464103585800c4a40803644814804403050320007100c440c0d00304030000580200051280d004013210035150820035042c07802480004046880e02d034002c4904810024080041290103084021070305421100c16080041c01200c00b034580c10130600c01404000c0c1c000c9c031601182c1d580303c0c50700382d44600503004562a600e1458420000c200082c8140d01260100c0340d1086191228000d10b1240e17020008003070040960000f0101c0607400240000780715020900c03d5046854600920000640c0110302804031040141400d20480e003060b001601103904200c200014403403100000480560700d49400d400c0900c02e402c060100034066003114902c1c041e04000003c4056100001d8001c0d03500b843c0980b450f0b40d0769549000d045404400c0018900d80007480005e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 904169190 1250 904167940 904167947
    0x103170a03110c0f010b030106060c0f06060b0a05030703050a05010b0409111b0a021f0926060f09190f1707150c080106031e02030c0d020304050d140a090501 69
    0xc860024100842c080b002020719001c5500300d01000001070307000764601202c05000740a15035071414141c000304071300c5040c00801414000c0d49000500780d2503030310b841602040300940c4041d00038291512926169005103000400d960702c00d481020002e130070f10010aa500300ca921a90b412119241e400398a01441c0070107040141c00380c014a5003660b01e05100302003c030144d252880e0408481880500380c40b1290340b040040d005015501c0c107503185019032103030b06d20b260008a00001d072411000350310900348101000800800d201650788045014043c1407010281100041500580303c0c40b0581d18a4410440410b400c15482103021b017160121404050105140d000d07810183c1c1e803c00102881c0c4103e64403244d102032200800201056940c03600b01d40380550000105014160b549030a00003042c0090320010401e19102c00f40301300c0303039001000c00c14200003901100c0035414080c4041d9203a20386821300c607486014001e03000010488991000ca83d400000c811118615559102c20f0b003182d04000044 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 904170440 1250 904169190 904169197
    0x9090703020108090106050d05030c01061509030201031104090207031110090b04021003092102010b06030603030d0b06040f1404060b1c091e05030a0e100f03050c04031e03110303010317 81
    0x13200d5603102000324a9031902c0c007200152070f018500030b65480280e0102ca03800c4980d80d03480080080b5100040440d1240c0c4520b501c0110b0703809180228a1188a09620101384601d90012203028030000b0b14108040d004402d41711003040400540307801a10390212107066030380011000303000182d42c100040040c40d00902000c18101113140005810680b581c1c0c2c1c15a126031000b03800c10308000c40007004503850782401000c2e6813200170750388503017507003403003c00300f9501e0041c1c16001039416229201c08460307032210070941d0300621081c3c1d6030441c0c06a6030407505042803080451503001e1418078901042411000080b40d041c1c402c84200d45039060072031004000113199030b00007107030f00f810000e4050080102c1d640a41102c80d000f04003030f66450181c2c3d800900450011b00d01140a20f682d031516902541d00050806000c04c05811f000c41c456603544000300e0140700340c0d00001d104e101041004964604c0300b081209074248a03407600d84545c60010100c580d42c0c04244002881c4003070a08440040d0791044015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 904171690 1250 904170440 904170451
    0x70e071704050f06041a01060e0d032303130c05090103020d1403190914030f10020c030c120405100305040b0a09060f0c080702070f0e060105030606130f0501090509090703020108 78
    0x945503c0400568280c0c24500e05440988800c800f0401d580041c0e40c5000100340100142d04112490b8000c460105d01032000070400a03041c0515030004454449000d8035440700b04040c00381d000d940c1d01d440c24803404206000c28040d00c1d0240d0036000440e084c10400003050580344c00500e0f030340a1a1290307a0b0b0401d181c130300310191509170005200c11003550141c0d030051180022a030b103c0310051400c0c880814002c40a09a11500c2503200080032600c92501003103c011041c82c031903016913500031107040e49155215880c100ea05030f125452100c04000c46107805402640c1089841c3c040b100e50041c0101d0954000780c4010307000203d010049400300c07095078011450070b84180030104401c0c01c1c49580c0011039004000003c081070007081084210760f4148a6a0054008100f0115410303083c0b48022130755580003040f59040c07110001c0441c00d00d82d9600152015079074004055402d0540310302413030180147c2486801e0100300c200e0320100d082d140008031188034084250003483c1d500e2560f001120154405480c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 904172940 1250 904171690 904171693
    0xa02060a05220509090613060e0c06190305010807080304120c120f0c080a080315010e0d0c090f0e0307060504080f0c0a170901140a02151503070e07170405 68
    0xc2c000c01c4001c00060b000b400e40c55940c02100040c90401802041d800040c40ba88150b00408100104542c85d50b4500106540140b000515030800c03040307191500c1c4030605071031390001c804a40041030b1840500204240e02d40740d07405001c03591380d544440c0c0e40c40d200c03400b07421503542003400140071040031844240200c03402200c0602800d07948245944001100760400e584010400302c0013414804855003100043c40003900801c2442c006459095480c08050076805940e240e0000d8070032136070300c9051002c80e980c0000300462810f621901e080c0d003092040c0d21034007004900300f040b10143e410280c0300d041040038080e005503140007c2c41d030b142c4009020040c0116403d071414400d1400400d4000c1c040c001414904004010319200380c03c000100100002c40300545220420198000b41d9004103131401ca21003800c1803a13100c0c060a43c0030703401d20442154100040e1805000c00000300618010407500d110154150b031407040c0c40c0d4081c8148404220340010103e5504001c281d422890300182c4d941c0580602d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 904174190 1250 904172940 904172947
    0x1c0b0c0d0903020d0e090c0d02070501060801050c070b0127051b0d020901120203060d0807050f0d0c020f1e1005160c1703070b13030509031e0714030a02060a05 70
    0x154120100c0d51440070941c01648071100c1d5501d1541c0280b08241202d43c11964410781d458070010061083c814200c00c980d0300c50f0080703060010001c0235000701018004010081c090351800d8407600080c2e8004036400d54050b0014400028000000c1a03034007080d82e4201511031040c8a0007034020b02401d40a881400741e80464200070b55000c20f1705001d403401a02000d0003696500b5500c000605040480d0308000c0c47c284104244080799a5058401c54010751205d01c0a4407103c04d07041c81d07414241d42c2e0f120180207010b0110480406070307000e185440c05910840c0c124032911001c60900c030740302c022200812909800810000c52518005401d02403681c107507d4440e140920b004403660550102142c100c2c0c2407a82c620781441036101c0711f0400300540740300b10000c40c01d01ca42502c45098504025041220004540280c08240362050301150010b62014080722003900d6a0700b07041c8146070700319a5100881c0120310000c214803506a0284090380c10040041640f000c3c0d42d000c000715940449008400d029007017 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 904175440 1250 904174190 904174207
    0x3130f020a03030504061205010803041415040b04260604060e0f030d0c09080a081e09060a020c120109170a17010609061407030203031308040f0803090406051c0b0c 72
    0x540741c00014501c2551007540720352910f03c024140c100f0000c2030000c028105401800000c0c00007065400300d030004082900f00319601d1010800c4d4080c1c0109980c0c0d60b840010700400d1180c1d260005008550310301d261100e2507c01040c030304022030301043c4821a0340d007081002c1008a8402c1d0440300c943c607106820349d103009900311010703855075020f5004040c400b40c582d00810001504190080020040303e80500840c110f5135860303c8142c4208a10f0151500075161148001c0070381030142d0302440030182c081551090321a038003a5854a10402c0b040c407501919858042420040c090207206543c1f207010b281610044034106103854000fa010382c0100401000400c11040c4604940d50090200342c8620581381c0c02d0a00040c44201124060071400c0810090017001948c00000c0b80e601c5120320341d40d440c80b41c02c4d038580806988220b038440c001010175040041540308001c4018210b0034000c4604010b1155280140480440f5a240e0003041e4079109a016003c2204803c0c0d1980c8005040501403401d100b5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 904176690 1250 904175440 904175449
    0x1204061b0804120f061109030604030f050f0c010f0501091506140c010c201c0c0c083f0406180302090c1b06220302011503140601060806010503130f02 66
    0x80f03106a6036030049140080a001c0c46102d044101c0c2d5800c61000c0c0b8101150000c6070750780300c0c080d000a041060340180300c44210302ca142038030721002c101681644c1d20411140503501908a015851110381c0c80d11000041c4112640715604001c1c1400b41400e4204d441d05d007081d60348181c01d003602a004007041015621184082c403c0b150309501d00d442e514240458644c1d0420200541110500c00d5440070980800312000e1151031109260a07243c0002a4030440c6400b43c1c0d2523700ba0312200151084140c41c2603440c4a00c141d170062440920410302c00454200084041c19030b0b615181d5800c080e0411061006501c102520b000840c843e00030ba0103101da4aa0120311044404c49001c5000d03640407803034840925010001c0a11800360900034182410b000c260048451660160804015842a21030003003500031341280302c0a088484c0319206103583ca0410000110000c082c00358280a094008140c1c103004520090007200180c1d034050641d59001c08a0800d000700890136186061102c0300100107944 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 904177940 1250 904176690 904176719
    0xf010c050c0901240c020d0b0c070605040c06020d1b08130e07021005060f01020d0e01120e0d0f0206130209040f05100c0f1115150913051204061b0804 66
    0x1200a440a04120f86002c158842002840306138104500c203000300780565034001800101a070052046102381c0c903403109200f818482c60000501950401c03003044140030b03d185840c8100c0d405502034604100d980942110440802004444805405a42c98011030b035410090180c03240610b41c0081c0721611442403205121046403484010780c00340705070101e594664019950424826190840c0c5a40b403240041c3d2501a0140c10104210307a017209500c0c240e100309000f007803401f01d030b40042002c801402100c0743c403204151400000301e10281c1c200e560700c40c400100d080c440c40d1050b08081c0c141c0403a500304402c0d040c020b40160b5a10340510800000704a0038030102e141d40200c0000040c502c1c041010241548a43d1204a0b0900000902c88040198042201d1001403003041ca501d070280d0303613a5a03200406d91010512a0412044002c01080140301c04820b8000c9004004031036103124041c540d108140b1440c010704000445045170074404c902e0003007250343c0840c450002c0509040d00d81d40c01058802b13 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 904179190 1250 904177940 904177949
    0xe1b0c16180203130b0405010b06120114120d0305060103020d020a0201050a0b030d020a060b0d06060e0a0510140d06060810140901091101050c0a1b1809020f010c050c0901 75
    0x151800020000d0036200000c0103086008a4002d50841c60501034a42d030144030150090304000885000030300b007140a500620110030018082030f215522100c84802c06c00c000d00981d0040c00f08203205465520704036071001003011058000301180141c087c0110040d010207002541455001e101400d4658120300203442805260341c000201480d08160310000c1d195205d007824041e0700900030720013001d41c0c007091110036150050804528049000b01055aa4224841c05000c45e0b1525a000c9001c0c104841814040d20214909004c1a21001054841b0040c1880342c1c18610440d441c0503d0304d420070403d004d0f041c41c001c0030f0000c1c00c946c0d1070310024144202d0744040042256120500140c4500380450320350050310107402000349400740d41e6a210b00d4041352501d0742c18018040b1744880b05500c00c110303205605a10071402c03010b607800d405c0f1030340c0c69403850300940c1d4600d4050896501042c1c52445000030303180d001030580c8107107450340b001950500c840381400c0c0c515001e40f0303101c03021984683e0007844c001c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 904180440 1250 904179190 904179223
    0x903030209031c021213080a0b01030314181324090e0307020906190314060403120506010806150c0f0a0212160302041a040c030903090f0e1b0c 63
    0xc607001030802d03041c0a800401d00108229807840300c1080b0ba400160ba0b00507040e80340340035076110340748000788500b048658421841c0d071241c0c01002c001c111808000c28100ca01c00d0b143c01c180700102c5c4401d80814001e10200e028024012568069503150201c0d12001c2c18503072075000184415105c801d20155200105900c20001d101601084000c0d101e04c40c0c41170403030044c4055410405254005644284058a02442101150700d0111131b48500c90b100001558041605c0c80c02c0e084100b40951250012201580407802c04030406003450b00c0f83c0695886400e0580d0b55110301d50b280c004102d810012650b00c0d41c50380c18144100c00c03601900f0056444810003031b20042a03042081e10410058028000c130364407190b00813440142141101e000c600e410789504980214040000c043d02c54204040200305541c05401d18490380340d100d4040e03102c00a407602076038400010580b03074075500050144d80d201d020110045540000da0120814414031121090110014948401c500340b40c6d207890b41550b002d0002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 904181690 1250 904180440 904180447
    0x803040812090d0e01020d0e090405012405041802030a03111c0c0506090d0516060b0d030e0a21020d0215070c0f0e040c061b0b09030c0c060c03092209030302 69
    0xe103801c8548604e916000f44018000c03a1091400104901407104900d80255221008202040020340240c05510f8a60040741411001003003100d90044c0d0522a19000d82d00e0000d45110403040e0210310100346030090020500d00f485c80e9801c5607071903800c800000840c010708488109001e0706801000189a096030395918185113400c1031800c1500117030449403ea441082425072031a0410251545441d1058000f03941094a003050009000c001d84455400034030b0711004c2e8101034100b202c5c000200802e844070005142c8412031320203070750342c0900c41560650080c10700301d005140c1080340d007038501d1018100400f0b60041115102e407a40240d5030844005010550134004d203000c02c05502d00511450852415504144d01c8561040c00700f80500410081518201d030008030150941043c100d6104414007001e1038400c020743c1d10303500403030301d55441d034000e0032102c003100d1078020305590b03c1c2208000071718070304070a170810040c480364000b909600118140041740d8442c1803d20980e81c0c20341c0203450141c0d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 904182940 1250 904181690 904181713
    0x3030301091a2704050102070c090504050c040908160807060f02071e0c0b0f0912010e0c06281403090705091e0703020c0307020d080409050f040807080304081209 71
    0x640035a00748118001e005100b180e6154622680000c00c600110755000c0c3c900340c49900b4805c3c003900c503221001d8140340d5000c400040b00070055005600c030314020810760752010b0840041000703032203101c6d0018100da4010311071604c1d03907031840c411980c02501c41c4020b02c2c6442c0e02940c404042e08c1c0c8150301c024080f81e001c14068203005214504080e818403201c0d90f2007130f61050380d4854125259600a80c0c1d070150700403519248103030318041266448000100ba000d01d49002284440c0a8031001003445104c0c090514000c84500303060b01500c1c150035240041c00001090b1b21070300c0b010820107080d8482089014119641030118100045020b5040300016280b11410001440440d07100507084854640c4a583c1c550414015aa10180c104115241c0943d0b91004203400c1d40c0b45005294000c0e6002490311051401c00c01580d0007481280c8020070280070607a0341210b60703240d600040324003500c1d0700d01c10400c110000e20300000645d4020b21402c0c0f51400d002040060200950341220741e000a980b00d500d8145 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 904184190 1250 904182940 904182971
    0x2713060e0a03090e061c21050405011215030b0705120105150904150b13031a04080a0302090303040306060b0c0601170a060b0f060a050d0f02040b03061e0303030109 72
    0xd4402501030014a1086416680148109a1031161605941e1480003183e59a916500180d0300d15641420b07040207099030703003030a00300c1a0038801c0a02a11244500c00301a00740a40c007079808452058440c01000c2c1001003588015080b01040b81b04040014003002c070005410004450041001d5912907441c0e8015124041d0407400607000715100ea0340422005008400c80d1003228445407082d01c020590b814164a0030a001c0305036040910074200119680d0111500504c2d95402c1300c1c054590034044c40210754503602d10a07001d03100a0f0a070801046107070345071800380d00284000c14001d401ca07842c159403510b03607004444145d000035001101c0014184c00600c01000702501501c40b0411050110034101e8a295840304040402000301e40c80b208000f43c00da4403500400d0251501130001a1b540140300c80080032a40200004400c6d1850308041030703100a030a01c20341c0c1c161905842074500e5929100e003040a18881402c40c450030611100041e00c440e24240060342c000c0c0303620840861401c20480360603 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 904185440 1250 904184190 904184201
    0xb1813050115140d0f030e0a08011d060f060a0b0c07120c0503010c090f052e030507020d020d020a140f011a0406050906060301092a080610020303090606271306 70
    0x8520401c45202604086001c110317240c1c000c55810305120840710024008a1007650f26940a8800d951808540307103401000e000351544440510b005886841d07548092100140509844840c1c2001d5641800e00c00045210000c050840b0950304545002c1d030303a081e000031441d801c0e407411a4014022541085030742400d002c3c2d100d0044850410350302913410690b2901c1b06c440d10f486031521610f00415189648183c50140701d4199055072110095400c0010340030300a0041690703003200601c11103007120b43c02031003c180007000001503030141c0328105440c0c660b280000300c018500c1f605800b44c4011482001d50034030900a82072001072a00ca070517503100c41080112042540840d0003106004100700c40303555502c00303d030706440c00e442001410104003584408480000da0b0240c1d5100042c0c50318442140e0802d0480788076540803200c1c2483c00c02d520340c0032071710303030005840d903403c69400303003001c20258a0140c14607081c91000109042c070121828550014000064400364140810f82292505202050055 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 904186690 1250 904185440 904185479
    0xe03040512010b030d180f12140316080901090b070b01181109040c051c06151407030305061314010e07020d020a20130518010b1813050115 61
    0xc002c006203c50110781c031820007014100801c41030301e070002c070070b0301c030a52101001d0104d450340e0040c00303922059608001e000108050302d1000c42150030312500d46002088945802c0521003800c0c498142da0b0301c2c22203580100500d03a0503c40c070b640e0081a0840d611002e8070203680205d810350925490708112100c00303502580001c0000741000081070340030342c0010403900280c2080c2d070300103001d00e02c2003001c9400780075101a6808104100c0120030180c103664201c1801e862007200e144441016800c1c081c0d40c400100880c40d0803480080c00502e01080c06544925400303034020f0500994504d0040c40d100c02c0320591a12070202104140041c00138051840c21154401c00314002800320b41030541c03003e90343e0f040701034009006030705036103200040303140c0400362008540d8094103c50300f94250620501c00f50404a030940080480040040c0c4821414080e21b0b00000000d4090703140400f040d0394051541100811801c0c60184100b010400039409101c0c00b00f5061340a40c40181c01400c040096038501c031140341 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 904187940 1250 904186690 904186693
    0x5070504090812011e0b0d142802040608010e0703060503010c022103010815090c03030a0906030b010c021e01020c0307030b071202040f061b02030d0201060f090203090c0103110d0e03040512 83
    0x4442e403e8141170f8600001e40c1c0b05c19009a4640d002c1c6a104030240c203085072205e40300f05001c02449006155200200d96040c52070b6040032502c090045880c0c100d025500c96040040d105000402c1103d2010f4081d94120304107150105400340c845010070300355000d184030440107a002d60744010000c4501004501003440d1410803d00e19490941c0540d130318130000d4480c03000c0c2180302e070205103001010004002510000f6080c0e0f5102c0a1543c1c016240b2000d500c212404241003218021035584507180052a240d4010319402c907024940c0341e49600e14104540b5241903100700e0106038103e90b001c2089000541c441e600800030707841d01c59401012000601100b0303820134014842400032001c09600d0234162040c6213800c03c44922600790301c080540c01100082d4060054240c110103060381074000c03a0903030340c000405048140d0348001070340492100b141d907088035402008000040750301c682c20001d405515101c281e402c1c088408101d034125400b040b0381c4215580700040410103814654040a652203a00c030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 904189190 1250 904187940 904187969
    0x120405040f05130204020306030703052506030c0207170c0411090f01021203131509050105060102070f08100c1806032712081b040803131217070507050409081201 71
    0x10500300c6210f40941c02403080d038002c1b0002e40180c81c100082401103410908842c0d13000c01517000003a00303411140d0000c5804411003404030380c5034081e00694003000040c0e401041401d2070000c2c00401448801034204207802800c2d607001c920ba94500079121442c41c3e1000030759a8103040e4040013048000c54999605540011039980081d56403481500e511043d11441d05424100c00d25001418585500a04103407070714060f102028044154803840c8a0802a0200c1d100765444000b1005000e8291048210031b50003002003820350a00340e04048064070107070400c084000c116807000c10718a500398100e200000e45e240703140e1480310000e40440b0501d5140c1c2242c020702004a445c2c1d01c045c0e5414034505002c2c040e020001c034098800404980302c41004240b642074545464020b12900ca80c005514040c101d03040c180c0106210052044070180254011440310404818040b00170081d0000c160684450191400001d160f40b41e0307001d0304880512a60079560341d0341c045404070540040c1030300030503040300f90750 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 904190440 1250 904189190 904189201
    0x90605010206010f180f020a031a0303090d1401090501020a0f02010c05160b130b070c05060108030a0206060112150312170c0f0c010e1e070b2712120405040f05 70
    0x140d44105480003070f6045e034840b069a0801d2800b80c10344c3c0d079620b200940b000981c9101e8941c9588000c6929941d4001040901d14060404d6a60301034004200d904c81200348207600010a15506501180103031800802d03401083d80740c290882e0000c2c8034940109a006400000c010360a1058000b10203040c00c26605200700c00320300000e40c0114000091401c3c100c9408600301c00403090840044991010800d01c1500d8000801490899540c8003240c0c94440c0034004180c007034000c000d070381c44040310f503004002541ea6400112100304500d854044c145a0782c200307a8401e00c030000f00750000b460161400c65a4100003080007415803200d03100e03400c4c001d40e144003400080d038034110031208a410090005520b4019007075120740100348445040055215880c1885c0314407100c0001c1401c5030905106a4242c40e55804016403070b407081101d072200070280c00304048000046140c080546140c041c14481c101071040c1501d134900000940c90b02401d00313012904002a1500d030250356241640c81c10144000e0608 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 904191690 1250 904190440 904190459
    0x30507080f060c18010309020609130b030d02010504121b0b010b1308030c0a0213140406062d0605070f141b040905100207050c1503071805010c1704090c030609060501020601 76
    0x1084c0b102c1c1c1013580300d514200c155a581c3e42910032114004052400c0100002c0180e8014000e0703001c1c041c000d01440b110701c0741d00d03030044c404c00e845160480c0004400f00d04140c8102e41e100900aa403c2c03919038041c4101c3d000c2002505018080c1481c4507105946681c142d144000000c510307401000554020803090764241000301e418800503a0548244003245441c25110000e07140e01d0524100041004040005010064102c4402c4850030710720b20124020740c1760009400c80c0c900d0a010100907020f80204442840303003000b014072a0107203400d400314488954a001090b4280300c103800b0384d54011806d00b604c541d07140316000c0001c10304440030440704035a80e842a4460340c0304800c1150b00e40d4081012400d000c1c043c80034040000c0c0041c42c0d40000408407034001082c0d001504d0346070000d006440d843c01d07078001d0071103039600b0340350161a0604440c0096543c40900680c0da800310003000d0042c0310000f0840003600a000c0c0049803510041002800c050a07041260415449503046621100041220103071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 904192940 1250 904191690 904191727
    0x5010f060f03050d03110c01090b010e0a050c0a0f1206080a0c090c020d14120903250308060f0a03061d10110702060a030e0303010308030f060a030203100b0a030507080f060c 76
    0x8031170402241c80d031610001d100081c0a13040c044421542414100c008115500980310705850403205451240c0e12aa1b05590848808654005581c0010000c0001250040c4c0301880140031070314001240000541d0050b080e1085c9030b005403800e03800148801d0400c4207001c42c21000d000d070504108078026031000000d55036040500440180402c02e4001b20082e590f0008460880504080318103041c10401400340da81d0b80b20010110000741c0b000d8400c00807003039420b2400103440c1c160740c80f403030385441c0e4400700040e0507291840294000c80354440000007486034040d0100d0010743c14902c44a20300c0c0d1692003400e00c800c40c511946418a00386250b020541c400040d2805240c0680d0302039101e0304c0300079042c1c5c01040b00040d140700502c030100000003003044050046100e04007003c507848068490409009020005000082d1b01d50040c00e843c0080c4034541c2d111880e6001e0040c0032001069892721214100462900049429004800c1500d02504c040109941000101c0101441c0902c44405900e6030f18 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 904194190 1250 904192940 904192963
    0x50f0d030e0f01050906040608090d03063006090b01060f1716090b16020f010e01022802090414010b09100302060a171e06030a0c050415080a05010f060f0305 69
    0x4007079030310b040c01648640d0913a2415800a000d443c1c0c1c2e07075140c88019014100031a241a0030344540442c1e200c040f8460f00a880440d1180e03400d44002030340728090070200c804400c60030301c0300e02e000c1007558001c06d480c1d004d400d82c0c40b805000d06040c2c0d07505090b8001c1484249007408001d0190049250001516000790194044400245011004800c0108840404c01030388062600803010403580030344650b15018954030b43c401c0b80c0f8071034185010001991400f1012403c1030150304461003545240704416121a0010000c820500c0c1e18007650780001c0410340182d80550b58100070002ca001c00900c240305200d40d4000c100c1c0d9501c803a180031002010172490314000240100000726818502a00510024034031000554110400d450700c8818408034400150220381c04c24203030f102284241c140403a451184d940c0010165684905000501025081c44980004041c1400c03000140e140401e10642c0303086c078810320001c600c6003184981c2e0f0040d992250011340907102026002c000144000514800383c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 904195440 1250 904194190 904194199
    0x10e0f030c04091e060e07050901080d08040203030c03070b10170307030f09030b1303020105150a0b071514090c0102011103070f09030b0106050706110a02032b15050f0d030e 76
    0x2035813900e04085040784c1c01a07088105600000e00070804c1541240d0012030b8240125488250380b40d0401114400c02c0c8a098400c0d04070300031001d4520311034482139a0040c00502200d140804480c1e485107036038440042621b00040b11428080c20451103540c5100a1001d814498030221a401a00703840f031080e80c000038140001c080c400d591481c00760582a00039a0042c085d8015450943d9000094240b0b10100310010352814001481c52000c241980ea00090b004d4003000c1c446042c80f6410003c0c0d03010080c1a54103421a102c2007103600494020f083c454100c10454142d24144088107615001c1001600e5056904113080540c030401c810003076036400182c1e40781c1030f80480f03074494041e110949a600007501c402241800032a809403c6402007100c6441002c04110810462000c05824002c00507600d0050700300f0080300030b0a126060701c100f008512501a0814000c10140c40d0080300c0e1140c481c0941d0410b003000030000b51030b001a0494621f10250768034410020246d600a084188010355540706 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 904196690 1250 904195440 904195451
    0x1015080a022d040f0506030c12070b0a050c0f0703170703140f0903010923070f0b1b0f010b0907020a02181509040503070215120f070c120806010e0f030c04 68
    0x200c1e02e902d02c0c001041c4001400130024084440b08050280c40e013112454002d108015800c081400e00c45d940c003135400c100708040c007000c44c284401512140d0004900b041004014401d4117004001403110850300c02c0844000d003031061551070301c2424100b200301481400e0100f03000070000301f034000388c514010f117203602c18143c0d981c1800c44890080707003e8440340e10341640c80c0051103020003115002d0b0440b401d602c2150801d45140307100e8510380d0f980844c0105080d200d40d60300b00308064411503003c3e00380940d0b01004901c2038880100c445242c4016219603c070740c1c1e9142c0d844d0500c50306194080c00d400039040c0c80608100d0107241c01180048860001c044200151000041c10a02400900c4800480300400d500a24201800c0070355494101c1c2c9003d0340303d07000380d9016401c41780005086807500c0d90002c00000c5940d46510b0324a1014500400700000e0000041d458400640380041c00424100f1603100c0c01e000e070806400051409150a699601525698131103001d03580d0005a071010b40075044601051 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 904197940 1250 904196690 904196749
    0x60f16030908030a050708010f050a03020d030306030b25050a051602040b181609080a03030c03061203020f01060609060c0611130f0905070f080106201015080a02 71
    0x24003001c100075100c02008028003428080c3c581000d401149944d646580c140d80360200c20139100140d1007071640c4181c5001041006080c8039030420711841c000c0c180000d103a6941c1d10303220010481120400d0329400300003540b000e0004100c81c403034141c20b05407418600304134960744003500318401ca072991648041008012021591180c00c0030083e03690161081c1142400c01e402d41000003800c0d40c070081c1d21000c91620040d5284500e81c01c000f16400c4400610390021280c40650007041c1401000041503115403000c1900d411291892082e54402e6001780340301c0d03901581450846607030360400350030031081f03036410011641e0140c088204250003110000c0e131022001c089607014420f02d106820441c9050100040c8a000c500300c510840d09a41424081507a40310801c942010310707151090045154100140003242c422103111f44624500452000858035040c520f901d0444989014000305845108146011140803203460043c0f0300200109850b08241c0d00103104104402101c2c0c201014840300e000703 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 904199190 1250 904197940 904197947
    0x2090f1305010e0c0a05030a02010509210304141c020303040b0c010f0501080309090703180b040203210d150b040b030606040312080a0c0503041a090c040e0d0f02060f16 74
    0x34000d5001c0000c00c4954110b14110341c5441c40308855511800f0800d000048905000c03400d240049c1d416950646884008010402c2d00203a40c15003200d000e2500044030a00201000108080c2c41b44010740721010103140100400e14119000500000300e495a400300107880001c04d03034094130520410507445c4d40920607010300415149102100381400c00000141e41000400200f007054801c0e00d020005039200302c01070b000d44080601c81e0116202e9800c810020a0580081c15000f0f8402815900441c103030313904049402030902c299a008403000103202d08110410711a41a2039218006211a000e14160311400907000380e200e0308401403000000500e41d0b030703980b9045070080d55120003241241c1d00700b1280103160b8401102c0c0d1004552500211001c182c0c00f0350140c92145510800310740d000411541400b82092010f4035441e404d200f08640056547d882c0c1c0120320203d0314030740081c260f1000c64a801003c01c0c400200140554100d1018080305800d0100080c2c2e0007035808140725445403001c8000ca = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 904200440 1250 904199190 904199221
    0x1e0b030309031e0105010b0f0f13091d2a061b0307050a0b01140609010c0c1211090609071b1b0303021509010b0607030c21020a1401020702090f 63
    0x4592600507402202c054100c002104400c2c150004005c0009a0300c50f4044d0324188110700c1b1001c100f5009009d0000607038001801002603c022410200c00caa0359020761805882c0302e40f1003980000b508070b0032802041c10030041b000d00080c0d80100c985034114070816289004a0700d0700c50078024140001e0b20024540398400749802c4201c02403ca0f691075000c0d040c19a210002810200d5242000c4400050340b6005c20711075401c01c14001f03088a240c09080c41c0159001d0b80350440c112201000c4c1200024880d811407540044180904000c82c10400e0100812050002c014119481440c1c24000d208900d6400349901e1401088004064400032950420300c4814520618280701003140d054044100b59000c107000b150542907910401503070300c505070400d090f5000c2946803501300c5014070a030302c080303407042e040050320b54054004214903800303122341c240100c440307440d2410150b4014050082000f0003c0c480c24240c52500000b1801c14660b940011100703c0c0144c4103444101030a40801d03402c0e03100721040d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 904201690 1250 904200440 904200457
    0xf110304170f01150b0a0f030b03060a0c03060504020a0509060705070915060206090d1e0c060f0b01080a02180d05010b030616020d1103040611070f03050610091e0b0303 74
    0x1500c00030440a2415030703111a000820142c0d9424035195a00c48072414040400362a80c18135100c2c1004103041080720ba04035800c034048201138a5092080e06a1410b12070305000380c10940011480000b0880003406882c0b80354003040c0680d10410000c0c41c084d5000f0700340c07486107004072050b66a500003030921030714090700741e00810241441c0c0300d40003000c00e00b03d8015801f1540d29400740d888036a00d100e65191980c0c129440700740815038902e00090380b1800400301c500807510606012016007002d848400486040e034081c1081c0740c0d41d0300340d01c0c6283d68020301d520354000c8800c0780c02d514100c062402a184c120415942c1030040340c01e00111801c01c40290000402e80b480502261090300d005010b40301e17440c5044074540054000d9215038203400744a00d0b4182001400540150f242619043e02100c840d10054212010390094807004034491700e07101d40c15002540288018101424089441c01c2010056840039500d05d1410080312100300e60b07003950418071804c8810010352007081a0200342548102e005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 904202940 1250 904201690 904201709
    0x9060705071805040c27020a111e0f0601080d0f0e120a110423040206160c090510120b07182304050402031203040312020c0322060f110304 61
    0xc94a8600207a200502c1640518444085e0594405843e0007005c40c60901d80801c0000308404503948a658004000b0349500340303020006020100a003500f44140c0041c40b07501c113210711004503120304d41003026003041c804110160803e5407600c6a81c0d562003c20f000c003507003800031444007100001e000c0d1011040311800034041001142400fa20241c5881e03080c1803c8400f41d2410a44078442e0070130303200b04010f0b0241c4507024041c0321010038102601c1c04000303008a07030141080100200000e01210358219861180138100321413401d01403841d00340c3e04010199181c01d14818002c0000705200782d82e20030b415406c200003030b16680320120200c440c04150b00c07a0602d400e46000002821038450a500560702c01010b41e20241441c1041c100800d07200c00b5500070354168048400841501c00b21002140c1243c03084c00e0501000c00300f0a007000c141e0300f0003008a081500042201c00c04034200760700c0e811001c07010f00000c03203030b0509110000d00000000c400351800c200b0b0110304038409000400485024214914 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 904204190 1250 904202940 904202969
    0x20709152106050f270f0a0c080d020c10080702070f080d1b02090412110601030c031505040305031306021c020703200601030b0c07021f230906070507 66
    0x71410020704059240860704607140c200003541c49568410302600684039091183c40c440d902e00f00c0007503036a00341a42219140207520180c03a00030300801400c4051403044494910191078607110b81d0070000c4400b03113030701950080c10500d4030359550a294681c1c2e440d41420000d40f5034558810491508000e0b0300864000141180c02150041e000034242018000700d03601c17040807126a11b5030300e0400c105240025000b1425801040028035050001c015000c5103240660f24400030114041c90280203034401d403040114041c0900500445200414844045000c1403215080c13a40d00108240b0000b001c40501044600119003000b81940440301c0405d542c1d5040414900c4502944001350301030075040340450f2004d840a1505a81c20515a4108000c0c502600300c030b80c6192a0403204000041406415000400400d00160b60f058100032900000001b00c101c90984401d000e0318a9200503038101d150700084421b0195015203004984c00c0e010306a40c0c0c543c9681d5940740c180e04c0c0c4480c1d50001072540615030f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 904205440 1250 904204190 904204229
    0x40c0c051002180406030203031209150f041203140a0b060906040e010906120b06010c0201090e0f01030b06010c0506040f05070b0c0c041103060d060e2e05060405060102070915 77
    0x350003030000003103501410b0300ca803d507040410003201e006100003905500184102c0540e900c0200c54507510240d08000e4504e182d44100b04104007900840d8822600c0029200b4031040c002d80345e000350003020302410100000c580441d4024140c0300010101e40903c1c1d102d00341803013142c1307540007501e8205c00040c01e155101d90326000f8084040800740940c414041c58201c0001d80740481400124200da04040401d041c1d45030f00004643d103200b03414050303060188440c00010503d601014451154018111120055045240c194140e4402030130450400c08820004400700d00c0220703a60b500150b021000d000f4540f0146049400c2641c5c135482001450740124190000c5500422681034401003101c00700b10f40b00724100199403138001555110340021161500500161356507104218000604040f9044010306c10050b14041919440840c0036010b241e13200c90001246019058202404807814030081ca00040001d64800c0540700319150070b03490310a034001d2070303040c25241005040c4a0400c10403100b02d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 904206690 1250 904205440 904205473
    0x3020f0d082d0f0a11040b0d110c0c01110f0a031e02012901020f030408070504050f072705030a1a100b090f01090503010c08160f020c040c0c05 63
    0x100c4181090b1005140026160002500d00307003100c005540304488aa110801e1000c420503004140c02d810744c0c2e85445865401207841e01400040c4244501c4540c2c84440a01c0c2d03100f914010310b070b407610010381401000360050700460b030182405030a02c2c1107081a1090103030b05180100713580744520a40240c552013000d06500c200c90b0041d00c00f201001a011a10480c0104c1c200c071030250034045101da040904104c0410070b00607065100078144112201104803014850a40d4001e41c4a40178942c4884810446400d1600445034001c1414074101c14614082170003400c44c0703252010050341141d48540035030348407004001480c05440003600712001c0c106240f514503030000c4401c04d015085501e0f01c0020707907180040c102ca4400d441440200c80e0800340d600c400c0c4501024051b402c0d038140202c1e0034000c02c2944003481106141740c010b585000c1c25007410030709500414080002c00f010414148403031183c02d90001070846032450151400a0820010320b0b040341d0400e0548002000d0303004031a10f000302c0004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 904207940 1250 904206690 904206707
    0x90b011419080c0f0a08070e090108011a060f0a18030f06091a0412053109060506071a0a1e050604180b0c0309070510090f050915090403020f0d 63
    0x40315120b004254884120322015405070b19004d8a5994040002558042c880e0640c0c40d0800c02d9401d040000440090000344001d000f40c00500040e951008000514030740d4410031180f02030161006490040300b0b4159500d207109250444d0103000030000005200800704040100070364210500d8a21306d00c00c4d28042d005130000781c0c41500d103144800c0208403213010240c40b607070050b80d110042101030b95030558103507804e41050b401c0300440108682801c01723381490a9205030000c00700b039106e0049052540807002c42d68681c003c24094402404800000f600600c8000b0000001d210620610340e1488188400303005004128101c4803d60000c41c4a1034110750805030007183c04070b505000200308491528140d1800d2a0090014039040c1d002c2516503811000454000b101c0700c0c203461009440b070010500c3c202540341c2c500c001a82881e02040071460710443e03d406172400f250500301c1428980031001c0310900b95080240310b0501d540214007054020011840203c8008050328030503041c40f940a444900c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 904209190 1250 904207940 904207987
    0x1003050307080a030b01050408030d05060f06130f080a0b0c0d02070f08030a2d051906081f0c120209120706120609020702030d1d0910031218090b0114 66
    0x2030400304644406c1d0b001748155819a04010700550030100043c0c840000b508000d01465003107802032150380460b440d07180c001c2455120103000031403594a040d1703850510407225440204146c001e03250040001d0740c1c400386a50041c0c8160411a1144524500c80780248101c00300140840d929070540f1041245180146101c3d04041604111001600c10784905080340c012250401d00f2108a0b0310007840151307400950403042d402c0c0e0800540c201c804100007120115006040d103035008a21000707030b9048a43c048040619600020f11100c0300899001c0d01c010000c0c102d0010b400d40104074800740d5103075543d07070f07444000d0301c40100c44c42c0c42c0c0d540c04041c06180000c90110380703850030041d0200c1c4100b010300850341d145c1d40c050001c0400ca012801d040b43d0795403449001d20038805c881c800e0803190b940d4032010346000d4101031400b07948452541c6000d40c00e00c450f501000041c4030003140818413550080c1006822a0190400400c640c41c00c000101c3d2814414001c070b210755000803070305443c4e070403141d16243c9802 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 904210440 1250 904209190 904209197
    0x10e07082a2107020d0f050a090504060e04021e030a0206030a1e0c0e0303040b0a1112030a1512020d0209070201020c0303130614010e010510090e04050d02010c0e01090308031003050307080a 83
    0x10f031122042242c407417203081d24540c0410903006030101d800344940014080c0140502e41001000c1d00c0d100001c040c0c40700369200c400912004d0b400d1005515002d044c4015201850390310845080ca0380c80441c0d11500141c0c80030344600404800145c1840e01c03608000441d02c9e03928040c14000158004c4503004045902003140043c0c03982500c185181400000c0b10705030303109a1b5003181480c8010204a529a65500340c0c10414011100b11054140560020b54000d00310a103010455440102c400701040a03954010b10b06201d01c1d804500c056111201c2c04100d43e1f4042d00c03a2400d9a9500400340d000e03124001c44010ba0b848000304100010401000c5c604410703110703800030b02191032000e21243d40041c003070041d00d00410011004220f1840e000700c1250036442d8a04005a1440d9140012003402800700c0b0180c40c1601300b00f06032040f150382803090b40c20412050405281c1c108030340000810504d01404010311016000011615034145010443c00441c1c2c008122580c4204a242814141d04107a2241c00030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 904211690 1250 904210440 904210507
    0x50c0c0609060702060a0621021801030809090f01050612060f1c0506010905090319020a0c0308070605250c1407030507060815130513020402160308010e07082a 70
    0x90711018021f9000700d4801e04600c09200c84012030611013510070781801c0341d00040307442003400c18000ea010154000c0d030041e0030080d142d00004007409414400104940711002c04070005104940c1c5140603a2419814881c034607407180e90f2038003c280c20b414a00032071a404084d55000034503034161101c55444145c46a07051702c0ba1a6682c042030300540340c06a07084008da40081c82070140156940a40303048074075031132040f80d481d05015100c0484042441d081134529078000a5601306002490003010341243ea40303076600c4104012040c05090b144412511070040140c0b01490409000c2410400c40c60341c0402d800761486290340e450111b07654290fa1140c14003059080740050203130000001c0b8503e1144000c1c0199100c200c0c452600d0000700401005001502e10490145016880c1c0348003801d10107030244031411200710030b403c0182c00c1450590000034208411000c200e03039a07501c40d5030f03079030410072a60300441c0101080c3c42600b10070240d40e601380d10107000400c00700d4880002c04030f02021120740980010300b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 904212940 1250 904211690 904211701
    0xc0705010201240b07060603120507030e0102073b01061809050702120f120106090918020f100c1401020d0501140a06050d0e030409020d0b1207050103050c0c060906070206 75
    0x2043d440c400e02c551018031041c00420060300c00000400c0554880c00c00040e6498490b518211110071900480000800104014041540042c2e14106a01c002d000030000545403601d140c00c900149185218808a480f010140c40c01d0300c03a880c01a5080f0081946010b0341e140ca0004100440e02e050490006e0380030715000880864920443d8082c41e500d6000c0c0101c081990a02c0c0e0480c1d0204100d00480781040262005200103000c4e0540600031b55a500c00381c1520308070105040e50080b03105208074900c1c0d00100b80050351050031103400e032a820380b26952142d10000050b18034041c8003102802030444060305010400c8194001c0240c106892010404d0380d80f500e074010000207001c5807180c0c0000b0a008140040390040340a4403545440c00d801155282d000040300c4d0454016034020490250081451401c5544601071445019800c2d1211000e0425403000350359504d405118070740c145a6600d0104814a0001044071200030703a49084941d9400c060002c03603a00c003001c41e200001801103102155 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 904214190 1250 904212940 904212971
    0x14030702091b0d022a0a0510020c0604060e0712060509010c0e0102100b030c0d0506090c0102010e0a08030604111b0d030e281a0f0703090803010905100b0c0705010201 73
    0x41501004014690600c0c038014640402584403440c074940f28031280c0b80d117070054500a0062104041d2180240255034070910f4072501d09288100e1300c6406030b00500208480319800101c0643c029001940401c512101907681e500740002908841404000000ca002c180310060704043e000385280e0b0020048402c07466001c4982e02c611440361401a005040040744c3c060302904010340413003004054801c100414030004a954880035000c0303505401c40d43c1002000182400b40d00955203080c0000e002c000b0140c0301168580c2841407000349015004004203400d41c8540d40550f20381c004044a040e80ca02c2c1c003c14000229495001d5054030b41301e52120041494840d004548000030b203a002424808a50407005c852a9074405001381940300540f8010b012440700386841d0280000c8071415005801c1140c5c2c000310094000302080c050508010f501000a62039004407070469811500c00982c41d02c0b2181581004442503100c010b00760700200d00101c1c1044003082450465800b600200a0b0200380d500f0700 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 904215440 1250 904214190 904214221
    0x20a0510090206030403030e07081905070504060308030402090711010207060204032022021603081008031606050c0705010c030c0905120c010309021302030423210a0c1403070209 78
    0x80d004042030000c03031700080c040d03008042c00c0c020075000c0d03600103600c82d44894984400d4440c4540c2400203500c50005000c0140040b1000d40015103007881a01d0840c2c50744c0e952440054002070040500b000040d10b224460100c01d03540106481c001d540d030360b046080c141c3c0079400034001515140e490074550315030301c0281102c01d28180f030064100250407100c0590b41d440c9240e071803442500c4a030204144030542e42c034000f00c140e10510030b4990840a0510707034031014450a41c0d8001340c1d210f41c0100308208004100122031901a5400040403520394bd6401d11b4038018003070200000d0070b66082250600b078454040e0400701c0a45000d0b1744841c84550790300100460740440b5214600e17141c00c0083d0608407940b04c0e40081007002d0005d400f0030090000c0c212010102d034800c4a00380d9001d082d000680b1010158880d010642114500c0104840201f812000144060303c3c0840035107441c0c000790010625010340003181c3d56541104030080010070051581e522540030001c102c0c800d5010100103010f2002d55541c9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 904216690 1250 904215440 904215443
    0x50d0606170403111006090608160320042304052811010311030a060312080606030a05150a1d010f03170304060204171507030605150d0e010c020a051009 67
    0x100e8115441d10b480549107036007041d04850b02d6014485001c1900a418010720005041c02200002d10309c2c42c143d0b5281c200004d403010352940711008442003001c03510354a100d6100791146441c11a445283c8c6000600601c12410680741040222621300004819032a03240c0c8900d00070b03c196022003a000760365a00d02c40c2d00d40f50105400f1b0025010390041040701140321041c103010f0400090301c540da8202c0c240c09030021140080341c2500c4c2e030010b1040012407404040d40603584d041002e40e50900e43c0009565020081c0303410501550740b80090fa1101d6000a003805040002d0b1001204940b207000564401a200c02d01c2d01050654400000b00300301c0600040080381d420001c203081c132803040d00e1548401d9101510580b09035400f8400440c51050450040401141071401403101085154100079041c1c001403404082c10302d889801c0100d134484241c030b1007201624102640d9a501441d100200030100740303288017a9907181800450b80c0540004401d404140500c003100c6a0444000403c001d49103403d00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 904217940 1250 904216690 904216727
    0x1060906030f0f062607030809191502030702010314310210030b0108070305010302030709090f1406060120030409020a031820040e060c070203100c050d0606 69
    0x420149120354009440164820780214000010101c9641594681c1d08055003d6085210310092110140d1099903c5d8503003a000d803135a5031940d00c1e02c01c140e00036011210300600c1e112a0f20000590803010501c00341440388860610802c0c2c0d01c50088d500e401c402d0b000c0740400d1411078101030500021040500c501c000850301a40300302030b11988180c01d48804400c10710440c1144010005a80300a0340800000b015540007c0307591350710000500d170030806800c41090514242c0103001680f004150181500d00b4081d000c02e04901503d42740000e0344130118040d043c2e543c1e80000b12100403000c600d2500800007661401c601068507080c1074900881919049a660f20070001007000e01daa540107048420040d080001c0c0d00703c8035035603603985142c03102800c031454450010101191102c08114151001c3c007074400700203000f85c1500042d41c0307034400b409406030000301103511411513404011154040381ca4440a2007030702903040018229801c40d001c5241600d040c07a6010800c507200f440c1400850040e0b41 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 904219190 1250 904217940 904217957
    0x90a0b25050f06073b041104031403070201030e03120114010509060d0c0207090b1e0d0c0f1404180b0c0d0212061008090703080c0304051201091a0106 66
    0x1030340685024200001c440034042c90440303540d41102802034920030400390315410707080c00e004c0b400020403440c42007142d80c3d1068984c40e0f041c840001207100c1840148242e500058000c070031641d1000342c3c00783d81c0c0010b04c00360b1070300b4001400d00000305c00f804a45200381c9081c04802c6904168a44034003e007401c0340310f0229104010000501d0924442800c187c040c1070561a0150160105446074000c1400015103921841031206044d0304201c440020700003001c041083c250310000003181c001c05030448500f8900c84802054003a0b44908030000c00b130b94003182e150901a0703201c02c10940300301c1521501d03040d0503942e07071100360b40c1c200340c0907200640c810100c06510303118a60742d460040c0c2202400e44244490b003072040c0b4287c4113240c03006180d50442080003210b103180440410541e25200d0f41c0007403c00c1945401d21145080001d62003041d203912070348840d100d480304c0c0c02061650280c0c2d1b0041e42d0054a581c0190640c1c03606601980742c8601850303d1031004d6031440120040c00c402803040900049014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 904220440 1250 904219190 904219237
    0x311061513090804050409050624060403201807080a060e2404020d1401050d08190c060924060513020d02130f05030d031406011b021302090a0b 63
    0xb5480903100c40d10408072542002e1700d45010074111031600f10308980a81c800c80520032030b542c1003c00c001c0301000c0c00e00321050804080c40492018004c074400145082401c8100c9400d102c100c10703080e02e5a220240000c648441e981c000c0c4441b950f002d64115011410040120b9400340e1140589020303268140035000e001d44a60343c420f80300901c0781c000080104424003118400b50f480340028030100000e041c01041090051080e500c00d908103a01642c0300e080120740b480c0c00200d0100032380c4d0400c807140542e05074480d401c20040e81c00101d91500108010b04e03003180da00400036041c9120303d6169001d01d170514500c21415502040300d1003800381645c05440e100040c4201e0699030000d001c3d440710480050700b06500e0070420300d0b00c060960481008203410035018400ea09003045604103d15003480c0a0091394407a1206414805001c0c02050401c102d0800821400f0700444480c0b4111798040c2400d050030b80140742b01030003034000b04d1265200342c040c0740b000911010380747e0603910f0500b07000d8088290405407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 904221690 1250 904220440 904220479
    0x4140a020a030209071803050303100e0f0a0b030a12090f0b07021e12070b0a0f170c07080c0d080a0e03040303020c060d0b1e09060a12230a03110615 65
    0x184170708100404041c2c1e40403000c4208403100700642c0b05a0065440381000d4880c081c1d8a006a0000074244696801b005006001c83c080d550300019000400200701443d03a0109051241d105005014004041001e0040380e40c040a80d03403c03960185400034000340c4413100018503224032000a03601100000300010714800b42035040e0509400244040032031a000114541000d040d0303803010903010b03804100c0440d00c5800c000f511003d14000c0c903000302d45960385062000142000342c803150314404e000c500842001002e0702110440709290085804950301003800038188001221613914580c200140c10f03000b142c002040d80c4c10b880c0e26401500340c65010405000c1d1a801c207900c0d008009803031b0100c260440d21001d00864241c4d2a0b040c2c0c035110010480240200c40398054085401044c17808401c00020203c1046220402d60218186410710901d0084495011440d01c5034190740c01001811420541c10900c00b01d074080d184000d0360002da450007901d25104140030281c50b084519812400c5d0071444 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 904222940 1250 904221690 904221709
    0x91805090304080f160b04080a080906091c03020d0f0522050d121704080304080c151302121c180e0a0b0f0d022b0b0f04140a020a0302 59
    0x100304032030034159120041e500e00700000c92001d001c1e1304418600d901030302a0f050b410780036000000900f86403e2030850f031145d48500d10318010f481c0c190003041c205d019a0707580c002c940c01031500030103500d4041c00814003845440c0203100c0450142c403c540c44c5101c21070140030a0f00024a00e6156141010489641a0442481011011070541c1c6c0613001103031036550213220452007030007640c010300344020600000e4000c602503c07061400c1003083c4c08210000751101e04482d4000d40c01011a41c0b275405070035483d85049841c1072401380c0090204200804e414018118a02050003107684084e02c0e200e0600303282c0c0b1201c000c651100c1500006a0f0403003628000c801440d4294200380d0b23440340300c1e40d4a40c4070b0590360000392100d940e9551280c0c0200b19914203034411002d00107040702c401d8500821540000d40ca8a02c181110200403200d404090b03a559003050303a01d2419800c202c0c2000f951070040740c50b03038510360103d404803812504c40700c0c00045010001131040649030301800440c2258255002c0001d41d90 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 904224190 1250 904222940 904222951
    0x11043801050705030703170a061503020706020c100b1003090b070c08120114010f02060f0609060a08030417060702061b0f0c030a1107050d02240915090f01091805 71
    0x504000b2000041d00800c0140141402075840d00b8400c00c80c00c40410003035201620307003441d031400c1410a0003c40c0e0034160015109280d4100103030ba6105919100003e8050108500c0035402402d0301c8a03000c08440d04482c48449007242e1042c58a440e6400a6040301d000305400741c54480c0613400950000c7c055080010414080c41c800c5090021094406e000030000742c00189007144a030440728040d5802580310b0448907640d001802c494503001080e00303080c1500422003440385440501041c400c2d01da1a01d203502520340344095a9a035502c4070400e800c4816400690b0380180724a0001a010510115800340142003c286201300c1340300f86140c0e034496800c45076103811002020002d002c1e05150403c001c004070320898995090451003441610f040400f00c1d03000030300070315803820810300596541c0149411f0f1301c80386194180c0c5880c21105d0040c0e90291017880b0390005900b401601004620721701801840408499071a02a910000111a025241e200c0d0104940449a4204006625822441d4001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 904225440 1250 904224190 904224197
    0x30f0b063c0a090807093309021326070e060102010b0a0608090f0c0d0201050f09060703120501060212030a09030c020916030f0b0d020d150911043801 66
    0x18804508100007036030101d89007a0101d18510001c202407201402400003c044103042040104150300110f54911441e0031452042d0010700140c0b0703200e121820790340010f013024103411511040a106032507001c910074010602c40600c00a00c004001207a040c1482c0031290020117041c000f86000e02040190380050003880c159521407002078200e45400354940001c001c15560740f0341038100b0f03000460415000c68500c001d59000003c1c042c0386030312104501c85013154280780a1b0360b02c010a105087c0c4500405090316400803001510038140344c0c2c0074125143e04010901d0400c0300d030344d860200380c0c1d4903022000c1e51449100c0900028401441a45c07020300301c1c1d8001d04045560381d0007640021003111040f14034402c80340640b41828565945841140048040751008024205103040068960382002c032000780301d0784100c2e0b00c00c010000f14894160721209c40000500446c021880e0211101c941c00e2515800785140c545c0300c54183d0401405d80d0150b03880340c221004a9a110150000c2105c10102010f050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 904226690 1250 904225440 904225537
    0x41e05060412031205070e01030b10020d050f0d0e0606011715010c21021608060c04170f03031905091501030b070201090519030e01050f0f1e0703030f0b06 68
    0x604e000340075451041d4820f130742d0480608440c2d00007504841101c06554059071340d40b40c1e44002c40340c000507209121401410040c4c1c0712940d0f41c9070240c0724445d14604078500c2e030400030020034100000800074050741090b01d940010401c07201d805600044200c5e00c4a11101c610728441080d1f500544100f00039500070341c20b0031319000c995080445210381d2a6200d4005034810355015884c002e01c202010007400142000d4081c0d41880341c400b8146019030301400220b805030b90004004000100001c18030300d40041d0540f522890f01e180b9105441e01c04c001005170f070381e04080c0002d04494001c41d121410011000381c000c0903908584500194501c000d080310103666850015101042c410010703c00c50806000700605000403a03d4020002e03550490301c681845000d210900c2010404d0303082c0c0e018902003100843d120340405101c0601d0001c104050403101400060001c281545608000c00c110180141842100c3c4c0700c5013880407502c40c00806040054503001041101d114281c1001c0040c5102c0012441 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 904227940 1250 904226690 904226717
    0x506133503161103040513020306010519051201090c0f0c0309081009150608060c070f14030a09061103040512240a0b1005031f03050f03041e0506041203 67
    0x962040d6650751454900200c0c240d0b070640d003d0300c00d820030740051004d0b40c1000e280c00041180c1c81118002c00c202d654010000503000d920400c1600c500b4003690070100c0b02d140383e1540181065101e8000215500e80315800402c04003054000c0300c003506980e07640c2c1c050705000d010301250405001caa080f000c2151842002130070a0042003a03081200c500000015150f8035454441000b41d07000c01f507944440e0626000701b190030320201d15154001c169100c41540c1d2022498540540c00e900f0380c0040c919121031003c10184000000a4014841c9a4485000e030b60340360901a50482c800710078042860703108001c10b01c110b00b44045056038444608049400c0720305011040b030002c180c0e07a0781015088407003800700883c0e040d0700e0103080d40800090780c04407a12500d0290040c40ca10004040d24400a05011058071198101034484011508403041d10449090300010580740e902a201c0c036580c1c0c541b0b0550500144d88485118030495800070111454585481014550b6410081d826030511424403203030314 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 904229190 1250 904227940 904228043
    0x80f0f01060e2d01110606010e090406020403061a1e03190c050a1e0b090a1a19030501090e1c14040906060203030403303204050613 58
    0x81043d92207410b100798014a03000140344640401c209a440d078020428400c80da6000094921188000d44132500c4a0342e590404d02d01030b12465000070a072500e05120030b04181d40303e2109034503694040340c03180080010200403030712108154600b55859004000310441402000340e44110007881011300130052aa50310025400386140d40c447c030075204284000e404807201503000d030405418900c4903581080c640401042061245001e19910041345800c1c01c043e080c1c0c10780940d0000d006034102d8500035014039000034068642803180381d0019081140d00e6404840100d45140c24a4600030005c9911400c44d10071070741d201180d241c03000c17413600411002c61006028041c8a02a0031150019517490520f80b40042150031040d0951300e6222560181103001c40b000302c04022450030400c4003003008041d02070910b22100b00d9002688100c50001c041c1c60020040e003111a01c04e60140017a1040340e80d402450b80906094510020050b00da03a2040105002c01c0046401720110510800e0310100901d00d08403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 904230440 1250 904229190 904229239
    0xe060a0f1d06010512030a0503070507060603020d0c051203043005030412031b030e0f0301022b05060f0a33020609071e0608040f08030408040303080f0f01060e 70
    0x104541d0700b226006101038240b011078000b00b0704502004501e0b041c0c4601c0010001e02014217030b181040400117100301401905d8208202842d0010301c1004008c0c02c84c602102000c00d14410907004108560480d094800084103a900b1901010b00c1500107050b20031075a60304905140500400c4011390502002084040000d07002070014a808005450726174240035216003030b120340150900c00c61030007200c00250700c14581d042c5004151040c00c1003500400010b0702a01409086025004820021042100410102072407176400c200b010070417900c5002c01c0c03244217010444050713044220800b04005040c07099120f0250a00710103050300e00500000e0040003a0800c5d140680f0051784007005000040c00184100b800906800301003d0b184104485821907031700c550301c01e19090000f40c034009018060704c901e511559603403008000f90303a0301d020f141501140e0480d000a500082c0c0200010348440364104605008981c60708001c001130b8a00320701203d50010503070107260031120030b1549074811006406031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 904231690 1250 904230440 904230491
    0xb040b3711060f0403050a0c1128080a0206120a09080304080406180f2106020a0302030417161205070515090d080c04210c0e0a0b040e060a0f 62
    0x1030711000002540070724503194020340043c2c40d004464090000003600034080f50015442400c103000f03504502e050416141c3ca02041d16a0032040f44290f08114480b80040104500c1c02105c046080a458131907017580e03100161402508040104551102007055044866102c254000d0100d0070711440c0d40d8140c03e0b600203480880302c4800c0810144645904212030080341c00000d400c900445141c00c0542032821a144507000080070f060010400b0780c0003008480300030a42107042036540d441c12250041c0298002c075019100c2c990100c030100210030b2078078203c520800080308040b49220494461091058100500c9020f00c5010000c400004a0501084000002e071074003104051400d40300050a000b82c800302081080312072802c00604280342016541a90f45410b104905415100030b520206102040d001e40400b083c081c00044001d14046003610443c0d40310000d200554004090100340c2c1e092140940c0c40b9042000040c42034610b590000c032004030a071201043c0d40d48070070700e0310403003110074a80d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 904232940 1250 904231690 904231697
    0xf0f0a121103090a0b060319140607020a0807123b060702010203190905030f010605010201230f1b0a11060c031e0c2802070b040b37 58
    0x18a40d00e80840703224a4211000310314410340307545032448256031542510341d4000c5c203500d501000b081e29900d0800c1760405c1000002c40310000400b160804c800c1c1c10222888005c9540300700c40019146500c0404d44015440e0300c0b4030802e007003c0d0b4507a51082d42000180d0100100120f0948008055071030f1000d00c0c3ca0b180c409503603041c40104a07110009103414000b0346c1c60051104000c01c50050361b000084920080f030351010b0a01180030b0900c1140c14070b1059003c2e0381c1c90700c02c0c0a0303003126541c010f5000604a403000d0700200311f100440b454095098420405060106881d8400a001040b003052200e0f80010003101c60301010482070342642d800e030081c0000000041051160b2080c92200308a001d8002c54012102c074154030b04060000501769070301e00300f8002c4080810114504800070300aa83c50f0303404001e1003041080c500031010f08140c603144030403001072095003c00201410a0401c41301a1110244150325282c41c003054018cc903080d450300b69441ca03a00b8203072806040204281c0510520725640d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 904234190 1250 904232940 904232957
    0x32a0f1103030405010e0f0d0803100602160f0b030a0f020c07032f0d03030b060d0911091909150c020303071e080406050a020d09032102030f0109020f0f0a 68
    0x3840000c054424840a01a038410401070100e0780e0004020300304000100ea10740f0000d900e8070040b541c030401048004014040201c1880045130b20700d6158400c3d02d800e40d088606d111111851b0300031b10803180c4611414000e40607805d114010500b0700455000d29110008911800301401d028101e07802440300b40e030182c100c12410300400c400c00501a500c2c00350481004040d840c0c02119075011012005c081d841910b608280c482054001c0e04a0a4a900c008000f981c4901c410340001018084400e02110f01d940743c0741c0b03250700e246800c41d01140030700f0b0f42d080400e03504d111003100c0000901170710005461907406401c0d1100d0043c00b03401101803600c0c590303014549032f003007195000d807105000d81640c250b040f190300340700c0e00d4141d0f0000346982d0007500300c0d85c04070390f946440c0900402403142c140c1d1811203a00f81581c3c0800e16800490840403e9006c042c0e20b181c080d1940040c80480c0001c0c1e4560b003055000c01c00400c07101c0e10640240600411040d4214500081420000b0040c0c2c80503007090003251048 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 904235440 1250 904234190 904234193
    0x2003040f0503010203040c170721031731080408070f170a1b0e070306061812080901050c03270901060c0209040503040906090b040f09080304032a0f 65
    0x58040d00080809030025425401e1503552841c2190541c05515103e44060b103062007401c4041000e90014003501101c1000c1000d410340c0c126869858020035008a1140c0312001f02100050308402e00c40e0840a9030118040c14280412101400c100b910601480403203039288082401c0c0b000a100030121840200703041880c0051040c00e002484e40440491400f600550000320380c04140c9428403a03201d0202c4941300d10152420700406d0468009000f22021041004001605a8400b07420345090380ca40003020300039142c0780e02c82002c85000300b044900c3e01035510b00001e5007003005050901c1050501909101c6c001c0345451443d00003400b02000c0307184c90302800d1102c00380510000c2d1400010307600301913550f0401c600039103084800003000b405491900002002c2c03103002e00a8a01410064005201c42581d8840b00d4014047c10b422062055207003017a5040500076901c40d03002d05680c001c3c015415503460751025103460203442000424043c0320303510980f60000500840070304034401c40c900c545050b500d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 904236690 1250 904235440 904235459
    0x4030e130204080111030402090117070b070302010c080109020c0a03052a15060613060f0e0a0f03020a141c1103070b121e060f06070b0408210609070e01200304 70
    0xe80e01c07911005c0404c109000142e126030b84694113450000c04c1c0e40f9041d484c0407005a10344801c550009600400100e030a40416506400100341e90605941d0b114081e601e4924190480c4981980c1602c03a520052407000000e010320080c002208030f1860805030070720401150341025050030400491034000409102c2c40c1c20220768181e400c03a105131800b5041c9001003041030038400311030050f8828000e00b041003080382c0e4801c144e2030b198644007070a4407055a0343c42d05052a50340c0c041c00120700c40d0040e0398021408051002e01100d42c3d00d0001c040c040c02c1008180015070b24201e44c078003a260f4038030a440304511624104580d80c010107404801c075170345100c40c0d505144156800742030144c030040c8540380750300d40c0c1d00b5017405a50040001c81e80300b940e4078510400600750b80f0462000070b14008521041005112000d800381c2020a1034034070241c6c80d18004441050740a100701c8990303034000c2d0507d0100341023900c121030031954078006051240c159045a000d01400401c0044581741550001a040c01034a65 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 904237940 1250 904236690 904236701
    0x501021c201c0e0607140f0106030605161722061a041406030c0111070305250605070f0f02060403060216021201090b06152206090501050313020904030e1302040801 72
    0x40503e08641201103d030000340d007500c200407003c0c0088000590400d81c0003000c2c030800c0300091141000b001007940e00d15062020b81401c44031491040b4040e42400045030082600c4480304c5007040080030b2030381c2d80c12004400c501100316050350310a80c0d07880d2000081e42620030b10380c4a9000700690481d00344a10100019190600d02c103020768884c4800b4070003903880c0051070099100d424204002d0783c14120000e0f030b15040c4a9032020f04039200e1080341c1411045181d68526221403410080c4003001d44819040c1c3c1e9611a42400400c100790070030902d008070782181c0030811660303c0245224a441d0f036030b4031250240d8005080c10b0241ca2820100c1c5000c520b0184100c1305007602341030080c8901085a100e01e8007010004107014012000241c084041e80e41ca0300c101e03000300040404244007000c5916810302c114415019244c04501d042d08042203540c01641aa403081035070a5000f0346400b0360350709101104d03030041c00807024040000c11003426950790702ea1421001100c2100140c40b14034180c0001e080d5030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 904239190 1250 904237940 904237993
    0x3031305151602010c02030c0301021315030e15041109011d09160501050706020d060b040e010621240b07150c021c02070503060708090607090501021c20 67
    0x904015002e010a03495600d071241c2902400d05103c0003c080c00480c0c141041d090710b59a15510004800600f940216012401d503000c00e100500f1104d05030034160125601c2d90b441e000303070b80e004503903840d8800005022994013610424007111000a0000803c0902c1030a030070410035018000100c1368203d00528800764024070510040001413200102000100e205004030b40c100080003440000380807450f0101e40da0004046000c1004990316034032850302e50005c0c047d0003d000301c480c000040b028414580b40503d2207040700b0101e1040c0000e03005100a00c50041c060740d020610030105806a844c00c00900c00a00c40c21704159956146450b0220180300081d02d451882860030310450b002542c006110413a141c20066103800320707000d81d80280c0c0b8100c0d06501c260303410304c82e0f0070400407040e910138082d44c02180481d086078521344542d50165a00911360280900681c8458010001d14025404400b04021203050212400842d40325070110b400003c9154411540004268215407103001e01450703861 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 904240440 1250 904239190 904239229
    0x80301090e010b0a0b04090f0b0907020d020f030304110913060e010b01020114010f03080f0c0a120e01020d1202180406090e120a120f060806100f1707030b1503031305 73
    0x145e04004d00450940614080d08424075502c035105440594554040240c1402c014041c501525222030025034403200714420300010300900406050202002054074001c5502000c1d1300350090544091003285c1e02c0007461085c80c1d0391740c1d141e104007140941c4182c143c01c40c8458000300300e01c8075800029080d650510b03400031051102d040100205042a4003034401d0701d81c4031004a64504000c241c0003558020640e59455034010080094108030102c83e11503d12082c6841e0b840f2400101c5005984803002d00541c100400d004070b0342c4800752484d80d80200400f070f40174440c40351140c00e00d20210b02210110b8200007005603550303030001c407a800104001c913550109800454507010401720010901e20041840c00d01c4251990300c401203c40d456081140502080030856400b031070100c00001500d203a610030303010304011716200401e0410f0700140343c849043c4014024400c00c0d10703651318103001d40002410303102e8400d0080c0c0c4080c802d82c2d040c1b0080c4260360065a075003404c541410701700640c0454890018103035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 904241690 1250 904240440 904240459
    0x4050c0d0305040e071e02060a0f021213140f0609070f0501140a1218020a050f031f0b0619120216080a091806030b1503190c03080301090e010b 63
    0x2960140840e42030784c0c80180d6140342500c83d96070581c1c80302c0f62121545880309154240c000e580b940095031500c1030946501c148100031000d60108100e12a85440b040c40b144104002540d130403403515040d242601c544225800c40b0f810624160400c010130718503000d5034000e0028815011420406c5101800481500841031464000042c01c0c03400c21882146241d030000c9058181c0a004602245000600070018003c58046c000103840141e80f1910880c401c115102e004120742c100b00c04d50b00301900c000b40040800384044452914480c42c1c19034030801c103507150781107500f40780ca800300604000740000d501400014201a006001401f802c06143d11040c410301c031000002c20394072200e00c610307500145003640e214081481200ca540468001130130500840700c0c6060740104030740c80901101d00400015003141c640407001d15a0680c1e50304d005503d544032460210344010043c01e000e50881c424881603440d0760b40c1e5959030501d40c0090b031103111019070700c426401c02040300380200382c041d1408880402c003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 904242940 1250 904241690 904241693
    0x3070501090e18191b2313060e090f01111605210c0c03160e0c04090507030203150d1a060319290c0d0f020d0905010504050c0d 56
    0x9081052189450082c03400010880080400000e00c0c103540c0d00b1000d0312040c201e5110414000e02c0100c030101e690110701900402035400d00c81c2c031701c0c05407481007803460421030b5802d21081040d804201c205900c59a02003200010b8490746c49484001c25940b1402c02c42c52902c0070403d400c05503070300301d8940c0741d134103040b115003515042c2c03411600341071104036001c1007440d01810403500c0c00b102511256403540200d810f00d507044100402801c0e6801c50b9400311454201c424051684501d10f40d03900340442c00a010080c000312000d1246198000c0e10701c204c4609181e03441e150032090b500c041d02c80c0c5022950020038008140491210f00303503603407401d0f0382001d0400306a54542119030036850902c91122000310110741995001c4c0b00100c801e080d01e051540c0021031906012a600181e1280020030344803802014551003082c032180740c824206440d130103041042100d00702d03014200d007144001c0380550820684800031041d208441340079001d4000000c003484d01c0d241061070322803001c120522510884800780d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 904244190 1250 904242940 904242947
    0x6031b1707120609060e06100602070e010302040902030a0b041b061715040b0d0614060a1a0c1e1e011505150c120d0507050403020d020f180a0b090603070501 69
    0x404030b03020800e9050803048281010030040009180c0144001c0c00c240c03424000c80d500050301801100700040914190769140400d80c2c4ea4400c611841651080c442c004001600d03155010b6000540007070283c440c0e42195656500381400c0c1100d04541b960403090f28441e0107000d543c00301020306403605060780721100c1c440714107584a40013480d03a030400d1a072003800301c1251259080302260301006800c0421107500d61911001a0400242c403c1c584d550681c0041c00900d001240e5804886500011400c80800d40d090041580d00180584845100e2100c0345080c41d24140c0341f41d03c0c00410724020700011a88006203449210500001901e580c1c18400d40004c05440100c4400494100300d03407511003c6a8020801414000c801c10310646004444c041d01e005051140188081c011189003042035544070903082d607540c0a203004c041c0d08540b44c4c00c181001070404064034003500030f0050032420046248203d2054040c800c4038161403041c2c4411801c2d01c18100001e0050300310070124040e10803241042c000a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 904245440 1250 904244190 904244203
    0x207080c090a020705010e011e050604110a05030703020c1e371e2303040602060a0c120614040624080c070b040b060a05300304050406031b17 62
    0x50145980000d03d4401c005c003d522102c00b0000d848024085a00000607080450650f440001c2c0d08d0703402d0070002070f00e924191042842945000311001d0400c00980401c4a8641004144d4802d2550070004401c000c602042042481008000da202400d41d0a031001802c10b900d0140710a204c100800c85030b5051545910b222450b0440449a06002141420b100201a0f841da10b004010381892420000b48403070f00c10915070f8a144c1451058000003240c0c0300680e24030440c8103400042e08400041054100960414584030b0503078540410440b004856030b20071100c455010b10300c40300000404080301d0606000d40001040100521108210103035146189440d2030079042041210442c005020396081200b500c0e103464114424540501c0c1c24a09043d480009654251081e200b20701c0004403480c000301c4e04540480c10308400c0795144204000170700c003600320041011030750100303110120303541e165842a00000c5000709064140d030307040c0c00700f07034482d01406811405642025500001e000e0400240c413 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 904246690 1250 904245440 904245451
    0x306030d030f06090f05090c030a120c0f12020601080c03030708041205010213120507091a040509031605071431061a0705060c09030a020603060d08030c04060207080c09 74
    0x110b0461a0710101c40c00510b00342d045801e03424981240401d480010368406c030310403000b110440d55151150020191b541e1150540201500010101d0941440c49071911418007846000700c0d6008085c0c0365101c1101b00710a0002100580c8240e0040181480400401c03944002c16070181d842c02901b074407480c180388258068401d00312040180d017002c0150035411030368600c48078018440847d03100d160100640b500690203031664421454081441160361040105103003213480324900940e003a41c1404054500104030200c2c2c0d010a0180340c1c0d54405860b0b035840741911070809488800d0400300306a00b00d4480d002c0140c05440c0d205480440354800e0f2a40c10400c5400d01d428200100704c005907040641900d40042c408199030200c80d01800084c0800307030802a1040050300c0050383c0b0004201218003440c0790565050748443c000c8805414079100450700300b0805005100c08e140a6158200700f540140d0f20039110a000040c10082e490341444907030098040d81e0003074403650361200001010039401900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 904247940 1250 904246690 904246697
    0x70812100603270c09020c0a0b070e01080604091419140a0c0618050d0b06032b0c080910020a030206010b04081b030c100201051005090c042c04121101020306030d 71
    0x1103040500c81807494200017070990030342c150b55030341611401c5178562105082c00c480c901c00450104440b1400341544001203101a540c48000355112010040030b000755800c00e6550180303500700580c805009110640120780d280c02c9402216100d4542680580403d02005c41c854100e0913030040041e0100040d0021920340c2c2c900051400f40f100c2c5c02c184d50302081e61210398001c8407510403100704201c1c40c40300b034401c0f0740403015540310541c83c03100c66580b01c407100f01c40307086500304601080e4114000d03514150005e001e00d0106040114541c04944040a103003c801b015a221242000030554100300702409400342034009414913150401055890181c6607512008402d003444403044c030385040043c0c0345103031001440d426444803260303c0a4000c080689041000e40240030010405041c49502d4a0042c14601c2d20b41c1c0c5040d15100e54100d84041e1030701194440c00410701d420300e0b5645581c60070381c082c50080d0782c0100c84d02c44c00312000e401072010212062082e4014010040c0668001c110205801c10506 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 904249190 1250 904247940 904248011
    0x70305071107150801080a0507150909020708030a18050a020405060607150b041b0804080306180702010f0f05060d110111011811030a080406050d02070812100603 71
    0x1901c1c0310440c03840711078152040102c00226210303102c40b801c0078050b083d2160a460b90301c91580305d440d8408404060000d0f40007401c1001001200001c40b001820180341a01d40582c5070601e2200340e0b40405810348030040c000c028400f00000318410008110b00031549200040096603c880c0c41e02000800a8850350707941d00060403c0c2c070b13903804039007149030301403280410030101e5190307a00201129540c0724000c5290000700010003040c1d040710359084102d070320344186a64035a80c038500c0c0d0364001098250000105820740300c1c071004a1800d107015440c2500041140b03c034441d8100201c03010713a02504880c03400d000c20b000c000c0d04e6100c0f80049990300410045094810b180042e10040c4454a82908139841c14081e0602a190f1040c05100e02d0b01c9205c0700200303600b03810105a60703982a40c101600030b44040008200d40360045000341081c10315a1005814a003841e02d404100360441c483c0303940c5142104042180c4902820300c49400707401c060804202140d801d100504001e15621240c135040310900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 904250440 1250 904249190 904249201
    0x10140705010f140703150602151017070815040f110103140a0624050a1d060403060218030f21161103150f071b0f0624050603070305 58
    0x29040402d10740e072904010301041d4140030414503140b0048482c4e80009140010030304179961024500011581c00e41c2c0104003800c803400d400d206008010b0800705a1a54102000602094024007140540e03002c6010340207851501460074240061440b4142850070742c3c2080000242c078601a4150203608503d010301d1140c2c900700140c000b44010504c0e505251004000c00c500d200494004800f0348107070040d1540c08018074940c15200208540b040c002295041c403080e1201e522401890709400a811803100803440d003e00410801d6205030002d448090300080c0d10710604c4c1c850425410f12540a50082240e0741031a0341468a80d036941c40c2500c440000350904014114101040d00c130140a0201210100d0040e0300d4110240b006503c0124040d01031020310110204224644901c6011005441c0c48143e41d4404100d0304da80712850252101e06505610001045078805210355561061000191550802c1c030707119411504a10b201408110301c0b90b0522194490302c0580b6003250482c00c01281c0c68961 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 904251690 1250 904250440 904250443
    0x3040602071503140916050607110d080f070c050f06070f02040b040b03060109020a02060708010f06080415020309010902011d0604090e032704050f01081507030204050a1805010510140705 82
    0x1c0c0c01c0d15004080302c1c1d40c03d1001e507850108400040c070800846d201c3c21240e565052244c18003030500d002d00303070b04804004da03035132410568140c1c40314511400b0850f02d407424042401d071150b040041d0030399007251600024000c904006103002d480d464200c0382c8a09094280d5501043c1085408000340103079112098003056840756000340354000c80060030f50703c0329030f194160272009400090007000140b05074800303c1c81581c042c001c02410398030503003c00340e000c81c2000d009480c1090094011a60686111110303a1001900c1c800340d8010442d240001c03540c881c070f6000050104c46000600021071a1044220703525944032000c4400721140c0303d5010606940180e0440e003107008016620100d04403d0103500074100da6144001c0300b00388226020031060b1900507190200d29070901900c00a58049480f103c407500c1c210243d26802801840d01600e080d4440e004a5070784070b0240d03c05004480326211480c51000c080c0500c2e4090441034481e40300400c84400010801005a000000c0100d40084e6030803d0180 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 904252940 1250 904251690 904251701
    0x25020904111c03050d050114030604080307021204090506011205010b0406030e030d0c0c1509120c02121c120203100303050a031514092a0d1508060702070803040602071503 75
    0x1082800b40324030862400c003d8525401a440d51120f2441c080c000b1031040d107e05134003000c00740d014009000c603540d07603503540001e6070000e44454113501c500c109901003801d2940081000c0c24004a01248600b442d10000d40300035076500e41040b803542002c0050003030550007001c3d20200c90840c41c01044030710701d210303a85042d4411030f40340303440036810a000502e0058002103091386051203201c1d000010620307044031904540182c1001000c500341450400c840074412030221102500041c080600c241c00704140031302c0c0c4014a8001c40100040c2000803040c01e0b00000d0003052101c100c0820362442c40d00c004442045811400018240309010400d07003682c911a40c802e2000365600481501d03800c2d180d280e52a14011203118040c441e14005000030315a04483c00d400c442060310780040c840351807054449186580001c0e0b610080641c0e0780441241c0a030340e51141400900c14170014180074204024000e003841459041508940d0080004226840d40000c244044680a0b0500002000c2d642c0d0100c02401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 904254190 1250 904252940 904252969
    0x2b0b100f20030a02072d0302010e040f050106030b01030f0203011a0a0210050109150b090a14040e07090506030c031b130b27070c080d0c0c050f032502090411 69
    0x10000c507200300c0f2560001040019102d00d10343c21070110701c244402c1d00d800904605041c080c03c03401042080154010244558440b078010030114a03d510388184d00200c2d031007640f04000080c1c49041007a02541c041c42255034a92035041c4c150f1456040140300401c0e000c900201c030f0318105000400100ba03d1007440582d80c0d01c00050418405035a540f910303070001c1d00440c8513512107145103000005041c206002102d071400b1001d000200c4051402e0750005011040a0032541c0013a140e80c04003401120500400b0050301c50750030002210b040c43c60500d0f2908045502090080e484205048410144859180d0081c50220344581c0105e60310b074809409440010107060b04210940303e407404201800303101c80040c214207192040141d8038440121a05120410060500f00c01040745111141060f0002d54013800b15090081c0c808000d9618240f4089403100700d15450703040803516050385401958481e0348103500030000088444a9000074448410181000b4030b1440c0d407810111554441e08030360007012 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 904255440 1250 904254190 904254193
    0x5090f060f0a0314070b071104091506060917071211060904050c070201080a0507120e0a080f030f0105011d04090c031e0308090f150c2b0b100f20 64
    0x15507403490000c0c88180304100703190440c010940d000c94101c0b041c000340d9410b10307004503090030035142000c09d0100601d2140410385210710070290300c64004145020b0315009104e9a9502809075280103400c102d60a84000c00c200540c000d8841080000c031031484102040d5005002600d42404110000d8018407030f0090060b001810031080142103a845400b030400c3d94000c1e00c0d0b8110580e196841c03081185c0080b070344240401c0750001c180d1039001d9554801c50520b4512400c484603036407191102e4115400c486400d0302d40f45400005c104983c441c16480310b00414080c280882040c101c0d00d103074a25480c0180ca070714012a034030724003442809101002360000f143c2094003d6568110300301c04140c0001860000d0340071408120118a219000140c0c001c0101c03040ca0181450b84100710309501c4483c0090109440004148400310f8400b200304101d81d43c4400e01c2961440d40604600700109464084035101d200700c00c0401d1012580c0d0300804101f02003102490140011803903034001444c807840440c1c40380d019 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 904256690 1250 904255440 904255459
    0x12050c040608042406150e09160e0a09050a05101202060d020f0d050414070e060f04090c15090e07080f0610210507020115030c0b03100302220c0905090f060f 69
    0x105818141006c031403201650320240c2d0b090020060088080c8140e0707040303404a8040030f825482603c078908009513044000c040000c0555540c2d100c0040e10b801b9164011059943c00600061594903562040101040115281c003108960001031007406101001e503500703034001582181e040c90107400c175507212203190001c0010742001e040c020856014003400070124881d04101042d60b44000300901c2c45a20014100c044080071380060002a06007010b00710740c8070240300e80200d41d005401890710010350031544e829545500c0c0c114034440407203015000c2c00078460500305000700c0504c80c070192944000141d8040d001a078501c982120b01c61007a4078403d840c010144100b0511400a4010600440300c50340203004c0c3c241441c1090300e0314240c5200003060040d9803001081504002c40c040c42c4d100880c000c030440301540d02e402064180001a003031000048194072110045882032003110381d44c640343c0c644000c0650a01c400f1554a00c000b416480c2d16240c00d00c006542991103014020900d000540325600 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 904257940 1250 904256690 904256699
    0xf070f090b060d2d020c0a060b011b03022a10141e030103210c03030e0114070f020105070503070207030b130c030c030b0c03130b040302100c12050c040608042406 71
    0x1c42480350001136034a485041c9510703544014001d90f5000340c043c4000e8058896039540f140000d00107014400d050006020108079081140300c130720b410072800381e0050324007044000d01c1710030140a01030440d40c08403042c07a1903103516104c000643c0b03078009032030910340705000113a104c100203402030740b0b204600312150483d04c14203100d0b91005113040700c0c03040303400b10008941d81e00310f90120341b00340d5a00c40000d02458801004244650442041c0f503200d440005144895806081380da01c4086407654003003001d6a452204007503091003510b034010201e10340542103080c0f00400030b40301c00c0d0b64400035112228440116105514046440d00a1507000200c90104d541e2480e01080c200c0c06880103071422080c090010b480d14121b41c04892048000703071602905020035070f9404201c1d100c0030300107400b107220707110504000161501c03400d0032820381c0b91c6a61500c902d4484820301550030041220b8000142880104070190700800e07a5600705034030850010b80052200e03a45180c0383c0c518105d48445c039040110001c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 904259190 1250 904257940 904257971
    0xc0111030108030714030a02062a040b071a0702062a07111206220614090c0a080c090c220906060f08160f110a0b090f070f090b060d 58
    0x71245c414282c00c0d001081006210742c40f400341a6030040036802110004190445150181c05007244000c0c00c0c105000c881130021100c0e03001070b045450301c2c0320005422001d120042460012425204142c0c1015181c041e0f8000e40710500076200807280d0002000c01c1440e034201650340800151000c02c0540c0361581402c1c1403004078400750300503005407852000c80300380c03180c045102d620800502c03003601c84020158481000d611740c210010313915148d40700030742a200c8124203075080c01440510300a03c03000c40c40504100c00e1514680c8101c25941c415220b044203500c078441140d511502441c0600e4032081c092030048541046c14003074180201c108400800e00070b810781d00110903903500342d849401101c0e00d50000c0d600148103485200c1e01034504001510028070171425000c10441d90310b801d01512030070501d0a4039041209408032480411f00c000c00480c003008210100b0318124000c018088580790200c0c0180180b20344c01080001521860b48fe079168441400301c6040180d070740b030b0070031099040440a4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 904260440 1250 904259190 904259197
    0x1b052d0a090f060f0c1e060f230c03060a05060301030605041e0809151606050105030d020a08040603230702100605011e03180203030a0203031f15050c011103010803 72
    0x5501003050800301040340020640582d0985005482e10380341000500010f50b40000e190004442111142c0144200048020b40401e20f0505c030f1100801e10902d0742126405072408285920040042983c0c0040d0500d01c440740d981d009541e0002103a42ca80320b00c40850007111417038201e250040d40000c00002045416805503208a010300041c00603a40c03005041c000741d014915000e00b1003003003845021118a070204a5000404100d03900c13501d012182c2a008440c000000c00589081e40e90310b0040043d42414004070a035a00b60303101611101c40a0340d12981240118040c0e9420140d451600485900701d10003c4403100001e17801300280d0785021140259111404222002ea0fa4106400003842d0750084d22281d00202d0714100c5081c02040c100c00440c01010199803102800e8000c041c54800340c1c4040c0b00500492502d41e02460340ca14000300404860070441414010300659a501000703600305c001000404182079143c069070380d0440301d10150150100d8100b01125103c004000109180e001005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 904261690 1250 904260440 904260457
    0x503040e070c03090509011505130806070e0f1005070b0a060e0a05041e02030303070e0112181a0c070b06040f0c030b030c010203040f050f0d05030d020304060b041b052d 74
    0x454034501e4a030700c1070284880c6c0c00c4c032450b5851203c205411070454091130250204a80b94a241300039981d6803030b4442d1403d5030581d804008103800481200990902c14070201c1c070711a068480d009003040241004096200e8481e014203031044501c003040310200c164104000034008000341413103500780013030306100a00c02520119818250180a001c3e101680517a001542c1c1c0c0040146080d0390710504103540c402c4040b50850304220b10400181c0309007099200b5070035030740f0740804041022481440c1c40e03440e13404030080e458100360b038440c2088400362058048507011688040711041680700c2d440801e0103810520301c0f8820aa05109815400aa040d071145c401120210100c4138001d00c0720006a88a10540c0250500145002c905010301c1c208000740d034200d11005000424417440c9510745608580000e040545001c0e000010710040c4152406101c850900c1210100904044418000c0c8070240700e070742c1e00c4140b1401041c5003425036072214049490400c10f5420b2010301080b600c0d1410203034801c50701d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 904262940 1250 904261690 904261697
    0x80720090703090302060c13030b01030602030f010f0f030f06110d05070e041a090705120411032a011808070e040218010f061809020d0905010e0102090a0e040503040e070c03 76
    0x40c240742c8039024002c49940c040c0c024203429102c1903a20310f00d075031012011032105031084600100042062161a0080d4050000187c4908003000c100c0141c04040c0c2c40144414076244c4c0500082c92070103509002c50381c1c8642c039641c03544920311302000503040744c4081040348440403980321100c40003074000600c20701c216a503140e5506103a00c1000100c0301c1c9105035000c507988a5450950b02c0c100343c60686d8014140d802c2c80c0b8200202010100091002110202c0302c190220800320320b141020082030050180000b561040c0307603040940e400100c07032051a1503041041c4612020200400208007001825040003907590050300c4072528106414251003c90290b0025a498440007400020140c1610203550305048403c1c5085d0044552603035480d88404041c00c40f02e030004111006100030420050645030100d1481042d003009801c4411a035044075641c0d004202c0301000c1d80c1c90b02030035401c0c0c0700d42c40141421510307207040c46032a40c0210382003005d05c140144203001005800c10b40d01e200451007541c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 904264190 1250 904262940 904262959
    0x3020913110706020706020702060703020304030b07140304110a03060608010b1c2f0904061e1e15030503040f0e012c0612070f080114090c0d080720 65
    0x1561088030074950001d624030074240064400200b09400510000b0300560b0003504041c81c80d0009480365220300d80071070150b8030014040040004441e0aa507100a05042900401002c2007000e901488001c0c0000d02c45401024141c4c4d80da0744664031034002c3d58000310104001034850039050700900500d82040c2c82115401e00c18080d0700e034070007032503148154468241c5003007080c191400f00000304040c04081264a01b03420010050b2181089144245e01a10002c5804a418442000720742070b1207440c0801282080c014176100d40406540c4000d0390f9488030b0015800c20720100e41800c4e8546a000103040c0e010001c1d0000d0030561001300607041c2c820215004003d40d90341c0c520008403d0100582f00c848644100000f500340e65025031079544001d010b041782c2008100d24415900740005da401550958100c0e10b014805180300340310701c0c1c0d01c002c040503d0000380d080c6180c9140c1c2c0c07a489151081d01c10f00b0094100b004004007071094485540d0302c90b00d4440d540c0e54070103a821842200d0950307540130700500d2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 904265440 1250 904264190 904264219
    0x301150e1918030f1b05030406090909050a030e010207080f0709060501110a08090a180c0201110c060f070c05030a050c0d09060f03050c0903031c05090c010206070c150606030209 78
    0x344241c410070040002101c034000c0b01540c0c10344011800031101c4060005a964022403200081030094130700d407241c0055079481d4108027000e007a4030006e40040d00134514101e007450000d480050f44d041c029401d801c05800c0c406071a00101d10340220ba400440e014080c10504440902000036440145e0784e607080b09000458440004480a43c10a43c6d004c41c40d6000c20110b00105242c02d0080856442c050020302442d901c45000d420780c81d80500420b005107030354542003c00194288500300589881c01c1c04546001607480203030356104000781c440110865200003060180c2d0041181c0c0c0c5030198040d043e0b0b80c94410fa12400b4049401880b50b00f011401542d01ca48001e9100e142280250f94954403070511562000c0d904400814004000c0240c0190030800a01150340410241c002602e05003402d006900d4420030740001d451020700000210b601946031034940780e0b004241c2e00c0c0d05c02c0b90b0340b8241d00c068200d07040050900c141c03400c10880705e514044000c12506d40c5074004040e012000d49502c03021101c103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 904266690 1250 904265440 904265491
    0xc03010c050306030304060503060303040302040c0206060132160b250302030c030c030406090212030403020f100f3e0d112e05010b070b2202040b0301150e 68
    0x22030f0441e80c5a0400c01c001d02a250041d8040d6410080180880e400c054584d8042412a20030322825805648840e007003018070740c0e0109103148806062a50703826043c12407070f0710000c0c5098282202911150100e030304502d0b0300c018070700490040e400a61a0950341003481608252010940c2d02d44c10b000801214108102d009000f1a802000110300301881c580e22454031000640000d80103c0c0c4443e161807030000075a98074981c10681240034409035565510f5441000301489854450600425000801c1540036030081842d41d440d110b94140320380381d80080e1000420048107800b209507007041140721800048a01c1a40680c0c540000c411254440708118040d039207107011007042d11459009001006c0d000210110b860015018020080500c2074000c90340b006881e004d800c000d580d00070101340b81c4180018822419001400031001102d840c01c00210340d01e00e0345148070701034000c40d15020300c000207441c00d51200b000c11180e0303400c0304511a12451f94489034881501d10829010491402c6035100c0032 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 904267940 1250 904266690 904266697
    0x51806070804020319050316122712080d0f09122c061b010912050703170c0d0507030b0103060501030c0c061d06040309050a0608150d081b0c03010c05 66
    0x70000c00078030720741c031100700017a0540c03150841c215150301080c400c000c481c00d07080a40f4001140300c1d01025000ca542020001d0a40d10740182862110001041c070f803860760f02c1d80030480c2c00d558040b60901131001c56800e080d5035901c640488070b00d00e1072400c5800704461050ba800740b40d20500ca0140344030001c0e4000012109a12039614140040c4c0c1141c550000002c520840f04082200291013242803c84002144030700d58001e1150b00030994403640410200010341081d5602c602160070014101500303900d00a01c4c50140da103031440c50303040c1c5602180d150f0411106031003100803030917401e005524080c44010f0107811841e004c280800d00f840d8020030690302a010700e2039041496910910344410356110300c00645580d114101080349140c0800c1c0d403402e001e101c1c0610480c0652225070365a45000240310203070486034400410003028400307110702400928414a406d0034201d82e0010107440a0615010324490202010000c000782e0040242403900421180d0741c095080340200300724000814141c07020710 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 904269190 1250 904267940 904267943
    0x4080c0f011806081008030309100b0103060332030903100207080403050d05120133112505060903060414011104180506030a080901140d051806070804 66
    0x400584090855090800d4640420340341407416404110703000c1591014840a500b00d03800240c11340c000c0111801801108100408442006610314075002000c40d448030420748092101503140c40c60440c15a00c02c1e0418405103412210803101c5420f40d034003d80141c140590506000b00c581c1c800c032501030a002c01500c50303600c0080c01420382c2c00caa01400100039070200c4c0c02202c50040620010011a1040060f00300480740c948409645489101803018520340582c0810078210544416034801c824050209081e005903500c0144100078042041d5001e450303403000e00707840f03100780301000e64030008042e4240070144e00700a40c03850181d110310a220851040743c2800303400d58021008500020048558485454009000011124805450040207901903846482c405d40c200c052507100b00c060b4400d564004008400414090146540310040b500440c040c50b4184910825480300c4051050b086494000e5003090801c1a458450906050255941483d040900c40c0000140740d00340a02c6206025a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 904270440 1250 904269190 904269193
    0x806070c05030910170c032502070510120c05041a0304050721050307050a0204050619030209070509060d1a1503060904030903210f0203090607121b110103050c0408 72
    0x720b00c180900c0013420000f000030b41008210102c491a1600c10040c40d8001e0395554451903407828203a09001d5540007840121a0004503c4500c0c0c8a05030000760071000c4070700a0b5404100000c000005864991f50042007042803410b00e0b42e800f90301544a002041511607003c40b542041480c0c05000000340000c440043c030950280400303000051003403909400348418041c0105d04103084d036035618295001310350704696035400f425510045162501a03594044004c0e14034003003400d403c2d0f0a02c03840e40e0310361001a000700344c100044ac441070712031001c6484411000d400c03196240c412401c00401004031109094043e103101055200615002d49030041001c000c0d10194110384400c41000142000584110148401c0031000400140e11222076003010301c9c1ca0036241e08000b424a80500b07940d012160810031900100030450150362480296140c03541c1082503504002a40d050584050065841038114a200c1c2e020f600c04010340c020131f40341280404ea80c24410f548421800f00302c03501650003501d401e03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 904271690 1250 904270440 904270447
    0xa060602071716031109150906010815030f0a05060a020a050d111c0906060e1e060d02121b041b08040c0f0b04030c1a1b1005010902040806070c0503 65
    0x1c80b10091044150080010940303812880307040e0031902c20031080d80105c03000c041d852404000340c604281b00503400110811a0071030303a0300c008001000c02400409090601c5a02d0011400b002c21221201e4010403001e0308541d0200c10b250101541d95040000495052240c1800034900300ca081c000e4030107101580d1200d0b400c002c0035400c450094002510480c01a0805100400f166101c0a164040f001e130000000070355240181489002d44070baa80020300c4900c400c02c00d0000c9540b6038010110a220103002030210340e1244000510070b00181c0ca0003a40c0848010b506042d885804135401e25003541d0321b0401d0300042200301c01d1101b40c580d8189180e0201140200e0309003428000c190036030b4031904c201940542c03a074440c00503401c4070103503030000408402c0c00705060007085243c1c220080588140701c1244662042d89006202d80d206071a140c3c0f100000c0000a40d40038a41003000c00d1110010340c500b849590385410b0404000c1d00b09209444041c07080c9404105042e01406002880942150142d441c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 904272940 1250 904271690 904271699
    0x140301060e2a0d06171b04090c030b07031e0605090a0c0e03060a02041a090d02041104150c031e170c070804030605040215030921070209040f0b0a06060207 68
    0x100498400009480503400ca1950840200e00002450010320f02c102c0003460703504051710490741c0000800c4100840d44603207400700c1c6036a00200c0f40308882d40b0844011a07502c08178a040c1c0ca00e4802030384000c107000030007014040510b402d90845401183c036000c240c0301c90b405032402c09090710480e01c1015046000300c008201a091a50090101c400d80740c01c0000c5101c581c5808a031a00208496100150781c1c00b1405001c0c200b0403407880b0b1045ca00340803040307090003000d05c0011907500020000070f00c0b850b034401d03c94102c03601a40c2550020038208204140803500c2c460060510104d48008500041a90300c0741400d00840341d820a9110000b80c6c0c0300300d4182d2028509040e50741d0080e007001596001481983d0015404400800203140320300d1010909003801d105000424900d41c0d003139102c1407414420415040c0c00094002030f01290091102084090200c000107e44a0707a10060f400c451203800304003e1103614100c184050744207554915466603040160380880e5028012500180c002400400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 904274190 1250 904272940 904272961
    0x506030307120f0917160611121b031803010f0c05070303090507050604092405030a120e040207080a0e01050a0e0d1a1006020d050405060316090b13140301060e 70
    0x140030410741c10581c01d4503845e1581c14110700d0b0820324000380d0341d0100c40211940c1c0c1540010030010003041c1400c821426070a19095110a03c025004403584400b00740301c11801542105000036039075000c00e40c0c3c1e881c84001c42c203201100f9190403990080d800d100040d0b11040142c4103900051800b55515420101c46a80840103001c1c580b6042c1d54074480c0c60380200d01591071f44000c0c8028040346d0b01c002095a07515104011044032044c045400298080c0200465100403030500c01c03c80d40f14580c0540e50454a00540c1d10114005d80680c20920118032182005180c400500400798907454503801075a1013001112203100b5250a40001980382011a19608194803e43c040c07600c00d80d50f001201000303003000d5865000440340030311041d240543c1000410380501ca50008424203142462410f070820001c1001444054031507081a800e0000c100307807840c132a91207940600810007035542e695a1442c90b020450140707000f10000e0241e0401c0640d2a81390501c59081203035a040001038182d920b040046 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 904275440 1250 904274190 904274207
    0x80907140d151401090207050601090903020705060c0304120309031a2202130905010c08010f1a0a18030308010f060504080c0d03051207080121030e090a0207080d090204050603030712 80
    0x3420b9882c0ca9150f141040804400ba55001c2c0031005801030f114480b905140c0d00e03090301039014030743e8140340404803008603a01080c4038055a01c1540c2480d951101e000c03c8620754442c5520044000174090020402c069002140804481c0140b4a6402d10010707803561508a01003030312003032480c10710305c101c2c0c00c0360ba0b0b401d1005e84101c41c0004e060f10002c1440311507010075590085812074082e59219004412240c0201e441809030042844080d66941008140d0607040b6541c600b040c110440484c0400c2810301c1480170720341800700c100144e00015964600500641020701841e1010700c002000411030324450350a4804507516a4001c1030b513040400c4c28090a41c403104030690400908010040d80c580f43d505c6418081d4000d5681d40100e5894403e5094400360306015000b1041112820280443ea202c42c80c0142600101e81150b96074590800c15002407003401c03001040c000c0045000400501d40350311078480c40d070080c1c509029070340e00c10042540b07074415070740300034903040407404100300e000e2182280 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 904276690 1250 904275440 904275473
    0x9150109033e091b090913020406080d080708181c03110f0f0a0e06040b0301081002070302030a031e1401080105070e06040e0c0d050411032b0804051606080907140d 72
    0x1082c45d050110021940080c0c003107520507030900c4004d03040011414076100d480700402080018042e211801c15000b001c041c0c000d8841020002080c001c2400b0101040185260462510803a44040001c09540c600c03403d0b120581c00100b80340c109841c1d034800400c011602540c0303100b2041880d0483da40004074140e005a400c00d01040003a0541206a8507010000c1028041082c2155125890710400a1901c1d1520601540c0540140100360000780c0000694810424506010403c20303070560b401c1030750303201c071421038900c0b503003030422600d0884104c1e54464107881c9408000e11250361542005c1e5440410202c00a030814801c01c030070050380940805564111604080c0b05151541a40038081a2003042d1130503900c000c0c020300800c81d540340400c0890625107041c0c559501c0b116035200f0b0301ca400d0444100d00424082403900080c1080700c00e22401c07020b0b00f680180c0c111041c0e21800b00500100d021200e0044600c039250b40401d4901da2003464244011005101300d401d8022995030000d0003034105032 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 904277940 1250 904276690 904276741
    0x30b060427061701050903040f03151130060105030106050a0306081509010c114813020c0d0f0c0605010b030601030b06040509150109033e09 62
    0x100d0a01c0a039400384400410f4000b0340035100840c080c0300c070340c04c6800192083c2c0b140c2c0d00c00c20003004900200f0890744100ea030415642042d92007503d030b01202403d40c82255a01164001030a0350440801b12110440c2c4551030010000404540c180500361a1055a080b404034101f4401049901d10030002045004801e04d03004c1901907441c082e51346000d401d20200c900750070640c8200034150000748514400640b4074501540a004140040ca4858950141c07510000c03400703044034121000f059005c2125105020884690003003a4940308121140c036042c0248900f4018011741c00b0240385009490710342e1808000362070422480700c820389a180305203d440091001010019010840c0d91140500030300300106199174030301d003020005044401c2e400c442031254100b0700041c041c0f07841c2c43e5070741a440454040a081c054070b0440c010b80d0000341942c0010a01a80d071442e0740007403050309003c0b00542c82001e90002500184109121505076039003d2950003a0064001454a40341d400c40184a4100e551 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 904279190 1250 904277940 904277999
    0x60515130f121106031302040b1c0b01031103060c09091b0a0f0e0d05100203040f08030c34030c0213020c0606120105041e11092401030b0604 62
    0xc00c500c840141c076032000811141001e41002031048a00e00a00f00c00400c40307107940b42d8038100845444482450360060300541c0d4446200c00940c81e90388100544207901c000c0e130800742c410751808401c602c10900040f11007845c82d200d048528240002c0240c002d6802250f4541041d0840c0280003041038010510050190400c0c0184a8401480020a000300c0c55580d40940c0d0105180081c00d00b074003a00340c26000319004007501c4040341c0c2c0454569103455886030701607a80c7d151400d00003040784001c1e9001d080f00d40004188001010702c5030040150440305031010742000003009014070180155a084200c141c200d044840010748a50320224480340700500d849418125914440100d81181107040700075480201401b441c3d00e071420610000c02e10080c02480185099030310500b82c4500a05000524a864091107040151a2104860320740c4058030b82481403130050042c0c6400021258001c070f05c000d40101141d0307039522a005040301c282e03015201624051500c45101444141c04038540c807401c2800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 904280440 1250 904279190 904279199
    0x41505090f1e0708090c090129041d0106030b010806060706090f080c16380c012d1a0f03010207020301140f010807140418060c1805010306051513 64
    0xc1e0b030740030701030a00c55880c0580c524103458000d25002110501c588078080c1140100310300f901105c4011545412016180400d450b460141100d034001e030f4225103502c002c91085859249260502181240d806940500c4120707103441c01902c440710180c924640040040203541d0216542d40c11034000300d40316030440742050740d491302d0b42c0c02c1541050000c03038120742200c00790010a440c1914140e0140c0404070581c21102600000c0d1200c40c1c181e1040171117925180314903921420b982c0c0094031440d0382070a0080c844540910303680101d00c12420045442c2c90352250b229000c1200038400c060014103032100407035007a840d54040101621036004402c1d810364081010741c0041e2400e024070b0b541c041484400c20054140b11103030142d0884140c011701e07455800790034100417031842a00310110b09541950000351940c0c41c010062143e21003803038081c1c03a1900304954980004d0f441000d02d56000c1c0f14810105505403242c0c011000d940c000d1059030f031b0104180304410500c4031500d00610410758404016401555038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 904281690 1250 904280440 904280491
    0x30e060a180b040801110909010501080915070915031505190317070201081311010e010915120b1005040e060d021e0108180d0f120f0209041505090f 65
    0xb500b25400804000c03404000c0368109014542e088045e00a0490030a00c0080104600500500c500d604011403240440c0c1108024400c000840440803070905079071030b00c0940544500c40c14480c2c1807030141b207000c0c92005203101c0e1054000d607100c42e0100108152506040140c60680c00e1950050ad49604c100000000c80c03d104090704103400701203940d200c1c415070002400300b240080c4820420410b104000d8001040240e8540d10704e54242403104800c1c2c00340e00102c17580b5603a0f4101d403100c600606803500c0c0003a0409540003809040c603c0c144441c512581c10310500416003180d0750b02241040c04180a0080055541c542c08000505541c880c0001c41e0000f030a03091100c1d886c910340b080d600c0c13159045943c4c4030506035400213542610070b810340d0001d0005035950500032541420010714808035031300240f04901001c10035089000070f000311540100140001d61005a00074483c0740b505180e01312043e40c814004049480c01820b0541da540c820418050030710004200c044c4054107005180400c508 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 904282940 1250 904281690 904281737
    0x181a060d060e060103050f07030f09080408010905120c0706030911030d1214150d03022d16080616030e150114030a1101110109080705010e1603030e060a 67
    0x9800c000305000703181808881c900e00c80500118109400c03d410460110085500e868020445280020709043d503401c1e000002c1030501001401e100d8001b900107a0000c054100701c0e0a203008030260303021030340d0000f021880c612840403200c00c039400c801010012a4000d601181d0160b00500881d226030240000090030820f038840030002088240d6446040744015100b00c1c8030000340911200a5814641e0414007070703803132140c0d545106201e92a1742d81e04141c0b0070701c418002004105181c0c141147c45080020882e500724003040f00da0f12503071030b0000d00140c001c81390200300d424030000341480e92101041e002c182c1c9801d2010300c0525403500110b8924600801c002509800210b0011a4a50404982e02c45100c81d005503503121303601ca07041c40008101100c00711844c401090911424041e01d00090b00e003d000c05044c0a041500013140210520006402a00380c9071b0700d070380507140130007118905482050300f10300014002071000d03d074040d16070800c200104001d0240381410407401300070458641c040d04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 904284190 1250 904282940 904282957
    0x506010e24030711120708180f0307030b07021b09010510021204080c010e0f13020309010b370b09010f030204090f0c021605011d0a03050a05010213050a181a06 70
    0x141c0011040c440e604092000c5540381745441d445900d01100b60315030b28028000c82142c1010841a0040048a80d13075585081c40481006810781da481075a905014016450407102c00c0003600071040e036086020041b01c008244044014118100380c2d00300130034041070f41c90710464041544610701c07240001180d0a4060802010700342d0040c02c500c000b44000601c01c0c4400c1e03540701d00500d0748050101032075841d881281104405490b00503105d9648542150141445204440d00607910020b1130243c00c001407440120384005070712030314095032203003001d032581241c5104c0c4040d19a41400600032035072041c01101071003485458098245610b0b010b5080c01ca07201042d4058401d0780d02c0c000c4450840c4c0505c1510710180150740d25071109494040042d00c641001b59501080250040040c040d0340d0b81c0c4040c1101547c1c000e001c852003d1182d18103075002750f02038088465480a1407a0000e00380c58400142001d0750140b0302401a0200309218183c0601101c0900480b5118404a045525103c0502410030b00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 904285440 1250 904284190 904284197
    0x30103112704050d0306180b1f0c0b0609070909020708070b09030a18050102071a0d0606080117070501120e010605090c071703090703030c0c051905130506010e240307 73
    0x2d040a10b8210b00c1d10351440540d40505040210030000c5400440d10a2004502928007149006400700090001c406441d0180d851840c580c030030300c0405070701400306401c0b41c1c464140d98217903403a4581001121541103d070040004d050650034048652150040d140407486800302c6801d01c49655240c0c003440008490580c0280d2010542d41d81c19540300c980c04070072820202d5902c09181c24800004d40390b48042c0150902c5112518101c00d0600c245811211111542103080240781d03110200102240720030311540e80c0348428492948400c00c80496850121071058644800c00c105066201020b81a6a12043d1040d503a490b8000354985815007403c0c800e80780c9043c0581e580080780381020300307a00a072a180c0d0071548280200103041c400010003006a98250400480103480c5140c0700e1480d041640000f40c01850446000b8a00348000b10041c0c2500c00823264075428a0b1604042c000b125030856880b4002140581504c41a00300404800141c003054801502d445219801e2040c8603070060f44c001000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 904286690 1250 904285440 904285519
    0x415090b0703110d0e0f1012020c01060512010606020a11030c0a090b01030c02190b040813030602090a0503061311010207092310032f030a0525050603010311 69
    0x2e10703006008000c13030341c9924181240c1419005020034207540500f00c4c1140684010b0940860160061a4100e9140070682003503550341c09025085000e024148a4240584d81c0394070f000c9040d180600030030040e01c0541d030007042000700d281c880700a1800c80c441000d03010301805612640646035201034401038020500c003c1340c103180f07a600043c121000c100b021001c40d0000256100d82600c42c000200140703801105c200c40545450500c664117120700d50440454a00e90180002008019005000d03092001c0350810b580595503010300d0f4407400201da04580b0500c1030625100000c014070b4000319005810720440e0310040d01c6008402c12503089c545001c001414000714000c14806d030514240d806140c82515032121480d69650225002c85032801c0788410f18100030540c100c0102d0a80d0b441880001000c440b0510450300f81140c0310105814414103004407020000010400701c1560011950080d198500c0c40c2c0c612303141c0c002d8584a284400d58440c0e00b9a4500d08034a41d24034240ca2803170101ea002000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 904287940 1250 904286690 904286717
    0x908070c0e0a0e0316032604060c090803090d03030b0a14040b0103020405061606090f12020d021f090f0b0c12060306070801091e050703020d0b150415090b0703 70
    0x214103074018021481e0500b45050460301e410044107654012450b1303016988090100d141c152901031782c070201c2c081810f60b1a840760040d125880045030045015140811500103106021103003e8001e00509116504c204000002c50078030106007901e0501a1a0008508940740300080d0212040d600000026001d50b0030b10301103280502c100d904600e400d0a045181c54a0700004c81c81381d01492000911040b0450320728420310101e40c1085407440c2c0d120f80c4058088016141402c400c2601c460302000500c10450074a066500000320368103070b010040003260186403850340c054041c220307a68040301c51200f0002c0c40d074000b0707040e084814040d01d45402da07982c0750f40924007001801c500c01008144280e000e54240318141d9080710100703055581805d0003245a501c3c1c1d0070070024681ca82c00d8482052407401d4100080b82c2c1e8594060010044180400c3c400301c0c1d0581708020a40421030807901c01000c00300002c2103100745075500504002400d0901c1082c00e40d55400890b6140c018603403e802140da50f0400c082c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 904289190 1250 904287940 904287959
    0x4050310060608060d210f0e0315061005090d05030408060a06060905040207211d0307030c06050903070315090c120b1812071a180c040f0908070c 64
    0x1a02041204030800c1010301c0c1810040000c40b0281c0028010305803800080244442d0030804c84e00c010780e080c1d10144603440e944004048070b102200c1c10000608140607040989070125002034031024002a40400c0d46540f02040502c40c10f807441f503400e002c000c018403140ba85508060300403240c003500141d5203440c43d002c495401d2000081c1013080042c5000b00034400b40f40c100e0070207025174605490058480040340740410f82c030264022280340344400a0004815994801c900320810014412040300c0f8004400c103041c1c0c0c5501074080100b083e6140e000a0000034891030141410601c02011524070a41d651540407001d1000d046034440d00d0f440780700d18400e12818003ca80000c11403c40b40d855071180f10703184d80850041c042d01042000041c00070008428204020703804814016151095450f042807400c040343c2c0c0e442000c40d2142ca694500056124220031609000304942900540804101745081200520313406020050b621f80c0c8200c42e00110b52000080c000007845540d124601c217080c41000d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 904290440 1250 904289190 904289203
    0xe0906072715030c020d0206070c02040f020d1509021e0c120703090e0f091531120e0306011401050f040e0a0510050f04050a0b120703060e03031302010c0f17040503 72
    0x10079980701d045003400060340024009d81c04a014a04a024a1020300c0064060494846a07808640c00890081c44911580c2e0085111049007140d5079140c60ba0385e00d0080581c09595200c1484450117400904480c000c10006e202407a14034069918242c40000c0807425030304a1802500000c0c40540180703c2c01c0f800e40740ca5908411442d450040518150550343d54501d010080410801c403644082281a64054405c01305824030b14010000740240c926403030702c0444006401e440581c444413540000c14050351041d06a03050150191445a0070602003100c8600030305441410050100b003811140100c402c003800c00f030054800c03040003500b81507850340700351a40602000d410700d803d99070400140e81c03940e078011032002040d100851256100740086000340a01d080c0d0541150811031300300394540e03000c01e00c80c060360b20038101080100c0504203200c0d0f80b40811180603c11916085018000d076004d01c2d03180325001d00c1070301d01c41d887c60503079552030510315001c0c1c4c19065200400b0409103d2407800b44500c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 904291690 1250 904290440 904290461
    0xc14010509061f030c0603021315030b15071a0403020a080a1707020705091b040b0a02070302030d030e07180e1b120a170f07050a050c04060e090607271503 68
    0x44043c1103080d40c5450107803041c01d208590501d030f07002802044044803418010010310410b200c401d400d501203040039010b4000f8844140c0b0510701c2d41c45040d441c50005003615112a040b0900c02c609458082649100d050040c01c10b50552041a48040004601000805040c0310503900c81c1c1080418001040c840c000c0688150150741000d0b100b4822a214510601e9011012814100b02407840302103100c654442e9410007648d500b00010035902541e000108081100e109504642003401c00030001c5049074030a0044000907013000d101001280c0c0d03010303541218848041d8001504105031180317645040340070a940002c00e925030700e805003645065181001116400e202a007922129503540d469a500b0f203a01d03000c49510041024041c0300760042c181d800c40d070303800000c1791007030300090504554515002d44140c0c402c9043c21320204481515030394940c040e11180005100c0d0b52100d0304146c808000000300c0a003c2c100ca034000e400b08c01200d0107400000c0403080e00c04040900782d50350080a54414840 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 904292940 1250 904291690 904291741
    0x117010f0906060203071104200705030301080f1612020f0d0b01090509030a05070b040305091503150d0f300c050607020c09160507060c050901111c0c1401050906 71
    0xc01408100a48134265850f81c082300c0009000d0041c102c0c200742c075040385180c0303410706901240c40800c000d400030085050380c0310203084a01070002d16071000d40d02d5840000c00641e202c80c5410820400301000c0030003400d07138801410141000f0460b804500d05c005481b4064a004000c1001040f00c0013040c4100368010ba841c101440c509080c0300b1000e80107124940008003500e103084001401d051042e026502075410041400707013502a15075010506400036608030019590070701d002040707807500c81e010701240c07540a14860096102503d41d543c2d02110000f4650102c0180002140050035902d05040100b40d680c407038003c2c0601d40d05045143c51402850b100c15540011650600740d40d0b40320340c1992180200d050740008e44500c6100312142c0c0a8460010100c60a2200c100d1807182c108024003420301080c0c1e1968441c449001520341d48900c02c0851004240341912003600b903e11507100b19600780d001c0c102e4551821200032403642150012a103c80d00342e00804140050360b0f40901084d01502c0c00c00343d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 904294190 1250 904292940 904292947
    0x408180a0b0403020d050c04050c030a051003030f1206050616050c06070209130812010609060206062413050d03080601110105070e0d030c02040504030807090f15030b0117010f0906060203 82
    0x210300760340d588602d00000e84a4120409000200101080365150a00002e08103124504000703803c5812a002031320b042c0d80c2c007400c00c400030b01c0340d249100400c021680c05650b201d1000001c8041a0b54054507102107200141c0c5403500071800352161402400d5445860b00f400300c10040300d0070101c1c103010600582d1482104200545400f580e60903503941e800500145480c8040d8075145842501885005441c2c0000d10451000054194000030030303000312103180d02035a9242d6541000c0010400b09542c0074005010013104400445030031601408050918150003054944c07182d00003000f54071002070031400110b119003003000550b402034440b90822a018001e014074103050b0009492004812203e0713008200a4a24106044c0b0507400121400d0300500200554102418001c208100403a08440803426a05002403e602c001240d2000c545081c0661500890202011030140405500f043d0410507403441401043c0c00780c00c03185008281c0c02c04c403000182c0c40e00744040c00ba40c4c0c065010509540050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 904295440 1250 904294190 904294199
    0xa1211011e020a05130902040513020903100b0604080708030c0f0a0c030b0601030902090f040b1e1b040b0408100c09080c12120a0804050f01091505071202030408180a 73
    0x2a0704a00116420040580c440e0041d0070101c680740502c0724844842c484445000554a070694010015100e0943e9000450400e111303001c0181c2c85111100c54041d40203812124100c2c030780380c0c800b40507030740020300d440d10705607a40f1001da203081c0389500160015000002d10408410082000d4460b4a0b65117010304002400ba44410800e016144806400345d80c25070b000030201d0707105c2c3d40542c9111360300503d6843d03603042a2282801600e000c58080314290240030101c3c64820b00003024031854107001c0022042e941e40c0c40c0940250008901c11003a5082050002245403440710000d03002510402008202c0e100b8050682c00681e001070760080140540799505200e4040041440c8044c0c00d000e4031061007080c0310080041c81d100b1007401d4811403001c08604e00d40c449a000c44064050b5000f081100c103411942c942d02401c031401c0d06002040380c224804d944825001c950000ca0b44200310b802c0005503820840f0191040e644110740450f48054005101c1802801c0c2644944003810161040000d15061 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 904296690 1250 904295440 904295471
    0xf040609080c0a1b05010905100509030c0d060209040b01050319020913090b041a0c030a0e0c030f1e0d080106081e010e010914060a06050f07080409021207031e05070c050a121101 78
    0x280c80038075080000000707600d0300036241037240c80c018400280028000c003111b410068001d4005030107141c4694204002c2c5102e41d0701c11001e072401124110741103107c1000080c101c10003540002c0c000c941054842151854002051140541c0709004910848441c9050302e8641402c8110082403c03011410320280451021220141c0394001d032201e40006540f100741c04143c2c03501c801c9200d09039140c81a5405240c640e48017003007404c0e4005841180d004140e0341110150f844482c8854540c0002d045000100611032181050b61f030000b40c8403501301029440e040c0c2e240d40a100c00d0700001e003e00407410041004000c2885400d19000c2c2c18600c000440c00c2c244000382003020a442410104480450044820340103135048908171070340280180d95440e501c2d001d401c0a5008041c0000310302e80e07902c0015902901a0040f00900f50248040b000c003000d006142c4401001c01501000030030010441e0b040000d0410084051018020141d003a0b29607a0031b94020541a04229000000d03410104040b21a090 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 904297940 1250 904296690 904296709
    0x7140d050c15090a021909150506031b0403080a0903120206072114090106090608030414041d03070302011406013e0d0918050f040609080c0a1b05010905 67
    0x140d141200d890f49400c0340407403408040c1035019600105000b0308190400e400c2e20080300729000c2d0f80c014080503007040c840e11307403202d482c2c414141c01c18800c01c0012514031810302c0341450745040c112040d040030303180d80301c0d100103820030b90001c0c02160901078148144400050f0318604030001c0d1004000c02d142100004043d038200c7e500d580301c00303601109018951000b5070040424441d00d0700710038819141000845000c0d182d01d00c90002101e00e4240301082c1094040115015149001e400d040d408410000703200003403103c42c103a0240d0154140620364428402d0005040c201c1c0264004200c45d5886c3c0c0d040c1c0b8041c1130141c8400d050180700c1061401d64410041c800d1501c030032440312200003417400214007010220000c0344802c1405025188940c1742d070000841810703100f03140421a40074420255a0040311015201d00710b03903a21002c00600042c1e050341121421620440e1034a00f0301c049070300c80a01d4451009001c0b50950405544c0c02c19108101641000824007442d14611444c03500300440c0c088407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 904299190 1250 904297940 904297963
    0x3020906220e100e07050a0801090c27020d0207020a05060a0e060315030a12020d030216021905151210031a1b0f0a020c03010510270207140d050c 64
    0xa0300c40c2d0004000c20024400e424801001c1e8006208142d20248125158041c50244602c0f54040c580c0200c6c01c0201485219806a4403c0382004603d00349016503040782e19184109501072a0740b8088409210f40c0e0000d4076891140100142c0c940c070751481000456004c5401c028081c10080c022542c6482d4040f0750310790380c00740a807209a41d07078490b551004482203944003555010706c40d02d1008401c219003120111000011a42070700c40c0480100b4040f42030703202c2e4071050511200543c1100001d481c01c48460342017600a0302c03484a03072503540e20100750003c0441001f00c46400c030104001c080031000e11104c650284141c0190aa11340c1517540c0e11419100740300c4900100201e000000b4810500d5500f4004010464045140c4952581d2000c44456025088040050141814109050a05001d1680920810b02c0d9001100d400d0118805c0c802c43d0307254030140d4171920328181c0b04001c0010b1004000386800341c699101c1010510030a189000820502c800c1041010488002c0001000c105e510004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 904300440 1250 904299190 904299259
    0xc0303030a09020f030a08070201080f0103020f010f051b1c1119140106090c031a090105010305090c0a081606090e0609040c05100f02120708031902160b0103020906 72
    0x5020a0021603991340b81c102415070540b0940410001740203540000e840035038801d981d40b01d2942da0b2070300c0c9400e0080013880025040144281c010004d50700580b2540001003591400604040c6481c100c41000180d00c076200e40c03c1e03000070725503001021100c2080750f80034080c0e00341304104400100c50f0a64414425240b03030b09d900c264644000801200203030424030551800003d0040c10740b03480050004007011821080820729122400c004456610080031000301d00400b444510303840c0c440194080c1800a03c2200d403409202e1032409595141414100a407008070020020700b11017104000d80740c0142e0b040b039000c1c01003040d02044109030551480f0340c0800240c904400d2900c6610b0900300034103e50f00460303030121f481241d51070f019a01100120079104642d00300d6240903944280c0030b00c079114403a000340a810041000035004540c02046040c030343c0250500615003c40c41203d03001801d20140201e070094500d4004200350300e00010140e401810842d6101e0109854600e901074424a0000c1000038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 904301690 1250 904300440 904300451
    0x30a05010317132d0e1e04020d0201080403020102091522081c09051c0b0f1909020d0b0c03071101110d05060a050604141e0d0f080c150106110c0303030a 67
    0xc403641109044440d03504a02d13240f1aa512070792446441d8100300d9000c5246200e072181d460210383c0e1407948901403038001d0080c52500e10b0940046a011800a00070ba041d5902000f040722203850b5011442d4080351000901c1d601d0300701c02d140729400004030955500b64001c0700802032001140215031000c0c1050407400040d80040103060035a0058001c0e404968803104510b21007860004c4140040c517903910801850f0025552000c40c080c4410080d200c28100c03940c420301490310002c0c01c2c0d2040f14968002006690503004035550210002011224441c1c00000401400711454018500b01d1400d0041c40091141c000c0801842455004900203260384035101c04c04641c164070b0b00b070b001401614010f450710390f8550f04e54691811603011840e042e800f038859101544003200c1892200200312500509900c00344900391529901269407403000e80700a9401c2005951075241007102d520680e00148042459603d8828050700301c900401e0740c3c10b455003004050050700d90700841140e5109103189000200c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 904302940 1250 904301690 904301729
    0x602150106080f1e010e01051002010c0806130912051312050d050f36090f06061c0f06060f0215040b07140f030a05011a0403061a06030a0501031713 65
    0x11307040400c02411a420010002050303000d54410458182c2e001a6490003038842400c2089080302c54201a00d4000b40c45100410000c1c5443d03840c81c01c4c00c000b54000801c591070320f5141c18124541000039800807600029007049001c40044041004000c810412178996209490306034a40c1c10a1075a18204400025138012100c017800c03d81c2c4642c0f0482403040c0130034442200364100206034a0940910906d04020014149000d0008510a401c42c0410f5030242e113405060103050307080390518113082c0c0140c4201d420f12001e14850040d5440b0030903004918a890550090414280c0c08444070844d00001600c03854420100b036040c3d0490f621401800c1942c2ea4003608a076160501024403070722020000d90044a0a0041d01640c0584080c0c0d0707003040240d98070200014520816464030304a40c3d024441000440c180d80c1c0b0600c0003d26440040a6070200d9100042c9158402c483c102899942c810040c024440402d0315001080803007d200c52070103d4101c0030744030200c42071045400b05e4980020458 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 904304190 1250 904302940 904302961
    0x80c030112030525122304050f01050f1c1503050c090403090803043215030a0f05010816090b060d1d0a03050414010f0c2003060a060602150106080f 65
    0x5810440313058070302c4040e100c146808600800e80383c5080c00001e80c90340e5030740c1e50a0b9172040381503104070140304007519051605051002c3d07500d240441c40d0500105001d210300303003c6088010503e940061f4243c2502020801072601126915a038025603485011000e1001030000201d8031010340782210f0720343c61990b0300d180c1100c12444d036030000019404080340c0000c00025000300e80384802d804a0000c50f011040040c00455500c81c4800b056000b20b60f001000e103240700d11401560080910040421903400140034002911000e0b1b00400290340544188110503c006d035000d405080300000c288082c01d00c800003e411030091000c100c004a90301c005440c02070004c0c203e90300500442c0300c00c1e101d112004d03050103001034210f48901e0f01c02120036545442e0540c8110101c1e0001407140e10741040050303142c3c503140907852070809500f540e1010f00c803d202040e602000302303a206010000d400b203142c60400d803000b41400140d00742c00c5003065504005006694005030b1496200d14800d002140c1a980c480a90 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 904305440 1250 904304190 904304227
    0x30714040e0a18140307050705030f061305010b041e0f0c120c03060e090c0a1205100209210f070e0108070e0402060f0a09030308180601060809100203011401080c0301120305 76
    0x4185134507860702000d0454010000e059018041c1c82529a80369940c0141a12180e118004c1423141c0c00c03c10004400c8182c0281b480381e402e0041000041103120b0782d01040071070700e1101540b100b651444d0448030401f0198041c00e0411040a10240407043c06124007a00d001d103030900050300140c54100200e101c0748268001c00c01408070115103400c0c4d0a04040e45c1e40c5804400c0046405200b00344401b040c0f009407411080c0c8129404802050f2107080100440d0080d0070207188541d1041001791503070719481040604044840d0b846001c0c00e40c10a203080c1d1545400b103d548460044c2e087c072001048000d1010500c04112010241c60011030360b610b06c00580c0700d02c41e206c40d6071910360300440d82c5840d141e03001c940300041c0d902c01e442d480c2c05a12000841e91a503460880071585aa1002c030040c450345106124541d001844002154000025151a042071760426000428561500c080304002c0c2d607031000c40d0a03002882e14100c00d280d5410811011a00300c0c0244014003400b1000520300a2201a02040d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 904306690 1250 904305440 904305443
    0xa090323070b07110607080a0c17031008070f05061213140106050a05120319140a020c03120a0c060b010e040f0c0314060102070e0604140705030714040e0a18 69
    0x180c0350740503240d100d907986507001110156940414041d1094090078048200d0b03008030b41014802d07080c082d4032001111201e4074040110380d0a178071595080a8409240047c40c01a8103281009020504000c01c241c502582580301c186100c40d0035004008a4842c9001c55178500c03040c0c071101a50351744503901d4818202c0341c5407000b01120340700c40c0710404818065001d501916800c88484035015a1101009030200385c3c413000b0301c603a401c2080032084c202e426410150010303440d41000024040820300c90b00494201d918950b01507008101c0494091605202d100780e035400d070341c81071030411300c0e00310000b4110a0010070050002e07554001c0e20000380c1c050035891400c0c8800910906c4904803140c245400303030400c140400c000c03d007083c148006100d10150614480c0070103900030250189044031664140c0701c0904603c4c0c0141e0750720754104034070f8a1100d01e18414945c07a00c1e0b50743e0340c0c00c182500400c0e003140859003040101060205202c041d5a40413000e401a5143c40d000c60b003444608500d0b6a0304561480 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 904307940 1250 904306690 904306693
    0x30e013b0d050a03023904090b0a0903090b071a07020a2f09060f040f020c06010626070e0d140708010605040e06040804090e16080303060907050a090323 67
    0x1080c00c000b400104021501c1c030a130709943c80940c21000140c9100d0f1010340148001e0398820700b1a410f20034600442000c034000904c0400d100c10035403504080c40c442074415500d102d0311241c0d503109140c4c0141200c002480d11580d03041c588a00c0381c46150480d22a0854040100300d00c4010401c503e20030444400c40941003446203141400c010317942031142200c650682e2800903080007452462a00504540c400c580140c5078441003c490780801004110600c141d44030740b0b82c00e12044c1301c0310720100441406001c19454040c3c88900b24440c40c503e0b101c10108941c524a003000400c03012503481711a00c1521402510b0300040d14201d4134044d040400756008038605072040c4140050407072415005442196020303102040140d11010f252500c50004940140901508100130080003a86a01c841c02c0c401d0800103803001843d4a50003980e095241d80d2140311381d98008401c1c00303014504061225048002030a14a260001d203001c05081c4100610020b0720169030701c900011030b4400102d5500c0c20008d02e20 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 904309190 1250 904307940 904307959
    0x20f0d141005010905040f0602030604140907030303060e04050705150c0a030e04050901090302060c22090f050606030919050f070806150919270b04030e013b 69
    0x60015a24207141c0414603245042a00000d0300e03280e1881900d0040e60814002600001c880d12481c01039400913144603001070750782c0c2e070005000a4503041c490280c00d1100241020f9880c5040080a88980e500845c040001800522001401c005035500c12500142c5800182c10142c04104400f40039201c0340c11698003850301ea41d07042540c0110507400c03040b0200c40c104169111180058201d44d2401001009030f03001c00089498400307a038010f0800c4114201e2181001000081d500038030301021f60040c402030f07803103045141808003075020312039201030181e58050551401000c1c03250b40741c0c501044c8130300c000c02c620100c5003400000e020b45a5040b40c0c860442d070281c3d9850005d503503540f0007100d984008000300c0308268100e18003020141d00920140d00c0c04000f01801140c4800141180504144400300346003448060890400507802c4042c052820401185000d0030081c2188202c40e19880c108401440d034400c1d42501522849000d0302100480d00c6441030b0700980101843d000d08c0c080d544010140b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 904310440 1250 904309190 904309223
    0x5120c0c03071e150507120f11190803130c0315050a11030103020d0218130c0803043006050f0f06090105061801021005040c080d0f09180b0414160e0607020f0d 70
    0x4041022085503512200e40c0d27800307142c5807138469415100148904001c140355402143e030840c003858101020300010745590b02140c0c0c3c1d00050350380d280c3c8100c2d11040c04a000a80420a521a60f81d12103800c2d170f001d000b0101c00d5095440684414000207115511020400b025034540c84142d138500c03d5a014502003905082c600c061591a1a401c101c44110030403034003241070100401903400304c402080c42c90201d401401507100d095a0030042d41d0289200c10280d11011442500500380a039103201e00c11011420900681640b6100007408903008089510041150391205811542c201c03041c05280302c126040100100d08007440710903a1110309080100340010300180c019820111354043c002c980701040e0041e002d03103c40c107071055217030007007040503004000b40e0158070b1071721004408204001410407131800016040303680301140745140003481d100700502c000c00310781c0a0003030030400d003042c1c900100e03084000362541c4144172009000e00d682c1007030f25100d501ca003e071008001d607209581740d2890400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 904311690 1250 904310440 904310447
    0x90f020d0c150509030606150705101d161e050909070501081806060603060a0801050709030606061409120f031c06050f180405120c0c03071e15050712 66
    0x9001d061000d0442d1810603400c1c50240c812504c3c980030150241403103a440c281048482c0600c0209040300b510700300000000964184100340415400c040c0004a00701d0007003081d064000d1001c08012954401821002804843c004000840d6011306031204000e082e08180c450144642d03120341c1c2c000d03681c603061003881c000205409040d2142030303a801d0010b541b1002081c1a11030244491440c030b0b006400032a220341080c00c0110b60081e8051f205424040c1d88089150840f40125095000101e00400920800c0084c1c050f500041c1f01920385011844041d041c04010740c441c0f8414503200e186a080740c003000180500c4503101c054080b4003526100c110b02e524003034252000d1468517140610b408004a0a03251825140c9441c40000c1d00b100340030201041c411540d01000741c02650244106140300324030120004c02001c00c58074400145c0444000007007030501c0c2c0740687d0044c5020070581c0c403180058440e100714901c215802c0000d450200c1c00250401c2e0b0f21403240c0d441c06003c40403103d501d14031072500b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 904312940 1250 904311690 904311713
    0x10f021206040c030b0616030c080a0f09051207140d05031c1503150213080105151801150c110a0e010513050402010203030c09152208060705070204090f020d 69
    0x1000c2c0c07014042d00c01c1c525000c50844250008640e4456014001c2c0200650032661f0800c41d18805c0c10580d032a41d856440b00c3c441504402515000201072940c1c1010142d0700c585480024131054a40003e0301542c01921a100c4034980a011150031940403059075580d101042100150780041c25240e031880030405514242031035511541080d414445031520350940301d10301d801100d801c0760840704a4585080b10301c019502c8200200c44086201c035010540807400e1154034000e0b00040030b050707911a200001c1c032080070000710340c1074140c6154200401030700407100448401c01500d07151080c1451810300d00b03004001200c09800303400c440040f4005c92031355650071046050312001c403120b2940d0300c007405800d01550002c0710002e0042e01b06101090141c24420050b04c68100c0c02000c800f42c00710300f0320582030550008020341c561161410b02010700e030b04c98090707118081c059040c0540325a2810510242c0300c1d200c3c424000380210b82e00c2040500b0b2155640c4500041e80c4e00030440c100340d12480c10501ea8004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 904314190 1250 904312940 904312951
    0x80f040b0a021b010e040b5a0105070206090307080105090d360305070e0a0e031806130e0c1909030b0402100504080a0302011e20030a090203031c050c040302010503041103010f0212 79
    0x240c08140b0030704c2016010348010a9200605c90a52a08d1900001101e4541003650101e07001a01405160303510340d402d020442c050841c01d80001214640240b5080c9842004c44440c001d21500e00e241c1003048005801c0001410b0404040c00280711030b80e043d182e080c214a5101030030340c0c000d03404045080d000c05918140100001d00e07007800f00000000000344c0340e00c994001e02e02080312030001c0a805040100c064240782c0ba2000c5010140c0b543d920407078209880480381c1100d100d2000401e06031268000c0350300b4624200510704048900d09554076192582c002800181c401e150003614a02c0316482042198042e084d400182d90079801c0e00c1c50080e002c0c0206203a00403486a40d0010030100401e14858107240c6912225043c0740030a8840c101d0500b070b07001030960107006450307000170805600c08100420420301c06c2c080b0301e814180c50b03140d580111040035100c241c082c0d008000030001340c0c0c1c0c001d00386c94000b5046052880040c8410001a0042c030442101000c1301d40003103a6038040c4290724440364404c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 904315440 1250 904314190 904314289
    0x360907170c0c0a12170a02030c0909220c170a0506040605091606020d031109060a03090609050a150e06040b0604051e0c0c0601090513030c080f040b0a021b010e040b 72
    0xe880b19200d0b86c003030f80822142d40c800d151060050a480e07140c2070072141d4102d684100c0810f5003024031021807880d030400c8401914540313043c0208100c4000f0400c4420f07000d074100c05c064807044245941d000e0f00ca400c00340025201680300c03008500010410b102c000d203991107883c1e0808c2d130582d80d414040e4540c0c1e410615940801e2a01e03008105020030030041b0781070303010300030b0201e403410180303000035001841d00200030b07203010f5642c50403400040c03000c0089500c0103018002202c00706100e001c9840655810a90651190300400c1c18000010101c0c040d03160410021900410146d46140c140c1903280041290036011500c036905100c40300300144010030010322000d041da02e0030b070f80342c0c8100c8056600989d00401c808010554260109126503600b00c500d40c4036411240c90510078400d002c0e000e80040d088400c060328001800780180d0740401c41c10807681030340300381150002003d00001c1c0c0f41c078003409a02c0780201c1e280e0f101100c103540c4511281181010307601a031400308400d0749640103070100480018609 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 904316546 1106 904315440 904315487
    0x1150c060203010b19020a030f2615030c041a0402070312060303050414010810090510030501090b0a0c090305060a02360907170c0c0a12 60
    0xc01d03800d04102c5d260a40d0018010443c440c4003806019075210800a43c006604000342007845a0340d410301020b4202d03000e140b40b1442180c100c502c1b803098450030820040c1031502e1010810200c05801301c61126006c04140300450300781c201c20100303044002461420500c2c0135001000c1e40c034400d190000006c0c501d19990400d580041d081100810004241400710052110141016601c2441d01140d1402c20214540c805c0c1424002d4050140e10b90b070000322543e40614201d03000f15030000c000c1000c1813450901c004101d0090710481d0381c080c140514050300030320514604083d03a0700400580225100c017940d0600a520410112506420b486500401420444103c200c2140c560115041151441007081002000181204203000580c00340c01c58801125010360340c0804410380c0207540d103c052204074508042c0070b500401401405044510384d03540709003521603507051003044400d13 = true := by decide +kernel

theorem cover : BRFrame.Cov 904136690 904316546 := by
  have h0 := BRFrame.cov_init 904136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 904136690 ≤ n) (h2 : n < 904316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
