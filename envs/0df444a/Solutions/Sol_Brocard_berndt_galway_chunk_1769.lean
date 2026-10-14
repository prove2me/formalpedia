-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1769
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:36:35.74905+00:00
-- url     : https://prove2.me/submissions/0ad84eaa-ac6c-4b3c-818e-75b27008c586

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 317985611 ≤ n < 318165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 317986861 1250 317985611 317985643
    0x806010b1342030606030b1804050a020607050d1202040302030a0213020c070f05100305061f02010f020c0d031b020c0405060301111207030b0901050a03080711030d030e160b031314 79
    0x150114079983c0520626000f41010305040c0410380f242000940d08070b215100c0a4080700c11500858144001001200b0801d0f50180130b041c0c2c0e42d002030400c10743d1605c445107a000003e00080100302c4401c524000e80c0c045a9007d40102108070f140ea08000c10604900035025082e9424000039441c0002048400014111340150b1a5500e04000c28050124036015000d0249801c240512a15444030100c0804114055503a68252001000200c1c054221000c60489582c0007080c0d250640801042200261905403020401c882d45104400803070a940ea40601c00f58110102c007007031034101900441c0d400380e00180001000481080450080d41044c110300c21440551810800c040c1d0709481a40c106c0002100e04440715032425002880c010400d000c000c00c10390002c6440c208000c40303a0324000d4814070040a55840e2304481100074020b014040f0103010903c54441010400e040c0200b000301569000f215103461942c0e2482c0701d10140d0548841240d0b1491030a800918000083c0103a00c446900c0c1c00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 317988111 1250 317986861 317986979
    0x2070201080a020f1b01022206022a0d0206070f060209150f030c281e0e0a0302061b0304030b041104141501030608070308040806010b13 60
    0x400010225500241032110341e074410050080c42c0341c4520240e0f003683c04510441c030141810000d017140a409613012000e08640020090900c000c1940700321004d940c0e89500b241d8445141958140c200c010030a1140400802201c1c0c03820b642c10100041100c480c0040d00f000d2800c0da05950704488045803e200740c405030b1307011402c80300074a468200c14040b03803800341a0a040a40e00c268294080c030024204014140c00050610010402d542c9004107090000c0890444040e2805018010482482004208500c4481c5a0f1845400b46203d440e076000040c5c1500c40050440d401e014140c0c0c0503034203040282c10780c0041104108002c06c010300246101d402031079001c0c1002c5c80c1c0000824010000c0500c5103050000d000384e0310b5104528964417400803070705030000b060414010b03402015140c110b0941801003044c0802072010300c0000b4001c88040c541200e205a9070341c03400203038078061081054101d01001d0401c120603c000c80b008040340c0300d2000030380c00d034190f129070111510300c1078001700b13080968217 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 317989361 1250 317988111 317988113
    0x180e16020106060915182312010204080606060703020f0d030207031d06031911040306050907170706030f060905070c030216060903140f0609030301170c0108190e0304090207 76
    0x2800740c00c00809480c200486450f04040404c140e00243c0d82e0000e0400c1b1182d480104018041902c9000809209210300d030822101d0045115588040c10220b00540903c401200f80080503c00ca03000c031104cc0307018080c6070319100c04004e5180e000035000d40071841142c0110300e4070002440580410103060b00d00681c1d940103803801900028020500c8040b41c580075501c90710a807591000c03654040e00c0c1c51948815003894060040c001c01c65001215030303000b40880d010007040300d550710243c010081d07a01240e20740340da0344042640b82c0b50086c2d10410b00303401c00748007004294043d4000540710602e150b00031030000d131104046000c481080f15030000140e1070800700d000303140d0140441305070703010707840502046641030602c00b6103c2402884000e02e030101000d8034414130101807000380000c030302e81c80655140d803c005405540e05d800a00581c1c017440102004080000000100318844079410784905030b07141e803180c00d403416400040b1b0302d0700307043c5840350301612400405000500c09840720f5600161500d0607 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 317990611 1250 317989361 317989363
    0x9051803220e070807122909010909020a05091012030f030c03140105190801020301060c120509030d050c0a0b16030f0216020d0302031b070302010e190501180e1602 72
    0x41c40d80009a480350784824003581d554040700c401e90040c81424407800075845040240000c0458440c0c1ea0342c483c000001c004100c000c4461140c4440e80c08588c10403c6980b070b018107400b1110303201402940f1400b42c1c00c003001107040520311158000d58000310800e40341d65800b0002e8120840310012030020358044000401160503100b100c07019400d9103810426145210f42c08030707c0c0c200602070b8a1151001c00c1c41c45409900015610000d0b150410003551a0759660304003a220030039070b94046561000c2007001003580c500c14400d070741040b14020014204003812920a545d50350000e041d0a410b8082d14807024003240150040030300a40302d04071800c005692101000f01105e011207424282d00b0300400007050f501c1900041c0c9030b0895011900550845844d16060f032841c0306400f40200000500141d107400c07464041a4a01200c0c001e889000d0500c0869041208a42d030444092902280d44a030902940d4424400b1030207000a07040e940b600c0c5621040c148086038421074040440c214400c1c0340c1d5084c181c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 317991861 1250 317990611 317990677
    0x911041508220b04020909010914010203010812030408040303200a110906030703050a062d060303080721050a0f0e071401020705130509031603020303150f0a09051803 73
    0x3201c2ca04821800003a580f59140075002410107071144008002149000c102948203d80c0150710105100c607044540d00424044e400c00d1080c0e2038540907400c0072407018400c01088a11407640200381d10704d841e00390398054507810b01d44811078014549508404034030030401c114803034210340144408030065034010208200c0301c0c1e000300802c1c003d4101c09020000180001402c0705903d0303000c1400702c0c0948100988080d09051560012401c4002d6030030310405403038550106080d41c0c0299214060b556884800b40d4500b12054900d07000c00160913085591240240c0c08280c1004040c0d07804a03c41c006807881c50705464440005c1609500f00142c200000c1b90022001d021041007070018000d03091a1100040002500d0440c05c002e040d110400985041c406004441e18030708401c0c0409502441070030000e640350030454038092122a600700c911040e290030001000703010401007190314280d041c488001c020744009018203120b80c03099404042d6468050020340181411070754540802c072101c3c1d00b0340e50001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 317993111 1250 317991861 317991901
    0x1603050f160b010503010c020304090f02091c0c0803040506030403030e0c04020307170a0902060313050106051005071101020616120b0d06090b070c0c09091113052e0911041508 77
    0x2c1c0c980481121f200f5004804c1d40c0c100c480d04034002545800f424080c3c0d019100301040b0941c00000f010030140802080e00300141d80da80107031008400c0988a10340607076644298081c4641c081418400680024400e40181704840e20b040295940e03041058041070507030304199240004202041ca01107400c40029100513400f05000c4024000a06283c010405c01c2c84050600d107440c034440040e200500c9404d4006da0001c00700603100c01501c40d40500020036507080007100b110200c07425400005158400107400380542c950801019440d201071409071064101440307940131488d100c1c42440c0c21551008a900303005401940d0101c0d500f10305240000303000c140240380d103042c00440603511011075482c0c1240303020703200900d0700006c0c91400e50410040d217198018801c0e078003801c000d005d0348800f0401e4001c0745c0220383c0031050010f40c50100d45040c6c3e00d2008000c0f151540704c0b10000411004c001c503040703850509549020700385000c1d06c8007640a031440c1ca03240200041460603003032014500c01914812065 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 317994361 1250 317993111 317993113
    0x6150f010323090f1213120201080105061b06010b09030601080d140a120905010e01060b09011d060f0a0c02131406010f05090409030e030d141603050f160b010503 71
    0x41c02c0401d601c44901c50340303a444031402288250000d02800f074200251510b0307400381000c440101c1400c3c0e40c41c1c41903a104101008032603d03240000a5040100302d003490409034140c54114450b0f0034030042c400340390040400c29a80d9030300d03000b2030901e540003400810b020384a05d509140c0d88016840505285c80c1040e44219410b5200c8081d031b080195002044a01442c92110030343c0c0d880c0230300c10044610480b4503510f075018a14081c261020080154010081520303100002c1c064142e0325201c0c8201d0b80201100d26010441110300d0700101184000c1e10018010000c001500300050b510240c007040d00031888610200b603241c0703c0c8409501d4000e8031f50140007803840082c480340c030202801c41d58201e409052181440208040080103900500c01d071003910b8805807080005034410b040c0200410514007906000e8016074414030f03c46441003440c0301c1902c488140d0035103085100a07060402d0540d1600c16010404284a030720100382210004010f020b08014441400c450141440195044180c0c0f026100b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 317995611 1250 317994361 317994371
    0x91509040c11120705010f020409050402030c120d03180b01080f0c030105071b02010c080d1406150301051011010f05090f01060e010b131805011a0a0c080906070506150f0103 76
    0xc140c40003c024812444200411341c0b580700c1c03841c260b405490000212079429001107030118445901e0b900283c42903000b10100c601d408058002d000c0e840d81c00049580e51600701c2603a1403003050180d00901d50101c000d10f031084211100c0c0d150000010800c0c0c01c120010382003200310300c000c40070030041d0341c9801d901140204007500b48840043d12070340d03a00404039201c02c500c44211003907a003e040c600350165009000300d40e80d074207200b850100404c41d06003808d00400f0508040b031024181500128030008400c0411461070b400c04042010000290b0841410000382d030400c0c00c0c06242c2030044514900340550040b0f614280280200e040041c0c2c80e9111003503a14100d4100b11042d00802214111420100b02c26a140b0f500049031018607010303005040c14041080d40c0c0204101554031150488100000c44046c150301c81040420600c2000230b44400210b0f42060358002c81d910130b0091014020080c042454080a56200c07403c240045030064440d5804164859540c18030040485012600b4030302004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 317996861 1250 317995611 317995637
    0x50a0203150105091306020c01050405031b06060604090e030408010f1a0d030c1e02060711010e0d080304020105161b14030708070b09271030030203091509040c 70
    0x4a0040c40715004152000c5c0000600c8503036811914069600b4000384520b1034103080860f52580055050600001041c03400040d01401042d00350090308024520b078542450452118064000340d0b280816600040000003a0380c0f8091240f210312801c84107003c180c4071021001d842c4000c061104060080061100b0540000d0344481607003940b943c040c0344141900c5800581c084001c9100c58001d40100d4000303140010f1004812407019080402d030380c0d41800502030010302a00c10715603000240400c1080c004600150301560103000000b07450140d080c000b40554450001a00180c1000b40d00a000c032802030003040f03580741c410415800141c00610b0b0b03040c6440030050340c0d1112807058000d0000702003121507980c0d6501c1c0070400900070b4516010a48400c0003443c401010080d1618801400214000900080001a0001c2d030141515030a00920081011001440c000b410b044003140000c0040d40c1540d036400d0380d028181c00602d85216107421452090000722607410030064107001222032510 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 317998111 1250 317996861 317996869
    0x406090603030c301107060903020a06050304020d0c030605040b010506191112070302060907120c050603041112031c0204030c0b0a050c060a020c1c0203090613030c03050a0203150105 80
    0x2040c40e9016208030f0307a2031041e8114031004e20314045110615280014501d0819502c00c6004060100c503000b80c0704020790303400c03055411014504c0000d400003075a250400c030340740c0a60041d503070083c000f4210406050703007039550010421081d04100e40d0960b607141440103005442e86580d01508040d10202d140401d40b01098200d02480c9403900e040021031400480e6000080c0b04002e40300350000051a20313440c00d460302945640080b40c5100c0140306415001a1310041b004903601d6958001044a80041c280820301855500041050b500d40601c40c854610035120401030f5103051513910040c40d1102c100b46103100148500308610000c0c2c50040c0f0052001c04c0400040c407080311a50700200341d5403080c0c4803040c1d40500078404401d44c28000c4104100000310641c0052011450440641d407560740c00340c0c1c07280c48811251078a040140d100b40908091745c00d00d17000a09040e00d03003a4058402071717600d0ba21402544855042201e098100076910000c5003010000c502e1003d02040712101950b041001003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 317999361 1250 317998111 317998127
    0x402011202090d06020310031704180c030b0a09050703060b030411040207020112050103290f0f0601120207080a140f0702010e06120f070f020705091801020f18040609060303 76
    0xc40c0c890303a001440c2c85855550f0005540003d5102c0b606640b40d103083c50600800e28400c2c4070580d4803c00340c040c031f101c85446550489040c1d40c918400780041d44184001100181a403010b440d081c5a0b964001d0391241c1c1d82d03809014018169110041520b1800382c000030195000b079405416010000d00034000014001200e142c520b00e01a04c0041e243c40e101e0004031590b0f64105020f02404d850000084280521a411040c2c01031a0f41e20458590b002c5051201307c03a4800c0b80c08800d20701c185804036495600b48403455410000514000181700c4112400800f04e0f400180c045440745800904c24410a806c9165a441903030039001250525201021200c80b0b4403941600034100b01c001140f0f03000719600c1d241590301c1c880103015203842074909080f288508003426250000400d000040c180ea0b140e2002925800744c403405080101c0544501c941008880b41054a49003595002d0145c01d44c1d04416001600c030401c40b0400c02400b4641540c140000c0b107801e500050091410311800740080380e042200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 318000611 1250 317999361 317999387
    0x102040602151b04180606080402100e031e0c04050106050405011b0c150201090605062d04060803120406060509131b0b0318010e0d391514040201 64
    0x104207050f541e09444448122180744240311240c40c0400c0104420302004094030004404030410012141c9a140a61b05031000301c0f0000d40c025010038803413449910401200100c032601608032140d40030f1050701d020400301c1d0301d12484c0007030703000e1f034490441303454a03000d0f860041400c0d0500c5440d060030a4002040b0740021301c01c803d0761051040307400f82048034010026004000c403000203141d40004070741c000d000c0e00c2180c0d01510164200700205916103030030a0a41c0581f490326071610440341c0031031241c0ea1452040481d041d4415a20345002170711000900060104141307120103114646820310f401021900d4582095000d00d10710010402e01015180c0340e2143e00e0340150116101d00d101030200301440d400b90300404c0c10040040180108100000c446900c0110110000d00034540c0c0031481039a01c840585041c00001c030340c1d45c0b1801e00b0581c030054185000096645244d0070b062588095000304d0500e070750450300d89004003100780421016100e08840b04a80c10b56280041c1032580000704040c0c10000c07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 318001861 1250 318000611 318000643
    0x6101511120a0c0308060a0f14030f030301081509010903120218030109111804021305220b0628140409170705240c070c0b030f04030e01020102040602 66
    0x6080000020410810301c55001c28401240d482001007802422040160001c402080c10000800d05a2601400010a55400000079140a80760018616031640c84000c425010f00070f001c0720080a0342c0502c000c60282c103000c0e00401c21103410200b65021801c00400080299140c203003083c00007544040785c0310701c0c68245900583c4070000c0ba801075001c98800c580007949076207000701210800c01070b004861817000c400c4031200450781007541004088603040f500298001c230713001d50102194140e6405140c0051103c3c00e0800704481146d42c0c0203034403542407020780c3c0c08010002004414a0182c403100340c0c0708074000c0c401001d00249000c91000b4001401100199078207000d114406445540c4810f098075003000c404501a217101081d4541c0354401181a1864021040c00382600114030920103132101e8501c1c940b02c140d0b0742e1021541016000f9080481d482d522021000a028034054055030140c48402a101914209480e0151107200110382007815a40180010040e10b0740219444040342078a00d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 318003111 1250 318001861 318001877
    0xf0606090907030308060a0e09010e060606090603011509050306240609100f1101020a05090301140103030c0f083603120f180301090c140102161202010905130e061015 73
    0x40020187c0c2d085402c03014400c0410010042c00c000c054101354242811802910700b41e840302d0b002d1008030b205105459400c10400c10040010010410b1212115509403600d100a25280c0d4006410080240c0d1828411000009500441900c0d40420300304402e0848107289040100408268041040000c220030700540c2c50700d808185025611038000004240c0c0215503481c2c07440409020f5421a9094130300030361034005070b90070310200d094516060300c1d01903c0d03a0380707640083da8034412881c2c40800e00301c91250f8140405418281c4d8216000b217151401c0c1e0b18003002004c0d06400c3d0341281050120070380700743d20002d00886c92103a030604172065034442009203a44e5168070600e0b9000c04000326a09605503103044180740c1446042c41c03080342505d10314a40418040b441c0d03c012684d0b0506403000b400c213140c3d01c80080008180000f030480f8501d2045c10038003400c554a0000a1a0581001c016a002d0b5111620102c1415092001340c0d03102e56400540c0b42c0706418084000300d07040381603d17080c0038003a80c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 318004361 1250 318003111 318003121
    0x7020d0633030c0b0c031b0f0703110108060a0308031302191511062517010905011509030819021e1c0302090d0602030a0f0e0f0606090907030308 64
    0x708000103050105040c550322941002403640e01d64040601c010344000c0300701100400c0c2421001d00b242ca50a0280c001035081c40102005007030307550400c16542e0f0151142d00c03001350f0750a4040c841000218010300c0f0280f1300300c10520001d8200c0000600c21403044400c16014800104a84141c036040945411140c0e0700881a201250380d90001114410780340101080001e107904003020030320100da42e140e50348009450981c00040d9a5501500c094803148162a02d4a403c0c40140303800d25942082031824000c501d81a103d07600c2c03064000e13002350070a07a0f1140e0040c04201d5844401c00c01d0f01100b85000030605140d5104c1410301e004401c0e0344e1542d80c40042141300e401e8404c02070b400450020784401d5a8200308090342c0c0c0c0c2e030b030120000d200300a0744c00150864403890081c82601d081002c00b4003c6c544070039699655000950004000d10384950380d500c1d0140c04084284544074070030b800240200b440a0048040514011b401000035121f6000c441c00c010220b40049007140459038181007240c07103a156 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 318005611 1250 318004361 318004391
    0x6140a1d13050108030301050f01230d0f02030703050a06080703050c04151a03090c01090501080a090303021306020f06130804180605090901050714130308180d0f05010501090207020d06 81
    0x700c040341d1500241400004122400040700a604032031080f0b4080f01840070120065070402c3c2200d112844020103000e0000080c18050028034000c0c1c01000001807140550001c00120f8000f580c600d40042e41d10342c01c002d00741c02644076403400340a03901d00030300f181450356544a6a03900d580302418000c80d1904025544c1d50220040c400241c1440007282c0742e50041403e4090841d00222502c100c07611640603181c072294052a24901911710607035541e000c598907030f03c1c183c01920003940c04504240c1d00b04034044c1070450001a00c000740c0034644c041c04148045020042c0b41103809403900340d000482e0100000000c2500301202c0c01c032094103049000341c42218221100601e0203900c84d0340c0005201040000e850300640c0814403076503440d00d807941c1a450301c000c2183c80e8050000740442078124010141302080340c250140072040d4540b00e645144801300004586c03000a4500100c030000540e07020402001028043c1a015192942d011400c03e0200e070001010f0594001020b4060b9950340806400303c56 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 318006861 1250 318005611 318005629
    0x418060305010606120b150406081e0907030510050c0301060c030c080a0503010e07030e0c04090c080a03020f151504020d0b090f01080708030304020a1406070507080706140a1d 77
    0x41c01800803c000e82d96218007519595004030880d40151801d0700610b03040c42d003120318075091140c100425003410304001041d01c0078480a001c2c621607800e8000c2c80458407514513050b910920000300a000d2103455460030a28010342c2d0080b0301c03a40c0c0e00780010440400010300580341100c0c654503022000b2034030b07070609a43d903200c124005407040b0800240e988480b5000b8005504856102000252994403a1021000c85680100c51001900028a0280d003494260803000c3e01034042e640d418600c03503461000f51f2134125205800c601581010310001d00c946414800b000054000f81815802c03031401c40181210402884a03041c41240e000c00c4240710f030500c603484005500740140c050513041c2410703100b002c0203000c2441804040d04c00d03013101040800d404003c2c0ca000b44e601804494059060143c0603402c06028100705030040300912a075130100d5030400c80c80000b040e1100191041c40e0a06100070f040028078003814940840400a001c81507500012082d941c40d6540740200500c495107000500c064 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 318008111 1250 318006861 318006863
    0x5060609040f080c0c0a0621020f120f10050a060e100306170a02031c08041401290f120a03140d0f1b0305060d1101021c0f0905011404180603 62
    0x10101041d040b42d00d942c0040e8890b17590b0401c845950f2000d949110840b4040d600307030034401c404030465240c44062000c1c1d4002d0900012144c110a040000c83c10840e2400c1c60200c03140303030b00140d05400307000a64400f000c00d1070151205840c0450014140300740039100190f210303c803901558900601100061195001e00301908501e40c01c0700c2e46000f03220700c0342d030b079182c00c03100c241d110340550900c84013140d1062110081400c07050702c0b80109940d45407142c4110b0051110417030400d5480e204969800783c0140042400c50012900302400070030400148505030041e10407580c094461b421407050525070004003403018550518001125a2840802405a000e00040c0b03500c0d02c2d0800c1001e040201c404d8200841c07001660344000d841010704c18044068a0b400e981c002d8220310340303061501c08640b0003400c0d000c0555040c0101c1b48100020440c1d400446050030070b1200282510b075507800c4d00d0764040c2540004060034039080b081c0e1207009208000c503101b10320034503008400e00c1021359414902600420011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 318009361 1250 318008111 318008123
    0xf030105100b03340206012709020d0b0c12161b02040b120f280312020f03010314060a1b03090203074e0b040624061b05060609040f 58
    0x411560503000038603002c4e0540c5a01500840e4008526803442405070a0b840c0441507040c01c107443c2450750400185003a9400f82d802c454080c885101003170000054078020720320314038400d07902c601d1a8801a00514060306c407210115014800541d03050340058105a505108400b501c10220350348001030040080d41c01c1c0542150040c0c00e40e65107084045030b8002c510404100ba00c10120000d41c1c44c07866100d98041144113102c3ca407a071040860b11a01c4540c1e158650076800500d420320110b107501440d0000d0f40f00315200600c1700801c680c401014031850f600121040070030311045c02c0d03000c0c80e414450300f80b90410042558442d402015550100400401082100c0031400d07129100c52100341c0c0503401c841128012a4200c400155850380c2144810401c0c0410520295217502035a4005040001620907a2210b880b42891154212424900340285c4007401100707030100d14100014241a01c0c400d412074909602080042c04a0400f080c2d83c0d0303024074105d4140340d41e9a00c030303d880520413050900103820 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 318010611 1250 318009361 318009421
    0x2090405060702101b030207080d020705100f0510141c0c09060509040b0a0203060409051614060705032a0a1415010620012007020f030105100b03 64
    0x3488004607265004040036826152014800660038080e1203515800d44031880080002c9080e25100e64043c20741035100b034600324600400700300404c003660000c0c0e00c02c0d07a0300e0b00002420b02010005100d143c0200340324400601a61030314406d914107036102c41c030540c1da0047e40300b4400c143c42d50358001180c0380720842c403041c2a200b40d0350741810310403008113010b5031050515040c00407546182c0114554801e941c051010103903651005034020280d0809810395070045c2e190103211000a8041c03001c3d075032a01b02480c080441a103020190fa1820021810190281c0010801200070900c08000c8400f000a0075019050600c3d84603001c082c1c0000017000c410a90242d50043d00410091800c2008140c0101d01241c15511600240d200d240c0d100f0710481c00450421104040140b07403105400007030814000000845a518014420b03a2645444440f444240001500d404500e05855521000c5800303030000c02180c81c1400845020040034041d0b001e80d2100800003a03414584580c3d41ca40551228500d200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 318011861 1250 318010611 318010613
    0x3040f0e0c0a031a0a17010c020f1903140a0503090c04050919020a090212100b13150e09090c12010209030c0d060e0a06060e0906040321090c08030705070b13140d020904 74
    0x2c104c45411b21180020b508148130209a1440064000160030920001c0d140c2d01d02034403d1004000c1c0911011814000c3d04000040816000300160482000e16294955a441d1901c4d520303050604244481e44190702c1c2806008010798000f85080c0c43e1149428504118422030001a8031040c907680009003481c0005080600d0280c41c00c0c1c558060358a80d489a20350301e40341c1c2c01a0001c0c0c0a495050a0354400e1040c0030001c1285071080320b1504087d81c104660306a034030790f0105080c1c070004c840240b0203500c984451800c900b0050780d03000000391480001c6003400e2102c2c00280c0c131405983d034614410b4074807403202d60074811079a01c02941d0211020440c3e140c80001d03c0c121014101500c540c298092520b400107a6000c800300304180b24a034155140b0341c01d00401002c1004e400d013038031740504000b5550721400000902e4100c01002a01c1c1d00c800460719001d0509d840362601c05075410400c9171640c1884801600c408160300c54042c1d130048007103140f8000d0a080070580403190b01202035881059002400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 318013111 1250 318011861 318011879
    0xb01090e10020705011d1f020304230c030c030a211806030501061245061a0102030a0e0103050a09080d0c11010903121104051203040f0e0c0a031a0a 65
    0x141d901caa854070040b144501c0000c0f45912585c614026818001c1c81c5011f246050a1035401180c0c05846040340c01066a01300c41c022a07151040c9c1301c800f1544c0c0c06018507040a05d801c0080001c030310310450092801074129656441041102516100203218520441c0401e03130041501c940200361740b4000c4c0205964641008000c7c02082c071900d00421258070500c035880405014007141c864981220944c1c800b01070780074150030720450032009420b030405030140110100304281115420301640c800314241e2888941e8203100401003d03083c0c1554402c00000c01025041000701c05a807a090900203800e51310710580101805504c21300901700c1d07000141c80d420aa98603404506800d09560b54400056804010107003241e600340809008901d1444020f00021540d070401c2c441c004441035658205640c40000c610a240803010f412060382010078188582d0400c8507a000040c15085122003d50400031004900b9104200e070940c00c26450744481c4001c941c1c1c442d0700861102019201c032815a5840c42d0b04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 318014361 1250 318013111 318013121
    0x3020307060c110f15060409020303070f05011e05090c0616030c08040b03071710050a0b03041403030420103204060302130e1b073810030b01090e1002070501 69
    0x2030460b005c2c10340d010400f01e082034800e02d1565039000e0700035454103500d601c50350003124060404640c03035900c4490311200356079808040c00382c10f8102c9a01144900340081c0c0142443c0300300c4882400350384140142c403483c50020368203150385909410701e1102c5200d80e040241441c401c60b04481401c240c00010303c002c90380d00050000501034402c0352038101ea110440d260114003003c2c40740c1035200e2901c48080c0f0403a0401e00c001c503041481002403e5640400c1348210b800d541080b0f50a96102d001071002c4440c4041d200004605088120751482c105000440081d00c3c010b8140f10302d010300044050101000000d056203241d1030f020124401d0f444c1c55442d0303c000e020b90301c14460f1440c01127070004001004052400024002c0c1d02e0480340c10031100c140404d441c0c1e141c114180541c0c0300305100d2401e041da520100782449011142c0c42c0740b602114018038045640c004050411850030302e4078001080803400103140681594501040454247d0035030351010714100ca003100303140f04640700180780401c202c015441 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 318015611 1250 318014361 318014383
    0x3060604050408070816440315120a0804080706080103020d110d050a060e0c010203031902031909030201020a110c031c03060509180d170403050d0609050f0a0f0903020307060c110f 79
    0x41c800802c8848034008960800124080c114410300101d0220821508040024080038003580420f5029242d2b4074a4200c001400b0b6411b1f1300f00182c20b0040c08000e00003031010b00701c1400c1c21080c55155602248003d03034080c1000d4060078050f4280365013035560084014120780c200d030882e08042e00300d0504600628000080f211144501e10b51540c0750750001c81a83d206484000320350300c07c6115908174001035400100380e840110607002c2100c003c5500c501c81c00b15228042d90005880d0001c1040c00340054100d21003048044d07102c448030528558001840c81d054a80e04414000304079045001030340602080d0300400d500255060400403100d008040b1410715200f004103c8100d003176020000c1c0c400c103152002c048107540300d0740300040c0402e00400040c40e45181680c80001c0465030350b65408101c85080d21103603500604d040901c28861340b0303401901c49529034801c080042c00e5041d98083d507030384240c20000340040e445034070b190f480714003608407190b030700e44c0d4507044c0d80d41e14100030300130f07503c550400740c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 318016861 1250 318015611 318015683
    0x6120a05090601080a0c050f060f1308070b07021c0c120303090b07032c100606020c130c0507030305040606050a06050703020105130b0c0c0f01060f0503060604050408070816 76
    0x1300d135140028180d90a0380c001d60122000d90a06041c021003000e01c410080d0001d00070000325100c0d0601034000c2c80c004064031003c00b82c16041202e002d080c4101c1e5400803120721030a0000d06d01590301c1000f07100c1c007002034038003c40d4920518a04845c0003203450f4032482c2d851020110900600d50035070841c60321603100301240001940c40e0301e0180c00300c5035440308035500b801a0614078942144a01e0343e030408010300c0d0f070494040e0034012a40f002954010303044000160040c4907124500e0038800006c054210622900740803008000c8001041401480d501404043e1190081030501c5280d0b4007090142c04080c1071040390544a03680940150302071038080f4015881c10000400412404140102c0c0903031010900c01c03151600452104550005d00c0800650f0040c1c803000e00209400b48600300040c004180400c079214076100805041c00001040760340650b003064200300001e40e03080304940c1c566074409443d036120f43c84e4102040040020301c0300104140c3c107a51485060b41c10703440c0080d2407003003604 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 318018111 1250 318016861 318016873
    0xb0a0c141903061703090f1e060c010b030d03060e09010e060a090305070b0f1b03010506030406091b080f0106240311160303050604050703090308061002010b0904060e06070504140f06120a0509 84
    0x409005229404040003058514800f4082c41c0c89d1500c003009003250000000007180301c0103c6c8000a042055908010f008240e070b82d441040304a910717601290348441010000c020100140c002039444402c01414111200e41c1e8044400030140035809964145400c09488640361409114450740300ad01903940d100c00020b25401220b01c2000c2c4407c40381a0343d03000d003041e0300b10f4031540d031000003500480c441118501c041c00b01c8449002d91a19004004000020051222980368440e060856845070041c80104400100c181c0d103a264400342c4240007074075450001200e00400300e2048140c040d0042440010450344d40c10014541d158208900542048900b04003d41311800180c00303d03404150001c0100e4a0000011500d26120000c0000f400c01400013151251140b030015685038000c4a04944c002d5440c071900180b00002c1007440e40c462031504021340f4240c203280450a40d0003040f82d4607031140c440700c801a1074644601d0250395000501e00070032000c07410030003203640180c9812103921945100d62 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 318019361 1250 318018111 318018139
    0x101b0c0f050a0b092407030206150a050a030b1f0b0c0d0903050a02010e0a05040c02030c010609050c1204062712140906030901090f0b0a0c14190306170309 68
    0x801482044980a0003c1840c11111000784803140209042915803485c1d040245518050341d9401022058840e0380506100c2c5801d0b04d0038140c5040384030049018580b00b880501464407410701040940ba0131407010358842e96210500041c0009001d103101084001402c00a141800800580304a042c640c1c180c45600000e070504a034215420b12024100d640041c0100d40035500038041050840c4c00a001d0400702a00e41e4007144c1600c0d510074000c8016400061900083e040a218010150105200a03c01c50402500200103800b659118001e01030540f0042030401c41c031988030020042144000d06c407819039454034110b182c82d108400383c0d9500b03c03041c5a0805103205807a002c4500b4008070815080c8080d520503c100354000410100f4690340c1c1d0294040443d00c014a03d911a92060b09400d2492401c60303410700c10340300308400f00700074440b500c02011240604c1c4000d440c1e02d0b48200b203075140d03d142180c40031005004150310000c44401341070614600c544000c40140350604090328546590461 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 318020611 1250 318019361 318019369
    0x30e0102010c090e0a1401230a06020d11190f02090a14010b0d180f140a08090409020d02093102030a08070804030b090a0b0109020a020a02101b0c0f05 66
    0x2c60742003500140c0c81107001d210109241070300ca0741281c210381e40000c000c4004c4416264400c420f17000120711040045000700b00f400c1c13040e001c0110034000c1c0c0704203c90030715010000e0354501e543e00b0700c202030082d0550340c01d0790840b0401010b080750181c4800010301450341d0508d1814490310110a0f800b074000b810018482000e540541d2074044000d130003c45a50b843d190700035010341c01401d01c028005442d2003034480c5a041c0c031260064500e008016400c01c0308407510b00814450141c282c502011340001d4032070f1020848580075629811420f5601190814003880069030144003000e0007580088004240202c581c090101c81401010804200e02303200030a10442810300440c6c000207615a2142c0c00b03030310004264602a1500ca0320500010381003e440340d0b078081890508594011080c0e001400c004c0622408100842c010b25a03c032046181147d1410000d4585901d207001034064100302200044c0544924074440b07014403141105400d29070360746001300741c1d203609110381c1d201c00e41107020208852130 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 318021861 1250 318020611 318020621
    0x13051f0e030a0f0f02152d01060203090103200c0f0118050a021005090d0807020910240909020711040e03040b180402070f0506070906031a06030603100c0804030e010201 74
    0x61511011030b0f203161004112030130070440c0c4002086025020303031807920740403114000d8052800d2105202c20345c0340c2c411400d41ca0100400a00b501c0707019400c0100201d64000c022203000c1c207401c1c6000b041150030704000600140c40c0181e0342c6c031840c00000f180c2d880c019000c0340b02c008020100f8000c1c801ca444a05000006480c4280e024120390050b4603c07000628008989444141c114140181004409000142c0c0310f5000e03a804c2e81c43c42400100e401c01c52414600c0d80d0b900c000580820350416050a6551484400c0307003584d90290f1200c1150070762203a01a0181600a081031b01d0103554500300d920b031802102c900440721a00560820310000c140c6030002c016201619112041c003402d0420003001295444408002c09030801c1d03080140c500071420030b0b90f2488089001d00010030190401e42c80050401e0038070b5100104052a10002c410282d403402e0041ca182401140d02d29281c3d203503a00003038106520200d01800441c81c01810420091700604941e03c03c81c000e44503c07029081100059081e95 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 318023111 1250 318021861 318021877
    0x18050a0b220b03010e0109050f160605040506070f020a0b07230a0f1a0a230c0a0f02010f020412021309020901090504030c1401061715010501050313051f0e03 69
    0x1c41445014404020607404038601d000010004141104056009402c40b15103e5003554190404000d40c40d00324070070000807d903000c1c19070380c2402e10b500e420703c02025805a40034280c40f80710300040800a004150056030b2202d6001041d9071a0300381d9071f0f810400c4680c40140100d41d40b0f8a62400c0324000d0389910a824001405500540002e076100c0d0b82c0c204000342c2000b4100d030170082c20401d4203800e0406002251050704078a10004003802203c1004881c000112107005165250400b0018079034040e005407000e001150901540d00c5149070000d0b405803415401e41d0495500c08540050b503900341c15442002030b402990810ba50142c400c010710240c807002840650449400001008000c24640c0207d41c05402458200035400a5075550b140300742003079140c080310360b4658a0500c1240b044558440b000c80d40080200300c0601440725900c0d25510500c204c6060120210016001c02038040002001d182d1203400c1e1684901c44041d010300d440080e05601107083d141400380704510100200b259522 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 318024361 1250 318023111 318023149
    0x20306060d0e030c1b0a0e061f0509031204030303060608100e0604020f0a020703020f0f130c03060512030403030906090305033a0e0f01050412081018050a0b 69
    0x101020607000082c0090a41002e40c0e88000c10079003906503000e110b0b1241e8083c40f040d095001a503d40c00300810b07821586c100c0e21540340d040c42445003503a502c0050510b61030741c3c0c400060f1503500c405c0058aa030f000f00040241c1602400c03840180e4011104000d100391780c407a490800080340c81e00303000c46070b0020840d0144160141b8000503c0745090304d188240d4000002400945490074401840c00e86030040020080503901c806020310440c5001d9081c42110981a24100300b4454510006032540e1415082c03451010b42d21503403014694407913040750025120207072226169171040910320b84e0740e0f07200384800e070006800300341d0100d80d042c4981072860449401c20001c5043ca1000000202c0ca40d41c54040000e60070911b00c02100e11b03440440c40e410f100e40d0b10420008840941100741424010b60071030001c21a498070382040006041c10096410003420707850500c503580d41d00c88113881c40344019002040798610941c7c1c0728042b1001034000604c19079000c10140038585940090007103150707081c2c22005c48 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 318025611 1250 318024361 318024367
    0x3031008031c020f0f07210f1d1c08040e0703020412110d060e0d080a1517030903100b040b0d02060405010309031b0501020a0f090608010b0903010e0609011a030102030606 75
    0x38100681d005031410095075200c040c0b81c0300c400146100160f00803e82114940c00c002c0350f824001048601c0300d03940507c181005140401c090500410a00c190000071a104c03002c07881e14201d1f0b40310041805d0196818807a41d2228844900381800350380c001c5e100301c0304031005c1d050000325164030a0007903904a40140c2901940414a031703031201482c40760100c401d604041d0b1408100042402ca009007101703011000d01600015805c8070004020420081130100c0030b6040644092205607005001001c642003100101070103100d001200c2c0c118410290007550600c24150103410f0b0807405e9005214005048400300030070040d00c410f01002846206029510000c03e1004000950080d009004818424901010402001c918145d4078408139441910940e60201d03a9022994100c448000d4014590a141c0486454084000c0200c10140a601c6047e01e022130910903030f0310250410007403504d500080d00e03180d2421081c21802014080040d12078401c0c40c5520f60528141807080301d005040280445107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 318026861 1250 318025611 318025657
    0x10602010e0d0f0e121c030605030d05040b070b06030a0f2904170a0201240302091003050a170f0a0206060a0914060904140d05220e150609120303100803 67
    0xd0b1a860f01081254071b40240070003010240160807a0002280e4962000030f0312900304018589080c07001100301d000d022041006101542400c0d003a02c94031540b043c3c06810a82e11000400e042c6800789100405400f01c4c142041d08004060b094848000035840c2d80703071040159102111410001994041e01040c40d2030541c13840108014010021a0980d0001041c02014464811240c49480d544440743c0c0001c480c0031300840c5072691120350801c9001d8100b030b65050550321500c1d21000070b40760060030040a1010540344181183c152500b0780038465130701d9155415020042e44821084030418400c3c680e0b035101140e4040c0510403210a19181003060176595601001d000a00d20051b10650f400340007911a845282c1e02042041980301180d6201074564070701c0c01c2e1030982c0c401400d1540001c0d0184c0c04042c0f080943c6101c140d903008002c0c0110910705140b12000c035205104504105401130008003403641c00d010000025401280380b140f4000e100d940e5860115101e0041d0803d07a04c030340c01707182c42c486 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 318028111 1250 318026861 318026869
    0xf070807090b041806090e0d050304020a05090a0203060f03060702031611060304080c060c16020d230a02031002041202130e030a090602010b0907020d0507050c09010602010e0d0f0e 79
    0x6a0001850a00250303454681c9502d503000d40290380000080c2c0007019803c0c8100b1510301070040109480b02c024003c07110700140480d1250940b40d03041003046000b200123415985c5000310038001301303c040c01c00320050a0100b030a42c040d51048070f000340940c00c80301c201895401c000a18510843c182e901460620760410301d410303485c0740762050a480c0140400c40600541d65074000030341c000c600c28610103a841030700f1140242030040003003c00b1900b1009104074041201901c2d4401c0c0640d41c11503252100440d940f0300300503102e000040c0c0c0021514800c080d243d03080000074404002c607000301c040b250f070502c403405c02c6e0059120f20300801003c45418003081d401410032801c80c11001c0003145000c1030a003403d0368540c1c550b401c1101c400c000248030803000c2210a40a01c10014035440030796810300149000032020396500405000c070010002c00003011401c0c00418032600e00c0c6210300070000809942d58400c005d01a00101010200350b00441c6455207019006414203000c0240a0310f840300c0190400b4108 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 318029361 1250 318028111 318028127
    0x20709181e240b090a0209010f020601060f35091006030221031c0b011b0b1f0f08031803060403020a03120906150602010e15060d1a040c05090601080f07 67
    0x50342c40c0d0303864444030003481d0340300c42d1401d10440f452000103841e45004000180040480709102007590040801802031580c0048021104040c90400f044610041e80c0f070221500c003103002c41c1401d489050002c0001c000601c04060203004180100ea504030748010500c000c0f5401444001d40c042c0b1201c19003265081c0030382c0b035004007541c00410b503070529000b940004159142e00c4005a0320b0360383c07000b0f5944950381125a03a4000400b0501420100049035905803c440d0050302004210f03600120681e22139a80c040c23000007410f42c25202450550345e0b2074403a50340e600001722340089941d03c3c01146400d030500040c20b5126940550080c00c600e011a1000d03242030280080c11100f6540f507508850104840303015420803c2c4800032624442e42c54400c0090845070518601101c5411031820a000074441070300d61504210202c4101ca04604a850305d42e445c00ca0841200e5103110311170f4104028845007180907000c40c1e17400d81d03650281c4d41c0d4400045548400445400001c4141c03040850718845c0b0039404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 318030611 1250 318029361 318029423
    0x12060b0d1503240c050901020d030b06040b040807080c010e0901031b15050c0f0c032104080601060903050c01140301030803060d06050a150e01030f080a020709181e 72
    0x1c1c40c1100e403207440e070380c00000000d650504039480c1800078482000940c8105019283c0f50300d0100c1c00e02d580c060000f5250324100c2c80140405032a440200d4a130358801c4200c80c020034008448a40c3d45a0700d094841d215803003031003044054054008240e1845d4040c03940300c0701901b0000d1070380c011a821503a40a0124941341e12529102030703084804505c200d00340c1d0105d502c105440e2039a40c1c03a510700c8000c00b440d000d034252044a05070011b4080b0816628000751000c0c4801a51510840e0103400408021042c09241c4c440380c00ca2040400020b0440e070004550001e9038001c0058984407a403000064608112845e2040040b0b14104010400700b00e241c2e018580100700101020340303402c82070319824280c400c00c0da07804c1e410b0b90b964034084200109501c02d040003488150b902d681c8a40c5180c0f98010044940f8501418285000501d4803001e48240321601c0a407520000400403641020700341035214101c800701b110300501200b07184110307502350b480f581131507a4445484c0801d4a1460301518030308580c502c1c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 318031861 1250 318030611 318030641
    0x31419050907030c1a04050604093c24090b12030a08060603070c0c230405010b0d051801090b060103050c090a05040b01030b04050103060509060f070503042d1212060b0d 74
    0x800461f081c3c1d50360008100400103406c0c00310b0020b00060f440707012115140e0078800300103002c444000a24500030b94a201c5000017042c00140b00314409107200c0003d180040300c0700e100100300000b190700312341c075406600021425640c0115094a5402e540d96030b03c100425400801e280030001242071030400c0046600407401e2070002d5290800340c0c1e402c40d0940081c0c00c00707101400d94003804201d2801c09500820190700840d010300455140100560715440741c00f1007850042c2e100d10010742c000d0f5094034401e88914041000b0468002c042c28507088220095070302c03034006810100450300080304241650110880180b11045480c5030804100003070070b003541290f05041d12299a14440d94a500c9040c0c000c5010b544013003010301d40720010b00d080401c024200c24012409030300788940342c0c3c1e100c41030b01c0e0302035401001c10841c5448017405c0d0394102c0002c0d48000701c41c1149114001049040d410850303441103107844490312403c00d4820001a607a05020341d0b090b00714140070008580469030090603640328865 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 318033111 1250 318031861 318031867
    0xa0206011e090203180d0512010b0702040204030203100203071d1807110d020a05070f030512030c070609080d050601080c09012001060f0f12150c031419050907030c1a 73
    0x441c2c402642c1040700c130310010404808141000c0e070401c3c0490901c0b8902c0d0315015290110210841c555010107008802161202003404400c645540d4101d0703010b0350b0004d04494203d0107900208019510484440c1c00080e245a00010984407584002d03114400081c500c0b21034440e4403d4050140c0070040c20b01d01001070244040d17086c81c03014807482400c1c062913405041c5500322414441c3c0340448960000080c182e505204001180b00842d40000200c0b03030030f000b20780d02d44545000b01c1c424002d2042c0905005d1070304001c982004242002400d98000b069000c2c0720a954010054030002e10031180761641030010032004480c0e6100e410f048604411800705030024000e400086401c41e0400d400a44d2003032060302003445640d0f024101c3c9001420030303000080310009180e5235407102e000c040c0d0148450b151034014050702da0340650892100c14560641c540706a10707000c3d03014441429002014011300c3d10384000305141d20404515003060380c4d0003659a0300064a00705001801340b031141d0b1103411800f028 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 318034361 1250 318033111 318033119
    0xd0f0b060d05090a0818011403010602280c09020904050a0e0709090602040915030b0114010f050a1101052721210405011506030207050a02010503070917030a090b0a0206011e 76
    0x410240202c4480382446c00030003c00302c000502101c0b60041c08a4110800784010085070340d0000e101803c0002e0f4110182c130078090300301c07841d040c114032070b80050026130707120341c086100c03103903580a860414021030f03050003d41c43e001080001c44086901d2008140c200c0b030010701080c102500700f40c0d60948134680041c6070607555007408003200e4519540c3c0c0c4071410050004c1086c002d104039564054000c10000080c9c0450250010300980038041030101440b03008211101054001c40440d003441c0041d000902951811076114903440c1c1d444902640100592081c0d000003050005031300c410040e151845c2c0c0e1124003820030342d5010303800050743c41d9240d824030301440500c40b9500b420580a2845100081078610824281400d1003e030781e00b02e41c007014414080da201049001806e00c0805d0303020300785142e4035190984200d80c103008642044205900e0081c2c0d034070304440000000d09503010a50703101d03500582c40743ca00720414410342400000581c049401441050026820280c001918401007903240e41d40f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 318035611 1250 318034361 318034373
    0x2151306021206040b090906070c060906020c070f060906092d030302240609040228030c08120307170702100905031801080709030b0a090807080d0f0b060d05090a 71
    0xc00c0b1042c080c1500d80ba07041c80748a0030240122000b0400403901ca0155241034041c4a03622000117000b9810440b18907541c500b13024556000ca480c13550000da0a40d0b640e0700c1082d00c903540e00146d20032400b409404aa0004d40d59200381e20300b0055400302c1d6144030340e140c80c151883d2004041100070440c41c030594002c5802c494400014131008520a40180a40c05903104000d441c0d54080c00c1c01c0c060f40507102c41000446d90f1059030580e8025811608590704c02c0d403807645060f100c1e80522040c1d4010081913004024000c160b40c904044651046c112a0b10541150100400340401e590f6580070030004411000c100800c2c3c0c80480d4001311030720480d0207401c54100004103450920b0404c0d01e46420010380c085401c101861810351940081c00e09c0b240900380345c03900a0030107040d40b01c060590982d00d030220750803440c503810540d880c0b41c1100c4015182d0000f41004a141c0d4810f42210320424a820141c0d0008c0249001b0b6401d001c0300204200d00f0180c41d4a14000908401030200049000303403e004400255 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 318036861 1250 318035611 318035617
    0xd020a05030a0506220201080f0901090204061706010915051c0203010207060603050d1e111207080a1b150c1b0b150105030408030402100207080607020313050f010215130602 76
    0x8041d400404490405000341060000507417445101211078560740c0c00941d1708220b6454114609201c41078050341c3d20200303580104035400d4001d6106045c140c0c0054007421a11842c501001c08509803009a66145003030340455607803075494801c80b001c54408102500d41144083c0d032000c42c40010742c0720440e09500103800ca0340003010490303c0302c1d5680f000b8428450100610410341d0210b050800b0b0803d41d8100710924031191701c90b1101080303240a20042e00301000d11056000e842c0c00038060742c46205910b0000b80d140c1010400100054a282542a00e021010302024074203400030a096458024640a8005413401b5050801484000d4000030340203100c0d41c00c0c617052140116001d070312a090480341c0c0416034890151850400c201801408040b50b48901183e400c20390480e42c8110072061020207904100040d030100307081c1d01800080203c8642c0200003072005501c0c8030b00780031649444008002903600e00b9000540168001c1060300e03017800340300f10005d800224040c0d91804401c00d0f0341d1104280c0e4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 318038111 1250 318036861 318036863
    0x114120a1406070905030d09030206090a0b07060b03011407080103030c41033c071208012106050c0d0603210c021005071106040e0f10080c0d020a05030a 67
    0xa4000803c0107012035011040d4000380c07204501503d04089604030003445262a400060312503840040d004046a4400e01c036a002800c805103025180d61207410940020450b400000b8000c0d42000c816030a40c2600780d59840c4903a0041c1c071201c0e410b900316202103543c80c401000851780308a070314050100e180d02c0c8103031940440d10f852440f90480c03008486100140c00020307001e028035070b0080c45030b14030b4010000c000e10814094407141d54482500207841c90081000b41c034003e00c02d9000041e4400510400709000141d40040d5225a109643e8420442402c400c1b10b1810305049403580c44010000745aa400c0240c000c543c1e40c0750107082449030140d5108440803076104859012446025203002040009024031840c3d03a400d000c02c01000d01d401140e580608190700c10700304000020b84104220140c161803400304800781040ba203035a154652141c81a40588282c494400b103980025240880c1b04190300507034103c00040e15991002e0780174032020380c00d10b10040364059104d0b400415151400c1200d60300003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 318039361 1250 318038111 318038113
    0x20a11040b040e0f01060b03060310110d0203101401140a0c020409121805060906070b09031213050f0c0f01111c08070f050711060f120c0408150114120a14 68
    0x60400c020b03a070031102c11f644280c585501c24020042c2d81c2e50007180d01c0141c0c8490040114520061000d454214481c3d1000440c103548040180100501c003031810b502078611401d4005c1e8441000c10040d58542d022020344400e28070100903c000b420311402c1580382d042d1020740085034505650341c400302d6002c0f0742c0d02100009003c1c23031884400079000c0e0f0104070081070300f503942a103085e640d0000f1600c280314252001d4030100301500441e14043c010021208035481c10002140c445c1000c80c80003620160081d81542ca5104400c6203140450340816101e182280080c2100d98106072080150b80d07540703941209540e140105803503001100d50902003040c0f000c3e916501c209480c0703891480607100f005c2d50b22101080200c103202a10016a85002e030382d1080404880054a0392884541000305100d81614200c41d2003400741417200d00a440b81c0580265100101610410701c0111f4015503503407802d110303000000034152002607580c00d005d001ea5007210203001c140c0f1401c0c212038840c204040d58090303c40e029 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 318040611 1250 318039361 318039373
    0xe0a0602090310051b1e030c040e0718140f04020315041401030b04300801030203010b0103020f0412050312100f060908060a050c0405130914010507020a11040b040e 72
    0x7403400f88031119010322030910400c06170820303400d08000c40366803c1099840240006500d0003000943c40c04042d4003507001c0285980c2c1c40c140d03211755a00c0c1c100e40704181c0100d9900d408a050315000da4042a4030301c2007c20101c0280389005c00d00c880c0c0004d2510b0040c1c1101611070480e00a072281e0000318032610604000040f2000b962b814401101c0c10141c025550040c0200140002012072610542181c1c00402d07081011042c0d00081608601c40505051100602c4c03200e000780703a800028080c103da008034000c00c4100d4040c0d00550607489907280f6030182207010403050080c03501460700103001902600c2281d0610040c0403003a400300c0005c0c0c031284d096030500ca41c100540c201c40d500d0000030700360b28a4038280b040d203091001da50b220b0024240c1d51702d203522040003e03421155a803c0d54000c3c01d00800248031811040012801040c2817001510361001b00f210041c041c207014015a402203442e07500500714510951a03e0329410604402544c0c416201c1e201003161303030740303a008444080c81d2030406480c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 318041861 1250 318040611 318040627
    0xa09020a050c0c0105120f06030c06071209080616031e02040305100e12030f0411100905091005010c08030a02090402040e22030e060904020d050c0a0908070b0304030c060e0a0602 78
    0x3140c40601801d26040040c2009114034041b081e58816800004910303c100c0329841c0c007070000c0d060481d040c1580d500002c1c085003500c01e110000120002101c1c1e66151158256105c010840c1c40714000c035212140c42603074440704a002c51082e800003080c0d41c010040f40107140703143c04072107007a60302c113600581c0d42e54004022809422030904c00c1c014443c404800030000c240d25100d284106000c02072007402c0e144c0e54000001d060103410410380100050040003440c0040f8017400140c2030f14000e0241c0d034000d441c0a00001c44c0381d00013448920942e10705844080418045560303402d02e40e44010300b41803241c4c2d001d0112450f00d40b15400944090004203514003460b2419980e4461914050150400701e06a25451a8040ba82180c0801181e00e000d0b0354190360b40e1100800f08000c2d00c540c00034043c207039140c88208501034020201038078542e001907450a69880e900e803c1c01380e68403484d004111114034104007050020b40260303078590166102c0c402c04a420400c100301a070500700300c448203444103500050082 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 318043111 1250 318041861 318041863
    0xc01060503010e0c011b0c180e060901050a1a060711130c08010515030f01090c0314090c010e060309100b0a0b0a2f060c0306010903122f0a0f020a09020a050c 69
    0x210160308100d1ba5107880074010b440303458036a0818819404c0c0c0101c10b910801c460480c030b4112403060016441240e10074103281c80d01500a18080341c80c074401c0c42c501260051a512403260300030010310018100ca04120240d05c61400c03604400c441c3c175034060100507103009814118000c40155240d20b888960041d80b4050621201c19440b03107a00c00740312070800402004014005581e810350b2010352000651241c1d200061b001880540c00c084074503544001042000d0600142900c10b029080c0d072000f10070500603051040c1404160b403040da01d43c214940800325000790758000f11200c640241403038036065440703020988582c020003011000424a0319a008400311103403d94030780146102c054454441440b08660f260740380540900c4180b0000004110668070038043d0001440e006282e00c18411100350007c1d041103130190f41444420501c0401500a18110400c0e028524125025150790f2000d96141c241e000406c40e022070b40719150a00120b40a185440540604802c07030700c41c25a00c1d00d00c1c1d8001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 318044361 1250 318043111 318043127
    0x607020a0c0621050402041104030f061d0303010e040503070812090f07050a030f0c05180403080601170c0a0c081305040f1b11010e060c071b030809060c01060503010e0c01 75
    0x2401c18405407079103c0071440c82e1101800703282c2043c144000f0300b40e11580300003005410749200d10441058003041c0401400b5050814448440c03040200f0001c1344140c0444010700030300a801406240c2041c80108071b001400b00c90182d100d803080c801c2e20f1030300040d5602c0c144103810034501c1d500c610040304c00b00715001508100301c02c002220b001c000c000312440c00000030440b440500000704245500c419200401c4031202081c009420005c110300600c552880e84901622403c49043d00012080700c04039030303194003415001c0703e44000c0e500d514080d40e442502d03001107984017821090070465a4600d01d030100340503501821005810700710420240c1c4c5418204010750300140c04081034a45080382c0c0e9524940341e5807080800c1400b03418045440407100111074010301400c1d8076a00540100000c0042c0c41a041000346542481100300d030702c02da0144540010b03000c003a0300000744010000c0041c00301074603000000e0000e284c000c10003c14020788960200c0d0070350316030007403491032544400000000d0390380080b06 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 318045611 1250 318044361 318044369
    0xa0e0604150b060c1e12090315060f0a0602010c2d0309170d050402011b11190f380f0904020702060a090e0109020403020f041d0607020a0c 61
    0x20411420030391201649804001c0019003030301e076030b841c244180d42c44940a0320244a101420355240b41440c0406162140103084010314034082c0051016000d580d40040e2083d00314090b004043c0a1400100f410b01240f0207072071540c0c041d00d03181d64244a41d58021040001d44410750003c247ea030248200985000b507440c00050109120089a200164082110580000403441c010601040360b00f0040040410003800e280151000600c07030000c022540c0000e400ba0303100b81c0c2c03585400c003070b540e0a44000503181c0200400617903066442640c0b6290100c050202080786110340d20859036034030307406c4c504201546e120f80d00e420a6602c014141c0010079140c0b40300c0c8032080b50910307010b0f40301d58802d0501e4400c0c48010b80440f500441d05250300c0e1a182c0c140c0300c289a014010a0b5030300c1003450098807081840c810490644240b000104503513a6600983d000c43c0c0d4003901c108001070896040101403340100900107041d070103070b1134203507594080080b24003920094002e0516080c2506099003075840c6a00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 318046861 1250 318045611 318045613
    0x504050f0105011d060d17040e06130c1b140d0c050d08040507270e0c040b03010e071403010b040c050a0f020118060509120315030c03060c0712050c060a050a0e 70
    0x1242d0810718443d0030405e80c072880c100c17079038a1300c1020361916142d0740410582503c01480d01045c007155042002094070301030041191b0310946013900e0b5541900b07444c2d0a0f081c240000e0f01c10700401c08800b5030b86400d500c0c0d4601c20078032244240302e25a9494682116041c0950000d40080c40140500c5814400c4205520312807500001c2c0385003076121607985050902c0780e8400402d08003a8412030000100940551a140c501d00348040c40701c03140f00381c1e990404d0f0000540700364501a00703141d080c501445113440d00c1d00d5810240c0407441c6040c88540080d07a5200e8102e8055480306101c0d0000d90f6a032061040603807003600c490307441c1c8001038002401c1510b03c1290800b513a1510560004028110703440c01c107040d074040c9006c65560b50b0881501c3c00c01c4840c1c40b03605003252000c01441140c40c017600e5001c04400c41a4111007203042514101903480c5420f666920894034108402004240e42c0d201e42003140c801801c1052500c60189001ca02d400b00c12035095540da48d50b4820b210407036030f0b14080c0f4044950048 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 318048111 1250 318046861 318046889
    0x1d100e0a0f03020a060f0c120804120c0b06130b0603070522050303070f020d0209010e09010f050112030c170403031d010203072117090120030c0a0f050d0504050f010501 74
    0xd0b01060130070501d03014000c18404c0303420170303a41a03d21031050b07100b1555001154040e4500f0843e40600381900540e4111650000380012103181c52103240c0450703d1540081141c0d5054480c0f0040c08100076582c060b40001541b180380d641038544680c0d0003980181900d984e495560b0245400c0000c0450401a0990740724561403000c020a65000095800c025001240100748141601c00200340c01e914072802508420580300000d0706001d0b04078040d1040c40030600911490202c0341c440c400302c1d0801d0042541039001880c0000110384907181981c0e8491054101002d15900d2092017415600f01d9801100003c40140c08200300c034021158117403c02c40c0c00c1c00158108880d964455912042c041ca0281d40170303081100b40d8521611856181c07c00c0403080e24280c241c0d080086803c0c0c06403c06501400203030140c0c3c410826112030440c210303031143e214580c2c901c0c00c0c04030813003040740d00304480700c0c5c440204a001c1c00a9680020766124690055100d840140041d900c2100d480d0309490050740800c0c072181d002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 318049361 1250 318048111 318048113
    0x60126030f0f07020355061d16050105190c02031c02010921090e070909020a030e0f1603060b061204030c0506060d0309061d100e0a0f03 60
    0x8156000e84081601d03858881c62514071004003070080d100065414443c8400260780440920b410700c203091051082042e550341080203c032041081031002c0c0000e42c0b030008900020a0400f001040200d03c1a607004c140c441607404018104110108041800d030409416041421b81d03803c1048003c1c0b8080c02d015042c2100c4100a0500c030018541035001e1104072490300d011590140243c060807103501c00c801c1c80040300001d00034000d1004e050b0444a22580d44046030880e44550352100011000750f450f0007649041001c007801700003002c0d0240303042c00501e45010a0506690025005031015540c0000d1900030b100c014a04d02880761200103403d8104020300c08000b18640e00090507240c0020001c115840c040000c81c01d50f200b06183c04145a80c3d00f400d02c02017580c0700100f50740d094011b5045a07059150142041035580b80d801d40103001c203504035010041c96001d0801d241600305c010005003030040c14180800c80ca80d400c4004c002c009403050a05030464980a1000c8010300002041d0000c1d150035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 318050611 1250 318049361 318049363
    0xe0114030105060307020c04020c1b041a01051308070321090b0d02091f080f0f09060a0507021c0504060201061e12050a0c03080703080c03072304080f060126 69
    0x10b000d0a40603100c0000025211402005641814000039104550301e03421549016100c008055045d650110800c50040c2d0300e00d030a01420320102c05151020324803245000c019590759000b6100000a408503034400942d034102448180000c41c05038030b03010041c855040c04001c103401020340450070b000001100b07110720b0946606440da942120480160b60b5030b0608000f88080103a0a13004007101201d001080c0c0803648001e01d640542c108199824050f103a4110140c0030b44400c848500c1d00303600031000034030000c2030b5410290304020140162074081014903000c0300d000d24142110408190005000c00a95509100e4500100550901c0c0030080d1040450103404070041d10544106c0c0481d0410102808014080440f506501800a002e20759803894900c981e41c001c8101900441d20150000300150001c1003128494050756840000310a0101c00300710070802007488202c0e00703800510011030350413002c010948801c4105002000b00d0340c50b18100c5010350b503500c6000e02000064409413200060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 318051861 1250 318050611 318050617
    0x4031106070b0105120109060e0708010c020a050d0e131b27033009090c051c0f060503030703091a0415050a020a060204120507060504122402070b01060e0114 69
    0xb2044842c10075210303a808035903002d441c17600d87c0500010301d03110214100100c0092447c08450311480203002401d80140c0a984600800402400640107515800c5810303108400c0c404001c0001000301d0324100e00b15000e8011108420611100c251840201c0021141c021030395000e081181e9051104040d00c603a00b1031004100f521004150040500303000b4446002d250854003000201010103003000c4441d00c0082c04cc00171403165410312481d0801a141640c1304170101c801450b00844d1100501402c140c1e00001040f00010b505142503072050003044655081c80180207e500030341c3c42050751b070b0802c058000c02008110480c2c580c0c1d0300070002007055202484072001c54040e0340c01c1854480b9180a0180e0415500072002000288000341c0454180c0700040392405031402101150031041e03d0f1103055406101754003503891410200c0f2110342c0001d00003e9141000304d017511600c003040f1003500508050303801c90102107540e040301a0040c4201640403c50320031441c000d1825080d9503880f108006c003684 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 318053111 1250 318051861 318051869
    0x315040e030f0a03091e150c1404050d02030115061101050903040302010e100306081006030506060f0f0d110a0803070b0a05100e040201180603020301150c0c09022101030804031106070b01 82
    0x5500c5141c801700380a2050b008412904110409104140f0a031800c1010040315103501420305181045841101b0321629840382007003507507400d56140c43c0c02c1c00c0801005c55030a01c0126031564170345a00344041e00d02e240941c80101480e0b2607030720603005c050710501d0030348000401990841e40280002c10140c2ea020541d900040c1050358044400b103a01c14044010380f0082e0010100c074800d001031050142c006602c01c2046174020320a5803942d8944108000b181071018541e6907100b901d000f003190f080c4ca00b5005401100d031080210f0302000c0f18010224201c0146c40e800030847e07800100e20b84050180b40002c01e540b0a0004c4001c200d00d00d030150080f6007042c501e028074848500031030000703011079000708905c00c00820281d4604200c1b503503d4500030060341c003d0280281c0c040c00b0201c0b0030000740c00380c41c0c110300b120342c070080060311242070481c00700c000d402291101140e103019406181148200100c1207000c0c1d401155030715580c50650502901500c02c500a09005072410800e050202c1e801309150b40c159 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 318054361 1250 318053111 318053117
    0x306041d250312050711221104240e0a1a0a05041e051009030201050d0e070f0e010e01050f0f040906020903011505090702120d020a050f0315040e030f0a 67
    0x3001c55801000580d100d40004003901032850340f8140322504075005c0d0200c00c0c07040c10f0031070245c101281405200e4100300c08a9006e0304072200d040d020204a81c001400f80f41c80b103504141855910354245460b40120740d151910359884500c480c55040d44400c901a02c002c0964144e06c0961420503c00c806104004100d0b401440c00f1a101365114400c030211001800c41845803150b580d29150703070804091070351140501c90b61813840e100070194055200c00b0100c94050b1940703810300030341441c0c01025200203185510a4001d21501060002440c00d4003005010000c0e5411003a41c1425030310040c010043e08100d1051254940c20750041d40d07002c0c0014a000d4060300e0103d040001458800c004e0700500340c08035819400c02000d02d40d003520718140c0008869084490a5840d16000c105076100c5403004402d11700c2160030007502c004a1725a40041076584040d00d022441d043c001502c00403a41c00544400c0c074245180b0441030224505409510420048480075601e0a0f907000d04600c407602c48d0324490001c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 318055611 1250 318054361 318054403
    0x1030506090d0c1410060b09031606020a03080627040507090b0604150246050a17120a020c0d0f05030121050105040308070f0305060901060509040e0d02030306041d 72
    0x1071100b05001d46070085c04407200600600381ca42451032001e802002c1494028800c0400c1c49130103034a8003d03c21b08844043d00941213062150701c08035004080200416044501c00b03619a0700c03411000844040841c5400c60049142005d141460620b40241d00808060381040300003000d030703903501048408a41944914400092130048103a0910000d202c1000000810011110015481c0c0354151a026560a049000403041070820400000c0b424030280c1154018400040003454200d00c0a4004440500c100d0800303a42410826803001d04031084540150041381003e40c03003070100300e0786022811504100c10509001c010040c454041440b400c0003c075200380100b124074081149001c081070b00700009001914150402500009098030076100140c0c4a0302e000c0342c128424801c5601031a0018034060700703a4a411412120380d002100c040c0d83c4595100c4140140c14401c0191903051107484d0091a1246814810001110601503032a50a16500c000046e810000803c644201d00700c003d0071600 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 318056861 1250 318055611 318055643
    0x206031306140408090f03060f0f09031b0115050303120a1508010f0b03120f070f02010e04090c05090601090e0a050705090a0303090e0c12040605042901030506090d0c 73
    0x201910340440014035002d040020300c01403001c0e5a0003006020070564a20300108075940505543c1c01e41202e00301ca02001817408039032004100c00d81c86421407010002c903400d020583c081c0d0316081703848000705060b40e07550b92451810248484d600e50020311017100a1030900321041170101d45500300810148040d80d07204000c880805d40980c941d8050102d0750020044500b6a8513020000e0280e40700035441380c41118095000040b0b40011140c2c0b80711013140c65030509803503542e0030160ba03a03041000c038140100b9100c00744d0b1b540c40714892045418041c3c020b605d0070501d86414400e407010081c103010b0400c40f603001e0a00102a40001d5541c00c4100384074005816616500100c0c0d541c060f2240d642d910440710800002072651090200082d984400d0040096072205054608503101c0d1445000410401400017004208075500803640b050041d484043c02a4484030300a80414840d801c200b1150107060040c828018104812a4001300701c10003030603000844c200c05003060007440b07401443c0d0f98240040300703 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 318058111 1250 318056861 318056873
    0xd020d0303330909050a1205040302041407120e250305010606050a1b030c120e04020c100e060403020604080d090618050d0e0906130905240702010902060313 69
    0x42d0114540b00c03088002d0a00c09180e40d4075032010410a101c07901d5a0400200c1c90881500c265000305034014020f2140b8200713030b640c11954500c00310307414003440130074840003000d61280d000350084031541060512051410b0031010f000c035030f141d080c1003000c14a01540801d0710400002c102c20070f010040107011001001104003510141160402030180d420440001401c0e60024041c00d001c02c2e1f0790303c41c0452000c20350303818601c00c0301a00000d4006810664100d0100c0c1650b880303801100c07401c0c58180b10103004003010a0999002180199082d03118000d8000341e000540301d80140d103003010001c2d00140c146038078001c1d41c4000140000e04010070005448081c0300181d4842801c2c681d01141c00d00400c8440031044e562500b0890301030b036040c042c031404000541c2c070500043c3c5034910002e04208981d29080c040c00440d0301c641070030303102040ea45c0f500b100105e0300803c031007850303034080b0851002940030408802c42c440300007a0028095a04000a000050342c4001c10750342d100301e60446002c00700c1c620781454 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 318059361 1250 318058111 318058121
    0xf120606080c070c0909050303010f0b0705031215031c0201240b030c1c1b020f0601090e0f060103050714030f070303210e060a11040b04050f12030a050c0d050301050d020d0303 77
    0x805e010351810801904001022002e1412030301e030384101c00c6180d030342d96810b6980e40c801d240008151f90000c0010345840b50780000c600d60804000742c0b00030720b40e0b0400008203241505080c0590094030a9249184040d83c2c24040c044a1400e28044030351481640d010709a400419406014100407000c0001071680c00c1c604160b4407a0480c4040310420760b0307070125a40c4010804070452400341e96800c10ad01c02a10300020380078a085001c60010101686043c120b800100080c4062440174042d5070100310b0040420000c0c5406180108050500c2c5441c00945100d1014119900c5000b9007140003c01764019011941e001243d8160601070f8044030310509510400c0800c401e0f016a042c0303804407000c0315450000341c1a100c0c1072060401c106a14400b0040c001e01d02031032042c2100d02408001c01c1c1701c182840442c0020303c0308080c280d585464003803c1030505607048130b80ea00001030b40110381c42e16000410040d40c00000413a080c0a0b26550414011030b5644022090203802940030b40d252108152080d882 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 318060611 1250 318059361 318059369
    0x21002120f030105030705040207120e0f06070317100b04060e010309020d030c0611130303111c0c15020403020d0602030402030f060a091a070c030c170a0f120606080c070c 75
    0x30007035032621401c000d400036401c2030088a00074419108041694202072086400007500120801d41c0f816003070408070f50440100074126005600044100180d031140405007800d01d1080e16180c0c0f802401c04019850500003e01198000782c400400300000034000044406490003440c00c244e5810310100141c000d0003c840000350481800030b00c01c814141d20140840040e07102e401c042c04104988484403042d07000e10320140080c160b9503c420000640074008611504010a01743d400c40c0b041400081207610115021401040d80e8210400400a16855080012a500504508003400c54010580424414800070011580040440c0540d0343c02c11001130728100d008105d55842c41d202c5240d10290900c541d049130386c04244009031071a4030509400c2446440a42e41d200c80e07a10054a0440d8101c20446003a200a0303030b0b0300340128407040408010005101c07103413100004038280b411b0040421802c180c3d496205490300c4010b00c216544000055000140031400c0f42d1207403083e0500240703042450384 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 318061861 1250 318060611 318060643
    0x606030f18010204150f0201050709050916120c08061525060f1b030605030a110405180a030f08150f0609040608060a0b0f010c0816030c02091807061407021002 70
    0x10310072610507800f50403096006c038242d000303104d10344036000159500716031070041550162100002400c10148404420b05440091404260140c4d01342180350427a201820282e0000c0d694404004082c00d0002c2d0090031080c400074410f241c1200007091110780d211404082c00881c08520820050112a40107080180380c8000204207600403401d00d00b5131002121038010100b401c1ca00c2c00105490089110441c41e504170700c030101040d04000820009080040030a0341a4801d1103104d2064031040210a030300300d200341c0729000c051486003801703000040c00600c0b421840b9502011005d4507103c4014030700d201e40003a11b1880d203980e4503070005405015150042c41e624071510081009016064100114045d0142d54404001c40f51400443d0303580000900a400c02c2010448a4052081e1145260809001e45001d40d850001980015241101590414141600c0800480480760280070400040900742003a66042502050020351409803001c041c0c811b9020440180c1c11500030b22010f40c1c41d0031219 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 318063111 1250 318061861 318061889
    0xe031306020f0d030b01110d08070305092e060b0a05030108010b060403050a0b1008010e01051801020406080f060a09020a021b190b1c020301030f0c0509010b03150f031e060606030f18010204 83
    0x140001c9c1000e00440700100080d0070701000c100d00280c0440c2d01d4400000401a0000901c030302d0391210028a0907a18140d0941c2d6503010000e8298146006080003490654942e9641e52525820501352007200120502c50401000100005035001803020700d02c2d5440012901e1503990080014000360303599114011a5092007001c40c4c27041c0c03044d80414441d129050358180d000d1001c8180c40c0c00c0b030046008100105000d000880c0450004012aaa02240042401e1807090300c851100b816600401148805603002400700d80c0c0c00207003099503401400090b2400700007000c1c001000c1e010901c507440b458420000c001001210030300050400f640e041310702d10003550349594a00d00308440c0c0c0240103003555048040240494945405c140e82d60484070f0300302c0c2107825602d0344d070300c01070b091110041c0107a4800207542070710310191424464a06d034040e03c0050001ca0544d06d01041e030134080000d140310b204400070001c10000d400c08510f29034000c018400e6401c2c0003010540c41c81d0080c820754220401c0700681d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 318064361 1250 318063111 318063133
    0x50f010e07080102250501021e0a080a090203030d1109100905130506100f1e030b031b03030d0203130b041b05010305070c240e031306020f0d030b0111 66
    0x150400c0ca031010024045034003050352580c14500300d001d400f0880c140651141010a52a503050401c0f80c0c020340190700051502000c0c041713098aa0440d124004072441000c505a075400d5008500c3c1d55000c81010b1084c080860035130300203030700c0b8811080d001102d10f9450400040342d44080e4152404004080c0803030001d02401e02002e001d40000c0d02c6603034461a515484803903420307400d0007428002c6202404ea000d103034142c0c0e82c0c20340b822042954101c0c2008400034410740c06024a1082e80f5107490300f603e00040e01b612002c107040c18160000d070700c05003000000030003c1e81900d0002c00c0310b0351050008001600c1c1e4541741e16541d44141341c150041d0804130040d0600081c05442c695146c9100b840819a80034a43d031840154280d84048464001054880d01c60070080303003080592080d450b12104400085014040050003184c04188030818a41d001081030342c0b030880c4404618020300041d00060040e0000303040003d554100d0180c040c0101510340d00b00e90b005900400302001c0d400581c0301a1000c0c0350070703 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 318065611 1250 318064361 318064363
    0xc030813081b190b060d0201051c0b01090b070206090d021f08061306050102030d15090e0c0a0504110d091a0c030405010c09051003020f09041103010f050a0e061c050f 73
    0x507002038076a5500910708010301801e09400d04400856100e2040076060b030712042005a84051b4a005a041c04010000c1701c401004242c984580140076841c0010f0b41c9040b000010103940640d0411010030008000304405a5500c600f5a200d44a0031900007900c0c08007840843c101240c00300c00c2189903260080c03040c0341c0c15000480076118182c15030301340c540070620708a40d2043c0c1d9014410740740584c004008503001d0030103d41180340c1418980001d0f0345020754503240c0c40121000d4144420700354000000c41e802c180f81100310303e0b000b03100460b02404038500c140700701d0350345205507880603035202c0c0c2d117010f080300300402c0344d010b1400f03502c02016842151a044c5d00740c40c840c2d801242e0442c0c1075440c00303500012060250312040309880c0081d0401c0005004410306a0084d0302902842100180038020039440355194000c411101c0c00303038400d40303031254900101100c9120b503130741040e44108483c1000340b0100801042c0740f40e00010880d20290010b881800000e107100c050b100280c16802000600114008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 318066861 1250 318065611 318065647
    0x509090c0d05070608160c080a02010902030609070302040e07061b03020a0221010f0501080c10090f26060c0d0f09020d061505040212040b0601051210061d010c03081308 74
    0x1300e2a140ea00140e43c6542e00480c0e5143d070760700c00d0404141d1a4400b14042840030000c3d0860011500002500d00b8240d0006480c1580440b44c0280607400000c080c005c42c1040d01039004452081001401554201100a1b00010b00650300050b140c03980d8214106140c42003044000040d000341407100440b550040c0726880c41e07659841c5102c25820500e01001450080c8502070484204502400507510700c1b00801c141a540c4070030100c10001003c0d00403c2521003551400000c0141d4220009800301031320a440f40c650301d90400b0940e94008400300808a559a011541d0240728100000f49111440c2d00d00d00c000d03c2c603000b029410403400d017400e80401056500c40340003500c3c1507003440e400d82e039110108000d0348907841d4881c0401c402000490700081d05461066000181414040e082441e003d908510940e130840d00d944183c1c1c00088200000e0760400400f00e056260170a000729042e03050400a84410312902c401000c0108107c0000d0780c54200702000c245040c3c2c455401ea90b1202241c1c80c6620280b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 318068111 1250 318066861 318066869
    0x2040b1e0901080126031204050105071b0b1009020a0f0e030106050d08070602090909032a0a11010302040b0a030f050f0603070603020906090a15080f010f0509090c0d0507 75
    0x40e16400484410000030020707100e032490141d452032641d07800c0c480c1c00d40d400390840b8010040200a15040074585206102401c040c009007410301d101880d00e81021800d441b005032000d0b00f80600615480c032800d90f000040002150040c1001d107050721000025a00c0c00b030542e1124000038404030b940b04d1850b80c0109440300e030601c03561720368080341c2804e0101401c07510b90340b29640d0b020b2540c889100c0003600785000352071040d008100c0181019004000301c1d00c542c1c0200c030f07401d0194200040c0ea145440840400c00a001d03442c0c00f02e42c02c600080104160703900030482000d0200d0301e10b288500c1ca20f80c480e8048801610b1510300c0c6039116014040c0250113000d0310b4801c3c40c0344a09100004125250318040288114402402400007070f280440c103500075440701c8080c0c1e40258041086039919100c40002400508418180038019000300000405450b000b80103800941480c0c1d0040041c10168500c20040c3d81d0304940032600c0d80c0703d44401519054641c108150000040d201800c107104021a0a000b02c07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 318069361 1250 318068111 318068137
    0xb01051b0a12020c030706030902040902030a0b041a07270b0d0f0f090c120c03021507020907021605100507060c030c180305060109020f090901080c030f030306031507050d02040b 78
    0x3411440b0040c0d89424255200580540c08540c007000f20390301c42c5d001064242c0c000380002801042a4021900b440d49100d002e540c1116058244002c00c03a00d142d04a4080c1c10400203030455090517035004040c2c51034400c24461003d021804031442c0c001c41d1075030b80d000342a2941c04580e249039504010300903151401c0540c101c04e16100a09648501d030307010301d0740c205038002c00348154103080860322041c0408603042580c82440840000c030042c0c50310b10085d9000703a03020010701d403204d0703c510410070254030050180045400c0006d410440c0220242c0c004248e44c1c04458241440301c1c001c1086646004150002d8109820300300d161518503015840011007008540d075034585500b030300050034690780311171100410741d030310a070010498410f45501800c1100d8214655500e4100303840000b4089503020313085200300d07030002d0034020910b1804020109240071100302031403c1d441c2950000740c403010044e00c810000021000080c9800c0d100314100d503007050f8000c0045444580780e20500115400049007031100d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 318070611 1250 318069361 318069383
    0x1401140406090510060c0c090e0703020f060a0c02060a020111160209060d031409130f050703050711152e1404050415090507170102180607050601090b01051b0a 70
    0x42c8400e14050280f0944030216940b90f0300e0303d0507000700c425000d01581a10030404803440840c0d294254000c0c02c504810400040c0081400e42c01008005d11840200d28414181080880c50444c2c05c140180e92894040350803a80b28507250406a0242021904034820158002000d0340c4420740600c00c0f000c0e2500986005169507210000c0c041c42c51550702018010854201d90401d00c004084001d050f03a00000e007000a81201699014059600c043d0b141915941c0300c0d820009056413502c04c1356400310716031400c49501781d9500603d68403885142c3c41c4080108600740000c003101969002e02000c4808041d071034081540303051000b10210b01c030380a0762401c15210981c0000f80d141500565000e03d8008c80c101d107032081d001c03c04100402070294200e0740b5008407000010b00b900d10f55090782c0100303100c00c00940c3d1400041084940301c2528502c803482801c0034455503021580c0010440d0540f00e000c0710004100101c02e0040c0c4003809100043e04c900b0501062014000e6030100b16104050322036003040c60 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 318071861 1250 318070611 318070619
    0x911190f08010509060a0906060b0d1a011e03024602060705031501020f100b04180812180d0903030e0907021c110601060207060212030c03041103011401140406 70
    0x42a03c105446528282e8080e030041124619280d200d00015407043c00005000c03507a407a503121258000390740300c44909680b0048005200d00140f5842454417007482c01b000c0781c018580f0113800c41c0d02d0b07550440341010342c080307030b03a041c0030440080c001c107400b040d601c0d54a01d242e4a1028800c280401c5084207550f8140b80315444030050000070a98025009a180c05055560f040000c244a0281120460451248069a00b071483e0180320482540c42c001c44003140e00e00c40741052105488074181510164081040c0300e802151240040c0c0f0038000c4140107075081034845844808054209207a14138007070140603600c3c1c803010b802c2500c16003224444d4070b81d24060890f04080100d090350455841000d60404407585105d03500d00a4040b003109042c1c2414610010030002041c60020260001400f41c2e00a002c103101c00740d01000340110704a200d4102528519218a850506002c0504010210300c4050304180e407e540039004001c010fa4008003d242c2503a5550041d07000525254005010f1031401d0001700f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 318073111 1250 318071861 318071863
    0x405030f0307150e01021608041712041703190305040605010902130302010806030a06020304110a0f06140304060f2c070305060402090601030e07030f03030609020a120911190f08 78
    0xa40e420b6005400c0200200d03950b04448050319201e12104140d5500700108007c40402c0d403030342c1c100381d400b440c1d1040d252414282c3c001d880d03a446142100565100d55070041010381040f00f194103542901800700c80da0241200300d140b45001e0780309000c13420441e800f00c0c44482c642c164032051090303000b02d10912a6984c0c03031510300105d208a02e11515034038204801400036502461350b0a8110300044d0441e8240125501e50808a07041950119100c5c40942e02c5070031245440000013001c0c1542c2d000311608a4031b0200041c000c4046045034002048001c030000d010700c000c65001e50603240d00908240840c1c440c00a20030301441c1512011003500d144645d8031854010b000a100f401c0e240d2040013401e02e51915020442d14110040c403450400d0740300c5541c1c0e006a00b09211400040d0b10414842030400c41c98500941035449541000001c0c510520008406a910500d501c096146050000822003c0ca0409203811503010003500d40004404841042003042d2040c010200c40c180c00d49800c400b9198400a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 318074361 1250 318073111 318073117
    0x10804030509012a080903070806091009051f0b0a150e09060d121706031c05090109090c0c11040606050702060f1204060b0906040b0a0909260405030f03 67
    0x14000075014041ca6840d94000e090512035a00000d07210070401100c03030007442c00102034503011924000c2c0030138000e915007801c1000c3ca020b40009005408940786c440c0d8101d607120305620004501380e40f2044600b040c40001c0c0415025103d042040b01c03003000c41c4410210180001c11a407038014000c42c040007480c224201c0d50701c02040c07210ba44034807880103000b007005012603002d00b085500c00b5551405034000750818852824408042c8c65601c42c43c0d001104240d0320100082c6030354001d030821480c4292421405081d964441131904042d510303070840c1c0c00129a08656500101842464100f4480c60f544c2c01a0b100801c0d0b03480b5200c030380300c030010000c1400191020740c070230792000c10024468031005203030a90240100d00b0804074058188114668140c554010940d8260340c603640c0c5009100050030452a115440041a14240000b42116000c074180140c1c1d0712401490658800b285410441c25065500300b082043e0400c4241c080c4050f00c0303250a61192054a03c02c6c0b1039048a009250804400c1d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 318075611 1250 318074361 318074363
    0xe0703080f0307050f030a02091903082704020a0206010f0b1602130213030b061c170a02031c050a05130c03200301050c0a03060608010b040501120b0907110c12060a0e010e030a0804050705010804 85
    0x2450781000c09444de00c484d07199110110b10107080080c901d00b80540c442c0c0c0b028044400680c4e0003007500c1d502d060700703c1081c10525080b1403a002010040c2c44410382000e82040300c503c0c0d06507100d0b54260407420b05000207000308100c11812184008000041c42600b100050244034100c0300c44450342c1d200c03a10984e042c5c0c100c1100400302c6120800c0ba028400307a040143c2000b03906401503038a460381000200040c5103074000c03c04601c1e56100103021002099129007980070300c0d910000c0c102d695090720303480300340781251000074085d407004014108078424203000d001c080d030005002403049007000c04143c801a0089401e202c00a85003100000b1014800c0170898122815034040b50b00e040c0c240401192410740000c0319042c41b6031a8501164140c40700d84565101c1e00c9140d4582c40280d1100c0c407402c4c100100c03600d041e031244100503062659840081100c45c2c014108600c00245030500a00c0540540200c1010301c09a0001050020206800c140150b225a20401c1074680a503141ca0040d01e1091017070390 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 318076861 1250 318075611 318075623
    0x103120c0201270f09050a05061c02091b04090b1305010510050c011d030c012a03051806070f1b031e03110a030c030e0703080f0307050f030a02091903 66
    0x660300d1000300902a000e80c1da000c2c82080943d140c4075110403000c91607941c0014a0340e982c410030403144001d02d02c6140d0b04410116842c03513840061030011528078082c100c010b07200d000f44202040110440340d81c0c00310540c0800145503110390369841200b000b4002d1101e414064461290000c0c1d07891210710555060380c1000b01030400c0ca040d40707002250240c22010b00d9079515941e555400b80d50540241004944000300d80003140d40d0080c80d10824207507804001001c03070808801580912801c54a00020482a4113144c0087c1c156240420001c1c540441c980d02d4809010b0441400040c82d40180c0c00303503542a541d00d4030140302a403a0103030200c02d01c2105002d00040d94105070cc00f001040548040d0007000c0518010621007151074101100b42c0c005040000481c2ea100800500c040c1c041c011010706031002c10141c2203061450705d4004462044502e0000310741070020009403464011020303901d000135488422500c0385441e0f043c40001b03500140070030f44101c40041c0740c4113400840030002803e4941c000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 318078111 1250 318076861 318076877
    0x62a090302030714150d021314030d02010c0813020d06090303200f1206030c12100e0708070501030e150411120c130203071b0c0f060906090b03060d14060103120c0201 73
    0x30030900001e80000012070031a40e002c0018044a12307640107034030f015201d10402403412230000c9041501e090358801241c001c2d0b904080420b0080c80d04200c2140d4418021105130905001510008551080030030300101068a0084810f06055150340007054600c1914160034080c0d110030712840b9580a2003115001603d030400c80c4908916070418000d41148000e4221440f201500c00000c8404942d15460b450a42c82f50300d2b0068001440d0080c900c0c1918408040c2062a003040c01c01604d50445024603030516480340c0940c650640c00300242070b601a01e0f003048900c0ea04040c07501e4203d04030a6816a845150100e6808a44c142c0110701c004462030000d1030248030307d0001d8200b4000c1e42008200500b84030301c0503101a00921a016114501c80c4500743c841440c1e800c00e00006e074005c00c1c0740c0184080140c0408244911500101c1c0710090f10010794055072a030b914000000c030049410f200061041d280c3c6601c8100e006000200c9030b040c1d91058080d102401407042c3c00322503040f51100040e000030621 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 318079361 1250 318078111 318078139
    0x901080a0f0224070f02130c09051207081605011d010507151e0213060c0519060b1507120302030601090e1b0703020304060e011407062a090302030714 66
    0x40000d00307140f22812403020000c00903240c440110380107102d0a4402d4030b8101004c2c0b045140c250141c50b8888802001088409080303400203042e840d05015013401076441c03800a030100700c000c00020004280482c2143d01d602540c03152452507800c584140c50206101c0041000503440942c44c04c0965601a9201ca04055447d21007540d00314540e5401e40c1d0b0165102c0b20100b0401c0021048804c002c0003143c0543c4e07810504040f6071414800e5070203c400c00c6644d60801d00001c001043d180f4070400841c0c241801040c03903080c002c3c010558004070903403160150b003540101001683c06007800e1070064400350401c1c1c1e04850b00380d050340700803510300f0f000036509181481899000c2204517003124038115060b054906081e40c150b0356074803854003600944c0c800f040401138507a000e11405003000081c82c15841d16040503c0c06951401400c0e00201140e0702c0711080e4490680c0c00c0b0006082e50200c0841e070350500040200900303800014003051b070190107404004111024900c0c80c041d841603024001468140b50 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 318080611 1250 318079361 318079369
    0x3110a0818010e070512060105060f180a0311030607030b01120c050c03040605030103020a090605010804030807030b2e05070f1b0e09100507030507080403111e0c0901080a0f02 77
    0x10040c007080803403116000e004046807091080a090601020041001c1e038186010003035030001120304c02019a000500600c41d540300c02095480510301c00c2c0c405a06c030f42551210713203c078504041c500d81c3c22855401c0c00000b480442c10040d1510401030f016583c00307440d1b100d01101662091802c0d540410130420402c103402180764002047e1020b42d02e0301a0408103101c00031402c1d94040e91104001410201c0184207504d0f00a50190041003880c6040040914004c000380402c00010405402c0c068907000040b420350094200322090180200794615604510303003c42c0c16403003001c3e621056081c40902c150f01c414014030444003004d03000b160000303000030a03a48021100d040c002c8002091504101c000844030303084001c0e180984140e402509607603000304400e03012160010441c2d82007509000a0101080c1c005a20360b0308aa09131800c0310109802c04030171407401c08041e0a1181d003103c508142088140d02191184801c40c04507070000340c507680c40b002a40c1d603640d01e0101a01c8261a04112001468 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 318081861 1250 318080611 318080627
    0xa0c030b0c0403050106090b0f01090806010603020315120d120908040308070602040b0313050d03051317040b0d0e01051003020924040e060a0605041505040902030f07080a0c0603110a 80
    0x4041ea10040c58a5165510903007540c5251b030129440c1c07134070741e08800190301d010b80184440c403400307180002085241610451752004c0c103124610038180e000003c030700c40c8183d10741c00210700d10010f010203411202d00e0705025902d003040c5801c4000600b5403100c00712003800c24011500c1e0303681c00c09111820207007951100311865210041c221031440d0308000020700d0442d01c4018610800d520340100080724005d05109003001444402501010728080c10494281d100300310340008550031101c40210700c40880703920950341c4240c0d00711344140040841d5000040041741c016400300060000248000d403a1000486910107543c08025800740e01003000500e003001e904400c030492a08040003c3ca000707441008601100c4a416807200b440c1c101c1c50811940100038007a0030b00800c0c041c2c4040010f01c03040e02000c00c000503103006180c480d94580c0a12f8040d990b00b0440c25801508070015189419520410660344030b40d841ca045584403c001d500140843c0039204030307070100d40e6a50900c1d03e440f011044c200d50802c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 318083111 1250 318081861 318081871
    0xc030703080a0f050f09060c0a0c0f030903060f090501060e0417130e160e2d0f06180901060e01020303011203050d150609050301060803090f0d050a0606090e0a0c030b 73
    0x59650300f010700350a0104d0054074040c5842c030724a5041c50a01000031810030030b0041c980c800101082100110840d031000c4015085a001600103050002d5442c0880d1209071942c000b415041c00c102241070286016441851b95a00c2400200480e6948030400440300008130340181c0080069680481031240d8a4024800700b106580403041c4141c41d403410080b9a04280c50848203820960103000701141c011143d03140900c0219824403014100130482e92564901d20350384c403401146c1e207500c0c110300e4075000f0680c07200b02030081050352103980403610041c60746054000303a03200c0c0201307600000310340e030140300d610324402410b134055451a0b00b4400258205c01800e4030440412504000d103403a1300ca070a03c40e800442c41c4140d00c1b148882d19140b0010f00707ca15980003980320340d142c20410449403c0000c212503410394155040400b02c0300150024040c40e0411102800780e00405052204014035a0300031000c0c1c1349208401c01820b1030f01c160b81591440741000003403000822190500101d400c05a85179401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 318084361 1250 318083111 318083131
    0x117120406030b060c030c01020711041a100e09090a0b0c030f011a040b0703030912170f06060c100902090f160c05011e05011d0919020f0a06050319020c03070308 71
    0x103040417408526660104030301c0703907059501117000c2c01081103030720b120710340031200303d0703042c030030303881030b40d880300c41d0704190031110b61040601c9241850301901030000f8044003c0002c01d05100e5250000c1041d0b100c03c00c0c0002207503032a07020400664142601c1042d6030040c0703c0204034043d10381c2171a030101c2820b03101540c030b20101a0248000284049070100a0126038400c2d0b8010580c1c440b18540079207560444564a030070300c00c4506900d00c002c00c00c903400603400744243c41c54801c2e94841c10042581e80c420098400b000d801681072221b0000c0d0240c000c0820f031031003500d02420a98500d094443d9100041d1211996203009440b407041d042d11500074240442c1c054000080c6a188055070041c2001c8807181002240d511000100549154031491285a980ca001c002c01185002c601403601c8060302101c0450174005500c0081c01e546030403a030388500020161284076440e03201c4a01500d02d401c215854412140821000c030035040f4103009803191043c205000b0342c241041360358151a11000188401a9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 318085611 1250 318084361 318084367
    0x10e130c0e04062003010b0a18050a0b0c0d0201050c2d1908220f081204060203060907090303090b0a030e0105010e0402100503060a03020d0218010e0117120406030b06 73
    0x40310740348403206001d244a00b01c0051094000e0480050140003a00c040311048401c1c001000000d441c001102c52450443c40c1460075032040200742400c42e0720f96002030344c0202204501040b00e5548a006103141700520044500107000d0b1041242a50302c120780e80240b1450038004031203c1d980b0b00c0035561016644225030080e02240070582c00441e0098144d950140a58031000c01e5501d40007104981c100c02c0d0562008030b090001034a401e50178030716070030003070000a0145041051085101c1508d001c1c61a0290441d018103280c10254040e40080c0c0700c90780f1074840d102c040b4140d1405090360b1003c482e41603d078160b400c1d10f408824040741d0860907102040c5a1501c03500300320b0740e0b400e100300c13400382c50318010601c41170400c3d00500c1403109801c000041404420000d1040964444103410101c0780d0440726084104013074404548640c80c0031000380d000c0c6031042d0004c111441c0d90746506068a0300c0b00b10741110708000200140d07841010100c204c0340070f802000217000261190300803010110000e00010703e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 318086861 1250 318085611 318085619
    0xc030109030201020a09141c03021f02030601031a010207301202070b0304080d0906110304030809060928020d0203030c030306011d010f1215060801170105010e130c 72
    0x100351800c021048005035400140b914085400c207580314050203403004150900345a820100314041200b00300024a000b003598103004041c0308200906c1010b2580b22314803042001d070070400c006900190703149404a401e100c01030661208000743e215038580141e00400e0315904e0043e036611100310500500003140790044403411500030300c1212903107040c0b241013146004e403013a200090502840b41c1001462000c10801e00001c1488030080d47e1035000880320000d8695154600b1000400381000110b52800c008400c00040c15000b809492107200c030360b0700383c4070f1a40d500b41f000d40d20745c001500c41c0000c41d602d401072100d0400c3c48240c070840c0c1c0c0c2d01c05800c070f42c00d030350151300020310715084000b8055666100004022003540d1110509140405410740382814441000028008400f800d684000300070a880742443c4080c80c0d60804524842e40b031040740f0311161610390091014600f40580d40b40d460500390520310a0f041445664102c45a03c090072415456865034442e58a440b1031003502c41d030714400004a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 318088111 1250 318086861 318086863
    0x604050619030b1506040506040e0901090f080a0305010501081603090c05040e0318010e06030a0f240501020105092b0c0605010f030210020c0307090e0a0804091e0903050f03090c03 79
    0x10003450041c224100d0b90315045014000c14982010114081d450030711041003140c07610308c180c8080e0f613103402882010342e4600d010709004141410300030b49084080d01000040c45400e00c010501d01049540a218581e00c0c1c3c0010342e80c1d042d05840c41000c044000d1450b40c6214481d6101070019442a440d9840781d6a0720000101510720b4000491020b0300300081840c020602c001500142107400c2c00c0c074950f0010850300042c038902009118144c229164801100490b1503035000c94000501d00c25181040e0f001d5101c3c5080040c00c5d809024059803a080c00308445402c001424440c201070001040da07050080b05040c1848031801c013908040c01960b07003a0400244480c05200d003e022240d440f8900a85540108108070b8142031100013990003c0507000443c1c0c40200c0c203035055660301d140c04181800d0f22a2481e103840c19203000036208050115004c00e948a29410000c0110760b004d041026407034526000e14100d80c00c1600003004510b080090351812144403025540c00780b9000c06039404a1001c501003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 318089361 1250 318088111 318088159
    0xf01020f03010e01120507030b13021809070b0304020a061b060207050a11010528110f0d032a03090f061d060a021806090301060f0314010b01080f06040506 68
    0x10306514003010005000245036181000d0040030141044503000701541c85154855106010240c8400090000505000f02c00402c0142c141e5010f80b02505845640c4591460480c0c26071382c00c2d60305d009100d00040c1c00b03000081507070701958008284058042c030349181511000c078502110600340d41c8240c0500b0200c0d101d0320141a8240c000c030050000000035282040c0281189a00c0d82e05000301072010724440074600040c504100e5100100c800e417070302c0305076090b6a40700102108140c81c0c401d1050807401c0382c1c40810300d02d214488645041c400e08a010000d450324840f1005010462400704850000d124800d4100000c1940586001d9842ca58161907100540e1401c650680d9542d1030b030840a14011002c00c825988181180710860400c00c120030309580390620741030018800ca80c0071418803060340d000c8d40701000a05400c2c8201d01c000e541c91a28490441c82050360795425403826225102c95405a042d8602c5112b9121050189541e5102080000c10002d400103800c9500b43e092854100705901d05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 318090611 1250 318089361 318089377
    0x1030506100501030c020a03030c120207050c0301060b040617040609080304030f0f02010b18040c1706100803030613020c2e0e01060602030a0c0305090303070818090609011203020f0102 81
    0x29001a01d06030701c403141c03051019400681014030b0184a4021a54040b0390300c030301e8650614020480c180150001c40307442e0030f4910840c11162000130f1100400500140c0c070855988181c000b07000390f641d641c41103800c50281c0d11581001c00c03210481540c401c0d0503408015841841404000b480d40625140e0302901c1e041103908a001c00c542501c1070007455007003011700300d0b8200d82d07100a008041005001c034420701c52005d6040103103c20f220115042224045040000e0003d0688200d6980c8503510341d159160000e9440050450707010030f0109440c040442101c0c45283d0162107209030200071098600290702044800955003d1f490102c0000d116000005c9098907214440c040366072108a4901c00f182c0650040610a0785407040030001e01d40c021040d00e0040f45282031540e400e1017603050071764080c800c0d1180103601d400f0000e6a0340802408401400400711025505181c0100c0042800004441500d003079038450342c0c5100411001442090700d00e281071080c4181e501410300c1c500c420f426a001a00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 318091861 1250 318090611 318090613
    0xf0c030f040e0f010810180b09010902090a090b060d0f0c0306020a090e01030c0b07050f060106050706050c03090a110402130e01150906120f1410030c050109030804090e0c0603010305 80
    0x103010004003040b00000307908081c200902048651410318281d944000c00410100596182c2120040b0300c00300a5000c0c3e0016081b0203002086d14110000328024036440e6001c03440b8002079000300b50600d15512824800c260b0082d0501255180d0100b00410454580400c4a0003103083c0d42c1c4100180d00030001100541c4a62405a22000d405401502d81005d6402018503240c42d0701c01000402c2c0c103030025030300312080c0d20391641d070704e00d05404e1a90410428803040404d9108034000050802e07400b200401499018000801168450f070f41030421611055a050034164040809807000c2180b41d04005009903005000600d800c1c00c05485130003a450592152803119071780c00c01040f0080b12a054103120303a42c40e1500f19111400c040c1c0180a201d08000040a219a43c80003400344d03c2e51540b010700b540082c15524003541c40e00c6184c0e484010546c1c00111040402c003500081c10754002c0901a0680e0741c000e12072800c00e8181050340c001045031241c0c01219100f840303610703181d03525003000460285004034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 318093111 1250 318091861 318091867
    0x21908011a130e0304090b04060f08060702060a1b080a0f0e0105060301060803030f1b092d01080603030403080c010216120807020d08010509090a0602030c1e03011a0f0c030f 76
    0xc0002c1d0781880c0d600b440003503040108128203000c0101c03c5905403000e484e0009000c00314080420024032282d0000160011030701d001007000a4001611403043c0081d0382103c0c50cc0d40e034900100281c880002c00c812010400441c00180c081c010840c455010401c0c110008407202c82429920588441c0d03004034030703165520400c0c4411390a00b03003c6c00028140c1c4a00a5180d420452484404480002c003181c10380218400610000034501080b00d005e03050007000800806500380c0031640c0b4640e4104044c040c0303440f0b0700140c03410394015481c8510030b0030010055030500d03141d078a50760490762021030401615582000b2010070400d06045540c25036010f00c2c00f0718101200b00d8800b030f010480c007805007402e55021031102c0b8a00d03a400404a81540c10a0f2510141516808030280c40c0c481c0c03c0d1402400716002100b04088040450060800c040590040c1e00d14500e00e01ca804d0301c148428028070000703174200c80c540c81e0302000c401c00400c600205141464904024448001c0c216041444a44140c0d4000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 318094361 1250 318093111 318093161
    0x203180d030c0810061b060204031208010509131e0f02040606090f06020303010e01060e010c052a120a080901110d020a03030b032b030204090905030306090f0c0702190801 75
    0xc042603413112120b048035a51600b044801307052000c180400019101900c4035800400040f038064500556000002c0320760080015005822503000f4001d5500030780d001d0b00019003c18031300141c408220303008103403d4154a409103207940c24006140c815210003510510802c0142c942e48148001811b540d91281c2c8002d0802d40d020101000640c480307000c40d44140018040b4000980a850460300300e4200904000c018800603241003d00b100080c0c2580900e002007100740224038000b0418030814400e84040b1070808003044071800e08a00c10001688c8500c44080000300001d00801c3c40c1d5605041800f06900400b100c246400c03111132410005800c032000f0345040507058003038504907013000c902034900d1a468449442840c4180c0a800c1040660f0003442c41209000c0c0d4100d07070282600110501241c00d2034180680e482d401510024002e001c00c1000660500540406900980c3c82d0001d00c2d2034000540c00300001290200041140c0070341034135000034011000d200f5007101c80d101b05100b502c22511 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 318095611 1250 318094361 318094367
    0x9120304090c08070206160503040606090c090312090608041103010e031605070e0613051902040305011d0a170f0405090f0708060604060207031707060603050304030512090906040203180d030c 84
    0x400340004c41958040300a21030322000352540c41c0e80040482c501203859544508001000d80b6003a809021000d00d030807001c112642d40b03c0208420369008a1a00c112200500c0d0300700c402495502c136100000c0c2c03219000c00c002074650700804000e883d0060001c0340e9040844803441c110341c00000e10f026421401801c40041040521044000344001300c00006185810b5010a00170340042e0404520680d9450006035462441000000240503840c0115160340c0c0764680b050090030000141d40c50582c80c0100c1c11f891503030004c0c45031345d665401580d0000c0718034440c3e030003201600b0511040340595814007020680340c403245401c071311640184014441c14240000081c2001002405a500a2900b00802c6c4005500019910200e0b039020209079011031103c0013005440c0984007000348801d04091000084c071800101510661303000744142d4900c6c000d0102c1c01d440c284218070307005420000d5180040d42e81c0c5131a901841d40205400e404902c00808807031145d092049280215010a98410703408001c154 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 318096861 1250 318095611 318095627
    0x3150103050c0c01150e13150c0207090501120b090105010b09060f041d042306070e0d05030c0717030301030507030204090303140405011d03090604260a0501061505180609120304090c 80
    0x2d09503001810301c60708c0c1c4422038000b220781e4088855617100c0242c000c002d40308100020040c08562410070055031103480e400d015001034070302550200e00c1c0b040401c0c10210103118150480c5c0d442d41d030184c580140c000c240201c0390020719507800208000c1c4000a0414a00c44200c1c1030f0712400d040041c19494140b503e1014001d40460703200c2001480070070180c0c0748200280c019001452070074041030150b00f41000808113008200c0c0100a8003002c140b08203074000024180c0e040c2c0314000e1000260320b088280040d5207010902c406040e0307601c0100e081025003055402566030340d0081c80c1c0408c4d1680b0301100c003541c1000c01c0c0d8040300c060f0b6407080581c01d00359840365541e1801120201541ca0004003800107240c074011801000c40d440005192440301394841d40030111000211400c1d02e0031011213060a500a00e40c41c407401145491407144c4804181c030440c2107500550900c0c020311010030041c0705202c82d54100c1c02841d500b028501541d4420303c0010006440244085000850046007110004000503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 318098111 1250 318096861 318096871
    0x1060507031d0d02190b07080901080610020a06110f07110f0f0a142d031504021f030b0d080702040c11030d1802040603060b0a0b03150103050c0c01150e 67
    0x54000030b02248079034400d1450854182c0480303000740c03208084170055007107408a034441000000b000807180c0400400b40040d100c085003d1b264441d00d580e598050042030104036410b070005070082103003800001c405500c8425aa202d1034081360400c0404141310311964000074050301c3c103c40c080f005060a25081c2c3c00960032103401e64140c01c4000707446011440d0f1380ca0074010340b00d60024a900c982c4940e1104c0380303084684807000108030b40304034181c03454032195041282c0141c020701450019038120151104003078012076015000d0140420f4684110110b4100351b07210404050300c2d6000341070180d03200d11f40184058020440203588018070304c1000b041b2050300e4040f03424070200711503240030712001005562b0000c003026000f040400c00412070050240d040c080081d0f105241c0301c0c000c01401459030000351280010382c4c14491454503100d080c040c60004461015403c52030480600301035202e9000300f50400a02c1c8411410076041922283c00c0d2581c118031850506c03202141004100d04191882d40c0203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 318099361 1250 318098111 318098147
    0x1026070801020c12070501090804030c0305100902060a11010e1f1a010c020d05030f040b071115031302130c0e0123040302100c060f0b030d090f0e0903120106050703 72
    0x9001010151201c0001c4c4048801e007901007240420701800390400c001149d407180480f13646070b4072454490035003082c90000b500c0620238400340020106c420310440440d903800134039a605200c100c840864190f00703400ca04145654032144607008a900030803514292023072010b402c40c008081c030400d00003101c5910582418407481d140c2c01c1750490740c00450740100c0f40c1d019078510400046034200240340d8030403404001c0c1480000180001c162041e0300150101d83e210b422400701e104141002c010440310f02001c841407200003000410340b03194541d04107044003840074069000c006401901c5c902211030503960175012456419010849c0d40e8807200c10809021302c40000c00c5000c1d01424614454059408000d02540301101c0358500e56000d41d030032103000743d4810350900080540c4000c02c4050b000c4101e0f00350207031203810380c00d0048a015040c0701069038089080c040500d890720044404c5000003400000c4540070800400070f000294045250290055031103059892030b40c3e10f4000d2124400981c00c0e115 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 318100611 1250 318099361 318099367
    0xd020c030d030b152206020706090b0306012a0206030910392106090b04110304060504030c050a2103020f0d0509010f150906090c080f102607080102 65
    0x503a6840031081d030400420403115540380ca2048030345500c1c0f035039a140c200e80d91180105e0000340f82540001c0500c1a510320b6075400c543e940d41d4101c001014001650824013140d5400300103e04104d112045042c03203a41c22044854404603600418500e0f4004c1e10b04041e103401000410020204078062086880b1441010302180e120407100314124100c0100881d00b11f0b400001d910610740c3c4941014040440356000c0f15800100100c1041e00a10301881840fa40d00c0c01d01c0762104651070320744548a40d40000c000084d1031a5034650340c29004000050045003480340c141c11003008034800300b0220902034402c0e4a8240c04159182d01c01c4140001501c0034000c01d03004200d0f043d004900d440c140c8100c110074150202e000c0d1142028240506004119001042c1c64a401c00d48190410000700b0700b03c94504a003000200d03201c0809606a56501c1100000306180c00040740c4c0742c0640340d007800c0e1b002071341d441c0d1403218985408803c840000b50580003a01440c0510071190f210324240003500060200c8402189 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 318101861 1250 318100611 318100631
    0x130222030b040305090315010608040302010f062d090204150207080c0a15020c030303101a07050c0105030a150b032509050d0f0519051902060904020d0e0d020c030d03 73
    0x9414010001001c2000c0800c1c40c81003924100101f803d0250000c090130010368642e9001000c4190865042d80190308180d030380c1e108460320f48030b00b000b61030042e1203024608445c4422040640c1c0d966240350b00400311000b00107070313060851010380090028580300744090691404024038282e09038001d001e041d0406148180c0701e90307800c200c80c2c0844122b441c0d10081c030a072642d0243d081015480c10385816010010400c01070ba42d031000740e0000d581080b20240b00c2018030039480c101a0041c0d038402001580b050b0060b1569600500c040c55128107281030200707103c0c001c04282d00801c155680407443c10388001c024020f040328410342501e218424001d242c0d807100381100c0d0007080300e5124483cbe00d00802e4810501d1043c0140004520b16040c4c00c04200c401d030034003a401c80c10035500071040a07215402000b954040c4602102c80c507150943d00105040d0078030801d601040001d5015004440405a488d00c504080f00b0051040441c0d0036400e030090714607030b8240c030b00b414200303000c182510003007600d080c9101c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 318103111 1250 318101861 318101873
    0x20309011205090316031e050705070b0309030f070804150e030c0103110f03040c06020c030d1e0c02030a0c050901120b0f060d0c03111f1b050c13022203 67
    0x20014440440102d11a152034403d1401c41c0b11381d807803048a54100500712414550442c1c00300c0ca50b98000314900e070305811442e00c01c64440c002c0312030040150b08919020810300310600301458000c0360700802d680c90001004800400f0341d100d90f10441d1044000300c0c00700a20707200d8801304280c0306190b0402030300340801000000e40f03503001d2030029418107960b801c40c03505003043c0100352401503d0003a00541e80381410305100c405070750540b1407103005104480c1401030394240401c154502c10b0080d00c032103c00c1e10840c0a07405206074100c6a8904004c9070408010240ea010000e01d26150b004012010040e41000c0071300400000581004000c8402c045c040000210301456196100f46014044a001d89461000803c2e02002180c06040c140300c407503000c000e0240400d02900c121004844c103036521100d078580e0303600360301c0d0350380600c0e0120b40280e0320301c8404900241d6502c1c20901c41d00075034442c03404100008282c20324034050340d65629030100d400c00d04d0106031069010003000310198080315528540d105 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 318104361 1250 318103111 318103127
    0x30b040b1006020c04151809060b0f01091a0702090f060109080705030d0311130f0e10050d0201050714060112060f050c09190302060a121821120906090c0602030901 72
    0x3d00550366940c024507004c44802c620b4016000703005a6011103140b00c54411f01a083d43c0d407055605510b400c00e03a4220f85804601d0922620043e180c844166251512030724240d044a0035031000340c8410060840140c0d940083d440c070804841c0d00358050750401c4000103100d21b4040d00305560603402070000344411b54000541140700451480c002c51846444011461103005e42843d08041e8560410080b07450f07941405448180c648070118070003156070b040b42d604030700316280c801e154211230325124400c09944144010b1031000d004d42c24010225010419040ca0500240e10006034840c00e018418100300b0540540d5080034021401032240c0c0c10400003501c100d01c2611141c44c032806041c010038000c440380f00400401035070018203d07030b2142604180900040c1d50458950007051420750301c0301304503480740c620121741c030740110b007120b2800803520729a28124540c2203005c0c10b10600c1076940701200b98500401c10312718880c0b4000f145040007403034203c00c000400d4000c601503400c1400f00401c10b036800351034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 318105611 1250 318104361 318104383
    0xa0606150f051e07020d080a1205060604231e150c060105061b010203090a0c09150608060301060e01080c090c0421080c01090614070201021e03060a0f030b040b100602 73
    0x180c1d4000892204540c0f41038441c3c00002500010419010801d0103e10030180554240c242c40300300d04007840140d40d6003103503012a182640b150040c00180002115103400841c001941c3c041c0d0210f007030340c100016100c00c0048a410404000c3d400030103800e41003c03222001d10786c06005902c0c3c14140020480b60306d60005003e080e000340408904e41d07180d000e02042c1d04403820800b1008540c2c034140a001e054540c07044820a54190000700b03000502070320184940741101251420030030015080c11011221030340080d2805501d5034075880e02140c65210380003024002c208041c0107040f9410b600c81400103800300242080803401c814003040040e801e40044807030a01d040307190b00c003034070a045183c903103000c0c010900d143c41c9944c0303403c4040d410800c050780100c1400b00b81420003081941c501d40e04a00343d1080d0540501a48181d041005820b44410043c54001a00404161900352140d440c0800e1940300e80c42650030900c15000e120a1003c03441d140c0e034020400300c126030b07492402c0403c081e61f10121021 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 318106861 1250 318105611 318105637
    0x40303110f031305031c0e0d0e010f080703020405030f010f0b041404030810090f021c060f0e0901020c01020703020303150307050904151d0102090a0b0a14070c080a0606150f05 77
    0x20f50182080002d10884c0c0030300307040a8000b50410340f90a0920010070b06580c0200701841400d507a0041c06004103079204540030165030380c2e450404403403012030310500c018181000b03058090002003000d940a0100401c500c091400004441501451000542e1440222030340074501c0c10810201c0390040d0714038158019058100440c09440700d51a40b0000720703a59016002e464941081441f40700c4241d001041d00c004483c194180f800c01d210194000c407401e03172084880c401403268041044a0140c1e21407640688580001030401010201e042c0c2a648100c50480060304004100000404025034034180e5881c00d4000304062800d0202091700340e0b40290000d45180c256550781c00c400c60356500621002c20081702200000702c116508036001c2c2d040030704107901c15035001d20003092001083c82a00c500054642d29103c01c6805182d07418005e911180d01a00c00b0411050f001c50091401c214900320301c1e1040780005101d0303141c60411480319945428040400081c290034961043d0701c40151138130158600 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 318108111 1250 318106861 318106891
    0xc070f0e0601261e07110c04150b040308030105120f0c040513051c090806063304030f11030a051b030a0213020318030f0a030b0f18040303110f03 64
    0x40d40012507007034440d03c40180350399036800c002250003e0421400b00030911070a030b1849494121080c0d405204642004815500081e4400c0c8545400d42110b001b50384180c00140b41c0301d441d48010350040e48260026a0200c000000410090400440b0115140c02a41c09071000c075000490a40d290240051414412500c40011810a05070250020056035018080381c822601e800d0950301c0041400280c140402c0084000240d103000109140d0b114180083c0141e07080380c0154404107140b03502e130b40c0c20714800ea50601c0c1c10000910b0b5a009002641c042c09015520b50703498640381c40b00d0400c41d2807103402600440c2d038001c00220002610209616080407010312401804003007803501d00c480718040d501c1400b801000521541c02e44c003c500a00030f605034818045000d2504994a200b001411408413804000095010b4800c1e80b013000c0d03a01c0700510303071800a04820005a40b0219040c04843c1d0301c4500700034003080603014815502c0e14042820030500304000455180003902009004510510180d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 318109361 1250 318108111 318108137
    0x1b080d0c06090c1509090b010507050a080f1e031b07020904030309060b150c01181a090106150302120106030c0e04180b07081005010e0a090b0d021002030c070f0e0601 73
    0x1100701100038161003000e0310f00c131050f040e9004008103042c0c40740c0c294092900082d48240d510600890314030a4002c0f0040809070f00c2136490b000725501c07521100c24441c07414000c2d06200d001d2000d1240d000c2161000c2e05840f420b00b1a030005540070355011108060348100041001610b858801640c855094103000868081c241801c2d40585100351040c2c1e401104042c0004180d810391015041000c400802000003204000040b81002c0d021803000d449010f01c40d0028a140400641880d440b2041e4000492259512000303200e482e240c4c1c0394180080b030380218001006000c80000180180100e203028007908101a00103041d458050b00c4250189849407403402083c4013030140c40d4000313540004130780401d02e84810000c4c40050151140d101140301c0324800512580714496842008400400c201c514501d0301b2070711070040c2a59000c407600f00008540d1a00907a40c0d18a03c403d508440750044c50f51000e420042070700f48505504040c0511194001c14000303050181c03201d0340d01c50003e00302043c1080ea1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 318110611 1250 318109361 318109373
    0x1027050402040609050c0703090905062d030a0c030203010f290102030f0301030b091908191b0b010f062109081303060605010801050d150b18041b080d0c0609 69
    0x480d0b0088100c0038113080a2142d541100c8000703003401c50003662001279194485d03400c00155034041e51b26640c001d08161403410910942100741c00c00c400051524800c2c0f01c4c00c81d001c0780c2000d01158081e523915901500c1001903050031300542e48850b00d0307482c08008030502c011801c1c81e6008080880c08601042c0c00110510386d00800444119120111405482e581d480c038025582450803034464056010700c0c8440d00c40c001c4100d00d020303000e990200701507044c10311040740c1403031400007810500108000c691100c0d201c80071601341585007a0040c1c244000d00d60404000548801c01036210004201e0341d6241d0400048440502441840101401060305610350038250100d000b020700c009481d14281d203000003000b00702d40c00802150020b072210002c40ea80c0c2d204008040c1603040014120659083c1c00b2080384125030b200d601c03540802001c400c50b02603411902031802404940032542c20a4545450386551108100c10004294240003044c0e0103c4029000b0b003051041c040040060f1348440d202010440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 318111861 1250 318110611 318110621
    0x70915090e090d1106130308131e03020105011a121b1605010b010504030812040c080d021b030a120e0102010207080c01050a0c03020f07111203040608102705040204 72
    0x281e151101109040015106032505203816461022400d9203010028444000c40c2e0144074440d502d141406e00702040d2410348440c040245034065034200781c81d4440c0010f00c68034000310003082070114141d0302003c0f8035011303084902c181c000b54080442000c441d086c00200008039400060b801c00d86508640329607140c10101000403801048481c0e0100d41c0e840d054405201404516015400030301c050041e150054503117114500010380066020040000c085021070201c0c1c3d005445004880081036907454410700700043c1c4500180160005d00b00e008003d03094200324031441e02d084000d810102229500d081c1c2c03101a21480c0424005c0b80d0240c11400c0e8000c2d41661007640d000040d49954000f880c880038024141110100c0549241412505101e4031904c296041ca807090700303032680b500d24961100d0003c600b00051413135005007846054149200c0a00141009005d540c4441c511030400c1941c18882c0c45080c2c00120710002d100c03c0400c1a00d1841c00b520703205168ac28400103030b40d1203138008500600 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 318113111 1250 318111861 318111869
    0x181b0607060e120a021c0806040c0e04020d0603060f060b03130f050601090c02251802090621090c01020703060e100504140d0e0a060e060d1505130507091509 69
    0x8014008010351106140004107030340072042d420380d20011160f546c3c840710040d000305030000040b1140009001c1c0e0405038441c41111100382004441d9014480000303050341d10100000e4072880c1c85070420810000140186d495155a103101448414100440321280740030060111035500c0d80c008c240030500c4907403d040e800300e50300304007a1003866845d01c0c1c420024022250b0b60f5001485030414041e800e201181017401460395195150030903600d80324255021300000d00c888414a0390030010790080b50307101c0e8001c203a5841c42903000032640d840e601d802c5034081c10081188406410158038208582ea0101c4d4040a403a071081d8002810a4040206482c0c02003c03d480b40300c82e458041884103028080200e81c4500d41d0386d404443c0c0a100074101228084502c42e00b068020407000000d2019901906000c4a0801c010740a1800c0400010000b400e6903112246e241c503102c2084400d0100b801d01c00043d50651100c5807082c4803908204c04001c003d24030500c14060b8000d02c1d445904a10f9100d0a0490010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 318114361 1250 318113111 318113113
    0xc041815020316170105120717100e06040b0c130b07060f060512060a0c030213060c0302060a020c03120402030f0a110a0503061902091503040308181b0607060e 70
    0x9400d05540040080d4010354000582c2d400181250008511450821603244100c204081e1142d01e810148000790010860242a60290400100d100341c2d81e01c20007618030034018010711080781100d50450440b03154400700c01d5540c00800030813020900301d91907035400103200c03e01140e41c1c0c100c0341411407004c1d0321074000300f0040c0d000003000300c1844a503070421004032400a0040210995580030003400b0101c40d0040841358005178005600d414041c7d10152124080b070a0251a2070087e0b9036041d40004250061008a550794610a05040e810450370f40d000440d03250071440c0c42504140711760780340070b004040302c80d212518000500715101805207805004450041b50310348031661034544038000c0c242101710302a4400e0b0100290f149000074045000e9120445810300b00d07205c03101c83e1000f0354010a2400d40248600800000030024240258030940c001d94485459081000403910050300c900d18003001d43d8024003000032684004a080445203000f2140c1c60342d54251403030704201800b6940110a41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 318115611 1250 318114361 318114383
    0xc11090106110d0f020a15060b040f06030c03050103170903071a0d14071707051207031a0301060b042c1e090303010602060c030601030e0610091d0c0418 67
    0xd07590300400c1c007107407101441080da0181e0000500450f000d101d031038505401079000c00400008a485640c075208140b007440e8000c103045032105804039555006038001e04401258090130000c140e454410140c2240b9149030a0007107500d1500c400140d01043c00300080055800228036601d65005c024100041c100060019403e0041003040b403500e8000070b1400700072504180c084600e4482d0741810b01c1c820b1a00d921041040340418844445810300107010100703100080083d200b9520008240b68410032855270085109a2440c00c1044c034014440e0300b143c0640e052210601c80c06031030600f501d09446500203a4070203c030340301e620350840b4820398024148040303074035041c01000780d10b0007000c0c12841002c0e08044501c0d10303001c004035586e21003441410016003143d0003045a111700b0000440d0031040514011036032034030300031506042038400d480c00d841494a0890421070110380e802801c48040b00014540188000010995151480d540307045214a9070b41d40092503002e200f04d450207905070004c4201c88 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 318116861 1250 318115611 318115619
    0x3040509070203283009022e0e061201031104090206040803030105090f040f08090d1202010b1c030512040f0b150a09060b0d0e01020417060f0f06060301060c110901 72
    0x2904056011100028001c4400800390b40f6035017001010048038020141d02c05080402c0d070030041c140c03140d003280d00c0b203a07400c44c101e010511075004080c01385402e5101c000340704440e0009096641d00c00300c2580900d00500c0703400c0c45103a07141c054a0460307400c0505c10460500400004001304174a590082d4042d0020401290404000000d58140c0d0400c0d034a8804a403181000d085070060708450040c0001200b0190720002803841025212285018002401002c0d0301e50364820039000c5400c3c0e1030010307951030481e41114545a065820104200a511803035103a054078010058070451314075030004000d083c0820100a003100e904e03101950020542c9507070b414090b10181706604140d4820b407251304082c001081c190460700c6401e0856400201952402d400119020081d001d006071480c10303554240000180d03488080301c0c0703440a40c085005000c07a13250100038540c00000c09402016240700e850b0412140f502d40c1e000b00e9065074007a00305800191150311707040c096008000182c83c1c0103607042e40001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 318118111 1250 318116861 318116917
    0x108091e0307060f0509120a26070206482109031620030106090b011116032a090b030c1206060409080d02030c0c190503040509070203 59
    0x14654480e6005201c1c4c1c8507a450400143c07001521190b0507074001d4030050098084140c0102039540650600c00100c00c1118040c00000441d1900401d02c452402c08002000e607040c00742591218171041c0a1514800c405108410501d8049040c0f41030070925042d503900c000488040c1e410b52516a0103266560f9104904426405012641d41022104280410200807000c02624406401e405024103100307041e4588902003103000c2c24520311100807042a0750103403402e008810180c807483e81c0100d1850000000100b00c42c00c0001700301500e4205006a0120100c0c0800b1001203d810011010140d9642002e40c064204004d50b00c482e8484805800241c141258120894803c4218160b400303001c4205c050000000c0884903e42d415002140042d501c0e00d410303401040c40741e0044c441c0d41e09000c0500c0300310080340e00540d0708a24282c000706111090100c01c01c070240e5a507601d620342c0e4043c5030303280d99040c0e900d0181c0d01030207114062000000340c04620810640b0078120100341c210894607540c420b09 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 318119361 1250 318118111 318118117
    0x140a0507120c050610060c03080703021306020303011404090f0201050a120509012007050c010f0c060603050610050a0b091e180403110708030f07050c061804140103110108091e03 78
    0x2114070f03018135000103180b4105138400504494a07030300d41c121001c10995044500030801001103041c546d0030b02104d140b2002c00c60300c2d10007501007a0000c50b0707213506004880c0c82013110300c1d26841c8918200107a402c000ba400038009000c00d5070a0910580b0b0b0b4102840c02d440c110000d41740540e403540380204000d8404030540042e40e038400480e0650380700c0c2d811124000414032804a026165500c00003400e030389540b0410003040410b40c14a0700000240c4190350300025980c1690003500e1540c40307201805110442070715000020312007200c0c80035100e440c0043d640c44c140200074905101e09555294034103012800000c1d20380d4000010600e60509d500328443d81d04800d0151002e400013840d607500003829460000f20320003941e4582c0c0003182001100040d000701c44c0e1003d40c04030380301e0107503c55402c902d844607009405040c00c101c1180300084106024403003110000980280c401c001c803001013010641c03500c400e8150701002e00c0c0c03e00340d503130300c140c6014500052005d0350703806c0058583c0c544a400c0000720107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 318120611 1250 318119361 318119363
    0xc09040c0804030e0f0111030406080f100608040f080708190225120203030d020408061501050a0f0c0507210506180706050705070e0705040302011806140a0507120c 72
    0x40203885266501101c80e1042294014045044441c0d014076600d08000b2000c0c2c0c41c401494840c1c1c0d0702a9282135242550450f9021001040d03c00c030612058042500d48c4030303808a180c80c00706c843c0903d800801010202c0c00350010345800014000081400b02543c02c42d44401c0d04506501d0b40c0d01c10755140e005246100c0719100c0018010f00c6000d82c144000540204000783c100c141d00000d840c00c10160311a0040f81040807603052108010000c03e1000e140054030041113114003030042460502014603081e19050711141c1040010401003007441e40001c1400d1646403d480c03d1002c003000c1e80b800b64a045030380e401540c1c11100c2c050b541c0c0302144641000003003035840303503040d544c2d65212402001120804142d03440b030719800a0314144106840b50002d402e896015000321030810740c2d50700d54802c01c2241036565100142c0b00040a000b03550b040820800052180301d624001c103490048010424107004c004259800d800288400368584550140e0b090700341c100315a849460210100a0070380459408 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 318121861 1250 318120611 318120619
    0x30204140702010b09160509010c0203060a05010312020105040302190305130806150409020f0409020612070c03030507051c020f1c020c01060602030313083103031b1502030705120c09 80
    0x40030310340c6003001d04480e40149580b1141e03504140c1c4400c807e40f030540203801d8030b90420500c506000056601009290301400c0c40d804005001d50650a2254032402c441c64030b0000e5a040909000000350b0008804105001140345c1e51002002403808032450b00c501c0e02d07080070361a000380e0003043c00300012070700500410348412071410034016070050009070b4054141c0039611200700700f41070000e400c20b41c000244480c4000d11039032a0805d40401c1c0302c2112411b680304000074040200481c1010303050f204580d00052141855410041925500780c2e803604440c6400d1040c036000f041c180103000d100350a544404024019084c2049842d9803042c009400a6541c440e4540c20000005416800802101c1c001c07907291642d03610704821501c994074160b200c50010008031944401e0702503130000309a1034070080b18401c52965201803450400424000300544a84042c8040310780340c2c0d0000e14000180c01c04040c2031640981c4960391800140c4482c01a802d644503800c0c4030b0001c10007c5030840008003030710b00d0121 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 318123111 1250 318121861 318121871
    0x210030b0f0a050d020405101503051905010806061504080106230604080304091e090b06040c020f0a020111070801020705101401030b010e04060e370201050f1303020414070201 77
    0x1d01040408803841c41156004101c8007019805400d003a002542d1204881201c500750a568020052003144400e55550000e5660414401100300c1c1c050603001e00c032074040040c0002c1d410203001e2a1110f40103410746118140c5c2a5059801200381c1e01035400034060b140c000c100c41c6985900100c078403054586044100181c4400711400c61038182e060750141d0342e010004609041c10005920b008107801c8407080e1a0300c40080c502040c0303039200c0c0182038100d840342c40c80c0082c506100e4280710554130440004001c2d5045060500d14050740081d81c01d40741c6809103010440e02400201d224201409074200154a500001d1000701303010001808004180752410100300e190603180741191410000e000040060500c3c4004102d0b040c407013001c0d0354105000e0b000c0042c01d0083d5a08451804082c0c209541040c0700030040300d40d4080030407071010700030028600c8060210b10180c1c00205107200d40041500b10140220b00e01707201072000c8480202451f4003810810010b0300d000c0381806201403c0351444010340c204 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 318124361 1250 318123111 318123139
    0x6010504090b0c0c010e1b1305060f0f130c09030c080f070302060706150e01081506090f180f0a111f080606120103060905010c0c11090606070210030b 66
    0x60710420001e1900000c160025403180319034a14154003003400e10703046641745d422020304083d09001d01400d40444503126000c0d07040002c10b119108501415842040c3c0c5040c0c104403260319800200c03100710300c04445003824688918000717007402080080b02c81480d480c050de000c502c640c10558a1042e20b00814103441a0360340c071828155075825819511070303541c022200400050078501c1c040e18142d40f1840c80806d240402c440c04003900000c03580062152100c9a00400862000380f04e40c18034940010700c40320301482d1a40215041c10750142c100d0000b041d1110014413402402c0a00d505942d20200580b83c044116040c0c3d00d03070300e41748441c00307485c2480e02c01c2a884682c90310600c140029001012044c4a07400c1c03040301600c138403000901d901c2c0c000408014001140f49481c0c0154069482480000780307800d0282880c07400c40320021064010300c0452604070002c10310131000f0410954045803407110683e50180403030018095048004d4010010b0200300420316010780102010b41002e0b101c9900004030313 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 318125611 1250 318124361 318124369
    0x1050a05011e030317190c08040213020a200c060c01051005041404060914120c07080309060412020103020d0f05070f090b1c0902030f0d171e0703090c06030e060105 72
    0x2c0c5200c01008251a4140c0d6981c00b02d018510f1035000945085058103069003101540a84544151004c002821101000300718030300741c640010041c90840c0e0840c00c100da901c10281c03d040480c0b18030000301100c10b4440038000d4040050030b841c0d4001510b0a9121640710100b1401f07400c0030b540503504880c2a84008c00e0b1804d05200e81144050103003d1041e45442c0c9449000013003048181c00e07602006103090819089404000d0f990031507402d802e6250f900c3c041181c6127400c00d60385d0b400c5152a50007c00c400e8109a50310419103082d100800001c21524804c1d1005a00921416401001301c0d801c0c0401560500d1275603209500c101843d4880619000368070b030341140da070900c3d40504000c100051120500c50340008115100303110100c6400a15003440741c001902d00004110100b020364440040da6a545a210014502800250400180d1070030301da2000080e002c0d030810f02d010400b55920028484522a400103046c07036030480c80c0c006109444440090141074607100d607241070720401c0000201e03414 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 318126861 1250 318125611 318125669
    0x2906040b060706050405010b090709030303063305041a0405030c03010501051e030f030309160e0108030403080a1205010b04060207061d100c050102040801021801020312220501050a0501 81
    0x12009110030b02c0c0440300d58031500100005442600c0e959601c080c0c488d0f0503282d00141d40d004401030785401108526501d0001c2c01c1d90441c5d002010103071091401c0761010306400f40505601724413001c0f203c80b44102e10706c0450f001c0c0910350101c003070090310038140b440814080004005441c004d60542c1c18112146051609854081c49900c0c0c1049000710b140d44103201c40c0c2c03001004a00c2c02020303505800c0c001900c551454000341d403000107a13040700c1480500c0c10700030000f400007400c0e240c003144603540c9000c036001d4072800b07039100141c0580345c00030340c000c038103441a04542c2039030b4000c0c001003119507140d00c28000c0c1600715024800140c07080d0f000c0814014080e41d011000404404056582031002c0b005110301084205003100601a5580c450000500d0070b0020740003a09050000513100d15258915079000d0713080741910f07419034104002080c284a082e02a050f40400012203540e655002203030300c029103094224000d82103503c0c080a0203010741d11500002d048170b811580d41d0040d014101014000f4103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 318128111 1250 318126861 318126881
    0x90f040b03070e090307020d061407020d02060f0a11030a06080c030a1104090521071127070e0a1403072c0712060e090d1e0302090d290604 61
    0x151245808003e40440c07540303569070101c16841900e041c52030a03030210340e07403010445044600503141c0f020240c034034121018055100390b4a200400790003009040107134031960081e2030b420071184d20740300054004c030603500203403010100036141691320302e0f01a0640004110038010000580240e503a880e4180c980020384007843e6800c1b9005242c4004000c0400c0010444c0316000c44640c02400d5040c442030941b500d09488205200c0c100300d81c0c550591a011800352180c881181c8102f20807100c02a80f00b01e0070b204000d9051100b401c020302900c40c5a0281d0f440e08086170081d43c0321040780b40c0882d00300b800e100c28031100f90040c3c04440c4804d440c0c0711030083d030004014000003030308440c00408200856440d0079503004103440c10200c400c80341c40c00c070381c034251031144d041503200314a0075040c0710030301d1000c1100740052085850004203041c0c040c282c3c50000201c82281d08101900882c00008654401c3c8601410503480181d010f10120a9441d92110b0140c134801d0801403110000025610b0425024044080c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 318129361 1250 318128111 318128113
    0x304050a050613080102040308030a0f090809010f0e0a060c0b010b0c0c09070507170a11010c08060d0312141b04050a050409081c0516020f060103031b1502090f040b03 73
    0x2041c141014403020307801c01c12680b100791008440002c1d01140c280700074400303580210009541d03403515695603016a0b0b20098907680c00740c500395a140204011006070380c606002481c10ba11075032401c2c00204d65141000c4c81003540608103900018103d50000800301ea00c0d8461852441140c0c0c0c1c68000444a002d00f60185449812081044050345072561441c1e0b4401d4903420b01a060681540f40c23010803003043c41078400e035102c00144003102280c012424010440c4074000a020764000140028900030010344800d002d20007149408080501504000c0340c800d0311680c040040001030040c50001d441c01b40c502400001007100c030004003100c40001c543c141c50000d091058a60300e08001d210007071540040a407050030080c00483c140304c00440406440e00c050010109544c20079140911410214001e0002558007240520701c600c040031a10b241143c0e010306180e203562007124600c0004240c860344c01442c0d11140c16070348001e444a58060b004400080e41d20341c0d030040034081031100302c0d85564452941 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 318130611 1250 318129361 318129379
    0x7150f0b030a080301030f08040e01060e121609020d060905040f0c060f14030c0408010c080105090a090c0509090115080f060a0621050c0303120a051b07030e0a12050a060509030405 79
    0x4101801140c151f41c1c7e00c90040c10340f906a030740510702d14562081c0c100c40002003041c0e5030b03100c40d1320340500024000100c040150403c440d4849400c04694950703c140d158080e000303d41c1c4c030465009607210000400701e40340b0904c894506450011621021a036049170038480382400419498401c55548606544a4451440c0185c2c440f0311000c0c5600f000b881d221300b8000c00c000100c0c01032000c0c0611411400700b41c81d1075403254100401c2081c0c1980042a85075031a190009601c04140c945100380121401a281e4100984800d564039001d8000019207400040b0a6480007480d124001002864401d2040035131b04c41d62943d0100342c0503030350f080c482e5115444000003104904840a000700340b1851040044681c81c00381440031a00f9508020f9060300c841e5015002c0000181040c054240d200d104000400c0d440c10704280e0200c2640105000941000030852285580341c545000200c064550800030505c280c0030b03450071035641c110f510801c481e0301d410700012429540000060b0340c107490b002804022 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 318131861 1250 318130611 318130613
    0xa06020609030f0d1e0c03050117190203150f04050708060411040c0e0a09021201080d0912140111090f010f0906050c0109061802190b070303050c07150f0b030a08030103 74
    0x10094001210100b04940d40c0c5d0043e031007840350b003401d45c18a90600c01000c10160820803000e012500305030b10035446610102094081d43d00041920190041402000500c203080c60001c80e2504802a00f8590707142d20758400e0001410950441511461141381144c4010b501c4827882502c403842540c0040c0316081031b5440c03040902d003540009244120f14600381c003420186200040c80040c19a10042060394000741c1c0c14880e4070030101d0325001d42050350091000400001000b4002c102c1482007407002c0250030707040030811182880034041981094001e001c81803400031030b4102a400313104110b00c01c40380d146011900d9401082410360400407612407514a9150100c143e403281c1c002c045c000029548e51001070005040352140014000a00094504a00243c0b05200b0740040300d100002d4003070603c600c1000b200010004560f003690741840c2c0805e0030748984440d40064043d000300248083b00da03c24a001d00e084940c440c00351305003100d00a04c100c404039414591110210000503140c2030003000180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 318133111 1250 318131861 318131887
    0x1020f0c16060e1e0409060f0f0e03032e08070806010501120e070e0901020c1504020a0501080f0c1c050f04170a02071a04080607020a0b0114060a0c060216060504020a0602060903 78
    0x450b038401c06040816143c40503a610b000b141e0000113030505503a901c1403000c055600612591103a001140015407843c104218003140210305c60700d45509042c1c00dc0064900100070005a0004004800803101c181751108809510f91409005242c0042c001c45c1d2440140c01c040e0003000200e0000e44040e10601d8100305c5004440c6d41c00034018140c070743d02040f800700d038080100105011030600c10810342990405104004c9600aa07038030190400500c0028401c500890744a4160400d18242031142e480b454180f0309403400c03080c140d030080c82c1480c0000b00000e5000c0c0e2040d485c401d074454030010200c1d1070f80700c0c118000380c029401c0e01030060b8001c00080c4031702c0403141d0100f81c0752000c40c2e1142c0d0501e603175160380e079141140842d06000140c00410410302081208040f0342d0140034082c1d82030b02b540c040d80340829032900071150000100034940740700c24180400b560481d4600880c13940f4000c0020342c2c0c1d042400c080c090a60b002c07401903000701000100c0500c042040745c000c07032100b0040c41c0b0b003146060180b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 318134361 1250 318133111 318133159
    0x80304060f18141908040918030206131b06020d0206100b12060d1205043318030501050a06030c0f081510090513020906090103120c0501020f0c16060e 66
    0x14107003071040c600001009041306024103c3c1d50b01c2414540da9403410400326506945a00300101c020080d200803410019401080c00c42d800765075400090a2101c0034140b5070451020307a110140c2c0d004003520041085a400303e1740340d24048464003201d1080d21a00030415401030035110b0900d15040c20f10542001e5000030b210310f50031000042202984611584400400b445124102c101040300005d0070801700c4080081080c1403940340401d820107514030106180b030200649100d81c00c00c4104410080b02c4910124040d0145030000000c0040e0b2900e440078000400141c0020380b580f5100a000083c640e0380c408a850a64440402030b01150b85003252030b02c002d01d030251000d0460756110740c000c81c03031034858460b09202d0418000c1c07808180c42c15005211038214003a0000380519211001400456003114010044440d2440c01003558025802c00c1802401400c580c0c8010701c07000100594800b0001442c4000460080643c580d966603e17081502c00c3c0100360075450f0007124810309801418000308030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 318135611 1250 318134361 318134393
    0x1090c020705181906030f03050c03071b0611070b0406230a121103040201020c060307050c071401110601060903020409060e1027030c060e011404080304060f18 70
    0x101d54519464200203541441c52540c0011450f0386501001101044a08030740900507514008005a6081d6150921007020032103000e03090043c0040c011050348810803c848000780c00010040035086e108620b40c2400c5040c2c403030000083e0b981f0320245101c0002107911011520308011680c0350618011040c0d621100307085045840303c51a00d000d4050f14152001441402c0e0b00e079540314401c003003001c1e03017500700d40c1c150742401d0000d00c040c010000142d80008132120600011035103561642d07165001215a4484c1d004040d015004001c40000c80029800e200302c80c03a03c1c2621640c0f00c6803403104075070350f44020901c150300018200c1e91082025003172583c4510400380c01800041044080a0b0f4200d10b00b42030303034030114450395a8107000411440200e07044540f4011000910400e800c0d01e490083c0320603481c1c203000e44801e5035000c4c40c080b0000254060408401241b043d180030f8642810003400540003164240c48240c2401c0900b1748110a80c461803070a5007400840301400300c01611404012000307200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 318136861 1250 318135611 318135613
    0x15050a0b130507090e090c03010f06030b0f15040e1e0105040b01140d06020c030c070501050306060a030e010207020a17071a0724050c0405040f02160210050906030a020403030f0c05030301090c02 85
    0x20104001d94510001e5200306d40032002031045600480030b150840b90960324500b0300d03a1616000b400010080551550020721402c4144419103816030308042e000b00610019500c14039012420300103240c045500e0301c00f000059850b03444c1108600f000ca003a202c08660040403c81c44100501c20200e0740200744460300c001401018100c2500e81c3e07807200300e0b0b01c500c0c00b03811a03600c00301e40202501d40401c480805001d0a29107142503080c504085805401450800710a00d42c0359020b010401c8425419035a503107400030036140d900313540e9400e80d800042c01e49a1440c035038095080c0c0400e060301440c007644000c1c7c40011409141642c0350b29100845188111401000d003030ba11007519040801d8000d41e40180182080159030394500b400300405c4460030181060100d0040c400c2141103080d039240d1a0789523405131482d0302100c0780204100c406200d5034500c99400600032003070040c4ca0319242d003e00152842030f120b034160a0341100003699100c2001c035005045601c200010b010900c4a074005c50782c0e1541d240 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 318138111 1250 318136861 318136877
    0x711010c0501020f0703170603072301020c04090c2409090b060c010914010c033309050c09040e03070f060f1401030602131e05010e0604050d15050a0b130507 69
    0x10404d00d190f9020200035000501255400104900390350056904460110000e008003880c059141c82f00e40701130044443d41d60900f184000d1180d00034800c24050400c0100200309601c0e161900d03e1140c07285024508150411003492060700f052400890403800c01501c0c0e07480303818500030f0140c2c040d024010016402100c00e1203006600303102401207070703190f5100d0140f200725080185c10031421a1445124401090f0038081e400402500352603c42080140c150442c00440c8880b034149040407803958031020b01747d844c000403c801200400007514036840101d400307101c80e885011003d0b5030703401400c8000d0000c0300318145130710024103142d12240d44665a5000800d5200c605a4010600c1200760320a880042c2c00180c1040c2101030f0100c404007a00d000d180d82c000d20280d0000703840c1e00401902810b03042c0105030908500301e640b2081600c00908001344004010021803400c83c070005d11500c50500360505000c0817070519040c0d4040d103402c0310f10241400b95064014120540503000c05000c00c01440f80e92 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 318139361 1250 318138111 318138127
    0x7090e0c1602190303020606010201183207150519120e0a0f02030d020d0219210215010806060f1302040506030c032509060509040605130b01090b0711010c050102 71
    0x180f1503424501c0d244060307124119281d0300f0083e040900042c085811a40340060389841043c04285590340507400000700711101e407980c0700b2110a000c2400d001030802000300300c0988511000079000c802e48010f85c84030446000c00c2803090380c0501404040b160098981800c14440c10b00c2540305071407094204001194044100c070fa800d00b840400d04041d92a03118005021081d414100050305440322244001d1082020b1824001c2d11814001c0040b40002e010231044030034060480e04800c0e00c44a03041d40300c4101c40e46030720080e40d102c3d2030380030908105000d8070001071a4000410805c4c89030350040d020b0a58a203524040180464a07000710601c0243d0034040070469032202406588a0061407040e02e40d0b90400fa0661014181d0b0340c1105035182419084074906268030070740000c100d0345a41000703619001482c000402821107504415001003409042c54203801c640d40080e0560340080c1ca4581515842d03503a52280307442201c0d40542594010490300c440c2d54441c0a081d01d00c5409a00010306103014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 318140611 1250 318139361 318139369
    0x30601020a0b09010212010e01030c1e030203060717071e0c0618140601090b031b0f03060c1803010209100507031701180f020702130c020f03120f07090e0c1602 70
    0x100f5205003415030f40c049501030400d00f003000b159002d45400101e03c9220341c035681d903581010b9414041e52401c5038010055100d021208103200b409550f00805441061815000040482d980c8900c44022050041d002c10340e01406411100c0403515441a482c040307080c2c0001c141c541c014480720848000b030740e441250108404201d079201c1d1091007a2140b40000d10380c4480e051030300406800c140e00307039480c081402c20142d400196112061036207244030b00d00c900005001540c00e41d0344d40c4a003500b5000310b900f00900c0800d4500102000c098460000e40c402039004280b50803401103962417500600c0c4805103200c45c90040c0d0207041003e21925002d02c00b00768510501d401c07039200b03a126841107500c1a02905c1c2d000076030701a140501c80c01010031400c2c003206400162604100c00440c028071943d50b4a46500980300b4031244003c401141c04880e44d408201d07032501814503040f207c001003051907101040e60701e031140c1c82d000304481c0282c036042d1546e102d241c1c5c55031345944001d0f9802c01640c82005140c0050311 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 318141861 1250 318140611 318140633
    0x1180b0a022a0111062208270310060b030a1a03100e010b040203150409022709010e061b090d06092103060b07081b01020403140c0a0b040b030601020a 66
    0x9110204402000b905030001d84800041544041c00340c004a00b000210744004250403655285107241400140c01810007145070f01c10120001c44050301c0e0f002c0610f41d9502c1d0321100e0b100c00d50540c00c88a4211800009100b1900f182c0204c0c600310008001140700841960480640096040801d1112585410019140c9070441110440c415110701842d243c1c988284100d4495440c2510158514074024041c0c1e0481c01094030424499a51074201e0f106645581c91408213081107807030034031004403071070041544140d070403202c00d0002d600385418040400b03400324003d4007a211001070001c50300351462a0081c20307040100b21a030002d45445240707001c26402e01912591034040e08000110040300e001035040042004129024542400b10812221080c20122981103801008058543c0101c0c00044010098902c1710f540350342c00441c0110601c8001d0704002011096a01105c00c584e102409000c10040c00b80300340e01407004103000400480d0f102d0002140d021205105540d021070722076446103001e10b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 318143111 1250 318141861 318141913
    0xf2212170c07030506010f091125050118051c050a0804050f0d090e06090603030f0a050403080d0c0221030126060901050a060605090312091516060b01180b0a02 70
    0x2605c660b00403c4440414014a0013510744801d003400300380c0b03940c1903078a66485a001c14425055030b4044040c00d03240443d141c408003a038080020301c00c001402200d222281c030007603015980342c010442030410070404a480c3c00401ca00e44d880715801c0c014441070036107440f00010001d035282d0196007421103030b0680500a4184100c44c03a220034014506000510403034070402010386001d1074007501400034580d400002d4a0404e030442d12100d0b9070701c1d104503048980303004c1d60780300070304211000c1034142c0d0503000da41180515841a6084402c03402580c19000701c2c000440800d81704c5e4502c100014000115501005a50009440c805074580780a07842e402d0301d051400c441c01c68241c1d40d5981400394043e014000c42c0d0043c05545001802e0100b4040040c1d2910b50344800c101d01794400141c01510b40d281d401486046462140d049a20b6904c02c806074083d10400410455015280c04000740c1e441d8040c00d04070542e4000341811141d8617081000080403981b040c80c405083d80715081c50110560744a40b4010418 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 318144361 1250 318143111 318143113
    0x60703050711010e10150504020408030d0b0a0e06130912022802062a0d0201020d0b0d080d0902010e0a17150702150406110f2212170c070305 62
    0x50310382001c0c002c010212414840b0800d07410500c12009620300040e41070700c0d104021038001030300c0b5003082840d0b8040007140e2006401a0001c0f8002400c0c1070048040c2c40264410001031050000090800c00744000c02c0c05003030024100040440e1141c05c0c0b1a1481d82d61b03446d070920002d015115601d800407000071450712103005a10008021958890b10810741c442c907071702d0500c0300d41142c8850780050014018808101704c02030124418802c49401d008185600c0c298420580f840b04144920081c040d50105001c0c0044a0600308121500d082030b91181c110243c100b0406402c01d082001c2c0000a4040340a00780d04100a000404103195143d0001000414007034007030002c440d0701c640d61141003e8040300039101c040d0701c00741004055074000c9415819a82c083c401c03100031303a42d075181010041c09507500d040f82d00c44001c0341380700c9107008460041c00d8150a841c02100411074801030003078540b5041c0190b104698501c440180016880300c04059000825400b0307900301842078546602d000010703407060b946 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 318145611 1250 318144361 318144371
    0x3070b0c0304060b040e0d0e1f08010e160c0201031e050108010b0414070804120909110408101509150909050109030f09030209060105071a0f07020f0304031121060703 73
    0x40009030f118030200100c050714107011008285003142c0d100d140c0303d8529014045041480d0069903108058018411058150031142c9c5401010081c42403030b0134004da003043d07c103000229074040c441203090b5803243d001d580c614a164505c0e50046015004030b0441e6002e00034000d1607009500c4072070040b01d01805000c0000107110699800308019103040c0141200303a0311030f190520220650008030b40d980315800003000d90307880d0b81c0180111004052540b1040003e85004801d900c209c841e04c0c010300448949200701c64460800301d86800c12155207400c03d40c05150b404104204407103180d044649501d48441c06442c4840d5101382084c142e4184290440d202d0b5940c50503002056045011034210700381c2032604055850640c0c2c0843d0380020090f02560500c1800700b0b080003040303400b12400ca81420403006006032805c0801030040c00032070580342da801601541c0008000424000107850440343c1046444114a00d844240b1000903c1545111890300d034904210015020070000c180c00b4220581d8000f40b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 318146861 1250 318145611 318145613
    0x120213061218110405060a0e1f15090303030b0d0c080a0303150b0702010806041b21020c03030f04030903080315041112180c18100e13030507020303070b0c0304 70
    0x100321070b21418402464201d600e840c030042140c00001c00756581064400055507101c400004403491500d602c03040319910b046c2c04001165040400c0c000c1a0040c643d002d10a00c1d844848075400c0300c0b4400c8007040056180c42040010038401e0304095076011018001009000c0d45440350501c0441d6600036078083d80c07190400e80700301989441440f208414505119000b1420100c03a025544034010010b0b04010030140800e03d00e542daa071154040307005802000c1074140e010300014100903500801c86005d1100d000145000c14031034022a110038448038003841c510350319a4440f110644014000b901000510180800091340d80c0c0b000718000c03070f01c5840203490002c212007000250f07202204032040e260b40a009070010903003003c00c002e422080c4900c181624041900b0150710b00b03100e03000c1d640d502c0030044185c1103502c0601c0350300343d0003050300c40e0883d1085074440714880d2102c1e070190342c40b0500c503821900340f0012a1181c0081d164103807004051702d20305911500ea40c1d41c0280252518460b400b80042808 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 318148111 1250 318146861 318146897
    0x9061905060a230f0d050712240509090c04091103070303020610090b13020703030905062e06020c060a0210060b0309010e06070806150c010e1c0305010807050112021306 74
    0x44282c3c580d15565150100300102d81110703010f40301c034182d10580c1317038408580543e000e000d00c44850120941c0c00c100d400c04000e40495101440c8820780031210318000082031905006c3e11041c4154003800050400010b120240002000514800d4510070310792500005d05603014000540254081c0d80140040e040990081824003440e50043c5a0245451400b04042c1c8820280c440c414400000050301c0304e2081c01e094000d4000d9100041480c0a81c80410400380380410810802005074444041030350100c00c40300008404e280a403c0150b44140200c8000e4a003400050401010900c1580c06c054503c901c0c54040e01c210760004d8581d841c001c82046440c150912520300012002030040c081403d0142c1c0151060f0005002039000303070301c00100e071499551303064120b40c0181035002c002c0150b600d0b00f41c2d03010344640303003207080c000b0031000102c10400191203400b031503042c0c800314009050000d150000640300c42091420008880b0780a10291500581400001008003116211409040c1482c1e1200d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 318149361 1250 318148111 318148157
    0x50c030d061d0402031c180308030108070603021c0b0111030705010501030b0f24061e0a09081b0f010306030609050a15020a050304110105071b08060a05010509061905060a 75
    0x2c8a00c0b00c1507008020250398005030000e05c1d00b0341d40709010101001b9203011100109903964801001250203000800c101c09000114100d5001009580c1e0054945504805034842c909802c3c2c080c1070090280c2501a0007a4480f801c02c03501410401010800d02c1c0a50341940c0200e501903d890b55900010014803e4403549142d1106120790703085406e01e800074000386d0607048c40c01e420003104401c090040300342d1a003408542254207050341c54903d0f100003100c3c07060b050740417028450004070312500c0000c00c03802c00250b00c0e01e0110090840c001c09260601400700c100a0044050304058544e100080440c030b0074452000d0641c0107002401001e4210300308000d03a520494a040f0301d40b4030412201005503880340c1a250031a46c404c00702030b074400c034420049515000d0890040e000401100700c01d48190035401401046a207032030181c030600d590300c88611080380c000b4030235140c0025450001500c686401ca40e85500b40f00c0004580c144c582d150f2012503035540049011101003411817500421680b002840 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 318150611 1250 318149361 318149399
    0x60e01060e0603030a08040302030c030c07090e0706020a06020a0c080d0902040b1e061e03010f0f050f2107091d010e06150d080909100302120c1f050c030d06 69
    0x524030141041e40119991744a043d41600803c8250400b042c20507100b8000c90300c4281c8010112070719000845072440c1c031500d030b901c00c0300209850000e60909200011a14508444543d0060601980c0a851384000381d40031001c007400300101c2d1900040020341c0e00c4040c2040c00f507081e81c0060501050303c10300040f540d10901c103903c50050950500d0f0782c60440399841c4244503040d103003561100251581940f000008520707000302c0f0400400041102011845000300312502244030b11040c03a0381d071040c006801046811b05401c03110060510f03200b80c904070603101c0071a855004413080303c2d0b603d102030301c115041e0001c21035000300b65855540a0600074081c0b070703080d802c0c200080c103e141003443c0f040c828000c151003914010b240c40844001072000344c0056843c0d00c0009400c00100303107070800c2c4164071901c890201300e208030706041650000c00d100040d403100c0d410025040d6042c080341c070502c941108007003401450400104004c41001a1014000f40130f00f8a07a0400c046511400c1c1031400c21413054a02c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 318151861 1250 318150611 318150629
    0xb04050609010603021e032a12070503061801060815040501140405130615030b010e15060c070b13170a030c1101030b0d03021f0915020f070b0103060e0106 68
    0x209208059468140d940e0440d509400d00590740e0f00ca8548201e02c0641000b0f102100401c08000c00018400703e0300004600d000400401401d090004203070001806035403010807001c0030305c000280d0080d01444c015034010320014443d40c54104500d41140c601c00f0240c20101c0020031200501c0003192100d0b001d4000c007003007190280000d40c1400410503e980000c01c40270301c1680c071200800c0034616810440264640c0142050000046a804020510b8194442218105095000058440d02c1c3e1848a8003604410f41d020f03c0c400a180d0411070550020791340740c0024010f481c00043c940094100a28a0010040f000d402c02c514016220030020072160300e0540c0c940104006d00006a8805084020303140d215800d04000144080100c4c0284590003510b5004001d01406005040d000512441c4050271189050142c0554800304001e403070340704c1c60040000b802001c01c80a860601d80103044250011aa480e041030411b484a0303146c10000ea200361303101e568444a00c07001c25400c0c09440302070a00f40d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 318153111 1250 318151861 318151871
    0x10e01020303150d0503070b04120318150f18060b0a0f0905100e0c07110109120204020304080c06070504060905090717040507030501020f0406030633050706090f02040b04 75
    0x100080e4403071000820240c80c400781d40740900d809540300a554162241c00030300312034075600c161400340030740f0406440554000240c580c050003510720038064102020413030040c3c82e0f1001000d903202d280102d2a400c41004058407a2070351203c02c40c841c031410844030781900c604c0ca0b04000b1420f004045520041c003907070003022600030074004800010340100c00c8818814002509590b660009050300c0036640041ca1015111420702030101039040c040c045681c02104076038048099000191340d200342510844a281c907140800201614103a4059540b2502554070607180451b0140c0f86410040d00f01e651101081e0042810b20481c1c0c3d01682c0302001d410705960f050b0860030100c4000d002040c0c01184003d440200100250400400f4805217005581c801e00a41d210030000201d45800d800500550001038602000001c1c2c10121aa18600c10311003420861940d00040085112400700c0030000d1060203000c00145000070b4851042040f43d81c0074049810032482035104000c1500d0b0405183c5100e10b081c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 318154361 1250 318153111 318153137
    0x611182107050d031b03030c03150312050703030906060303081b3405011109330a1106010e010e011403070618031b03020f0904051903120f06050102060601 68
    0x1c2200503036400f1100da43c2400e410346421210850303004282a00043d044a981c41010b40541000d015007100f80c80510050072503030322005200c003081c4000703007800020004002c4103d000d04014003030b250081c03030042000f0781203844260540d1019441100046c0b1060104400f154041c8240e1002c60130b0902078900d466001c00641c010715803042404102901c3d020b00000103402c400c840b038440990300070021700c00070602029002841d008410b810740141e2840c8000c0c0e03005500401250b40208490459054088603202c521100d40c2045c0c00e401c050005070300c1d1a00010100b0440c0d5402801c007103031207100960400010190a90040e0300042061003681110342003654042281001d5882d01d14001003900504440d95056030f01c2c41d480542031a0042c03a142c414404c04080341c00c142d82c02a540501c0c4881c8144c244041e680d0211400b070302581003d48014905444039404007070702c90003480c7c20781e0010030780d01545045806841a208046940700d608100c2944c05101c1603a202400342860f4100784c1e00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 318155611 1250 318154361 318154363
    0x1207050f01110714060c0607020109021f050304060504020d0b040b0a0b0a0321090f03051b090105061b1c030506040b010e01120b0307150f1407020a030b0406111821 72
    0x500841c0102d02c400400c1c80c641e91035030f0040d213003d403101b0001c5800d00d08000390003034002c022120090303001e40108580101a40642c1034003040d448255601e991a5645e60344540c0000c20b8040c2003282c0c000c40f0012918040b41c001100a030289008103e099424100780c43c400d41255140740d0441d0217240c0b041410408507003101905901c41210300c4108007044003401048940d408140c019100882800c0004801c1c80000200c0703489898600003030100780401c000412038070031024802c0319400f80c01007114042805031410f200015002400485401000c417410700010441103000c5400000c1d551004c0005900d400e000e5119006800c1c24940460006d81000900002424098440f141c1d241c40750303041651420090708000b0120b01110080b140103101c4010140d0600509401c00281c000c100ca03001220300004640d42643d000f0301800055240d6510300c800c04030000c0c0246e900c65582c0030209042d19202d0000e044214100303c8403180b4130007800400140c044446c00d01b0070400340180490b045104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 318156861 1250 318155611 318155623
    0x12120f0112020f031e030403020a090219050d0b0d1a060d1203090c080a0b0405071505072915030d1e0c0f15020d0b100c030302030a0b1207050f0111 65
    0x20301074071021021031144000c13a10303001c101c0111050304100d40c05880f10401000c000351050700c0c821500207802d42c0e543c6005105074050ba05425802c180902034003100e10b409800182524140c1e140d0200740d641080c000103141c101400019a040c2c085244100c0011292144807a0b12160480301038801708400c0d02c410400300005005030301411365890018041c0600440e0820040102000700c400038400d501c3d1861004900341c1d4115032034440c011005ca60501e0420f1409060001507403024281151a00e030b0f403403440900e101c01c2c5034a201c814404107025282c400524480c0340784604001e0f940c1d0004090510b0a026030401c0307002c00242910b14001c0e14050b4000081c2e50071a840c0c0fa265051213410203500041c0720300b500902c42d40d1000341400340703d0b40c1600503040f001c80e040c1c41000880409824890508044413501d400a40c0502e01900064043c2c0d0185070002c9440c50001180000d441c0440d02c944101c070340001866000c40c100b081a441c04801e10764070400280303400c8044401250000c0d42d605 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 318158111 1250 318156861 318156863
    0x5071e0804030509150c0a120908120a200715030b1302070c080a0c030501110408060a0507180305010609051305030a03020f120a09050706030c091802040812120f0112 73
    0x343c002604190b070394640340500292600c83c0702a80d942d4208800c90341e51807901b06002c8a00e02c200c0359003c4043c5008140020488081401401400d410b1074200c06d440d6021240e400180404413080240f10010051a11200394000d0010310005090819200c0c0031401c1c03249150405040c403070002d100d611951004281c00c6407015001d40c54407110f1030306817000340b804d802c0240d4508c40c0c040c40d107040c0602c0142d401c04890140c0020460455615440c01040c801c60282c006e440e4000804956032440a034800f07984400c840c908900504c0021001c01e40c5a1965402654540e4489405101010540c841c50303410000ca0400034011080a03540d07103869001e00704100041c1a404504000c0a0002e4400c41d100680c021450b1645880d1a0142c00018002c0c41c4c421344d2b20388144a408521140244200701400c1e00d9910351956040ca01541e00c0140743c44d4035000c2007030076000d01002131400320400c501403001c0000140c143e26025565000c4c4003080c0d0040554200940d044010000c403440762401c0e114107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 318159361 1250 318158111 318158117
    0x18060f050c0f070f06110d050106050406050a08090c090705041a0301030c0e13020d060911030c010801091104030c030507170a031202070204021603050301080d11060705070507081005071e080403 85
    0x240102c0c10644c091001201014141e50700300031003c04c041c10081c00401c0e100c1601c807001c10550341c94503400c0380d10f030059004240204600700320a1605500031220540c0c03100302d000486103a006450003042101000f5500c7c240403a401003418090715503d21a6501e400020030360a0341158034517150b12481840c14880d400404500c82d01142c40d10500811000040e60040d15850b5920840d29203030000341002942662054441c0c2c040700700713619010800c0001c03a0016501d003032069007021240342c0146011410f00301011000c2000000103904000108002d6000d00c011308080c500c6c254624296215015005401c0c1e0004450000002d41060b81401545620080140c407101030f0700c0880c00074440d2104140d4503140040c0351104056011300154103036081c05d4180d8101c60140c000c1036030b80c1c0030f9090b03106125030405400035451521940c09008224003031411280320301e54403900319040200d04401d4801850f00c50041003819500000b07030044031b540c003508155100d013007000300810b4108050802010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 318160611 1250 318159361 318159367
    0x50108040816030c03080601030b0d080f04210c050a08030409180f20010e030604150b0d1208180309131509020d0e0f0604060203070c0618060f050c0f 66
    0x18494914182c0d00c4410702640002c200001904010300080010780040707001561000019a15500c0b901400f16031040c0500a4140044940d0794625103030441740740c0e006040c009000c0001e60f04a24004045104c01400703000080c00b0090a09507800119500914000e45120000704100030001044404403043c1810005180c3c805000c420440100c85101620021003940301c141803141c01d00103d90808540c0021810300600c1000644201c04071400d01e03a810f0f04000d001601280707000300c0d600c0030400d00c64800a055001b46000505010071008181c441801c000d00f403100603900030304a03030340040208440e903a05449044407995a4030981c440c1d140a041340300e0022150358070b0364105246040948a00743c0c0001d403188586030003500074560240c50241001401c0e24041008104450381d444600041c0100b40d172162500c0303002e9803000c0c041c07200300311000d404500861090b02c92210fa500c038080ca00703900900d103420000c041d10342445a40745400d1a00c02030043c03a04546d0f0840d5004107a0481c10741e1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 318161861 1250 318160611 318160613
    0x806040b0301021603050418180b070323071106060102070e09010b04180302060106020109330f1e14060d0809040203100602100b012307080408070515070305040b1605100f06050d0c05010804 83
    0x80c10724080d0240400b84002d1400d1071510003703040520800741c5656030140540921069640e540055850f82d0150300126024050500303900d40300da0380040c110001181344606c40020508513440f407c80c4000c07480c030b0712041c40b08141d8184120f07401403945200a102041064031004103240140040c0088145441c20521403426804444e019100448a0403c88070f0031180004018111003102c400d840300c1d212562500880044c85a0118024851944100c0d82d640c0414403496541004003560480c2d01405486842d540314001544210ba400b200215918501034000e841d10030994442c2468508103183c00f20701d43d03401140422083c880740049000034090b05a689802c3c85803150281c40c13a40c00040200d6003c6002506c0b004070360007981c0400e001200981c0c082d135940125034000f030005008200800c14140040c0107004550402445480c4140065584034070300f4080800f960320f074684461000c072490280340709903c01484103484240c010202a603907035070720201d140a190305014084000c0740c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 318163111 1250 318161861 318161867
    0x910020a0b061309061a1203040f03030503070c080c2404120f051216080610021504020406150c110f010e0405070201140c030f01060e010806040b0301021603050418180b07 75
    0x41c0c0c4a83d0014010020403a0020b046e001b8610b07101c98007801806854250134120500004031811115491441d1010500f5503800712115403015100801300440c0c04c2c000710100380030310000e0059038542001000f0300405060640c05240d0f000300e4a1f41c59007101002c1001007622100c07450441c2c019868403030f000400501d010303a507501800c03d018041c441d8540c104520800d10040e41e94614006844043c1a40d8851041200c0000b6406d40f04005801551155607c0c80c4048400e1360007920040001c688252618440f2010403000007600001601c400741642c28403041005900c401c4400340c4005805101560003e002144045e0a6601a035680c00c001200c44d8403e5001221a44081c0540e0406041c05400041180c00584144029401704800040c440f40100c0c1401803000b41a1110160307951281c1c1080000c215410540360995001c102c251840e2840c0c01013020098841e40f200c9489504060140420001940070003007028032b028110405100d200d41003e0079a603000402490f00d0b40ca0074011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 318164361 1250 318163111 318163121
    0x608040818031212090609280c0e0403020309040f0b100804080f03010303020a060b0118211b0305011109030a15060801050c07150606050a03200307050910020a0b0613 73
    0x8100402001c101004e06508031020540540c4030300c822075802d52588880180c031a0f80d40460f00602003030425400c008050904800d80203507004050054003070b590394076040a420030844007100180c10004100405150a1061040c01c0c0d50003032003000406103420220b03014a078aa403000080c040102d0001e001c0100c454120f4005039044801c0540781d59583c81c0c040d41d5002c440804540041c203265444030725510481041c8200e2070500801e5034601c0c50524010801d0584a400364041d488100c1e03240081a05200010804551060307545841c0c2d1440c01d00508440400916903e0224100310060042d81c00180e18140c15400c1001c03420729515100c07129000784619481991a0350805041140d11030b4000084c0107a50301501c11030640c1d6407c0c000352000c68006004030400300300c007480400c0800f442580000e01c000800030380c401990b1155501400c0940003114507070001000054a1055410025140400c08003140011710700e204542d5a1701144d60320040c03055002ea0401050f9000c50f000d15040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 318165467 1106 318164361 318164383
    0x203060a06050702061204031106010807050307081b2205070509040e030309150604060f030f020102011b054003020f0303120a0b21011401060804081803 67
    0x10b01b1420803405001502001543c901c030050808003000b601340038005030b40040c0200d6250008040c5440707880d40080c4c2440d081144a042001000081066070820407620040c10851040c80a004c24155100400318582007070148030200350007600074100000305541c14000c150343c201d4059541d100c15120000d02d90321801111907820000c0400b1a04000020320105100e640c072008010307284890f0304203552041e9114003440856809105544035401c140141c1c3c0c140001303484010348a401400304130340d00c041c49000018082c550314011890386128a944050b035580e0150708800420703100d070100f00d009000d070705001f00440c500002170f44e03501c550406841c1e00603a1480c58010180c003204440743d420a0301045400d082e002c10f0010146c0504030a000024440791902c500842c02d00c069100000b800100c009200c042101c00c0100d824142c465207140034140b10b1100442d1070f212506d48 = true := by decide +kernel

theorem cover : BRFrame.Cov 317985611 318165467 := by
  have h0 := BRFrame.cov_init 317985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 317985611 ≤ n) (h2 : n < 318165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
