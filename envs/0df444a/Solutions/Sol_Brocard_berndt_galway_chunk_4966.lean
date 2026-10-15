-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4966
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:18:43.963416+00:00
-- url     : https://prove2.me/submissions/638c961a-09f2-4781-b599-9575ffef6f89

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 892985611 ≤ n < 893165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 892986861 1250 892985611 892985627
    0xa140c09070503150f01020c04020c01110a0f17010f1e0503030f0c0105010b0a140a0908010c11150f150f042a1403060603130501050f0618060907050a 66
    0x1201030034100203410003420090043d40100c4240703050103844030f500a01441c1c00e0964190302c1805900900c08139009901b004001d507c9503a10300600e658a0b007014112410b0038025090183c05900c80c01c10340e003e07090000d441a00500d25150412555400602c140c1400e04200416500141035000c84142c03e00b02001e19040260842a0305110215605150400b200c000300f0140002d2030091009990381c2c3c0304020b241c000c1c0c0d9842d102040f0700000d441311001811024181c02d8506203001c1032025070340e440513421900c496568800007520001e09003019041000804844024044120340c6403804201c0c00e00c42c0c000285c00000c00d10208804803560f41e0b02c400c00a0440c0703900400c00c024205540040003081c0d02018510380c012075042806940c054051444c0911000300b0016440c41c66648000b00401030b40001c041840d0701c8a01d038a0500800c90900c0780c0743c41065079015540e2182091020080e260585d11110510914006c081041e00d454031149590004a282415a103c13800303514107440043c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 892988111 1250 892986861 892986883
    0x60e150127020f090402070c2112180509070504050924031f05040c08031801020f0d1b290601080c0702030c13110a090906050a080a14 59
    0x18a4600218841118000501507090450141600e40c0c4030340441d88168000c1c940d9001c00403d040c0003081c0d86090580050014130700c5089140320460f103440307000795000300c0d82035284072100900d0400030801c4410703624ae90342c41c0c01c41d080c05940742000403213100742601c150140b94040c031340c40300100d000d4901601c00d45c0d0180000800d0f1100a1405840715680c400d60110707041c0348002d418075015005c0c20007007115560890040a90242401c1203054a005880c01600485881c0f1102c40005401d81040c009400d0300da154925804c5d82e2040e2400091038104002001c414641140b0034540b540c980000c0780003030018100c182c0c4c0c48c80081508042c01c484404510b0036001c00001540505210814088280b041d0000d0301c0b102c8542d05c030781c01c410069008060009416504c1000345400078a4092000740b10701071030580c08601480d0fa807000d1065500013441d01808208400e200340305030712413801844040c11003075604110a07031900a2081c1d9030503140c0009862611000d40d04504200117010203143c203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 892989361 1250 892988111 892988143
    0x5100305030702012703110f010801030213092102060a111611040906090b091603080a081504240b03101e05030d0e041d061603020409050c04030b01080102090607060e 73
    0x101e540c2d00300801a4800e94088510806807a234850002d90b02079800603050b240c01600d1601c5e1a10125010001000c0808007a1410469504108846501300210b41b08804030356020700b1244c185070b4442c00985c1e0401385c290300403610034000c54148216a003012001282c206400b080c0d18a070880124000304039449010741303d14100a400340a01021400700c5029042c0d0318100c0350140c007c0055074148041e40d020080612100b0800c4210041c03040a00a410015078044c2b0441c140040380054100c42010805160722540030402544c03518070510702400500a13030030390901e1032030444080b003415046409401c1400300c4107090000c6040700702040c2006080c000c1c08640b2219126140603021b004001c01c0f20b0f118605041d120f55540001d00c035840309c220b442c00024142601c071000e100c003105040300c1d0780b10105582440001031107034190003214020420300c10360a42c1c441c20360800761f00ca008141c10100783d9a00410100780c0d00d0700c9482c02c8a803400d8100700300250440c0510001d9061407617501014505c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 892990611 1250 892989361 892989437
    0xa030209182818081c0e0106080d08090a0b0c070803010f090506060702100e04021c2403030c020904020a1502010c021b0901121e0b04060510030503070201 68
    0x14403900b0080d0405a520501c540c1203010241046840558500084400d2a06004880a00007912020180c190482001c541c26220321802002500301c030704a80c1030b404d040c0c1d102d1500300004602030245160074029442c2c08a5185000604981e851010f5240249000f000c0e4000807407450743d440951f080b0340da0200e90559a56526100e543e011100c50203201c804500c5c210218000d440c0207007c13240e0190f401f400340080e00045500645440c07010400c900e410640801615180404a20711805185410440054101000090700101d210165900150004908024800309422290f2005040d81c100d51030a05a0340780d102160b80c94115510089a0043e40340c103c0b80e0480d01034201d241c15030f010790f0840f001100038a0b04420341030f14580007240c1000c50f100c018449248030450041c8100e008048014100d510814000c0704182c0b0759000341e820b01c10310028070007040082e0158641150302d1940e0314851608580394592079100d072440003410702021510181a0b03414124054145418100302e00c29 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 892991861 1250 892990611 892990621
    0x31602070515030702070e042f060d051501080f04080903030d0606020d080709180902030c121b061201050d030c1b03020306010e0124020a020a09140901090201050a03020918 76
    0xd4982c205130741041c05809404800b041300200070703d8144c490768003c0303841804201c84a104107074080f0703e062042140801401e4080903620352500409100d4200c610004039403034007401007603101103072035050741c1040110030510090340e5040b03080f41c2c2c11a802c000000e5440040740002442c501c41e012282880a007421000039206402144209040290351034000c2290745a12003240e0b1142280112000810746040c1a07804c10900d80c08489403074405021074030345851344c4000952140d05446005282d92102004409410090f000901008010340d402820000f056414103040c610500481d4001d0446558600505214821400c0d400750801c0055403480c4401051003c885001e0005900a10900000041c01242d0042d024101c80c0c41301c04000320010002440e00840305010003090442c03003000684000341e5500900f2400408090100013a03c801303000910b0034480c0c00900f4205141d160070b441801503600a8120303229222a0311740169074011920020f03c9503aa01d0100c150000e4414003004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 892993111 1250 892991861 892991899
    0x2d110a0320030d060b031603090b0a0b030a0819020706090501080f06060d0603050f19200a0806150114070b0c1c110307080f01030302030403060923070f05150316020705 74
    0x180211400d18070395204d900302040070723415245c000c1c1c002003a507001d100018017406a5580400c41e4920000c05440844205455481aa41203200d034001100000001001c8003501008480d0040080e402c080c0005454400003030840c00005003548074003030851000446659800b4129400140d82c1030f020443c040d281c0c00c15642c2d650194104645500c504c100040b031058140120407076082d40b2070800c110103003140b1003940311801e00d000d11076002111a44089445c1c48180405403051020364054403e0402c008001080d2140e4000c0740034509408001c5036001c642c2076200340b503106480aa040f03946070403c060512a0790306401c4880401841c0844210b0350b811004011805541540e8814030706844140e6050f880003000c1c070008000d64020082000050b55039008400e19500800d480e0b400307141080d080d004200c2282040a055070800c4000b0700c0b64410301d10041c1c2c090311007030324040c50f0711070b4252000701544000360260310b00403441b400e001601442000480050030014000c142c040e00ca040c0c400b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 892994361 1250 892993111 892993117
    0x60d0f050f0111090d1101030e030714120705030a0807050405060d060e01080606010807030b03030712020303190605100509030f160e010909110904032d110a0320030d060b 75
    0x3400954244031080f40004a0b81094802510f001000322000290681d1510501c0c4440c2ca1164180344d02e038218441c8940c003e10181c032485008100c0d0b422105101c203a50350a044250145281d1042e06000e0000817800010036103003001e8160518801e540c84260b01625180190b501c500d52250000414900200081e00044116020414040e801c2c1c0d880e090f5061715041c04540036400280b9080c00030701510710039007000d03000703505c0039040d6071a0580e07075220420511000d0301c1c0c150140c0e1001083c00702c0180c3c044408850b130140441c0800006003807500140d00c111140440d01c081200c0801d0021a41e503050110311900c4007084119108101c85e000c121a01100a00c640790f060300300440000380036000c501424180541c40003192080300a50340c200522684080c005804101d4002c820646c201d0b10342d448800d8029441d822344800440c92a80100b07035108101404000341c2100b09000000b0f600b08810051010018403210008503600558516500442c406808080c4c144500007500700b00050007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 892995611 1250 892994361 892994383
    0xa082a010204080c0a08011406091f031406070207080d1101110d1d0102030603030a1d0a0620120d0507022b03140f0a0c0509041505030105070f0c0b060d0f05 69
    0x45013031074982d82c8000c01e00308e90008104070403800440d00010702c246803441c2d0155108e20b51845088440280405090504010f03820840b80746140c46140e01c03621004105107644054240f00404901d414001000d413200383c1405210144660340b111100d070045c0c09e4022400480036005c04a0700c904100c07000c20090092031340b9031710110005603c1c0722456041070003140d03c02c01006d0011881d0150114007180c02c800204d120601c82c4444100d881102e68806901c080103140030750b600b2981c4038114080910a144075030811101d0f6002644144075540320805448031702c03450510004155481740740603410042d0f02940c0c4614010992500904858142e5800d40701c1c01180e0b03000c002461606078150172040050300d2040040c03507001c1c0050341c0b410b02c80d0004a40e40740145000da003410010400b00c1c0035512859a01048500c140d0070a0080b41001d120315948000700f0b00e03100741c04e03100144001d080c00900c610701521004011001800b0740d1141d005181e03a955105c100f2050200d001c0c01c6c0b094030f404440c05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 892996861 1250 892995611 892995619
    0xc13090b0f040c0b030c0702090702010902010311041202060901051209160e07020307170c0a060f050c16030e0a031403030708150102031206130e03030411030a082a010204080c 77
    0x10407001c07410720503010700c03030381d4072541040340181403641d074100b980c100801e4200d03000380400c4030400603198201c80500645290700080b80d4104c6901c000b50a4410714407a11158043c180310070071030300c4640c1010425194042c5d6100307940c2d02003a0300480703280c4a010840c42156000a00340020345200140079242512500c16000d0301079101c00990040b40c3d01982c6c070500591060100b140403800d070b00301d6001e1280780b0280e014a40f8109815050800800010030b40b5495618402140d60400500030a50700c086a8080f5a09d489056600c07450302003030340b407805402c2104115201c0c42c15201c2e901d01c0703030245400c13402016029001140d6070390380b035000701ca9040014801c48042100d0b0074030034002d00b0f4401d405030051401c0c401110400341000c030005241c0350f803004d90004820813625086c030a110890500d03402451b545c1c0b819060012406100420450095211b141200c0129031480251810041c0c4d140d48040b0031140e44064400c005a0b4100b4044594400500003c0103000020b100d44144000d903 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 892998111 1250 892996861 892996883
    0x30606030f0318281403190b060102161226030718081002030402010216050f041e2f0304030e0907031b02160e040c1a0c2a04020c07090e0c1309 63
    0x30086c1925800d00c401404289002444510009220003115550140d010300c1129511580e03c840744001c0000d80e03012995009034160b089040c045464040b110180d001c2a50003408040001d031030400b403000a215004119200b45800d165805d43d0124070300409040c1d0499a0101550401c40025842a2403c03400340c801c0c036200c110b00345406000e00d007c4401c01011420b44038845410320018000c004940c090107010404046022a40361160350354801c01140003002c0355400e0722000d009192440c060111540c0107100704400a50301c02400910141e0640d20020907860b00001900944100e01400c0b40e141d404220301035030107a0000d0043d11407200170b40c000c00300d03590358bd1800c00846002d580180c6001503a410520024010024044603184420843ca02d8000c0000b071b8030b410706c01c28840c14466060a00c1a80380b0881c0105036582d44c1c0d040131981140b4101c07806403215035800c800c0c865400c68030f031034a4039804111030511085010074000782000f01180d00d1707500c02c0c030014840d005003207410340c11071 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 892999361 1250 892998111 892998149
    0x40b2206180e040506010504180f2306010f0513023a020f070206031f08030d140606071b170a0606060305070503130c030818030606030f031828 63
    0xd1001c42d40a59045000f6143d10b908140620001e08034074008a00b680d010f0740200e4002544030704212480a0241e10142e400380c1c2d10f4883c0d004060140240058544d0041c0018040750000d00d2064040384c204661210030048085c00c100701034001c101241343c0c0100398200940720903150480c0b40240000c1d01c0c12410030750303e903000100c04a010700b88040b400c00c1700034001e000050406400564102c07a0656000b07020307110000d13001c1c500400f19003111010350000b0903075201d0020140541020340c00303050410300840c0340c0f04c004100180200c0c0c001401711b48034400260039001d4124500c074044c228020020604016041c411039541402d003104407980c502d4a00c0c006041d03813003072140901940040d507400349161031b01c48070b01401c021621030964000e00d0321040040003c0c1c507000208008850585042c404000d1801014282032000301035a02a0304041d24045100202204861150117480d0b03403078034036082800c0403d0391075080e041160f0440c2c404010009034444410404402c6800a034a000b800c2e1440c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 893000611 1250 892999361 892999379
    0xf051005060c0726010504050d0f023418060512030a0c080a091e05030d02070e01170712110a0902041a03090c0a1512060308040b220618 60
    0x3454405400b95080f019081c0401c0081c1300300c111000c0f1281030003101c0c14081c420120700312070080c0c40441d03540e44456100075030236400c004c144d03000300344ca8009000348545201d000440803c041c1c803401c6032204200c80e046580c241c0d80441e03201800b0141e0718100b0304500640c0350001030401e4029240716401903c03142c217400b02e00004445030841c1030790710b482030152165078903181d07504604075000c00d1204010000c1752100d2002141c941c0041d11840c04040c4600d0b00301810705001a1101c40300844d00400b506010300340308588018112030707038480300c209841406011607003445441c2c0c20401c5400351210005e014060055002c04031541e08503451842642d492203a10128410341c458180c20b00e000c0b43c450300c0140701d010061503001c89210160350480341600c000610381080d581080002c4000380d0030640d1744940c031002001480407940e104210003411a10b070701c07643c0e000c2ca22035852104000100956410900c240c1c3c206400300c100c0300c000301191203a1010740029580d1405500540016000140c5420307 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 893001861 1250 893000611 893000617
    0x8030712200309070b0f09010309080c1b0f1f0807020106050607051024031e060203040c091109030c091803040905060102120405130506060c030d020d0f050106080c0a02100f05100506 80
    0x1b4402104e140c044000019405401601010f903006103051000c2d0514400910200c4802c0d0707502521020429003d10400001250404040e401176060105031288907002d50300c0740340c004216040c84402ea1f50f5811003240500441d4020341d4210001095510410000003180c450302011900207126100e0b0b200c00f07590f20f206104981c48040310341c034003040000c074510583c0100094070401d8408141d030083c0d282d640603a40251022030f848501903000b044204000d11400380c8130180c2900c03640ca003c445800003070392440300603107040c0308024003000316091f405002003e08034940202d050720b88031944c40c00c4440091100f290300300d01602600d510006010022001c0b50103440d4001d00c1500c42a80107421540103002c01426250080d04c00c010031008280200003034004140302c2000941e445840000c0001500c40d4a1a00544141420018040940c00c409400e0340642c1c00c2c0701554a4030901c100880c54400501040f0040b1031400c0d00101c0d064000340c000c288101c802c141081e4805984400748500c41c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 893003111 1250 893001861 893001877
    0xb0d0302101409120d060b0c150906060f040f0912110714011e0c0212030a0e0d081204060f02030a09020f0904200f0901080d1103030408030712200309070b 68
    0x180004810708001000c03100030340020845ca44000894503100c201c114001d600c1800c0d0780306c90361f11006c9503559070070b101c1c04a103a010000034080d001c1e600305000810400460114000e10482d1681d07200409089680d014580f41a0003050703481307034101a100b01528112020032030a00300d02840d81c02240c4003503160342074400a601a95a052102c82801c0c2103954004088070a60400221010303450243e07a0300d1001010081032000038540d541800740d00a014807000c0401a40620402c1c407054011444c03410070344180100d4484284c5803039460b858502c0050001c904140b86052020040c011030721035990096036018400d4415102900c01c1d5010009070100803107008240c0c1300300c142006a4040303002820382100c407014041c64a081c88a0300000c03640e0500f40c0005c1020b5010b00c1d00320544a43c0a021101d245003040f01031803031800c0ca5160200e840c032005110009102001d0022644c00c6810380c81954142c81000c0c200e40000c2070312040906a0740b09468115003440740580c0850200014400ca0713003c5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 893004361 1250 893003111 893003113
    0xb0c070b190c020d020a0905071704080a0503040305160b0412030b09180c041a030d1409150c0d020a02100207050d0209062b0203070617040212010b0d0302101409 71
    0x29105031a0446880d0b400c0c1c00b0498004500c0a2854016210044e404026040c0c107036002c150740c603102000808001e212484004100414821b000c00700e042107048402d00701081c0751803541c0e07075154201910607110f56002d1082c0e482869401005100004540394000ea10030002d01e03808041800e000c40507100e04500301c0ea440442c2001180d2074980e143c034242000c0110100340d41d100301e0428000f0341202d030700c000360050520071102444020301c3c09000c00d41d1050745c5410080d02c103040c4000b8203501c50207804101030040664000c08040034103550140d030860400501101d0f06a04190b2009450f9050028124021104182d803050500d001092101c241c51000e05a019200301c50f800f006001c20313000d805103421041d00a8500c3c80c0b100b034440301a00a500403440980310b0440c501c181407a0080544c4a54100521082da099664500c869040e0b085a0115510454118403064441c010043c444181c1d41c000408020701d030406030082210003d91545da1820400c1d103403141701ca004a00e000712048245 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 893005611 1250 893004361 893004397
    0x90f0c0306060806040905070b07050105061513140604090c1205010f1206090602160506101d0604150f090603060f05010510050a0e0a0b030147090301060b0c070b 71
    0x150b0405d584030018460080b001c680381543d613041c8083c055489404107541c01c3c4d44990030440242002031307411500b00d0b07030b004080b840d0018070150110b0754901030085d07021140d0095240f004035600c03141a02e020300414001045060075441010345a4402044041d614a080800000e04810f00d003651034110b4a00180110035604c5030b51f00c4c8001041003980c2210750b20782c288021600842c101102da00c05a00c24001059035041c04400d417840781000c3e074881c005c1e42c581070314484046000c420800350040020794000c1020b0340b140b11440401203c54000702610624640e00007000d134a0354000f042102c1c060746042026076580b0790040d050f640f0074040c560704060b020f05000a0340d0311610081c1442e030b0b07052030710510b0882024002204030100358000b10003107c01100510440040500b0008144541d02400580d00383c4903059858034154650188117041ca00248096180c2d80e100480e080c4141c000c000b000345a0702c400b038045440c0c129000c600850300c2003003400700c0d4103200349040ba0045000f440b03040b08 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 893006861 1250 893005611 893005621
    0x4170d1b2f03070c0b090315150906031c081b040f0302090c0f0c0606040c1e0f02150f011401080f0c0306060c0613140705091816090f0c03060608 64
    0x40e8410034500c660018441000200e000c1080d800c40780340905603ca85d0540c0d1142081c081514001661041e042006016402c0c04480e00100034005030303682c0c0548400c3d00d40e039910000682040d4400740101400301c1c540b4030b000d00003640100541e00c00c03040e60030b010880e00304070442d0400500032405080e401d01a102c005101602d07140070841d9010003140d420074980b03203100601105980014124041d654010300c280305e00740c60700b40942c1022800381e00d4a004020140d101e50042d040c000c0d01d50714144a1208401c0d04510301c00c1c4202d500c0c2a16001c00b400d201d0511101c103003400c59091051154051040c420311415600c01e42d8003a0040018196400302500c5a244034009940098240c5134003001c00c06c040b0345140000d1008620401c0da007100040c2c95038950400307035550480d11112040a0708100802c0c84141d0b00c5146ca5600f100c1840c5200b1910310800350207501e007004558481c1c840000112000a00030020b401c40c88106d00c152105000340d180118003032301510040d0041c03002007030105000070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 893008111 1250 893006861 893006927
    0x20d050f0906150a090b0d0212010c1b0206031602100c0206160212190207050406150815030a03031104050406030f1403040e04030e030a121d0d050606010804170d1b 72
    0x1d00c001800900018480c610b0740e0000d24006441c927002815a519a510728502a40140202c000000c1007118490800016400140c16100060842c3d5040079103020030501188200592603008000ad40200480d4030139a03800ba54611044481c000020b44400351405520f10102e0307401a0310080e054024201800d11580c00880b50302a01e2034000c610a15000023050383d9580911001003028030302d42ca40440400c100140003013070007000710108010101c641d40e40c0352400241e03050919058600010303114448414020759129070750000341e1040c10148040140324203c0074090a20784684070b07491031036030540c05241e100d000e24400e06109940b0f500c005808070f801520300002000e00101914100001a0384252003500240602000500b011548400d645940316080192030000ca40e0745901440301e9950315a02e480061441c4d0401c130411003c03800300300c03600c0180b0103001c1000b00565242c05501240100070800e18250b10400c002201240b42c240d801040f80c074401d00090040041c003030b0326205e190 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 893009361 1250 893008111 893008121
    0x70c0302280b0f16080712121b1b06060302030f1c0c0b0114030a0b0124021c03090206041706071b05070618180204050102010605191206020d050f0906150a09 69
    0x42c0d4030503130b0421042000807801004401c02c1f070800d44034070700c0004c001d8000c02c1c100c0749a1211142450000d0500300341c883d4100641d05c1203008540b20340c0c000400d151a240c0c0c0134064581c0000e40522031100c43c1c210000300803452000305070045a402c0d0600c64400021908501c039004003414003c044c10042c4603a4010b0742c444841220013034212905940541d84006c44484242e01c0070740d024001c0d02d401e801c0e13900f11198003003001e48248010112100e481220811a8a409500c0e10515588a40310b00c1191211300989005191695003c0c41d1480b00c0c0c254036884060844005002555440c0c0c464500181103202d056026040001004c07240e090a0080e0307030f240143c9900c10100c100c0801d00044250142c40b038841d03010000400513807100e01c0c08002a094456641000d0300c1103190140e00500001030003130690803592003110300802500135044c400005d104e01c0c0c81644c85603007801c04102c101454426464040d00140d0121100c2d91307540c42c55140e800c00400b140b541d0000c8010000c204400c034503005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 893010611 1250 893009361 893009363
    0x30b040912091a0723010908040311090c0435011802130203070203070f02040f02070f050d11121e0a21110906070c0302280b0f16 57
    0x1941900548541e14005034140240c40000d01c600c00a20800703e43e19074105420000780182c0e81007500c203a4412100081c402c8210100625500c96034074408025000080c1c0729800c0500075640d036031603040240d001d4100012542c01034540b030002c625810f030f00c03104031030031100c0800351030100488002000110410000c0172800482000320000388801081c4141e202554000c42200c510603514410702c0748800c9206162800b0707620500030021882c0d0040100d40c2c0b15640403e50008140042c40024010400c1d14103c0c4203141c800b05e22081040040d140d0040f1060040007224030300b80d0082d40c2140d48680c00000801c5d984c1000d840c010032182c5000242072001055080c103c003100b19018045180d4218001010011703c240903401c0350f81c1d2014110700718400c00c0c49400e0000a800070141055403007402c1c10a805a1400900700302840107854a00c000b035503008010386200038000001c80f41c050040e98203042030a80f1800300140b441c042004403000d802c4050801800d00d920f03200002c10083c00d086c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 893011861 1250 893010611 893010619
    0x90d0c03080f221503091b06050c010b060405210a0503040e1e101211120a030906030501080705150903010c1e08010e0a0e0703080304150518061803130b07020102160b0901030b 77
    0x3418480c10400001100d02030b180590310070b4ac031444480e0b0084d0030758000301140f82c002c00d010041030086403240450116240d62409a0959065560201d2172a0018080d8050014040440d0124110700010400e501401108a2280c0ca5000f035080f0640e422400390346803803200303003078400030490401041d07203116007103001d00000d0740d580c0c090790041210111000b62407100b0f41c0100300200304268024003000041c080600c0c0c00c010541c1040341065680352a070041ca413140701404103280321032207810201c80c5144006002803200c0c8800c00405413240d150300001c292000c800070040200780b445002e110707049508008041406888102900008200d0342c0b6582546005545011011902c001c1c0154012841180001040c070104e0f903054003110409049500d220021890000382d009000071519002000603070002d69150003248100e00d50b11614070242d25a0801c1200080c4001d441c1000d8450a0b0003a000c0e03801c4500d00c0a02805600c106004004161106120780d00195100b07500c15861040054 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 893013111 1250 893011861 893011883
    0x10905060a210209031c080c120406090c03063e18030f0a150f0513020f01021903050408060f16030c0c0b18010f050705090d0c03080f22150309 63
    0xb0110341881e88081c8040f91b8a03500010040000c0c0d0300462140d8000b0800d0000c030706120703142c44c030090081e102901c05400385c1d454028003400e1102c00c43c1458000d60340031000b040710854000d112031508203102d01d0340e016580d00c40180f4007000c0031039100c2800c1c1540203070000e28101c1e5591741c0720764204464134050380500c02c0510703103485240c04000070003136a40601c3c1c440c03694030601c00308002507800301004030365035500b00000d004150140300c0c04144030350b90407030301403105032503040040340b4201070200010000c8000740c080760145500040148291f84910081d5026551b5003c020088200c05a402819540724582d000303045a12035400010030782c2c0340f86440068541241c586548240064510b030500041c2d050340c52030209000d116001ea0450340500074421880e002101a12074081c0003a102d0260403078403140c0c810040c0b0b43c4580b401031580443e46984841c0781c4085100f213608200c100c8141d002d0000245c4502c02000d009086c120b42407440c48480c3c03500e400c98220040d00a840342291424085 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 893014361 1250 893013111 893013127
    0x31b090317041a0310050f0a0e15130b0f0405010503060f07020c030d0f02010e0705060f130911090307080f062404090602030a0f0204030b0c070807051902010905060a2102 75
    0x300500f0351128520750702c2c0e41e12410804401c10b0014002d600851003134100300300a00b0030361100c406900403a800600101000e80c0c4900d601e03c651806000516072004440f2820444445180d000710301004080e211104000c0016060104580b801e00815516500c514005070040c1d4503d80c007568801c40d28810b41390410722001c042413a0043c0b40c51401c0203d1904441d90481c9030742486401c800902010003000c580380340101048041c0325200302000c20080004914821040c0402480018410305004202080489401d940a41c10030f03981d56200780030b0003200080e1444002041980703031007190040c24894481d103c0c1c1d0301e403400e0b10fa0b0080d5a100e231001e1020740690b8031485090007050040300096520310785035000000f150000d00341c80010038414001030002c5105c0d000040d52002c22402a603540b000d850a2250560150000040c190f00c15203000c03030840500d1100c00c1070401d1007078076a0340d00281c4a104101081c0280001e8100003010110040551a2140320b080282d180721000140f0381617030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 893015611 1250 893014361 893014379
    0x91005150907022a04060e0c07051c0206162703031103070f120201091b0509071409010c11040606080118140403050904060b03040b07031b09031704 65
    0x4a60300c40d80c00c00e48254518441c10000303801e99000b185880500091000d41900480244182c4420611080d51907549140c42c0c44580c4a50003800030706a01807018a45081c0c0750080d81c1c00000200d0342c47c003640025007020002c101030303280b0b249000d40280805039034180000d00004a94000c070700401038441480000740c0080c4201d46000c24615000c5c0245c0c134110700f4081d298000d150025602035004002160101d03400c05518191294800d050020543c0d08240072809440e01e020085c21070810340d90036886142605420740101d503820796800405a90724241595101c1203040f40b0001648100140310182d8071500c0c145c10301c1441040030303500c8512aa00440c00700d40c02a040100490942e034014410b8005c0101c440c800610260400d10400e19200c000c1c0258110190004080c00320100d00f500080d55550408400361580b521265240d16250408401c41c400556041c0c002c40c2ca407190504040180e10300e420044803003503d891405500c5d40c0e65900101e102c021415104001c02d00000c190054 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 893016861 1250 893015611 893015621
    0x2070612090206180f1f05070c080316060605040b0901120606090c020304030b0637030609060b01030f1a120c0603041b080312010b0c030c0d030f0b040b06040506030910 74
    0x40400761110401000014840021007811140d4400c8141c0300d4601440702031000b099a1b01c40a51a145444520900d4900c001c0c100d290040700441c0408206510400300300f01e002203039180960340900c1403503910414041114850710140350480c0040307006100c044228600488260710071040051103640e20150301e0129002d00b8208030060b0800070f010018408203110031f540114045811901c0100d000c01c0b0015200d030341e900c1c19104000c082d80c10440c40130962071581d00568100c0e00130321a803101480e00100402e60b140106010070318100100a41451030b1103400b201d4040210080c0880107404100591640d0801c210300061046412022003500e4010145004a12811241c0c651541c0b150310444046000e0700041d40550060250409040b0080c0e03403141103400d0780700a95a07500481480908511030781c4200612403046030204c2031420341c11f600896404c50120f00800210260360200016104a0038407598804000e20040c080340ca4101c000799000784682044a02043c0b501d2b10802c1510 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 893018111 1250 893016861 893016877
    0x6080706030e1606120e15180703080301030c0f14240708071412120402042a080f070f02072c0405030c1e150703060911031506040602070612090206 65
    0xf070000080d4902050745c60160105611400c40606107a184843c611103a40800a00d030450324240602d040c4080c800070300241014540103030386a17540e036031241010a5030300103620030071074844a00c2c04001360782c00805002031038420000b08005042101c049000001e0002e403100036070350100030825100010014401441003134850340810501d061005000381c03c0c00000c6040321000034082144030381400d44e2801c0942d200e58111000a079011620018500550b001c0800750131480200194441003508041e14920542203001f410499580c0e580d0126005200c00304d4030b2026900c2154103001c0200c0400c1c08212a19940f0f1007480c2800c40300c80e48420a01d0305642c1501c0c0b6030070018140042d02010f2160015010042010780000d500070a052590f61024440400075140e81c00085117130320b4403a4100c0700043c13401807002c2c00b0900c0411015a02640196500c0116168605440c107a90922a05540854500c2e402030500e142ca40139099840200d00103104840719520800800182d83d0398000d04882 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 893019361 1250 893018111 893018117
    0x606051b0c1012200d111e07110a050d200d150b0904020a090c12050907050a0510050a0f03020f180103050609090304050f03070f06050304050d0306080706030e1606 72
    0x1040707419840740f003195942c410000050420964003040b00e20040e0866080480c00800000c40c04050940b90b08203005200f105000180e0b4141280d42c0714503860040c4c02c006009400004001507241d00b00a03841000b0b105694209003141c0f15900132521684860903910f00340740030140d0351106980020b045801615080750300c0c1000050301c1c580c09009201d0340f644440c0503181401c00d402d040d0009078491102d4814051286d484c0c4d8010900e45200d8442c001702d0307081498003884541041d40342d59844806600075540146070450b400141c070b02c0c181c40c551040c0101912018a4504500401c8070045012109801415000c10124003540d031000d0043c490241e615513401080c00c200f000050648402605082c450340d050030500041010120448040311021503034072030421042c08c0441e080554a50254148451501002680603088401184580d109105949083d64010403da044805601840c0a6580b100d074040c00000d010398003003684504050f04680b1032400810405210341e01e9031b0015000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 893020611 1250 893019361 893019377
    0x20612011707060210020c03160818041b030b1206040501062c190e06090703060c0507030915050415020a020301230a090c080f030702030607030606051b0c10 69
    0x110308581e128114241141c1c0050b02a00d442c00e00000d60300d01d41c40044000382c0742c0c001200f500720181001240d5509140034581c000c6c82a8904000020340c00074090310007401f150031003001451a140c86813000150a940c01d51035240e140300c40450080c18a00b060b15085200c900e076840700e15030100b081500c42c07480381e00046441070908c100f85d070001d000080e0658408519110803a03640382e03d01c1110340e0203442588030109401c4070000a90142c070100400c56000e02418003031100c0c001c8007190000036280078600038000c142240324220f03a85d1040e064090009190070000740701280242c5001e4452002900c0d0071030501b600d90712103c420307420074040600541d203c0c5242a04500f0203010b00401603840b04058504001c1044000320440c41c0105034000c0c00ba40d5400c06803c0140c0c0b20584c4000d0700ca942c0071035200300d840200d202c1e56a4000c1400764030034816440000d112a120340100300985409a0300e003410012100e003130141d02d117020382c0510018040c284a07507045458885984400b003010750740b80303d8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 893021861 1250 893020611 893020619
    0x1321170309150108030304031805060a02060126030409050717090c09010e07020d050304050a0b0106050403110a0501140d0e010e030a170601020703020d06090f060203180105040b0c0a0c02061201 85
    0x102d081c1c070081c44000c010000500400c40c0d1000401901c0c0e005401d810620300801035100390080984950700300d9544a50081000c405050740056054180c80c074504503100004005051806101c0314078042d5142c0740c0c02000144407011050b00010780101d56410047d0a01e03a00381c949849501f01190241c01e03e5001e014041d001b4580441d2840c01000303d01850b661070b00300140000e490f545c1e115080e406202001002c030b401c0001c00c111205d40e20341c11840c20042c2c3c0d40c58030360082c19070b4024031058403880e41210814000f850000c500c0d1089a10503100e0865055600100340c00c140c101501480038a0b0303450744c4034034a1260a001b00c101d10034110b00a150341d40c000360b4020b011402c040c2030014000001d0380401807d40d80000304002900c0c0c040301c003c0301003581850160701404048400800840701810f08000304499034001e140541107201034080841c1ca0760740c14600f02c8500300c42c003800800e99440440d1070b114500c0f0041080e941c152610101c0315550b40c000c20001d900c00b640c40100c0000c8600104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 893023111 1250 893021861 893021863
    0x3071e0620031807080601090509070602010e030d1a1306180612021210020a02010606090605120f060310021605191106030c0d15060201111321170309 66
    0x2011800e0681d141c41c21040c41c0820084440c08002c0030440200b241050100c8903c0742000704000038072800c01250360795a1a04100c0020f02405c3d0b03070a5500344070b03d90300400c0307281c01800341c200031050840003035080c1603149200c600503202c3c50000c4003080030070b142c681c0c106480e0b145003c1301900d011030300481c00c14500702580000100e051250701c98146000344c1031005004a00d03850b040590125078407120b000384c40841c02c1c14521180c2c0361090007480002d250408a4064115804950031900d86140e03090b6622800e64032485401c82080c480d00c40c0c2c0f40000c4020b0417000c6600c0d00101d018040304c58a1712058030070000c903404041d15000b0007000005034020040d08000c540344010a25500c68959000c50744c51994074180406500d01c103c0c0c0100000d03007030821180a6540d03010b1040e10a208036501c2031201c01c14035945003d13041c015400d007a0300b415043e4200084484c440c000718010000c092a11040301020b20320240e00c901c0c1d028440900c1d1000c14003001c4529049000c00d0300c40c9640c3c1c20510821 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 893024361 1250 893023111 893023121
    0xf060d0e0c0d1709041103010303020c0a0611100908130e0406060503030a020d0f17161101021314030106050a0b0c060a1a04090507081e060a02040b1b03071e06 70
    0x4521685a0314548800543c40d44a64111040903000b1981c40d0400040010040e00c0503514006944002200020500d540016661403403802900c0201129880d500200d8840c402d00325003803000d03842403800b120044001e9000e04155801400c016041c42068120040d0380c207070952003950b0300c03d50601400300348481d81c0708150041c002140210300c1c00d4a00c28000c0d448000c180c1c00754040c80707030804802a4260090074001d00c0340c10b480004004c0c0b85081f060040c0d1070508480043e0008000c0e00c10000b18040502c02c585642484441005405240a5881504141c08801c5a401d9500e8480000306510741004400203006600b80084e202d105009200d13290010042030110f45500b80100040302030480624035a840d001910045900340c0e0500b0300501d014041c0d880300ba500d115403c0e040714292481e40b12000c2d150107010989100340c07509194842640524041ca0031003802c01c01404c10401401540502d48000c2001520b0901c001074894179680003000030215030600c942d0400c0b000f0410240b10b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 893025611 1250 893024361 893024383
    0x306150f080120031305120a0f09080c13090605090a12030212060f060c0a1202160e010905070909020409020d052d070c080c01060914071d0f060d0e 65
    0xc0005194000d40f0074000d02c6000800401c1600010204100394200e510709000301d070f0408120344813842c42c200420416804044e50500154109012080c80351086840e03500300c50240d030060425140030340412002c40004040010300341d0352100e405d40090803d01485208840302c03c05080100c2c80c1e0b080000103207039100c9000041610401490015070861202180c0225040d51a80020113461002c07980354031500d5030f5545c5505c034811601003001801117946071522055803d030380e00c11030060700304032400d1240e000e0030280b5080a0b006018440c965400180d00c0308040c5081c2804942d6203450004983c03154018590071900050395140c400050700030960400100342c074811f034010842241d0b980070303894561584c16400d060070118107480d01c076031400105503411240066840c482c8511849c028409440741001590500000300300d85a40c0e14901480303406152102500f5594580019010500b61001d040d4030076241f0b0f07032028040c0c6807440540740d00150780c80c4c000b03014002c0e13001113854003201d822 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 893026861 1250 893025611 893025613
    0x182723060115050408060a150801140c0c03041710050f0f13081e07060e1f150f0312021e0703030e03120309031201081c180306150f08 59
    0x50048640000080c0c2581100c01c801e010010b4210350110440d458031030307a0b2090206110701c005100e2505000c0c1d000e1424842d0418002c69180d0342e8096070f6080e40c15102c0400c2d0f078101400d0002e803580705442c005080002074441640d162503100c4040b00ca5104a8800c0b04240ea40140200034074035a0901c00c42d5080300990b003c10240b407600d00e504842121004104980105105910508012162007540d03015000c040c0601f0b0b01c4c810001240ca1240c0004805a03401030510a804040c024041400d042c800c061420004036141e001c4070140c003605841400c039159070403038034000400c2886080506c024600c50030740c501d03004100303040c021710b020101c10000c00000c004202c100482d1000144610489030b041c148103a05590005c0064102101c3c46d42401030090000700300810154048001c10400c0040800a0010398898090540d074094a030300014404881100004009005202650811030704040b0b098840707403255200016a6054890300703c01003002542441403a0105500ca005084114 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 893028111 1250 893026861 893026913
    0x90513061d071803020906190b0d020706150b0f0319060b0a230913150f0312030203011d06030f0f0309120309101103073008101827 58
    0x240028000b0700020b414184261008422005a842000510230082480120f016110030700043c5040107513020400880e1000e01d0a140042500c1c000e00c0d11005071003881000c00e01b050215680c2480d254000703015078510b010340c5502140141c1c600e0080d8400350104114180d03e80d031a800c8090011250001d40c00c1002c0d07060722504219070f20b0031082c1c0c0c21b403180844009220750004540c0c6002090306001080c0300d803501c0000401d502c18160350350001c0303034854040e1b82e80480d550030086089000a020f12002210803204010303007004800791b900e42000c1700600303032203030307107002c12206840c110382a42d800819801c040f1b07201d00707035141201c16190356410003406949042e80764000142140200700b00d020a120f020b40c0b13111589038081080d2075595500000c49010003614005440072104003500101405059502061003140301300c00c86c80c010f106074160700345064202405003104820fa4101b00385881c0d030f80c0503000c0007039000e21b5030364440c60f03414000346804410f5818600203940003207864261410840c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 893029361 1250 893028111 893028113
    0x30906082202040f0207050f030301030308011707140a1e090b01020a0317101203091a0705100b01180914010806040c121509110a060e01090513061d071803 68
    0x241c42a490301c03941200c0001d20108042130120080c050940701900500c5145a035051a20001000318180d034003c1c0c4031190140e036075591b003020520a450142e00107801030710040164441398a1900500c031401050509025110b5012a044910301d810513022500b00410400c030010780d911410010036002c0c405000c4001c0c60b45c40251030b1010790520040c003581e24100044403403460000e078602404440a81c0d041c00751082c10700402c00d00c0180141100e0365121045032054160b00c0c0225100642c0c01030240610700181c1c446d00d401040c1d1078018a05109a060a041401ca0111b03040409003400c00c0c030000314846004c52a0321200e505030060800c81c0c0c4203006100c046940480c0450881d4140b02402201000c603191004008101c0c9811a07801e50a2081010402c5a0030030f41903d685801d03103542c4003042e07a400c0b00f10349402980084e9804540850014415400c0c83e100207410100002c20200d1020f6036010181c4503641e591084410301041c550a200440c1d5010500400500c11140c3c510451811 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 893030611 1250 893029361 893029411
    0x1202070b070b0915040b070206100f0b0307090b030709030b011509210b04030e030c010e060d0f0b0a0b0c071202060405010f0e09090c0f01090e010e0601120903090608 73
    0x1541c0006400300752003a0000e0107076241044691520b40040314540d0803801d06140c030a1005a05175000c1001d40100c0d400203003112030800c002801c075908803d2034440b1526224000f16642d101400020402800b00400319481c00444011401041d82c1d84e500c0072020318608000c030141c00d040e08200800000290001d91041d800829003041c2c4040c045000702c0c800e8180c51640e03900100b041c00800b0352100000b040141a0030201550a6800650070703a19160401801140d0106c9808911980488280700d0800e6241c844d40c41111501c440c100b0000315500b50000248601c50582c0c48803411510000300c2c28910401405400020000e44150980c00c014950004010340514010345040181c00b900701c059080c85424041c05010018080650509201e80610f440c1c02c8c107468041e00035000c10003541020b5100301c3c030b0300045403251481031842da400c12781076144041e005401541004504e4440504440c40c1d4420306540030700c684c460031900c03442c1400c00740008000900725259540566104000400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 893031861 1250 893030611 893030617
    0xa02160b01091d0c1009090501030312060608040209160e0306090115060c0510090f080c010c020705010c02181b03071e0f08040204090c12230c03070312050f0d05041202070b 76
    0x18116400f80c202c80d05c010044400e02d88903440499102d0504e4000070526800010721880051002c42c140315041d01d440c3c05650001068800a4005001c0300002d00c0d0120601d060040220303451810346a240c2203540080d10300138081c1d84214859658003904c41c05c000c0914a0b20005044a042c45808a2060b403500354070f8642c0300901c2906c064a03803065008002840c0c1811010942c4400c9490315403440300b01d024000c0090070110000b500c0b41010200300b80d0300134000800751981c01015844064000295401181030140028442a10544500f18003d50550146121318100c2e9240d07243c8816400000103903c120344010411f0000c942071400b41d40754004040e60b030054058601140240e007178503060040e20241c1d0b0101c1c403c0e04448070848100680b40383c41d000c08040044a401d14403ca00c0300303190300c40d0001e10364954180e01c070540800010f207100700b05168103401800c1090a2000749040d650301980185001654140c5d914100002c002c40c000d145e4a40300601e00c0206111400d000c2d1318141c1d44 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 893033111 1250 893031861 893031883
    0x1d0105300309041e14010f140a0b1605010513030f032d0204060806042c01020d0504030e01020d0f210204030816031209080703080a02160b01091d 64
    0x11068820080c450020001c403603807440050020401c0000c001880301000d080700c04042142824000100c01130044035010b0f038180e900d111414429141b40c00c02040e0241100d20f0203030780124a24000242c044913400180000c825001e091285011980c60182e08484000f00454600440f0800031404698048400003452103241000a07441594040064444da400d0f41c01000d944181240001048400d801034011101c3d692140303131864640a00b044240e4072100345280050b110242100d8060f100040c50301e921010441c001807070984220031130019100308407801d601080512000d2030607540e040241201903880b03464918100f0910180040c291400f0014044d8045900d14080441a80c140d0444004603030203803200340c1d20b144284020080b4091402c007540070071040d2075880069685402034840300743d440340e445403601c0c103c0e40d0295000c900251501c03044a80c203200584220b40b1030079040e00c100d4010101980d00c2d40c90022040241d40140c6e08210410580c07205c40000c1403000600b00000d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 893034361 1250 893033111 893033179
    0x70210091211040b030601091b0309080a181806030209130507050f0316290412080706111303020f01110a020f150a0305150907020c0409060f061d0105 66
    0x1501c2d10a0004000d4001480d180381d25004000c000074294500394400e40b0b10003003d00d42d2280b034802e030903816411103009050291202c80d0400414042c548515086402c40f0880c02d6048102c94841c03d1040b43c10300d000c2d10340c61007207580380024415480c1a003a0640e00080041144a00140981e80c1700e031101907520800f4010000901221b5056405020745c40b0745914000c0707184e11043d503c085044180e44103022004110f0b07040d00150345040c0d221001c0310203a4002c0900300c10f0b441c08c290389201140c0e00104050320300a0740ca1071b48000381440103000341401501c1c1400600028150f0040003140c0324241026418010044407500c501c400204e07102030b065070102da61815414688010603802e00815100902c00140040c1403948590964400381c01001500d0850303803034100070002d00120880c107844c008096800f601000b070507450702d50440060b0a1145002058a003210610305042e500250032850381c444920361a8590070314220400ca0040500304d50405604400b43c0070820040b4004500c00b600d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 893035611 1250 893034361 893034383
    0x90e1509070201020c0a0c050f0d050a03050c07050a03080d0c05090a060806120a0b1b0a0e1309140c0f06030121030302130b1c110a03180b0c0702100912 67
    0x681ca000b0f505880301d0782c240070252100100c19150058401303070301d80141403283c400f54005503c0790030400600c01d20581d11100420345000191000d5801c2c0d000810055118414888046680d8941c0e407640c4000b18810030440d5114203000e52520291010325a0000c104081400040b8160760b54a20f20000c0b60420f0410680d0747e00c130440855499480c480c450780c0b10748225410a41005088200b1070b00c5220100041011503442d040c1495452149048010003e184610041c03024034000d03c030320240c44502000021500c1080d580c51040b01c081c000014041d801940342200356080440e404035201f0b200f290b40e14070b10f6041c01c10070b9100c003050400306042d00e4080d91001c010140694100d40300303000300e40c80d00d20380c40e6605d042c0000584c0c0260101d4011800008501c49100c080e4001d003c4901c0e6070342d11450400c4192801280140b0a03058040034407008203040d500400c1d01103903030728002d0749501120742c0e440245006002145401074440c40400c005004100301c80607480f55501c0d000d40c1e2004294134 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 893036861 1250 893035611 893035621
    0x9071d0906070e01210b090c03041e030c031d100503061201180f03140d020301030204110316052a0717062e0e09010504060506010f021e150115090e1509 67
    0x40c1b0688841540054415060002e072510007409035110354807445041403414400c0004458140140000401042c0b0340003010000a001d280840f81031039510b2509494400d1183c0007034942a403080500010441c000300307021907401c212440d80f080320781d1440280722030319010a0070040c01c1c0440c5030140080340580200300415105a41c4a11419915001355855035450315018000b94020b2004030b00c11480c01c101c556400f00c0d40c8040c2c91160781e515079040154028407805035550703800b501207040050064003840800e03a840707070403100b4248641001811014102098030b0040b00741552445c0e515400001001922028401100d02d080e5000c007851014500a4100502c4000c42c0c3e0041d110300d0141030704011110344154441b0388510b000d140d00f80590344801c0010740b490b80d0203c4110005030072203042c4407001480f480c80000c0d10780891045a00d490903060aa0450035020307002510740b1140d441425107010351001a8901a02544080070811b0909014180d082001d000354603000c0c07812440010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 893038111 1250 893036861 893036927
    0x633011d040b0d050607080708060f010f181211031f0906020702040e030a14040506040303050c070503010903050a12150611070b03010f09060801050601050f0309071d0906070e01 78
    0x1d0010b840030306042c64009880c58041c1d103075801110303400000b880660004400701c0c8200c0095010301c00c0501140c580700840307001100e0500c1c01c2c5591500307000e806420806000300310300c0007030018800195109600001880c094160f6580515100d1299000100e821110019041081d103d104410400100b22145103011700103809000c402075840380c9041954101000080700078201d40780b07030f0b907103c0c00359a070b2090b1400c005000b103000e117640015040c0700030310010340128003c0c20380385040e0089844a0b6507d900281c2903d80c403030011400a00007003802445c0a800c0349110b201d004180e0b40078810855505a600c480405501c1914100041300d04000340340e00c000e11a800c05400c6004041e41c0d00d60711101170605074a00c0744240001d131071602d40c0001e00c104e01842524000e03803050b03444500d0590452400d42190b0405402c208003400780708000550046120307182807500742e11032180f119915210b52520308025000301040207200000c100c107020b0780c0c2c0c003c1200c050595110149001e89980ca0317084 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 893039361 1250 893038111 893038121
    0x10c090512150408180a0311040c0c120e130603122f010203011e05030d05090a080f15010806060906041505150403020f010c0b0f15030633011d04 64
    0x542c00107601d0703200b80014000403000030080928200100c61142e540c0105000c01c80f003140c4000b40c4403031019001c00000c0d140c250003071040c419243c6030081c3d44512a45032081445c1c00c80c2d5500300440c185044001d01420080500010b0502144041003010b00e180c4604044420300030100c401c001c0c00304246e003545614000915040010040c00000c2c036025000c03818003c0d40280512040b400d4811644804440d06408800a40e100074006c0c22205111180c141c40c0c64104210303050b88929822408940c010301000702100214424000f454400130f09040c469102ca0181c011861641106040140380e07100d42504a81240c41030710006100345031540d68131000040c1ea0002944540c800401401c0c00703100c40003034000d480c002c45101d00620f01c03660056580180c01d00303004105640440c0040c200c668510034550b03010112980f6210002140700c0040d0500c60b0444a02c802c031445e50fa1440508a0310041c1101c1c8885103c2c2e0000100301c038000040c1c11020b42000c158005000c3d45d6003034001da104c6401c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 893040611 1250 893039361 893039383
    0x606010c210c06051f0f21020111030a080703050606070222020d0e0708100219030917120414030f09040905070e071214070516061d0c030c03010c090512 67
    0x204500d050004254003504a11800100c68031941c1e5004240122a02d091108840c41c0c96004030303075400c030402c2506011503101408d03414003002640e048070250b0305000608404410b40c0d100ea04903e00100c011b000c440002cbd04050003400b0522803c0010b031a40d102c503c03c19000300c4405a0a01000c02c03129019104404070030000500704a000014414005030390400d40e00400159807010710f024140c103049001c0d211105a65404491704610124001d43c803503112603003d40c0030b0181071045102c0d200b21551014494036414010705c420081407000c4446502c40c11400d81000c1c520b071184002244801e4010b8095843c411a5522104420050200540d01c0284130030300c01107105150254029010780001d01c2004030b040d040038101c6a4003120414814031808581e15810700b0700e001403980303c82503581d0850894603550355580280070790807250054000002c50200a191500a410a245c24800110010340c000e170304003501c5019045d046822082a26010358202441c0c228015a02d0315041d0741d034074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 893041861 1250 893040611 893040623
    0xa180b0c0709050f070c02060d0e070b22050105040b160501050702030c070f03080a08190510230f0f150d020d050f06030a0605070311040f0303020606010c210c 70
    0x5400e01414030081481d100300c407100c50007049281d0300d810002c049200104c0303410b400208416240d000600d0403102424034600e00d880c0025001e003014040070714041d081c1c1c011443e420303004100c0005103030300000c64070580d90810480d243d940745807500107003d82c010340c0078084000c1c40100d0580b40100540101d064426040340081c06141000400070351070b030340140c170803480d07600683c0c00119810200c07000d03203800c0340e0344140c2c66480d00d038004204946003000a0450344560780d2000c0407803021410340c0101402000c0080380203192510700158810360700140500340056504103180341d07600c0d643d03950b1112000102500c82030021000180007410704440310f028810901004140c442a540c811fa01810710b448a0ba40104144d0b01d6071100b05100940c2181c00c0303075056204186020008003660061038020340541400315a07a10807072254800758110f500200b04070418404204245541000f4242c2c2006081c00c0c59400d11026440d03001c01082207074001101c44800d94020030650303100d075005442c1650010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 893043111 1250 893041861 893041867
    0x31e020c071a12100f0803120a0c1b0b012303030403020f010e150304021311090d170a2a050a031d0d06050906070824060f0c07090e030702060a180b 65
    0x340340401c41501d1780211031411102d000d0105403400008100d4a068000c1208408a07503200c0c2c1200025084c102040c0c010052400d20030103000d00c03001040c0c02c00d05d220b1940000c03a0344c184840c1c0101c1d00c0c0c0340c0841c1800c0c1450320035054020b840202c00c58095940503900808003000c0c21005036207d5002071015604004181d80d4074040541d0b40c030165005620844210011072854001c1c9401e131a03401607a80018031042155104620301210104081071007590078100038000c00030400d015421020850010808070500003401c0c0c1072114a9980d4403584907031100700c800e01516091780d103510901d0020f05028102c8030b80c4034040e100040d078807511800203120ba600ca400c607203810009041c094901e00c03103d204007404680c0e454064403180b8410351214103c0ca050b03100e1441c004022645c2d80306032503004501003000c1d80600103200010300d04441c000300240511460840e070700b41294100f41c521021600f05222200041ea141011146260481e140800da54018081d01d403541c041e050344001c0d8040000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 893044361 1250 893043111 893043121
    0x702121e34150903030f08040201080f0604141609120f030c0309050301050a060305161413020d110a0212120c0309030d0e010506031002131a120403031e020c071a12 72
    0x42a03d800642c1d2099071180c2d041e4103800390545115100f0769009010801604c0040c2001e10554015607112030000c001040141c09810a44e04041064805101e9003410801c20714015030803e580e00c00a1a081c040140990080c2e250200c0c000c02d954001403c00407007a4122092510800842c1c014100c020300030820741c1071421480300100300c1d030b20080310180030319103224840d10510803261044134030501a24200000b040c04025142030282080415103a0900c03085401e580e0500c941411441d482501d680d45000140000e454a90b2680d2102e00c1110208021403015054031140c035009640c106010740c6070303100d45030424114010708040005507460b14501903020101504014001c2d142903041c1c42e41d46040000407402d910a1180d41c1c1000c401e02c4400300610b12494011010f2600400407007814203561801510b10500f00340c0c0c2c26070000380c4910103281030021100007010301c401e00440071440c040d50150719a8482c001d52168007030407824400032811410380c45007250848076441c2110900c40c40c0c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 893045611 1250 893044361 893044367
    0x181e060602031902010e0c06160807080d060b0a0f0c14060f010f08030405062d0d0c0306050616060506120a0317060409050703060507050702121e3415 66
    0x40316501009110040354003c000340103104d0400d0301b405007000303402c0000c1c603503090010a62103c03103416026071580d009403011454100180944a10401880c2c0c1d0781e60710441c82c40240d40c8540c101b90042c1030200030480304d03da0481d00003d410049410090740d030701008d0a084212100205090801e03000364000c03c00c82254205030603041c1c2d568851000b8a4540340c0950300d64a014900a954015030200316484801c410440d8000740c5945600540c40d940490425902a581080812071003c684600e8054103283d098041c0c500a414240d620f0f60070f1200d10115001001c18042000d032a0a5990000c566241c84a120384000c000052044031141c1c0300030320b001440c0c0030890350342001402c210303800700c2d00c0c51403c0d00411312000d400800500c83e403403c0d51913a10040030701a000c4410b1080400841c40180c455120a818403480b00c80981f0b5010f800c9044c90940b0810f000c802e45c91a04400d910342e40a1740300305550260070300d09103034000e5042500000503680313145030f401a40c024a00d515540c00003680c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 893046861 1250 893045611 893045617
    0x2d0902070b0a0501050a03020d08042705070201090f1407170a02030c0909120c071e050405060103050610121d010605011407030e010e010c020a082401181e06060203 72
    0x4822a0007500e190356020350441103803000c2c000e0307a51240c81c20400708054541102003100b441d000f0003d09250540c0c501b0728810366461942c0b8005c4030365400d603222031251a28484d0f1948810540003c0c801418607945403c0301144003900188001540100140407440820442c000751069400a010015842050783c0d95880d01c044128803074410001c142000d420300f5a55280035070040030040080364940754078449aa086050900400c0c82005000261704003448000311020001d11f9084c420b02d070500d03042c0300030f9402c01840c0a05045c2054288005a03c844100c944c800c442c61a00e0030f0381030a10284c00d8090080000f5584100300f107404801c4002106520050444909072a1b0b004640c0380c2c80c2005031203020304200070b00456007140e10030103654099031119030701d00c2d030500d040400807a183c0d002607282d83c2d49400481c0c1d0369004c0c00b12004ca50061541400c00070240440051840d13140012840080d001401d0380301145031115640d401052541c5c041ca00c2d000c400c0c1a092240fa9222070009581e90 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 893048111 1250 893046861 893046863
    0x50c030d1e1e0c050f070f0f0f151a01021f060906141f120b0f03100c0e0105040f090f020c030301030311060c03010303081b0c0d091505040b03012d090207 68
    0x500d004601c442c000d0043c4200e17044030f401429001d003020a59110001d00f441201d2040c0c0e80d024120441d0700008640ca0a102c403d10700c031f0102408410002829042180c02d03810a00d8820000d091080d40035a800107503421031a0141c14084440340a46100c41020704640d03070102c2d0380d003130404a020441480406400c04c084034103550201c42002412504140c441e1048440f9010909000701503070b01c00c00e980c0011000035401341c0948100c069000100b841e104c040c1a580c3e00e104d55469120030000d40c019160a8001d9091800c18103140c1081d031542c0f006032452147c000305a94500c519142c243d1903070107407400600c0c00e0098945944e502e007406818001c0002c6101110702505000915614284080d681601e426946803c00780c0c0d541e1501000301c0d1980036860502e98000d00000c000e4010070048041e400c00c5555542280318034084002507001d50a0349210207004013844184610265002070f00c2c11140a9280c0c00031000a0700d440c2003244121503a0b98005401403080801d00100310b400520b141e03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 893049361 1250 893048111 893048171
    0xc07120e1c0204111c020a050f0f03060a08070503120310050406061205061e01201b0f0405040b07050f0405100f080907080601050114040e15010906050c030d1e 70
    0x41075031484e081005100300d101c040d00c2d1200b8455550080031469002d07013081c0b01103007002450a039001540f00580e1700134030102c0240000c00010003d4909010303003d60001d03c40c0700020158241003200182d103544070301d014207119002c00700c0003038190701401c5200c84c0201005402000a180c6820b030080018103d1070704040c1082c141b10200b015400c003040c071071081291511005075465043c0c1d00440b482003a640d034040c0001c01a00302c039111484280b1400c030343c08020541002040166405024010f402803130703503900c02e40c6490200000b0485002d0703619403000462500507a80c040080d468155400340307420031504038800c01240b03480207400508a041c0403c8946904070700341d0351001075030b0b03846095000385400c07a0840070042055501a480601d02e41c480110028101a1540d20b5030a501e14100d545000c01e030f9003081c0e0384615580000300c1d040608440d1400900c0e25070861407499907403040500c40604103540b01d11502c0e9034851241c50408909201005004504d420080d6000e01019041c0183c44 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 893050611 1250 893049361 893049371
    0x60a05040618060e0f0102100609050618090601120c090501030b181b01030c1101090501050f09070e04080706060b1c0b0d0201090509090307080c0102210c07120e1c0204 74
    0x40c1c00e044508039422100f4660b00e4100e4080c4c98418840c075100c481c0d1000b0f05510824640c11002c500318026034000c1c151000d030010351817038802c040040c0c0041c0d002440c418900170700f0a21030042c10100740d040c15540301c00001c0c0031701d011515000d002141a5880360030305600c2e00001000f0882d0246400b03014502d0368442044800d8251000b41d107460b01c005495101d0034840202d04032950098001005192580c00d040a07180d032460300d11800e640030054202c0740381c0d64400401c1810400c0c40d807000e0b04000c0c5d034001890030600300300003025583c9000d08040e081d140c010400208000c06904000060a500b800d59a105c50108102b169803004681d00d0f01d0426051040c2d810980c107245611001490701690703481041c81c50700c0140110b12402070604090760000308401004101c10b0401080c080310b00c10001696403039131680c02c0d03005024a450030f0744640426410301541c0100340c400e4801c596042054486d040074003c8040d40d82419030b04d205500094442c2030403d0460030329100548c00c5009950030b200c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 893051861 1250 893050611 893050637
    0x15030705060c03070b0709082113060302070c0614040303030b0609060403061b0f09050607020a0e01120c0e04020f01030b040b0405070c02040e210705031c0518070308030c0702030c060a050406 84
    0x14841f40c2c074080c00314036038054890440200c150030401c6150b429401c0c8000d26003001d040b041c0c0c6e0000070a8021a01194002804034108a10381070340744001c150398500b0180c07010040861301141d100781d11000d400c043e15941100c01d541d85d40d0048a440e000001c103499551540d9181c04000750a6404880701c1880e900103510b2041c82c0581201a00c0419a076103084009080c01d0401c20f09410806069810002e0050045031408a409c1e40764043d20f5100d0588104a8180c0b9150740b910102c2d070000c02181e200c3c40c05110050b181c08a5540500000342800f29842c02004046001041c802400726441030421060080050704034200740c0e4064001ea030240321380744510f00740d01e54480111003040581d00803210b034141c0f590001e8016146441c403c00550703180101c41c1c03250040180c80002092122940c44007445042e090840d54088060321080c06020040d01d16240c0341c009000082c540c41200400180b9441103640c217108195060a00030703c6140c0f600c80ca401c0007031445c0c200d0702a59001c101e41c05403400e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 893053111 1250 893051861 893051867
    0x108010f0b0306130f0c140306090d0c0803040303020913050613060e0c0307050c060108030d0e0a0b07032d090201201c030b03010c1812030815030705060c03070b07 72
    0x50078440c0203002440e09450303e8a06500b82410780c070042e201824507840398000030310046d5244000f000084070341b1145c03a924208140c1005000351000c41583e102d120002c0d85e203604035980c4124650081d0340f640d260368503801c080d8068461a1440d507404a40710b00da0940300d141640c80140110030540c0c002a183c89190110b01c1114000e002e54517081c240b031400106404607090095034400e110b840d15a0400202950309440c102d4280c01505d40c5402c04503400152800f54807861410b40c440e07400070f0481c074400e61240f00e12240040c01c441e0406846188014024101c1c414920008002d505450840c41c00361405000905c038101040740028075a0308084a40070460100d011103500c201c001e4030180300c1c1c6a2100b01440c010900c8001031549913103840506036402e11425810b00760940380c001c1c00003810600944040c40e41d0b0084880d040b00160000302003070340300c0340c590341c409085a2120017484054002a00c1d01082c1d44c012584104001850312280c0808005806414450065400d06481c1e40c4016 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 893054361 1250 893053111 893053121
    0x302010e0c0a0f1202063c03040809041109030f071a030103020312091c08030901060611030714010f0903050c16060c0b0a1130010302010203090108041704030b0108010f 74
    0x921502d0f4061400c1c003030442184a003000880c40108028900007846801c400040d070f4030a0044410315030301d034140c15144244a01c0e6482c0c00400410b00307107186095503604619015003040c403801290340304c8901081403c21001c0b0f8200500080440e451048109255130340c906c01c0c2d000c2c2d20506491050502a995244019641641d6004002d0311041d4604240074206411110081e94442e24003c000701444156114003a51540114610759992400d040c60600b90780060f40b0020411110000c80e03031000c000072050f1103002364040701d000c1c00c11441c1047c040c094408000e00702c0318035191801100405402c00020980d5000c00300c10b46903035000c000f524100001462180718045401c40700712500003041030103880d5010362256030014149200201216290300850227210b820060100b245032001c0041b11000d502400d540d5200200d90f0442e40001d4890003100c5099042c000c00c00c011a04001c0103085c0c40343c0840b0045100c6440f241d407420000400c01c0b0130301c680c40182d4078000486071522001c2c010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 893055611 1250 893054361 893054369
    0x16050f0105090123030c07030f18180905030301150f1e110a0f030806012a020405071b03030c08131a060a0b0d0207020a060809060a0f090602070302010e0c0a 69
    0x389070b040c20480c100544940c03c0413200105208110f2070424400382c00d0b031000e1750181e485e0aa40c2030700d51103a403401500d0307602143c0c04081845103030007030500c9441c860701010342550090011024111141e02d0b040c0c002e0b1a0802006110303000100c00802d0310440107000b614040e94555880039141541d400580760704004906a10550f10f4840901038464040d18024841e1600396080700c103406040e841352041896030f81002c400140404081c0f02d0250b80c041c41e442c41a640034492014022400f82e400d6440a0401000a019684a100103860103019a00c001c4100d1151705541c0f201702e4580c60020000e224909901000c285108003103000c1259002400c0c02e042e40c001c503c00402c500e680300030041e80a000b0f00f1942d00042054000c02c0c94040140070b400c403902d07502005078030b865461041010b19502a008802004541000c03c010400c0010f5030b10f0f04080075000c0007912002e45040b0fa000741030a044050700e001c2c00004c801c0100340d0305601085a441180b01511000d002c1d042c00c00188030301d10700c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 893056861 1250 893055611 893055617
    0x1080606041508010912110d08041e020324010b041217160303020408120906190c020a0602060709060503011512061706040b0105030109020913030e040e16050f01 71
    0x1500030305040d40410419400511141162030343c8401c0301e425100c0386181112010315146643c801a42c1120510014052450203010031641c0c91200501c0100010005061100011940140c885000010401540e006419140b1401c01c00c00341554122101854801e448c081e003000054003130303000003075605442e400141d01d1550440344d1a140c02e024046809c8583e4600200322030000344404028110649202c1d0710090380700c900e003a0405042c5554011180302c8803000b044045030581d540c40444c1c01000100b200c07069520000b9004407070501e100760000390428111031001ca00545c0009059100d190703140d45000440740c0b600400c580c6030100784512035614a01c180701141050045180300c072103440644000407000e5136410b802d100e4801c40324040540d904106e042c04180031240d0092405040c046c0c00900103400c0301d602185280b24000c3c07841e13080001c660680010144110741040386d602c1c1c01881030103043c820600c407589400324011400c0003070300c030440005001e0810400c15080e00c00161 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 893058111 1250 893056861 893056873
    0x1b020307110d0c0314101806111e1308011812020708031603051207050712090f0e0901090b0a050702010b010e0604031704030c080c090604200a14071b0e0108 69
    0x41d40e041000360841a4917042400381c1300201c0c507414400d2281a05085811480180c032055a0030f14500700c400441e20f00d255503400304001003001e2900c0e951f02c0c1c003004625818940c0d40701c12003404a0581c08540058006500b40b60501d0f85410843d41d122200900034440301c501da00072200306a9860a0038441c125040c0c000703108025884a216016128080c000d051461030001c403d80c0301e082c0880100c0320040131800c0410f0000134403003400b2680c0c85446c1d0500340b01c50f2044c1040c0d1540c816217034074490121a01c080c1d01c00210880001e402000749154800c1d58690107045c0541600d01400044442c00010740c0b07403400d00c1003a03610600150508840281c40170b840c250458482e14001c0c00001d598585030142000000000351070725200f0b200030880310300503001e148082030421030705080260915200e281404409900e101041001c64124042030503250781d100b07502d400c191a24410020f094281d404c011400c0428001a4075640049690300c0c090412201d4030341340d1345240b1017802e02504000794014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 893059361 1250 893058111 893058113
    0x90403020a0312061e0e0f010602190816060506090c040e060405040f050303040c06031a031c090b04080a020913051005061f030c0206010801020a170a1b020307110d0c03 74
    0x5003580c0c40c4080c3e14160081031403a240c2a100f0f02602c2c00c41054020b85141880400107016220905500541d1a401250140d450250020354424480c00c04400d4080f0b014003100400084500f110740ba182280741148001070079043c9200100f4040384d070540100121000600d4102c0c0000440d000c0d181c0202001416442c0c510034040200001041200ea03403046540d203a02145d42000518444c030300c00d2202540c442d04105008054403280316041b1200142e40d2800740107580d0101e04a04901005082c404500c4918a411a844404e03684851180f03140010702050184020800300d006500981d00d8407100d07124160303000d030025103040300a8100e0b0409103100e4511762503038201a4105100418071348520021101120307040d0001c8554901103651102c04640c100c0d011310650b8010030303a60002718100744100a02400040d14109121090f1500b80c0014041c0d1000d40d02c85011401d50300341b480303e48901500042d40d40c0e400f8100581d4040062031010811785040009200d603164000007202c4000d181d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 893060611 1250 893059361 893059367
    0x7120e0a0609210c0504090f111909020a030b060c0106090e0c060304080d060504020d090b181f0204031b030213110412060b09090d090902030c25080c0a11090403020a03 74
    0x450a001c80d0500300d135010008040e6680c0c0914491130b4000c41c591042400c007442e025200c1800031350801e014450b41104145112181c2c04800202ca1240f1400350b40ea2044810480060075409000c0c0d50221001c1000710740400150300180035210704803030170040d41d40041001a80c404003040d05a9001d04200001000201050702814926140d9000031907440c0d1200000790a9800c080c104004141d5100c80d941c06000c420101039410294844481421500190340b15490f800d0311140202c140d0003900c40d00e0620304030b43e41241c004540110450841c103805440c0084100940e100503841910f0681c200428000c4d903100c1d6444683c8074008440c50580f42c00d41a01c440024200c0543d15241d50354500e021035101c00f036001f0310a000078000f402d0034480001003d0072105441e004103104503c1841003102c5203903040308403423007142c0215140c01c460702c1ca2015040020130703c070001000e401000c0381c1075440b10000145a00d443e485035a10311521708060040c040d0740b0100322400344c010303881415004003180c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 893061861 1250 893060611 893060669
    0x11109150409020d020706050c09010f05160c0f320405071b060902090106030e0613050a0f05070602010c0302070510050c040909051506040c090e0c07120e0a0609 71
    0x2240c4803941007035510801c0c001281c20008140891070380020350b04040200740d100d02984040c0c020040d60506203034000080c022000c4403440c4050000004030401110306100d881092280d1201742a4034250304d903c101e614010039031040e01e00f00d28a4184d60240a00c00311b02c0c0c1e101d1115200d0342c14114071040c80401006d0301002d8070781d40c2484282d82038010802c1d120300c5d16803651800340801141d07141f0390384140541180142d01210030145041250105a44d010480300e41110700000030362150007003418003600308507022800074403545030030040750300b00a400700c0c0c0d43d0100d42581d002000440d00c00003003039040e8031840c5402003030f42d00100009031080358240e00c400e402c400510240d500b0b282d191601d4a04980e803070130023a00c00343e010494440b004408100750303d910400580e410700401c613000c54044c124011038052000344041c0c2d40b0000307c03a0a541420b8955864000c22225000401244040c15803001104068029244e000c80880c2d1075004032003140c1141c81c02850640b45a400301440b81002d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 893063111 1250 893061861 893061889
    0x303020a110d030c0f110411130812040b0c03040b120406060b12010306381e0d1401112b0e070b070302010b190e13020a0303032714010e011109 63
    0x1e11b071041e1140d52036610600c0042140003540c207a4074141c441c10007080c40c2c4294040e0420b940031044100c0d28038401d1041d80c003111020003540b62036003498035401342140100d4012950708d1a0109924482c055a40308050055000d504100310050300d5110034281c6220314071025034800c47e654010000038030194012420034880101d48071001c001c1c07421030312900c001d2100b154400c00c901a405289494070f0500b11019404c1c0702c401030350110034613011070207211842001402240000703412103035544081d040a01241c0c1c0c40d0420300d6841100458406c00200d01070f012858030034192140c40c20030245c61207010340c0e40741e180f40103244103868200c440d24207a02c00c000c200c046548410209106440f441c009610b00201808003615a50400001601030f0400801440c03284000400410168403020349100503aa05480c2c04210a40b640c82c4a061058445c0e50b6803101c5d181103200d40f001d02c00d044060184110400c070085c419405100800b50913110754682800c04c0250401119003e458800b09010840e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 893064361 1250 893063111 893063123
    0x915070b191503060204060e031603060b01170a3602100e0a08061b12150f0907020d02012301120309080f030703020c040c0f08041b0303020a110d030c0f 67
    0xb400020402c0b000c0d000d120781c4219030300c0e034010805002064004028000c441c03010b4000301102078400540c40302d568258480074081d503541d88600c5160340d209001e0b01c8a410341c4480560344030308100b03c1460050250041101092400403500c10400d12a4410000503500010314620f00803801c0d02044a1000350b450310005100d030300100e108668030340c41c903480014140400901481c0c40d040d03200402d01000303803007018020b18040200f40010b10440d041c00e900040202501000002500e000c60f01305041c24044035030042103801008081c55000410080c1e0360b80e03640c0240031219015185034070340e04801c03075000000c0b0910750050000c854030010342803011b0b00034600300d16000d5450f0a050b060200640081c082da42000a03800c003030603010802907010400940c0d04100501c1000030080144c1c20041c03014042004142c04a000e2142c40021110180011200c5c01c02c560744d64680659103441c680c100312400c400306a41c0003614070307110040004158140d00d5503a000012640c9030300c1441c10b0407600b1600323 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 893065611 1250 893064361 893064371
    0x140f15090d060504060b030d020a082d07051501120f0516080a0b010807060e0f1201060f05190e0c0c101803020609060108030d090c0510050915070b19 66
    0x450340c4260708181d840b402407000241c9810a42001e0f829122464081e41c001d6000c1d4002810b481e80c0010450792054104002c280c6680c0060200c06405104d04400c03c15041e126440090203074007000108403480c401d00442d0403012190b032140711300740401d22031000600c000200600100c0c80707402544100ba48190700f66109038510310341c55040d803030780360b040b20a103944000c55120410030344244085c0540540c1c2c4c0108053340c1b030304200a18190b011400075020f203004800030290743d200c14140000d8274420074020301140e07860f203003e042225480d21500c0d20407a503007120560800040441c0380c05907041010002556030321100c41040e941e1182500e10024484d07082030100300f2010344034501c0e609000b048c01220101032401c00916120f0040c10306a10350300814010401003800004846c1e0031402120046403202450900d5620040690300071074025805c5042524a0799206009240400742120403942210384040000c40750300504500a203a04503140c0807038031007a00c80b035003510314800c0d105002c54 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 893066861 1250 893065611 893065627
    0x80906120601090b09060703110c03060c03100603290607080a1706010f0f120f1a03011404050a020120010218091f090504050114011e140f15 62
    0x4258400229440c0c400c00c0081070181c2580c0c001c0000c402407101c251005d00b00020711002070b01d50300c2201d90050a000c4040c502c81e4000c07000303101d25030104500800391411391505021504055000715182248241c0d9407502007400780c0240b20790200c0c12804614080d070005100584074110080041c2030758000c1040c45040e000410203030081c506281166240d00c0203c8400110300d0040381d001c0d05880c14041c05241c10030702c00f030303001003003c0c00ea4200d807520b40081b1000f400343c140240810120511024240001d01810041814150301e06100940c02004a903e4030406103001c1101958020032507003040c68003c1c00356114804841c00c1c07800c2000030040104c2104400c500720382c8411411211904100d03085001403400d80c0229521606101e540c10000114203200c0210032098010540202d03551404103041c031200358041e038940080c5005440c101d5840d0000034051007040410071b079004032002004902d21480100304603100c000901102d2031f0b008901d042001c0d40303094540310108194180050f003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 893068111 1250 893066861 893066869
    0x60c150a0915020c0601060c0f06051f0306060509060d05030a0e031f051f0f180e0115081209010c020f120316021c0206190311030c0a1b0c060c0809 65
    0x115900d040b90742c0142d0b1100c001460340d007420b805a004209000c1c0f07405d0b000020504100e04040800c2e44030a00140c2640c03131100c2d2400d4800341e403c074221045401c2502000f000720a41c001410b80e80c04031840c4080b82d0390642000842030071100d0040c6260018001c6036811809200503500c0300a00500f95855500040740e0203006d1007140303c2e490442a1038006106039460040c00c020809514541c440c5080ca05100c030890580095100b09002c200d00542c03800d112040690104100c1c1100700700038486064010149601e105281c000c0391240c1c080d2012840b4028102021210040810385812902d58695002c05c000c100c0300c1001c2980004071040b4040da90030091004082c00c429100c80d583e603215641c014005860f8802c8100744d280314020090320096603500007a40c1101a0410a0341b03c3e04000c21012400f03011481131130105d901c00070007071110444ca100c0241000c0f490341c1e6507140442e0000144008801030792503001d04084a13989050080601c945100c0c1c50301801034028500d0072001030042 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 893069361 1250 893068111 893068133
    0x11e0507052d19030f09050d05070c030f0308010806090105010807030f0203430810020f0c0a030309030305060d3504030c09200f071e03030c030b060c150a09 69
    0x4107030043c0c00405801c10058040c484c500420310014401c00c40400aa940c180d03468500d05155402e000380400d481c003c02080e405210040e540c030948a4a6800c01458040e00301e11082c01109580c2c0100000113462400510805048401072401491054a151a0752244028803a41680c141c010140200d0b0040a00386c0400307041c00c0d4584100c060101d4800c40b524081c03100080c800c091929010040050a40c0000d944446003561080181c1e100003410700d8880d50301c180c0304548054081d44107a00c00340740d0141d11811001c0d010340c6061041c0d41d203007020004202e40e8903100502c60180c00360110b8103028030b161400300082d10100b0120074010402c9819a864016900441d0ac43e8010b00b4140a15103640c000d03800c00440c400440b2282c40b02d4078640703450501076021100c6012001007044024003800748864520b1828a40305002d00e807426003070040150000038400300110b81400d880d040d10341854021500b1100012019108a40f4242c2c074210500344090889070156440d0001c00001c01d00c01c03a10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 893070611 1250 893069361 893069377
    0x3080c030f0411010c1406180f46030e060c0307030804020307050d0b0a0c0201060b042102180f070207060c02211e0d020a080930011e0507052d 63
    0x140214030304400c8c8109080075100e46a0043d0700000f45208907000c00040300100b01c40d0041510ba81109684520310f12600c10807850034020340e10701c2c0c0170f180380701c2c4580950540500965499604460200c01e004d194402e01141c0681ca5004005205c040b074400c0e017440d50403600c000d00355401d01e030b41c440c001903194102d00307010344132901081d0500c100e08409200d0f001110809000a120b07091601d503c4a849000c0c2d4490383c00a6081501030381c4409000c45648402154024039000c1c1c0000007140800c640a0110786040b40c01400a0200b91014000105c21b421680e80381e90300301150816600740115184d00403052201c8a211621007842442c043c031101c64800b890710581504110301c40c0549150140e0001e9800c159040031748040007050300e02003100c104803410341c2c0407152840c1c03142c2002c0a1402d60200c60809501c00c0c81440180c0006401070712292201a15050101450380c80000442d0400e4030b128010400c100403404080d000b0091a2810440d0400d181e460f43d070b40c0300703082100359001d014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 893071861 1250 893070611 893070613
    0x1a1302091602010f0c0e190306050106120c0905100e030f01020a020307050d0e0f09041103010509031909050d060e150a0c0306080d090b031f09050403080c030f0411010c14 75
    0x1003200085a42441040d030141c501303a80074003004006800242011100c54410360140030258008100c1720b0a80c041c1d48003c55005008100319030b9a084010190070202da1616020784c00c00c0300900706244285900b0f4151a4010500550303051341714015170742c032036018220176018012103100e0300340c5010a01c02351039401c1994000c1c6d07503100d0fa289849410505a11a00b809000c5a442d5040c044d4039007800c26060b01d0000d0b228a092a151814104079841d044154940e01d5800c20f8108441c109001c4003070041c114044860720740d03a00002000303844848071401210340001c03001001801081068001140501c5444e0540d40303600d80032500711000720012241405400e480b6849806410750511800c00148641c1c0c0140016880b50712004144200911901720399040c040b01003008817010340ca07039021400703020380742040482daa00002009090111810340102c3d0079080050050084481213921800501d03000c22034035900c0356a05107581343c0e124652350400184030f0078100059504d281440060f19180 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 893073111 1250 893071861 893071891
    0x3040c030212060106050313023618061f030b070c150605060a030b030705190927080a030b0a0b12010b1c050439121a130209 55
    0x300600c40b907041584501202d592020004001041d8002c040d250404162541784251601c2800014220341c0804121240d003c2e0340c9032202c3c101006c000c0360000d4507050545540d095656000c030680e41421005064403590440320018010403c185c0d030801151391003008011029840341c442d09031104049031400c0204d514400d04070140b01c020303103101d490860382420a20a240c207080c0410550b0040c0400c000505450341d0904000340d605110b8ac1c800307000c001d050103184200a000070740c60304070640324940c0420311b4078511f601000c3c90031003802a2100c0c0c03466488000c078060741c0c4801441d40007540ca20201941c40412403199611078010034024148500380c2601c489510101001215043e03100701c0082d02c3c10010030f440d04841111003085045035010000e03403903a4500f000985501e030100c001140200f410f00e07201100c2406185203511940001d1130801d010b460311010135507100448006000d00601d640486c7c03450240f0000b40354024040e40903004040650340c007042c110b1400b80e40c1080b02a400c9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 893074361 1250 893073111 893073113
    0x31214090f0106080a110919020313060f09120f030e01060f051314150a05042c03070201081611070e1e060a121a04030c02011b1203051b03040c03 64
    0x24007884021303010600c05421854802e40c1d030703040ca010399200760500400d20b20000a20668600204004a0700c201c07070159501d00c0c107480195060310301d0f0300c1c080798981d10303010100c2c40007400340c814030f0401580014001c00840000170107441c805c030034008010415403a0071080c00300040a02801008161406060314401e04200402c011004117220380d061345031400840c4290a8140e51146421441d0007051100f0300d4426008038135140180c0e001075800c00c1c2098401c5084802091311018842c44400c030424102e5000541c1c3e80c0c44e8880e00760080d0000b400400468442441941c00b0441881d103404c0035100c9500e4000124100300c0e5641c070404035148000200946000150a08804c007044061b112115141540c0010001e002c0c070f025401070940c010014500f00005000c1c1300702c44605440541005160500e002013080328400400c0780001c02c002051070901c904620881d0b00c0035402900e81e01c40e0001c9290881c02008020440014803107080311800e00040000001e43c02540540740002103c0c2c11 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 893075611 1250 893074361 893074363
    0x509030d14160215150f03161e180f060e0a060801110408030d0c031e020301050f01080c0d2d0506040b0114160c03200102010e060112031214090f 64
    0x540000c1c1055420903010248800400d001c0350394000751401e50030328100711725408075841c0c240c803400d03142d014800c0301c04000c80344420640300310468200da5803200540000c2403031459402c80390320070f800c50001d1981d41402502955008207a645d10b42070000130300c007075a580c034843c6004030a94960003895600c00040c46008004e00480f0004404107015a15045c900240d081c2d603445500100d0b40c0e040d03951484004001d00c26084107800748017000d0704400c844101c00d00c008c000d600a1050b0751103042c82120403045540210b500c1c0748250000c01440b410490044001c2e000f400a50340d2440021100340e0f0308200e07001c0c044030207030b40e0394100341c40c0060245484014002240c0c0c0000d40c89060208aa4080c0071343c410041c100d4002d946004240e9425248519150440e01059040200410840c6004542d000300013035502440394030981c020b20004201c60030283d1103203400e020300c154088034642c20748003090144276461000c000030100045c0f003000e02605244008070945d048074140d04201076141e40440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 893076861 1250 893075611 893075641
    0x151008061002010b030a0605040804050d03050c150f16210606031a0604060f050d021818091002090f040c030903170906071b06050103110112060e0601030509030d14 72
    0x1990008004d446a640002580d5411400e0001c1c0210744481c0010104035444040e07400602c0090704580000e40285070182c5503400002859031030784200b82c001c0c09040811600140110603c82c0d03400c0131502c0f520002400760107000050414000c001414000210700c4124141c00d8500d9100c000403038030308051006050781e894400740c2003652010070f001801c56450804880464545040118a03d08810720a80301401070754001c0c5402072010461010420082d0364103101c1440031507082c1413203084488186400301050383c2c081c03400da010525004003170301154000e211100c802440040c103a681d0b00d001406032445481e41000194079200314101301500030501141d0010030064852751480c10060340d5540d004014540d10400a8007040c40c81440c964807500d41d030a540100c81440190784038184003451846441d021400202c00c3e070012581d1030860b2103401e0507901c2a41c100035007030b1200b00044001e00307005400540c190004000f00a022552072140d03404451008115000c0b03480e010400c641a90 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 893078111 1250 893076861 893076889
    0xf0515090f0609030f060f040308090105042001090504090f051203042127150203041d07031e0b2b0f03030e03040e09010609061d15100806 61
    0x8a000d00c100d003055a035600034041c0010094a0941d01c400300000003c0c6440c0301c4155620803806058180144012a19801c85c465070082e1200e44568035086080ca0884400b254050701c50101e0300c800b000c1844100c0b19070001040145003007104c0c591501c00040448140f10b01c00c9400901c4d080300e40003004001e21a5811085032102c145c2d04500e007680b100c481440c0710343c00c285808201d0b0981140310764050401280c146440030034a400030308003a00c04404542150003240c46020044c058180306910000894060340d0b803c90107228110711402d582454000e001e004601456141d840f4107170850a41e202e840e11024081201003501e9408034140480002e04c20310010035040c0741c00300f052403420409607610b4482d03800744050004001ca41000c400a05d10320500c019180000280001c200c14018a20350042400310000c0003c00c0c1e03108200c40031100c16120351403c44c00340181016010b8918101c0a501000044106403003080c00000070744602e899411010104a810303050255905001059007061 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 893079361 1250 893078111 893078149
    0x109110307062109150c030e070b1206030a02030a0c0303080c03010b090105071106030907181a06032802040311030d020c04090201090e04050a05120a080402100203130f05 75
    0x1e040540080c007100c8003501201071540c40600340c50b01a10f042c3e00001c2140c0d0810034682c40c0048007000d44000d007091005034400642411110050307008082800401c4985609049141010760f810a51140c440240010f034940950018000542c60500c814411188280e039130b804e07818258900900b01810103061a00e20901c140018081c81400c0011100d16100900345552111590710344950801f1803541001d400071804001e2115900d0001100010380d504064803103400600a41140d044a51882c0e895140341d0b0101c100700e40c241055001141c1003010081d002c05480444118000d1003a640c0454040540d8005000c10074001e100202c00c8400100b1070240510312806c0380025900c99400ca20035106d00d54810120341103a0040c110400103150f607106140303080c0b50034281180c440803c0070013550340e03010300300c01c8001c000d940d070003141c0421031a03485400090304d6a80a001c03000b43d02c40140000d500c4101304a22421032540f00c100300400059042541c0b040c2081d05002c5040152403c0c0580 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 893080611 1250 893079361 893079373
    0x112091a011707051003050c0724061202031c11030f18010e0a090515030a14010c020a03230d02190201060f0b090f0303040e0103060504031805010c1401020903070801091103 76
    0x100341da4001082c1d100000314035010606482303418482055102c1c100c0c1c01010010604196845488160400349590fa4400d004100c0c0950710f1b8944020700719a07100081d815000340101d1074510500100c2440241c03c1c520384020000303064840140745500816805104e8a03000c1818807400d840102942c0c4200760a10342000050061804141054030300e000d969080e64440b800980920f2a05450300b05104009080742c061003075a0409000e50060144200015402c08a03140c20f90380c000070b00c0303152440d0b0580d600d802c480e20314041040d00c40f1003248000e084220070000d00c1c103401c0302c500140141c2210101d1084072034a40300406070845141e81d2140100780142c88041007106040e800f0f44e040010180d83e0140607001450000303007144100d0700010003030585407001005002082d801140704510075111f501216041d049061800042803055900060a044c1c40f01c1c0062403034820b15103008030000000d41071001d0b010010b17007070984030b40002100780e55500710802400300f80c4c905001040c50680c05003071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 893081861 1250 893080611 893080619
    0x30e0906150304031d27010e01120b0411040507030b011211180a09330b041e08060c070204150806040219082406090f060112091a011707 60
    0x11280002007010f0203000c85d41907110fa0808003c04440c200c0b040c0102441d00028401d405040a88208a0410001842840041034000c080030132207042e03d000202030074405049542d2560740c1d803402801110201c440f8182020f95848a00501d80188401d450125003004243d00041c14100700402d020086070034208021a002e03c048115484071600c42c3c1c14400070f1342d40902088000c00b00350b0044400343d282140c2040c0d44e484000c1c0d10001850304608082000309020708a5401d00010300072507807401010001045003003415042c24404d00100ba0300c50200076550005141000b02c21030310722030030f014009420030440c0b81910072629109100c028860341c2c0c50414207156a50722000b04001d01821010690030300742d500c0220b20400401c48a01210b52418125442884822240c15604030041c40d00c40030401c0c07072400c1c2d1980751140b0311615444001c3d80e0798a00440318280500042c140c1641d03a0b44110020407000004c22a290302c12134401d0b0940c0d454540c0f400400e000b01c0074030240b59080840240 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 893083111 1250 893081861 893081899
    0x61a0d0e28021809060f1005060301150c0c08010e0f060f06060a020708070801020703030c0f0f181809110d0c0b0a030f05090f07060e01050f1602030604030e0906 71
    0x1540951944188002001c0319101240426041088112464a25208000d202d10300001c0142c42644c0ca454400380310f4440c440006100b22076405890741c880c005200600c220200400d003029000f100e803802069091168a8121141099030448011a51144500c803c0c000042046101030f0f040348000b080e5601c0c20b8240c809840d04040c1c0410300c03600c1c0c00107001000703a00c01c120f06400360040c0000e480e8540c2c0d0f03982042e0b0003540048003c802007400c05806900c9070b4001c602e90080513205444180b02c201076032904071003101d0fa550340395011440b10344010a010003107800b84408814862030006140400d4182487c901c420610301d0761080810315010000514800c01c50401c459554191a45500f070600c010341c082e215011404102901d0b00b002c2100c0d071100003402c0200e5000d520152100240c6455048907400340306030110b1b010440c10080c810540045800404202010f0511010b2055481d400603041a0042c2c0707081e000500040744402c140e1a11086860b0000c80071075800c0f4000f00c61260341 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 893084361 1250 893083111 893083153
    0x60d050c100e030d090609050405090c090402040f18060509031e09030703062d290d050d080f0105010c0f03110a0b0a020a1b08120901061a0d0e 63
    0x550284034007181031403001d4002c20707250248020050940307240c000c0815004094103030b244180c43c0012804100003400b030505219a078010119031b8080c0c80d8a142c16410f1040c1d80744068012a00180d13a001c0016a10805102d07040a030804803440850641c2c0508002c0191031002d081803500e038000b0000a00e0809110024141c003200c00c9041c0303900e032110000007900700311880d40042c000350b0400c10007003904008580302c411446141490100050b051515501c1210300014040c817206040d60001c10010001a52201c400c0c82c0043c006813071004c0d03542d256401c1101c440d031000c0210300c08100f840705480f0802c201e280589030078600400147c1003911f5481c0202a13811016080c00301c82482862524014003800d824203030003103a110841d0420741ca03444001d52100d0380c0d01c00010307a44807940314940b00050600f10120f400c00300030350030107512411100300f29101a092030202e40d03aa079000601e80420501101500355000c007090f8840c0000700c5600203075180e02103241c0e020380004280c280d00d4903055500c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 893085611 1250 893084361 893084383
    0x2030403150e030a030237050c010e101e090f0201080405012a09090b13051f0305030d0b0301140c0a141303140a0b0c0a0c1505040b060d05 61
    0x1480101e00030703651410300200341e40000d41916000014490301d00d650140c0003040703294000f070b51410030040c110800b0002d070340c26a03044181e4100a04030042020780700358041d00407181124000280e401d05142a01c3c505141c8402d006c500d05d885001154420b0648001d0101707410b030341d440070f0110030510781e00c0b0094800c1d602d000905124008000c41d0900009501c00c5040002c804522124941d206503210303800c1d060b0f6030307100c000102e5000c0c0200b28405e207070140410b41c5c800034107507190300c0504002440c007402e001818800118800a560f038025141d01c841c4070011801200910b644200301c40f1700005544030079800314042ea05001e21404290002001c95a1244180c00090744035107000c442100c0300d50310003c010401a4001c910308410406a940040440e0701c200c0340311548180b1882d0150b291001e540c00984051442400184074529084c0104802000351401c4a260141391703a80055018661480c00700781580c13003041004101d0701010098002c801190040c40d00581641c415030ba552002e16 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 893086861 1250 893085611 893085623
    0x14030f0304030c0e070c110d06140f0f18100903020307050d050702090a0c0e01270303030e0105090708030307050903150405060405061005030a1412030112110d0804051908060a1d070602030403 84
    0x8c03081030200d544c1c0181c82280403c181c903030345400e05030381c0c0440c00c2a050300c0183c1519a014003003103261442070080c08241d0410380c003408220322000740d400c000741601001541540003c0003080c0002c1e8040c403c50301c10b141c4c15104d803600d075104c40c0188852100c00a10146046d4504091032285541044078141003a00900e0103ca5000080340f0311302c103107001020311b40d01548071410013104254040c2c00c64200310b40100000c01550361601082d60741c0e01c040c1d10480100b5001040887e003141d00c648010b001d000030240440d800d08607640071801420b0310485080c2c40980000307040c003080110520400e81c116940c0004074145a08081c00070b0f03100c0c2701034140140682a2419030a50410007070094504010483d41c0080d00d940c1c1d181c803d0f008070301c0418400c44071504e040904070300a1030420103200c3c0b050b410038020381c20a400c00b07052000e0801c2d240c40d10750000c8800c88000440c24001c20443e0b120314404030000c03e007007090301031500b900d0b500c8610304500340c2c00c1240c088c03121030b900000799021030350401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 893088111 1250 893086861 893086879
    0x2100902011d12010509010204170307170c0102070b161e09060c03120e0a0b09070e0c09030c0d03110c060309030304260712260114030f0304030c0e070c11 68
    0x11002550324440f01950381215401c01c030401c81210b4042d13004d001200c231082e5100c000700c54460041500d0380710f1611b00818103150b5070580c98078507003000050001303070495400051a00c442a01c1e2040203040854080ca94044069094546940d100d95080d5006581040c90b900c109900300001d0400500da02800b8100101d800c18001454880c4003402607102c0803c1c01007000d407902c030b0001340d11040d41d03090650380303030a03c40042450b403080001c4010888001c4401c007690741d210900d07900c0d441da203c00361070341d03051007400401010b5955132802540c045200303848640342400c0a840903070500d0030b406c082510612040c403c10203801400310440e603001e43c0c4506100d0080314a00690b46603642e540000506100001c24001d0410840036000f405d200d0550f1208040d0400031024075051241da003496201106241004000c072660040000d41a0300303004056440e0720190045280c84d680041e4016904800c044104101200c01d03000c00b250000f54904e0a16031000854907818280e016041c4400e004d00000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 893089361 1250 893088111 893088167
    0x10080708070224040c061706150c01020a090312030b0105090d020a120b1e0103050c10020c061809090a03050403110a031a090106080318010c060209031c0210090201 72
    0x38411904401070103c0e0594541015648010030030314211011220740ea51004017107402c3c0d000d2610361180c02039600204900395100303400d0044800740236500d900902814008100079080a001134101180c00e581d54141003232942c28000c074500c2c3c0c4a02d09505040c5003c04075a02079a1240444210090561b45440c115486201007506103c0550040030f40c402a81c960908115203100d5050050703004d07010180090b2002540f01410100070310000384203030712404541289040c507280241e104a0140140d9104030821408182e80d42d00010010f902810341c500c0042840c50031000154001f4188030060120342419980904070384204e00014000390400400f03103400d65200704400010750340c000c040c440d52542d645030103c14110f0a03200011103500b400d6002c51241400001c0e103001071844403010f02c61a5500b001586e83e1840594150b840640030400740340c403a101005044036021a9001205100c1c0240c40024244090760700d074240e070103007804205401f5030383c0650010003140d40c2e15034218001120b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 893090611 1250 893089361 893089363
    0xa0b0c03040302040c120b0a05130c09050907170f13020d0809030111180904020a060e0105072112020c1c0507050a03031d0a08030a0b0d0c0b1305100807080702 70
    0x102d520096006080c0301d075180c2d105038880624115125807100a020082200003001180035040c041c10b600103031030549406d58040c0301e400843d50404070341030060405845034007040c554201211000c010410344550705400508400c201c3c0c2d80070f020380032408420305004d10741e10741c00d50424401a120720825501c0c0424040248100d03084004010020411400348849142d0103800103c4075007a200c1c030342c00c116003190410800480c42140d00400d41084135080084c140c4211641c00d4107907042000c1800128000740348186200c64a0450b070884000880d803d0b0801040c0101c400c100007019401440101504200014203100c3d00074001c100341820388035280111401e00624001510f0741c895075502e03806054060307000c00c507009100b014600c01411200ca040340e80c1c030800c94008001e031204000003140d612140d840310203600c10081c5560b4060900d42c0b1485c40b05506600f045980301d0000038441d441e4200211018000d1009954000640d0002d1401800c039030f800800550500840600042c22144 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 893091861 1250 893090611 893090617
    0x6090602160b0415050d05100e0108030903060f27100c091a090402120a0e1c0207140303040e1f12050606010309060b0406030807021002010204050312073f0e0a0b0c03 73
    0x81c0035001041f940c074000484c0408400540b180d0490b1440080000c286100048202e510301800070707004258035100c0840f21501c009006100c03a51880c0000c05082001c0151000009140d0180c001401d105410805100850791110510010f01145010411040e100f884002066881e083c0106880700048008103029201d081ea4104060003054100210301030160710001c9142c0380401221201840c200c1d80c0f0030b4050485c00313840c01503805544100600c015404102911580290969091035610036201c410100c1c10341d003220b0030780031030806003030780010009141d0001c0000c210846686099511010b40311003010342250304060321118860180607064100c00c0641c440944100000b81d52810144801c0d0003881c0c0803403068210124021100703105000382c03001e40304001c01a1101d6022003901e0003007a03100800848400c11407a00c40c82280d00c02d004041210315824081c4030010000e0301541401038100c82c41401400010340c4002d0103500c4040c680707030564840fa04003640e140040759146103140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 893093111 1250 893091861 893091877
    0x406031e06270309152012120114030604020a090f0e070b04081902090c0a0c4403071d04020c24040b0a0902060d0606090602160b041505 60
    0xa08210512140b20b400c4000e041c00e40740665110091a61034032050303000703d0805507035007001555034400c250304c2540c1a806180041c038000e084500001410001a640f40c001c00340301e4480d144402d0042022a01c501d20080d1004022009082d80b0314080e800500484594041c25240a62701d0704000810056540a0344444e08810b080b01c003070341d0351200045c0c0d580e4020300032140240100b000e10034400c908100b030582c1c050b03402008444659a041c01c0e001f2640c003c3c4103070700c003040b5004000c040450241c0c1800c44504030205400c52056001c090705031803540491000e40e03018883c003412104480084415203400190b0b61419400c0340300c4146150400700c3c0903091070350303000307100150f80c2d100c110340040d071100031804086441038940100700d07210020003000c0b50081c0500b411400020003070600c42e0b22050801d80700900c00f030300382088550304004403011a0025000304904000a000c003540400100303085000b0121404a454101514202140a40c0c4102d18035400d00c030103da03945900540036030b01a5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 893094361 1250 893093111 893093141
    0xc03060409150c02010c03020c030406081b071505060102061303110718060608060d050c010804080f070302010501090b0f0d08090a1509050a0905011d180109140c0406031e06 76
    0xc80b10420000400302004002c1c090340c42d080040c8411402030003511009036001015605181c64a001591441d0b00140b12000c3c140c000301074500300c21503520190074003600581c43c0041c540720f04200501202c4003d040181550711520070805086480040800400d906240001006207400007441c80c0501c1d50700101690f1403810000030036400300358400c000f00c034465600c07080141c48400030b00c0140d02c520040503285801480c101040c3e5406048002d41040c441c1c062140307030044540c2d2900c0c81e60441a002c40c0143d44400040140f18450701904041d4070b4201c0703441c1501010070340080d40a41c1441c400800c010700205912071107940301c0c3d40c44001040401c000d01100240c0c14402001c0300360f10f0207040d101d80380131040403034030000324030466040e5084c2c8a000d10340c48400c80ca02c040c00d154020b00c402d03e034402c40c0600260703904007806640d140c10f1046c0100204004999045410140d4028101c0d00803890680c08001081e40c070441025800c1200145503421112801c00c40c0c0a0541e5461281107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 893095611 1250 893094361 893094383
    0x20705060f160305091503150f090a02222c130303091106031303090609180b030c0411040e060301050702071e08060c0405010809071a0c0f060c040f06030608060c03060409 75
    0x11600b0f100e0000c4d80300303200031550030f51034200c23031f10812001c00c1c4100034486d00114002c0008040c00a50340c02080024060041c503401002c04030900c041d411900d0b002400d001e1070a80e004500103c0501d09031601c0d01c04505d1600d641e2914101940c0301009141c4090105500c90f009001840b4210200b4116000003916550303483c50004009081902801c00860000e0941480020414451259901178540008c2c1d038030114a010320201002d003000c00c1d0740a6241c06100c0e020a440ea4a602c141c0513040c51a1203251744513441c06618224060000b040d69000b030b4106001c20a905501013160404e031541204040105440303800d030008907a2482d0003450031807084005101c107901a9001400441d0f009030f0310001d01d40d03075500482e5202c84c0c241c4a090854200e19280800c00e0a1890150220942031001c50301000301b084016450100262170004031400d00040a210f1010502c00d90700160449003000d01545244c83e080036a5141c00030106038000381c000c40031800c140d48c1c680002c2c1c00b5582107210301c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 893096861 1250 893095611 893095639
    0xa030c08030309060903070f02042307031a04140403030507050705030c0303060f10021e0f01060923130219080604050c040c0207080c09040c12080a020705060f16030509 74
    0x81e999000740c0b0401c6092203007800049028400204480540b40e124402004080050342400090101d036086110040300055031001c0030b81c12901040c1c8203882a81e80811890094000261040c0d12092a00d00840c2811072440d0300c0c01401c80403503001541340c0741c0000c2d00e44d52420200d885018490004000c0c5c007000645c1e02008a0000107103029a50403036060400200c074200f0440400c1c2d0012250303004d6042070502c0160301048024041c010680311042c0c1e6001c290728200c90b42101ca013a04000308442d91003514142004403c00900b1466030501e00302c1d43ca46c1030a650203455441408002071103406402c0422224040c1815018001c013400030440d84542854a045611190690409406031340791000004080d44001140d40445158078050213030349040c5400e1110302c1070300410545441d40309540000f404490842c414441030701600c1081d80f20400000e00a04040640d0300241c0314820030f000c0030b00940806000c88104c1b44000301e0391a11004a441d080d2500d00499510903446408126504 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 893098111 1250 893096861 893096863
    0x3041701060506160b09031308070305120a120203040501090c120b0c0a09060302030406060e0702071517010b07060905030a0306030c0b030c070b130c120302010e0a030509040b0a030c08 81
    0x5185511644000e0181076140c105100349802002100c601003040c40c200e10300403e9888119075001001e1505891910303552102c2c0d030716a1101c644c0090b18640c4a880304200744003060040c4c0e41d0489091004030320b4a10200300091000500203090310b000c0340e001001c102040000d40c01003450b1907100c04a001032665540e1079551402a054055403284040e034001244c03a00c40300c1c110bd201d1201c0740c565000306410031400301c0094100500c00c44030540c1d9400041000100b01a80c0c80c030805459006080d180e0426030b0140b08400700d18044800c0c40700c10340510294000c0c020b070b0b2605560590030740030385800781410b004014001d040d0300a001400002182c0c06402e03850b82042c4152030040040c00d50440c0d42c1c4030110914441210b902c84500001d011000018041c0c440b034a402280e107145c2422001c0c011f80301c0043c661065403100c55480700304460b01c801c240c0c0a0080e03030406220304010f441110405e0f20064860300c9010790a41c4525a1150784404a82e1800b030311201550704007502c5103510341c51703020302 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 893099361 1250 893098111 893098139
    0x411010e0102070501080a1d07090603150e06060d081306050901030c020c030c0904080c150402010f020a0b0c0a020304180e01150b1c09060c03050121170a0905030304 73
    0x11500068064000500340e50000a650b002c0b244181e40300e2030305903102d604050041a00700014403d240310006542c504070002c01c401809880b1105c400544103145151454504c607000504411003030801007001660340740410381d542d000038155107861100c40b96113000d030358601c680100d2136086100e4203804a082e541c0800a03014400c6c0030788041040305040d602c10790355540f144500d60707803592042412008505003122010f41143c07145080380d0525184200d11401c020300040c000d0b5240c101c100030801590790015a80510603418006402c2c13541e9070381c4035549100001403010b402d980c1c0c000b80144005e0320810854009042000141101a1700c4166113401f50035281c03064403096080c4030ac04907011030820345130320844054828191504a4560b100a80300480d041c0c81070046640b0070101010415a02564074600c0c61036074001000d6040000e886c0d20a0402c8203041c9010050005090004a04400820120005c082c440b07440307040c100000c403140162500416054003002ca40042c0d129954819 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 893100611 1250 893099361 893099393
    0x1d030d090f0501091847060901020c04380907020c090103030e040f06030605041211121e0c060405073002040f0614045004 54
    0x4581807660740c8800460f00440b0381c1c0100360351406001070b445501c9900b68000340011a0001401c1c54401d04464150f02002d0350184c0700c01c0d1703001200d412800c89282940281d0100320101c8016042500000000303642e40f0303902518501887d07903552030791a604400722600503d8241e610a0a07040d001880c4220f00c0c15081c0d680090107040f000d0040307415140085040300040c2e0001d48032240030381c61520200c0e1030903011000c140c0c0050381c1e5002a401c5007201e010300b102960040c2c01c0072400d428a460300d87d01d003061140c04013080090701401003500d0305c400306900b94144400303000700381c4441d00104030219805071101020016403001602402028004c03c003144228000d1095401704c0d42e070707030035810941c41051030358000306130503440c2c449000386101441d004442d0001d0000075000310454054003c60b81a5004400740c80700a41d82d4031604e00e024040d100342c0c10400000468445099002000000803011840e00d00803417050707031420b58240001000b030480712205c0d5a0516420075081088003c030850203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 893101861 1250 893100611 893100629
    0xf040e010c0906201507051201061d090f0106030914032217031603020f0610051507020a03020409050f150103060b1903111908010e07050d0b071d030d09 67
    0x88400303d501116188442c1e4404281301400500b0301c091000d40c150700d0010728200900c0810720840020559000c81d0501810319078542c0c640c00060304c0ba0707155010304a00e050920848464003000505202140c5e400c1c111500303030a002c1641c811a01e460b045030308614242c200c3d5403002040b0f542c0b444030018004926401b0180140581c242c0301c605d42c0b0400c4041c0d01011102d03034000c005410525094220401c0c0890103881582e40c2e80d40d01035103084c01c4c4441554a0b881071001043c05102c1440e00c141075000100c103800e134075031511a40b0b602180901c1458070010348619a10071104061040601008070210050b50a83e455819050b0225072100c1081c0400da0320a460150000d05a09158403071540d00201c0c000e8003900d051555941e4134032030304c8250b80160400c018040c0141d02e0400d00310398602600d8200004511078a041900038980b20702607001d58490340c9110282008100c0081e40350350011040d16200c80e0000702e00764800c460384a00c0c0c400e650184034450b00c043c0581d900c40807103815650954 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 893103111 1250 893101861 893101877
    0x310b03330f04050304060f030e010507120507020c0d150207080708030406060f380a02061609050d0b070c020a24050c1b03161805010503011107020f040e010c0906 71
    0x75078201c0e546442128001c00c0da520410083c03008900071406070110010600c1d001c00e50341e0f079440e051401c0d0780342554240081001500540044111030103210380c80180352005222040d02000010040450200082e24100c0c0031200c028025409070115980c03150011046c50365607545140844080e401254144d80306460b000010510f0f040ca6890f10b41128606140a4508541c81d4030060592014440d54107504202d81c41c60141d000c0312001804a1074030036005401c049ca000408403420307c0080314080c00b004161802442190703103904c602c1402581000c095215540c80741c0c0300383c44106010801a50101c5d4000303000408042c2900b051104616021080601461a0109994600900322241241c0e000b0000c000c0c82c9031701c41800700c81c440c2c0008044907112000c200c0e82c01c201c00c074650059002c013500610300b00c8641c580c0e1300407940102000d9008000d200d03409201d0b21868000c1480091148400360304c060b8041c1d980b41c02a102d5400350000030441d0030b00000c80606640b0f698401d1340c002c58451 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 893104361 1250 893103111 893103121
    0x1115031f0803090f06090f040c0c051011120705041211042009040207020604120501020316020304083a030203100e040b010b0c2406310b0333 62
    0x801603c5a9030b4010302400ba00c540b03003000b0080c980d000121295001008000410701c5039440b030107208030040382d64566103800622342c10460305120300250304000043c180440e485404402100325041580c1c00b030984503c580710100115031a20580d802100c0280041e64058103001c10110701451041c422901088540510072035040e0042d2506440402c2d01000e10048a050505400601d00c0e540700400f0145016152422500003440580041c0c425a5020003008807107000c480300d241c0b400000780021400c10340340600c0c40f540d03104018100f140d110559150031481c0032980c101140c4034042081c10700580c08d01d4000042c004d4200310780038200703501102800201e45001c0c1011074040d0781c00c40311001460b030900c04c566440d644410005030142c440d080d4884904c01503001503602007260304074150800e04004082010307502c102d034a101b81c0a819200e40c0754100040d1410300c2c51090700f09030041440301c0340000080c1801e141c855200c030079070030740d01400041c0c0c195003280840e40108041e0348400c40d155 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 893105611 1250 893104361 893104363
    0x4090501061704020f0102010207020d06020301300618050a06201314060412120212180d080d020f031014010c170409110304050d0509030a1115031f08 66
    0x691582d04200301c44042c00300e405810490703a203421081060002500d09102540491500c1d40c1030f2605844607580440148600d4070b285518107403401c2a9142c217404480c44035192580f40d0440c48005106c103075a0550301c005130480c40101d10501d030700002501d500366a981440c20180c10146800480804e00c2404c1032120f1100a040d98250714401d29100251030030100d02524254044030034070340c411020b00002906107480801c202c2c4103031141c14803010344030a2080192811040340396041c200343c0140203486592001d40d0310320102010450719400d030713008641050302c424450381440840f000e00001c0d41002201ea0800254061045908883c00d11a80e42b103101081805d0021601c0c00606031030b0030600402c44010b0201c00790345240c4036452405958480c91001c984001c01082c6004c48080204021b106003445005136415803401d04030b190010400000c0c5c3c40301c810320001480b400708015040e0f4a52101702c3c008103041e032003c01d11945d0b0309190030b00b1398045424507080d07075030055003d07008209624 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 893106861 1250 893105611 893105627
    0x31f050111030703110c090405070905070813022e02010e07152118030e0310110a0f1101050f0916080c1e041506030b180703020f0705010e030409050106 67
    0x440d20002d54100b88241c0e40c2100d03138500040d0400154410201c0f40c95144d40e6070b014503030003107100d0401841c241d45011010741c1a164002c09071800d00080208001c81d40181c02ca8494149904441c0c240000100408c4d1501d200c1c4000814250f40ca0070901c500400382e01507001e12800a8564200c421441d03651300d0720704814098107912400208500e4041e0390008132080480840c03c046000030541000c0744140041d040700d00c40c0140e001450092522901d41000d102c80e1001444100303041c01000907500004811f807085c05a94420448400001100c148c880c0c607580c0c0382481114000d00040c10643c00540c3c1000050b01e015855001d204515102070203107940507811240c50f00c01400c1c1d0580c0306010010901001d0034856903007000790785c42c50001c0e40c0b18400c3c2444c84404025180b60142004001022100050002801146100103116000020030000380d803002e003920300940e485d2411880b0708031078042c202c0028020f608001009451031404000b40054901186040119070307691901240c3c202 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 893108111 1250 893106861 893106887
    0x2010f1a1206040f110d0b070507140a02013e03070210020a0c05040c2f0f010606080a0b06040f030606060e0a06080f091c020109230615030c0402031f0501 68
    0x4034400313100e4000750f084224010700800040403d46106078540300c06142c844112044800a41c00007842010010402e0380107000e00010002440e111400b0342c0040c10000c1c503040030031007441505414500d032983c1107070b00d0095001e861750a5900d42181202d140d035203400400c000c0344030380f08601032450007610000c0d41e0300301c00340c1181800c140d5601c3c010601005000240e03200781003200070100901d40307940c048011a85001060a10102c1e42c0c00c07820454100300215464807000d90501c4030801200b503010504030380000781c1c10380009440c5602400100345124507441340340c210000e10000011701c502d5a021000303c0c0d05a031250300c0104480c030208100e85800e40540703000308810101060a00c480300717218903401101102150080303113456244070b4a102c1c6031005040140e4540410000708030340c1c00085490035140c1c0d8540940a0340a800080c0c03140c42c0200041000325002000400c0ca0342c0030450302c1e20110025004640d203040c07452a030124140c0c01c1c902c1400c040c40408001915500c02e55080320341c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 893109361 1250 893108111 893108123
    0x31009060c0216090b0301110a050a03050105060f0d05090715080103030801090506212a010212120c0a02190b010302010e0f011407080904050c04060212090105091002010f1a120604 79
    0x600301413040008200908210340c1643d614404072000d00c5400c4014868400c083d1185512f5602514006050f02e00c160081030080400380300e90f42100001005503642c1c4002e401e00829507645180b202407500981d039104698050400322440055904180b20724143c900a030359281141c0e07200c440010a4600544440b9007040756078000c5025510400350880c010304e20321080e1004420108007020000c02d0040a548943c568a04034222075a010011039807066010501039003003031002404880400c0008112400300c00c1c00269046240c0d00c2403010b019a00b03c070034900303000c2c01d00c103040c40346001c072090000320301003209590916003e19005010320001d8105a59002400403a030201e140a600010380444581009009914445da01c6010380380c4907900e03032601c007605d0391720300440249061241f92a800300b840e000c000070307801c0303992110440b00c400740f00740d56000600f1010340f0100c3c0100b90360308031003100340e140140c48405004075040055151070308991030042003d055013416210070007170300c0003400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 893110611 1250 893109361 893109403
    0x180b0a080a091e060209040f0501090f05060f0d02030a080403031808010207050a08091903110907080108071406120a0903020c0a080c04091a0106020a05071a070b0405030405031009060c02 82
    0x43d40842c2618894070320420026061000030320208050383d82440820b4203558039000148105030030340c862910070550245041c80721b814004082103084802103001809024440c40100039510100481e80005038044010756640da52801c000301504055260300e4030f2003409142c00a054401402590191504030b0f002c0c148030821540c41041d6a4081a032258100010301e08e21120070102803001801540201e140a004240d88010810204401420801030040510061108540000e5400203841c5050800040214580300144050280d4010b0307100c1c1d080c0520400020032170640051041c82e11a408941e92564031f803041040110050140408a901080e05d20116180c103401004c251400707001149042e4099001c21050507000340c202c0c0c00543d01c0052000100241000080e00400c00244c0d02c0c0714558001355149511300c5511009858006c4040210701440f03400d10440340140030040844200e0340a80c2a90301c042e105401c0140c5030035103802004448a4000f08500118100b0030b42c3c0401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 893111861 1250 893110611 893110643
    0x40518030d0b0102010e0a0605090607090317030402060910020a11040c0e1315030b010608091b060c0c041505040f0e0304180b060a09091524180b0a080a09 68
    0x80140b0b203034603a0034110340d260640001031100900010a05c2030217403101003080d107040c4d09558904080a03101c2800c00c03d07981030030408241d0040010790030800020a885d90790301d882c000640e13540280a03180341d12414441c0040080ca40000314030040d1071007072000309044100c1c6420041195151401040440c42c1303403000041c10310740300d02c22514210050500142442c60700207441e0700c442154101300d4035200e0303100c0144801608416085e6001011000904580102ca080010849030111b102c6000e110007060b10411172400348408100340501810401000e003d9000200600019204860055150054140944001740101c84450580c100254034040c80c180040700d480e04800a4200c040d552000840007e54a100040000c00c0c12552186040d031308006d40241151090001903140b1205250208054040e9811601c0705c86c50744101320015540c40c10b000d84001c0600005400c032096180c0004c80c80d819280042e100002050741e54040d250390f4540b207041204c0d05414050104800c0740c491003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 893113111 1250 893111861 893111887
    0x3140705120726090613082a0601030809090114060412030507170d0c050310030f0f051b040c030e0a110f0405130b060306010f03080a0509030a030f03050a021309150308120604051803 80
    0x46620040751035506020011300d8070927007043d03000e810880e4810f5000807802c0c40c038500745024a000d03102111543c045ca03d00b41e00010a1445a8401c1c0c1c00d01c14103000c41642450701070070079036a94a4010700d141c00d50344180030140280c0ea0045000707100003440c0c01002c0a96074400c00c10b580c890507040166074419815501c4094100d10000805c54a02d0300848215000078824001d01c14010391184001118081c01410001030b0340202001d102010329020209150300b000082115600703820900d100e01490810021410301540d4031b40e02d58025040c0424858440e0059a036031030018064070034103510351940001c00d40c84131000c0c4504102c0d08101441400407a80b14401000c40006e82d0038520b00e00760360710700840d042903500d050940110b000074920049003030300740c001c966000651b24400c510340655040c81c10328130301e40c9000303240115556107600b141000d01828227402643e00910405d80f81c0c10309150f03c0d295900200c1d00c5070701132400d001c0459489402d403a110041c03005440c0240d410210464665 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 893114361 1250 893113111 893113147
    0x9110306150f07121e081504060512060a15060f030e0c0904050d0807080c04032406030f060c090501080f100b040b07030314070512072609061308 64
    0x206a46404104408007280c1e02d0004280051040d0200c039020300c090380c8060a0418002c03941c075200807480381482c4156501c0844594000c20078100d43c3e060715160f101103401481c071a044990010603411340340b8800640003941510400150030300f80f20703120b11000894580c21080c031620b00442c20030042c12443da400b031b40000ca00950380c8012104078920040000e00e00310b00507541551070750440140d1245a5034062045c681c00160f40c20241c0e16800e10015155040c41a84805072100240c0d0b480c404100e0450070303824090040080c2d090121640381d040101400791411000c440c100e15002c5081449400f4441d08011030340140c5030f0400665030001030b2420a00000c2010603148000d0401144c80400c00e0041c1020700303070081d9800c0e00c8204034a4050105c444100c851000c4145450801091075170142c222041c0742c031030b000c5058050f181c45000f920002c624118501200b04510000307680b03131100786003261040304000104e81640d101d80b8240715903048078020180540504100f010b036203182107101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 893115611 1250 893114361 893114389
    0xa030e060a0c0b0412110109022101020408030a080717010303020c0f060d060306020a1106192004090b010801090218190e1014061c0b0a0312020a03030609110306 71
    0x40c200b210203e559070003c1c43c10480b022a81c0181c40001c610145a010800c102c41c813082c0c4008000c0001c03241c000688907035140c0d01403400e0a80507141909800f90a40589009154044c2143d0b00c4904485001d400d1550403505480000c606034440c0c0d0030860240301e8079040740c3d01500a000100720340d00510244804060741c10307401074030030041ca2403200c1941c419800114010140145c40750751101d0000c2000e82030012010143d032104c010312400d490420050f113214210303a100056407180094010707110000311062206025408180000e036260307945c04c6030316024026030380d9051983e01c502991007240141003424050300001400d11003641801c5000086030007421400f6001c00b540c80000000b40315048440204050307841000304104620300420415400040318028248071103220122001c441a080d100b10441c0c880c066807042d903e90910f0b040c088c41d04100450110b0014180180d80e03050307039071b80031800680360050008500c074451080344903084850020307510703549942c410803d040e8a1018 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 893116861 1250 893115611 893115617
    0x140919030918180b15030c0306060d02010306030f0b04170f1909091104080f01020405061c140a1428020904060e09100507020102090a061b051605030c030a030e060a 72
    0x41103c180040c4088107032000d600c1031641a60500d0700140e805d40340c0e415202418020b500030381305850582e40100704154460f505403159001c0040c107000403405800164030150090600380703141e405000702d00310200e100701d0040c071458080300511020720300316210f0f88148248200c42800280c0c03004c0d2040d1030f1681010154a00308101c80c1d01d1390a12000c07101007041159030301c0380006042002e0441444000c10f0f034000e0304000c505161410000c00c0043c4a0b030300b00f247c0d10030a182c0751600c41e800642d1040018040e8403100e070036189002c1c8201401069491401d00314000e0f16000600d55007600300300c8011002c4206110548007000c0d0b04d10314041c1d045072812652207620b0300400b0420b602c69003051481203200d14014104507413481e00940c00c40d5005000d0000b1640100050006a200e512003074080f0b8820b03260088888001080c00e8900c400384071710040140c000c4214065807018800d40043c16220224103995103618010f0415540e1400d883c1c1c000d020604040c005001440e080004c1e12400320681 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 893118111 1250 893116861 893116871
    0x10e060406150504050310020c030f030a060e0106030e0c15090103090c050303070615120305070213021c0c020d0503160f020a1406070306050105090a05130e01140919030918 76
    0xd400c2c0d001c4001658034000001c0c004201080503203001c02240350701c514906800c616003550901c200c1c0d1284035410381c403c1d0102d000004a80e0410b03c43d8440001441c003e03a02c461556100c9000070054404507040c0c0c07505116060040d102ca00e800004212907011910743c0c0d44c07600002d680150040c094181c02a03c2e10381c030395107002501e03403000e00003000d0540c0f10b0b0f8000990303160b0f40007219480c800d00790004c50003024408562400684c0000440b4000380d0100ca00e40000c0c182d00304000c01a102e0981c003003c0c0082c640f222000382c01d040384c1280103030b1032281e026203a02c02d500c007030200c52901080340e030f07402c100800e418030b0014070b40244540c548030884d500c141d0741d9010054a40700507103500e070070140350103030310510400c202c5a60500c600c201074202483e0140c5000d000a0020380d07100f80600400e0301c2225040d030f100e02114035950003a840d079914140240200045002144030591003141d00c002c06014254107880c0203190030a00704c0701e00384e054440001960501c0c48589410f80b40d01c01d4000a941c2d20 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 893119361 1250 893118111 893118119
    0x709090b0a032001080c0c060604090f06020a0e040506010c030c02040903020f07030309090c0c1112031c0f05130b130f082b06082107061b030c0512010e060406 70
    0x590b0718003c00c1000c0d814940c0b20b07400c08400103202c0c1a0040440c6040b44007030102803290500440c000c2d4100b041100d012640f0020343c104011600c1c0c0780d0b20001c08007031000032641c0303001e078008a110040f80001c81e010031850391b0f01801034520f403114407001000264000c604030010700c3d241d07200e42c008a0180c81125505615525801c0c83d1891942041c0c0204040d50b01c01c0100b48901d0003444118922890043d49400e01e680d5410b20024810b4101441010303685a0941e40c0c03a420000c0d644902a00d10340441100481421440202a01240703810540d082c0800640c4c8100a60054010254020008a045e030f4942d01002c502048020085803a1130606818101181c00ba10181948641c488041c09924010f4503801170403003015414002441d0500c1c40810800328041400210803890a042c0ea440c05e084450703c16403440390035801410716141c581c800554000044840400d9070751074a0400c10f5846035601610300c0d0064200c01103018a2401c0107100340851180459001400035102055003926 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 893120611 1250 893119361 893119373
    0x20408060711010c020109081b10021c0506090103020f1003060b1218060702030316050405060f3414030702030109060b1011030307080402060d0903030b180709090b0a03 74
    0x80d034220000991120b6032101d44042880ba110b50700c01d250008114480645e6140b050b030703001d00200001d03035184500300b00c400008103000880c0c00038200b0404540e9002000c40c1e41d10303090401c00000940302c0c50580003510720300f040e0f0102816250018045030b0540818401c11441d00800c0704107400301500c44000040ca803c00c0c1e03010302400182c030000c0f1001071038192500151881e043c00c0c10f0041d548864184400c1a4003c000c0f04d400503103040d0440303100001a40c0903184ca01c01d580c400c42e000307000001e0b000240081d18003c1e20008100426008004a664818404108441000000ca0111969104009240003000c0748c0485c5c00c0343c040e01d0034182c19800090841d50034400990717605449081d805041e1400284000c25001d035070820301040b90b92241e03103070380d00c0c04000c00d95810300401e40007040940d41c2d510141e41c02c2c4020000305001e210840d00d001405805034132903543c010404130359440e40c99081d070100e40f4071330180e96907803603805450326500b000905107a50003d41c02c81400c1901002081c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 893121861 1250 893120611 893120623
    0x90305070608011701090312020c120d050a0501061d041806090c031118010e040c050d11030d03090b0402040b1207060e100c020d11010212180a0f1215020408 69
    0x1580d6211aa002c3d8542000260108180322414039603034503080d1141d00007a000b04422446c0301c1540f00058170790300d040449625250f5441030300e585070240403c1c40b6800308a650040c2c2c0c4500504001400241d0b85c8103025103a085000c510041040b101c410f070a6844d05080c1d000c0e80340d10a4003040000366207680c0d25140110341c4107650603140800c0c9514140300340288c0b06200c0d10008400d550049d1003554030340c0102d901140600545080303441c4440400e05102e02c1c1c80d070f000082d02000709545d01c4c2d0070052600e699045009070950b0b000f8014040700025541c0241f00724048030703801500401c142e41d00d80c5d0802c001040c618060300d90101c50b04070020113180c001c000050141c509a00c1d484021300c0b50000704038840d22252521020022032803080ba0068403810329403549140e2201500d0b000811000050b820b000c4010f002d034282d0200422007540aa0780ea00400107614000e85100c0ea04603200c2c001001c0150342c50241149503441001480000307101601c4007040c1c0c07103100300010b0400e912703611040d003001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 893123111 1250 893121861 893121869
    0x60605060f0c070f0605070f140d08040c1202010903060f06150309020109090506060a050c1005070c0209060307061d03030d02031302090a061202011b1a01080d020105010803070602090109030507 85
    0x507030101e46429600010464500074140c80ba0782990011700d0460014002c1c0f088074002080c1178000348080080060301c0000041c851020740c1a1101c3c41e024880041ca0a00d007101e050b81c2c030240000e80001c24040d540d60f9006030907010395800e080039046444a030041c2103541c041e07130075680c3c1e01c400001d0720f68806000002840350664012824000e07900005001e05129000301340d4052401c01880515079443e402c84031650903a0900a45031562019901c0c2401074602c1c07081600c500b0802005521548102005412031003114034542c0c94a5040515642c0c4000340188000304074100380d444500110540c0400351807800600303e03850101802116007ea820950b1070041c4401c212500808500d821001240d10440001d410010203103068803110284000401c064140a42d101d40040920515540015081d41000404049101d03212043c41003220900c00c103042c1c2d010302d800c0d141c165841030103094101d803424001117041412644fd054020f600c0000541d06001d0305510000c002076050007200010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 893124361 1250 893123111 893123137
    0x3150611102325021f0e0307061e020408031b0a0323040b0c03090406060f1704061d100b0d020a05131418070e160c02040b0411032a0a0c06060506 64
    0x1005811114269200c03c0c01c5021170024100b540080303824000000f81c9600030b4000e00049041c03140c200900c54041c220075001c034082c6000150108070010300100400403c040e036005071506080c0d401c0320b1a200e901d0580c0003000210820b1542e0442d00301ca000810041c0a00c0f82d070186400c2c3c0d26010350a40303521030101c0780071f150000702c7c0d030054516080c0715080083c05d0908041c80c0102e100400107010440c130754a16180b2044400205081c07180541c00b2903075071031b9210716070010948403a1813243e03500b5200840f02036442c00c2003407540c0c45090074400c0c507007034503030190000c48101c3c00d0408020410241c040361402555640c8014440d00c1c0d40029882d001d0640c1091080c000d083c05d030100c0d800d002e41a0024201164824103000c5a086011002c600045451401c0b0801594610000d0060072100c6000b0b5801400c1000700d41da42c100c2c0740003c40c05005800010001a810108903207018840d80c2c0d0001c0c1524410320401c1140ca00840151514a1080304001000da0700e41c1c00081294000816090780 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 893125611 1250 893124361 893124373
    0x41a0402010522030615060f030c0e0d0f11150405040209031014010303020d050406080a15030b0907050a080610030b04080c150a0f0506031207030315061110232502 72
    0xd01204c0d100e0803c608a0950030300c0070860414201801d6101c8e00103440d800c1540d120b41d81403000d0704c40e20800708040001090034070b1901040c14000b07e1804a03031408da580840c1c000b101030140c501142c0b545204510214450b0038a0703c0c20381000025044100d41c29014006c0640c90143d4808034480c4101c5400041400700d065415400d000303103001c80c0c85c00401c1c2400300801091212a81060300c4650000d48101c0206000701c844d940c2404c4600c4680c0010b00111542c000c3c02010305020034603e0640701c0585004030900c2c0d8903000340d03580f910f00341c1d86c2419212050b001071012030103100c42c091780b00703000392400d501c0c00550349000e6207800420200390043c4035200d02400400c5d00d03540900d608000110340c0c140607c1c01d0150000f03031104e15900c0310901d942400280341c01054040e40244d50350484c0340c0452103145980ea00c0c06040c00d811612200214010384c5003022099145218103a150b1003055407000320b0240c50310a4804c00350700a44220052a401d034800240b0400002203600c0510706580034140b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 893126861 1250 893125611 893125613
    0x200d02180f150901030b0c070f140c061c021b0609070501030b010c47041703100e06060f0d0b12070621141e0c03041a040201052203 58
    0x400321001808142400c1d8921015602e030b40d941c81c0400d41520313008450f000c03068540d100b0041c1e15200b0508010041549500000c0c10700c07403210b940000701d103a40d800740e4151b40705120401030301e84598804508024200d0790050203d29840c0d002e42200d81c5000400004448003c031700b9464000d003150502c0c1c940d4000c3c4003d00c065645801941c40f0250700703081101c3e22011079628642d40c1c1c4482d04040c2c511003c002000c456580b41c4a41450281d1407840d4140000f4020060140c4981c1c030071a429903030350f40305082c141c4400e1070b2002240c0c0b04444655001001504024080301101000703003015034002010300c6041480820b40005201240e600d031000505c11140c0300900007035104890060007150807005041085030340002d0b01c940c03012080b1b00d04003041c10000c2c9441000308107140c03030302c1c1e07101987e0420001050303100190f0401500c44840003202551700c50b00781041510040742e0060207844120344140268000c0141190014030504100d42003804c090200b039220800004a80c8425901c48001c01c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 893128111 1250 893126861 893126881
    0x1209030d050313020d030e06070f0203190b0a050402060702060c01090c140105040918050604260a0f050a0923090f0c0702011d030d050a0e030703200d0218 68
    0x49048402801e1081c2140340040c84801c0d030b10388001019000c0c4139202669810944592040b0304d050000524407a240c03401d605000d241021030047c224000d1140210040d000c2c0840028200c9069110909400d15502e00707100d030700031307000141080740c00020074800c0030010303030719100688039265010b80001aa481142091351540b1101c1e40900741c03030100364902d40496640303c000c0b202640c040c0300d0082140d0a400c0340c03081000110320400b03006030103200244820000c44002c0c4205440300401018003101c0c0d030117400a140c2c070484401f8004a0010091481d2040c0101c018008040e45400c120301a560340e00600e5060341290b2030045a0800b9481c1c50000c07a151110846410041d2802c00354820320707040b00c0651085c40b0382c0d540a41400380e14101130005000d003622074640340201500340c80c1d040c04449005800b94201c00d41120124810600c030b554941800180c0204403a00074103140b00c500d0494081100d01000e150205400c020892108070158480c100082001c4502032802c0c603a03454006210 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 893129361 1250 893128111 893128123
    0x3080d0f1109041a03100e100e0601050d08120c0a0f020106051e0d14010f0501050d02010c081c02031f080d08011509030b07090801060f081b0103020c120903 69
    0x10a64462510440400041d540c00030340d641c004050300c1c0000d242a500c40d4082c2c0660f58904043e6151054124240c60314000b500b00701400303020b01e0308171040c10f0a403480c503005545014400104551006c2c0040160f481c10640b1202420f00403042c4070300e400c1d100d0034541f2030240e0469154030140c40009050181c82c0d4000c44900c1c00e00401d2000304a018100000220b16038400c0382c2003030440c0d101d00b440300e40350f40d1900d0704a50400c0c0e01400c0e2400744041b02d80983d01902000981c1d0903a01c0c640740000400d4107000c5030819105505940711603075001d0648d079030300d4142c014140c402d84600000502c0800030b211071006600404c100c5004640c0c01611a400000003580e607044800c0f01e80250710340722201070f0403c0056054641161400f4407400117400200d514000903407018000740301030803e02c204280c00081a4003070b960020000c2c001c5580320244203119540901c903a44030303a485034440c2c081650240d0510001000145009407070210039994980c03801448520307940603204005015807840c9010000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 893130611 1250 893129361 893129381
    0x50a173705040e06040507020102040503150a23132a0e010812030106050c0c0d031205090c060a05130b030f0106032403020d0215040909050105150319050a020a03080d 73
    0x600c0c50b040c103010b188019140d010307204034021380c0c070740c4081707000903000b0b4041e134010305000380031900d81c1601220458560384040d10480b0525180215502003214418400c14a02038410081d450300d03155514409211a414030050703801d40340781c00d00031900302c076803528865581c00c40c25071400c10036040407000c0c04007640c1a40242070980c0700200050082d09130009480c111044c60407c15128000070941500380044410302c103504c10f40d0074600804242d0003a02c01404018005010026647c8050107250350f21910b114441d40580300b4854001e0b0180b20b0f0b001801001c0c4032044903040c16036101c4a0011940042d210709000b10356850040c003505606100e500a031000714480e486450b07208419090008420b4000640504007040945c015500e030701603c1944207400007002983da5688200c000c0041680f00c204a40039400c24000c45d042c211002d845039071049008010b041c4140c610001000e00c01710b542003c998038081e42001501680d03d040001e001180a1407109550341c0000760b594040703d6400c50 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 893131861 1250 893130611 893130617
    0x4060f091407020c0111070902040e070f020d050301050607020f04060303030b01110a030504030204020d2a140405091810150e0f070f0f02030702030709020d1503050a1737 75
    0x80000b516400122065550303001c0c02c0202c2642c6d010f644440c00d103005c60704010f076000d000160000f05809800c01c0c461052030340b5603030191102c10051040303894081c080c04e0307140016803d00050149281401c02440384a20050000200d4410800401c042e0f034110b600c01d40229a454020000035604007050b003860991200142c03030040550703500035049015900000c0d0040342d0100d203044640400303034000d0003403280d003c12900d1911403400700300701e52081c5030303401200140f4000748103404070b14120252015a2001031402003180e94000301803001d001410850a030310312829613101248040d5209002c50307855114101a6101e0030080741c940410b80280004901e83c04003810807020660101e90300466000c5032400b03e0703170590b808a04030324601903181c0c060b525000b00e12001401c9a215401013848100c80603040c0064000b040301d01d4050345043c03001038a16044100c0031400506c941c002d00d48034480c800700c0032342001c0141c1c4110718842001c2e20503c0210429504024200303600741c0c192080211246 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 893133111 1250 893131861 893131901
    0x70f0e031e0601062010050a1d0f0709020a050f0706090c091410060c031107150914010f02100b18010e0601030b1009260303040b1602011503030f0e04060f09 69
    0x40c5c10703556040581d100d00781d00342d61400402c3c02a01107400c02a944004a138030310710b000b649685456224852040126507520411070f00003180801c0303000b030322544402a11000c0c01d01024900400980c0d110003011030b90250b44102400008041d00d080700c02030300303850748000790303843c400c0d11000149803004c0d080c0c1046070820700c130030800d05921105480d011031f80b5203031008020262070758440c5083e002d41c11440c0080388042c01030903a035500100c810200e4039610f52030382500d203404006640020403404081d0050300070700340c0ea210307615041d00503420002c0d003c0c0080340c00c003465040c1102900320a03004041035001100031b0045039030b4140920b0b0003243c81101c40b8194480c140d80040c2244c040d500c0780400c0700f10100203902d13210383c04609101d01c018051023640d42d64981850b04207844002111401c65121031b18800d951414414424035804bc10300d595014886801c42c1c43c00e03034030a990300e2000010020b440c41d8070050740d21540a070070020a032101007030f0500c0d0f080055410568100c3c0020041582c201c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 893134361 1250 893133111 893133167
    0x60908011107060b03011b030207110405041e0c1e080c0306010b0d0e03090603090a0b07090509010b0c0f0a03020708070605030f0606030c070b1006090e070f0e031e060106 75
    0x70085420b56644401c00240004549003c0b0f400340403410581a4150502001d103080e03a50141c005049042c4035511800111051034100b0045641c151405000000000d4254000701c00c20a1344003046c1d4000c0710301c40c8060b5036403599010440010320441041d824680c1d810058024100700b4008504030131409402550b050406220f0035003d00001c1081c07450311082400c55a0905000302d40c101400948455644d2806410190b658900e184085684040314000a004148285e07030410680d07100800500da2640707010560b804075000b51440541600401440b02c1c8044410040800740a01c81c1d00a0504e040c902000c42c1d060044962185041c41820403c010b4900c040b0744080c0c0e4000f108540c0c407a143d032030303211403140c0c503000d40c240003000607491100f8400301d240008103032421601241c0d5181ca24a4807540c908080210903901034005c100401107246c86c150040400601098018080315070004444290100000800c0343c08180c0e034026400600107250b020003444112581500003400d0000c3c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 893135611 1250 893134361 893134391
    0x414030a0b01081614031c091a031b04031a100e040b0f090109030c020d0c0b031302041b08040609080c070308041a0408030316050f04060521150d02030a0c0f06090801 73
    0x5c2010300d68001060317454587c03840d4003c012050140180011541c250304085466640c41d5000783c5120080450448400c94012804003c40b42982d5011099030340103c3d000c1c51002c42000c0c040c00c42d4107072607100080800c1c3c40401e403400070701c503070f005520350141400c04416a42c60030350301078134031060f590503c0390714804650010451ba00007a4165010004c0300500d082a1129440f48e0700000c140503000018441000d08403c19000707541e00071601000400268155040d00410b92101003002c0b401c51000200424265440004818090000300b0325081c0c201c6041c0707091501941003181d0303020000c507080c00544d0007552800701e280080350031149087e0400312140d45e00c5c0001400031031070700e80103800914039034452402d03111401d0b00e2884ca41d403101d80f80d042c00f4090b50404955492403008651034208126800800d590003a9001c0261000c0c241094003400480300c1e1240050741c1600c21000d600c1c00144200c44040020702c0b200c1c040503107980c1022001080700e2502d52145010303a0401e640c00081550b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 893136861 1250 893135611 893135623
    0x60a05011704110604300c051e0405070306060801080304050612071b060911180705091f0305070206070c0507090f0b0405070f03200414030a0b0108161403 68
    0x600000c848055542da180c8a00303500c07800092690049404580001d148071603920040000601c28403da0340c42c4010005406010070000024002c0c8402c0b020400c12030420ba44800d48800354003860242e4014141e0120b000d46005503040c6001030351344c4404000066004131554094501c1902a40c500740c6454001201d9004d06420401440d69020100d501507000b84011407a1500780d4541e207464a0365820900c0c010f10300082c003510002c282031360b004118503010070495180203080700c048900e5115800e00b100c6075000145480e0300a00b6911015041070610010410607255542e4007041c1071820f840000e04148019168205000d00410707100300061002c22210142c3c1c1c2441070000d0410844501d0300080d00c03002d2819500145002c050000c036950111030750f9683e81e400c0c2c5040c00365140303403010041c202a031070344003400b2200144028040815480c00c8189c1c081001001c460102040761aa1030000c042a0b10a42c040d5000001c0c40010450050819008000045a07140307616003080210752910 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 893138111 1250 893136861 893136887
    0x2c070b041406090d0510050117010c020709111312060e031617071a0106032301050d111905180105010f0c0303061e03060b040c020d050f040e0c0a08060a0501 69
    0x1c401040f24900c54840541c0b00345075581000c221441081d02000d48001400c0a00030400e801c0f4002c03040c040d400a05004291446160303500402d9130610b0217081030014860314000351141d40c0100080c84682080300300480140c8451040d41050310024a80b0303a045506865040e0100d810030b210301c12540c0394142000c51000c6d0401003210443c600b9880c80c4c1a84e01c42e00400800400000000840c41c5040340f0a26059503d2520100f00e00e4110f4010491000c004400580e2aa200800180983d05040d40c0c80b0038024464018094501040400034001e034800003c1c116216038801410401481c01c01076800c81d078070300c40d010200e16505200009017582c83e90f40918003407001c80c182c00003c06100e42d00104c010038104030205150f5031440c0140c450060a480141c94140c1004803815261038184a04c03d00726071036030010441e181c8900d02c10b603031540004d041c01400200a102c00101d500c4240805481025100c0c541540d82c511200301529881c0003612142c06014024404d200326600301c04100402 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 893139361 1250 893138111 893138119
    0x1090b0102010603120807020f072702070624060e0603042012210c060708070c150507080906063111030702100b01212c070b0414 57
    0x11400000140d014080e40c0e403008200388031842c05e000302250712200d0b403406080558265054081c0c2c0072502c594505060040100300d01012200c440d0b8a4100e1144100014450320050b09180180c2c89080803500030890100c080c101480306100305840c000141e0740940f202c0e00b0200005440980840e0003030200920040c9800318454401030b00c030107190b8907200d030000001c0c040642c400582800d1511003010603c24804001d51140605d0120700b0141500d003086450001410290b850b03000848a081c000b400313507014021840802804110014051125040c14000c04641401c10b40c10080c00d61740020800d03412504014207000c11380d07640c4c600356242200d06503101510022180601302c2e40c00c07008040300c1040f0345801510103500d00428042c6106901c01c4e0240c681701a00c01c400c10040d207400060301d40c00948000d20840c14807443c0140d2005040f21100006009a4a422041120440d080307140c00035941c0d0440628200c1e404021a00140171001e6406080c549020801f4a903140030308515841 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 893140611 1250 893139361 893139371
    0x1009050702011806020405010e040b130b0a08030705010c2c1e1c020f09100b16050312220309261024140d0c090603030e0f01170109 58
    0x500c6100350052100d1001161071241c2800491030424002d6000303101e0381d40801e00301c0703076494030614080c0b0840842406c084c3c0780d40044440c11400800038160303081000d900011882c07011501d03e0041001d0300342544640c000154461445c031001c0d0000402a00c060b1441044046280074a0003605903942c0002040d195904100728000403c080491281e241a4212080604850603002002c1b54561014001d541424030044004207000e9840c80c100c1c7c6002c80710b040c950007003000c4041840101a0480d01c2040c1d01e10120f2943d480f181542d006180f038401e403a130910240089400444200100903441d00e80280c10110b60366030103060900c0921a52900c000007040b90143c030b0030401044001095400161410b1144d1040c1c008028100d0740c001c280e80031680203010303c4421165065409440f004880e20b01084403e6007000001c1d410644100c41302045e56074009407841e02802160b01079072082d12204207070340782d08050143c00c1d03c04101ca241085002c0142c000d0a0b4035580105066490766140824 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 893141861 1250 893140611 893140621
    0x1090c2c070e03010905150a060b07080f07080c010c11160504020d060b03010b040f0b030c03040f030306170a1b0f170312040f0b09011e150312031d06100905 69
    0x1030304070b09001c42c00e8040d4200300c1c000b0200040454141c0d0b0383c51000c05003120944036000c40e0f004468244c00382001c0c07100c0400801d0085052030002d0419130310000181403500c003a1f40c3d9140d809420110f07050003079030b450380c0c4046003031508425902068100400201346003455540880700f41e02491003081e028641c0010190b5025445410280c05851010215560380d42e5403d441d5103254090301c80c80e5241e0181a50100c0c026001c00122400343c400c060301503041d51503540328400c44607a140021030506075142d0002500c6003c0d500080844500c82d03015288003051420208403080e010240802880c250107014009501c260501c6010707187c241c0400701c16810440e20251444c458000703406c055100350310400042000510b00c101c40c852103240d03002425100d00d81c58a081e200b0710320500e404622b0b00704d9111020141940040cce044042c281600312059601c0d1941c614030b0b0511146400040d484540c50001c0d01925650030f5265061540100880d1400300a941d071202528000c0110043e2074401240c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 893143111 1250 893141861 893141867
    0xc02030a020402030907050a1211040b01030e0106032102010501030b07080405150a0b041416081302041a01080112030203030708071202030a0c081f1a1b01090c2c07 72
    0x40302103030301030021036490920b00030b0301d640c8100da48141c40c0b04032640440410080700b07404d0342610b1707a5071040c50402142080800c020152480b0b030700c11030425a880c0030b5105242001d01900307000b50f000781581d950031500c56800304015500b490700d11042da03061100400015103110342d01a400606851b0a8409072200e15042c0d00704a241a605c0e04441020301c140021f01800368414025041d040302d042002e101c2949100f01203900c102c5032440e1b45150007050b03800c018041c4c50981e61003042c10304075004240711507000030111228910000c1c051b41a0300001c0c1499600207500070302404001880c9507200419a238000e40d82d200c010120002c0000804c00310309003e00840049841c260340103015501e92600c1104200200b0070303141c0d564001402c2d100400c60021700c00c03030207111003003100f11034101460500c006c1d1043d04010700180c40806804000d21607401d040c035443c54018100d5240003040120482c10305802d0060300340c01c0000c0300038441c0b001c40590940b00110b036044260510741a1520780d60580b0503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 893144361 1250 893143111 893143123
    0x60603020f220e030c0a030e0a1a0a140c070e0604050a021c020a120903120c05090d200315040c0b180d060902031903021204150c0c1a0711010c05060105010c0203 71
    0x1916003403161b680f0040c00c1682103082002c500c0011703500004031655509030619420700d200f22031898114100310445031a4482d0040c41c3c4406001001c491030301d680d07203181a00e420f610703601a5510842510510849140901a90f80c100152a07019070034450034a541810070305e122100c40c00110b40c006810020540504480000320301d40680403c00c01141d03080141009800e2540b400c101480c0a084290306030250007541c82e00c1c40c0140240781150b2155031032103800032040800300304001c01c84c08030800d0f41c9c0d4100500320340c031442c1105071981418249000c81207069240c21580c9170b01c90a110340000c03074100034540e03104400106e5103142405000c0c01c113400102880a8040d405010b54514040b000c52044840c616240c441e0b4203c0d400c80d00d1100c2203038420b02035802041704125842e019107007024402c1c005241c215014001e01d10610780e403000c0f0319103504003440401d10700d0000842d203501801a02010661022805e00717103010bd1400c1aa9101c4d140c41d014080d250500c103400031403e040d901d0800c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 893145611 1250 893144361 893144377
    0x306130e0a061d0f0d050d06030503030702070f08030406021f0b03010e2404050c01050a141606050114010e12030403060207050c0a120f08090105070f060603020f220e03 74
    0xd5030700750740160500c003010b4400008160030302d00000110b4000d0780c0340003804c004104c03125070142032040c00d0b402c0115016030044011034921500c440001c004180144000c50158600c3d8000308003107403a11001500c94171042d0b200c41e507140c0051000f0484203070041001c0208400d540d01d0390000301c6050b075040004040840d1058ac00d503180040d204000400000c2d00e0405440c0440d0b524814401410542c41600003100c00414a40150f0740b02c16255005801420183c0b1072810b000c46c0200b14925a518680c1152441d86450001a0221000d0245a1141e180900b0bc0020b0300007043c041440040d00b131058003004680102442c0010841521040c01500c01942d8422000d6564a0356400d0480e92025002d00c510f03c0f80301004c038009042d28044040400240d0b0048a90580724456110b00390260400345034a41400020444540050381114031210302e5480750700b0001d002821801804001d8040c140000e0040c54141c149040b81c1810094400c8500324285001c1940300c0c00785602e174114021415 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 893146861 1250 893145611 893145613
    0x3020319120c0e0916090902031e040f2618270118050103170c0a0b0103060f0c080c07020607080912070e07050a09060815130b040f110306130e 63
    0x90b03550060f4070000c409500c00c411a0442015210340048040c88400521171201054400e002002072802d03a402940d4801d010641440150a05406007945800d0442d0100d41a0280c407404004010700300055a403c01002011144c1501401c0055896072142c21600301c006c18904e61a00d160355030340e05116100301100192154221002c1c000492130050a000d200c5084003240900502d0b12042d2043c6812243c00444002c071030a0405075008903a4004038500c01d0f0382c0a000e00d1840440e98400c910381c0214401c040c00502c41c1c284980b070f081101c2000204904100c250ba00f80702d5400560b400307884046e40c04036059540c8281918010803284180640e254121300c401000c075100745030108400007104e003038181400e00b0303954601040300c280c444d031101d80300070501a000c28050948284030b00d691100d003c0c4503100114080200241c80c41d20990301c00c030101615101c540e01c40381464041d0200408030750303c09001901180110b50303100e0000800380c6001c0c0741030b00010b030401a1244c0114105501d844 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 893148111 1250 893146861 893146871
    0xc040918170721031d120a0c060b03060f0403110c030d050d0b371a0a110f01050601111c050309100606020a11061204080903010f060f05090606070302031912 69
    0x14102038007510301c400789176080e80f5074007400b41c11704500031440f890030034010503515140c049107103401d54500403d00390942d29155501960711541d14100181d6010728454045503000d071403e440c00510381c4d4900a0141215004402e4050842c1c600080c45504005a0b040240d101ca04c2440c070307000113100c408011039020114200e14014843d1554140035a50000c06940290f42c20003c2140841c0b012807058084c0b40503286200100c14840d100500121a1140341c0346c8900c483d8040d0f91440c10b04807170b0000c070440e550b07601030000c2503800071107440c0540b0b1140040c02c010400469a80c0907011410441c10038400008002000603070284914000b0080c1c40b00208501920303203030000e6850340064811200700180c1e03810028185090790646800c00e6810103001003a40e2141e803045155082600641e030550b483e000714044c06a503501030407000e41040412859a00d00e000300708a14804094261401040100040004240d021084800c2c000c42500d216601c1054694100e924142c102500f00b030840c0340c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 893149361 1250 893148111 893148173
    0x90d020c01080603101409010e031c180204020a08150f15071e0f05010507050405060715021e0d0b040c020712020d020a0e0a05011e0303031a0303030c0409181707 71
    0x28170f134001d1030900c00810170403001814080c0d4038441c1c00703040c02f001801c402e42e03600381c1480c40d00a0030202c01c44007068480c40400e17030f000c1000e03a0000048000401c0e14001048003800400201f44002541241c800655003198404110f0700e281050803c0e060480005e0940c081c84a0000300100480c00410300d902d0040b840d061000000316102c208036415402c24001c514140c0c4190207541c140c510007000e01d86843c01e540d8900350300c022042605032149409000c10440d5081062000003a000c003503544541e100c3c42c01c0040422150010000342c407071840c04031005181c0c1c0e80080c4200a441c0c1000408900d000f0394000100e6080032075400944c0801d0712007000ca0f449069614282c02010710798000e110a1740c0700e0301c910012070200803280720744010145d41000482e00c280c101c550b14541c200240d91010350201c0100e8203540c412100c42034003400c00941004009a10b00c5a88203404507800d604401c0c210315511440c041111118908e1340641c04100391017072142081c0c215280203031052040092490b4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 893150611 1250 893149361 893149391
    0x8030307030507020114060423012d06050702150403021512091c0e0a1208250203070501050c0c0d0507150c0c05042c060f090d020c0108060310 63
    0x1114280300090030440402d40c1180140120b8102c501d504140444960fa0042884010049542050b184d0790100078000341512aa6001c2806410860300c00c6041c2e144c118051601c0200702a440390000030782c0e8a08010f01c0b580b03c0e09556a01d03a04807110750840b403500010705400c1c015900b0103544240e22100680400c2c0c111002009001400380c0a0525690b40b45a0551603080824240500b11100c501400300f051281802d05a0034000402144c10a43c40d03010f1a826060241d10032030b01c0b141d000070107200140100e85085060490700e180710411411030350100e6220b03007051148506000300401d00300c996000500807007000b8400035008100c8031400342007180da909080c0c86006000f4840200e80003800784070308102056190000440c00003540b5010501008100038044802d061100c091030720025101000b40280c485800c4004000390300300180200030100e005080c0c1c440300d51008940081d20b0344c0200307100c0907200003424202d4895036034802082c14803080d80c240310b084e5443c111211303184820b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 893151861 1250 893150611 893150617
    0x706050c0405090a090209070806010201060f0305070905180d030c051c0917091f090e010b0915040303020a0215040f0303030212100f0e13080c0c0f030705060d0f0905070803 76
    0x10b000c42d21003140d6101c214494013111103090029401400c20300c000303004c29015114a640081044c4000070309190754008108100c0c1e481d400440f181c1d0003c000c10042001180180e41e0000405003503002d1140b1080100f60381c4100040d1000289502d0710450b00c1c21500034019240c0c00004e0100d00b07461b00201c2070040000300f03d5102c0840c4c5002c4d94551049510070090142c48151300040c04510f07840740d002c41d40c0c0080341d20404000041014000001c500c0810a030712060090001c0003141c1d80341c03603c1c8800c0248220200e90a480c000000303210800100394000b9100c1c07801c0390155000516152140320b451210b12854001c1601e42504000000406034180e00030141850903241b0f0140c588c1761610305a0080da0b06100e851030003120702c40c09204546103000030036080245107400b90b51046281d0703640899a040f5005201c1e0301e4011102804e55804c1641001c65a040e040f00682049030408001800c1c500580c51112071450381ca80070003600400a07840005c1d0740740c0090840342d00564694101c4c1d41e81d8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 893153111 1250 893151861 893151869
    0x2a180f09210a020715051b100903050c010c0f0c241508011a09010b0a050909070918270c0f03050304051c030801050103020726030a060803030c090f060706050c04 71
    0x21103042400200e17100740c22400d03120341c1346540e11545002c4980030070810301c800d100e1a5003480d014810340b2035000801803044249161081e203a140c1c450352110622030849a40180311000e101c0741c1411282020360004440143e554040d40e00c19800e854003500819500e401c0485016880c074180c9491728400052005004a90340c0d540240300c038120341d1003892801100750303d0458010b141c42d0018400c45050102030200c40340c807480d0117403c21040384001101c1040940d20100410181e0006001418580b01c00d4001d50540312000e00080c12540d141454541102e41281002100840c00008010841e400b6000400b030b1007044800d05a22810596140d6200b0301c03d00c0e2040d4003616000e00045690920501d6641d01501c4111840e071800c001980030f0f600030003048a005004421201c0d06442034250700081905046000d601c900d043c19403081150200d4110707004c180c2c0240100712a80d0913207003c6518040003511a20f000181c0f0300c0c045a4107016144c1c00800c2e080c2003404108101d00094054004c903 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 893154361 1250 893153111 893153113
    0x132c030418180206030403140f130509100e071206080633010e0a05060d0902030f031608161208041a0f0402041d2a180f09210a02 57
    0x41e94103580c489040301e02030742c256010300c0510b0b901c90015241450141d50b01030302a08041034014100203601040741c1c425144402001c4000c240390311003120350340304c4001500341038403d04003d050000000000710624070a0301506941d03500010000ca2240840c443c04a8201100740b02c41c41d01d4003405c940b140070841e0400102121180c3c2581160f445410303000258608002c07080f03a5841000c0112480102d106906402605400380010503031101c1e40146801514803100203610081c0344101070401488841c3c042180e0710500c1841310403480c84400c840f4003680540c0f09a55041821100c000340c5084c1d5034050100300700c4c1c0d9003415400d504240d0703c030b101d14411111b428140e12840082ca0916000340c030a6114001204001401424642e1081c0000c14600440f0f050482200b444240703019082600005a03540048501c1d450214184509003803040441d1003050800400c803845a00d2100100400500780154010071003648040c80b0380084041600310380140c04103500c0390b55010382d01c090651401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 893155611 1250 893154361 893154389
    0x1314030d05010905071e080601050415020a06050a0203190209030109081b0d0302040e13050c03030a0c0312020705151f060e010f030b01050f07080c03070f20132c0304 73
    0x400e034030488006d1010700002804040b000c4441c081104c482c82c0c000c110f1814003504020120360034051500d050768101c41a801440450784071b1070300320140c50b80503003515451401402070014541590303070b051a4401c0303031140041c0c9800303501c0c1c0043e0242a03000c1002d8580d0000280290411003441e0fa2012100c3c16441103542c6140301000480892040e4031502c070b000e182c6403002c20910240c0307141180b00d450248044580c1c0b1144940000c0c1590b0003c20607038081007e0700560750030503030090b4001c503481079491011030502e03500340c480d076485124070782c4c454030a5070344000010030505d540d010784410b1064680700100d5440e00e6450140190003e00d4229002c0b40b0301c007030503041143c40703801a89001c40043e90340c141050303000c6e410264281c2041c03104452441c02800030503844001040035104007809143e0071a03000c2d1450074907280c03c8071050030003a481990220135400f59254140c84120008075840c1c00240e8442d40b2218454490350303e104540240d003101c048d02c212400000240091b60003500424030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 893156861 1250 893155611 893155621
    0x150d020c070f0e040f4e1b031b0803010303051c02090a1a0c1606030608030f031f0b070f030807020c09062b050304030308070801030b1314030d05010905 67
    0x344500c42164010003660010240d000000d00344401511500c06c401d082c01c80c040c004820134141020302405079400b018252840860580301c03a0081ca0f03140d00b0700d0510203941c10302100c0e0881c2c04c003040303c00601481210401140c142d6030100b40da03e003283c0c118091036225612490010400d50103025407828040c1a404440100c01c614400c0700c0d155207000740043e0403280b500352014440050081a00e413481414412000c0c090400d0028840c00c03e40c50000c1c0041c03d0600c0300c040d089030040d800604044e441070280720102c2c96103070203c2e07800c2100e118009c19604c02864684000002503040944802001315100042019a5210444842c400d413229080c0d503a03000030480e0b035010215020b0ba48171040c080407500310b08290300c0f980360502c4821740b08614802c0114040719030110020080742c4940c000a010030074198008130541d0011201d00e850030b0154515200c2480ca404040c214900c03110100d00070303204100d60800162158820130303040d2521b50a41c0c806c0100203000c24820222000d00b41000a9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 893158111 1250 893156861 893156879
    0x1030204050f01120b04080c0d090e0c030415050901091a040201080c0a12271505150a210210110c0f0612072304180c020705150d020c070f 61
    0x90f040c0d9907050281200216142c40f10205080b000d001038904120800101080752002d00000840c42500e0315000f00c0b007464100308100e5044000d10001c84910244140320024403101d980c0343c42401100804038147c2c403000c403154018080b041d4003e1801e095202041c012241c543c450381d00c40e90013604d407418542d0b039040026040c0d118183c07100c3e000a00310910017041c0c1e0003030f82c0421b814540c10100c0284210b0148601c030385156411205079640d410200d41e440d810704c00fa01030198401e84c844045c02d640790020b408148540b20500a040a0448042920b828000c1c1e5520101c603103600101005c1410800c060064525040c5103c5040e00c1c1c00791016940c00d50074200c4521050400240005290507080c03c4110003221021b001a010000c0394220846a9842186000045070040c02401d0b900c5140c481d894100c1942c0c40443c0d1400742c01c0c54001c1900380d402280d280200d0b101915019110302c0103600310210f030301c15011b4001301d1510203d51700424801c005413400640e600c82c5941c4409946a08500c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 893159361 1250 893158111 893158141
    0x1e1009031101120603020603010603051617070806030f120903070801090206030a0b060f07060b0a0e0721062105060606160609020a210203070f08031b1e060103020405 73
    0xd0981a141d0004407429482400000710300a400c040000c0d110391a503000a174198420703402840002e445805000c00101048142a154100342c101140b040c0c54a01860906010007081c020030b0143d0bc900288840d101444104403100b00340c801e070707800724904500701c03061a0030000c003250007440b4501010030000c005101c0c510489070001d1604d401d40d924036803800090458111480d4100c88140680c034a810300d40c002030455140700d580040b401c1d00d184003e00c80305078030a41c8000c040710007020900000782c0d04a2050201d142d040c028003480868000c2c0700c04013512240d0710128440951804204001210400c4c69007207520500a0b00c6982d1900c0c0100500d5005174003410070246040078514000460545c4020000e034405080a814241d94480f007d840007180d000b6040700c2d0070441c10a03802c516080c45a0400b6001c00040248441c0c2801d0901b55640035200a80c00100c0d580201580410820072031094091001d401c0c1d42112440c0c0b2030300a442e58001e2001324001e5051102041c40b100516600d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 893160611 1250 893159361 893159363
    0x170901060e15010302120f2202130c05270a090c1b050709051f0905130818150c2e15050405010f03020108090a030f080907051e100903 59
    0x440c2036a141c0e002e200410030450400241415401c00000c2420300f40484040d11815250905682510b0a151055080e403444210080c083d041000301c0e90042e9540540d850110308919000110300e421014240c48074422800440c032400b01e0107425001c1281d90901504810700c09840c03140030300c1d0791a80002c00707032803410080e0340104110000c01c241510329428000e2002d4002c070304a0380460b0703942200070101d0364240e40c08010101009554400e280140c2c00140c001c002103841001940f51454070400401340d0624003c26616000500340c4c1d1449402043d4008200001c20303500040856580918147d8402442049580100c082100414126088803220f00c25041554480c5e5800048880001d0501d030f00c46002d14994010003040f6a01d882c032403640a421054100300046007140000340400000030004906035211f00c43d5800001d030f0001035040e614009003088001510b0398495542440c005800c415003294502001215032a02e007225606a03810507284501c0305603200d40c04030b60038092400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 893161861 1250 893160611 893160629
    0x2040f0612061406031e10050a0e010b03060105010e0402070f0b0109052505030c0c031903150824060123041d0f0f0c04091503050d170f0a020c0d17090106 68
    0x2021840030185c0c10801e8404100c1c58090b100852032901c03020084a000b924a427412681d0b500030034620302801d10882c48404c4040700200015813510000074402951041814040c9401080f0341c030801a50803004122250702c66001d000c4c540c0c50b400440000c110480e040501c9441010031609050440400480c015285588184c50750391510454240d9034400300364603074184004c2082012300c6400300203034044100141d070081507080f41143d1110000c01503400403101d0342c0001c00350300c29000050300c040c01c0002c81c10410803010303511000140c0382c0390341348c0c100c41404905c118001410040e0560050003911a168882103401d24071500350009040c089a0f6981c3c44002c88020440a814404145510550946050f841d0984031038403c1c0583e03440b0050065241c0c082c402c00c0c010031600344080e04110300c0c94034200d402604003a01464a05001800c604901c810f4100400c04008141d0100c0792a07441d070f48226070005483c088010810245a914090800c074841e01140c80c08806004e10411508815 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 893163111 1250 893161861 893161873
    0x904080a230f1312050a02040e010212131103060705070c1202010e04150815010e0703021306050904060902160320030703030b0f093d1202040f061206140603 69
    0x105150b8440da01c070b034501005040e00d03001d0001d50390031040c03800140d440c490000340084102c0e40c418842a200c010030ba50281d07034014400d102d4161104e107502c69021511050703009400c5401e0800300c0402d05a100c203150903004520400030880d0300300300203003a00e502c1a007140d043d250b40c40315811807a200e1440002e001800280c442011450103800c445c0710203122994111140e82c3c0e81d06441e00e0031810b031030345101c0c02441e6401040104440b20704142d2001c0e40342001d40c90050311030a50b0700c620f44a80220001d120002c91541c006031a42d5010700c0103052080760444d901c04101d203140400908041e4100c00240704241c40c107240c0103880070b02074a102c1040d0700450130025941e80c250041c01c1900091508904800c821400565840c8a00c500404010780a60b0210755450481c00b4100b000c04600c115940000c1248441d0384048140d600803a540000c041a680e0300742c1c40002d01401d85440020000d078100b1001144008001040000c01403080c0030030410241c03d00040c000010080325001d42c1034200d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 893164361 1250 893163111 893163127
    0x31b03081206150307170a09020307030f050f0607031406040c1b030c0803070806090c12040818030f0c0301181a2d16180b0a0903020904080a23 63
    0x1040001c1d0708a04010000c40414030480c41011554008542c41c00026104e01c505119071001010156042002e10350140100315054011a0751900180320040c298040da0420070f0906c60203000c459081840481500c4c0603040081000340038001c4641008080c50407030001c0381c4a442c0a202c0c5080718009529803c1202600c1040b000b0180c100f00c1d415001e01000011800010701420001c6208600c192541000d50401205000c10f03090002c250420340a01006984003000c40508200d0b07106a2000f8429a2480501c400390801c4c4141449079030188903913000b9458807040850300d4001101c003a0002c0042003600b800d034000e245a100700142013010070141005501e03500c0c1040703946c44183c9410491400f00724070039807a41d444041004004c0c0901034014006400c005140c0a20328140c01c2c500182600b410803102c02e08586c032489441044000000c45281d194001e4445000541d0000d203501d42c0c91505050801c042c1d0b0207805a9400224460b100700c44100c064060315041c1617048036035504003800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 893165467 1106 893164361 893164387
    0x1e1e0f181d06151207140a0906031512060e123019092604050a0603020c150408070609060c030e060105180402060d0213031b0308 57
    0x182d000680708060b01c5000780c2c1c42e003034400d070340c2044d09032108401502e010340003c0841c64000e1000c1000a290342d0001c03005000c0750103544040c44920391245942c2074980c2c181c0a4242d01450241c806000b06500368000b041541c0004210b802d04281d82201c80301c1354111a03540c4280845a1152080740b00252080d40c100405c007170a05651400c041c0c1001c0c040c010a038503440816592888068144242862000381c00100d00310700c1d580790710014101d050b50386c3c403601a59000c2c4103d4000003403194480d108071181c060004010301300202c0f190030150261031015001341c8543c041404118080703102441411481c6100712030000d6003c0000b02b001e404d0700c00d0443c00766601c0c1c02c10001044181c0398048443c9110f1001038a202881d551440015020700800d150340c46260310100d40c441d08040300ca945e90041d240900c90414230f450203580704001040d0b030f901004100f40414861242801c072 = true := by decide +kernel

theorem cover : BRFrame.Cov 892985611 893165467 := by
  have h0 := BRFrame.cov_init 892985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 892985611 ≤ n) (h2 : n < 893165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
