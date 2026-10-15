-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4815
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:49:38.61136+00:00
-- url     : https://prove2.me/submissions/f6830d7a-c65d-44e3-95bf-7ae9372c5866

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 865827338 ≤ n < 866007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 865828588 1250 865827338 865827349
    0xc07080f1c050c07020d060902121b03010608070602120a02010b041404231f020d060e100803030f0705030714030915060307030201020c06160c0b1c1a01030b04020702 73
    0x3140c01191403640341440030701c0d40420036070340050240380c0510390400405025071545058421042d811003c0465a2034491001c526040b550f2500d83c48240034544616100944126540a207030108400900811ba1101e0031140c4400043c441c4102603407040100e02100640000546400c01082c0000a121310f4a01c0118040c1d444040895001d10605010030042201000a00500815207081e40c0c1d0581500d102c1696034101e4056038a080c00c1024442113540340207501220040440400148807a55841001d040c0444040d1084800104a1304012840803400400c0c2c80c03040c02d0722049004561201101507696038005442c60f410802884142c0f04000404002140111441c0004240d190150381016800302c40141c110340c803941003000d04101603a400604480c0d8194100d4005230b540c010340c923100030f10b0740780340c440103120022400c000141e680b400406418031070f5401c00d490010019040a6504860b0207200200074101c45020350100d9510075440ba982c82c82c00034000600e40342d0130750002070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 865829838 1250 865828588 865828597
    0x10051605071e0303020f0d09120618260a0503010909020d0c080d11070b0322050a151b09061103070c0f06180f09022104030c0203160e0c07080f 63
    0x1200b03424410010168100030381c900e0306540301d01074107840407a0301c00182030031110710034010304100012001c414044640c1c081c0100c1c50225028000d08401490800b04120240601e00d109030302d00752506012a5203d4200d40004040f540c03081c0c5181c1c201100c0034010300303d0010907a00511003030008400640c0d481102c8028001000092903603d01caa14003d10022982000d4142e54018503001c011f410034031020742c1d4125081d8401400c6003c0d0034042c14011526266015086119601c0c1034000c1c4044e403040c9160f0790400040a0003800294070030100000d4440fa4000006102e406c010480d2074030070040944030843d000c05807071070107500c4c4d228043c11610942103110258800304041048640180e42000090b01052644100758a059200d0131a6089440341400840e00010411000310150003560101d00d0110060f54050505081c01002880c440030124000d20403130750000b008a411481c00300880e076540681569039694201c000c0e4070354100b041d0440f2091401d0101d00107810581e000b41 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 865831088 1250 865829838 865829879
    0xf0c080a1110060e09070b0304080a0c05120403030216030f0b0603100c181a0a08040c12060f050f01082a0a120b220201050c1609060806061005160507 66
    0x803c00303d00b401d2091140d80d80140c5070500e9540119410025400c4d101c080c2c9500540290f503044d25403c030000166501003890200626a003e42e8800714001d48050005d032041e02d00071303070813641600c6030310103134100e80e40d024007024025490100109001500382c44050b039001c00041c1c00c1d01c08911903171001c075040d03854814520f030114090400c0014644100d0000b5001044268255071002072584070f0f81603039100d03514044013045860720000d4180321040c40c001000340b440c514042e1244886090400080103a01070b00140e0702e0405022808006444034002d05172001d20014194119207041a030000b8090f02d60106000c0c550200c0100c0c00d42c1d19064114014109411550040003051401581444000340845030303000e00c2840801d65480d400502842c11542820701070b55030041000401c0c60100088207541e9075032000344002c0341200b4640c105d20101d4000c41c0c01c8903615190001000a161000c844840c00200b091004503160424140742d8180b89015030151030002e612004688110908907246 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 865832338 1250 865831088 865831091
    0x20d11030109090b15010c020d05030408070e06030d03060303020c0d02210d12020315060a1205010b1b010b0f0607020613031b091b080c0d020c16060f0c080a1110 71
    0x40c401401144144c00750301003019185c81900c02c0c0e8540019000808002020340101e4215005900b00301c0d007007048502601d219003c444000ba5584a505070035901200e000d0300078000c00d600d5030107140c080e0141d941030b254580c001c1c192400680d414814460401e04059074480030798101c0300146020800003c503010034030400741c42301200d101e00180600d049030044500071481002001550482d03180c03007000e242021140f02d96209405142220710903083c00480b0301d02880c01c0c2c00010b1214080c0c00415407401048480751245000301e181c90301300c403242c000b07030307078120651f8500760520f460b2203001001014802480d060500c12205211000d081c0550400c4a503a01c09015078007200c01040c0d804801040c4010090001c0022500345501e403111100171502408420404104003c4403141039a00039010b58104544886264806a544842d82004281c40b051060390110f0380c80d21405050005a641e5143d804401416654581d400c1d40000f080314100b2184404045000800b4000c0c802c0c1c107102c0b10340 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 865833588 1250 865832338 865832351
    0xb07060209010f0903050c090403050d050f040b13050606060f0c150105010801050d021e0105210a0609050123060904050a0504140c13020c0c280501030b0a09020d11030109 75
    0x25144014104010701401140351040000400020761f03000003850a9901080d103880e00c0c90143e0b000c1c06a0410103001c0350a20040146022802101c070348600c0c0140640107040c1c881401c3d104141c0d203907550241c01c40d040b5000042142c1441d0008107000c02e940e252981c5000010746080d030034203803402015214520a440100103a681c09070040e4003400742100e964070003201503800620203034141c408940007901c158040082680c098020b44141315a149640d59000d0704100400d080148202e034a00042c500d0000085144035003441070034143e50ba224012003588032504440e005003065422429440882008950039075100e074040c807802558021804103c4e4101072503d034a00c03c207200c02013030482c0d2003241d078101c2e81e035070740c9000c24502c1880900041c0c4c4d42144a00060a19140f08501a000031144c0704103074840b01b040e02d1441c03000020600e000f12032078495004609031482c01e80c880307920100c0e41c5001c3c03100720b031154014002006142000030b0045100e503110740854009034020351056a941c0c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 865834838 1250 865833588 865833607
    0x1003050408130e370b0a0302061305120616050d09050d0816021204180f050906040209100f1a22090c02030306150304050703080c071a0c060a150b070602 67
    0x200100001e04400440003007000d0b9411050381150702c0c4d100740314051500c0d1200c02500381c9850640c040507580140c6490307550000002124030f102010310030107001c0d42c500d514a20f002ca4010900382c0c011039072102540740024100780700725995045200c44d2a10b2940d1006000000745080140000c0001181c441010328a4484d810b2840809845d00c0c090954102841d0b2440c4009002c040b241680d4164000c10b0f0140164544100203000c42040413038907900d00000c1c0300b4281000034505100d1032007100d101c001a5920b134200002d80069101e09200300e01001c806000d441d11034242c0080705074800c03c981c0e08011001d400090b5030300da06048140884103c20060012000f80d01507180c0c502e481c1e0000314a50300303100c00407600550300042101c0d040349020000c10100a414401a80110703004020152150755181401d82c40c0c40c1a0701c685031240c86090003141c84958290107031180614100040c0c004e65552070300c100f01a048002c510a00241d055001251441c6000080d0040358055034005031141c0c1c260 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 865836088 1250 865834838 865834861
    0x30f0c07031e030905060a200c0a08070e0601030f020d140405060115020703140a020a091b0903021f1421090106030503070f0602270411091003050408130e 68
    0x2c2150b00300000036284903101083d00100c0c0c0c076080303850036180c5603640d12040b0f2044071500c41a003108041c1040d032036404042c0f01d400107070380000d1150449440c1d021031ba80700601a035880c86482615074000c45100054021b42c040c0d4410000810384690140c5400036080c1503100300c03000a00614503100300c0c5424030007801780070480540074001d00554803800b40141c5002a41c0d0f01c42038400201010402c603914056030005210802c0950303800b42051135003544481d80d94000d000c0000c59075907041d40307003c10701200742d114002c1001126000741040614a290382c100c0e040003114244200144207114034002c80c200e462000800f80c1010009650132030a0920300390a18502c13015110010380c0e0304110050012420200407180003a07804000100322100c82c4c42d0901c00f0707005e66604000150207030040e00c0702d400041c008680d00b03484201c030200f10744400e4030031964850041c00030303554000d00340b00580c000d604e000742d00c0300d50003a00800d07240341406020360341400b915200360002c40910900a0600ca041c0041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 865837338 1250 865836088 865836113
    0x2190c1d0906163c09320f0a08030f0703030510060f3204030311010c090506090301020c01020f09270406242c1902030603030f0c0703 59
    0x10143c10000d0542c001085040342601158100200f59013070412440f04e1081a031580500d40030114201040c5540070700703105900d110f50072400b025410804607450720f00c4514650041c1208155100d00c0318403051000e420f03e10750b0306e29000f5460440120340004200701a1114030b00c424916940c0c0d56161070700a0135964042e288807110800d008040c000355030060414072031844c03546000a03810502000041c031512031960703003945c004410a091018032000800410070b80c3c2c0a6122032580c0d0000d9155682250780111605002a03c601c1e028462454807000415114000900250600400b4001c036422a40109a1440d48071000070300f49480b82408940448020729102400210428460340c14801000003800105a01d0707070f40c4041c4000303105082d8158400d010170104828060f46401090200502c61101e2500e010f10001c0c0504505038942d01d000d100302e1294061980d9000d101c101c240c06508040d000f1b0307130305001c2030000b591800a024094502080408001c0825614505101100d81c42 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 865838588 1250 865837338 865837351
    0x1509040b0a1d0601120f0b01120c0b090d0809030705131b0206010803220312020f010e0a0825080313021e090601181502071a040602190c1d0906 63
    0x880c405060106000403c0080c1100c4c0840035052402c10300385841066501d50f0003006021041400008c0b448500c0d000d040d0900c103110780b403000c0040f2b03200d007221011409102c3e400341d440310860001c80001100403015250b000009030403140c0145e1110001840e0385c01c0481545000d9550f140d80030603046a000032207140c0c00550001e410300d94100500b26889100710a50b0203c142540081c150780e6141d2040d15400550f00710b4103180c8114290380000707494000c03051180b0071642c20201000070400d0041403a208023544a04000e281031809013603c8180e10250b1034aa000c59030b45400d0b09e01003010000214420400c0800d129103040c0300344104581d20380760400700880c00f1240b458207021610b40d403010300c2c0c1100e02428007240e5460001e12041d011182d80d000311540c52809103900c0551600094440152142c0038003850410964985403100342c000c501ca043c2c01640036800078101d29400d8001c0046241c001c00c15040c0d03107910b440781502e00b42e000d04003c9601d40582000c00c02d0440381030100b583c0021 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 865839838 1250 865838588 865838621
    0x3261315290901030f030309020f0406060512010f29040e01060f021501060509043c051602030f0f190801061706060a051c0501080c03060a0519051509040b0a 69
    0x5044d501c03403031900b20b5110001420b2640d2880440f05550b21600d011666a000810a01840d43c480303030001c210b50048540011181090f100200d6501c039100401d00c10380e40a01d140041002c002000d100c11800315600d1740307034404800c10000c1040026100030501a18980d1500307100d86001010091070701d03161032569020764a1004c018000181d0000c203e6040390f50444003c64a0410007000c0c5420380440f202180d501000e455040210a22100030801d100780106401c00c000e41d81c120710081281d4900c0504801a04100904d0320600c10b5400603004003400755040c142441c02c0c2001a1080c608210b0401e400704000b030004005131a4043c00740510162011014081818550b002c00c5690150070303c0070007071080c0403a146441404194010008039412041404156503641300c0980305c585003000140680208000150382d10043d004160164804042c0c2035109003030840014020000a0311010b10f0100c580b103101a2540e4001c00d95004a020781c03018009428200959001c845600e0300e4480590f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 865841088 1250 865839838 865839841
    0xe090d02070603240e31080a0212040905220f030e031f060815040f020103110904230108070515030403032403032613152909 55
    0x180d40840d40800b00d40607410041505500e03440e04800400d0036211030140e00318100c40003d115002181c1d01801200c150f5103400c40c02c04050040c5002c40d0009260031908242e8034a85000a07400200409400c1c2d45803050f28183c28048540030f8881c0c1c0164800700002d034841c0c081c880894103c1082614419100411901d21080c50396401c03880704a202014041c4403200301480c4240d1011b0150030b5101104924400c0ca0a106111140052202c0e0041e0390b220310840310320b0a448041d0000036800780d904602203141f1841e15600440140c040c18615031511501407003078582c1919036000300c9000b0000008000c0b405030895100340d00c10310050303011041d2030740711341c1c8100b0182d16026850446045a416415502d0303480303080640262010402005103030070344100300f0b0000a0300c040403100f983d02c2940e40c04011020054070700254240221812002d045140c082011240030740b99803012580305001c0e41c0c0c682c58074204183c0c204d07a0040314840300e131001d1000000c59510a45a40c5200b01c80848030340005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 865842338 1250 865841088 865841113
    0x3050702210d0207031e090f15020c1002060f06030601120b0c0c16030c1a250203010c0324030b013f0201030e1b0411040510090e09 58
    0x88692184030201e00c00e40602018449021000850311a090440c005554828075890000c1207402d0304a0400c8040c0c510f000c1101e6000d00ca10024011601c6109240185600309521070b031f0800310082d228000d6201e0042c1400403a11106600c01c0380c001c494001d081e2030316102818900c6888024020f40c40b0b500403200510640d403031040b00c81c062940000741d00d0074a0b80c40d5404101c56214030f00c40b4000c68441e81d103098001d0070340d21080707400362480b4101e044505a074030310071110161746042580301c100e9028088981d440c51204400d40b40f040e8003407d9048c2c0826107070046400c449880081c0303c002507c0d18031126605100e038113000078043c1054a030400491841c0c42d00b40f555841801048162400c407444e0000c0701c13062508072480c3c560030026071200031054081440c2100f103280000c034040f900f0000620011b0750080380d0540d4002c048c0141d4400c01c0b944000308401410f4880400d072103513005100210380354981942c11001c48405446148126091000325007078040002c00c00111580b018203079110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 865843588 1250 865842338 865842343
    0x1b150405210f0c07050d080415050c030702130b1503062e140f0a180603090f0215070b0a0204030209101a030a0204090213051504060507080d110304031d0103050702 72
    0x10b100840c002155140d04200400318188003c42d480b40d03522038040c02e841003d0012140007442120b1030003078440010748540e5010784413801040902c40391600140050005400d1222500020303200726400040c00038270000000c4c6514804219200040c2008001c03c0400e09114800101d40c42c0300032141071504d1411000d0310a440c590381d686404110300b121880001840c00c1d0241c03400320807082905034540c4600480240085200003035845819490440028003078000e01c00c40d03d2060300f01912400c81e04064080c00912080c0c00744881503440100280c50118100d000c503030740141d0302500050303695440c41c0104400c1d10300c05000499100c104440c2080203011002984c503110700054281c6840b5501d001400009010b02d0b8490b84140e40000b0f8031020800c900300c900d070300341c7d80c2c00c507070055010f803ca140100f41030059014003000304034100281d0000c01c0c1100c01400300080000c001180380006142c640166420607181103002c00c1e0704110311000030441c05800850394400303103010401c61806040003507 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 865844838 1250 865843588 865843597
    0x10f0207021e0a030203030c0102090102070e070c030f050408071d010b03060a12060f02070b04120206010602190606080a0c0f0b1305210105090c0307080303060907051b15040521 78
    0x41041c001d100c0340e82c041c2c8810210340d0065030003d050740c0e155080301c4801030103540020744460040c051640d001c100d0b07007941d2026901900c102d90f10b01d04880455641903e0304110401c1030800d0041c1404001a1003000304a21406041106420189040c414030100c034580c106810511103c6801e0040002986a984000301103458510452028401c9800c01d04002d013071079a401c075501d50000401030300303000701c0c001c410b80114170501074091400701700103040382c4480c2c00380500c0e001a040a0803601c10b002c0c00f541c0c1107503014002c0500241e801c0e503a90b1100c1c504512100708907407070040e0040400c007008810034404003c00d440c00d2480c0c070340009031040c5644a00f00b405010710800c0b21851044c045101110000782845000d0000c11681c1041752903145d881195013080b134441d102e1a400030603a1030b80801500c0c0a81000762a4070116240c410080e540b0b03801401180b4070a21400402c0107a1410410062000003a5002820700c1810242032036030400795a0a14a00105d60341d00d0800315503401042100d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 865846088 1250 865844838 865844869
    0x1511120702060901180302040908070506280c090902310b120a0e0105090c040c0915110a0503040e0703060b0a0c1407030501020d050f1e0402151909030302010f020702 73
    0x711220741c0a0803030b105c07451081e0340003e50450f00d481040700410901d0f500a099090081301114980d603507000d5001c2e25a400811036801401c0d040e59140311420090300810340a1400f400c0c400e42c1d29840312944030481e0450020180460300d080a43d04900c207140d40807080072145450552412401c00b50403204a20078204282c000000c6000040c0000896038810224100301070024011810030300ba040b560f407a03401c5001489030b460a0074103241c032800342000b542115200062101c0d52000d01d0800d444013001003c581c041402504000e2000a0041c0010000303041d200710281d00d1420114801811240c1c1c541100141310020020300c2440382d002041c6031040c6503c01c9800c0c1140c030341d000c4000e0819019520040240d07002140c180c80d4184070750411340c41080003c00740480b640c0e40409200d0b84440b4a040004050001000314000d814036811240502c0325600d840d40c984025510380580400301c0649100000d50f03055010720401da820b0186c1c0171071010712132096013007815603000140c0428014200c1c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 865847338 1250 865846088 865846097
    0x304060507120c0623220605070c0c03050105011805190b0301202d030f0702010227030f07080316050a0605400803060103061511120702060901 63
    0x62821610440c11600c803264405018011510311140b0203080e0501c681400403000217140c00100d680000b203100c02450b42900310f05040c014410b848000c010000601094100300a068038100403031b1441c00010019441480001025031501c00081000440310140c030072180d003008144100e4100303084460302030100d6440000380500310080041e00610611340c0844400b40010f00862074140700703e01400403070030b08564041c1d05124461a45c2c041e628070030000202484180046045c43c42c007400f0f0a40d20410a000051800d5420f0700c070344503201d088603814240600f03c0e00b444d0742c0b01e060520465103100c984100900400c0e0400c002103459020340032008040c410300c000300f031050040822a0707507541034100604011a082815241d01032056083c10b90102900712060246c0d88040c08001202d16245506c071001c01d01940c0d40e9000c480e0340081d04c0e550426444400114401030303120011081448192a81c54100705940790240c1800d040c2c80c0c06c041c41c1c010a000c40405038440100300c440120303003440c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 865848588 1250 865847338 865847363
    0x315130302064510020405030f0109080301031e020301060b1b010b031c03151e120c0b03091c360e090322060e03061b03061305040804050f030304060507 67
    0x1070070310890f07054454081403282c0885800000250f034000c0095074026820744070325035454642d003130030795203141401010302d90200b00400101c0c004010580e90408496204080c07a00950002401d50310700c1c3d08020840100000d24004503450141c801d16440f031044000d116000c40d42c000280c55407208000e8080d40d41d020a10800003c1c2300c0da00c10440050b61960b400c00703003034503180c04142c0d44070703001200c0003000c401280c0440d0201c1c0c40d0400c0138415034841016800b85050a40d5040907810103002000184261108011889164001203403600c00310707512014072082500403001171040d44c40e010100700c10a840c50038040c0c1800c40c02c0710161001c50b00d1080c41d644032354042501c0c5110303040c503004109950f0200c0d940c0c504103d00011040b9200c3ea601c0103a4810608205515050291030a00841c5d00039101c00e03280622800246074800c07002405040e8400f150588601a0b91046400b1a102940001c041c0314600e001d80111009260039401541098200100904148070307441003c1e10015180a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 865849838 1250 865848588 865848691
    0x515030604140a06020309060105031e061501031b02010f110702090c030705071a070f0809031605031303080309010f0902220b0604120b0a0c0c060b031513030206 71
    0x1c04000542c0c013110441d524640302e00f507681c030313040207000e018401e01401003070a008210420820000064102c040c2c825500c401004c244442c5840c5501414551030300d009100410300700b1008890785401c0d40012a25600e1001c070041120f90b448003d100c291414000000542c54a18040381e004110080e0541d90b610750307580980c2c0d24062010018941d24044070081440216040c00310300900140c0c803810651222004103a82000782118000415807090040d05020401c0c0380e0010b100c10b0080703003a00c1c07404060798000e074504149608140c071910340010502c03c140303a003449a003007120703030b1140100885405940000c141084440c400102c1d43d0000c21200700039200b561040304045401450036503101d0f513500c1455003a800c101c0e010383d11360b00c4840009070200d11502a403a15040386030f0b640070103440c03556201c50080c0101c00300c0e41d8152284440505105d0b5038401480d0085032014004107200082d440e0080c0307006001030600320003203c2c01c802c0c41d000c4170380c3c81042d04807011541e15541c0c1c5c1501da103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 865851088 1250 865849838 865849843
    0x60203041b06020d03050c030103021005030a06151107080a030c0209041118070e030a050601052e090519061d042c1e0a17040f030b0a051503060414 65
    0x2003060307500c451006403001507902e0b00090340d2500744119440070300895480102d030a02d0745c002484043d40011604c90711001952241004680c0310300349140000b1055114850144c0d04001e210400010950941c0002001d84d01009500300034091207004081090b16a50000d0100314000c074000e00400814010604203c3c0350b415580010b000a40022107440c92000c000340001d2007034030f0300b00103c0c1031500c01c800c640c03c0114400e91100d030003800420741d6910300030900070311580c1001041c04002a2044040c3c41000b62240300c040408251383d05402281000104038690442e50509600d915400004100640d0085a88104140d200d40525026640c0d400414040c1c44411040004040800302c03400c0901204c020f00c0c1026680001200c0316141803101051102180c686545c1d966480810788800240d8248000d2080d5102810100d0905590303140e2905800c000ba0000c54154000c8030800c51510708520815900070405900701050b04400c00c0803907140c140141c406400000c4218005e08101d204 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 865852338 1250 865851088 865851113
    0x609060f0309030a090e040b16020309041e0c111b180406140a06062a080a0206011809020607110604050a0b04180b1f120203090c0a0503030a020a06020304 68
    0x4168510307a8925158010a0f241e41c03002010b480401c07600000418401460040544900d50280070301c6080d44500c0e501090000082d415101144400c0280c1c0150351100d0244032481d12207a0040b208601c01b2031000c905907008081c041e410898981e0688403803680001d80c158840030f140c064480b2818410300410040d01140c5412242040c5c400700b44410012554004220017121030310003807450301c0d401442010b8400038861900015101017182a4520000c0701048440110b0001c10f07150309610b42e2000c0c0c80703800400010380135070425001080180d0042c603070031161038150700301002001144c0d07000514601503160301405140504601240a840c0c1c10200c50141100401a0807955540d0510715056800340c05188015078842c000d20703159424134014132540840003040c07241e220590310140003101e0341000302d0b101000450440102c420246100442c02070b0700c01c1c0080c1c02031030080d10034400790102d281d0106009510801074048181d50104281110340d43c000b10160b0f894440341400c1a480c2803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 865853588 1250 865852338 865852357
    0x15080109050d1734050d060e0115030b0d0f030f0f090605121906140310140c030c070204020307080114150a03020c1002190212070f0f0204021201090501060e040e0c060906 75
    0x882d13980300c980325005805448046182c4100784481c6441d149141140e400a1082e03942851000d41ea0040d13013406500f050740024001303895031181c64102c0c0c6950456120001040e4049900f1040001c0c503d07501c00804510703288141481e400c0c0624084008141d4813818440082c00210780001c10008030340950030502c24246c0d4002840a907490f000b00058001e0480c04491092294250408044600e0700a101c440c401451034180140d41d140c0d50180143e10003045c0c41d0300c4810410590300117a0721840a14003451240c0d0b280b507695810041c640e421043e042c0c01403441084400ba9491021201200f29010828245000b41c3c030303840c0710144146020386134050710701c9150011406501349a0000d41c8070300f403800541d00b00c5d4400d0303481000e500c0c11b5201e2900c01914003200c01da80d642c086180802c4186807039101a1005203441c140d006581c1c01a8401c1c0c00c407001058542c001080400e510011010b007a10302145c040155010401d44141d884c0d4400d2a418003d88001c0345000c1070355a420241d0b011042e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 865854838 1250 865853588 865853671
    0x190807051209101505031e1c09090e0102031303050c0717010906380a0512060a0b010203090319050703020907030e0706050c1f15080109050d17 63
    0x2400c8001030703100d610038420f0002043c0780c482c0800c801c00e401d8100740c045503030140140c40c49465020210050020144d14101c580c41542100e04c0c0040c6c4281c80f4044c920026038a92107003a0911103000d0503101e401c00c2801507070380123000740603044507034041804045a144c108655510f40604681d814205941d1240c1202050103900c1100d00b40190014060b06109000c02c001060040c2c800f051030003a80011008000c14140002003d0050195000200d20000301100030095440307000401c2603a280480c2c200c0b40d0040f07000d20240502c58028140e6003030003400614100402440030035501c4a4503071104454402c0d030b408400502c4070602c40003010f190094030101151030840c0014014207148031403101a40700f000c50015020f4460420b407854020020b0181007640c403602500c0400d01d0600d040740e8091655421211020084070891500a0810500120344005036042150038052132051010500010410026094003040403482c0d0003265180b510203000720451180340c101328610b0070701400d40c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 865856088 1250 865854838 865854841
    0xf060409110616060e0a0c150203040e011806050a062709050f04050c0d1208180715120204050306070c0303020c152a0901031802060301031211031908070512 69
    0x9200401900f00031a0080c5000d120303039440d0b4100b29664030a215000f90000481500910001060f5150000d0f03400c000d10441341441c0e100da005c2180400d0a038040d4020029070700075100c0145140c05074000070941150712080281c80c262019003003102c810703203000d01c0ca020002204105000350a40030301601c03004008104500e81050319041d011020785081d196031180106520161034400940355040390301070002c2034096003040c0300786c0b001034010302501a881d406005643c164141040480d0003011180d00c420205903035440d003e044c890700031100b05551401004103000c1c2d5180081c02c0c07900074a0740e1510041d41c0d00c950a04030002e0103040c0b8045604d000703200341d002c25602a0403072139005200710198801107142c0b00414004940e40071502010740101803059095940c040d13032001621480c2c050500e18600150b900044051380241c104942c205090b011901d1013a40c0042d03821002d020700c038002d5240000d04d13101c140005c4e5940204400700040c9500060b045c502c00d205803600a080130441c42e03000d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 865857338 1250 865856088 865856107
    0x16090b16020a140105160302010b150d1406030a081c0f1b020c03150720010c1b05030904020d060801020a020109150c091e032102150f0604091106 64
    0x24420500800c0c0c1c841c882e003500c04201d14620700c039401c4203244161907551a00702440101c040b85168081c056017555624501c264054540c41221045a0100024281c0d149011901c00301104d4940925003080070081c070410825442c00200300c03030b4041d04807001d2511110700d50500c0d10603907200000203800b02d0808556035001209a080382c240320300040c2e40e00c1805040010103d945001510340e059050b800444a130702100d6910001d01d41040c042e1505400c16403601203544842c003d44845058160754502821040f41e0740001c5841654401d6070021005010645482d0354034000c00c803c8500c1190300107403d41d1041d415a01130030092901e003000355240c500014000c0d00a0084803011b940211180d00d601c2003410703d41c811104c0600c1c06442d07603940181400884007040c01580c410400d40742c1d0004021000c100d00c4d6050750240e060031500166251059040282080d5010b800100b9104280040c0a191882d496940e0382c000c200740c0c2c00254000303060808004a6811020311070304240c00040c0103ca = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 865858588 1250 865857338 865857367
    0x60f0c0c10030b0a061b0f08040510080f091f020a1b11090604060b0403060f0f021222030806091005040608240c0403031125030201121416090b 63
    0x45001c0f1284c4410755921542a40c441c2c010000e8040d80114104caa40001a500c2c500c14240780d00484402e0b0a02d500d850128404041810749140810a844200a0002608201c06030300000f460058040d20824990328449403000010b491180340d0003140c850070141c801c00050212803240c829807e400000ca060520358031000c459a140101c0040340040d249080c1409401d0403204191001c51901e031640e100c0000820410245808668840d034481512120b60f00240484a9000001c0c66480c20b1072b40403400c4080050b08400e150743e030103c5c240d00103c0c0d00207540d154805020354081c0004c1d56030004d0740340d001d0303d26000a98804d152020220380c41c00001010f84000100c150500031070007448900c600e852804a800c0b1240410400091000a20480444529000050403074407104e054041745c076540f016440042080c40b1740000d0030010741d039100c40035030512181a0420418800c10149422079030b5001045104600d089010440c05c640c03092109800400c1d010308916200c6140111800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 865859838 1250 865858588 865858601
    0x1110f070b030702010b010c080d020c030f040b0405010f1e030e0a020306280605090105040c0c05150a2a08181f20030109090f14010e010e0a02060f0c0c1003 69
    0x10011761801000240e554000c10310030701841d402120701802c0c200300724a95800f035030000781d00002c40d010a01c01c1d503c0800504000d08040d0480045103034940f42010001000c1d03240042c81c24080151211061000440c001050004c0707101610b004100f28480c0ca2000380b03040c00e4035200075050700c15601084910007003030100f4450b078690306c0101014a400740002c01d0680e0083e001c0c032780d400580503004210342c0c9040d038010b00b428581420701c42c61003000342c0c503410300780031841d04070b022801c142c1004c000b4401c110b803069010550b039000090005400d04060260000490040d501c103012202c00400c1a0100c503040c0012990348000c211851030503841c4140308641011f03001c420381a030520002e8042c44a00d48218415406a500d282e0b003168030304a90b203005000c1c00c8074140d4000e5107008110340815400c0c1c0290240b110140300104a24044602171800c684680c00f01d9502c64202c07074001001603540e002210980180b80d540c0325107030060450214182401c40408540c04a907005051601c15013540201 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 865861088 1250 865859838 865859851
    0x60f0a0b07121d0109210c030f03090906080331090917070b07030903030f140f1b040608180604050607090e07050d150e1504060902041401110f070b03 66
    0x43d400285000d08039122034050484450120b1059a801d00225610078441118041c0b440e121110320866a140c104542840d03030010741e214100001114103241d04182e80100401000b84200311a80c901001e46882e40950380c044554903081c100c44c0c03e001030480d851446483d17101801c5081403030340d600411000707007000c3c982100d407403110345c2400c900400e81c1c000703440206170003150555081ea10030034100c0080ca000d820850501d90340e0390b0700c018101c486114680c800d0091a003106114200a41e1140b080c0710014504992800000c002c12201c00b80503042e207040303580506111050381c8600018040340305020700d082006200700310400081c4100003c84d2030240c40c0c00d0310b403400708903103c3c40000c003c40340c11104c1c0c8003c80c00400a000c440c0849034044035000202c805a450040d8a5501d80f425084040d03d811400c0742c000074081c1c04a01d0644a0300c0020000300404515280c941480e00c02c1d06040c02c01b0040c10f01c01d09848412011606100c0c1c521002c212a090300c4940351170340d0f020442500143c400e0b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 865862338 1250 865861088 865861097
    0x40507180e010e01020c0703031419110105060a0f0b07031b0302030301031a150108040303140117010b0405060a0b03180a0f1509050c04020f0d060308070b070215060f0a0b0712 77
    0x3d150314100f0610845003201c0b0282c0117002d52a0071174400b074650303100541c20716265a000304880c200f5425403c1e0000041c400b5076491400c4800d50702c1c5200d00b5102d02602c030910900c0d1000d400c00c951910380922000319562200e600f5111010750070250f0b8240d0b644c1551007410122403814034209607000c8000c41c180c0e845501428440c4044001002444a04803480b60103a01004100d208a40c0184c4041c1d51040c841c0c82c0105a141e00003224680804080c1c1c050185900b043d02d50051044082c020010701503405c1c2d4080146140100010361034180387d110302030a50301c0000c0429001d40c9554000f10340808003008035031445d000b0389421a030401c0459003c1c0e441d02c107806401c040c0c0300160300a584007243c011009040c044490402c2100960091400041c0ca200030482524098110f015000041d4050a0103540320307102824804400ca40c004d00e5203003190088680804520780d0030500f45d40040d004d03908030660066442c00710749003c0c00360b0059524401d011540034200484408a09080350040d41d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 865863588 1250 865862338 865862351
    0x309060503220f21020d02010c051e09091e06040606050d1a101e030b031b0607080d051603060b0d0e010b0904050703060e060c0f03040507180e01 64
    0x111101c1c0015190360b6108000100403802e401e0240b841d03220001e0040c62070280c8688540d41e41503203c01c03a02403040c141c840c05020788400e140c050200c2041180140000d1101c0001c807a0020070301e00c103202d02000888040c85218848801c030405592105002911507141d03810a18213840013004052005e4004024000028403d42080c0c000c010403600c95803a0203041c80300c0c4c644104041c00000c480003860441d0010070109668490000301d0000c1200d89032080300c0d00d0040d00603140c0180c941c3c8001e0601d82488851065030701d00180342c00b150b824485444144050340000903d140c454507234007500014020901a03040030380c540c40a8040c0400b0503800b1302c850088041503095034010702c240c540d042da00744100050980e241c0c00501c04003604034000503070810007074002a0900404e0b02c080c0d80c55400701c0803d1082102d03070b10a60b251240d071103008010916007a1848142440b43d0b5140d1250010003002150070003504100e05c801a0a48401001ca076007007036200c1800038030f5280300c8603416608100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 865864838 1250 865863588 865863599
    0x30c0105240607030507110f100c060e010608120d0f020f09010e030a08030712020408060702030c1b030a020409150609020a1407020916200109030f0f1d0a0902070605040309 76
    0xb4129014290f0503103403d82042d82a40b18208842c080352807440c0c10413120454140302d5692219400c2a55034651078401c040c0d0b4203070400e0308c200d030100922014168074050050040c4040007602042208d40300381a1585d4554005680c03000e80b00a0808070100c0b8008180314000c10b8180025001b004401c0c0d0b80c3c128601401010150f6642c401d242c06030842c40104049101c0303d2141e60041d1500e09a0100540703070944c1d901005241540481d19180142c20200300610300c130500340079400da6280c610300320224106004000a88035001c51600038030440d540d4001c00208494003548160440000c0d00800110307030b0700c807003135806584191074441c0010300e0414040302d000794078420340300c42640180200c0c10300e9551001000e551410385502005101075122100c20014078a40d840c030080c40580f0000c01c10b48075070301d00a80500010000d540611020700d988c610320740ea1100d001c2c0303801400d0030840c48103e0260b001103a03a041158100650302c2d80005855403d109a42d0040750250384203603541b4240c1035552 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 865866088 1250 865864838 865864849
    0x170d0203130b070810061209050f070608011d0a1d0a230d020307110f0d060b09010b0319090212070b0304140c01141e0408010c0f030e0a060509030c010524 68
    0x11545c1200c0b2000d480d0080c00a90310404802000700c0f2000030006409241d0b0711903a10345641c025100e0300d2540034810a10485034854502c90041c4422240850913800c50b9031038080d0703250020242e0f040240c2e10041510010344490715030384510107000540750030311444c2c18044502050803041103201c0744911070520b96104000746141000655501940c100809982c1c5e6245240170340d018a9403001182c1d15043c0c25654910007803165500c100800115910444144800814144c0c800305815500b44204484072042414600800a248000103155407683c80003c00c0030b031001040910714800c0050209420300c1040c0158022400744e540703000020382c013210303455651410400c0d25000460780c0046108003140c01c405000018120054040c007020000b41c9401c031070700a03600c280c2c0c1c569101d480c5415440c1d0020503503681417101d890305000d01000c0c0d29030142d0314103209000604807a900c80008807074040a10545d03040340d80c40c500920003424012008100905c05a0b0400380c1c90001d0055011140f408 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 865867338 1250 865866088 865866091
    0xc0414060d02090408190c030e010503010605090d0f0524180d0f23040302040506040506091302041b030e160e0411040f1d0d0912170d0203130b0708 65
    0x18050008586907a00f80250302801410403030700c2180a10090034008010011034104100e82d43c2c0d079213a494002d090007844545a251900c2c1400000c000502003140d1000403902c85010640c1c01c05000031503450b280441001c24000071b00b00d4001e030322100f0a2141a000429080c401080c14020651164030000309500184424984540e0110b00da04a04500840031540071806500b4180e90080f5281d04249a00c1c540480d400e60010001600b4021032606114054012009580c00c00103480e241c1c0c0491000380010701001d82e1b4000e510b6000c4215a01c6030054103041403c5514030010f80c2c44080068080c002003040101540280c0f100480e00761468007901040f2140c24031480e510340c480b915075003840182d031151507410035103580b40c00c010b880d001d0140e14030ba05c01c4090000358030100b90000360b04018a2490b0142008400101040f2621100c2030301e040e0260804400300c00002c04140e41c1e80fa40c0f0400361189440c034004000c0107120008107000700a01750081010500540e9207510071104200c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 865868588 1250 865867338 865867351
    0x31e020301081b180705040504050a020309060103060f020d180507060c030f03021e03040b010f0f080309040203130c09140a02070218090709141609060807080a06030b0106020c0414 79
    0xc90700d030b02440e180c01080880800d82c09042c0d1502d03903184d4200d94a242c00c0031140754020030400141009241002d100c1c15605c81c0c1180030460079401d10103035440c0c841c0350620015244640300d540702c0841ca09580c2c1243d0904000a20402c206a00048000c2c00c2090442d001d983c40d0094580014010b40503c1b200c0d001180d1555401c2020003025109900a4210744450070802d040c400303c3c050403650300f070000c60003540900481d601941c581089460b10140e20381210710b035080c01e80720802802c480002130740d00030b200480380584c5a41d22581d04102203851031601030610088200001000c4503250b2181c000c6441300100300a0b242d54075201c000991140210094100c6503104000d14010007201d2816000b1840b581a500780740d590342d171441c1c25154a6490f40035003440c044140f044541c1c1d40c0c415010304100a04003040114505840a80315440042286060000010008110980961021000d154440c0c401d46072541c403890000d55601840341064019481c00306200b1603194004a01c41c40307000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 865869838 1250 865868588 865868593
    0x60e010f05190c060b031212091c0c0203011b0c080c0f0322140d020d050f1b0405090c0a0b0d02040504020a050d0b0d1104020702010c0b0115180308040905061f031e02030108 76
    0x3103c82c602350f078076400d000b001203001b8015050b094074159103102050a140400d80e0b1245411000c5004260850360028100f149404907035443c0840e85822035004041309402803070203601c0d24021012603040524014a41150b4003000030743c5000d99800690901420400c2c02c1010359594542d80b03058642c4100c2209a5804001d1401810052810350341910940744240140c0301c2c0110320748402c61501c501d512f040040311085400340601c4d81041d03c1a40c0e480310a030303002082c90361010004144841100c1c040c1d02c421540c0001c4500c410300e4141c044030000d01c00a00119590301f45a000203002c0c2c0c0000c03c040540508003214400280b0309140f22040b6a5040320503405000c0d050000c0200030352000310103d040c89109207061010440103141a17000b4481e01d0003510151581100060030624216000c407299140300701c0a01c00700361104192001d4502c2103c001800d40c80b4075000a441d14006c4103104d598805c2540d182c100240c1c19089404240032188401c400c0d442402c0741041680801d000f4104640d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 865871088 1250 865869838 865869847
    0x50607201216051c05190309080313030c0c0f06110105150105130509040b060405010e0405030702091506071b330314071106070306060e010f05190c060b0312 69
    0x2a40d402c42c030401c031244540d0850350202001007200e060700c440c0b519a440401c1000c15a20401e08900c0078056108036103190411013101d1698400c2d8450001030450203401a4a62005007010b009207401000190080b8441000960340c1090520180e11401500001150760141c0755240c841402031600a1004089041d0880c1962004440f84e810240c81409005005100014191240e0b50400e0017a80994120030b981e01d00356060109590703040e4024800582c044040002041c0c000c0240d407001ea0381164466401c1d00e443e4040e51140641c1c1080c40e61001c0d0000c2d0309010001e0300060304220803180c1c04525400c950311207880d0b002070a61080008540c003125260072841010368003180c1004054200020031401c581040c0032079042c02c517aa58007080c113a005400d04404200015640030301c2038030b010f00c0300c2410042c00400c00c039980300c40e207818401300440c041545070240064464841c0102e01d800d00403640b458008007210505201940d040340740213590b601030704000c6118048140321032000c5140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 865872338 1250 865871088 865871107
    0x190308030405010614240f04030609060c081b090a03150c020d020304061d031009141015030201050309100e070e1324140c0909100501120c0c0506072012 67
    0x1140004ca604212041001c00c824200220103400270b1402840000b4278400a0300e4000219001072581c40705204e481c3c000c119003588241d4840041240342000c05484084240c040f95101c00f580d04002e120b1820300c440703040311070a664806e40780b01e00294229800101c4081c01646c40e84600d0180c18001410b0308d4418002607101a2031801c0480e02804840245c81c880111a0480d444d0400844040305480703001c4001d024100240e41251603814410042e5100000c2201c0c0d0b407000900c0000e05000300400001c901c488240070b1340303900141007031081c041414845080c41d00c440d6540243c85400c0000c20100e21148071004c1d2901c1031342d6004008501810409004c4001e44607500240c2203d140c1b20344020003003495580c07026020341011160300d03890300c14100402c060120000c103141d801c070154440400440e81e01000306d58044044550020380c042001d41c08940400310f0350006021482070300d0621240c290301003005640b2001101e0b070200403c1e200007100381c030b40c89407008120a210741400613105 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 865873588 1250 865872338 865872379
    0xb090106051909180e1e0c040509250503150f040f02030a1a180a030807080601050d020f12060d0f0305090a090e0610120b15190308030405010614 64
    0x240b000b49418509030413039a840441e8400c0c1c0c5807200d0007070496141c1c040019203901c100190440c0e420160000f25414500007421551022044525489551a0784c045156034a00b40401400040f0b8000310307220603010400c03080c1c504640707489020300a11600403c510010210082c840c002c0d00d0500d0142c0c85601e80d03446103200194119402c5c2d900d801040c0d4441c0000e0001b183d00301504c035a040c0c40164501e8410750203100c9000f050928642030f00211584800285d01c0300c0800e80c882900d0138440c81e16116040100c5140c0142c02800091a10000c1c00d1441070580001400c1c184055580c4008039594172000e00255255000c8020286952048000c0001f030250019000c003030360140a10b11156a1403140c01c06450301c003100b4000c41e4100900f4401d940350aa01480c000d00480391560980d44045c0d681d56885c05401440b12440740004a91915503030356100c240031551900d54420b03171a860300c9003014206a48159000c588940ca0904005070091004401350034003100107110728440c000d41206100c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 865874838 1250 865873588 865873627
    0x70804052103030a0c0233070e0d05030c061e04080a03090b0103061d011a04021b0f0721021c0204090c0f06140f040b0c070503071205010b09010605 65
    0x110206150000c01d40788a400c0003e50301c5402c40c1400440c18034403402d0041d08040b0341e51075202d0402e4600d0300724800d0350078215180d01c60250051300340080d9038641c03008070707510320340015016400035400742c4036401e205000028200003680480ac2d41c507540c8800c5241c4241c800b082c09154070344403017080001c010920341d4020380684140d90030b010510340996a2402d6181c5800d80003120625554080114a038080c04254505494080b00800800044401c80315094091100083c8207a40005000044614180b0070510050321001100c2038611201d0150340c64000500034194694000380c10a842c81e03000e92802d050554018018402d80303410445c8601064022280a9801503103603984000000c4901d101071005018485072049800d0901078003c0c0010b84000e48003411060501800c2026004401200c0c21502d048121030b43e03c020001c2034506000182d40100c0e8903008610000070036010348415000c14900c070720001c000010080e402c00514481c28094640000d0050000c80a28a003d44100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 865876088 1250 865874838 865874869
    0x80c01020708031003110d230703061103072c0402070807050f010605010e040e0705190b0c012018041814010b240703120605032b0507080405 62
    0x1500d0214181c0328465983d00a80310301c1c3c03501c03600c1501001071040404040001800450349100050106d450f54202d2542000305a901c001000f40311800d500000c2054000856100740c051004880b81007040059401c02c440740c1020038002e0398000c4050401160300a851944400101100d010280910000b500f11304801c83c0c1e5850304100040c0130950401c001c407120180b4a00105204c0e05041c00104003440c103181c000e0169051801c4d2410640340441c01c00103465003038409624050381080c41130b0070101554056007200c1000202e0010074001900074007401c06129890000d07842c0041e045005034801c170250150b40b21005142c0f815140740c6030b013045104210302c00100707680c0342198881d510f29003c0c030010095540e54415003880b0a0502c0d410382c0710004241a414400c0f00b40424070558503100b0500020200030310003920b400c01c1c1c1c1d1150b00000140c4400741c125118412028400326590b21000d204011102451120481e201e05c103004448003540d0000c00c0c1824a89000140201e503940754800e0b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 865877338 1250 865876088 865876091
    0x101e0b180109091d010b120c0405060d0f030207060e090f06010305040c0902210c03010b04300b04061d030f0d0e160e0106080601050715150602010e070b16080c01 71
    0xa0001000d000d00c49500b130091003030285000d5100d000c81d0845046459080c092920f007010429980008148000301030340a480114075a542c40001550b0411210001488140e41c034440c5014981c1c00519081590215180c040840040108100c14103004580c0440780c2d185040004099512079042250050b00c01d0300c41d0f010b026191088442a03800400c2c0400800480208200700551310034541504040000c0c107039465541800402c5130103110300e0150307140c62020103e40d00b118100010b46542c06001da88500c41c41c103001850039040300394064400b82d0b100c41c1011200d26403420200c0c03514581c0c4d071004000f03501c0d0058111030004240c03c000c4804610b942d5500c0b40101c0070308180008010320b80c090002d00e1565050050282c214078068000344d007002507a20400c845a45c0006c05ca483d5980c1266031035641e40e512252000241511040e1035900c0503181c40001001c40d015001030a030804150251803100b921405400141e00800c200c4c18001e200a00041001c83d5040005003182401d1400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 865878588 1250 865877338 865877357
    0x2090a0b010c0b0712052202060703050409050c0c06092b020106030c060c0210020706020304030809060d0f1b17180715090f06031a060a030b0405101e0b1801 69
    0x220400041d00c02c075500c5000c1000b08180428154040c4942580018440b50180035004088000007c00e1540903009000f001d00040c0c038000e05008000340d50040c41420020b00903032401468040c1940c00038030b0750000741d100742e2000c20b07040c171008a401c10f241d0b407c880c209181d100c240304001e6007004a0404420540d581e071b02c03000c004034648416800c040c100a40300d8140d401c10502c1880102404540400c0440d08011014000f40d640803040760b0440390046005d070344800210000410511958001d042c10602c2c20544514a400f41c1c3c02107940d82d404c0409502c9004000c0e6030541d00300c0b103e02c2c05540c0c0034400c14006083e1845600c0b860b5002d8841404440845451b511070300c25401101c2622404101e14007420000220030001080280403146400d000080301d2008000c810714000c48400e2080b140802c030289424030a0b407013460b8140b4000d00902044c2000120210400300d28082c00c00c0203d214049240003140384581e040c01c1321903010001303203803a03036070500d8030b03404001301d003c00e81001580070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 865879838 1250 865878588 865878593
    0xc2607030b0d0b1b03070806061e03042a180518070b070b011a0712050913051b040501020d350928021504031a040c050d02090a0b010c 59
    0x50504860030f100760400c2c4024140034003841c181031854012020350b0801003040160f0554401c1e20542c01103425202207440d030002d1a02c0c0003e6010750314480007100b0340072007040140302c6241520034000300070070600100621080c9104c401070b8400e02900300441502c2029102c2241c0a520080d0320882040701c10041a20b590310040c1000300642c0321907042c0c10081070600a100c0c60100443c010038018010480a00501442803828050f112011b4444500307850552a002d015008030307280401c0040900c100c0040c0d01c03560b80c0007000280c40301216044003107400349c1e44440d0541203400b9030740e05070020325140e140d5080c1150705000781285540752840b0421900c4460324252903000078801d402090010390300d0700c00e5056151002c01c4540400e802e8503400210380038081c0488078004a83c0556440d084454280c40d400384610543e80000e2414042400d0340340020b00041a25018901c201003100d101e5603a0303410040c2078445400d0196001c0881008070b5120b50055010401420040c1004401c000c0303141c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 865881088 1250 865879838 865879849
    0x7080615090607060e032b02091e03121b07080105010308041a04080d05070201031404021309030e0907030b010906030b090c07212303090a1101090f0f06030c2607030b 73
    0x104447da020000c0408070f84940d02c452003d08000a1400300b1410a05507a0015002c00c46404080714000703085100c004454900344910510028140455581c8000042590524159907906800a80119440440c0c20001030103818122900f12070a40d08003818114418824041040600d0f000c0b07e007000f001030030103030034018080c482c03c0c203817105610741c000d500000d010744420815103111a05400100001642d5079000e42038000821342d800070b43d10945140680d10701400341d4545a01114000070020900c1e03054100048559080c0e0781c09808654130324082e130940e80811b400d554045201400507041c40c0100002e001081d0143e4800da405049200c2e1b00d031501d18540c0e21680011300d41419050740c40700c03241c03100c0c1c40900c81449250311710700d080580646c9641020310014140501e42034044100da11034140380d400f03480b1040f9000382c40390f030700c41906485030568811880400c2c00c140c008070000e800784015032024035000350340540d002090300e544048000c0052004042c155514220305154988 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 865882338 1250 865881088 865881097
    0x90e01030609020f10090314010902030106080f1509060112030909090c0e01060207032004060b0409020c0c060301120f260405130902100c23030307080615090607060e03 74
    0x80200041c811040d0044c070a00c060080f1015015084c0350050072407180d444403010048a0700030140304084d03c0c80c0d90949026140c50507000e0b6056003040da01244500340031400c1801e09400c04119a0f040b61707050402415003504580b6054550401801041415448499240324500c00c1c900704990342d8480d001301003105c41e5060301b0703915042c02d030b0001d01c42a41c109280c140034103d9400203003041403640d660064445401d15120090b100450000f04042e161034000f000030f0140e488440b600d55441c0d012150094011407990003203841000c00d0446141032440880707060f111b01d10701855031300249803203000d1600b6525a00303d902c0460441c82144050041d007006440451540182d0b580303519060070410300400343c0251084452501280c140140d880c40352040d0b88190300d0500d1072805220741803c15110185030403003011425100440b03404c82c1404001184a20301d20303140c1c030358161a8201400004071884d9100e00c180c13081008051494030f04400a0282113208a00100304c03504000b0031107045401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 865883588 1250 865882338 865882343
    0xd080f04151a03070504020c071202061b160509070c060c2016050402040501230f0d0561021c080f131a0f100609150807090e0103 57
    0x142d16050109850103100880081100300c0d000d600b890040144c2a40301c03c2d061041c101164128a2102d0031034035031703400390f6406802800104500c5501d05000f03a8a80f030030306161a016020140c000b02e450f1500740e41c900d024402c41d607241c50b2604a660f039224020315030341c41c3d00e0041c443c50301c03400341103152a0825000b01c02080c2c4003510408854458401400c005030300480e100e1401440b003070146907484048811101c56a05641e04142801424060f65205080264080600c0085c032402000c103142c0056000d516407800c420b983c8413040510000d10b01084404101c000001e071500460a003e42c2440e900c490180c40c221140a172452800b0b88069850007601d40140e00040f0215802c21440c14584910404a0078080c4851030204d10903074192400800c4841031078102044041400842044261010800110390794075050444064541040841d10395071002e00c2c0d5100807921500c14042242141d8001c000101202c0a5030415031b990320b4000c0880c800c1040d04180011041452100075000b1030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 865884838 1250 865883588 865883621
    0xb041a040f02040b2d031e010b03040210051e0c07080105061909050c040e190507110312090a022e0306050102030d050a2d0b030d080f0415 61
    0x4a610180400e9416660010340a0762062008200e200711355801c65005449000c0c00c000842c00769034511800c0380c1c41e442e00a00241d404000c00c107410b000607440f400098a541c100d040c0580c1e03035106004c8a423200f01c0303000f500101d10890200505004070003402c40e41c0055100c0d901030b0b60f90f480540113150052031b100da0859008210400c8160800c0c4541c40c0c0005081d02c0d044511a80e20b0641900c400052050001a90740c890008000040780010b86001c1c00340c4011009180c2801441c1008000840d100119128901030200c2c40c00c0b070041000003080300606020f542401269034074084d03013010040100d030041c050701c8584401039451701d1030392130b035142c4118164103c1000410040c001e0b05401004e40c060500c2c182c41402560703000010748100030b405040100729907507645c1c07040002d885801c2030605000c40c1c4900c1e841440384c05038604501c0003c020f100f08421342c04ac2d004c065441c800542c840001c0340042d404101e40c403d9a11096078441d004032209200040100e988108640e5440d140b8100c0e013 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 865886088 1250 865884838 865884881
    0x41b080606040b21060a08070303050d060902040303051b0c18060d14030304050106050f0a090c09032126040b07030908030f070215010f05040b010e030106090506150a0e040f0b04 78
    0x400107141c1c8645c1090050b18440a2a82001c2072150303510b0b410701014045c040c0220741d0b62007081107908002c000d803440760010b548980e42d0345805411500000d0351600041c2641c0c180001c0060002049505c03d00c0c02040b810300b001a145030601e01850103400103400c00d0074204554041039200741c00481d20603d100046940f46810b003002802c66402da040180702d000f08520710b03815961500e8500d01540c40c4040009078190b00ca4200b44c51a04c01d0b60701c014000460540d1142c40c3c00c0030325030840c9201d045c42d2030350505100c162408440c1100320182c44c102c42d40e00200400c1c0411003058400703a0022580c10009801365164440c1c0c2c1003504111920342c060700100c000c00c1f0040da8148820820880c0151905455506141141c0741c82c01450044901641e0303945180c0f041a07101c1c1035034402c401405402000206d86606000c1702070281101c0903402801c140c0c20f9221501002c40071501c00e1000d41d42d4101c01d0300505801c02000c4c20728a203500e440603486814100e070560343d51041604e0b40b00c0700b16510860 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 865887338 1250 865886088 865886137
    0x2e05030607180e0402012a05101a010504031205030c0f0d060f050108040b0f06030c0a18180807020418201215041403120c0414041b080606040b 63
    0x1c0c030a441e04100c049035a840113102c0183d8100c001c4102e03040d150075982c81c001400f141c10b070a01048042006e003080c0700f1051148401c0702c196000710905035407000782542e103403155001500c10703110302c3c4070090000041c0d00007900c00320320400245801032440180c16180408103604205190040305525125503540c00c1c00304000c1c025a0103c5000b0b140a00740411030b854240c4900300810b030020300002c5410500000101c15640500a2050750030000f00140c2985032600e5041d600700c040043c1030003000386405450106501e8031101e800c002d0f03600090702440c01000b40e0031700c0080d103480c00b10084e4138450003003c0000111040d9032102d404a5034000e03009103a66031810411000c181050200c800c0d0026866a5000b1092921407644607400005108440301c02c401510f19500c941483c851503e2841c0042c050103001600081c4102e848805480d0689420842013204894580000120501071041640702440c0580c0d80198080001410a42056600c2651403201e501032038403000e840b0000c01d0003408 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 865888588 1250 865887338 865887377
    0x8031305040c1b0804120819050f2d070f0c0b03010f050d022701030c0f06090519150f0914060703083102010f02062e05030607 56
    0xc0c0340856003842112041c10340a00801c4203448440349100d180fa96507810300c81a20100c44c01803044001d0842c1e402c1041c140340d0341980008580c900d10580700803e1052452007002910403181050704c1640c5072002c40e00d40d480508620b08404600e07056115030610701089210090300c140c3e4081c60f402400001d140c81e085d040c0e81101d810450684d102880103110b00c1040c499464243c0d103081e40c0c0f01415814500000385800c0c00d031035801d400d044040414003211120090161704882c402d41450b055180c840d21270b1703011912039001e0400002d4070003c0401c0300b80740560004044400c030001c000012a218a08074255501904a81010460107040303000c0c42507010030b000c0300074200490a101c01243c41000580c2134420b94601400304402000418052504061f604601d02d0200c001509400c83c0006410f0450303d42140683c00f2400d1181640c48803400851030358030844001d02400e2240040345000301d0030103580908a031041100c1500403035241c808000450003031400d91038004214445495241 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 865889838 1250 865888588 865888627
    0x10e0702060103440c1c02030d1e090507060216050603060108061f0e04110315061e0c0c0406242a110f03010e060112110306010803 58
    0x108550140d07004101041141d200e0f80340240c3c560131101c0e541015543c40d984820040941c08110802c40210035010040000003800700c442002c003503800703104501d5880d644401e6040b01c100b01580080112034101c001355440200e00000784442e19040548e02784440d000c842a008088419501c012428803489030100010320324554400031100e20981800f001c540d641c00701401c00fa051040038008500d850361214068900e02c1c1590102421510070584000e20107028411031500452034003085003055440403044910480c40a10426200c20301d4105100003503201c2000004050391810090004d1329041c03008002000c4050000d2032096144420001210300030341c45a6103440010740180f41e00803400c0c012034091001e41c01c01c009001011001050b01405d180c07402080c0c00d041e02c1c5a20308014645040c0c1300181010358040201c110803105042c220f82c80491401041d03401140100407034106021040b1103140304114031038114940300003082c0784c03520a0f0045802c0b6040452900d601c214080c0d01e44 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 865891088 1250 865889838 865889851
    0xb13061e090b092b021c1809111b0f071d06270903040504091b08030c1f020903011d010f0506060405130b1c02030c0402070b220c0b03010e 61
    0x2001c040e0151814056480ca04002c0d003031071000704401002d00c860081c088414455400c10188042840c00c1b88000d2941c642c0305140803481d52843c1020418410300e2090b400004d111400701031500c4800c20b05041a020844181c034501e100340884072540708401d220400003040f450900e44c9184283c0b07101805607540041c0101c0c081c0000b0241c0904d12084800700001c0084500011f0803143c40d0a0841030552003141c00054210b41004102c20801c55028010a5424200648201e00648602001707449100311074008040380d1001d0036000048403107808807202581c0c1500018a0315180c200440d003920988584134081d94403034081610203180a0007807640740d402120b4100040e1400c0800681c2c24040c40c00f07454058000345c078100d00101c50b6584010030365080100f4800066001d00483e0a40c0203070f03d00308078080d003e142c03070b050354a06050013a60605640701d5010a89651100c154150000b00c107103001d20709581480d1100301003030100c14100094108206600d90b258101100d6885184000c0d015 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 865892338 1250 865891088 865891093
    0x30c041e0f11041509050d0b0115030603030207090f02090d0f050f070e0c0309010f060902130f0f0303030b1f0c11330d05130506090303040b13061e090b09 68
    0x100705040c00b2010031101540c07031144141d4226040410102d54a01d880c0c0c100302d41008924104809100c048d04602d812989003060000034a03d420304124142d03000e40c80000c0146e801642d042c8120b480e00e8002d03181d01602160014100030480000801d506a000d100303413510700c0b090946000b8000248582c010003024000145002e40c075205803074a42e4140104807465600c800720104a18540a4000c1e0884054050050154585900f0b207240294440e4148400c1c41c098400c3c00192a41c0980030304089402d0103054074400340c55501d0070340c00340070309403203507544265415a004048401c0846080582c03500c0d940742c03005411203192031004403510386821840b4444046051585540b4061240034000d0405003a031890600d50081d440d05014942100e080582800c081210607101e0762103c00849024000310350709903c4400c100c640300e100c181c0b005800c0141d008000b5070070a9401c17106c00e4125103d0440054410401190400c480507140443d1403001d8a9582c81010700c6031682000e5000385030780c800f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 865893588 1250 865892338 865892351
    0x1b080f0a0917040524070303020a1e02070e0a0e070b030901021306020a02040f0b0609041e111317070b0c0c0d0b06030d030b130b030703080a050c15040f11030c041e0f 73
    0x1320385c030303405960700040401da00003e9803040d003489841d02c0f401000c00d600c43d4000b24a030b9070202945171625400b80c05513141c0002d001481001a9001e00341c103182003403001d450102c1c1401030b12007850780b00500e50041c41d90201b1000008401d18103030180108565800390044110030b204200665600144510245040c5029600fa5583d00400c13500021030444002640f03c0c502c030075940780c8058641000415074074201810394089001d0004004011040d00c0e0a49101d44075074480c03050203411401c24105912500c002d00040a00348010040d1401000841c8d200403007003800130310710501c8180704442804080302408010f0a0810518420f00301d5402d05200406402001c18070600103002c80315084e035240c900003080780d14240103000203507030450151682c440510388003a2082d803141f02c0101a0784148908180c940b8108602d281c00b86920480100c03051006440c2c1089902c1c2c0d000e0015070500590021180c10b55442c070903000040d2600e598490400c044102e654210350150750380c54005400c195 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 865894838 1250 865893588 865893649
    0x1050307140d0311011a040b092a04030b070c420b030105010e1008070302010c0201030203220c060f020a0c031e1a0a1b080f0a09170405 60
    0xa0038040201c03050300c0350802c1034603070304049500702ca019081001951808480c2201c010041b020044070a400340d90900c51242004144080414206c5403410b0441c2501c43c810469a41d0300c1c050100060051074460805849407200d0040000640e40340c000710b40000511000c00c411400c100c0c00108111403202c801c400c446481c11035902600c403001b040f410700d140a40c1c04200702070f844407008a0000d0000c100d691307164103141007071903800d4590f2450090030b0b06001812030f000003400005c0c0d1360b041c1d442c480c100b800c03030b401034020b9000540340310591380c403512214038a040c103c802601e41a00980c4103450305890590081c1c480c40b000d81a000454100e44020808140c0c0e034010a0201ca9216800d0800004c6004000e040c20840c00c00c020040940320300590b0410310305680b803d0040300001c00821854403188800030f0180e05040c400008070728020005551021008400c40c2d024629400200c4c00603101c0d07980d144421201d1814903842e04002c0f40c140074604040d8000502440942503920400a003003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 865896088 1250 865894838 865894859
    0x62307030207230a20011407030e040c0516030c031404210f08030c12010f06020c01080604060506070f11090103053412030305060102010b180405032206030501050307 73
    0x20340c818210843d1021444101202084041c1c4042e03080810916001c0402c0124507802e40390f5061640001c0e000010307181040f0241c030440f5a000c2d415180c2e29906104042400b000d4804100f050051000070700a000003525074011014040d840f035034990060302800e150203480035900c91100f42c3c000d8428481440001c07c5039207016000c890300d0241c0600d00c040b501e0000d410f003040c1b45008081081c04014000d88a4502d0040d014a0418140c500c0c1c0b0360780c0311944000540414410ba1005034030a1841e00322a5004071031541d0803940181000c2074558803100421a1079200820844004513080001401c1c8441100f8103880b40c8411100100c40354595110203644949841000880c240c0d103040400510038111102c404c807030804c3d9451245c0980d01c5001c4200d0504124041d0b01090030040041d000d903106200768580d800c03006000c00d00307030303002c0740854444040300800458180c40304111340660b42e5203245203c40510b00b1100326400180c10048000d080e500c06901003400fa80c0301d541d080c0920b161a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 865897338 1250 865896088 865896113
    0xa120c0903020d15020a050d0b180f060d060c110c030f2505091005010201151a0c15090106080f07060206010b180a06091406090a030b070c062307030207 67
    0x45075900038001060030443c1462100c03410181c4e9003440000c81410b0030750401c01402d865000d0020030803501d2440000c0c05156150701c000c00c0c000a10f0349000400031076052203c1a00842c028280c8400a003048d6070700f10444414103a582c021441c140300e0041280f1007040600c0c040c08013580038205000c00802c401d542d40302000680145903803031030b00102400e0821450007004103402040090982803480c41e0b804005403a004450055003000d2030740d01e4100d03810004030226445000000d462107a902c80065072500b1840041c4294040d8007500d010300f2442c41e0081e80251841703000098200d00c1c150009140a1501c01000c2c21901312850401800d6008104641110031501e8590395851403d004c3d585040c841e010040c0d48110144004100e075a4021902c2c82650f401031000c2d80d540c0414420042c00c2c2c015030612560240414009100040741400d146801410074105501d00003600e541e0182034908800c0000c00417072010342d4030180c1604070a400d540015084c1811442d00d03080e900d804900010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 865898588 1250 865897338 865897343
    0xf0c07080610090e0d030b011b0f0b0703052a1606020d1b05071b03020319050c030a08090d060b211507020c09070905130203090c190e04020f090a020a120c0903 70
    0x21f8820384020342d6401031002010f000100000a000d10b4441c4c41c0c809805448410146e0740b032580d040015014a0080c4a0103004142c1e0056410142207102000301c00200340c405500744000b800d001c0e202514200401c040d0b42c0c1c1b4414080540c0396070030042d0401c100d4144540342901c02055160703140c80780350070a040326140c94100d184120540c02021051402c400a54002500749c0715a2110030450480010340034019803080081e90150fa031410205a502d0034154000b03002c0b21030030440e913039041c50b100700203c01d0f840c490b420120f03992458400145100324803c1d101d0f000c6000040221100c6801440290100b10300110942030318101058025550010310072031a01030803d140c00b140c0c3c0d00f0300651450000313040051032180c502c0c0090100001079003056550125038800c002c520780c0342d460402100302c100c030191090505040d00e01100da1240140150042c3d81122046600b00200e860350804284a010070050160340c40d080c480d00101005041c1e0400c40c2e10351301d81810b005c2d14941c0711040c5400c40385c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 865899838 1250 865898588 865898591
    0xe0115150e1e03010b10020f06090615090a0e0708031809070903020904061d0a23030307080c090d030e130e0c060f090d11090106031b03020f0c07080610090e0d03 71
    0x2e4001e40401d00402044101c02c0d0700c22950f80b5090361140c2d000400350607141903c020b48417a41ca03840501903072010140e400e461085030040c520001c40c00c1c1440c10680c0b100382c101020a0219900b83c4041c1007400d00c0e00404516040012108404002841416200e82c2c05898006261800b04d1009112040380d000007481601e10101190521916401060b9065414407040b01c1e190781d090032482c0d80d40003d54080b45d440074540011111034105a1945140d01405005107145031f9855108441000004021061a440501030510b003030325410a040542486620380041127007a0804000440048003081203c00f0b08000203100c504a0100348109206015030b085520303800d01c0315440c0b03010300070380d0f1440c1d42201c10480c42500344070071071070740e1a50480c00b40c84c10040c0f40d80314001107003520034111003030002c94600d10301e8494452081e4010301030341601d600709509181e80d642c0114200703991548180495848002030104141006c1c14001c0144410740007000180340103200c080e1036540c078288000525 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 865901088 1250 865899838 865899889
    0x20706020613111905191508041704030b010f0e040317090a060516200606010e0a1205010c02070803120406020a050c150f1302030c0d02040e0115150e 66
    0x455190052003a04400400701000405062414400728413984a40f41c45000d100701c43c9113210480c03450700400d44180300076010b05290021070a44100001900031543c051542c50004441c0d800030700079101551042d160f990300381d41742c098440c1410110703411000c55602c6400c10b11000940190b4040c1400c0c0c0d040142a10994800d44039070704102940c0801b500035400c0c0420414080d540214500301c6a1031502c603661404400500d105980314202501c0d03820b980030314003048441d8000c00101540300390060062803810784a040000052071441c1e011542c40e0b44640400390401d40510006026101400045013001c0180c0911304c0711480241c0090483e69000071035150b4584284101e50f13100740980f040310b5006010084031070182c0e84c03c07210070361801c59010204071004c03049100a11201d800800130801a03104108001e20020880002c030b92250fa00d10340300ca0b06020a01520318901c0c948071038100264600b540e04000302e508101074001704402d6460090682d80d50000c00c001c3c1000002d4a80c216 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 865902338 1250 865901088 865901093
    0x1b0f0c110307090905070b030408180f1f0201200703050f19110c0603060d0b060d020a350d0f0909020310031110020c0f1c0b040c06020706020613 64
    0x909121a615500350080040c0460300c03007001e07080b0000045c81030040341c148907034555106041e07000035179000740f200c10200100c500003c0c440250140c90100201034500d502c2c4004006000302d14640507201c1702d102124881e80319140c0a00c10138032607411141d00a03500e05a52006120588101c52004040c0075002c42c8034401d203100441501d03034100d14818800308840d004007010f0032a4071161409a0148502d400c2d8040346d08158040d2402264041c0060007041c0c5a55541080844014002600030348869210001350b90346c104848000e21941b042100c076030450f49284420004000301400c9030005020303205040031b0000802c1c0d0b800000a10302040301c94038840044030302b59a9603000742071250022060041e1030303a100e0402000c61b4816030b8451800c1040e9403e00842803900c0e0b5100300560484c11f00007401c0d04204403102d16281004260100001851a541c44600d2000c07071f06136002481f43c0108420000812030364009041c2d1400100074451810400a6940200410310024400781001e420704 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 865903588 1250 865902338 865902353
    0x603031416050a0503071203060506092205010315060e0c040608070c05070617010510020606102006011505040e0106050717030f0901060f060e060f1e0d1b0f0c 70
    0x11040c1c1c49400c1c3d4404a1980c20300701c0d41d07500482c2082d182c56501d18a404903460180c8504402c480300075000c01d060007520030410001d2015500da441c0c23842030712105610155402e01c00c1038043c1d407080d0403003c2c420300c00c80c281d0300488003150001100c0104240500000300041020ba0f400c9590a10b0070348460364404101320341020000307600a14034402c0d600c1c08035686811205403001134130082a020503980eaa6002c00200c030003403880100c090f8000d000800e11508114060b80d82001c400e0914469510800b2541c691400051309821080d401090042c40089400c0a01660013502071404030705140c01c000d60300388908c5e010b12032001030100015052007001481c00e0600680c0c03448000140d01d91614121503a0300201c111642e0b84154030700300300403c2e0070f003590405d6001c2d42c42d03d44e600b0606070300382d000784821075218100200348080203201c090f4603500c00894a500207064990025180c40f0385410b44002c0d11101d00703c070038408040b00c444181480e404584419481c07005e203403406080c005401c11a6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 865904838 1250 865903588 865903627
    0x1905210d091a13021e0103020405031903030b0f0d030e1c2f130c02010b0a060c03090608100902090a1505120f010e041509020405091e011a1018030308180106030314 72
    0x1500750003046202e0034140181c00f330650305503000f0f440038441421560108080110071071099030744906600303808404a846080d604e11a8000076221180c660214429440b2400e9604000c4518264843c1c8004212017083d02c500700c0d5505400c05800040c0700400081c881080c07030b11010301c1c145d9484080c203115138070035044108868000b404540e102c40e01e4450081c42071094400c190042407501c40f0004200e0f10a0710014451140e074403003140c0340c0d4207001d454030280d8080e406080c0d20094121002c101514175080749202c04044c0d4030380320340e0303070b0888802c0c0310b1501c20081804858188503401003200c503000a0000f903001e94071600c081900000b00500000a100b2018069046450300003041161100054020749407207502d000009241d512914071403d80e40700c80784507041e030140340000041c1420104600301440c41d40e420640a81c41c030410034084500c1c1c150b40f064001540910a02102e012009169003407621000c0091000c0d078150380780504040d0894000c0656800d0009503905015485614503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 865906088 1250 865904838 865904849
    0xf01090e030a1e180b2d0906030a060e0a0c031a0102060a1517012c190807051b03010e07120f02120607050d0f20090607080408060403021905210d091a13021e01030204 73
    0x1070ce42e5090186100300113003500e0b40f8100109150003803e84042603084001440040143d0052005a644800c03020150090205207542d28090030b82c046039006010003800c401040600000880c1b6452066200f40c1e0f0896903141c000240411440403001d46e40400d900c100e032000c140c9100f4100c0350a141c0060b00703108803c0003401134000c0d540c010000a041c090081402d0030214000d0200d1136844502c035859910300d100c0d46e41d01c10050070a100c00940140d080380001800103045a030b05d151402c40315810240121541d1001440006400d602031070248517540255607034240401020083c0e0820300c510405001c88048800c1e40400c00321920ba88883c00c55500d150300140c51525240e80d0401c0c00c0e695841540c0c00c134007502a14010703014614820140360900358120004010800990803966200e80d00a42da11581000400101000d58486e0051703442c400c0c801e46001c1018800c0100c09480c160000e45007504280405450f2409a515220001080400c14140d0118004c1140040c0d0092150740e020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 865907338 1250 865906088 865906109
    0x5063405010905010902210a120e09040302010b13022b020f0a03050a18080f0304050109020907050702041b0212090402120f01090e030a1e180b2d0906030a06 69
    0x602d0204941900700d030320120310940307002150b206803405910f40c03400313500c450b005154002804400440c0c1e000214484240c034604110342c4091041d80071071341a0030200c03010b5001d82c0d100e010461450500010070220b14000000231401d014100c5000740300d1074041052030480004100d548100c0032015411a501c0307808400603a950703003202020160282100b140c5040c1043c1c50510341c03280f0212350340392043e5429807040362103160568000d00c070754990300090f100351603543d44c4d0340144005072104460b10380210116100d80d80c45904500c10042569050380308804003410105c50307810116000180a2442860015030720380324240c44010500070700588030b034282d01703843c2003003408250070503a04224141c0e0011603081c40f00d401c120103425a81d115600c2c0860000318039100c550810405d403485040d1188003841c05c43c071812003083c408030b0075410a401c005070a03a0300140030b90028a201c5140a040901b095115600c0c0300f01100c04540c42c00703513211881c0900800000680740b9200c83e4000d20141c45035911 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 865908588 1250 865907338 865907351
    0x5040920040f090b060412080d1401060e030c1002060114010302220501170609010323010e01021c0e07090c05130311040c0315050f040f020c0303060a0506340501 71
    0x61240c003510240301d01054240ba159600280c0d04180013200e00b9241c17a047e941c0880c0c4e0441d80c404445030f2003000c40702d1021740c1c1c1d42c1c0f03600c5c071440c40200320324020401c03952040003103545a0105810810110139a0b40300e60b844800300e00f2059000b0403002e046680d0701000d101700c01004030058000c1d01c2f03000c1d020f48240c40700c403d03244000b01c8141e1100095070400c0c2c6e80e0b09014512904200b00080090b180c45034041034020040000580701c0c40043e4141c0d041100d141d01c844400c1c103c8600f91a141d16a2141517500405d0008800c102d0038006c0b42012104070b0240220510816040e484480c50701850b1046074540e5810400d807805a0f0407101c402e00317040140c90405640f41841d03100328083e411854442c50902061104941c03190103140104401d42030480c031281c0c6060200300741080c211102c00e80180d2514051480311842e88090444203a019018596030302c0e0200c10001104000c0c0c000a100e0700c0107105c1e41070b081c4001c0303039040b00358202121003080e40280c01c1c1c2e42807082c40031220010110741c03e010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 865909838 1250 865908588 865908599
    0x30706050f0709050117130303020403060923070e0a090201031b180605180120030f04080c060c061303031d010e06010609050312250b190207030504092004 68
    0x5110030b00c2031900355a100b80d202d448800440e410001031104000481c3c84402083d81c00c0103c204031038002e4860f0030f0051500f0b5499076074000ba180504400d440d4928805006044030100d0203200040c0202e180113010750302c0c01e12400308020000645207440c207554400600086901171384c0700c02d0034150032400c00c400000060400404103100700c1840100e0107409600081c01a01580c25103407030b5044680b80b42e00b0607034007500469602b0807403403000c0e0110f80d02c00802c000310607042c001007124038010700c02140d4450800c1e01c4986070000b03070036105000b520200b14500365180d0207c1e200d41c0100e009071034511503c40e42d003012805408a011440131403101544100440107055101c009908624000c0e41e090380e0b0780380000c1e24105103e204160309900038602c40310b40c50700110300400d840b0300d40c800c140d004620401c008400070290794504544e201b081c002408136040410049410203285048190301c0d00700c85a0307008005020b1417284000c1507848101a00441c9805952901880300303280d0344c26203495461 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 865911088 1250 865909838 865909861
    0x6141e03041217181507031d06010e040b100504021206030d0c0209070f12240f12110d1a220819120c0305010617060906040c0203070605 60
    0x1d8504072100851070700301440003409103442c590114820340c4200399968030800499407000c0840301d0301407280600c5440350800d00425207003034014545568000340200801255510034008041008541c0e171180b0010480c04241e44c42441c0c4c05988121100c205440d116080c024115554004a90050002c25910000b0251010051046000302d04461407420381910a80301c103c080c01010f9007200351034002951044c014039070f41010090900e8040c12035145003001c6400c42e030071400a00b0103a1800c0c80c21240040ca00365120003e416901400e4080701d180090840c1040036010004001000f400303010601d070741d203505230300c0340713068000c1c000103071042c20b001d42230610010840700e5440075a200e00b5038100041980854036491035000c0045880c08212120034542403821040500411811404842da681458052282c0e803140e00e84011525504108000c0c0409400d01002c1c4180003a080c10040035035a00c0c2102604000242d4000403505d4000004a01b1072080d80c10140c101070130a824803108842e074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 865912338 1250 865911088 865911091
    0x13020103060b070203150705070b041b0602070f140105040504050f0f07090311040209040e0d020a030914061602040209060408160501030504050304031103030403060603060f1506020706141e03 84
    0x340da00300400d58645042c9141d500039018041e40603030201e0701d066220006201e41e60341240241c18800c0c02d000b1581e480c4050304004440450f50520f40c04010710118101c000145c029001ca40050002c0d10700b85402e801d20100359128101c10507440000d0012641d0240e01158090640500300340f0075450160100d6814050036906000074910355400164441c1c41200c2c144141d951040012020b103084e403007000701a420100500341d015a4485010790441800c1104c1d0803120340a401804030403a06040280403440203134807448a06400c10303007201103135885004030380020718200c1d210f070400300050004c100203004489081d50800000900441c03910f1000482c9184012040100c0c0c00c044e44840045096078000c0c0c5008000340e0086c001440000d0b2523400b030810f0302d600a41224101a0340c3d4807160161000c030b610981d61195904803c1007940300718055404adaa8050307150b103040a24101d0003d43d129202d1144004010714580080c100811000459911382e00c417907079807a10b4640c00b488000c1250320 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 865913588 1250 865912338 865912343
    0x28061103092409030a050c0c1807031401052211040b04090f021e07030c02030d08091e0d0e060409020f030906070903020603040b0402010203070c060315090e1c1713 72
    0x404045142c0110b030021400e5104a071620042c500380034201100740c443c4c0e004000540003500940b2541c082980306c0c50344d071510f600030740d403241003160812030000740c00c90714813034100c040c00c0380312000504c0207407130301b81c10310380c90403211081007400580380740b2a10002c00e0b4220401480072400500000d00154900c0a002601d00e40740d010009400041c0c8004200c2c8210740015202d11040000000c141e40140080c18800740a81019104082c0c6580020300b441801c01d10b500103c1c51703680601041038020400c403920400032500600401800802040d519040244880100070040440200c0e81d2508415a4010402c4c0b000c10354660500d40d2010300207800481e41d4954521072800014100761003007140a04498000c2c1100b031458555844061a07410300400070707410740c84100141000100c04003c3d00e401003c2c2030350001460f0004500c7c03003150254a610200c4002c0c00d00c40c04d411401c0c3c0c00b1503008998114002c001605500c52134041d08c40307140503045840c280316030a082040051061100340c000a2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 865914838 1250 865913588 865913623
    0x3080c1e030921030603161802071502030c0403060c17060f010212030901020414032a06120a0501030506011401020c040b0a050a06020f060a0c02191104020a170601022806110309 78
    0x590040090350b0303000b44c400c0641d04131039603141e8480103006a0040001c030303020302d43c9038401600d404000e100f4dd038002d4030450400d1100141c2042401620300c5076103c000400d182c40c024819000a02d8864220b002d0300c480d1146111001c4141540c1c020000d8814401d400b140e215240d107001070a160003900907100b0610030080b09010507841d4640400c4a010000440340c406181d00c4290081d12510004800b055412000801140c20541d0842410911404465401107a2981107103081400d002041e400314800d02d503c81030300c2c000e5030380126442d125a40182c0380003461199803400036011740040d0381301c650040d50a2001060465001c0340c1d600e48090068211a56a00e0742c0c4010801c4540d601e030b6540068200143e1844407180e201c08807000c0307a02a400360180180e8000000303040760b010480c0c4070081101d0b900034a00c500590100142d001400340058100fa040005410307501b0703070041040c2e1040d21404403000c410440940c1c44030803401c0c030880180f5280d00d0040001039441d02d800c4403504450 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 865916088 1250 865914838 865914853
    0xf0b0306090c0102030415030b0904060c020c01020102090604170a06051608091c0e0a15020a050601120203121c150302011701230d0f0c0303080c1e030921030603 71
    0x1880c1c00181251007640c107038000d501d80f52500140303001d40303141004084205034035800006030075900d00c01458055402164001665104200301078904801c0d9100c3e40c1c15640180520030865030b581c010307a07084503013150101001680c0c07001c12504200c6640d0006002c20301d00b00c28080c0c4806480c08000c0d001205840710140342d11103400c03055580100002e882441a040410407100c9485202c0701102880054440e100036510b840e01e03160007071425444840141d02c460300b0780d002c1c89001c210607030043c0200903001040e200c003500880d031102d1400ca40f488041c10b00080c815031900c111690340c0b54408003181c041001c980c50300d069000742c1c01035210a034006500c0e0038a00510203080110384c0c2c12070301454100044864680030403e0031460b1009a9940007201003031050100e6203080703a105e00c152080041c200c000303040d440d024045c094040c02c0c03661003410a0100c08001014040020b604d0f0400481031a01d0343d80e82031203a4034156103c0d10240b071035103400d5002c8046004060146004140031000d44404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 865917338 1250 865916088 865916101
    0x40b0609070c0b0a091b0810060e09100c020a06060f050901091802120312010312030510030503160c090c021f09030c12140a0908012307030515040f0b0306 68
    0x182c000408080c12503911032010640300e00701035103c030703413441c0c81006160000d0700c4100c03a04212400c55404010103821901303880c403040700d1a2113242c014007241c4000d8000c2c1c0c00e1913050700740c0e100e06070384003250300c04d5465520302c030040c2c020020004042d0707005600348252601d803880101e000c2014450715018020400c0041038888050142c034101d000c1c81e244021050000390200301002a225140c8186030204218064000141108450203540075480c100c0b072000310401c1c01022254020080d0704012804142840000c07008001c4900340ca90035050711014002900348008120055800480345074540401107000c5038010403810020f120403600d000c860010500da80003912000c00d0006c0000301590380380344c009118029040800c08240c9417610b10007101c0f60407071585a200c0e0401c00301055038040104074441c070034050118400304002c4034040740c1ea00403151841c1d180014007030f881410740f540c0010b000380c0d80c120084420039000520a00042c403122981b040101004002280a401260001042c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 865918588 1250 865917338 865917347
    0xe0307081501090c080a11090d0c031b2702190804060f0b240c0607020f0c0103200a03090602030c040e010f06020303060d03020c0a0b0405100e1011070509040b060907 73
    0x40c1c0a44c03070381302d5001903074441149038000c2111407003246040000b404044102d1300d88103081c045440c0b184003a0304010b07003035040000f82ea41d1080a1000c4e00d03c2000c0040c400d15550201d1510b00c40e0180d4514848042410120720103409204040800351000c200103c141c6540191308501a900940040002c0c10301c0700500ea007a00d520345074098210641c9580304840d0040743d40c01c261200c035a11031043c100b00c581c80916007096070940e01c4000592080020090955003800302c1d005083c42421300700300381c480400ba400a11000c1c0c0b07111450311070300450180c0c50240250007103810254403031b01c119503030f10b4401901d489175003042c042d13002041c1e1301074004110301091800304401d45000790011070855507010b00300b0454260a101c12000c50240e403c941c0f0864581e0080703500540140704a0544403402c1005200004200a040c0707420801c104442c109140c5800105d0400380c0150b10b490342d40440030020417450500d0580c0541c0d003060b4094100401d001c024050307a401101d0440f1101c9aa4076640300440c3d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 865919838 1250 865918588 865918601
    0x30d0c120e070b0c010603020d0f0c060302030f2e2303031602091902040f1403010b0f12030f03010f0515180405131a040c23100e030708150109 63
    0xea00c910b1082c00103605400107004ca070800c600c0042095901c0b41d0210700007500d00380044464081d0384a20034200b1410200600c0500f180f032a00310300f9490440061202078001610ba1403503a04c810340d0500e4141207012003d403c0c2c42550b003065100b241d640c0340f0028202c3c1a041183c040c00b2244080e444140b5000c0204c41d070980c0701d28101001580e86070200b0042036809400b0f085040004a0b84081d03400490014000800d4645003400c2141d01d04030403071000070140700405100780d1400d0039a00315650f6840041039501c400340c1c1d034141d050380b80d64442d0780395100e185407002031190040000079032001c44c0c0c48110151030007614140748180c01942020301da07020f52a0108101c2418a6201e074043c1420b03400544d0003102d1101208194406480303d18100b000c14030713840c0800e10003004100900c000b00e401c20703009101950107041181d20081d2406408900d10750f007248507040000700080c1c440e1040880034401040103050314141340e42e546906582d034503070340801c001c00c01c0da00303000280154451180c00d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 865921088 1250 865919838 865919861
    0x140f030c0303011e03020d050c1302070b0f0601030e0114150102070305030d0504080702040c05120907060c020f0604091b030609020a0e010c0f0c060903050139020f030d0c12 76
    0x850039a400d1802c2c07850200481244c00118540784000040903030341c0d038140e0301400c50041000d401c1307141141d018801340a807d04030740d0010600400c400000204903110700c0342e0000940b0003489140d120100100e000c0c0c8403250448001d0b40c20407c109000e03840354072403180070303000b01440f011102846400690b00e0f60741c41c0c40050119081400b12252003485504100c1e48144941303070b0280703440c025500050860b030704034061600203400840c20030a50004002410b8119075a04000c0c40190329001c4d00030b040c000800350080c0035292981c5030550350385070304040d0340281c402c5060500810425202e403120607040d2110003000203060281c0020625124400c551200d0480d80e560324680c190180190b55200906104891182da0000c00350081074510103840d001d00543e9941d800414510300300745081d6280b040e18081c400302d144102850403204a180f0240d98104d41000c0315103910700300e209074280303041c1c0c46c140000ca02001494012000d00c0da882802d031383c1100d40f1a00703041755015403103004036a2200c115 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 865922338 1250 865921088 865921093
    0x90604030e01080403020a080703030e100e07051009051f0807050301140906031f0203010f060203041518080109050303190b03060c2a0c0a06140f160b04140f030c 71
    0x44014079441404202d6010f8046c3c0125142e032412a82c03038400940c030646090700029621442da000c901c0061210016040d8005828080c030b2002003449600e480b924070919110395000344010f00a54056180b2100410005143c180100410202c03814551f01c0d101e948000680d0540000e80c036140200c09880c1a14030a0302441d10350f1403124140a01030b1400b61090b54107224020700020014191072a8070b6002840540142e01c0754074000b010046070440b0f821800075504140820301101e00646550040c00000d4501904602061141e2201ea003400e5004100d665082030a40410f014000004500424010500703544210310454030200b00c0d0610000180e00d60040302c007040c801c0546001420f81320b80300041200e0f00020b008254582c042c20b521212a458000c0c078002c0d240ca141142c0200c0040070241030010101c50019400c0c841481141440800b0301c001081c829241c02c480c078094405540c0c0028a625a4201401c001c1400b240860480219201e00503050002c1c5001005030388111004200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 865923588 1250 865922338 865922357
    0x18080a030518030318061b030a0b060f0c0703022e031113030309090c0305070c120912030e0901090e0c06030a1517010e190b1504020c01060e09060403 66
    0xc4016000150508880e442001819402c1c2541440110300800f081e4121012151100c0009420a80001d20b8800c0c101c1001016002d00110801129071022481d40c0004407288940700240707a40c02941041684c41078042100e4500040010780c10084d41d0003201c0350400450a0380c14405001886031070416503114100f041928980244c003e070700c80e400302c0c0d100d0600300148020310f0304041911380d2082c0c00107400c0c9501044000c8083c801c800c489000b5140a1142c2d02e845072021380b844d5003045004202c8000170040351401840340c0ba01c400a0155200406015007580c10000d100c10049030341580b084044400020390381629200300c1d10256198000307040090701480800009800013452080801d459160742c3c036240f1074885c0b070f050160030005801000d00780b00341034040c210340741d03401c00008661001000c1c1202e400c4c03825804030859400300d8850031a40d00e405082030035490659a15070000c0c008161072003404419007280c4259440ea0a0720b40c6140d440c08013031541c40c4000c0d100540440c46c00704 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 865924838 1250 865923588 865923607
    0xb0402040f05010516060203100e090a1a10080312090f0c0a05060d06150c120f171f03081b0a020616020607080f0a08151f03061a0a031808 61
    0x11302425005200b01c00010341c035900c64907034405130f900807690303000d480724445018424080c503007000300c4c0c1000e5090b00505690b007070380d500c240e50090f44811500c000100440003076100c1281e1090040505068401d4a890300405d85d40201e0701902075903451001d015046010309004400903601540041c002e100c444600d20701014451554003050032000c0468851801098a050142400d04070350350380d540e500c806800c141030a035401d41081103840c0c00c0294a07900460307178a510a00b0152050709000304c0c41000d448001c3c00040c0400034228134801021541000010b014046028081d41c2e40d16041c49520406064509500c0d80001e000003584114140000120a07004a03c0c4030200380c4042c00f4586400d0058031502000d41181d80c20b4082110300081d0b20766010750040290b60010801550b01443c2c1c09610b000440750342000780c81c1d00c032400e806142d208056100790000002880c1608891441440c1c69028a0740e55014101540101c0e00f0300704442035401c0c0305c04880c0b020540105100d4102803204 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 865926088 1250 865924838 865924847
    0x140901080a1203021b1b1903080d1802031603060e070b16080702033a0243030c051f0807031d030702030c030c0109050d020d080417010b0402040f0501 66
    0x907601c0c0c070034208008a2400500743c200075410001880c500070100c0281101b007013001d1a01c0c54495100e41c4800c0b0030007040042e9804040d9110740d00b4007440461440341c00c1c052411190800c08020394584981075030040c88403660380380001664007498061201c200c480c030650341d5422444c40360705410202046100021505110342d03030a124400c406581c506400b54000034036041408000c1c00d4104030301903449030020009420895a01d02051810000b90440f0501a41b0b5034084080015148550a064842d071002e55200c003213801c2d00000344202110181c003003d50032a03043e000440b10415602d00200f0b40386031044854400c1c403008d001503c4503151805080b1034040001c3c3c480803c1c952240c9041403040e42c2400c0420b91080b54000550300c0321078600416140841900d034a5000e9000745139800040c1c0da000c2c0305034041c0d400c03c0da44d0710342d0305940d8808150000c001403c00740800d1404200032460080c006004055a51103000a2002081c41401c100403445a44120001900080f10400c1194001c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 865927338 1250 865926088 865926097
    0x311150a020d0c0f060c091e05060307080417031302040b0a0803070f0501020906041413200c0f0f0a0c15050d0b04090f0804050103110304080708091306140901080a120302 75
    0x11301c0200c620381d415991844240d5000c0e00040d0045440d0250034070040c214208604003044103520344002d91031918002c201c1a2102821101c10059900c1c00603091000ca070300541c01004011009503039a04d40025007450744401000b040f0300c100d040120503015481c1c01c6102205540c130f16030145107807045aa60300e41c48402d0303001c01224955005d00049172250345110180c0000c00c0290b401c08100045070041008541504041801540c645141e0690034444000800c000d80503a00625644d01c4013901505d04c4e24010b2001103060f4429408030400445001c01c000d40201e1290703003111801e5450725408101320030503004600020740e05000d091a03085450b003040c00591b20140c80000ca40350f69031100e2800c2e10035a601528440700004041000303503454864108158038291005040d42031a079030340e9040d0310812802900c01180420103030f1180d51071a200d0801c08160b800100040c65840c088181d004c4442c0b84214413404a000c00011044008200f00051507440403c0c800842d24820058009402 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 865928588 1250 865927338 865927343
    0x30c15090a08010504030c02150307020c040209040f110924071104110d05040b0a0606091202190e07021902030309011404151d0f13050402060d060311150a020d0c 71
    0x29079080000c07035480038441d281c000d41c0030350749131001c1071180d005108816201060780c0302c0e420420404c001402e41d011540d00a000001c4401594130301100002402130b090710400046032901c2d114101182000704801428001015030700084200d105045001d01005003000841e2040c4082240384001f0300070758071031020904010000101605030b421115031030342010080132040b0380c0c0c8070184818040303102040c691001d0090000d020703c5003096002481901c00d4812541166118071035070b4215034450050039034404001e010440000e41e500443c0d0360341e00c0c0a0314040054050117841e180f0715120b1a440303009458000c8c0045107040c90880045814180c10038401c040040b003800003246e8281c24402c0841814101e80e94818060060141f141c0180c0255400f00d10403003002110750299107070018190308100c50030744001400d95aa002250b0a4450560a022174038074000b4088200007100141480c076000654541c1060080d0345e8100d4003a104200c0c0300300142c0d20120203c1407562041354068403661 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 865929838 1250 865928588 865928599
    0x40f0b06150705010906060816120503120423060708161103160b010e0f041b030c03140c0405060a0504020c010f0e0d080a02070c0506031f060302031005030c1509 71
    0x24085800000307640003014111480d9455017880824048507000d00400780811801501201150030025001c1c40e8a0b4401c0c0d1407441d0040000701c1c00d012082c402c4c0c0301d04222401c40b8910380c0c9010300c0d11030511070400d40166080352420503801180c840001d10706224111607181e038041c5d070302c4004040003001d1084116004205000c92000c4a4000a01c0034110040c1d01d10030410f00c0d05c20f40d00e8980c1c403080303050300309082d603011200c00c01404a0084c046507801541107100740d100409101d500c3c0018443c142c101400c0a008248000208400070348004080e034904010389404080c030008100c184d40080e201c0d594404e1241406210f540f40a60041000350f03615000028411072a0340303040f00751610481800007a0304a05201700001341c0ac0b41d0103e5201d401140c0452902009984007800303141280a5540074580100029041d2909107140724100301d45e85800c9800c190352036a0082c042e51003103da5445600440300001343ca814002950b080405008280070740c140c54191510016400078507a00b540300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 865931088 1250 865929838 865929859
    0x9073501110d0605030a0503090613030c1824030209095506111b0115050301020f032e090603020f01050c1509120406090302040c0305040f0b06 63
    0x198001d12800c00544000190203440e5a86070030840c0c100c6040b580154002c1d04201103200001714044200d408091044031290b894803560f040d141c0c000415a00f00801e21898020082030242c804224034440c2d0011b074200348000c80c0b20303070698000010040d8454600303d02080040c2b00600c1d003000600e500050030b9040310f001024400049052203030b01394408125019041c9181442607000242d9102c007181a829000078403100b8900042c1c8601c46140034205999444011000f0a00202107a0300700625001754505074520300380d00e9001305100d00031210078481c2c0303040002c0c81d4113060003a941c3c042c02d10303492541541e50b1201e600060b030074059240b920083c2511004c036030090f00842c8010151080001c0090b0840c114418401e0100c441049c00c1e040c058240041250384000081c0010a05145903410596807504600383d0301e403119000d819030f500380001c10003107281c50380f0034503110451323000700c0d024400801025000c1c1d08440f0203840c00f509400c2d2180017080403400302c03407445800480140011000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 865932338 1250 865931088 865931189
    0x30f140a092102060d050a0906090302060a0c09060c1b0302030109080c0d17070c03020a0b1302150a0e1005130b07151a041503021203120907 62
    0x156009500500c00720314100024402c1c8002c8241d1003110040c10700d0301d8080482c164000074402d000b80d90030101010b44810002d50000741c1c0d90000560a580560180000030141c500a511207500300d0b44c43c66580d24240601e0b80491146180208588485d1500c1c0d18004480c0c8441304080705000c08812458546100080181c409226000800e4000c14a650b00e0b0201141c22a040c4902008101c08020991a40c0c02200070f40031700181d0083c110f030500d508615098a4240d0520b512001c01401242942040040090410600703030210751080307882d1000c00d2480c4110540c6801401081c0e000031350030300303081e040070f00b03040702c484c80d546815050640c00c0180c4010289414952500320038469600803070080100540f40580e100741d50100030050240301d420701d21105614211a0415100e103817500d41e207410645200014001941e00900310b410a807040307044d01a684d50001180e0f4400400c40d100040540401080c1d40b802c2d14814842209502c1c0e0348003091481401901611456280a8110005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 865933588 1250 865932338 865932377
    0x30f0c0201030b060412050d031116030210051801060e041e051c020c13020a0e0906012006010e090f0c0f01050c011e1a010801030f0503040e070c02040501050a12030f 73
    0x511b02e0b03041200726414985000c504081d01c180e514000d141c01d01c0700c030b003591400707140603207141800814900659001504080f0302e80b600c40c56105510714500000e00280000d81000038600318100710090201c90360b542c0c80c03502c061fa0708580181c4405102154003460041409440c65a80c0c0984100d40001610704900021100d42c901c1c80c3c8050f2384a41d07002ca0b05410600d100d100190720b144401c42c02c003440c3d032001a150884120781607224200301d10014109030f014012031b0115400340e50007403610140c1031082c56035450080c01248400c103031a40c00259034210010f4005040c21144004d840704040e482c2c1030000307400180201505109080c4240202c03081309218026143c0700031240d0070700f0920088010b070110303998a85c0316402040c40318410307412030b40c0040b8181d0440758085110066032200d41811130841c026a003203001d500382c03502c0a12012039400340242640070b0088804100c140d81c0c807400c01450b9101032007040d1311001c0c98205400840d0160490412022142c1021100c52044644450 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 865934838 1250 865933588 865933597
    0xf0907020f1504051905031e0d02040906030b10030f030e13050a0515090108030a080a020d1514040213030b07021626030405060403080f0c07030f1101020a030f0c0201030b06 76
    0x101c9071107640411081c80383c2005007410320071031000d000c5817180c1c10741c9071582ca900c030b42c82485540d10801d030440034490181b01e0460b000b01c03050700320441d1950348a040f034401034601444181c2d0303c03a40c140081554030850341990012079a2142102c140d040081e901501d1080308560385580c800c06034000d15005007254003074184140e1a80400051074a448803072000459403083c1d6079401340c40351a00500c94240c00000300c4000210505140b80255901e2a440000c0e2180c004441486070900e504207094541d03110958007501c0c020000c000c0802d04110600c000c138000d000455603400c8565604001113107002c0720b202d82001c19441a1051114001d6134501c0c00f9400740c0c00410328840c41c00d450801c0b410341c60722903032807002000007443c039003132410b000594240914000644024400503030060f10380c03810f001303c40c500010181a180c03c65600d040010500301d0140041d50450161040200c40e584041ba0205860794140c866090030009481c0413180e0302403021040703040c940d0b59100c9103943d0742c4190182 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 865936088 1250 865934838 865934863
    0x9040c0e0f0106031b0f032403051608010b01050a080606070b01032009061f0903140601150305090d05090f0d060f0c0801080604021e060304050d03060609050f0907020f 74
    0x1d0319490600000c04841c44120310b48203040305074007110800790303100c160710503030a866180200345102c440006040d45c0f030003904908000300c03d8203400820010046021544000c181220307010745c6a0b18103040303090f11141d8000d94000b94080081240050207211107d40010f33018042c2d50a002080d9a10000d080003a081640c0c130210104449610281d038084400380b0b003c05440442490078020045903110402e0800c8900707010b4082c140720f400920401000004580054107180120a001c11080e00c420081c00760319038803090f450500c0c15190190160602500500b0b00900c0940a54807045500750408230701e9541c4119130981208040e5280204505a14000c4400040e0080c03040941340441f000c86c3c001e042844650001001031070008035055600540580d450015515005072003070f824009100c4240d442200032080c0000e22400168071741c002c040d20b03201049103c0d164034041c2c1d03064031240300700c9503c040001e080b245241080c20101e41c1061050040795417802c425002d03141080c0030090170 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 865937338 1250 865936088 865936111
    0x6090307061503050d11070501110c060702010c1208060a0b0403150902040209041a0a150c030503130c0605070204050f010b0f13470a030209010e09090a05150702070509040c0e 77
    0x12140342c1002845030000034039090030100ac260744a1654039845a641c0314485105a00200780c000559018100c00008245d11030301d601d1030101c1c030900c0581030075002e5403818028407007607102240b00c0b20800d0071101640d0b0000e211130020521551101e00bd4600c00008a80064080c06428035a40700d80c0140e1006a01d5100414000342501d410b2024183c8968040c040c0070800c599040045a0040140c2c56956018030b49203542e42e80710085040368941e02003004080c007040100004280380e002e000382c014584200c0e802c6c0a6601c1d0a4110b2a80000a0003010300480d42005031106580a0300024141c00e040480d803054015a103820015031022a00306030000b580c43d460109401c100c65a071028503041c100f25031014010850360103204540660104d50303062650005a0541c41ea00034a407801d0503810080800c070581c41c0401c100c64945120304000c0341e841c8540c10b8101035182070760302c2451044a0690083c80005c4c40c00c000c2080b079010241c01070350b603411600300104156241c21042c034403a5054441 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 865938588 1250 865937338 865937357
    0x50d020d0b0c09040e0c01050906131d070806180c07020a0e0c031008011a040e010912031a0102120d1d0109200102031e090604120606060207050306090307061503050d 73
    0x9020540b500002d0601d5590000e040844a036030b0048c095540d401c41c00c0c2c4509071900a00c901c0740495602c00c1c0c01c1040c0c031030750580d402d848151560000c40d204860136039031511507440350400c2c40019402090580340c5520710340009448000c44030040c0a03540d000401c4601007580d503050b40000c03030005517042940e01000004203e4100c2a180c1580014071000000b00441401c8a400c40540c43d28801144d10494036844c01c00c0441c1000d41201201d0382d0040d21000d4500700c4110040c0081100641c090340302400d130140c410aa600209244900205080340a441c10000808910080c460840b420715140807521307030b844001ca024800c040e071091041c058180886482842817001d520111074041c11580304010000d11003a44015409003150078800403501c0c6e80c91000010464000d607004544603040c0545240e090100035006902100c59a03020b5910440d01c81007450707142c80c1c0495280280f43c0c0704000c441d0000c0c0d4160720000280081c6140ca0013015281e607076880c20151070b03400000c0010a80710 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 865939838 1250 865938588 865938607
    0x306060806131109040809270c070305030c0d060806040305040302011d0d0609060b04020f0711040603050a0311011d0d0908010513021201090c030807030206071404050d020d0b0c 78
    0x803041e048000c0300700641c80840b8030755038001a01c1d18040c0c041c0c003e00d01034000c40e0400c1041c0c020b55080600043c501c41c0d241103660301c0c5003d00c80120104002c140c0d5400c1c0810540d015250403258503a406a40d454030799911a10034010b66486101c0320202103654130f00016440d007043c0925070091344030396aa1982d0f14590b00006003c0004640443c0c85448240c0c086800f45d901c1c81c00b034440040d0b1005020580742e5150920790300900f0351454003a000f40c00055400c041061940c020081c1e58410644011722402c0502880100d42d0f16020081c050b501c40c02800001c68010b032400c0307e0b4908010000710b2000d1021480d0550f0303e00704015a4400c3c2d00c840320944200d0380090304080a4044000204914940703a1264000040000f5001c1c0c001c582c8a5500685900c0a4000e00310464201500744003503a0f5038541900a03500200701500140903c1c008184158407450940c85c0c41040c3c900c505042070f00303120030414030b2100e503c003ca81c002544048140084d00d01c041d86482021544c007216102d21804 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 865941088 1250 865939838 865939843
    0x90c08060c0406020105060405130b04020103090c181404051203091009030c060c032f1905250209060f18070201020301050307051503010308030c0c0304080313061706040b03100603060608 82
    0x1d080b948c4a2400d000c00c004c20340003003552403075038035030000d000e07145c10b4895000680091074480c4001c2c00902d074885003c500030aa5540380844d40d01401410440c07070b50000102400b0400645001702107801135000c0001d8442810302a642004003502511a00c0824149460450300e810170b0803004140395a141c07206200b4a44140c850110316030406000d100030000c0070b00280380c864030156600d40302c0c440780b101d451601c642c00c0c0d407032580498003040164507020002500b160010121218a40351031074000c0c40e00b26103038441d4000030b903020b04084c1c1161166070030043c0b04030200400a4000a0849038411032001c0180d0907030180046800050740c0754101024103040c120a03400440c0121f508071504880c90311040d0480703044030b420500e40e50316a298801c1040c02807180c0790a102c40340c4004600400d480d08044020302c01084a014449540c5a4132082520b00700b000c47c40342000d820a41d000624107083c5600105007429005042e00c0340740920b42c400e001250300a030800e43e00345550752014813040104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 865942338 1250 865941088 865941091
    0xc061309180201200a120c060510030615080c27130210030903020a060e07030203070807151d040c0e040e030403060f0e030423150307021618090c08060c0406020105 72
    0x1150403940700600400c9036560345e41495802446c0c407004031840b409151103040c01c00a2990b01031001e012500709041141049251400103071142c52030426002055410049503504490001001d001d041c4041c0c010070001c418191402c2480040410018078008081188207110710320000c03441203c00454014040310350b080c1c188000600d4a0114050003103500015061951903000501084202086042c07600f030016030b51000f5018411003401081c14100452a00c0c1500c50480c1540e43c95a9122003c89104116100044222000c00700e66001070500e0b40106040c14500c1c180080c0700801c0c1c9010400b1030740c010020078540c0d000407506100b00a04c9010300d0b202003070300c00d10034064410050645501c81c0318501c120f50209d2003a01c409104044a9400364541d000003e00c004118446009595000e5004031004070050060b0003041d0f0548000c01e02041c00e44582a5241c400c0741d4041c00400010018000245c0741c1901810000690850400440748545200c03e90280c99600d40b62002c0c0c01d4900 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 865943588 1250 865942338 865942367
    0x608031c0515060f0409090f1401090201080106120b0a0909020906060f030f0a110a031b08011a2b0615110a0809060d0c030e100e0c061309180201 64
    0x28182403005104008944420b94001159425541c0d152203241030304600c00c40d84084103d60030040020280302c41c1c8110f03510902c1c001c0700da516031500840143c03400c86644100c024049502c580041c0406480f5144c0c40390345141c0200000b95520684001a8000a2944c40b2201058032070010380f04500306070704282c3d04001c060b5030141c14803a04407101111400f0080600d1010398000000a00b8220580c11410503000c05034215a690b0220f060020003030a0320440d607450080031007903954540d620034210141256071030f100340c1003007100d0200c0c0c0803643e6000b030f6108203000311581c1c240e103982c003d0b030509071801c0d085410340012090704c1c054150302007036141d4507a1000e00900b11084442c017036000c2070007507020364403400c00340d03031000580c0c0001d02718010050314854152a01146031042500760703005c030341c488000204032403509800b0210344003601c03034030130b141102904000c19580c200e08102010700140c901d40842100c0b03640d05d984c005001c6a200c18640440300d480e0205820655070004a00b0b013400b01d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 865944838 1250 865943588 865943591
    0x2a030106060203040f0b07030221090a0b09090c1b1507020f030f0a03090611120a0e030705071e08030309010c0f0c0210080c0904090f200a0b090a090608031c 69
    0x203140085c510442c10803449442c0300b0580001d400c0e0101031003031201c0c0c0d91700070440c2d0300c2c0c0c02022010400c0600b16082810701078041c840c00080410300c44007070381c00e4a00d6200c008052122651b00c59100207440e03000403106446005e400081c81c40d020780b0900c45040d0f40c0c12045038044003440d01c00002860001d8020070f50300c1ca60402c2100340d411824800484501c80400c0c01d021030346000301d1030282c0c0201043c03007841c10190404645c101500c2c0710011514021100d9030000c1c0036819200740d4090b10b07441039000007032031036010180410400142d400b45110f01000c8005446255548000341800c6070b00c2103a01c20000e0f5503880c80c51101507002500e042d001052450440402d00301070340482e0078203080c45110010700452030009104c10804004682081034050306c1440101528a0a9000038800710000c5501c07004004545c10710191849a14070141e00040100007510b1901c04800c0c480e41c0b0040346c0c0f41d0444400c003004605c03c482c80c0111002040c03031030011981c80100e41080d94028400400108009 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 865946088 1250 865944838 865944847
    0x9010f060609150e0616030201110901090509060a1d100b070305032701060f0518060d0f150216110405040c05060f0c0d02210403080301090e2a030106060203 69
    0x12a8000401c1095030819842140d90114a0b001500c1c110384c50394419900a1001036440d125180751046206028426002131150b030307034815551041800394a00711070005540003000c00591612a500540008000e414801080d407100c0051403001103041000c08049007420610143c001d00c40110f0009004001b055800d148542c0c0e00140288006080c1e200030007910424108158501c800a0361000d840030000c100c281e6441440c11a5442d140c800c8610400c40080d5070100300840992152003158002d01414041c40c079a561848940c2c43d034030301916500c030784588040001086100800800039050345890310250741c0d00c4d005281101d40c01c00a40118141014040040d002c20170306015550125929a1101c8640d0080350342d5000d904002d00e080d01c41c1d8a03078090410b0700443c4441c1e40d01c4424000b1141701c4032041c01d82c16107209903c0024600d0341c08100400070880c7c5580280e11984100c0140c0d40079055030b0034500f4140100a0b12951050b199500d0248149424803c0000800190001d1801c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 865947338 1250 865946088 865946099
    0xb150702180603010e0a14070923070c0b040501060e07050702031e16030614011703121803120906070207060206060d0302120d050114013b03120309010f06 68
    0x35541e055109441041592020506555003134000c51240c03840241241d42c02130310b90a100c1404994a405d002050040c4680070a000081c1e0240024020714003290055240340c0e600c41142c0d6000c000c20070002c000349408494000f44201d400580030b42d00450000c9800750038040c060b500003d0103000507040c040304016510060b00d0108441d200360358044e20070200d40c0141c5440500308502510000051003410300e011081100175403043c820703450703c2d0f2501402aa03c0785500581806601041c0030190f02c1840001c04604600e107546620203800b05010b100000c150910070b15613008102019520340b1032800300030100c00c00700442544180503200805004c0d2410601a4440324080c0450740146034880e40e45003850f008000c0780091000181240e0781c2d1380c1150080a00500b4280909203006011018038001984078220704880c0d80f01e801400c0300742030040003e150584800791b500d034528680d84040c030801503406104901c2d1808221088550300c0c0740440c2001d08452070909040c46c120704c0c00c0d10a100303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 865948588 1250 865947338 865947349
    0x4060302040e062e120e0a0b0907051e1c120e0f2409060307080115030c0f0305042609090901150519051e04050f0f0c0703050d0f0b150702 61
    0x2c0b0128807860071025113214031411200c0d00300300a02c410721142007414400b4140800190381c2180d6001c0c0403030100c10b8840c16500c503220407882c4078a65028405001514002c8903821515a81400040c0312070000a20700b030034003915442421041ea0103603098008808143d42000e20352400c110121140305407445a0000261040701032554808503d035030fa4a050b48121100e012038818070300080603d42c036890181d4004001c2d010900a41c4000c100341c500c1440b0641c080e00034680494840d803248141d2503584c950880007000003c1094690482c80329140440d00d0044071030401001c00da8083d10369810100c81401030000010308100590b031f2400354140c0c11103284201c020250340d0300303c5100410702d05124068040c80e00d16008598451802204840324003d1207440d6a110340044e5014001036486d04428081044129440c0070f4081c00311f40000c0b04d03411035600410200b803080c04c040e400c1040110006084402e1031040360700c0c00340d5030b110030210703441c00040318440c1d03000385403105107020382ca07601080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 865949838 1250 865948588 865948639
    0xf030b091e0d050d0b040624050705030301030f26090109140f1011030d0c120b012f03040e07030b090108030d052d060901060f270b04060302040e06 65
    0x4200680416101049213494201152a060080c414400310340c070756400e0710b031040041070700000c205018420005040c4c0140107896080d40c1100c06107055a11350b4488400800c3c00c56412282844c450380007403000c0da80c5856805002d5141c0d50040d03120100e0748000341810045400880e04040d0802051350309944030b209206c2503807001c1c0c1c1c480c0e200c2064200705075045425071211401c18040030442e1400d840b15640080210380e455603032750030076006401b0740d001114464800300303001510070303440c2e00b4442c1d00014030b13152801c7c60b0460070200314240c4083c4c903041d41c10a0300011800764080051003041e640c98041c620103542c5c01c860501855260501d00ca50f41c1c0b250010b8220855222000a19240100c010000380d5210016044030103c03004084c608000c1c0341200d40510603589800013160340751003100740074811461034503200301c12040240c03425003504c00d0b4440d01001c9561100302180388031132036000e000203050688001d81c59a080c20b02080c8441401041d9902034113640002c1d80d81a0030010250 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 865951088 1250 865949838 865949863
    0x1020712050a060f020f040315061d07030c18030507050307051516020109050a06020d031a060d020c0102072102070b0a0e0f010201060305060711160b09190f030b091e 73
    0x20130003051003020001e030107400000c01e44c0e604081400001d1085640b0700e20003e0700c81d090104281034035054990030915042c0071800c3c1e2a10754000160a1600036030001840e41c442c0d040c20120032400c5003290b440c03a480703504200c3d5075800109040065050402c1144080e110488850700d2540c02c410280801e8000c0c0c405081001d4540000c40c010b40e40aa40340e200038180c060f1411482a0f01d0b0480a175440034800c4041c40000d1502000603001d241252814508031002000e20b458814500c1d0381c0c034060f4001c80b8a0030a00d542c00c00c103d00c000341c46c070191549420091200c03c00c0204003254041d003001c00c564800e4000345030401004a2255100f0b04485040208031450304421140d800101c0c010210ba03003004140c4e102c1c0f041403155a640080c854255202c8560460390014000000284c040045d032103a030b0f01011040c07042d41a5484c10400b20443c080540310034441181c0d4039441d00d90f80b064668415651281d4140c103205c1015810300100100280740c007044640c46904440440d55020300b000d51 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 865952338 1250 865951088 865951091
    0xa080318150c010f060e0a0b09070f09050d03020f06090601050a0b0c1e010e0d180e041a0a0f0e0c0f01030c0e19240c08030a0212070c0201020712050a06 67
    0x71001160020341d09984150070003000078284031110140200310038001d401203202c1c900d0018249002c00e029404012501030015410f9468599081d2028008038004c207060200d007910100b030b15110302031b0300141a4040d038020905000c000000c9428040e000e045012203811090062205442d001e42800c101c0321007194143d520030407800401c0c1807240440c00f000c00c00c94a00754020280385d054100306000510103040d41c0d400104404140c0b550040f49000000c06c004034242000301c0406c043c01e842d03010f03020307071403104c00000d154000d490510401c482c00310406643c2d0b88200400c01180c40b420680f00d404000402607031520200052502d01904911030406403035421909250344100b48035030410302c01034400741d195108a11901c1009005015152004c1d040400c0c018444030072449040119489403503050030340d003094951501641c401050000010f400700310716034040304480c0c0340344c4c0300318619907032613940c41041d2000a0a10300f480d40101d0401c0f5060441501142c404986e4a0740f41e64000e10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 865953588 1250 865952338 865952359
    0x60f170c0f0d0c091412070e040f080c1005160e0d0c0909051e07121104060b0f03060f041a13091e0c050a1211181003020a080318 57
    0x812a10a12402c03003600e18042c20710007202c82154010250b14181c0304060410707081d4034010014018803142464013500d1030790040301c007001419219100f55030024025442e05450f10800d80358120300d907024500140310380e40194040304070090203100f06504442c0030516883d1481d64008000d143c1071000005510540c00c0703e08040401c219003a10740c0080c05410400d100e82c020078200103840d04503120381075507003402e0300500d241000d4000c2041d0003554003140c0c1e0381d90300a47c161906407014603a000c065070050f40d40d50020a040114401600640d0b00814038079039030780b403c00140b044864006070690b0045080242c080e00100e603400c19149941e03020b582ca4070140f6800103207400a001d1680000d4030f04001949905068582072440809541c041c41088848650300c1050020300d45c3e0030b1040c400c2d4004014210304c00a9141200c0c1000040c00414130851120b03002100c011041d0199240c00450a160f6400c004604002d405480141902009141031041e41c2d0b5400c170751a110b002860780300759103808 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 865954838 1250 865953588 865953607
    0x804030602130e01080309030f06100b0c1516111b01030207080d090503030f0112030926070f05190308090603060d08030411041802031e0307050f0106060f170c 70
    0x1d603480010f01806010602c5560f4442000f6100e920030140e6500134029091149901c00340018100d010300014210068018580000400306410401d0b070b42c00c040c094070507003001d6004801c03030150091030000e90000e80d1000829000d80140422000c400c40c0b50003824650710005030036001a800c2c8102800d016039244c5080c50070700503a11a001c4807289003403070300007070400b80280000070b18801d00d00d01c01c041c400b0389d80342d40b0072400e034160410000780000c40c00d4000b4041202c0d8a80d44101748414408a001541c103d6001c031810840c5c10b80009100704007084040201385081c070119548401c4038010080860f041d5140d00202e0703ca030841240c06600300001003041130302c4409548a80315000110325840c6d05103450304d0050300141d6058a4440c80c1051107401900c0403071400300d6401075008005200090f1410544280c4807911032407010180014405000403450600410003096050b6000180c001c1c10100043c00e10500644c096041041c4604205800003601d0740c034035082812248107944501441 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 865956088 1250 865954838 865954867
    0xb06070203010e0a020414010311100c140a0b010f08071208041203050702040f0b060a0c0302010608070602011b020d0c20280e0c04090e10050403180506070804030602 73
    0x4200290950b1900149190425010443c0343d0814801c64050003100c7c4165034000f03d9003420300028204140112801d942413410a03e0051408031504042c0c00100c21502c0301c00002c2c0b034401c000700e00c0e504404a050100000446070070701500000040d64659411b160b203050396283c25000b4660340c0111520210140514102a5001400201400544020240703401010b0703812016040b0f0056040c81083c01040225000341841004040c100c2030511400940032626114403084c1a01995600c0102181c00001401041c0150086800101e40ca20310301300d046200e42001c02081c0110f402c40405035a02560280078015080d82003100a5a80c4024043c05018480070002c0a0751007555100075050307840d083d510742c401944643d000014229074581c0c1151110108948942841c03030104014030580256a0000712441000c4003200e005520103803006040354070946046d0b000c241c3d1002031110305141c01603040050300301600c0c00c90070039600d5552580075020b00d0000618664000c180c00301e108000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 865957338 1250 865956088 865956097
    0x1401110f01051003110406531501051c051006060908011802090115120c050726072406060f0201060b03010e06210615010e1f030b06 58
    0x3500030426402e20201d0035202845621040302d154070307031301502c54451038180f2407001191005000004200440380780704449842d100010303080460302c4000c00d10041da05079141480c001c4010b0803d0400c0710503914281c90300d0080d403001416080414014000b540714580c2e01c6600381c3e90f0121003034900c039640c82c00508154030300581c4011540f81110008005a0200c210011204200020040400b56645e4051250301c407460203500400d10308010455905480c00c1c1d5071020070280750802d080203d6000c5002601c030034840c0d10001540111300d00c030600007684143d5540c20b60703042c4080070120f0308201c0c5209130300403400d02814001728180590003c099003601c8800c61607001c82d040050342e4581da8050908028008072000540ca001004100311a0080450341600c020781203001c0b480c3c1e28841004803c001c0c4090740c40d400142c02d59051846082041174074010242c1c0d24100c5122103450000410400e028504203105d0b94862250341503080c070f08590b0312105a481c3c0350204e426900800031620501c00d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 865958588 1250 865957338 865957363
    0x4121202030c0a031130160c02010e03120409090b0c16120e090a0f06080706090b0d09020d050105090d031b030e1f29360103060f0c0504140111 63
    0x844140041001d42e08015100c0900c42e20b581100c5a490300f9090250391a00408007d011036100440d5102540c000c13030001003034610090480740000c0c041c0242c404030381c0080e4421152140c5440e2040c0810040030134555110455421250800c8101c04c41c8116100c0074980240080c4610f04140300181d20800c2c945410f06809001811745040a5039241c005145000442d075002e46014004500ca010104040c011204507a4030a0500d03407c0502441165002400f1082d5550703580703188030016190b01165044aa0003140002598600910043e040040341d800c0001010300c0d090344c92100301026200e540c1c640e005131900280d4a45aa19001d140141e00211b00300801483d4103804000c051a42240c4020782490b581e800412000034803986000c4c5c09c030f00721164402003d1004442d4101d4890107800d69070b0790140c8003003008124070300c00e824040d0f081e04107884c0b82d030311003901040c000158012143e03028401d240c441d24161070009006000d040a054150400c1400c0d18801c1d2255420891001d65a1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 865959838 1250 865958588 865958617
    0x10c050328051e01050102010c052b0e0a111903060b13020f07031e091a0f07030309030e0f0a0501030b0301150f0510030221180604121202030c0a0311 66
    0x18800b071560743e00080070b0a9031840d003860000101d90f65106005561442031140c84203401d202655243c8003042d80003441060503045005000005221030380290848102810040c0c550f00c2940d00303010420b61b04503d041c6d03005014079a4180007a0320b1540d401c4041300e411038400070300381d5240000a40391580002000300c1703c600104801000340640ba0040400305c0c825201d18201250100080c07280c00e0000400d075000c200f8020040180707018400200e804103030321140c464500b02442c8100b000030f401101080c1c0000b66108880810950451000310b1300c1501144d542204200720f000003261010345020342c60402d900c8440d0324030151400d40202144080e40e040450b00641c8803505041050003034820a803051600800100005000c2d100f1120b141c4140c040070103100e52100c000140c014009030032920241500c4045124071041445078500039480b6210500c01000b0f10030f402490009003280c034480851042040c040c80c05001070031a807400c04903080106084005502020b0140100b409070142103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 865961088 1250 865959838 865959841
    0x525030e040b010309020d0212070f030602040e0703180305130e011211091317041503050109050a0c020303011503110301030f0201030f050f1f0f12050708010c05032805 74
    0x90381210003844142030599081280311094401102a00c50780386010303400c181e4622851025040c000c15030a11284188101c81c030311a80c801c01025141c825030b0058598550100b03041c004202c1c0318600c84d0b00030038945001d0040311700102981c2d501c01c60012000b42842030000b95040c20340d0f4400c901c2c600421580b40c00c400c55680d9043c2c0c880101142c03c200b2210100074800c00812490714009180c000c0c800402ca500749046642e48810040c0a0214400d01c801c00c140070010f052604001d03156803541c1c150380c0205d8694504010001035a10242802a0490038909425500c41c1d0000980c0c1c111200c00d40c100e800f010800c3c0f0154024809070900d00c401c17100000021080c0160241c900208501c02e9a040080c420401c1208044a00036103402d08a401d04070302080c0a00c8100340d80448422082c10b00e00a2980d4a020810f02440141d00000c1c147d40414030000601006000c1e0704010a118402804048280080200070340b00051801d00c0c0e02d0b07020b1070440707540a500c142e40c800201004900b00102e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 865962338 1250 865961088 865961093
    0x1b0a03200a11240408210a230601020d080c0906070c081b0d260c0a0317010b090d030c02060a052a030a0309020d120f0818030a0525 58
    0x222511907100e20091050040998031080c40345841074100c0b4589660420075103d0f6a17441d00ea580c458080d16545c40b0600000c10940391320a072600c0c1c01200e041c03c0c00036030f50380000303030b075114110461184100300a14041003104590f008545041418070714540036545980c1d0b014004114042c00f10802d030031a00c086100c43c01c000200600900b40c454450403110880820b4111207441003080c48110f030401000c1c4140d400040655030491441c0d850005001d0760080180111039030b070b400444040100da8052060341003410f8108491813110750b201045060650304100700c1100078030602c40c01700c3c010781c0981c0401c410305218003105a001ca500070071003560344940034002070640d00100100d020038444609042c820303103e0008011403008460303015604002c1044002e8008111300b80c4282d0304005113003501400141d01c5822048030748010b444189689006c01e40c0188400d40c0148245880601404440a1780c540001034840400e42490510369645146c0001c90482003072940341901c208452105804 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 865963588 1250 865962338 865962347
    0x2090d050d022118040e1015060e060304020f0108090a0c0906050a05030d0207061b17031806100e100b030a0501141801030602030604020f040b0c061b0a03200a 70
    0x10381d024071000158040d0760f18645615511400c540302c040703001000024040390825410010807003a181d0150b407800c0c02c440c417902c8140c0d200c504e0b000c0208034070b402c414044a81c104102c550440001c0e6401030842c900342c3c0c0490010000c03d0000e03810f219510000452455081180c120b04540c050449000030f0740c0c0e000d00f50050320003400703018440e2039910004942d82c2400a00d018011a0700e44c0103145441c544041079070200c003001c0c0300303a862111020000d40407908840e2000084080e962005940b0303e07084000c602030301c110300c8402500350003010621032550303002c80e9984181c816140342c41c070941c0c8510300844a41c1845a0000402003c00300c04c002c0b114009901040c100d540400758211011801d00811031981c3c0c1d8006203010b401500c1c001840401c40755030284d944000c001d04010314080c4040744514840e000340d40040d00d00c0300002103880c91800c0620417030fa0070a40001d40081c1c01d00c0c4548418209004900410081503a60103800d10640c102c0c100c1500f40c0424141810390729a9544030003031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 865964838 1250 865963588 865963603
    0xa0f0b06030a0f060c200a150b0406031b0914040314070c08010b0a0906081f060b03090709180b0a022206091703040b0405060706090203030f0d0c02071802090d050d02 73
    0xc0106a2141103242010483c4803025a409580800340400010715600d203050b910051007540b0400f91784a2740810503854612400000c0d41c000c00c110692007501201085208440c0c1c0c00c0381907114188450601e51040705a0780c2a002036150501e1204990546040c8000c2c0c017400c1000381079038001210004100c04198450100c5040544510184640721007007001130356090312411005501c41c500c145800b04030203120114094901c03101140d030341d44e07903a40442d15400c00e031100d90103a001810108013246d20b80c8180040780c040d07100341c1d1a20884640b60380390440c40041140c42c4803070700080d07000814924070501d400c0b089440c0b0804800c3c5619144010300c00451402501c0500421001c2c3c800003180001c00d6034100c4400c0c908035442c003810700c810710003140c11001045446945403010080140c0d42031000e8086402c18458054440850300da01c3c0007640d1102c001d0009642150328203200c06411810150425102c0f8040075a0380c94020000c03c030313104c00c042c1014086016a0340801007451740440c144 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 865966088 1250 865964838 865964861
    0x5150a15180507030509030a113a020c010c080901030902040c0f1b050c011412070810170a080c0f060a020a080618040615170f07080a0f0b06030a0f06 66
    0x100450350343c0d09410340c22141d05441c0b911055105100e2251400d100c0d010402240c00544151000401d2070703a41c0200342040d69010500425013002c015030b00817140c1820417103000103480209400e4140c0c00000e41081103200001e00046000690300141c1c0c2d0294114090b41c1c1d80c00343c8204416810f02d88010003003140450000005440e000e6040070442132141a00580e607086070181c82e1102c910001581d13000f107145030344010074a00703000c059540f00c0400340040c0b05001a4568041c640741c13070440a801e845007504480035800340c0443c1251360000004102c1500703503004070420b84d110300740003500b031500701841c500c106c0e5403188100f084010b080d1350b000b9140000315038562001c80c0c5c035000704204500c443c05407004200112800020702061207074004e401c41008641002e007107261196064006021184144801c540c091440040c69110070400b9100800006020345052045940d515805a0b14160081c041c00122404500d0695003480034011503940030442c4460083c181c41c112018052040c2e84 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 865967338 1250 865966088 865966091
    0x10b0d1d0d0f03020f0f1e040311100c030206060d0503130f05040b03060105010f0c1112030a0807030b0303161106030106080a05010602070608061c12030614030a05150a1518 76
    0x40700c89090084c000e071150241c10a0303409082031041d24025107070760041c4000d13117509000365200c54020316184008101860007908282009404602403001c0750314082100804c02c060001020301080e0b010441c02e404c00c00c111400e208000c0141440c034958026240355081142c245000003074081940da0707031501181d1082e07805015640102d8100b5403900e0091140c140420206880040c40c41d10030503030303440302310302c282010040290220013003000801d840070503003c1980001104114241c0000c40d09078403202510b418840d41703003600d000c00d40340d00440d60f14506010308103103008100108420782e40d10062002d004a034a03507944440041410800755030200d4031a280a002140451000c601c00d425101d05d0744440c0301644424061006100c0100c1070341c10000000404640003520545d04840c00c45119500854614100380b41c049454a844680318800c0e80b044ca07408000420111381c0381706940c1643c009006030781d9554112009010302e80201c2c840d14140c00c0b40800c845011b1200c415080b840d4240 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 865968588 1250 865967338 865967357
    0xb030f0106032d170c010f050601300203090c1507030e0f06070b01140117040b0106050a02070f0f140103020702090c0a0c02130f05130b010b0d1d0d 65
    0x10118201c440c540006000040d0300c840c0c2401010030101e8181000518074914814070ba401e45407001445002c112a41001600040c4031405140034010709262959009040129091080c00a40341d640e14400382d41080000d00303071a40701c4c11030001901040d022200c0c0c0941d668506041410f803502500c6100d41d110703210150125480f8120306054800320340c0e041e10b40d40c007540650402c1001e041d501d4201e0f1944400304005800c005100034060354000c020200002d1034900c070b083e002404125842d10041c2e0710000e694200b101280c40f400c0b059044401c01d041090303440c07070010742c120b0610359580c015010954421000090005801c100e0104461003d01002c02950321000110180e21510034040d61211221300442d00940c803001c010aa06540d03400d00a0032281d482d4007103000ca00e04040d00e0a6140d0340c1d035110703000252081c00b40651140c80003010f01c86d54012a56016100003041c0030741140b40f540424900365200b01e645c014040c0707201070300d8072080c1080c000d828140d0329045d81c0035a4000400241 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 865969838 1250 865968588 865968613
    0x15030e0a261305010309024c080c09030109020a0e06011e05030612010f11120109090203120706180f140601061209020f0607050d0201050f0f07030b0f03100b03 70
    0x305960b0030408120030403035400c0c40c0000450140861030000c0c1e81c8280181c070f4520748140b010840164441c03030311400b511015000c42d0005410440320326601d40302000b44005e803d2941c0d000005039031004070481d1032511841c94102090050501180c02500125040c501062a4004030304152180c942640c0708900c60000112150a50084990100c081101440480c0c2c0e54a04010300d035089500900c00041c60007080e440400558a12480c038004c444000504120320b2803031280c41c83e001d0300700c045040c000b001a03640825a100030b1140e6594400c0d0000c0341c02030800450350070441cbc40b4003200600c0d4142400030700303000b00c1d03102000808407071180c100d00303140c0d00000c804505281210b860351581545000d003800c1d0000500040c4904a03481603410f0401000ca5594501805200e4001e50080c172038102c041c5001790031114098030700703150301000700304101030311130384250701a0300000524000c24294a0701e80420082e11a902c6010ba2500403211910082e0301d0640c4174044080342142169246030100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 865971088 1250 865969838 865969913
    0x1e0c031428140a0501050a090201030b03030c07120f0b0103030806030d0e1003021803190506011a030406020a0e040f0c090b0f0307050901051c05041709030715030e0a 73
    0x804103942140c00c0d0501004103031400040c04402c85000309954491045640340c0b400c580088400080041d540c100800a65903d4400c411404c0d1003a0f00452070600840d48107a42c5842c20312400d40741d55001201901080b00d2200034903405c66009c00a200156160326015146020403900c142c001d05c24603241244d0144100d14100d00c000d009003840400e00c5007110110065400b034000800c102d0003080300700d07003591810080e07400c20080016644900c10450320f17120b4180759040e440548698108903c600d0000c14107000c80380c000d540440c4c010fa42e0b50304c8941c20b0b102d4203221032040c0e5015141031003800ca550741076003151210381c040380d44100000b42c480f2100d0440e0b00804811840c200018400134004a008a004050000c8141441401c0c200d00401103400111040780c22811641c8400511081016090400880c441c080c4d4001d03040080501c007003903031000c06208018102a620148500160080e4460860101c5060945108444504140c0103045040c4200389200c0f070300c01000485802c26 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 865972338 1250 865971088 865971133
    0xd02100b04091211010b03070e060a1502100c0908150415020705030306240304120e01030209011d0105042c131223040e1605161e0c0314 60
    0x40c600b980780c941c2d29003048030000d100301c4d1440d00039035a0302c22030021580d0400c800301c007d069651340910285005800e01903c05660b0b8014903041103002d500300b0400390003082d408840e26200d2070000c3d80d5280030108903099501c5910041d11400703209061810f900c0201c040380d100750300035440141070343e900c405002c040307208514020300907030424008a100307890940c52059030b81c50004006618182a400c0c0801385034420b80b8211785000e21079103e108681e0700010a025421402d0a045042130480d0002030281c0020f2407080394000d11644000501da8000e401f0349001e8a024504014800780c47d40c10400c02d00c1c48541c2c11b04500e007007240003035841c00000070f240009071b501407042c1244038250132083d114040b0b001b90302110908900c030050104008440580300403c000030141c00b0070304164000a26042501700714030200b02c410445050030810f1082800400c0b980304404a40b207800d05654070f401182401c00050203248051800000d200e0012101e0b10329070703681c03401c2c0c4170100861545c1140040e02c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 865973588 1250 865972338 865972343
    0xd0c0201050912160212010209060a11070f0e01051012110c07050f0d0803070c3f0914120d08092b0c060e0105070f17040c090902120d02100b0409 64
    0x90310091300c00181030040409005291080016040c03c440400140311a04007011250010744545092021007c00f040b4201c000d114100b50002c80da42041d40444011405018841c010003603100d000242c54070414031000c4450340d140c02042078190100b1056440d0f801005854003034482c0e15004641480c1020fa040c0b8540001062100c2048280d500c100403600300a02c0c920510403c2880400841c41c007029400345200440c00780c0b0221001d0400000120711710080c2d00c031340080e203200f90700740d03060304000750209a9100720140c04050300c0c0c0754000343c4006407014024466000c2d690004882e50340050b035050191018030241c54101010490700281444a50b2a00072040c00e01c0e81f1400040d8080d0b891000c0890056001181c203a201e94074150a56409a030064000351403050601030b1590701c0b0710400c440064041c2c81200b01d090940b11a2025520b5000308a00c00e0f54803000c001c00c640e0791085002004200e041522469080d011300651a2184041680d180d2401c1040440261030544181c118959 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 865974838 1250 865973588 865973617
    0x20601090f1e0e03040b04060306091109100815060c01020a0219080706091e050709060515091e0d1401050c09100807030605030102040e1f03050a080f0d0c0201050912 73
    0xc40c1c000e40b06028004000d82403490380401c02001ca580100a4010005403503240c0340803640c1480c16003440c0884684105001000c8828041d9030314650706c03421909168243c41c0b0300680740d510b80c03582242e2280141c862155000000160410707038018190060710642e1226000e4410040840f0fa640c1c421001b0304c0001070440c8410810f00b8001103035980300c000b40cd1b00600b441840000c2d4454134101b0380060304810380f4690b01c02c07a0200003104e214001c030005003000f81d4507900a9400b01d001d0071040c0c0600c84440303115014880003003072414000104c1030040c040082410700c030401a801c00900c00b46007900c000019508180c00101d140714002c04985200344080e200d0168081c0081c2c049031041c1014081c0342c101b50713740782c0008159509001a101908050102d900d4604241c0312001240401e01009208000020f40070804110301282080c1c0c0d00307811181d40303543c515240c00440c13607611030810700c542c10a1410403012030403641544201e1040120104079103100c9209468003c1d10302454807100442c9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 865976088 1250 865974838 865974881
    0x30d0e0315070e060a020114090309010905062d1902070e0c03190608010e061e04080315092502011406011107090c261909020105120106020601090f 65
    0x180550641a40411545040c032400920030002a4140d8440041040148e440781a00b840c0400c0d42e01c401500003814900561508005c0400646000143c1c07042074400c480100b81c082605010208030b007001e0071402503c10a143c3c0040e071160040e001400d114a07214148001030b5502400020074a0984d5041e090308201680d0711050f607041a4401058107020180d80d000f14415106240101c0014200550000c554401c1035950707145007001c020031450f880c443c3c24011300c01c01e040940e011600242c0158110381d69948400d0041d02020300c8540c440c0d001412001003050307500307c6604200f0700d100b8048000300000e0781244120b09890409014230314a80344480800d410358002c1002c084260719210650b409965a0301408088500c0203510002140803552040c07031010318404080e1400c80080650034003070505440c10300c81c04824490010015a13100c40040035a1b01840690386003280600c0c41c05015a1500d000a441d08001c0c4113299510782006205c0c1c0e42280c40d0302603040350040310551400304 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 865977338 1250 865976088 865976113
    0xc13090b010206160c050607080106031a0f0931020a080c0307090b0d02041112010501020715050a05090303032503230705040f0e0717010b070212010e0d020c030d0e03 73
    0x4071304181c400c0310901079555545400208140150751050790b1a03191050745614041010303050318441c00301c100d002103503003100054a80c0da107803004aa401c8d003036030031040c03c0d0740b0000c2c1000c2000303031280e00e0000c0061024400c450b000c081461400b0701d0703100703541c0ea48949940314015640e1310701ca00d2000f41e142d000305805000f152b80c01c4d0b20500c41000004e1503c05000340540205048402c602d12080307004c807000420007200c002058116004000c21720040c541e2070710700120120b254440d24209402c000000510f0710190b8490300c1518601d14004007500c0c1c2d40d041010303010060096402c08140a0810344e501e520815000c0d205180000e1051528003e05440a806c4400300c0c400081910003407203002d010120746001544c01e50300140091410301801d13814209005007031803141c3c411910103038145800602c4014809410b0b5940319038140d62040e00300544445442c050000c01c00d80c98900d00c0f4208032161003e90004039060080b506a05450f050381081008a80b039140b5031080d41e806070701034a030080c0c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 865978588 1250 865977338 865977361
    0x61803020906240a030b04051503060415060504060e06130510050d1406270318102a1b0302030d1b1208011e08060a0c05040308030c13090b010206 64
    0x640d0039044400d09000240848000c42904000c4e401d070000307540c81c0e07550106406c06129154020107554200b480f40196500000da640b03000500041092019491141c000c00440e0040005000300a0050141644580b10500401c50440300c107880b031034001e0f404d648000054860705014200e025120042c41d4203103014031140c1c00541c05d00f15811500582e54011181e018000c03c0d000d04120344090760b0320360100d0402480c0c01c91074500c0c0300907504100140101100a1040d100d0002c0003558456007120700304030141c2d0000c40e0000384000320100349a208580c480402c80032640103100b0f10444180d2001c20749070000d4440d8601000f505588680108001c9078040c000c0180c011342c10306109c82d036804880c1e48041041240c0c0c4090030100b541100184281003880d0034400e80300f211a80082049403821200680d28440a02003c4110fa92222252195841041124099a00300400c0c69607410400741d8940701e94000c07080c04800c04000040850000356501451407080d10503402001c46441d120400309 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 865979838 1250 865978588 865978609
    0x302031b0c06030a0b090c12070807051905030603070b0f0403020105090a0305030a081b03040b01051512010f08120408030403020108130b0403020607080a0606090e220804061803020906 81
    0x40d1803044400d800042c0c0d81e0340000710300c00c4000541c086002d03030990342032003540c030b001a0140c0c1200f0000d10002084c2e20428103240d038081d01900c2c3c42007464031011025a40c0c0d115201b03084000c030140303081c406c2c40c0350f0304100298043d080c01e400f158190380d503a17a0307500c171203001c0c0d0010a1003440b01040100702541c807035000fa01c03c00b207000300b094a00554a81c0c0d6549107130302402c14000861680400c00c01054030245801d01c012000b040b09929502c0c059031f4504c640c400c14006e0b43e100b80082d14035081c0c0500c600b825100404030401949649585400c0c5e00c510030f90396032042a0941c45011021510070025009071401c54034007900442c14142035a0054441e080020000c5506081c12100c81000c14074031900d41b130090f40a80c028000307605080c0d40092451400030403203960941400c004006165216042a0442d801707022010440e80318210492104450090070300d2805241c0d1800c00c1c14442c03980000c000b1617403036850320358100810391000a0f0b80c1005100295102403808001030b401d08208d00f519 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 865981088 1250 865979838 865979887
    0xa02030a0204120c050a050405091c02010b0424080a0507060c050a02180613020f04090b0612090f3007020316090e150606071e0803070309120804030203 67
    0x1604081d1036070603140030120f00d0b04040c0d60005046604000d03034200140c184014000c1550103100c0361901d26240d0f942e400c0022040b00344000e40d550702c0c1405900c00e41c0300c40303c030850040092245429114603200c181d45c61503000040d003c243e6000051202e0f00003101c001150340400a004001e1601d48191404c010b1404182e906014000e6000c0c0103940d1181c141043c0c4503203411000480c2410414411b41e240074810502d4100c1c0f0400503101c1c0034041406a8040780c4081c0004154200e8010124a2500800401c40c1122050400780050108042541d0346061f400e80d04031858659040d11000480002009501010003015055817100740b0300e1004010542c0050200c0302c011040b0030540c1c042d038402d5448082103030307522107041013850003d105030701039012401324000785e50030000d0000350713107100d403000081080b02c04130003084003105480e42e80344846400c20103064407481c2c00072014014000045080710620030308031b61400780f50b00a0108e1805143c0550080d42083c0d2580110002c84903d1450b8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 865982338 1250 865981088 865981091
    0x270c050f01080601180f0b0c0c01030c1d0f060409090215160210020a23010f060e0f180f0109030f020d02150703020f070501020a03151a160204090507060917060a02030a 74
    0x108001840b010220000c1c080d01f4451769452803100c95160402c1d454580307281c101814003e90b00e080314be01442d41225440301401d003809819000c40000c01d401e800107902d50300f120707000c10001b40081032603103d8101c844c000c1d2519a0b0400080402c60101c3c466481040181c0040301e000c4da000d170802142007504041c00d40101c1c1c0c0c02402c030342c81b03084204c07a91031380c012a04800048180c0755094207000381d6018084e0001c007401b00d13034100815882404401040381b2101110311300003840540c400c464011072008100c0c15102146241242e680c06021822401d4001c00c2810b8010746003140b0014207601180309540c040d01c0d42c00a500100d0064003c00b42002e81003507000c5c4844c030000e000c030800a04626100781d000694440404202070207030344910704500c0c0034840030503003080070a1060707c80345804203102d00e4160740c900b240c1319090100113101c20f000c0c1d040b518004445003000000181607056070155214a090301d039403100b42c01202d8038005102c20040e040200410340043d915000703190800e5a2000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 865983588 1250 865982338 865982387
    0x1006050d0c180f141501090f18150b0711060a1706030c10050c070b091f020a060908090f2710120f03031a0f06030901270c050f01080601 60
    0xc900090303d010000c1d510804c4003100600001041c10700320000e1140f030a08002201d1454008046880c0707d2520803001d4007003140f01c291116402c50781c040d11054480381040403886441c0c2c00f81c240079400103e0300325120343c01e060f5850928600034050f50003110213541c40c2c28004001340d03281c2c0355207403000d0b01039501441624240e040039559140742c2500c81c501c544cbc6290700c030942101c3d02e91a0080c2e139408002b1240301044203401a0310b0314103c00070790444108558850298807801240742200450002e000d140c5030000c0341003044903120042c81c010408441401c50456880100110804155140840c4c202e0446100081141d2110004da103e030541c1122549203030380b0442c0d0301580c0b900010403217003004c54070000420590144140c03030045600b02911800c5442c0b51020840125a031f406543c030800b40840001d0b140b5100f500160307040701c07490b900d00b44004803003071010a031504200340c2207400540300d4801251a0070700b102e40740702d5018140d40e51261920703100015900c40300b804248940165503000e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 865984838 1250 865983588 865983611
    0x90607031101020c0c04050a0c080426030a061d0f0112050a050d020d02150106081b090d03110c010806150708120c04090608160b0a0507020d051006050d0c18 69
    0x301500d084c4a0300300141581c0c0c08030804120449000818090205240040082c2c2682e80007614682c001d510020441401c2408201507030301b0044007640442010000080200c01c003415080242218019140403491007500301108450001c101c4400d85081641e0004014150361039400c582c100d130155044d1142400c16440d19820110390030355240140e445aa11072045d03543c1040fa041441c003040031006000c3d410110000c280003400740c0607581c002184154001590305c2e400881d040c80000919a030f41504042c90054100070035080c0031354180c0506400d6130641c0d4020481c1c148100e2004018201e80c1504084a030750a80206000307a4940c0801d2140010743c0e00c070060304a008075601c21015440340d00d00400c2c4000c3d80c4582e00004000d40046280d42c02440104050906541000d5400707070b118000005c04071950b018604004c0d500c06600c3d48000b040c4000460f54070560500c030081440203903140c0044c803c80c0002014000c18987c1003100801070080095944000f000d144074000c0351603031509 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 865986088 1250 865984838 865984841
    0x3030f07120f05010f0302150c030703050f0409091109090f03030105060a09030b04151503020d061a180a0609050124121e0609050903120c190f030f11090607031101 72
    0x91700b0090144095402c14415840d11130240141d11082c00a4145030040d41c0d00384070344070f0217034080040c2446000728080305848408410f441c00b9100503081000f98040d20300303143c0741c1003810900c03984c09010400c0c0495804200491510003410402000354910307468403050014a03400b60100e20100202d81c40d0100000d85d103030000a0085006100e600c1c03502400d5205031003144d00e412012407925415080c1040140c03140e030208421641c1080c00000c00d0755401595901680310351400aa02103180b42c004503a800300f0f014024014810804200000c0351605920002c41c0ca0070b0080d0007c080d910150b001040031800f01c464105403041c94502401c025003020002a80d02001d42c03280c080440a81c9400c50f01d04601c0303414010041c6031b00a0001c0c0c00c100e0701c410384078402e4030504103006071800c00142c00e41c401e030011564250015450000218800d4030000c0c10140343c0300340b01000034202a1003900703801150080300f10a0449110441c03400e4a402c040143c0392703200c01003c034148004c0b8a02c00b50301000a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 865987338 1250 865986088 865986091
    0xa0b03040606031b061d1318050321090f1903050f030a0f0e070e130503120a0203010501142a0f0f010501050102070906030b071103120114090903030f07120f05 70
    0x4400350342c0340c10f505044000d00001200c0d014116291a1400329991903910080100d130300d51f0b008400003441c104c07480001200f50720400005403c0707200c00200302c1894206068484034003001400040410785541e20302d82d459000004465105070b21004042000000c0250a80605486418124600718041c0c02804075604103c981c44c4080b03030381c1c2c490601c0c4640c1c50701400b0004404140500380490510b41d1070140c2c004050142801d20b00c4101e0110108002007040f00e1580b40f1040364001c40385844c06035280a0b5209000d11400600307110740a00c0031a2040090b00c040c01050103160320a000441c4001c10031002d20302181e141d030b04c1008d0407190009002c5c402c3c5680c920078640040342c25070400e00007a14207001544180400351900c902040451203404c138003604000e0702e00d0030041c01112404024654000c6854122007035500030300000c0c0c20504203146500d18072003a10b862800d50717100218107850380030841d21214544800c00004056500c00c0c004d8081214603d41c0004828901201e81000c03142c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 865988588 1250 865987338 865987373
    0x180f031b08070f03210f03110c0a080d140403050703030b01031103091b010c02010c11010e060d02042402060a0b0a0b0c0102090a0503070312030c0507120f11010203060a0b0304060603 80
    0x20042414030a21207005045d008048810248007215414090014008400700d0420010503035031342854000b40c071189040310751414170340c02120038044603807c2c60002503000340040b10f9a60310300924250640000000d5901c50354168694909000d099202030300a00150707800340e410180d8580d109610860004061401205203038005c0c550a1070030103071980c840720200c4400e410710007070303c05020060781d01020000800d60b010b200609801c0e00c41c401031390b548451801595020310003045001106d6046e501410441d0b500f003044030341c000509560305822a000340080c3c00180c0003c0001040d205154115442101000d40ba0340206651048152507075000310b4460b400c0c6135000035030740c1300904d052a040701c0548400c030007405000b403a5603a5810642c0d1680103010038151030f80010511039014030191600309412801d54002c1003c8080c000308040c0c40c030800b100104e031003103c00019814052083e00c0c130072007002d444c00540c41e0404007002c5c1030350001001111090348410b0702000158001e22422407221 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 865989838 1250 865988588 865988609
    0x110d020405090a0201030507081b0f0904020309031207090e06040b0a030b0a2301260c030a06020304060f060503071815140108090607090e040615080607180f031b0807 73
    0x7101c61000500740c0388040e00d008c042011034014001070307240382d0058a010948880c52140d0f81c601c1c070883c5202078066081ca1a80c010320202c00c2050211020000b0300c0b000d0306030b40c1f500c5001d076070307c00c07050b500a909402031142d484c6903040001c10a0501d03510504401000404140c0040d41d41c0da11004642c1044a407400d1154480d201003044042460b00c102e110382c44c03503195080030740c18000d4a14001140751683c0d080c2c964154034258074903005102083c0115005800d8440c10051400c02c03002035070044d40c08440a42c58001191821089481000d06903100100542040c91400100d4501c613040100e040881c103554200603015498034200850080005051010391902410009410302d0b50003001201076400c1003080100c0350398452440c90654031480004a041e4680d170403c88010302c012070301c032007281c0d41104004c02d0b2400e0000f07420b4403e461541c0c42c1034001c1c085841d04c07000401a071081c1c0002c80b142c0c481c00d00001d5080c1c41d0824007142c507650090b04566035a4400b600e0708030540e02022804 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 865991088 1250 865989838 865989853
    0xd0510080c120a0f0f15050f070c051011210106200c1e220e0708151506070609020f061204030f020708120d06080118110d02040509 58
    0x2018240520071040e18212a2039400a50030000d0039221a001c160040c0a895030400900403c03140c0b603c000e40c401d81001110301d400013401001e00003010140c0d8100703144c2c1c0049000440b03a40c4240b06081043d540f01014082d001c0310464000040d19005403402240c01c0140966014012440082150f215000c0c1c648080c551504c1ca019040e14002c82d03d1058a0305010044080d0188c0064082c91000c8183e64039600c200e40054035080c18208900316aa110410b032240c2044090300c80222441c0402054040000740844000265200503034407680010340c2000c0c800d0210512600e031040e9002600b40c1c0ba5250078480040021046d40c8402c40480e03030a0355840d03680065040011110582e8407054805515040070b0700c01310b801c1c49900900003010010f10f0ba014051480c800e0159a0040c1036004c100c9008400c1010303040200d40080907044442031030590300080401c0c3c140580c00001c60604210004c02401e40c075002088003003501403c6c1c001005000040060f203462203513911402c1168040d0112 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 865992338 1250 865991088 865991099
    0xc030d0f0203040c1503110a020604060b09070225150203030702100204050f040207050a1b0302010e040c140a05071a04062412020109031406100801110d0e030d0510 72
    0x45030041061051040d1040c400c0100061010441d482500c80080802c1030300304c40320404034050b00c0d81042003080303814007140e900e56a0341c0002c3c00c5400746104aa040c04096010814440d0342d81080b1003540041e800a15100d800c501e030300380c540ca4254204408507000c251078885542200d141005100010381c000010491b030140c0c10b0101d2803154168480951415190030300003032009a442c40c809100c0c981c0041c035071041141c00c1080721a8168003106008000c0002e82c019108a507035840141d0100d500520070308040d203403030300ca031504900c03c0ea210100880000b200312009504803a1114007170003010004100404c01c0030b01c61a40700f4081210504640c905444e10070107880c0c0010808040301c0c062032603d010031b1400704802007030780c908041014240206000407960080b20f40e00c0542040c64081040e1100c0354081f035614402c0403034031840d50456990b540403034200d0301d03641c500c0034103054148001c40c0d1141c240c0d0401c80940340e101d4102d134188a078460741c074421148141c030030352011011880300300203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 865993588 1250 865992338 865992341
    0x20d110705210309030d020903212a0a110a0e0c1305102709060f0608070206012102120d020c03120c0c040f060806161d31020c030d 58
    0x10100000c182c2e50550070300380c5911343d41e40a41881220384035000705d00e0b0302154404000c03801c3c402032081d030510030070f4140c640c10032040c0d4080000102c1039040c480340c04052840303100d26031094000c40d40c014a9030703c02988481c150131071040007440d4000d28000000980705602c5001070302030340c1941201a994000410207180301c0405074480b900864202803090f20701a0824410f9240318550717010485000b980003016002d40c05d098001c4180701d85422004074a5410111000d81906e02c10f403188002c1e13403100041030382d60301e80920800040820030824031b10114a0041107410b03291002c1c04265850241c3c0343c80a013040c40860407000142d0011a4112051070104640e1440c3c030391842d011468504050b490a8542c4103a0209a01560303c80f004e80c1d600c4e01255126400418484041c1c407024140381c91281c015440010b1280b0000d04030361382c044140792100070004051030700140510078444610082004210724054106407c817100c000341d00091103640020031044e01020051030343d90060100000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 865994838 1250 865993588 865993633
    0x60b0d091703041b171c1e020307060f02121305011e0506030c01140d02032e17030a050a0804050c0a290a0c02011209021905130507080604020d110705 66
    0x70400e00d9070550718000c05401040c80714010360095082c0080d1082d0b500240c86079800b120541c03110301e2031f841c515058103034084003800c040e91051106100c00e400c203181e800e050703004010f41c0034146600380e40440c0c0203031f00c000906040e191103440041808800412014514140d10385114089900c46080001d5864140015038022000f424208480c50b13243c0c3c00d408041c043c240d03103101880d07800400300c2c1c24650302010390100d80f0001250b10a00d10340e1140040b070499407522130000e04000b05403000b0000c003008820b6880c029240d60301c850801c840010211410380c0050402c0d40c107030003404020035040d12040c83e031001414520708181030001c0c1c07003440005d0341000301030a4a41403100b44801c10308076a2000203100050b4092a00f1a004622507032500002d000800d0000d502101a4080000500d516421541151011101c4207954100240000b090741d50031a0418001480400095914540341c0e0280c200d001505800260801031102280d226a001c100d040d06c00394000d20b0140030380ca40060048 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 865996088 1250 865994838 865994849
    0xc0c0402040306060806240d110a0b091009050315073b01091a0c03120f040c0803120703050a06090608151b04030f0602190c15060b0d091703041b 64
    0x1442440044c0608140c2414103211841551000031050901411a80700d8440003002040c0f03d00544d900c0cbc0e944c2c0005d600c01707410107002c3c0d2120300010300014041c800c98021550040e000c2c00416070f0159150b880c0c80d100a051400b170000b1010307600101103900c0c1a240c14030310094280001c04020402d0034104840380c40d0014100540c9400503c901410b0300c444610801a81c001581c032180c80403d528214007810420071081c004040030807107480800c8990501607070007485182807150302c500d000e586a203c0ca9541c048a01010313030214001034800ea0242c0c0e40074401000c00104641c41c3c219504c19036107660b202d45003580c440000d42d11700c02d07208909150044044410020f218400c86561051802603200140c136541d406d114100500c940d07501120060f40e100a04042d0400c0c142c1005030842003c15000c3d070b15101400d10395401c3c8100c40c81000300b0b5504601c00242403802d0034a2034405802c0001084410402c4944d40f0613107040d083c0c02450240313100701c080c041e00c20002d058504944100f81e119 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 865997338 1250 865996088 865996111
    0x70318151a06070609030c02031621081207110106030506150a06091703041502030a0305010b13090e07080a0b090d0f080c16020603010f0f0b130b0c0c0402040306060806 74
    0x50000301d0b41c0300e40440b20300582c04040802c1c0348403641800e440003212100003940601445652564070840312585005541004200316003000e107001d000110300148180c01040d5034020424500d02d880700c0c903851a4002454076003092145481c6055500f5240e95500072107680e44000107001591a81d0100c0c01c0c0f010405981c0351035885d10b00381000b021551a441032800501884d840b0300310544c0d00784100c0740a82410744104000200c5000001e50301c0c0e000d0754506000034230741000400d2105040303045501200c044415018514108100b00d0002c01c404425968140304481000444410611520020b240224422003440c9008002e050600b8520110f500400440490090b03c0d01d8014001c3d9402c1120300328500e0b12410b040c140e0048161751050081e40c00040840005078081507002030005459040d1065090159156030750421406080c05846505001e04014803452400d600a40010001003080b6a42c1400d060b000c0707000c82c5d000782c105542458441c241031002d800100b0109800034000c140707 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 865998588 1250 865997338 865997381
    0xd0504240b2b020a0f061101020705150406090206030f0f1510050a030219020f0f12040308030a1d01050621030f130e041101031803120b0604051801080c010503010f0b0307031815 78
    0x84103911544104ce913814025200801b007401e1000d9503000b00210303a405496076550f03007080c41464000364400c0321a840089009400610306c0403144043d54881c8001511500202551010548181d0062110001050340c24425150784080f811049038400040da00580381800b074440040d03044c8440c110700d00f0340301c0d40038280c40d4500803c5442200d0440c1d41100c00981c40c1d45500b180c04010340301c101c007081104002800802c1e824041980b105001c0c803007caa481d03240c0c05003c112011584095080151180c000341b0405140300c0c3c0110051249070040d049001515807200d5044c03070071b881c041d035003941c1c6e00c0c0308160320a101d96014812000c5964104802460b29403440d50018082e901001c410304485440d0480060702e610713050107036800f8100051000c41e0341200b110000321280000d01c90310f200e6100728444200154050011a81a601a100d40e80195400c0040c81d0000b50700140410341015038982095031140d00400c2922003181c452188402e000d00d084900d041070f10042c51000b4070f031070f96148 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 865999838 1250 865998588 865998593
    0x60d0f0e1e0c041a031c091a030609040501060510020f07091a040b1c060e070911030a18170d06050a0b0702010c080d0504240b2b020a0f0611010207 65
    0x82c00d0064481c04a0340401c02142c8140380b4030410f0340f1a000e20b6010b1044030f8120081c15840f091414040d10306a0300c0c0e440c0070ba5030364003407142224560b28045626500300041941810300b0b2a010758440d000310000f094059440d0301003900f06154540311030050704903014121403000c0a01c60b80000f004985018055100288500d50304c28140800b29445aa0f44080c81021030b12142c084149082c880c19640d129581d207130030040302030000441581040d028908001c00c2660544c8101802d0f500802040303800c55903054a404014541c81c18440c2d4400324003040c02c0001002954502c1c001302c42490b4540c3c84c0c1d4a5101040181c4034290000d51084100e850309110403200c0c0c10075105c00d1030302441e14103000b42c06c504042c0214403450038810b0b103c0b4200020401400940c05d101c413009101c5e12115003140c400312403240704480e604a1219880202e0500b9124a84c072004c2c02c007248100c02181c801c1500d882980000c2d109030065201c80310100390840300f0060150410040000511424025490140c503035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 866001088 1250 865999838 865999843
    0xa120503040201081302040f330b120a0b2101051806070c0305190f0f03050615071e030801050a0b0f07300201090213090f030e060d0f0e1e 61
    0x1000c0d904084003d5543d0000e547e9180c001803d10b181d010801c2101074110f024540410b5424a0a604110440c203c80c4400b40080d8103500300b266000c005107418100000000034071110054400303c402d544a400c11406075a07202100e50074846135541821102c030340e2080c402d0966000501c49481c071000112800b0004e80d006c1001d41d032207001071500b807001503250301d02505c3c00c1c025250f0341038230000c04160002040e030308660b031411041340c0c640f0fa0060120131094110250b503002c1315010f4001d01c1c4c07108404600b0704c00b00040c000e00c91060860b13000802a00740c148035022000c010603000a600c8100400840c2032003050030019110b0005560319202600d0050f02040c894000c0c01040a503240c400e10a0801552040856815200712591489902c04a00901800301504140e11580585000c11040c896a21800c1c20ba20b9010010010728800781d00d05449040e20b0a2409030826010400c40c80c0a601e43c3c440c00d001c3c2a9070030400500180c000c0d890502d05000010311406a4140171081c041d00c2000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 866002338 1250 866001088 866001091
    0x30f1021020f04020d0608030301170601060c030c0623040213020c0a020f0102011413050c0108071d0411042c2a09040c2c100e0418050a12050304020108 67
    0x55410945012151003c01d00034070a01c00040211498884085030003500800150b0490304100304020102d01c0140741641c46000a10809010541c5003d02c440041c4c00b480000c6001313401a10001040124440c20410216082e8a895404100d8000300130840c94040601038030000d4680c41182400306100219903942c5500001a04c03406030040c032606144e200750400d0042d0740030200c001100d0b00300841000c2c442000000116201c0c007035032241c1031003540300e07130034652183d8100d03601e00c00360148000c542124408009001d54100361940280345284010f00014001006100d100d07407424104a00e40c040307441c02003240f4500c00181c0c081408a81c0108849000e1004201000c50f044d1103202400a201c0c1e01c54551941e4025080680807070754143c0012190002c0c1e0486000f5101d100600d020344041d65603500107043d0b028000c400b000011600c1407010101c00b84003d440000c034019541c2c07039041d9125640108807030075480303035004808019020305058003046960404604600f0a80c3c00078041c03035030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 866003588 1250 866002338 866002343
    0x80f1b180109080705130e07081e060114010507060203100b040b09030f0703230a020301110705060619151404080304031203020702030705060d18140c0102060f15030f03030f1021 78
    0x107d4074210351050905100110017008050201d900c44003002403101090000411070050501640d400050034641c2000c0f40360805405035a9a480c0040310354a500007034001420039101854244004681030b0091001800a058580540750300c030078080b003c2515045098501c0c00c038503082000c003000050100410703000d111050580411401030f0002195203054810400694590300b0504c41c032500900303420041000c0c038060400c1c0c5880d6502c403403d000d130409002d6103280c98013201c204200318041083e0800c59191550f4644050381461284402d105604280c000341d4036a0000039040080081c9041090800701c1c06040960400c0d405030000ba4403081d4521902c0d0080c480003a41c003600c0c03612030b03102d40340d2241d8250001d600c01c0d85500341130742c034140c121085030103074481c0d4101d07480b00d9030002070150300c921100401204907907980c1200046000741034500316014411104251810355060020303500c20440d042c0214014070b804929141804e20360380c891042009418504c10600800315410400c454 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 866004838 1250 866003588 866003591
    0xc05060c3a0c021002040f091b2a022214040c09020f04050402071b1a091011060403030b0f040e150c0d06030b06030d030c080f1b18010908070513 64
    0x890000580c00c2c040038850301c001382440024081100d20b02c15405034250350128008011000c41c0002c41c02514a04500820200c0c0c100d208411305045076900c0c0b000844150f04c41d440350f4100c282d0100d5212042290f04090074544c0c481081c03180c89281c41a0305c0f810082d850416103031700381912004805182070244418503030700020203010300b8004c0001c940050401030000c564840c41405c086030b02d103e005681c030b081a10030706400240083c4c105160b070800d091408005140488031002c021100c00560003070400c1c00001400207003c0c140a000a0f48514044d88005c51201c18800401c08a8030840c04c0e01c030300c9580344c103800700025034000500c5850b070301c0640100d03001520340c0200441580241010012014100503001c001c105500016a002d5003058080b188000d402000c154152118190682c0001c0c48540002d00c1040454502c0c0d60010043d854403008200c824015411035400322070f90f4082da0258000301903507540d0013142600100071580190a4032414040080e142942c840400120705 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 866006088 1250 866004838 866004851
    0x30b150d0b0c03042d060b010206010620010e0d09060201050f0403080115120f060602010b0d020906010f121811040c050a0320130f0b09030307060c0c05060c3a 70
    0x1094200044800b50071107405c10071a03580d81c4078022440345044084070020b040c03200340c0105500000748141a14515103270218813240d11140b40703004410248103003809649842910030741036400d2080210a9500396103c890701402d026000c2d0a40b81c0281c07516803910360b01d01c2000040380e0b00101d501e046d20082120a2220480c05038100c40002000348805410f610b40340300ca40d00000c0681c00002100d4154000b80320b00043d05c02001206610034138081d4000e407601000511562240303c80d410303404d01b10b08240c0030030080894088111081095110a4051902000e030203200c090031106150f00011141030110382100000246135000c3c1d0b400d014149900e9180c510350780603410703103661038800b07000300329907156000d5041d5412000e906115400d10b200c070100c1c021807075061034000c503091100c010380150f00c0c1c074846940715801000038440f068200402c3c00000c000140f0244501c83c0a59544d1201e5900e440a1000072403082c00d03030728446640c40402c0800050203002480300703504403070700794000066074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 866007194 1106 866006088 866006093
    0x62202060906030606120405030403020a091811120303040b0105010305100b04031b0302060a020c1c110d0215030109050901140c12041704030b150d0b0c0304 69
    0x410300c104201c0519041a0005540141015200920308031603100400180c5105440454030394000040410540c580020510042d100d0b0b6142080710b070380d6881903000040c04940004054405a03000030f4441c0da40c004070001c442014106507696403800c2c0c03900040420090042078086403400300803415880250000a00341d51000707040e00d161506644038031079060004501c21b03001050030400400140c0750140948404440d9030010308904010f02c040250320514116a4646150680360b0b080c00710f802460020411070090b10078800180c1d80d07001180c00200c906101134520040000006090307803465101c01d2240e882c0800030020b403000039900040c80d45083d00c0301c1c1750902003031141d1070b081401a9081030700a8400e049000f482825103c0c2c0c030311380d6001980140d030301b107001108102e25500030507014500c11008a42c104c201d0101603030307035508641700544134000022010002408 = true := by decide +kernel

theorem cover : BRFrame.Cov 865827338 866007194 := by
  have h0 := BRFrame.cov_init 865827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 865827338 ≤ n) (h2 : n < 866007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
