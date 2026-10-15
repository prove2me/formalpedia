-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4584
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:05:23.21232+00:00
-- url     : https://prove2.me/submissions/adf6efbe-8f8b-453b-ba77-be4dc6cd8dd2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 824280575 ≤ n < 824460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 824281825 1250 824280575 824280637
    0x924320706061d0c0412110415060e150405040b120d080703050601030c021b04060b0d0203070f17060f0604150306080d020706080109180512070c0f24111b120102 71
    0x8a01404918458807c1d10b00400d0031500c42c40180070009403c41c9040240e2a40201040000310044e140310242c082d0b024000300c01ca01075401014851500ca50380300289881d0445a100f0750000103007210303a12808a500600f8518003500c0a0300000d04000010360654024095400180011303402480c0183c0841410000741640006c0f4551050b228100020660303044000340c41e803a50303411001070ba00d0800c01c00183c030400001c2158000c0c4500203580181c81d0884250701a4419000c0c2c901b0440740d007410000407014441d81e0410751b5543c500d140a031404039810391004055034441e0048034000c1101c0c1000340c0c2d5884d801d110700c000041c04440180095015500000d0300200c0b0075440944044d9240d075540d0402c0d460035290036940c1070224152007032084003907001008003401c501540c45607040c50a01104402d078020014a50500109112040b612446134034800c44000720503030b9110701200d40c0d2160120620250548904400005000c0502d4184202c0b41c2e2101c020500040c0990990218014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 824283075 1250 824281825 824281859
    0x5010b130e06131211011b0e19030f030804081b0a0203100629120702100605060313020423130302100c020c010f020316030924320706061d0c04 63
    0x42d500c07008628000355a80c1f04081040c0c440383c0700c070100544c0d00390074004014070100c83e0704c4c50b0b0f819189040000c101030489402110313400d8070303200000b41d4071070800d1076a5100b090460a180d54120201042880d03002c2664001503108900755020400400150700039030700f1900880b4041500c0000c9154411030381e26a1000c1800075a004a061524000c18140c102404803080405a0803640400c2110320003841030601078036040340d8143c00c5081c41c40901c4822100d008000b8000c9545950006800e811a00266001002056880701514182400004040c2c6e030010031805403190382010302c4900c00d1801206490b8290b94020a191039001c0011902e022101c80181c0a6000401a400f445098284d8807502507010b034a51410480c50031b0b84050310b00041c00b00c49203007005940c150300000c03580001042d460450b40880a800001000040140500c031060854402000000c07800304018440d0094021502c0c404140400d614001192185541c4215015044500104420711108001c4030740080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 824284325 1250 824283075 824283107
    0x60106180b070c1806030b060d0320010f0b0402070b0c091302030703020306010e030f060601031a120c0f0d0807020907030f1a2d060705010b130e061312 67
    0xd0895540d0146107559111000c1610340401c56081405000003448008201c0c24601d00100300e5640786494a500b40c02002c0d040a10131105034900200741441174110f002802c1d100c448241191501c074000500815500d031241d8030060078030040203564035051098640854000c4000c100503942c4a452a4450740050519540005000314005212005101651207404141c500580e28100000050100410003100074480c2d072001d0841d40e03200c103010805c01d4002d20203003008141143c440c0140f00d0318005241c51580c1200e43d00000f052180c0d0000f4918079503210a6880200c4410480c042c00890001e0072005016098100710040050402c1004c0710307403140703c030301d80010440c2d1101c03100c00c00c0d00c08240c030a00c0b202050f42c4903600da40c5003107583c4414002200c80d54402e05884070038034900107103127102031520401c07002c40c0308424890203420510141d00000d00b246840125040048010850300003072108501c643c0700000c0e00740071014001001c1c03a8001c103102c00c0100c0e4000e0221110b4a484003859 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 824285575 1250 824284325 824284367
    0x50c0604120c0b071805041e0c110a0818040507091716171b0120150403090306051506030a150f090c110c0607020d03090302060d060e070c05060106 65
    0x120100d0a41d00703a00b0f0080006648007002142a08001640e85c0301c1604450702c59803815030004100c0d02da8460340d514641404001040340340000c80c065070402c2458080c2034040c01181025020019000004d00324461040300001800d107154040c042203405c1124030b030380481d00c1c000040c45036480502d290402e0301d095000f201d03a120801d1050080103107250b440800403401800c03d01080800900881c0011140f20120800030003440c400200305c0c452400c0b0701445d40100411403003034003009010f000c1c07100c040041714903900d040a18004003400e171180710649101e8506000f1460000c4400101040004010001811500ca10b1742000080031461141101501e480300000f4003c0c0101902c4801040b00c1e1000080f0702c8a2450003600442c149034040515400000d03148019603a15415102c0380d1380c065842c11680d20701850241c95550b0103410103036021002207180c01c400319241d0414001d03968500f00640321600c40c24002e442c1c05c40c0705400148560018001400703818801c8441d00b648007000503880c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 824286825 1250 824285575 824285597
    0xf060f0516060c080702100c0e0d05151f0603111209010e0601090c030b030f030a03020304052b110d1d0d08030a0c090e07090303121b020a0b07050c060412 68
    0xb030700407624414400310104840d18104070702c00c0c0e01800f00300c0480300854000e0002d8040c0d4540206011541403800d8400c41070101c4400601c401006400d0a900b48546912443c1c144596a00002c1c0460b0070b50b03060052000b5408034000b40301c0d00513a43c03d512440021803c1c10b1440e031522a8518004200040d00e40d81da40c40c0b044181c10030001d280c001d00c14448002841807402d10010256140300c0f814034002c2e4031060405c80308001c000105e0b020002c0038600182c07213490700d180480c00d26900740f220160024492004514001c2009040d0214198948070072101d6030b00c40404a845860410000010034803203020032000e400140c0601c2ca442e40002c0c01c03c000e2074003030790b100f8001340c00030340d41103c0d116174804c210f10f0f200d6040391015020300302401c2c150400d4941440028075603001804003c0400c018000304130000707802600070f00e81b0304501c001001d50038190b80200a550314080142a115039590340007140c0c2d41409074080f00c2d109130b60007000e0900c40d6140e499a03080203032030189402c1006a03240314 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 824288075 1250 824286825 824286833
    0x30406020d050a09020a0b04050603040f080403050706080627270706030b15040503031c1805030703090b040f050402030411060f04090c021b042309160f060f0516 71
    0x42c1c92041885107800101850741d4018056048026040400c03441820001444140d80303207000d4135840390b4080c042030039074103903858010550b0007a03070300c010000c3c0b00f0600e010814942003050710348981b100390741c04403a100030320a802110208580f00e07041d0410840011501106400e001042c401c01000c00420405071440507441c50881103500280c0080d9407060203195529210131f052500064201d07e050900e03081000190b26846900305150342c490744c6010b001080e059903004002d003030001c440a103280c4455070410a44030390010030f0440003c0c00e00d0740e000c64280f00e0306060305c00f610f001886c2c141209042206000c025132000e042951100f03828000043d0540c0e40200401c05100d1500140b9211032404110005540e0206448015504100c8203203c0610000d000015102c4007100d001c18a200081d400c00300344600340c010040c100700c0709010404035280009404070201010034904543329a55020710460107481d00960002514107204000c03454480c4d000b03011065109050740d54980300d56aa = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 824289325 1250 824288075 824288081
    0x1104051804061e151203020606060d09020d030512060405010e07140d0609143103050c0f0105060114070203250b0c07150c020f06031e01030501090b0717010b030406020d 74
    0x941403902d5500c60400c4113883c059a001140109500a050a8040d2059030069201c040040a0303a00601d4007040300c1060f0344881c1c0000d0240d54014160908070691810000e103e640901038880305045104081440d0342051b1090a0480e0052041d0100c1a100d00034101d03a0030860010742008030300f05101c500390400c018070882c80200100180041c0745e40748a8107080440d00b000305140142d08040f00c4034041b201c02d07812101034a0050b901d204408944502d81034030340340955500984035100e91008203100c69015800300d401014262103160341c0d0300703a5046001c000d12441c000290035400148803043c80b105503102028283c00801112101e403038950981080c01d4000f482660340590242e2410000c0011007501c61000305002d00c1c0043c020070300c940115a4542480340d01f180203800c00400291804290800040d807185041440141d0b941c2d607041040c00b0740000c040a030748580e1820b002c81c07020341c05141b038100041100d421040783c50386048118422a00010b00907200c068003001040d2428840d84 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 824290575 1250 824289325 824289371
    0x1020c0f0307020405010b1e0912060f1902070f062a02060708060108091902040f020c010912020f0d0309030e090405010f0501090e03040e04080d050f0a110405180406 73
    0x200c000d5440b03208600410040c0c0d00d060f807200b414540d08204881002010f0119505d14045469144c4c0c1c1ea0b01482010071502069a0800c0b51140030700c000f44840307496544405d5001da1102010024407102440010040740701c1c255009000655011005001400340e421a108402681c0300380410082d40502000b018083e442c50000117800040412440581140880e178103e43c0a00c0c3c602c90350718140a29a41d40c1526030030702060080011f0701602159140c1e040000c0400302100c2c150345500e0f0742c040581c080e140c001401c03102c10f0b44840f000c1c9146440059a01c0051801400618007403900c000240d0040c03603200710031b42c100070f81489030b14440e45501d420980514401c00000400c11060801c200c21038a060304484c424600302a0031a4200a00206650a40f04541c12800145d1202c2c5840c55141c899001c4a006a41c184000c010854100ca10a244074114850061100003402c418560207403040340104c3d80d01243c2140d2401803100861a01d40c0d02c203101c0c590005d40c400c65118030f0a00c4001c6a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 824291825 1250 824290575 824290603
    0x1a0d0201230712021b0d2429090609220203030a052722090c0801050f0c0301080a0b040201051c0b030c03122506090f030809030a0f1101020c 62
    0x2084806840d4104401c3c00003e40741d119240c10000e40400080c00101c0840780a01443c40e010780000c408401c00400c407c4904c000030041200d0010f042c038020500742d2041252000548410031928a0b0525980240c420b100091804645940750410805400d48842600700221305042c18000140c40c204014410300d00d40e911000e440b078800702103030390000001d03080100135400d100c41c40c4000c035203030030000c2d252503803040e03108440044001c8100001401003401c050900c01078003000040c210010340c451030040c60001845221980c4071040f52030b00344001c3c407410000d544400107030310108004a6000da0400e205241940c40c211079544007091414a4034500002e85a880c004500f007450b0401130a011400c0a501800d01c04805038104445030154040550784000c80c1d0514000030070740c140404601c0c6500030410010031000d410010782c00105113000302e02040c0c1400100714401c00c0041541c8512100b90b50344a005d07060b540e8112440703042c12401c401039640900000200880511840780c0724954 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 824293075 1250 824291825 824291843
    0x602040b1206010e10030507020f16031b140103090201030209040504110109050f090402040b0a08030712030c1407020114090a24030209030607141911011a0d02012307 73
    0x211103000040e09101a10841c14004c41c0a040740386a102d021090812481d50700f030000741ca55403c6810390401d421500c000b05640a03010813045a10403100e2001c090700d0080043e2415031042200341208040e00d8018042d19400e0100308995035881303500b0040c013152061601506010700c0001103400e442c0103480864810b280d862505840e942d105843c540107007400c41c0c5c0240003800804c04038101039400340010b4000c6481c1d645404580d150301900c100200340c82c100701daa03299100e0400380b41c84402d0201300e40c00a41040c41003001140710320051141c1c00070740764040c0d18282195005660120050801c91503c0700c05000c500f80e40d0780d07000c6480000b001043c010880202420144c440c0308000c0c032a4190a151040c44407034450344000542c01c0d846241d0303080080400d40c0129001c5154003407402080b0403a803000818140a0ba4070030100400301249000a100c060b00e820311803000070110b2809150402c1552000801540c42100c0c044d00316441042d4039400c2d44480c0613050501d13800040290b46410b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 824294325 1250 824293075 824293087
    0x16050a0b0d1116050120070206090301140405071409040b010b18030708030403230304180b101d0a081b04060b2b110708251101031103310602040b 64
    0xd804c0c0602d0400120b003c06c05070001000d03035010354281c018900080c3c043c0c803010950b40c00350b4800750b0140c82400d41000510345030b80b80c0707403078503540d18000c84c061084403480c0c2c50000e04160419900d03180c019036220000203110b03030800c1c10440c0d2540081e08074201110b02501d04810701e4a0610180e00a00500030246507241d081d0300b8142c68228507070307124203500b60702c0c1c44904110340008015581a196820408119012221110720280108c00c1e291944103040d16a40d8002541024000030303848901000741003102444070401c10103603054855070200d0b4022300d02c0028884484c481070b5030782000040002540302c0d200c0703200c24002d407c8500340300259084030411010364042160715036442041003c040c4044407000b500d10b5100d0003402c030024200640452a400790100f60f20402602d00410822402c4100c800d00340040782c4030b281500507005c6450240710b00c1081102d081102d214101802c04184140c0343c4032000d8031001024141c41110461a040410024115000420040c541060320588401c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 824295575 1250 824294325 824294333
    0x61f1206060203070f03030509031201080a0c0e102606010b131208040b0a031d1518300a0203030a0b010527060906160516050a0b0d1116 60
    0x81103500100190f40c000d00210700005c0b41220a800c0107641032401080c0c51700c41030b040c0d03031039402901940c0805c221100000300b01c4007030001d60a42264011034200880302d030b45002e400103036181660b102c40100d00011090050040d1039148101d130340380c4000c821000c140384560142c14607a080e0800c121202e00010510442124002001d02800b0f030b0102c83c8071882510b03542d0f13112601c070b58442c3c2e070106003001c280c1e8400720f4060707840140000d44a6190450707080401000035213030241d0b03610f142902102240419446840281c40d22250100c0e40c2c010315050311060013401400043c0c0c0da1a0440c561015055117007010900e019044a46441d001551a030a01040c0c140640740031100d20350411106002e012440300528010030100d95280710400d07412030a450106181d44200b030500d03a0406400100c210f803041402c010714880d6806002911443e0000d683c10b58000d00c124801d15078030510320401400392401c12802001e00c00c84c1440b00146c1a43e40c520714015540000b0340030142a030007079108034140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 824296825 1250 824295575 824295581
    0x601030c05060f030a1518020c210403030c021c0f031e080c0901230d0b030102070210051303050106030326010b030c1309090b010513020c060f061f12 66
    0x103040100d580e035040010f00e22107000d0f9404014000f080c11500c0c1d0340f174000900c0703040541d1000341540c410700d001c541056426001c00380d03101c99002d1880d442400803440d00420b86482d5034004550070345880c0d161510310f44003154008440401030303a01c45c00300c1000c03c05144803050407000481c807508024000440e00c2c2000b50012004c0b0103601515030b4030080071600a540910440d80c405415518240c0702c00902e001240c0940440741460014003941304c40c1004168240060180c2428010043c41100c1514041c1404d034000c500340250403c0d807400a04018602840c06020054611211f04401a40c0c0b501e5441c259260f07640280d02140e62403140390254010891410715294080210f1000c551404188582a120042c500e241100b07001c50755514405201041d00001c0641600c28402019941070000c1120820b105d0103200340413468000c6803100e250700030380f20001940780150443c1da8510855642000c0010601580300c15103000e001e1900c4241c0903c0014003a241e80c81c03425001003000c5000c11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 824298075 1250 824296825 824296829
    0x15051c0903020d170a181208060a08010b031009030c06140106031d0a080c03210106021606091806080f060703060603060e0a0c030605061c050604050112060b0111030c0601030c 77
    0x104013090340551480e21084240c10340004d00c6a0000401e01049040030703243c804000001890b107000d281d1150940c07030f80b001c401d43c01550119441c2214640c2d4500d42400c0342c020f4803250360141c000c8101c0b00e107450210780c00400d00034005d007011400d0400c0c1e0394541003194040350032010143d9006006022003a8948190305103c000d0031845d600301505450304c950303114022403004003c0704001651903a0f03140248107442d150a4501e0340c09800340640300231400c8000c0c09005030001403040840c40442c640c2050401e40c111079190301c80d00744d100d00b80002c1c048100710080f006c5500350703215003001076106001c01946090003104405440d25091212004054803800d0b80328804050030940c0921043d81502090b9801102c900700c005080320340080c064020b842194441c0d40c4c061000704240c1d031200303c022855020040320407401c1050390390700b42c10081220300078025510102c4200300f02da400500240d10560764801c050600d051510814180d0030310b560703c0b0700c0c604106500102d004000f00308a610002d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 824299325 1250 824298075 824298077
    0x70c090f0b010e03031b0313080f0c150a1101151d28051e0903040e0a060f0b090d02090705120a0204060c0b13020303041d0f060a15051c0903020d 64
    0x5100c070700200060ba40c1d0090100c0543d1502c0040780c0741506c008100100c03100340c4801e0b40c0080e40c103991820f030f840e01e6428003101c055482c00b80d080600700314070300380d0f148032070707140300120002c2c01c152407504112140070701041d690b0762640d662608003030b0509541000c01c00500d9461001c094064110004d0030035181c0c0900841740c0c4188203104801c5001020341011900c200000d400a01e50b601c034501000000016888918800106020301c118408040020015555503a8100e0050b450f10040c01046a1561107207241c40e0644030414014510f041d001442d94560042038480c01c50001d40001c1c20085c8180c8a030004180001002d101c642c0e88001859405600888114101850480c0c00b4114850a4030020f024020240005a152034030f0326622900d50740240c103ca456548900704202d401211401d11400030749548005036883c4d0301c0001040c030070320001d03240c122b4403468165503248908911204105100c030610030041190070250164080b40c6440e00081540c20319424040d04014450039800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 824300575 1250 824299325 824299337
    0x30c010207060b041a03060c16020a0e040311030307020c010f17010b0a0e030319082503020d0e0a020a0303031a032a0a140d06182003190b070203070c090f0b01 70
    0x103d680c6c0d004aa00c583c01615036044035a03c02c2c0707038948405519940c03040250310a400721070115410015141a0f807085101351a15402182201d683c95a0b82c08112505170059000c4108140c203548912a9240c1d04061801c1584d81c3e041da801c0618903a0070242c001081500001c03803c0681143d211801d80d00c0d0f07080c2038020703504c1c00c4180551100c5402c0701802174002c1c03118241c04100c504000ca4008800e04440504411102e00f000400034080d500040310039a5035818510303041e603400070114644011581c0104860400c40ca0740d0340543c0034022446d0400e50b01410700710b080005407002e000389840201e900b0111510b00700c02041e20080b401800c2c200c0350084060b60020700500841d14440c051705101103850780d40400152400d00d0141c1100b24801c1120307511070003980d080007003601c80d040080e144010fa00f0100344d900d20034903030396584811104020001c051001300100c0c00c80428585c2146003807058034a0004c01d40c540031034102c0180c2c0541d00c000d5440c103000c2e080d2401071140740846502440e10f6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 824301825 1250 824300575 824300621
    0x9061501030c091202010c05030a09090f020406022e0c02030d110406020a060b0a1a090a0504290a1d070206060a120303181b0911030402060714030c010207060b04 71
    0x4003003e489001d0b03044492000980c0c041503a000c1c002e12075245600808803a62284081c100a08880d00e52003080c0c0b40e5800c00d07010f20b410504074003c1c0e50680d54158010046111151550300c0c441101c00f0110580902511441e080c50401e8010302e07458240c19001142e0300c900d09401e00c0c0c2101c00301c200c171034803100e000d000502050341e010420b055181e801500100f11782030101d0008070988000ea008181156007076910041d490044005800111012502100a5075070b410502c000c1e00d030121460001002c0f821080340321100401c0341443c041c0c00150034180f125071611a01a0300880723610004442d1607a69040200d0241c3c1046015800481176809100d1545058030701040c0801d808401014107884204908000c600b08848450054000c40800022581042c1c0000344041900a0600950400d840001c502c1824800c990150798040c1c4850b10f04031007515034003489102285d900340c040c00b0820440c0c000c90300900150140c2d03401013a0005101c0f0180c02040104ea820300d54505c0090580200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 824303075 1250 824301825 824301827
    0x1a0303040605040620060f0403170f07170f0628031b09090c0b030703180309050f0d0206090f0a031506090b010e0a0e06010e3601030c030f060e0609061501030c 70
    0xb003500400d142407407c502d611146026078103948071200c01c00c130341c981a004001e64800480d918502402c5541c03210040a42c403a507032201c0f007400483c0d00d03500075011100410010704000c404510024026080c0c01340c0c0f100900292200d110480d803007642c0c10b046080b01000e00030a1a00513400901c0791400402040f501691100034110451040c60080c810100004540c1806604101c02d040c0204400c16201045c500c5e002d041049540100d82c080e00d5820b00d460410309102a0a048058005002900b400700741410481050719032040580c008841700b0300000040d05001042079071360b820100102c1c0035810000d889040b6042486854100004103000c604291104a88101a220b0f00c8500e44015501c05006030b079a515041000c640085190381800b80c00400c1c140c00403905121110350342c0c40180c0c1001a4035000710b007800f02401c0540c8520040000030140756446032001d00c111004200043c55060203401c010085845101365000174042103a0a030340004106030121003400d0401c210016a00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 824304325 1250 824303075 824303083
    0x9040e0f10020307050904150801051e011502070e01091407080f070e0102120a09080c04020c1f0b0409080a0201111c0e0c0d0305130b0708030a1a0303040605040620 72
    0x120320720040764000040303015284200f003200e0860101500c1440901c6400140e561250035031310810500394039101c0890b000480780c201e260354102107155071aa00382d0130550350b000041e40500c404400d520034502c0004d00b40001d444c283d0700038158040c00103a9214510b080300d8080710020318050411841c10200450790f80180d06080e002005031510b0000e00c01910010b0386800f40b1604010302c03241001c0b880000e942d03400500351083d101000f050b509005c42c1401032005900170f04c030b00720b0950707000030f00710704805070300640300407054402c0c19004a004460f05000c18201c4090b01c005440c801d00c001142002140c0901070303a4441c0c80041c00c80342c54100300b1890404244422041901d103141c0f03c2011070024007003000020007a01c0c0c004c005250380750781032401404950104410308865549000001841c08040e01601c0e0100e411039032503032850b40c82121040c014809040b602003140c4d4038031522015a10108080e2002c1c222a80b50a5500c0c2c1c04c00d44050240c20400503106c4181444004890022030301103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 824305575 1250 824304325 824304343
    0x12050601080c1606050c13050a0b030c0a03060902040b0a0f081009020f04030204050f040b1b0a05160c0305010c18050303040b0c0f0607030c1103071a060f0904060209040e0f 76
    0x400b46601c0d209007411001440703c4010026002c035080074103111500341541c004003400240034107500c1e155603652013400300c003035102d01c10541100390a000041082e01c10780d00400703a01c13903a840d0000c1d156460712004402c03030b08503400c0801000004143c0700c0c042c075040340780100b0201107401d029946291618400310b0b001e825000700c2d2203071900400c0702c09040c404601030314043c41d40244140071914007403011b001040012201078034460b91140100e43c00d940114034007240340810700403aa180c02030040c4140c03560741c070640700191113019081000380460340e0100100c000c0c52051001003580c000c00da200905000c0700043c8030003031810551382000165070000464049508188036076403109201100710342043c00203000150305000b030008200527941d041d80b201d40211713204d07114625030340884401e15030341c1e014200d0010002410607180754080e080c0d00b1865507001072300500c42c04a10400e00c0110799411410b03036045445a80114080201d4901802420114500c0e400103006c0300801210313545c4d48003040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 824306825 1250 824305575 824305591
    0x16140906100c1a0604060e360a03110f030c1b0303040b070b011809050606041d0a0c081b1c020a05040513210c08090a1a03071205060108 60
    0xd011041c802600500c40940510f030804035228041e0007400c0c0342c500071034049034514800c915190380410601c2d20011420b01a40c411424106c48100480f801c91861621140850203244200321046031808100000b042551090780d40400c0006a451410302d4084402d182d12040d030020700ca0820007800c0010007500c1200f40f091039480115000c00441e00b10300c07554109858840e00041d440050260858665040712400c44507483c003160740412681c11980c3c2c0c04001491a041800812058580381d0085819900034042043c40200e10360740323141c03400e030400400b1551481d40c5041000148410303c041711419500c11040f25034844e400c0300049003031210403c05240c0c083c260101c5c2d0103540b12412828064100a0400c000b1410a10f41c1c0401601681e0021125582c416001c4880d040d4014001d5080290320f407540c602032521540c843c041c82e0403440d440d40d00900c198000007040041801030900320102d08003055078900b0701601c014042040d0307104100e02103050030305201659038032600301a0300c5006 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 824308075 1250 824306825 824306839
    0x70302010e0f2d120705061b04050603091203070c0c1505042105030711030c0103091e050316060516030903020304062708010605041802090106030c050c010e16140906 73
    0x282e024074520010104010103d101d031381911070488a115006207240f038050b01c22941c03140d40f004061240c0c0d0b10602d40ba200746182c10b020401490502402850b003180540382a40c960700d01601d0780c0d0600d504111040c200040214240106100440d07840e000034100030354500c004024241030162642c8100c1c03081580c001d00f04444a4071207000000c041c41c6055121040c0c1c2e0380c4a180d4200031002d0742140c0704881c03080c01ba500300b40344158081d102c0e495002e42c2c00806000b511301598008110045007400a5509002c2006051000800c80e003214008522036800051182802596071007120107004070f58041c14680141c00e4003203500002035908a0b15185000c00d0300c0c2d000389500d2481ba143c0900b0210816180b001c022507207803c190010742c10342c3c0c01901c040280f000309114031949811000300203034004003514014000c080c840d400c0094100c809040081c601940401e60350f003156100b40c2c4440d081e400072444074111200c0300403040d0040c41c03646200700c1003aa400740024510f8030082c00a42c40303110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 824309325 1250 824308075 824308123
    0x918011d0402030a0516090507052a010b04110307022e0b01121a041b0806040c050c0d080609070c050d0806010908010f0f0e01090507060507050a06060b070302010e0f 73
    0xa020000103d040e5880f505a8140300824011b042c8940c4540c090802c000303040034009280c003072040e030560341d1143e590040301c4172079a4034040f00841c0344403c0f0788011055480c1c00f441c6001e91a18050954400445180c0d29504e28004200900300854a001c1c034080038030300b039042c0c05200e601062418004120ba00001500b10140340142c44d0b01e0581c0820422503404d00144445081c0390340542007a56a0503282849a060314600c039a1501100801c040007088041c00407414508007039010a01c59802801c21500e01a03100c500d19103082400102c43c40002c15550401650b0306048800070f80221480c2000030084015035945a240e244001c4c0c00c0d010041c440002a03400da1041b4035110007081154003c003d80340e0401c00010140000d43d082c490880e007044041040d10b04148034848a450300314010340710090500344121203e50000c107060728544a444041d00c0800c601c1d200d000c00031300a0940c621b903143c40350f280103401e40d4075003c0c03800416082000c1d41e0950400114101030000d10b00c00381011410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 824310575 1250 824309325 824309329
    0xe15030a0f0807020306060931020406290f091c02090709030302150411280b180a060914040609090c1e050a060e01020a170918011d0402 60
    0x40442002822900406840c00d040c0b000c020000c20041c0d000760291101603654100f4403e0410040e2140307900440a4510001171031107410001407002840c0d0b80000d408500d0741c0001d01900c4040e00000c1e60182045105070310b0005c2509550317100501c1410850800341400520704590064007125400344182001005d01e00c854042001410b5a0007080c0d12001d05044800500d202d802d80011800340c0304130540180c0421002841078440d5a119103034041001062061101503103403110b030712080e003003c03141c2100380c0001900a140609030300000c00781c480b801143c4901c0e043c2d00c04140ca0340070740c200c0e40c01031203000e5000902d0000e5841301c0b007140f40b00c01100d070701080c003c0041780d2003848058580010002040080c0900a0071100c00f10301010040d030417030080301c440514903c0740303c1c0e2080400c0c004000d1240160381d00e224102e014015501072450a8a5860b034020017071100c0f916107440041e400702d803803030803603070380d5500c2d0900cad010821084d0306014921001650402801d5005000580028115 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 824311825 1250 824310575 824310583
    0xd0c0303090602092805040b060a0c020d050a03030b1314010504050c070501110a08070206100e07090803130504110c031602040b2e08060d02240a090302040608070e1503 74
    0x40001521145e80707090000021140c2d10812480b0851458002c500003641c0d15013802501340542c40104410b10700280800241c42d6405a01c104030b8000391403160280206c0c00907c50044000c0c041d440100302900d0300e108100340e10310203500e034040b064070b01301c441403038990464a04e0341500c00580700001e0759211a00805001d0082d0301000344150b08001807004894088400b61070b09084c2500c0f585c48503220100142c1c0c0700c60044924400030341014008000420013035070151b40050850400c0030482c2e40b9070111504650005040c0040302140c000304101c1030a0501c14003260140300c003251400c202d0241002900c038810000000d045002c009880c5044d590303564041030f01950002d00e600740c0080f02410051103103030801400c0c490020446c01020001d802110301c144151001000e600382e5008546c02c0203c0c0900d441d449141e000c02441b8038000303c01840f00140010400b907120494101d185104202c150307405500194669008040c2c2001120003010429810829640c030004900003142c0100b864 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 824313075 1250 824311825 824311837
    0x90608160c1202010e010f061a0c0604060c141b070803270301060e16090801090b0112030e0907050c070b0f04170a1712070c02090601030207060605030a050610080d0c0303090602 78
    0x286507e0484840300d80c0050742d1200b03044a43e41e09014078642462441703028070303018140e08202983c10000000300003540315400100903981c1d40c10810f0f105185103203888001e03000480c1080011100801c400c00125040100700000c0c0084802145469045008038200750031004d00010300d5804406003403019942074201c607001d0700310340c568003005207011042d20061814000a034070100d030701c1500c080f809130018041c4076110382d088220641680d186c01826100010320160039020001d050306111010b40c0c82012090040800c1e40c1e5440d07c070b10700024054288440c5600100d00300504010f07a008e6220301800780c3c0c0465038108803030f000280552134058141400d03094010900001901081a5649100c0181c410385004c6981100b60b583c89000a6814000008019600480c3e00c000102c06610076001000075078410200412038542e1364010900d4009200d03022113040d0001410003142601404030032000f006200002c040d9010441c50140c803d41404102604043d1900546000e0000540407508 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 824314325 1250 824313075 824313101
    0x9150b0705010c110a20040902090106091d16230d09110913060203060f030f0114060a030f02060310120c03050c0307060914011e090608160c120201 65
    0x55503096901c1c1003030090408141150202c2e00395413a69001100001d10034000a60102c00502483d01c09060528000700000c03d40e80d0181d220202400181c40d564102d0f40204000d445144036641840b01c035158a401c010155142110450108524406000d0321089201818101210440c69220f003141e8000700300300e9100e259800006102e510040141e004500303560003805a0030f004c00640781003104e9008140c40d000d0949081c541500c0100702c4aa008503080103005060490420000c404281000300f0941503001595682e624410028224140d0316405103089400608060950380c4150700115030f403402038020760006c000103010704440d50140340904002c803050202e821a41c602600c0568039404201d03528001c044014485040001c0e1080960324552141d040c160300340f0300400e040c030080c8503a036410003031080184072800d00c000301000030400080c1d03581036545003080700107441090060050301280014042516615911034034224555600115a0301014040d00c0124090300044041417 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 824315575 1250 824314325 824314327
    0xc03101707060f05090f130e0a0f171c110d0c02070e060a0506030f040c0e0423120a12020405060301120521120a1407120f0504080a050307020709021201080114090709150b 75
    0x12090141040c20f112052f80f155069402020f50003e0707114450149044800820b21101d20440948242d6000550400140c00c00c0c1c42c1001d03081c140e50350a84615007407010161700107071410700c017401800b21070991041080e030b41c140d41e21740382101003003440c400289481f448640620100e000c1100e904031070b1004040b440c03c0c451590415041c0040c0700c10300e100034522040400000d090300e06c400031408055407403200a0680c01c0c801d400d20140c420001f0b002c80752089950820012034141e43d0a03010718040c180c81007030311015140600e0054a00440410001c01030040e1818180c0045000000c8408015610a65200d40d448550034107014152941400c440000e600b400c001e0340075407011202d070501c00ea518060286102c8164144205c9100b45d801030040c4070300f045021810790156009680008070303441200c480aa490550f04200c0e00042030404031541401c004004071042402106084600f45d43d01038440d00b0304441c3c00f942c6c1c0070140b043c001810b441c2c0c0d45ca1804100801304090040100748005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 824316825 1250 824315575 824315593
    0x40e100e040309050f030106030203060c0714060723390111030a0c03090f080c070b0324011815030914060615120c03101707060f05090f130e 62
    0x29203e2078081c040c60f401680c0f000b41c8401c4500d81405600e048a4000c0d018104a031104a0840015070002e4001c0e1280c038920703115000014002c0040512400080d5182e0500c1c0c105854001c86105210110100d264401d004e41c01580d00c05116910440c40c84404d01d203c05000007140c860140307034403600a0041d510b0030407500f91104c0d412000398810b4004c00c0d400c105070004a00154100c84085a000e00010620000900000d00c0c11006003d4258cc103411200c000d503035944c2c0381900e0342c412242120340010a40844008683c200c10021803c135090a008902e1101a05c0d0404454030320b104921203c1011100035a5003406136010000241e007007180400d07980e005092480c2c0e01c40c0d06035045401107802c0380f0f0b07403803c20710f281c0d040d244a00c035409030320072054446815004840e00041c001007c17280d600342000401d248408040503001001b0030241059600c1c0150261099030ba4402681c05e00404209052150382c03407403140c08464a045502c01b680014071407942d0014030b0762922100380c3d4862075030f031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 824318075 1250 824316825 824316827
    0x15080109060f0b06070804120503120408090102070e0f161b08040f09050c191b030804210522051504090506030a030905010e030c060a0302040e0a060b040e100e0403 72
    0x212440218548062020383e0001081c00000d22a401001e48500303400d1000348a144d6610034680606805030341280e01381012240360b040809019281110300290000d08000c2658040c040300005001c4091039a071207180205400d5040200280343d00e580321000b8482c10710043c040c0f60b000d180c164040005583c110b4003032174100007552060191445181c5c200c1c00000d03200794079000b079078132a0f5410311415040c00410f0340340042011074815541c050045031050414440421200c4189603406699500100d040901384a46800000203606200c3c2c64445001c500700b80d00541140c413070810040362a9032002d021082d6a84121183d08865448401c420b9001c1d000134040d005001502e0b40524200207584542c030070982c0d1045031040003070202d242c44400700b1141d1300880078080403440c05816111202403140000322a1303031040d00c8a1020a82c00315060024500b1010210750140045500700541824112203a2040c055449a0403040400100040c04000d0724011030b0300900084a41f000e2504040c54 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 824319325 1250 824318075 824318081
    0x11010c020d03061a12090a0f081206010809120c070503100204030309120308150f040f0c02070b0f1210031401140f2a0f040909020f1002030301091508010906 69
    0x1158001078106040468040d241503603a90703001071080ca8442c1740040d01301e90360071003210042000b0010301580f0080310225849444651550f803044101130799500d8030048107048440054035407410044000d040145a020010b464a02078a00c4803135540c40b05107800029203011607540069406015503446082c480740180c0240c81602d109407205950903445e004480c07103003044038102400280000002c41c40320050b10405810094000d00501d40002c1e00a000c0b80c141c0720100074400c040b941d114501c00304d403541801074101030240b01c40154034181100055250500540e90003044070460741c404503440598400c0e140b070007946e0085802d201c0d012a405600d00a01d1403650841e41086001e001411041c1801481c0f88200b40c0c10070407500002d080d407201200541401c0c0c40d03d00c0703c001000180c0c9140c1c002e4010b40014015503402040a5400e0b1040c48080b42c0ba007035200d405414000040302c1d40c1c54001c42a2419614043c000003807030740d06650402000081544164407079481e0030007030000d004980e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 824320575 1250 824319325 824319343
    0x2061915080a050f124e070c05100c0c020d1a0106030606170a02091e101412061c260405030705090604020c061006030e0c090105010f11010c02 63
    0x40c064402015008010725202c12400700b145c3c0701c0c007034204544407104148842d103498180400c0294090410b1103512280350b401d10761041d04a550481c1e03a40345d0098066801943d000c0788500d0010f2140c1c1640ea99107644e24101d8542e800d842d9104c2c21196590341c411210103940c5900240180e90780f8606040601c603c00850001c940d003d049400003007082c0d400f90040c00c00304d4103283c1c1c0d1956074141c4030b1740300c21150324064100f501c00c5408010800a5035207221296900c405106540c000a4248508004610681490031024001c11340f01c02c071000c030400015a140300e2818001480c2d40d41d80c0d4000200240d0303462800706a40c03d0b0000004d0180000c00d01154141e4040301c0c1c0a5030f0352210840c150032540141e100b0980d15602c1442c040c40305045c500145604460044c201500b000399400f1190308208040f28030710020740e84036804200035641400745041d82100740c8050001070444c0c40c0804c5072980140116418000320310900300d001c92003050048d6441c8080802049240e6103540000e40710310081c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 824321825 1250 824320575 824320583
    0x70c05010605030105070c06150b0a110622021201020f19020607090f0924060503070909090b060f0d05100615020102030919051e0d1103090102061915080a 68
    0x4500460b00d4201403042c980250381a03203c040301034596658150286c5017051100300407042d411400106407055102030030885086850360b468010380c0f070079000c0c40c19100818400040c100340150107403800e65420501d4640750192343c4030032130407000b44200e40a840f031070031603201d41240000c0d00d4000340b00392a03141c1805010b42d0300380d031034039150104e048444203803c0c011a42c0c3d5190303100d8100204001a40920000ca101814141c481c0744480018031102c0041c0d4000c2001c90800010014060390000300c240250042e581c04028851442e00ea000502100800450050011124281d03586c1d039100250741d0031030390220894020184007001c2030050400751154030f6220103808070f1034810301e0042c02540e00ca031a0410040117152400782103210139a4500509079018010804485178000940c0780d814004800303040141a0100e501800418900c3c905800e48855001442211740a80e400b05801d500303c0c1e0110310600030700f0340e450003d0005081000c44180407044009000920110200c1c1074680c00307000d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 824323075 1250 824321825 824321831
    0x22818080114060105031e100603060f080c010513030209040614061503130206070203060f101a180f0301090f0203190b040803100f0602100c0509010504090203090114070c0501 77
    0x34400c460307400c2e102ca00700032101c00102200018581e500c214082d6911103440d540041285001d561644225041a202d03180e0030a15524103110f866014040e0b20020114101e005020a01d0403108680f42d146400220b4104800080c40352580c1c4191401207014507002010410107050a140c1103004010407031414005030aa00700080c03080c58581c2c0a01c0d51121400101440c5a50b40c80c0c29214000c46103104130b92015090000001684040005610540d40140414050308002c04001f0031140c0d20b5104945442606a101041d0044c03242a20008a0418a6208065109400150942d40d20403840ba01503181200c1076080c4aa005c1e15007090500a03001e880d502e880c5840b06c0440c0d40500207000d080c40b862000031400050550b40290b80c05054840101c0c082ea0716041d4040220342164800c0c3c005a00c40003868501d1202c0c1e1151214072508d6041072450100188006002da0040b841032251880c1e000c000070350303080800e40004584190381c5140f000945480c500190205440d40400c0c1e8596203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 824324325 1250 824323075 824323079
    0x9070e01030e070501050f161a15030703120e01030603060f231b07080c062e08120904091401021201170a0b0a1401030b0a14100306022818 61
    0x1040c180181c0c2c0040c0c1d1600d11f09801d040450302070354000f0311045024100552510301081c02070384820720101302400808083d0600340c640f20307900e10907012024404d420000d401c100242d41003908144122550a00c601c0c030400b01e100580061500754005008507041c240c12224001d41d5a0040c0d10801581105241c08242c8500c0700c0344c41c52088a803c40043e5100362450442024403000e080414490b00106203403044582d0260700b01034090741e4040244c00d5003000f200d038031009030380c030400414401070b5400d6549103001030542e510b024a12080800480005100d0030341c2d00d07142c100304886a003003810a0b8501f425403070f04c10f00130340c0001500e040f038000210010680c0103195103c0500c641f042001400c0e9120310391942c0101400142843c07061a5480c2d50005021040c1418580294001d001c121001d1814a101c4015648003442101c00034480800b04662881560008010380c1c1c1c000c1c0f00140c80715166149241141d102d4400c40d070361440c02440101c41d0316480702d2031020542000e00c0c0c2d100a59 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 824325575 1250 824324325 824324351
    0xc020a0f0302070617061804020d0804120215090a03060c0203130311121615110a0308090c0f24120a050406201b031303050c09010e040f031d09070e0103 67
    0x4682558003645c440021940c040300c0d04a41f854003a0414001000030150103882d90741c52a060303009904c44008900c50b00b07012419481c1803d020b51400c0324150701c1510705500d500000b5242032550200038011390782e941450303040034400c106488444586403044100320f5102e040080c015480030040c948035482403010b43e2901c81002c02c1039803017110703440151000142440045814804890003030001c20044490a840c038a00400841c00e01c0d0340a612050b103c0d00f04040d415090420f0880c98a0042100f00c00341210354072079200301641c1030840c0702140802109219020100c3c407854280c01e40038004001403143c2c04c140b07a4415405948502020003001680440f100303d1101c4c01142c407401a981440070300ca42800010400d0761401c6401c044e2841c0941445e81c0303942c40d01340fa800039030300d5620400307010859041c1044d54a000d0809240e4501051030980d450b4141c10071010030003010000840c15a1000c0402c101c0c0c0b4409440c0010b00e50040380c907221b18003e02d03644120050900103400e18001130040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 824326825 1250 824325575 824325617
    0x60402030c01090605181527010302040b0a0c0f020301021b19081b0708060109090204051003050a120903120824030726100e1b090a0c020a0f03020706 66
    0x131415030303c8803030421030544c00c8494660040b2200030b4128004202c401c0c00301c4403800050901000c3c12807980302c3d460100f070058407040c60f1420014185841003005004441042050b5030400141e13241c000514855071420280b600340c0580008d405600100b0710b80f10a90070510390036402c1c164642260341c500f10400320303142d040d08400c4001d443e0603030400030026001c030742c6440c411100707032040c00310303040940d444030100d00d010401d900500e061940d4258160071450a40a0781d900001c0c0c0301d801e55034007030030341e1a46610340d8400c800040a00d4019242d1802990068031381000030354101d40188a69030803180b0180a510040f0360b804080d418002d960f4640000401040303012400c0030340108409810303c13041c0102038071100000b6100c599031070018440c41d5801c0012400d541340000020942075013019509190424640c0010015900c1101c9001241c461144003540000b0034a0f0104881c0c1a4600036070900400840c0a054a82d140c080174044c10b0300007564004403005070f40c511241104070a244004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 824328075 1250 824326825 824326829
    0x140c03091f08010e0903070210231e091f0207030210030c0e060c070f0816080d020c13090f030305040b070905010e041a09040510060b041d180f060402030c0109 70
    0x301d0510b03801408540c411107580d65000340342d00e007181d2a090303903600044d4880b60030615103800202003000000031352048100703000085800310803550405c451214541d038070351000c11042c2c80e201000b00380032409642e480d4000310054200b0744100c1c1007c02b20341c0001d4803640c1034003003a4040c00000b20503203000c510034440c99101c0595543e80301c5544103440208203049e4000c203118109440380035008510011191030380001404410000c21405d21480004483c0d00b180c1da010070f14503001711620154207600403d8540301c9a9084448041d0700201c2c0c00324034000c292806015009080c680c80071010907030558042d601171030195400c000341780c0e0b442e1070448181c480344c010b41d0300007060580e1100c92400d0a401210422515190074070f214540c1c0305c08603a000c1c01c100d50036191a802035907035903890041d6210385000341c0000180f540c90b0504000ca50f00d020080c2031442650706481e1000107a020140c11030701e17400c0c501040160780700260300c1d01c502952440c007a20143c0c442d01030f1400d000d00540c015404142 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 824329325 1250 824328075 824328077
    0x7091e060e0a290c0706031407030c0f081b0712140309030a0809031204080a12020306060a05090112061701050f06010e0d170703170a0504021f140c03091f 68
    0x203651000741050100182e00f200c000d030400002445411800c580500042018000070303a00002c00140d041ca00c10b01c10308015207180189407a00c1c1c40c0c495460382c090440e021000b954200081c440d1100304050101c0441d40480062005011681004000c600e114001c0d050349183d5036542c9054a1000d4001c4900c82030300c01e131006a10402400072454095400542e221002c5c0047d0b03801c1800745581c0c0d540c4042d0490701241c40410000d0400c82580d045840060302540c01c25086041d80380100204d09144615000361013401008601d11089070302c07461081681e036250150502030f0030f594044030070900d01c03080d23200c4019500701000070b00c8200910541c0f0f0312414059450300c051306c240b0410310000e44d0b5508002e445140b41c0080c0751104481940050201610031f07945c041d00003850401411a0300d001400c444e402a06102c280070160b035824410411105502c1c44a546000c40351b203090301c3c105285481c0c7c801204020031200c042c0320002c4054881820280c84c01c01000d07122250280b110744005203c20 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 824330575 1250 824329325 824329349
    0x909070f030c1403061311030103060b10080618062227020333071e110c040507020c090103060f0b06130b1e1216111507091e060e0a 58
    0x3945c58a07240c9070410301c4448000c800a842014000c2d5060207a000f60001e5401c40d407116945022420040d2899001e802240303007514690610300005900d480014200ca0803220324040410015500c448401400c070301d401d265500c44410f070703111290141140c40908510740001c1000e414921002c2c8003586c403215402000fa1482e03c580d60704d440d50110175440c100d61401c2ca4004008009a0603c0d591401003803107440e0040703c00034840b103070180021481c0d124420407650602c40f4401840001e40d000c103680c41168042182d540d6150221324000c02c42840c3c0ea444511b0200000038443c0c1c036402101070503c443c5081c00039a120f642801014403130a038445829941a2008120f6001510040c1440d846800403114140c42002454095900324015104001d11280244041c0d1511240b26088085072801c1050290005400b200c1c0c8070700d817510320080fa1450000000c0c1c0590301c01e8501340c01900031441d09030b2005100d24000300d03414040b40100c2020400b00c00b260a183c0c640701003a0412540814419 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 824331825 1250 824330575 824330581
    0xf0507201612230703020a0909151e18050609120703140d0f150f0612020c0703170316020c060904020901140c0c04060e150907050909070f030c1403 65
    0x70031010300b8081c802e40b84582e5240d90f940394080d0310010810710180d0b0740010070a035801c1d4010841c810410781d01082066282c01e525500040282912000100c10b403034001071104a00350100315100c202d010032203c0c81d450101e2640500c3d030180359020701c0601031400c07280c284d900c0b0410030340c0d980140c42240d16082c82c24030038800000d110b01000c0d111102d0400d8241d05000d2034060f141c007901d040780700000701142c5540600320308aa45e03003480f0004025402d070920402e427078020060140002c8a044409441d00019940454401001444020f41d40018003050302e070824038031644160006d40d4040c91020750343e40088403061000500e59000f440060481c0d18003000c2c2000c0000135441040f50307074103001840e540c00e1207640800020b04105941e80d0068181c02e00b41804100c04c80741584c02c49205101548203004640b4203a144d004000b80c3c058680641c181c0f500c0a0a45190085801c002da22140c4501004140c55100442005010383d5031800c1c09070070711078001581c90700c01407131203180114024000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 824333075 1250 824331825 824331839
    0x9030306010915141b010c1e050912030c0c03061006021903020f060907080c19050d031215051503040312020a090b0408061005060c0c01030b01030f05072016 69
    0x109030041401411300200810200c8010f010580200c581413030300012000324400800340a0140c060710084920300b00807400014034624008642d004562001c005010520000ba51100240e682d14907a00c070702200c2d1520b48400c2c1d0503668400e08241035000b4083c410104041d44071090024040d1403240c1c01410045820032504c0c0c013414490304c0300740d0071031246a2050441c80c10031300c40d4034021070b0804047c0c00080c2c142804a854881403100c141c0c001c102244809000c1099004008107488040310413001000c801c3c02d040300e01070075070300d1341c081020715002d03402a0301c60400712000100c40303050302d00f860f440501c440c1302070080c042280c3c00b8022031994940104610442d42c0101030380402d83c00c0184000d512051003c3d0b05820a4200b0a4268054000d000411000320501001000300311800c40c0352000090410391501e051034051030502d80c5a10304034109a001e074020417001985043c00304010315040200a040f180c8024400c0b0301888400e0f020b800000d004a00f98244101c812101c420381803404070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 824334325 1250 824333075 824333099
    0x90615140907170711120c0705060a140a12050c030c07062c0307140c03030d020309070e04050a02010e04020c031608040f0b0a08090316060902130f06080105090303060109 75
    0x141c0b01001801080003018030b100903000e80c0100e0040e40c0e50a11007a00c908080d140c80410074044e10b0100382800890b10103030000030008191402540c0081e1642000007048e01c900700c01038480448400d003c0b0700103e82039803026200251842da00c006200541390003100700141d110070740c1d42000c03482c01003240b0004203034190061220040c030107600e401d001c2803c401014098918502d048141c2d000003c441052240038144801d0315600c80e40908140318044001943d42d11030208201d0001d41c000c00000c0c8500300170b1000c01c0040c103e620340c030702e141d240034a03005440f2080403c080f070216036490b5505001d41003038401d64001c0f14a04009526060854002240f2010080c2d41254410402c1102051007000d41c0380410042c0041800b6644a429501c2c024084c1c1e24001c1130081c0c254400d1010f004450000000c06134484d420070301c0060b006055001143c2c0a292031601d00398690b0030020300d011907448540c45041210740d01d0b002000242c850a10703c03078a030b12081c1c40c0240003d5140d01c051281c0a0170f16 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 824335575 1250 824334325 824334331
    0xe010302010809100509010903020c03010b010c020d060f0609020a110a08090d0f1208040b0c12072106080616140f030c070b070903021807020d210207060906151409 72
    0x40480e940e42030b611504c01c090305c100710740400c184e035110708444040580401200201e510b00700c00920502c182600000c0c040385440d10041c0c4103a18001c030980074003409a0284c840e0058410085c8020340d25440030201130f500c402101c5e400200c4403444841508070129181340095404010740c2e1810040c8030802420302c407607001c1076600c1ca41050307008000500e4240060710145c5036881c0d0380d0349850a030402c1c000c03141c002010310485403410054040744040390341ca2683c0c0300840d030422000503a0072007091340408445550b02e5040902d0b2080214002c0400540b0500c110a4411089c85000481608442140320395110700c80781d1006015800d1031a1600c0b01940d41b0103184040c0c18105001368a90048020044c0c0700500842c00b006014825401c284680f9149601c018800505605041800940c0d03803c104150108002d150846510a00d0000d1100c034008070480e60159115038040c01c0c500c00a2008041c2180c1702460b181100792411602e10180080312089001900c009802c2070034070041001c02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 824336825 1250 824335575 824335591
    0x10030b090c031b180f010914191505060d05090609030c0c04020904200d050a020903101a18090d030e030406030b0f100e030d090f140402040801061502160e0103020108 73
    0x481301d058440307021400381510901402028000075454010080112207014100c1c959443e00780b41048a11405000b8202072042e0381540013a603440012501445161140c0086521a00000d501400074001ba044540203c1c0590159491354650aa03882e94a02c1070400b0300b00160405d11281a42d441c19501030400750002900100b40f58840100102d19003644412a045400020510540d40a40c0c0e118855102c1e03800c040131440d00b13040703e0000307a40700f01c003040305040e1f95240d035803007036049603c04500d00c610350780a058150a45000000d19010700000c5610b820b0901c5149800c0e440b00d4401e00580d07459401c200069890325080501c1103000e405000c1c54103811800081c0d00c0400c546500e03207800c070954840d946403048201020100341c01c00b50030600c044208210402d0901c518560b007a40a03044030b18940c901065059880041000780c0100c0e1304c401015441e003d0b0020380e01d40d41d004219110952a4243c403030f81151641070502c020064001c01d00031203100c100500055000f40c03d0f454002e201 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 824338075 1250 824336825 824336839
    0x2001020d050c011517010c0801030230120a14030f0705030a11070305121b25080a0e01120606050301170109050d0906090504021c02090a0e10030b090c031b 68
    0x403000580e844816139901100300130098030040360050f8003e2180d12a04d4090340b4003c0e046500d1900041ca20184101100e005094a01200b101c0480500b2840600080709026145040d46542180b60a500084405000708440000250382041d02400b203d100d01020202d14507a500c4106084410760802025141c019507103a034480c006624840103445014401c0e92155030b5030310b505156900140019210ba030140f4a004400c0402d4045c21098925403818801d2401400189230001a18062040c8010740150800501000a61f03445608000000c800f0303291102c460031940c0016088488512407080002c000f80010b202d210b0703450800c0700000301c80300300205100400361a80d40c02d290032290303541d001c036445ca03408010154114584170024002182c0450500c2d03a03e0641c130094805040d2949a0720746e0009094480e40d030380002500150050030303003c1c2c0031494030501104a44e4018002903070b5502c240d80c00a01000780010303c8603c542000741c040c0403041103c000305480c0300084034417241d03c40c4c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 824339325 1250 824338075 824338091
    0x2102010215090715020d021515090a06080c06190807090302030d08010801061203081f0f0303020304030605061e0111010f0c03020318210c0304030606080a2001020d050c01 75
    0x1416501d460091000c41d0140c2109440c06102c0001142c1c40075000c0c0642d0000c80c3c40f10003558010441200901600b1300000c1e9594990140789d10140360110f41c5039001c05260280100c06900d03911000c10b40707406204880944c000c482c10481c00c0e0080e400912810042100c0d2030f0740b000e1256011680207581c6040c00301e1800c2d280e60000342881041949800064405030040001135000d009100040c01c0160318400e00c3d03161520002c04090000b89007030304004520b0065406481c04800c001d00810741030301284100c40d164034000b504c1e03501a00c0f090300c0590802020034428502024111300c001c40520580c010b82c150240113681ca800441100d680c5550f0b20350500325401c41c035004101c658002903800590780d140c01c0e52509110382000a030326505d980301310040f14010090020031050120040301242e100d042040e1135900d54859178000030a01030818800240c0d086000440c00c9406205841c000c3c0502c40c0500b04102c0105100c40342030050b030185404058640c002c000500c40104181d001051a80e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 824340575 1250 824339325 824339353
    0xd1103120c0d094b080303190216060b030c060309070305210405090c04030c09290105031308040305060708060907110706141204060209030f060121020102 68
    0x14220103400c107125041189210b000720340c0401c016018194682400c108902401c02c200000d20b08111800c0030344403190311301c0d480000d0900d01500e40140340c503520002e050702d55450716180d40041d112400c1800c070400d1b0003014001c40e4005e90303030142c4540d1910440c150717440e2640c2c005820942082505030040d011201c60320744410700114401c0c0c4603800109103441c9140f0b8002d1403ca0007480401402c0008160603403c40c2e50b2900b03e0b82280d408841a0070b4545644040c80701d64801d560000f08807003041c1c2380026051a00d40c0003c401c0b5500c05102d0024284556180707040d80300c8254285000680400000f840f00d000003184410460280601c1811b058490b91031500d030190503900400030031209804c0103203926019040340c0e4404c030285000720080c08110701c0c081d518031140c0210303401e02c040c00001842c280c440c10152030030132107103e51122340c0b8109810818000e50089603c140280034184124014460008c5c82904a40b0707900a18001d41c030400944289000d44903804038114080c01c404030b1480303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 824341825 1250 824340575 824340577
    0x6050705120f1c0606020d110601030b040c090c080a0b010c0c030303051b071103060717011203111c0f0509090a1802060d02130f0501020312041104090c1a0304020d110312 75
    0x3c205400c40001c0c0356410581c0113071074184044102410001400900007644002007010ba04607548180b820b5a1a122071502443c2c01c043c03034100f0007400d450802c0c03012a203603000100f00d0040185940070001040721100444025201c00405044c01c501140200002486944443e46c0000c16044800300d01040e4844228640c0c009032054800e40513003a0303c00d8080c80c00303101b8550458190b01741076540c011035007074201c00a84148101001419072071010340515000b00b440001c800c9504059981c05940c1c1190800c00030800e01c4200c001a4074205201d02c1d641c0654121103035441c00030310092480d0368000101c406000e10004040c0717041c8140400d5401611500094a00101080c1c0d015032601c9a400c95400000303005d9020712400c0000c0c2c0008c00060340c0100032109442102019148240c0e40c905100140e20500c00920781c2042c9400c40c5101405846480502641d01c2e00d0341c001c0501400c1c0000d51044d0000b6240071754043c80c4a20310b0700000e80e500c005005954009015244810380300b080302101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 824343075 1250 824341825 824341867
    0x203091003140f01081504020102010b0406080609070f270209100c0b0f0106050708130f0b13090c141c05040c05041b05030c0702150703110706050705120f 68
    0x1c80c2e200d0b02034030580810160420303842a0004075448856140c10080356403000751895010885c0e4405010a003503910030f420400c41c0b0070700034005106003030f83c45018075541c06044034080254096800301240440348801010f040700d89080e00b03c18040100b810032003881494200c0300000942c00c0040039020345906030b1003100101d56844005000e050f5041c00d4005040082c0ba4034841c0b03200c00c0c0180100c0f030f0040c0c16960510b0304000c0c0aa00c0303103034010a80485c14046d822807911840c031100001510007e101c0106903046140c11004013090790b440c0c0c010190364891440350040b4910004140c162842032000d041d800c40c110701d410b0307405510300b6510000c44605540580390031300360f81000d0005042c10300940d40ca440c281400a01c0407040744000030031314000905400c62561000441e1019940c40c1840e0103602d481c1000840ea4502d035902c3c01601c43d58140c0e1104905014403c8009a00c5001e103060b20304260300080a4003401c0d01c402c3c410489075001d80e590b1b200700b01d030030f0004201d8000c4510001c01c0d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 824344325 1250 824343075 824343077
    0x121e060b09010b0309010b092a0c25060504080d031109090c0a030c0201060509012c130309050d020d061a041b1106010b0703050d021b01060f0b040501200124051503070c1202030910 79
    0x6862f00720b090090a18451641112091101c00c0000b04458980005c15a0001001d80340001d40051800500303440ca128820070642e03c5040b801c14098401d01610084c42d0038641c1361020041e44041501c01c0c0c0c240c0740c80c0d02c00c40e13030700050300c42c010017907000440d00401d00b00c8200010300333500c032000ba000c0da070b1844d03000c3c0c1d4140b06a01036462804200358104180c0005054211950700004600f503002a130102c1d03520300c1c020001c035201c01c1218040303540e0360402800300c5001401440211524514018668061a1244d000400380055512482c0010904a0503612620b10745460004151001c1d603041e0311004288074504c0e42007225a60409600403000d041800c854004078009181c1640d400c4000c0c00f640100004540401c0104030603030308114500e91070a180008518018003000c80c250042103d1114441400390b2108928109008480c00302c0c2940e10844042034400c3ca850340790381040c00100c80010108442c1c1c00d684000c210070102180d9001842d03c100d9140c072040c45c01049004a00c100801c1c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 824345575 1250 824344325 824344363
    0x8070c0302030606040920060c0307051609140a02070c09090b09070e010f05040e0102090d08040807060207060c320a050601121e060b09010b0309010b092a0c 69
    0x120440c07a090103155005001220103100500680d05c1d41f0b0110340c1603044240e0b0140c40401e10550702d8881c90b080e1000c490524059035140c217110f08200d238a9003904131262080340c550340d02c00f241d0004c641c85100382031024540005500d90350716003400c0081d400034006032440f4462000003c2c1002c064029010030902c148001c201a08081e114607280031025003000c803c0c039550070014441a05a5541c1c903080b07840455021402345561980c0354024424650a281c1280d45104400d041c030015100410464020008480c41c05944810032a242d0025014503030004400c010001d000c074160944a2540140405240010308200202c104001404414104c1c13581c02810081090100c02d00116004040d40c0044000180180c1da8450300300d203401e140c40103100401003010003480410740c000442c0384000340481d89156100ca058014a4001300d500009940c01c080c00380529080001e405801589112403006405842050320100303181440007820b84400180003130521998108032403101d00414001107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 824346825 1250 824345575 824345579
    0x504051903020f0102060403020c0f18010608040515090c060f0903010e0f1b0307030222020a020714042c010b0d08030103030311040b0a0825090503100b2b08070c 71
    0x100076020390030f003102419034009904220100b0740129034031100c03075411a841c101034000c80000804e442c07880e00100c820380c40d0f14800400e110b5008007903140100e015004540803c2c0340005500500b08086400040c1c940084401000390f0a01c20040c240d00e0034030014107400e00c0c00120210342114150300074280168402c03500364041c00300602841800039a40000d03404450300c4100401d982e80001c2c40000e00800c2000030004040c001c090094480c00c0a1090942d41c5a44021000b9503860b1706000e4088090000c4c5c0442c0b40514081c81900a14109901e00a11401c908c089148825606071350401c0326541b201d01000840d680c00c2500b10200b845114080c1e01c950541c00c00400321194204d4000c500c041c208000c0c003401c0c018805540007120a40b81003162551120008461170b0404c3c0b500c4c0f50450b0200e01c0d025074568210400d40182c51098044a4444544020324001c0e507803a120a00d401c600031041c0d91042035244030052180c1100d01007501420308155a41030075981c0072810a4603921b48004003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 824348075 1250 824346825 824346829
    0x905150613090f09030806060f160812070504060806040c050d0908070b0606040b220b0c03211003110301090f0503030f0a020315010809160801020a021e1903050405190302 75
    0xc0f0558503007407840800c40690366a9002c1c1c8100c9000e807081e4407581011a40504001e210000c07980d03410514030b000040c040c4140360074420313030300300384842d582c014205030020394524072030310985049464036503a0030100d07183e55081c0002804203040c2c07042000000c10104008064a0180c01d5601c1c0c41003a4251b071360107090800110a0710040c03d210711038002000108030200052040e580c2408612d4901a0704032281c0514040c1c0e0300003640001e41840300401d04500400e404009482d90041003089480c3c01e114403000000d03a400c048901e07001819400304240f021841c1c01c60b102080440140c00040c7c1c0c91003e4a500320401c401180855441d4000000c22090245600702030b41c0100c1c10420550460515a090712440355001241d076041240040000710301150404c9081e443e039003000c0ca0514001d407107441c064041d61003a00311001600c602d10281044210071800350740c8041500c405040d8194450700da02c00907001c50036059081040030310001c02c6a55030b0000c1401e840107003140c00000e0504c2c501c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 824349325 1250 824348075 824348081
    0x2030c0c0f010923100807110f120a050f181201050c030f2d0a06050d0507060f110d020c10051306050a0c060f0b010207080f07090515061309 62
    0x1040c600500200d0070412103640c0103003400041e28050032042d081403400c5a2119030000c0722020980d8000111440d60800d9500441040d025081c142d80c0e48464010303800c42640d9400e103e000d4800e00b03038405100349400c4524000070b400103171007500d00301c0d2401e024400b5604060300030200b40040e070300c1d541b031164080d450000220f0141d00c0b4204000d110600e000c000b199a175000c000c005689401003240059409004e05026100750508444403110324098541a04c6241c0c00803940c10400030301d01280420141f60501e8202003150b4810000c00e4a035003002c500301da9051115190b0410b1000341036a1108621060059001200d001e5000b0040c0115080c00c01a006040c03002d4202803001c100706103103d102e00e11070000300350303102824070564030340302a0380851b0001c2c046003003e048540350101f101c0c58501113400c2190044e038243c0c211403007980c0ba10318483c1c481240d0391401c10240e1001e00304008060884d0070241e4014207100c01c442c40008020301041c419404000868000d0b80086402c0c45000610300c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 824350575 1250 824349325 824349343
    0x6050c0904050f01061d01050c0d0801031101030b0f102a150c0c1209090f02040f0b03061311070b07020d0216120b100306021912140402012d02030c 65
    0x7409290f00ca51421201404040012106040b081c00a0030140b0f03080e40600c1c21031780c400e5110300c21121100c040103001440000c0a0100300d402c80540101001c9070b620a0180c424068001040203075490340c000200802016054017920602801c1d00703201c44d081c2c008241c1032079041c03250341c442d860050303052809940440c1283c0441000d80d103846052503c5940c84092040250f90003135560504c40045a03003541d013049180d01c00c11b243c60902070707139000340c802c681c010340121040140f50507130a0b40c6031440318549000c02c440e410342113104400c200b00f0302d10003034001080c00b43c10708584a260003540e44070240307080e00880d03100c40507902c00c10541740d015074100032002c2d41000369450110394a041458218040152042c0904810103540115441c40c514814101c000c0d503110800715a80c130380145d5446981101244d00a01150358110340d0b01809c0424042c44401101461407000b090f695030340103548030550100b00c0003030019040e40318144c803002c10f0043d46031200c0d030303400a42c0c41c1c5d20804641868180c1031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 824351825 1250 824350575 824350591
    0x81b0a05032e0515091e091b030a111c05011a100f0234120b151507030e12060939030a120801030b1e041203060306050c090405 56
    0x70004001c50005540c60710005204216000c0c5e80940b00c0d07124948803550401c5070301c5607400340901403105080c00003901e098540481140c00c40c08042100805441d114601c0c0054210090041500d01914003002c40140341501ca020414440c0c42680340e031800c580801103003440f0001e003507042c0c500f00e02d003400071440442d02c640760041c24100c0c0c0d520001c1d00c1c2c0e80c4180700d2118510b006480c1c6c2c817440b40130300c0d1181003e42a00f00c00307403840c0d5941d0490840074251100300380c074841d1404002c03030514100c82c001101401d4003e484403071840580726030300300c41c4e0b8840034042c0e040041d80380c4050420356444055200c00f145c85402420241050b088035402c24100700c8242c2480c000130142100d040c880040c500911141c41120704846814010109050a00e29a001000805103281d85000d07a07801c40078240c1600d0040e00074018aaa80f641da10200000e4040c070703c402051103100040004402d203180d000900582d1a000c07404a540303950320825940c017540c420380040da000c9520119801c191046540c041c00c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 824353075 1250 824351825 824351831
    0x2040905012111010503181c03240303230c16050d020a170f0303010f060206060117040b07050903070306061805040c0b03070323061207081b0a05032e 66
    0xb540c0e48202c94003100269880c14000080009000c1c134107210b2141388281c400b08145c0700410411101400f20807010103550340801e1078240c512001c1c0646080c0f540440c0f440100f44036030035003036032410368000020099a08500210b000d41482c82d02c1d0100260a4507882c1c40c0043c19000d142000e404008902600940d018a440d0300484000d80d65880c240c80842e003100003c500741c0030758400384a041c1924684448070314480000005040d13220a0380c00302c11900503a00399001c41c0c0310000110782d844e411000361541c00070260302150114041c8420142c2000482c01c1592401030381502103400e005590313205032000d640d00d14040000950010103c48024810b000401c058a002d5031100402440380c0501e281008020000841c010b00961024840780405000c201610413123000203240b14900b02d40c41d5005001902681e0121880022040d00742d406c41c4015007000c2810381c580701c903440c502c0004a41d00140c0b500700000c00d51402c0c03012050310101c20071001d40176840700703040e4401c11940404100e8060f02e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 824354325 1250 824353075 824353139
    0x70203030615160602070c080d090506030103231006082503030c1a10030302100501060e0402090f04020f0901080f09070b160c0b0d1401050a12020a090204090501 71
    0x50303103418800c42450321144098840210f0a0380d004002c4008500030010391000a01206005c0031002c46011110100111054044010022a1029030341d02c2115080715003030005100040e849840b05074400002e0610301e400a0440b01007925140340019805170066603241c043c40744c070382c00740708000540c0d00205c25109061900c0c000303c0000709084c0300c050100544070500b142044840141d0301c14003108a80b140407642171209000d0700301c10381444110094802da92054440c9065030007858100c41c8942c407614040c80d01300e414840a0742c00309a51913405040111100308039681c0c0c2c03002c1d0010300951100907480b54080800507007542e0002d040c01001c3c01c40328003040b20208c0c0004003601616200310300d050f02c4011102c007008081143c02e0b0014406080c3c5100071a14003089400380200c2000d01d401404001c0e00314170020454a401e004454004010040c01d118559070304041a0b0664405030107460343c40d50794030011080b43c200d504400b4500340c40e180100070525450004041d500552080c01c64651 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 824355575 1250 824354325 824354329
    0x160614181908040605091c0818040903080a050618040b060a0515250f0f020f043b10150501030b030d030f110c0f0f0a0b010e0415020a030b04050702030306 68
    0x300480c4581000c2020000b0002141d44a510003031410882d95007c60502d0030b8540381140c92030f085552181d405102d0100c6040d05840d0901801c0f00c101d0701074903034641544403000500c010f01070042449400414030304001c40390001000a9505c51402080d50440c0c5003000c0040115480b00740e030281d4880c1c40c40601c89007407801d000c1300712101c10100507031042e10f80c8042d80147d01b0b4000c0340800540103010407081ca100340400d60101300349261003110300e40100022034040204070741031500040041940b11490444c140c0f10000508101810a03041480901b08010038a16009006451280b156110004000c160001c60310b04d1000d0002400c2c2030080c4c1c05004042942d0314040301c0302e1001c06844090030400e1905aa00040024200d04600c1c2d5a03030004030395095441103803a4000c0030500c00c806501c80403c00c041890450301d680f00400307044691820300b1600704c0c1540074200ba18050740311035440d244000c00d0f1000b03105a80681c0c50105405000707030704000407076800030140e605540040007000241c3e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 824356825 1250 824355575 824355577
    0x612080a0f0909060603050406110315010323070f140f09061c0c020124060203040b0a050d1b020f0c060901030c0306050411030405060c0a05160614181908 68
    0x20803514200100350204207007103492030026032101400c03a203000804900250305400241c03040b400350405000403600e00301001c0142c03008641e0b4840341d4414945480041d842074204c005601410300080d04400e070000340800450070255080c20208401203514002682c001d50020480c1d406000ca1904044030f840d410b03010b512554040030702c24640000c8007451008560500e061030090060208845000804043c2c003c0c40514108090054500e020b030208072103d040020a4070b46aa000c3d506003031604030314041941040c0e40c980184002400f0184551300381348074400d691514126805101c540c224400b03414462422004034440d0085036903140552100422281c0821080c0303400100301d1070b8070380100c004004a0304410750103400c02b943d001281d03600b80007940c003443c09002620200d4a4040c19601540309402581700403d800380100c200c0b81030071342051841907001c3c080c00f1503c0741d0749042070f0352811812500e00825461b1000e8980b2004c40821080110410310780141d05c41e400035407914419 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 824358075 1250 824356825 824356837
    0x2130c261303020a0605190e0c0d0204150e070329090c0a020106180f1107050a0f080c061305060702010b010c0b070908030409020a0e0d02010c0b15060f0d061208 71
    0x42031107100c20303840030144200200c3c2d02d01500040301300414100307401100c00941074070045006a80c1015103200007140d01156101d03080c4d00c001c01c0e00c00301800c0c903828032015240728510f0f010440f030801e000050304c0c4240342c06248698103e640c00a038200c103c1900d0100041a49102d0801412804c101406611662842c0d5000205041c40303540380c24080380100c2c0500311a0704290036000211041825440107034100f155030301803030304040c4a038459203441306900d03005000000e131640d0303c03075040c02000c1003051050b403544501800b015481d28000350312141c0707030800c1a142044148860009517052140a10466402520300d00c000c0c05032130958000281680c00d903030000ba06207000600410342d154020055003009080481c1a0b90312580e0700d0345440000c0d0880f910344c6003c125481d900e060b181c0352000901c5591a81611002d4200140c0e032181c04001c44018085035204044140d445203d130340e00d02c00ba002c0184241c1d01980c4d2001c0d18a1030304251140e82d030080030313140070070b080c3c1c0310001c0d07081b1082d921 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 824359325 1250 824358075 824358091
    0x70905030c132301050a060503090706050703261b0c0304180912120e0d0f03090c050a1403070f031101080403170a1b140417030702130c26 61
    0x28840310754444400c0100b0300c2d441030196800e02e807900fa8410a03421010b4604840d0200c550a03101740d540e50f82660544000c0300d40350490f40144606200c018000c902070510180249006100500810600c080706107040d10070241040380b00003000981d140700d21080440042d0003600310700382105440c40d29030300e01450060007000d4801186854409075a54800c07040540c0000000031040c40c1020082d2039511310a22149065040804a8101060002e10002105080d503240f0701c0c82c13550200118000c0c0f1080314116880076031040009002d54420b0b50007800740600d80410519101c61030301705807620109074040c00f042c943c00300c01040814030154401c01200000c0c20321034496581c500d801c43d1018080350b505d44010900405011250600d1703440411844085110b010040c618101c2c1991084200d00d0202c0c01003c04200074801520b0f25a005000000990200da04182c401d030300280b50b1000c5c1f64000a941a51078400002c41540081e00c0c44084c00d02c0f00d01c056030072a006a44c14052100109840b13 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 824360575 1250 824359325 824359339
    0x703082e1211030109060b12010504110d081909050a0609081209060c060906240f04231509060d0c14060408030c0a0209060a060917010e07030302070e070905030c 71
    0x40c00303100900030340d010102c034014000c004846991034400010030381805000d0240a011491150340401446818040c54122001d0042d444001c2e08014059040d04000c0b82c0c20b0300d0a02c40e900021100a505d030105419030340fa0100b495040c0f034140320201c00f0f1035000c00208180400100000900031804004c0b040340d040d101660b50f00a100820401d12640d2184020351080c001004003500000c120315010350000301496081d90643c0c14228107894060b6030b00e640c8812180c4a00b0402d2915903c601c8901e50300b581d080c4040702841c40c9131412400112582d201108012081201a00d89440078650144017201c080c0d50004490316840303504180340c010341080e21009a10701181d0398a0b481510014608041200e64621031000139945400306d81608a0150316560081940d0707160410780c0100b51410b940d982c4441601d0017420b01141700054640c241e1a560f038481c03040c01c00340c00340030b03490285000350010705810b40781c1010303051041d1004003810100581c0060501c0b0964020805c5540d4202c229065 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 824361825 1250 824360575 824360609
    0xa020705070302220b0907020303190b1c0c0b1306030e01060905011d09062202270118090c0603050a06230418030f230703082e 56
    0x620300e080041d40020358441c0b50000c009040d0360310102080700071030806400f4442030111708184002c03020252000302c090b8109100151514440e04180c1c9860b030241600420200b603808007188003611440d1402440c00101d010403401c0c4003843d0000001040408502072421003058240c00700700e641400b90004164031503c00d0000e20001350090f0b030251101000c200415659120f042c00f042c43e050045041d9800c440000072412400442d2051180d00000c4400b003155444042c01c0d14000f030040b5003244e00074500c100c0348985000300418448005540f0765050b21950621010030140030069080c48400e6042140d4000007810b501a04401c0721540d0030041059104d1450303010141201d600700d15810b101106481d4228211846016400b07501958204030951888100990540003040044d01050210614243c100d00c112033740480c807000c2d031100110048084104000b01d5004040c254000751032b44040c08980d0b40d030200340840c2042540c010788a407402c04051150302c4542d03071180040841c100303141 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 824363075 1250 824361825 824361833
    0xb2701200109050601060302030603390a030803011d1311100e040e0c01180b16260d060816150201020c0a0c08010b06070812180f01141e0a0207 63
    0x182c01803562102c140c078180c1d0784a0a00034020341007100c0b601d10074820304003681c22490429102a03100b1601020190b4042d10100c400a80003000304036403500710000c070800101140100d409140030305031451114039500003d0301030401d1f02001a01b0303080c02d108025103d000050001d6060000200180d404481500c000142500c0072584403201c542c010f030a05044441500300403a4884200307c098880c03044030303c10034080360f0b42c02c40755000314100c40c1001c011100106c19a13a440c03007a26845060003400304c0072002000c402c20340d141c1200c005040004107105200d4269070090f140a080441c00074000c80c11018a015150705483c40746c01c0c013039441c841716403000920030340440703003181c04203004c403044100c1601c0c10000c40c00840c4124a802e528095a0450230319114048a41d03075034201d28590f007406d1411410070039020020f421842181c145076015800e500003800955000f000600001400003010030300c1945960000f05500210156a018104881c1c04055040d81061b1001c0c03005072200da203864 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 824364325 1250 824363075 824363081
    0xc040501031112041109070f140705030708040905040213020a050d090302011d0f0f010203040804170c13020a1103160f0c0b04170f011104050f0d0c0b27012001 70
    0x40e145003003103c05080100f8030003c205c40d0164a0f90603106e441442d546c0c500115210190303034060000044141611014403044000540a900d000f00c0640b1f00d099002e03078940c1d4240d0710592024044544401c20031040d864203180340c000002c003a034019031074100b000c2e10090680c4203200402091640d00e007504410b16100350301160a19041d6940816403400c84c2d04200d03a02c28060091064601c2003100701848000180243e038011980001c3d154201420005964140d0548207000606842003443c0711140307a894020000d14508416070050b6941120703000148005c0c040200e0b00741e0390380f003000b501c100d01d031600c901145170607008440d9040d8542d40e858030b5010b076402c03680080d00d0000080b801007a1500c0a50340d54400d4500d01d401c459400c8805c03074806003600c032181030320b9840150500080009090111000c03c103808020054040c02c001951800f03408601c54102d600080000b2414145090604031070100d030707070340009440c0114058070300000d0080c1040c074084188007031040360031014000c00350 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 824365575 1250 824364325 824364337
    0x15060112050901060e090102090a12030503060d1a010b0d1b0e0f0301020c010e0304060f111b040b100504060905010e0312160506040f03080a020c1b0a0e0103290c0405010311 76
    0x5207110150070a220a02d010f0740146149c05d118040c20800000e150a1410448422990548503581595030302404c00c140034070380c0003003621080703100c42e04200c1800480301c000e80038110350f9885503292600e1103049001c4800800070f0b03122014107144685032580c3c2041e181054104212640341c104048840401d01a0282e024420050760800014910003403001c0040c1040d1051565909070200b42e140c42150141c100c2913028600e504900a650400c9071104864003a400e006000407c41061503004186030441603560000000e03c085410700681d80d002100b54000c1ca800d00e405044c07541c4903c00a520380c80845041d042c0b0142c0088c4154860ba494070300342440e00d411000ba500b982c0b03043d081010415014030707812000114802c0000d04043d440344290303001140844010015009c0350380e11500c44071030324a141540f0052441300001c4040d003001805020314410010003a03a1481d2503900c0298950416042c0d0161045800704142000c2d400305540c200c460034603020840482d01d0010040603c554 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 824366825 1250 824365575 824365589
    0xb0c0c10021f02250b061e10120c1d1009050d0606050406092c0f070303021b0a0503190611190f020715050309070807060f021506011205090106 63
    0x1520300030320049542c2c00381c800701d1360318400d0302d03141e03440400388462050b5609001815001c071032004c11410300b040c0c080551511102d25003d101c1c482d0400000303031514108820000003031210303022443c4e007008a005011030b0041c242801c5c0383d03941100544071070501d507942c84540108043c0c0c8580321101c1c480c50f00d0030003c18000d80302100da0242c40c00d295010385124082c00340150b04062000842041c144200c80c190301d5000408a03220042e81d81c084010300c0400840c400c58800c9000c5502c8241c001e101d901c0056100f07400034020381750890300e200045614180700394403521000c0c03002c004d40d450100300c1807140e03401c1250700d08220007a45418401896001c400308050540800d2100c880c116502c052404a062902d070544011500c4400300e0381c0d25518002d404086400e0f098507240d0034020340295800c01c3c08a015a9207064541032090b2030480c1c154071400014901c10400c3d10f0050301844002c1c10900c080c41003407800c2c500400064481d8215803a001203403030340d9000040310104294403000c054424 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 824368075 1250 824366825 824366863
    0xc0f0c0b1b04031a09030f1b1f0e0f03192a060b01020c090103020a0b07021513050909030a0203030f2e05040e03090a03060e15010303180b0c0c1002 65
    0x70390400c040c0399003010708452601e200000201c1c1e1780e00000003e545c411009402014609910b61503449045041d10b08041d07072030301c10403118141890600c907014030211000d078400104040c1c40d11100d460041020302c80034a80d00100403002802c000b50518100e010254100803044100c9141d55400c144c017811240c881507950580c1100402105801c19030482d44242d003210350351400c040030070505840c280300080d4416546281040f4409401c0b0140040d180003c005840f17182081e0302c1c0c920741c0e0b4421042450304955841e014001c81c83d103229641e40004000c0021403d0141c2d4641c060341d40e120151072692907031050000904000607a0001c0d49207621000520042d0a0130581d040344151864000c3c1341c4250b08210900304100c500005454040000410880d091480d41e02c0e4180100085c0d0102d4000c2d0007001c41c117080d0347d82c0764120540258425616802c00d0104d1243c0b039051007e540c2c00a480308041045002c4030352400003080c00611004803501c551022022a00f41e151840c10540c400c0d40040e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 824369325 1250 824368075 824368079
    0x2a070503071106031e070207050d0b0709080f07051918061503110403120504030b090606010305061c030e061b030d0f0e030409020d0b0d150c0f0c0b1b04 67
    0x1804805082403910501c400b0507058280c0c0200846800111421440e510007009044c1302d410440c3c03070450b0441982d0059842c040d4407800803030300303500140d4415030300e0407895024800c81c0c0380c0c001554001406680058079118800a00e03c07611040c9600c111441b5004043c40214a880c05407a00300007040c1444050602c1c40030480f0a8020701380d584198409a11007244222400d4064003d40c9003607110000710920701800c0d82e0f2202c80e05140314124104000081c032010000581801605002d008410020222450413900040540f0002401c1c103005402d100e00a409101c120f00a440c030303140d818100040303000b0308003000c211207000b9001d40d98118562901012911000800101440b0f0010b000030320001c001c124182e401d0b20769403041045590b01c01c1208002d16003441c1c0c05030020162510000c0340b003648202c001540c801e50442e06881031401d50f400e0038120003042c415064140c2c502c2c00d081e0724256140304054220807100781e000d42182c003110002001c00302164075414042864913090703500c0e95 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 824370575 1250 824369325 824369333
    0x709090b070801050604081e0f0d02150709050d060203090a0804060e03160e01051207030507060306061e2c030604050c0a0905010506090402071425090605092a07 71
    0xc0c20555003100403030741d00b600208003401e042044400ba1840300004110079141040340121659599555012602445078040f00c1c1d80c0c0b09100c01c0031008055401401c0b02da02c44091800c180c80701401020502081368010045a25404561002650001c0e40183c51b0b641c2c043c5a942070500706d0500800d8145e001501065540e0040c100c01481101070782241c1c000a201c03103094620300441d005000440c0c2c90400100200c1c5090310444414550810a41d48259504c2d03840c545051001e0b00440301090f05c032074050084a60162440804400802c140c0c000f1055409000e084d440c03400b0219201d0075a00312a9a44c40e0b002140210404900035081302c0345840d050900645540030a0162840703031000c98000102d07900d4500501c0d041c1c503c02010703d803401d02403004000003540504070484480c0d00000c20300e0107600c024450325200401c080d880203124010101405000e00103604449469842c004050025407195080700d0360000c542803401c4c80d00240c5038031200680f258010300e00c00540d00014540104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 824371825 1250 824370575 824370593
    0x1050702091f0801050f0109090c0f0306021b01020a0906080a02120a0c0f05040312080601110d09031401140604200a03020702010201051305062e0f0806060919020c070909 75
    0x54480030003204031191140c0006090342d03020751b110310b4065205c200511202e10742d07078020f20005100c0d00d0040b400964428203040c200e00c1e160710036502c0e580e0102d0160100791070003642c0d0702c01c1080f403c000c40c40c01d1141034024140d00600c0c0121010814048009401d0740b4441d811038580d06010744a071822850512011400b800c40096281c002030300c10904144503a00440560b8181c1e42c0c03043d20401da2400044003129a40c0b001040181004014484d020710210240070311110403003141d580c500040e0031420801000005c0c50f040850503032401c00740c03c40c092a04030b0155080201100c02045804541640004004034001d800d0030fa45800103001442a4041d802810502e00c00e03002801280c1d00c08510785040052170700c0c040c0c11500100005522030030404031000441a4640d030b400d418411510a42c503541c800c1d81c1003d5203c94406c54140101c03101000309035440320b011076104d6910b180001079240d0f52905140d081c0145500850302d80f030070100030701201c0007800f440304007085410b0147c20300c031540c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 824373075 1250 824371825 824371861
    0x4020c0718020301030b1803070204020a2708100203090708070f1d0c030403030e100c090303080f150d03050c120d1a061c09020a0305011b020309100302090105070209 73
    0x400714101d0255599101600030350341200d41084110342981c1c1d6a0030980328006900301c080e034003800200001001030f034a03440035155405403550b414031620005034603084e010341065400c00400d11122401c222440c1d00065009051450800240e269140d0110003803414101340c21aa44602a442d00410038000e2088070404aa040000c94000d4503403442050350070060030384e030700754004004100040200e4080d0700804c0b51480348508a45150001402c46021514102c40000c00244080400c10601d5480070768682c00204a4802c071640342402c4480f4207403c415141002e01400a407081d03881418051800d5603c2c202101013614038a25000512511541c05240c0018042e8038026141d2030090340709a81c01c00400001d07040314a4a21119102510501d40083c204003164813801c42c1801601e41c508110000c40c4143e0000c1114211361526805550202190408540c41800083c074281e650301903d01a903000c900b40142c0da8135100004945070310031100065080240700c0213000340603690030303040f540c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 824374325 1250 824373075 824373089
    0x4090e01020c0613020d0314070c090b0112020c070e0709031a160c02090a0f091a1e070206010e180d09050103050c090a0506030a1b08070305070e0d1502040504020c07 73
    0x52039540b1603142140b11284c40c0000b0750003003c2c1d0300403500002e00407107804c8400f05250b940c403400e0a0269a4041c0f80b8403180e0410210a0b859031045030301542c100c040b108000c2c910000660034500d01489040e80c64219100f41d503508880403000ca0106400303906140043c2d600000c0f03076401e0300154983d010f03036200d0903141c640c0001c0f4202144140030b441150301103981980107158108a840310200c99010302000d42407000940c0c2d489013990001585007215104108005514114078542005a0324a0f54900da518101a284038410000c00980c082026415288aa006440c0f6500c039001c40101c41494000002061721801451b4540c0c2604001020b04590003642c05102c203a0f00c0405580c502c0c01003540c407a0b08040d5074801400a031a0078000317903521040105000400540407046c0494040001141030049816102849580c4da89806001d600810702e0900702d545100c41780201300490003081c80038046a00041c0d407030102c88200c1e01114020b190091013507486104500005441c1c40d09441204 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 824375575 1250 824374325 824374333
    0xa0902090606030402040b0a170c060a0516060b0d15060503010c09230913140309010903031211070317010f030b0414210a021903050702090703150b0a0f031401050d0804090e01020c 79
    0x5206481e0103401c40d5101c403055564513090885411a0051151105404689040d1510c1140c10035032181c0102a40710750084a12114144d080d0320b00104480c151717003010f4082d9041500c11a20341d500b01007034404035a0b482c0740c06c180460400c10361080c0d1703140904403a6030007030000040c000d030014114003070345c22280500704500d40c00c03203d08051940c034851009405d020610b00941003003c2409580004044480c1c0c1c440492820640080c1e1302455212940450100b80b000c00c4081d001c81131028100e014104a45014000d00d080d91900e040394040140010302c0300d52020010390881109211654400005041243c17416244904012070b80d0041c41604005201b141d008003c2c142051a0902c1c1c2923405407141890a08560280710040100401260504d51280b007040810391210070300400805040c075541d40c81d40c034240d900920a14030024100c003090b0418510351380c4451201030460445104548020b03c148861600300f06500032580480d90241c60810700100507407040d0020b11520721011300799 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 824376825 1250 824375575 824375593
    0xa2c010f11061314070602060712060b09041d0105010605030610020a1a0c0c0303090d0906052703070b0f03010e010501021524041802090a0902090606030402040b0a17 73
    0x440c0c9000c00e50084180d242d00c030002040c20031840380262407045000e003e0814140e11100d00d01d0345130940c4c0c2e42c030500050344540304219840382d111aa007100e00c405101d047c40301910f0008280c88038069a002c080c440c540e01c8062900005040921800d01902c0390002c3c0b06940e0340f010080d003943c20407a5098000d00300b8021104030340d0b1001c615240e4050340a0400519400e28284820707044000034001c46005100300152044644108065841100c1060040003a4080280c004101240a038415000d01c90103000600f00c400702c2500c1c00e881010341d401c2e00c040c146500f000007032a22029911448101c2000200d8280310707040400118180c0d8202000c00d840c83c0d80c1c607001260340d1074020042c3d115076400d500c0452914000c82d030701c0411400480807041ca41140550000781210280b03282d0202422a0041450841c102200310640c1305d41000002c10000500f0f401241c921000208407503c12440000041c08568482c0d02070610520050400e01e6281d84900141e011380350f4903407080e81075104541c8030b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 824378075 1250 824376825 824376827
    0x6080a06080f1f0903090b0c0312090f011401081902030c0a03030302040f0b0f0715200712090b0a14130810050f04110d0203120a02100e0318060a2c010f 67
    0x6080f004d9a81650340b0500d05250105101c0c0030f42110210b0300076400200042e40b0444500b40300ba038015001c45019140c403004040e861400c4602c003442201c1124518801000744600120f408412005c0703030a0f010305030341f11600c00203082401c1e00c105a80e010140c48001f1060682c160b010f8825609468010310065031280032000950082c0203000b01102c074200001070005e0305001800e440103410010101e200c600c28000e000d0b001804140d404098a4080380304814400b15500c6140a1902400c081c12940d04180c0360310202d10503444800b0500c8848000c003602c01d00107400b01e644801d511a50240c0c2192a2100d041e11504210a9440494200b03004240c0c0c6040402d2046e02031588412012801d0b8820010700c2413901402c0300503649405030400d2284d07404e007020024031120841740e018101c0042e115904808441240a105200d42d2090126140c29144810759030030010040311200d0311140d00741c20449083c60f00e0030900403090040e1500c4c012491209420000b42e580903210f403c045c15510f84 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 824379325 1250 824378075 824378081
    0x7020109140f0a0f1104061512050603030301060c0503040b0a0e030d0513090b04090203060a020c0f06010305100e030d02070809101121120108060906091606080a06080f1f 75
    0x81103002c035811401c00400010810724425001510951600250320310178000941100d60980c40762040c4054a1070900070f89521044000c40c9101000080003030741404000f20f80e0700c0c0014010340c000d0140618a210030f00a0400645000b84072101e4800e40d0b401031000b0013000300d0300701c0b01d80f14024418403401c04083e82c05101034807900c41d0900c0082d808603107032407000c8026025206681d50055903980403880561820302c0360710301c50241c2040c0580d072003099032141c0d45061211260724030203810103001407002030710120307000a0801080c08081450b000102d059421031189000448101e44002081400c100058029203800c071012240548440291041500c2c92411a4001c00880e04800070118444030002c00c1e007504003140d560f50a041020b0036548034010b1000f070300000425031104082001030324003080044d901c4100035002e414621003109048820410390b00a050030310580030001410315403958007800080c943c00c1c2c225100680b000418985803206000c1484500f1146d501e001d0034003003240 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 824380575 1250 824379325 824379343
    0x10b0307020604033902100f02030304060506041104030b0702100b010531030c090e0d1209021305040b0601030606021209010e0a030602041d070306050108041e06050702010914 77
    0xd005000790b660f6a80e400c80e603c5d2001700c0305c901d0f54269094000040c4080b581140d100c1c0b404603901c400154038074010041c51004034000d0340100407844108403807807a404820340b90084c1d84088082041d403228000640500040c0008100c941e0003c80c0000a00406c61b800078090035140c3c0a48000039091100d0b501514221844240481d02c01c22030800d92508265055915440300c44a10341003034000b002502900102e90f0080c0c900e01c00d43c45052040340003920541e0000c0c08950001c1144900450000d06043e400d15904c034400c0f950b0783c12010654950545140d80510000c104210b10b203440c0ca0525881202900d209000915141d004140076000060755241c4101c00100f40f41442404001140d601c0280080c013a004602001d001000030003d0010300b02500384c1b807400103808800c49120780e18652006207564200343c200541080681d8000d0540c9812640150001c1500c0c204445d2541d170080244100501d82803404003041820395040d440305901c0c0e4032840300c04401b10102d10350a60307902e03681 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 824381825 1250 824380575 824380577
    0x30411180a061e0b0a03060503031615140c0711040c080906060a0602060c0d110705061605120408030702010e0a0309050f09150d020a0305070902090a0506031347010b0307 75
    0x640c1c8240720003010134014200f031040614020a40d140c42e04082030030340c0c000b100405000c484100c480c00030000100b54502d003190400d0010040000031001007031440e10f026160800002e400900307007080c456151441a80058080c01c01e0107011030301c6200070811030040b0350081c803e02a08022945518003888030a08440c403e84c0140b8454079a4005940c51394440b00511004543c0c50f01000c0700c0c80b18800c090031645005401400151414000031444050500281c00402800700302c1e0f00c8040580c540342d1034209801146240e00c0381d8500c1c0703050340146402d00074110f86110f00d40c001c80030558041490000d440701922460003481c10901071002c4518190f8101d400a0710b041500d0041c0e01707141c000270110030700040c0110402e03540d0707489403800d001c0250040300139160001690b90040c1020b10007100100410fa03182c514525151000380780a42d03c038840101400404100071820345051450064816410000d40400240f0f1480c4041d4507580c510340c4280c0780010500000f1030f4121481030b24492050303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 824383075 1250 824381825 824381879
    0x3070b040201030c0e0d0f051905030a0f0507080d09030f14220506030712060501360503010f0203060f040603020307060e061c0b010e030303070c0305030411180a06 72
    0x1039900550207090801130800c00c20021140081d070580e549040900c1e964000c081c003103031907809802c21030b0800d0100300500d1843c003200c09010000800001c00ca544444c1c2506d0200013034805e00d0402c80d224442d1501c05405000d004c203110340c001c002a4041c00401e84030340c5913414140b07001501036842c0c80e201d801c0162000024040404000302e4200c0c8000220ba07103450050000791035200003450b64000f0750300c4000244250440f81c0081d200341c4154405070070b0900b00f20510403181c50300326217454000d03a4002034490b40c0d0b0300100072003011800301c0b901408000740240710340c50600011030300030340046410603c145a600d04540c3d503810544150310070742c0c1d005000307019070034102101550f50f0034180c0d6003107400101c200701b1b4010725107121981c003440c03210900000c030f0158a44000140700c3c0000c003405034400d03002001030101da2904100340a032815490b050035516a501c84c10061980d00b05130b0302070b94210303480405c141d420b40c03c011100b03403195030414020401c03c0d44403444080c071194402607820002c0a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 824384325 1250 824383075 824383081
    0xb030403050c1c21020705030a05310b0c0718140615090d030e0d11190609050409141917040302010512090f1c0908030f0307031d0118060b010203070b 66
    0xc000c441d0b20302c56134180c5501502d4200c2a540300c51640d4000c02140002510102d0840b0380c0a00c0141d01160031b0144080300740c1000001410030841141c140708030301094500140d00803480105105107402058401045c818403c40701c0b46c144054001e400390284400c41040014455181140500d00c000884054071410040309005005101408000540500c0011010000c682d80c5035030403a42c100c0d205241185a160045061107000d40c090560300005100c8154180721565001c0e1042044030801c803004210205142000f201e000e41e04440b00741c15000300410080d0071521071a08580d010f00c681100301e00b00d494030340b070740e1603a02076404001c1c0011010003880300a2039100307214540000d05503080ea1515001c0a4156207400140c0c0382c0283c4940e03140c1c446403203080e00312008100400c00d43d4081c41c40c1c400e940da50629a0b02c0010000b0f01410360f00c0800c0c9001c41d101081c10b07680701030b4900080200c0041400c120302000c00c60b04045840c0c4d810031004440952001c030503248520b03405003400d0b00b152 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 824385575 1250 824384325 824384357
    0x9090b03070f0501211a090a0b090432071e0803040b07030909140a0e0102041d0901020f030106091a04030515091002120609010510020a080d02040b030403050c1c 71
    0x600c8419889064442e6141401098070380c61281c8403003507031070002d06c40e0329100e07250901011a600400c1c80072080c2ca040c3c240000360300c031403503402e030300ca0790103105901146d1a0381c014500c1910402419a0b090040800703000b00d10380000348100540c0c858203200d0184003101021380c0c0c072080d494001e05429030070a0004010602106015001032882400c10300c20380c5480c0e24000c2c04856a8500781d15400540906200a816130317481142a0510858005d628041c104a844a00040800014086c982000300082c42e41e079420b40c10356911441c2c0c1038203070380e503541e41d103500412600150182c1040803030803602106000c06075100321402c5a40c402c02030400140c60058103490103100030107114032401750440c032a4202d40c451008118880000c009414142090814802a0a0b050300300c10300038844441047c401640000d103080c1e802d036005290b07669580782c2c441d8901c044d0195600030083e4100102c184000c00d84c10001914542d0b03142c60131160780d0041814294458000d42031110003151021800704506 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 824386825 1250 824385575 824385587
    0x1080d05090432060406080a030c1104090f03080108010515010f0c0501050108070306060b0306150a0306031b05091b0319090b0723030403050d0c020f0601030309090b03070f0501 78
    0x1d45802000025243c58649290380703800804080b50202208012a21920300e0864503640e03000101554108100c3e81482d924a0b03503062490000b40901640e00302000806c030183e074075851207041c050000c0c485140760b442c004000400260040300862030754400800d40100500c00c8070300c01c911040c03e08600181000054840b444038031038a40422000c0e20303000c030103d0000d028890080c0000340044c942c091841c03c04008440403600b2027110000c0070820b10105540b04011091040c000c100c0c650368500c1c0208003a40100242c0d4030003089088086101c0c035070304001300841e0003150401e840b82d0b091a0384204441080c03048070000034419560610204110b4000c0854452141d6a1204009800d9003991123800391158115603103030000e2608211080a40c180409000403443c129900d01e017141819078014000780240c0400031010342c0e95000b5610501e02c05c000c3c031442c10034920217440c05545c413420300401c50321041c001c00340307030380c0c106824030003241000510b000898100801341075083c0d007014011250 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 824388075 1250 824386825 824386837
    0x504090506032508190b010e06060c15070f0318080a0c060e031801110c0d06090f2d02011704030201020c0f031201150c1203020c1603020909030301080d05 68
    0x588103d440740080c42a400b008103220030f07161082609001c0c070344008907140c0200100d203407401444112200e40007518070340600d4150780c0b044e45101d03425500c50000c60900c3c003d00a208820344a0038640d95001511051250b0080306156505010300a08800907001d40f54a640e01c0c0601d10302c25040b88011801443c060424041286003940c800d06c002d0712080300b95645002c110110780c00016150652000720100c07040610400c2c03c1001228406000c8245c60301c0c04402828010010090203004002c003a511031703005a03034002559021880d00d810b0041e948085803001c00910031001e8001c10900e001c403001958015170503950855007011542d80c42c1d081e000081d0084055640030300c499007100d081401202600010500107540b42c5804241c40d441c00441a80200b50860012030400a02540420980340080d0000480030300942e8070301c4228004c1c030410030070090502a40c05105803400f802103039034080340d00851b8840080d44450750041c1c0c0701e200a1180648590000705981e040d94025409441 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 824389325 1250 824388075 824388079
    0xd0210030b131418060106080a020d11041401090915050f030715050a0306150503070f090302131d010c1b05070509040605160e2202070813030b0f06010504090506 71
    0x240040040a42c400c1d100c3c003803441029051070004002e144410024015040d0030702d04002c01c001d524055001c0d000703200185c401c411070b540005400d0a0280c190700910303410b2203603003203160780c0d00d80d04c4001c882e618886200b02400204402000108460680240a4400030034007002d24601d18000400801c1d6002e242c500c1e806005021000a203100c3e0445c0d001010056030725070300e0b0340f4035400304010101c824a801581812040e18418582a5400015294450110300340302e01000d2250900792164402580001d42c000210503c1031002e09541d0021205208469040000300240030720703450994000c003040c44001170b1021404c0c003030f400c1c2180c0c422007901d0041082d98003141d20740c0007194158904940544260f82ca51042c44001040441d040c09407a4940c5443c2c00e0b1000580c3c0014145900720070890120b651661210f80c2403020750341250080d40e80049055a07421200602d000c5c802c001d17110555423040100009911060001611481040169620b41c030b410b040c0701095005250141402d9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 824390575 1250 824389325 824389339
    0x40c030f02030a0204240e0d0f2f0301050c09240304030305040b0609041a1b04081c0f08010b1b0d020a140c1e0f0310060609050d0210030b 61
    0x211040350380d4030045008070000c507005a95681810094000414030811801c495070000304414841d99020b071446080c40d1003211240301048050505003c061b1040402a000100c0f4225015a410200081c00400301c0002058090603104904041c202c60003250f40f0f00e01d01d07408003c1c140080c503100d120342c851321644000820075400306103550000740d00211401ca010a50b25410302040c4020f80b04402d900020460310002249050784c1c80705003044000e070704802d07030b8924500812001681540c0241c1401201c4070a41d0721550340d0721701c25540ea1405a001c01442d11804010350059105501c2010700825903241c943c070781d910700b14003c0c2040c0e001c0d0740800c1c0540580c03032600390300c24020b003d6a94918060742c0100000d03480c50230603d000e404040c03215049644401510503181e20f840c1c0c21030402e2051861440301c1d40c00c004005c504d800c004480016458025a241072000f501d03240d01c49010b4445948d40e44500b65118000d00c10840d140c2000690f101309404500031035030b4880d8109000c0200003515035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 824391825 1250 824390575 824390591
    0x1206040e060108010b2e080405070515041e050a0303121b0519030c020c010e040b060307200c010507062f070201030b0603040c060f02070e01150f020a02060306040c03 73
    0x80da0a00e0300a8110345000c1e51204820041c910b800c0098603500702c076003460322980400006080f080380901c1c036480030502c8821000107040c0a001d0150600a24000d0719074110034084003001a4168800e014114001c800080c85014041c400303082881655405403070082d810f4250b44050381d2010500c07882034035070b41d102c030f9402040724a8603c01071210950383c0c42d090b88850680f64a034000000a201d1401098a81110700d04401e078005504071780c044080c2440688600c0a0740803a0140080060642d0800d00010500450030b81c0302c0e60340141c0004603522004140c221421403034a944800c81d007180080e105004500c04507005a2103060301104260503280d40049402213041501d41c5a240c85030468004500c1c401503580501540c03001610481c0c0d25455071605690303e41e410b00d43c3c0c2c040c180c01c114048201e103096038002c000030406444036030b44014482d0b035509482d1222000004450700000e044403071380070f41240000f98400800e50300600d4681103680341001e02006004e0400c44104054441c241 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 824393075 1250 824391825 824391851
    0x130507050d1704060504170a050d140c0a030507031b021003020c0c0a08010b04110403151e0e031b0a03022802130e33062704030e03030a0203120604 65
    0x20b0001304035a07103541c2e8880d85040289100d901d68405900314a802481c04500011400705010400304e0a50500300100c800c80718600405000d2020484880e00c1000100b0040c5608840500f00f41c40c42a6903038402c03c008503181040394000e4010003900301018080c81001c0314000e03006024000c818004a4000344622030000e006424a80d104001c665545c05810103a81418011000d02d280140e50081c0342900c0d59540340e49500c00b82d02040c01443d03641c0210300c0b0a805140580006800b645010b10400c0c0c20920f44940f29400460180c0d460204020f00447c0004040340110006425801a24403920b002161000c03030203603606821800610a401100144d441d01c83c00c021540040301d00088044440583c076103450415500f0305900c09007003402d55200548030544000748912603a52400f5600c400c00428200ba00da20800d0000c21042d89416190000c1c8007041d51081d0701a6640002d40c540c030405148d1284600d41100006800411146071744107404000781c0c2c1c202030080c10006a120001c10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 824394325 1250 824393075 824393077
    0x30a20250614040b010f0506301018110913061a0414010809030a0e030c0d150609020c070509060312070c091b120f090803130b130507050d17 62
    0xd4400b0344482890244818042c0410000d0301600c03138030f220f52442c0c2e400c100010700f090040c2c09402e4000d151f018480c0c10110b842c2c4c03018a5200400045641a1742070120248240407010b005800c0c400c0818001054903040c680135031980e0034101001d491074800e248041c80650082a20080c1c3c000d510f44100142d042d01900035010801c031204c813515202c44c1040342010010030381100c610f041011400901a80003c003004460610440d41024501000f0020100341403402443e00d841d4440002c407410001e02c0425800030540002050b805c1000310380361348841040303002c1c500309010113a02a08091045003890f041254004038020103e0b10b14201f00c40c400d403082d5001d54000c4407000b008010412840c0c6035401240c100da000b10f00726112503c14404018440b070031921001da021602c49400f00e9101c05079911224050380c2061708982c1c0c9103440070303a0ba25822049001210096070400c0022042196460041e2202d0740c4000035020152620040159000040b201500c00940d01c2200c00d131100d00180c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 824395575 1250 824394325 824394341
    0x1030809040b0f100f11150720010218090f25020c0613030c1a03070807180803040612020306030303161115100501170a150b030c030a202506 62
    0x103074810928030100a4020a0203003200040c1b0340315032014808540b9072200840320b50340125985400d10501c1c07000451180d03080e21001034148554400100220315413800f210804034003c050311940f103075032224841d1450440d0304445041300840201c1c140d06991200762001d00018101e403040355507040b0450001104c9038002180e086880200d14002c104021162160400420000301844803141003081d4181d072f00e2200520312002c000710a000034050602504410b805800c24559240d0160f4592480e241c0d00d61003402180003081803541d2144080b11640220f91094078007030088d50964985141410400007040c08100c140903042200c0701c88018104800041c401451030700304124208014240a1010180c216504021580340f003101e0900001190940095114100103010100010885010242c64100c001c96540c004140124010050040e41c0502c04030741c0104090308180444038603900310100d6006100380300303100e8000e01825980c17988421100302d0980b4060380071300c2d07038581c0c08490640c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 824396825 1250 824395575 824395577
    0x9060412020309130b030622060b1516111203090d0c050603090106151b231506091609030b04030c171207030e1509031207080a0b01020601030809040b0f10 68
    0x70b8032200309038a0b0421040e5023240c00c0c40070706845a010011003940e00000600007800d41503d407805418030303444845c0001c2034010001001521201c4024540200101c4131005807240075150184114902c0c00d090b05040082e502c00045103000c02100074000391102c1203400741c525607100040002c040d110030740118820140800009031160900450900c0e0740d40d2052080b0800c9a000121141c038940320704404030464110b456042d549003a0341031075005542443c00b03403040c1c1c0241a403287c49045003071003c43c040c40c4100c5a0306859551036444884a07440030841c0800100000c504101040403403181036006806850200b0b804101901e840c0000f40c6241a02f0500000000e2941e40701c12a140500390002018581481744a5220301010b0361280c080c0c030000c010301c041c0790100713403050020001c940107410a403044820614203a00041c1c01d901088071280781c0d0605040300841c4542c408a0264140d9a00807602e50030000c91909000003052107040d0142c0000035030041c1282681c40800a400103881 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 824398075 1250 824396825 824396831
    0x3031306110a02060d18050d020f060108060f180a2001180510030f320c030c041203020307062d06030807060c0513140a0e0906041202030913 62
    0x141480003800e01d8182900d85555801c200c080d20016990300d402c45010302c2c0d1302da41c0400c0406010703406a50203003409000078213602c01d041d40c1e43c04954001c6000d440032000042a2030160307030b0700c00c1c1c2d85840e1103040b188900d08040ca0300014800502401444140b0809842111380309181c42c0d460100b00040010b039080a6400e040c618481c035a440b10506050100e071021034500503103080d01103044000b81150610501d5110a5080008040741c1d101c5142801104140d0b50203070705103e944000100b42c1c1564054600042c00001c401d800c0e42c3d4100c0b13000d604004041c2d0f04d00703490108003024401d0390304000c40441c00104010780c00301320320b8010703c0c1e09904114401001c6c2001c40c02502c04d810f21881300c0c503002074180101040411410000c0c0e401081d00410040740b0b085900004441c14800c40420125803150701f1400b00e8140000c81c000f03000100c059846c0100c080d210541c000c000300c000c80d0b030a09154040030001c0d00180d8100c507100f0340d14000b40101c03410002d078600021070810b0001821040c1c969 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 824399325 1250 824398075 824398079
    0x1020403111002070603050c0f030109020721090302151b0c010e010912020d020a030b0f06130b030c31200a020703080310030b071718030d0f0b030313 66
    0xa0605482100c0d5031048994040c00882d004000e91582904c0c482c40c2d0501d0340e00d400003030011140c1c0e0304a40c0c10f05c2d1649441360781ca42e1a0039142c0d00035008490192903901f00c401400d0181215210f6220074011075440714804107295a00304503c000008151005145080c841e0b6000e407081d11411480d0744079282e01420710808078800041c080c10b0b1100d1458108044003800b0407000e0030004256501d941c06071a071442003d0360b400405d00302106580010615000b43c01007105010b5091071250080c1412215030101644814609042c1d1300a940c1340c541c550400611005a03280030400701e503030040d02421034040003020400380003084001041c642086900c0d00407018103d60088003402c03903414024080c1d0f042200c8a940296120001d00000b0070005001001c108480c8208011800031640950245518030b131410b0000c00c401c0711400a180d0440303080010917026060160500440c180c02d00c02142064510300d01c0c0405000040d6403403101c00d0f5510000d1129031003e000070300e41d8020021550200d64 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 824400575 1250 824399325 824399333
    0x825060c02120901120b061b1b01031a010503060d060203130b010b040323030408030f070605060a0303020c0d1401090f0c0f0b0d0b1c06050108070503030309030f0c190501020403 78
    0x1549018803010b00003080301c0b02d007a03a04014000320440001500007516000703d40030411034421a43c00381c100000c246800500020006082050310030385005140c100b0110314015000d0320582c1c0400d80e01900324071282e01c89944140081c2d50703c00c034000d28125480e05d0035100e00040303901c00d5501c40c0001001c40f030b481060000c0a1150780c01031900030200352400c2d2070364454032440f006862545000c07008510001c4012801001034601070000102680e5440b101020701520f10740c41040e0840e00f040c148400542d0074079203007405004a070b0301a005004020455410001406d030208000c0317561980d0160103c618403824820700a0251190908170440c40d82400c00c80c2c00c002e4203030700c513403403a00242105208034a40c2000303460a60a100c0e03000705903040004005030500e2295080c0c080320301c2e052280107040c40704a4000c90b0480c1c02c400c040e10860740d00c402c1856201d100c1101d040f8000d40c42000f40c5910340e040000282078807291002a1160032a5102c494400e0098500080c0d4080e90045000c0c410301c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 824401825 1250 824400575 824400583
    0x60905090f0313050f0621160e09061003061a03010504050c030403020a080a2a060c1d0f04060f0e070318050d0809330a14040825060c02 60
    0x3400c45000118140b000404218100f440c5034000d4034011841c1c8410300000792624400c1d01d00f11040e9032a21030300e1104d000c40003030364000c3c2122a0310580e00c0c000405281140070724402608260050300d010340a070b840406005480c241c80104100300344e964000024101c074504205640d114040006036640d5140c02e0070401030320350103000c15046100400a200001e600003400012990f4825403417919900800c40c2500d0480d090500340448001c1c1100412680505200e41034255100e04010008001010400c4a014450b14050700c444001e01d1551803e521302502020030002d4000c001003121030f190000c83c0d042030120383c0072040e64001e0809000d10709170135010341424601100d4425a10003545d03111550382d1001e079103410b030905c2240804190f001c102030000011288810814210751a290360342c40680e480201d51a80f40c070342079038010411422083c01040d05054009a103540e46880ea52034805807584580f001080424a0b5206160140480b00c0c614441c14052440020b07070140030003019040c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 824403075 1250 824401825 824401843
    0x11061306030b1521040f120305060102060c0301210c0306020f1305031f0c090312020c01020f060124020f060403080402041508030a0f0e090108011b050a090308070f0606090509 77
    0x4682c0c1441035048243c101d0951604c844d00801c420f10140e00c441c140a0f591000e9240c0140501507403100c201010782d05608006e0294a0070707401c41d182c0b5525130311000d0140c002809805424480f119000703809410510f01c201d4071501510781c0004c0984c0d40c2d9661030032a440038080011400340031402d18964102c1100e240010300054000d8034003802c03c21640c0d014000440c1200204555648a12441d01d1080001070083e43d8014010a0f44400c80c490103903440c25a01145401481046400c91070280301040f8503040398039158140103004903118090395a12051100802181708840044140d003c2c03c222090099020b9181c0102c01d04060040c40107407006814504150300320b0316410480d8020000840f150b00c4040d28003002d0003d00300004403034a900020070560310034030002c00811606410b501170b940400d110311089141420301e03e41551a80501c00c00000400c120719000c0000c100c402c0014419188101c4508200c098180d0300d03d070490381070340c200800040d0b6a03c10850710388020044180 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 824404325 1250 824403075 824403109
    0xa031d0309030a0305071a04060b0310150314032502131406090a060e04080a0305010e010b04150e030109030c171c0e0a05060901020702030c0a06080411061306030b 72
    0xca0610074101003641ca8042c1c0000904000c0005112000c2c80240d01c207048240c1c2041f071001810781014103000c006014002c1a441c443d000701c89510304810a00d2003102d48010300c614004508524603116034a1652151031560042c1c0070802c100509014514072030404055040c110452140c043e0040c05505c5460386038100c1058070b0900803a504031107101107030781e110a04503440815551281541c001500b515440742d20359400e010140000c102a00c00074208083e8155410000e581e41e54091609154003842103000070b0004000502602070f00041c103050076140c50400104400e0510013080c2141c11000080e030000e05801c00300010084000d00e880104000b2941345401d0030200701101e6400840c103a241c46003c0e90390a81e5100e800e40a03c100f40c06690844180c030b10f07a250040c40d480c080e612030360342280319000358004000203140245083d410340d00241c0d20207410f0743e1590342c0e07100c08440c2c0d00c02196000d0300a0181c80712113440030011700d0182c00301d550045003081007141803201003a05203050f60 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 824405575 1250 824404325 824404327
    0x70608010605090f1f12200d092108100e090309041a061c0c0201050103170315090109061e120f0317010e180a0c23060a031d03 56
    0x1210a51150658603900f004540c0344604001d0a40000c216040c022403007105c681d045e0054410164000142603418107132148144462800388500503c0120195a4520140028444808608000e83c03000480764450b840e03510041507a40d43c21584141d4940d003035000a452241084101d84659050000800c0c5880d82541c85007032410785a0740320b01410041d80e0140740c0e038415401086102e1004601c8060024111399030768005e03060000c00e01140c004441e850a03081403200003206105101d41070489030003052108402c880e08408081030b5001800340950000c1241c80b400032540d6075140f95001b070200190004145107003000d06564101c40130501c000d0151011400c00001c0c0c9484110036220303078054040b600000341440d0540b9032141101602d11000d1100b40040380e003011064500c0d020b010300c04181074a1800361510641c5e9072210590003070150440400c104031017202c0c060b0005052030340400e060004449000800d5003a00545803010000303881c1c3d646105010082c4070b000700c440111314003075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 824406825 1250 824405575 824405579
    0x70b04090e060f0c0a02031c0516090605030f042303030916140d080f040f03141902091801020c1c0c0c0e070e04020706270f02040e011506020d0207060801 68
    0xa40683c0d10010b281002900d000511a55140e1090040307580308000548000411001c84450300010001181c040803403c82c0c01400d03128a074000c445d40003c07110503075115032a5903624056143c0488014004030b401c500403441c0000c0c1c424000103079101c03c040c400003c544074035042e00003e00d00f00070301550a610300c4000005014000103458141d071888000e40b00e0200b048080d00e0082140c1c4a0000050700700800030a000c1400c1c00315000351022a40900c0c41d80d200c0e9110346040c50f4640011000c4404055010030b101001418a00746065000700ca00002c00c22900b02e0b81c007885d00b6640009032242c00354004042d8051041100c84414011814070302d04221022107a46e500f0700d100e001401a14805280d0b6400650094800c046c0c907880d142000d081952290101e14012025081001041d01061008091410644000c000d5841500c1c3c001008040d8182150203000c01000014a408159521a10300500b000d100e140c5104c01028540d0003004040c2101c01c0080c00c111840d04442c0c1045110001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 824408075 1250 824406825 824406841
    0x120702010c2714120a050c0a090605031c030b030d03020910050313060209040b210d0f0e090402180c070b010905070504170f0d030614030a020306040b18070b04090e06 73
    0x810242d4904a0400f445216581c0010b868a000000004080e200d0702e03410604000780407603a40d9200009807180c00115446052060948600d805000d41540c849041e240b407040b560b580d0000c0c075015500b00050800d590401107401c1c482c0c00c01184020a8000680f41c50904201080a440070fa440c900745003507040c980816050b2070401100500420380200d182440c5036503950015801c0d0030001e04003c1c00d61043c54440318620610403480000d401036180803140e082c0244100c80b42d0000a96031001c2d5030100d0010095203810103003040c2c2c0c000c00d80c900c01141c0c0807c40c50016014440360b5070030700d07182c01c400c3c54801c82822050f0405940a4101024061385540010a82c0c059440c240143c080740140906010318084906020410354411007480382d0441da0581c1c8044181c583c20b03d010401d000a800905540e8050017000035050342c021400600421001080b032600b1804240d40c507085210382c6a80d040c54400035400c50140d052000604002c400b4451081ca022080c4001c090442032500c411 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 824409325 1250 824408075 824408147
    0x91b0303050f0f040807180e0607050306061305031b0306090a03080a051306050c0c0c03060f0a0c020304030804031101120e2a04020403050a0c29070305120702010c 72
    0x2044411024007207010f010080c207201c20366000c2d040400841c1ca0080d40c80c0c58450f5110310100300780340c18614154080c2d004072004944039106042d1903d420780786464007001e014080d4850f404242016440380008140b650303061090f0b603045400d05d140c1d080114401c400f01420a00058688030711507201c5881400080d130800c0009910441c100ca001a455944501404500140c50340081c107a9103003004011803000704101404003441400102d40e03460502e00c0c05d1542d1200192903443c1240b001c0000140690415080700c1001e004030f00c1500d042598a51391404150829041100e4107450540c504906507800031400311200e40d515000e02c004440c0c000c40703545981500e1404074584200225203118100441e2038180b0351752000d801150340b240e503410159160469510300320b0303203816605800104191710541b14010400b502c100c00f81c1017200c11030681e0f0143e0100004501740718040c00200000403041988610541c000d80021948081c95080245200c0c40b045000e031349000029062241c0c100844 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 824410575 1250 824409325 824409337
    0x120b031c08310f230105010b0a0815010225140105190806280905070e0108131509050114010f08070306020310120f12020c010c121e0201091b030305 65
    0x944000c1c2d021403d0403c096220040320b40640000258054041c9852481580c0c0e460428404003c012998894030303680c4c8a1f11440e07140780000b40e00c0380d0104a850a85062004c4801c0d014011624040da03c0030040381d8510000100100381000c3e20020855464201b0a0f0041020b00740f91072440c250000c920595050903610101d010081100000b50300e640b80e2224182102e042c1100440042c0c0301804c200314012141c0c0100c3c54090f00300740c0412940ca0180c04400c442c160161119a007d94842e01d4800149400d4002541d80ea920401e00307408016903072107410002800307a4000b09140c03143e015260300310b00c0180c1c0400c5100803404003c0241d8000454400c050707907840b02c000741c0d0341d440e1203805101c00300c0544c014602203002d0b903410314100b00b07015030940301541c0b0504514040a8540006a03141c1c0b403041c20b1140810080844040080e030050664044d400c8241424070740d18803103001c001c950380842d104080144c0c3d0740c0d004140501040d4161b000c5004c0e00c5408054150f41190741c0200140695 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 824411825 1250 824410575 824410651
    0x7060b0f091305101e0e0304060522230306061807050c0102040506040602010e0d030510030b0c0c070906050109081609020307210204030606081c120b031c08 69
    0x30b00101c41084014884035101c6924103005100070508030396001c860098514030b40c0c004610b0b1505550101e2400301c2034034200d070441d0f25640d04001007400031044c0898100d0602038008200070b00822070f02c2100c0c07280089000e42c0c140314000c1603403000906107402e0028000a203d1104000060b100c046814502c0d5400780b010725041d6120b240e00860180640110781006900c81404034000c25056415480240080310483c1180c6002d40781ca0020b40840314240d804008041051070144082480900c070b958000e40001e03e010300d8800300d0b29201e0308010040d00b1010b1070540310381c01000390b0740c0d01100c104090507c4102130a090340d00d07850b204500c01441d120750001c0340e4004c0300182c0c0b202e00035404640614000d8003c4c1a03080c8000d5003801c001e5000f40000c584031031078142c01180d01c0c0d03000121409100415010320346003400924040d0340245468441030704068640842c1c021645082c0310001040f9044800c050351003104d4a030151203c000103100760483c3e142000c0054070020070041d16040c2a110f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 824413075 1250 824411825 824411851
    0x41811010306080a080c1c0c030c020d061406130b0607110109050a080d02060a0c1d060d14011d0f0118020f0a05090a06230c0703021507060b0f09 64
    0x21200580181819034000866801072070301913000e212000009203650745a00c4150740f004e03c1540d443c844100098681d180010310100b41802c0041e00a00700310540c00d00003481091183c88542d242d005842d841c0a030402151109400c0c031206013041110710030748005000051140080100c08204140242d10300a4000305101c018501540d008451a0340941806007440e1003464884154607500c40000009100502c50880029122000c80c40340b940b030020f585c1c2d9a907106001a010803143c03403040c1100580d20402c200061035a8160b40e20500d02515081c05c0f10060075072401f80001000e0030600c0411030040441c508000440c041690614151440d00381402031001074440c10390000c1c040c60480084c003242c0010400483c5800c18054180d25208031380d2585025100c0c9001c40e481508001d02014140355850072111100440c40038040c00d0311204220782200740e894001841070b400141d007a04030090002209001d00819019000d0901401d4801c80c1c0340103007103404200c14120060840c601010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 824414325 1250 824413075 824413103
    0x50f060c070f080c060403260601090303030b03010b0406080a11190b0f300610080601050c150109050118200c1504051c030e03030a0c05040902120f060418 68
    0x3c034a80548041c0050302045544074641032030003030000001c0c01d41c072219100d608005000c100314a868102d10502060351840350b01c52a43e6016006800a411003d605540f168011400341d150b0344210360042403800020041002242000100412050041d070f0184000343d401911a90701c60661604503240c140035181d0b90440601402402e00500350081c656040c4481e00c0e001c03e58005070070101c04102507500d0700c0e094848804200713461100e081c241d00400c0f02c40d400520380d50701030300150030540340d11070a44080a0390100c2400e20300c2d000340c0101c030303981d541d0fa8010f01600300c0200c01103146845c464070030807400c402c107a0340703044210302144034250382c0500040c000344041c41407040c0690300d400542c924645040514103551211203420600744440307a6208134030b002c5440781c0500c01c103828902000d18650b441e058201c0c0050095426140d081c803404020004c4d01c0005403006020303080c00e00503800c0c40d03030401801c04000c9030406012a40714a0401203003000042c51000031952b100d50011003449410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 824415575 1250 824414325 824414333
    0x1e070f110d15020a2d14091207090605010903050318060f03070905010f03061d070c05030a020a02040f05390a020a12140d0c0e090112050f060c070f 65
    0xc80e851100400b61280603550b50105041d580107030240000988540300001082e107418620b0345c03503017006020045114040c42070360b140252030110541450319074541c035100070400400e008030f005e07c5514031154080c240403c185001b910908001d810b091038100d800b42e1560300c03510b640b4081c0d8030110940f4222030800000747d580d050b00301ea900480312129a5200d240c003400190240f10107204090128103079201024441c1e01c03070311601c810345001c25950410340035605a48550044003c04040034014040c1158020900400241c0001a001e03070091181c8146032041c0310584034143c1941300e14070304202c1072100035042038001528030025000b116040c0c0d000350031012801c204102c1070a00240d03000030100202a400305500d0f026600607420a0b10102080340100c03803004022444034040c403000d011050a000307580d0006c0c020b40d400c178544000030f4400340b4009900c6550a81c400c054101905100718200702040c030844c0700c00140503001d801345141c000064149440ba4003030040400d6040c15483d0200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 824416825 1250 824415575 824415589
    0xd091d0619030303020309060105090915090c040930120905010f110a1103121f030b07080906100630150302030712020310090f14031e070f11 62
    0x124000741c0c81e88109075a070a0103002035009452040300c50180a001050500301495401e0090810000618000303800600d900c490720700c060b103059100d0040318100b10700f40e0f071640640381c0c015004107000000501c44408480c0182d001180007450610049030412900f6084442c12022031020340000c9507815280c501240107054070b4100c41e00492801d18407018030b1101c000039048501442c6c50340c0e26189001c040195503802a000c0040061820f4000160407080078134404c103030744c080000003081d02c603200d6803003940c2c0c000c0894802002604540402c00758403020040c454201c0c401c5000d025419080038402080400200b00780419004500c50403045001038800081c02d0140d001c0f0104510303040404503120048091006030310a01c00d031400800c1e03800d40440200c1c905507005005100e00142082084040c252041098400c3c01021806c0400324601404402048018401641d0b644845040844400e00410113000714403100b0302024000880900e010302001da00004040f4032084000001245 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 824418075 1250 824416825 824416849
    0x1030e030705010c0f02190c060f0908030a051e0304020a3b0603150c090d240b0a090c0903060e0f1902090c0703050304110a090905060105030d091d06 66
    0x142d40c6019440c43c000c540c01205030301c0d82e017001d6080d10800d8000000088041c0150800501b001c17514041c104500750042007100742820f6103042143c1d1f002d58540e560ba041d500402d4803500819000108007810700381504c002c140d0850082002410b40c01c041d000701d21500240d00450305907024980c89008840c02041e04200400030008181c1407038401d1608401e86480142d525174042e00c68000f41c40d104035552070b20284605004020207041507090340c2080030004400c081900c0303040080d0207074403d000e80e2105042c0300803280034010031014140307000e0080c42055584403408030b80c50404c1d00e520781c1c0e5000c41000c0803a9000200480c4095070309080600301403089290308928444c41c4048041c82e84442d21a2400b103008986a22003960303800c003010300750f22500e800100042c81c100700040008002503080300e01c04402400034003407252102840300890350b80310401d4946501c0200100010310b810400c00e42c0d818005c6c5030011101d480c19040001100d10034035001c200c00c00c1c500018009490726603040034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 824419325 1250 824418075 824418083
    0xd080415110a120e0f15010806011d0717090a02010801050442061205091902010f0e0306070c020306151c0f081c050708012d0b0c01050907060206100501030e0307 71
    0x3540d82c803507806055940d0100d0003806c0e44101d028000145000e4080b601c3c0303040303641e03400284000da4030001995060940080c8100140491020600c40d03810000380e101748140c0000d8020005504240009403c44105030b01603803041d400d00e04c042300d610451240d06001c131a030040705400d80345100c4084455003030a0300c00800700350084210002d21107074001914034078108582030422450316925041c1d41c0740c941900307004200e603110ba41007000652040494a844441c0c0c0d10b40071b6200640d1a0020381407600030707074594001070079403030701107040d440c05000d6a0740081e51414128202c1c80d00401050b80d1283c20f04000d005d2418220092041c000181c8100d519540e010351803542d0750b000d03604900d08120b200250411964507010008081601500c8014140c402c00d094070b034081d010b2a000907a070043e046801b41c04842c0c1c08500021400d800d40c02038806600900004922481d1500b0714500d46000796122501f194869030a21040354010070b48113055a071b00703280115480c40480246880d522990320020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 824420575 1250 824419325 824419333
    0x903090902071a15120d020c01050d021c1a0910030215070506040302060a0f0507170a0209040207080d0c05070314070c180518160902090406080d080415110a120e 71
    0x10003000c02d49100c5608132040310210440c60194030b246580d07070141168080568440600d1074500e60040300a4424402e4001c000b500d1321210000d00b1207001d1f00803d0303403461603860300d916545191241c0e190180381e510a0f501c0010078640710000c08200501440040d0142c0c1c0c0510000740e06c8070209080f941007682080c1251428205450000e656232012150410603610301080d01c6005801070040314050000c1d5501c40910050841c400894450040d01818245900300180c140e19150303030000c1c081803405441c0098946c0c000080d103400faa60365401880420904201440020350006282c030300c00c5010800ca640c0f0b07021107180005001c0070300d4114000c030021b8405054030080f1180c001d10720400240b5a14001104441045d554800c8022484610f4010303001b0140450078066000e484c1d05c0c0f9008001188095403a480d050601ca6400c44480c00075010000300001c0c08a0024032130b004400c104810000000032001210031401303414114020000305440020040d051504907003280e10220042e9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 824421825 1250 824420575 824420581
    0x2d02010b06030906100509070f0f021011070204150b0d0905010b0402360f04020306030a0b042303090a03020f0312040f0501030506190302150c0a060515040903090902071a 75
    0x5540d01380c204e5085410740c44030710010440f810940d91180c0a0401903c0e10100c4801981059580c00081201013046100b25660190066460b00030502a1525075116561b0340c4d0450041c0819a100c1c601102d039004503d100070001142120115044081d41510004103035034146489400b5001a45005503c2400880d05200c0300341001c80002c0480e4040c1c0140c0d60110303140610794200390300c5c0074204c0d0f440380b501100c0950074105500210340c070a000506494000e40181d80700480c007a015902030310400242d0308450707074840004a0a200100c0c0e450003c500b0510b842c0c1c0017400b80d0080d404000d00030700482801031100e4408000801c0c14007104c040b401d488988400500403140390520030180040d007000c2c04110b440c01c1200c96907103042ca001c040c0c003060509540920104031038808040040810800122070941e9043c009240c0030780c41028045698100300012803078810380c0c02d840303d100c4c80ca820542d40c00a40c01142c0b00b000c403580c0240168079104036092102c04209503610600c02000c1840c10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 824423075 1250 824421825 824421841
    0x201180b060d1a1005011e0207121a0135030a030903180b09040c09030f020d24020406200a1e14060406050c030c0406080c07080a0207030201020c012d02010b0603 71
    0x780c1c03095420a0340c03903e87c083e26150010f41d032040b440303000c0009a08070300000e01081e507640715500c90031030003136a03018000c6044d500b034240000c400b40e000c01d038031109001d5540c0040399039101601151140c1301803400f01542441242ea22882511003200034503a56035010300826004110100c6000300a00c07141c0710075580c0c5e50b440070b4541d00200d580c43c03040d460701550103800350041c2c400e0002d80c1d030404200031070704840340e080c0800340c14080d205555151060a4012660190b01d14212000c84900e80c0962101e06c6e081016040d100294091901c01d011440c410030300300380c00240c00408641200521801e4244001000703010644000d010b04a643d130f00c0003061011800007140c0d03000b01c0c812a010049551002462242030009403298030350020b0411003040154070480d546900a1201c1141c113182c0701303c50380c0d420501e40c090b00075080560010f200c00c10940d1380500143c40710170310a080840d041c010b402e603907520080340c5518a045540e401450003506074802d5000300303401600544415034904200319 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 824424325 1250 824423075 824423101
    0x90212060415110c0a061523030d03020c03030610110f030705060105030706021f0b09090a060609110d09081b03040f060906080c07060b10030c0201180b060d1a 70
    0x801001d8100000d2082086121044808135811100945201c50786665481e018050001c5e00340d50050143e0b4011034551104154285488101c025a04a0001000030b16051080c03014260090501c18050740c0c60817203011080300d600c04d02c2103a80d8490a070b288402a00e08850361000080035105140004e0001400040248038030b50080084801580c1c1c0c400c20150380d07030801d00410006030850038640d42140c0c0d406480b610076000300440899811524000314028410440d4502280d03408881d44505103d0144250005426021130510804003002c50504043c41a0600043c030030307680780d02d410706108140c2d094540c01540d400d1248001d98a20052981e030381c0160041c2030030042c3c0d425000603518040c62100003158490340310340d031155540e80d416a01d1600000c2003034031859254513410307905640c0d848a9a000d4a420f803800070b290720460394000d00310345005da03032422801c10070161f4801107650031000302d50107041141e03140001c500c035180c08508404614a0001c01c80000014000040110a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 824425575 1250 824424325 824424353
    0x6120603050607121a06190e0d0609062405100c06020f09030607111e030d11040f050109030b060d0218010e040201110a0c14010e0315010509100605030105040902120604 74
    0x1024045200200000c9410b00d00040e40c05c0c0e4444000c028480c2041e1000100189008441c20f040d00801030030004184d5071007640408070b0b4890740d1030071040308001161140d4200020a0100103c480a0713904075000c0142c45401014407802505141510883c07249910032111940044d0640d1100050002c080054000740249440780c007610000564003407044880c1e2070034101080041035071028280445410580c0c0d00041c0f1068081017108014160480c000c0402d20041d440a84d5070f140c3c50b0102d0303c008410260445410000d0058041000c02d041240b9640c01540403600e05e214601c50f0f20014100480010f81d0034090300c1804000154010003440503817245000380c072510b454a405182d01510340e02c0c1d5443c02000b8903480d12050105160848400305820410f051441c030a5400000007864131444c0c4a02544010318100180714030305103030140c40c2e040051000d0708817003541480005480da0005004580c003441e6581603510541d80c5c0c0c086101a0740c1450000d84100d4100f60420102d11003041c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 824426825 1250 824425575 824425607
    0xd11030c0607080f0313020612010f0503010b13020a0513120c0911270a08070f050103060302101206030804062006130f020607061b110a0c06120603050607 68
    0x504122145414001c0803100701c0c960020220349018241030101610f40c0018281c1004880110074400c01078403908010b051550007240b107a880c6626100038450703d084e280d00441c0c001d9051002028017500ca8020081059a025602584640a140c401c9605018010f0080c07680402154001101c1c1c0717148e0b4602601900645141850759114151903003642d90480da084142c441c20450055071041e42881044084101409550030065441c005a184509500000c0c1a500700c40010400b481448406100401c802e0074280310306451500083c041c900300080d4001400024a85100b000041c2c0d0710280103140c0c4804290340356074840320002c04d0840394641540c9058100055103500380c1000441c07902c41e140c428285d15011078159560003500c1c00b2148105c1c1c1244043c040c000004004c4d0245c80c40170030f500b0380d08050309484948002c001c2e0030880b0414031070740c00c01007140011921180702103017a5001c0b414002d10051416a0354401003200d503102501038083d80060041c40c50303104004006ca4500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 824428075 1250 824426825 824426833
    0x70c060909060e040210020f0f0705010e0307031205030a090c1202010e0f0609011214010816060804170c0312040c0f0b031509041406040312060815010618050d1103 72
    0xc070744206003250303064054861a80d0040c8000307001481e1404550700d010340d0324415500b40d003102045591824414a41100c07154005280c2800207583c005003841801c0c07422402441141d1454885151200c088141070040180000c0000c8403060a9003262280ca940b040315103e0340d564940d11401c1d00c501c90017007240040ca15100171502440c00080038080c4040040c2054a4000c0e028015501d102000f00b03e5480d254481d1030860102c490145014020110480a070000710301180c0315800c0103d640d0061800c0c41000320030322000c185500201540b00360902ca00c45d0b40e80b1803034044946035008030a1202c003554107210402c410061510903060484451880b18207007075031a480700d000240801c8608050094011994410a1400f0448550000c1c0101a21210780a1420300c45003010710845055000c12254406e4014030121f42c030441009000c0d44025000751138000004000d100018401c100400c60030201d51000b0340f00c541c010b000204401088041c450b84185000e065603603030502054400c0c05 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 824429325 1250 824428075 824428079
    0xf0501020a0807080907170106230f220507050f21010b090d06050604111215040506011d01052101080c0328081207121a2d0402070c0609 60
    0x201441c03149000e031020700040c2503210f050150700121407206c420580b8048d0340300c0c040050b20025400340306040030190106444090480001e0042602040c03031a18051240b00348000c0803030070740300c1448000d23500070038010480d9140c40d00101c0f410300a85500d20000c0d4800141c480c82040b01c8a551500125100281c1c0369603030f69000e02d1002c0d4021440c001e0b030801d1035221030400240c0396a102ea5031203840100300090000c03000a19450700d820140d40c042d0541e48040c18410042e03141c0d503110b039080d102243c0501072840d280c4002800c04110a0f44c1c800e5030030041c500002568000e0f020b4884041d07a1300c01c4060005075581d400a4000820722401200e4010382d4898861782c2404550300f402401220302582d030206903242d400c52070029000303017618802020b006404211840014660081c1c00310750b101c01c41090b500760740c42c0445840c0c038401c040080d010300d850003454030b44542943c62010b800302004161650020840050180c841d065941715200007001c004001501525409941450340c0d00c00e003050b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 824430575 1250 824429325 824429327
    0xc0904021c050135070f0b0304060605060313020d0303110a09050f0607030f0f0207050603040b0403030b0a15050f04030b0903030f010806100506090612012619030309030c0f0501020a0807 82
    0x500341c8418030f14070b2116405484138002c0702d214000000340c030042160f040c299260394850701002140c00408400e400003060106001c19800303040d010307040850f1840e15600744a050030600c5295504000d00642c4520102d800307060182d0704c00c3d05201030580410750b550403010401000d40106001e0340d4454066085840740f00e080c01d0040c0ca81941d4162902e5050300044202a03030660300c408408401c40c401d50380045001c0e00c3d600301441c0114407070b038195044c50030f0a14010301030380e004505c5d0703e004040080040008582d5607400210460180c14641e685290640501c6214440e9800c043c10744400c1e00c0501049290002c01580b04406d080c0c4070301d640da6280c0f0b4240d902c4a20a4941020301140840107201d1440d1001c01808861802030000c0d142c0110803008055102099100164800700d00c0f0410045daa507984d0024817612440d40501030008104c444806000786000c1c02408041d0b6a01c0c0d2007040501403182e00c1074840c0c2082c6401e0000c1200e1038220b001c1d40c0441042d0300081c1c1440c001c0703000a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 824431825 1250 824430575 824430599
    0x20708030711010e031e030d1112061005040911070b07080702150a09061503050f0102071a0c070804091b0905011e05040506040815130209010b030c0904021c0501 71
    0x1603000c1c80c1000d00446600c011109001c13842441c942c5030140d01525415200201c10034612144003c010b9070303d8110594010702240c40d00c0d100780c0003000081020304402c001e00c40e03420350301c8107044074225005802800101c0e41c0d030003550444807400f0f20300700c4141c41c409210405820301c140301f6820101036589805003101d8402040e90a000547c3c0302424440c0c0c080c08074120154401c5003484005004c00e4261200e00c2030300d07804c01100c5a0092002d40901c00c5c48014031102803814000d000035494082030740e41d07010480e1050001500c002c4030607800324101c0f10758031003266403081c0c00641c801c1d01d8640710071080006005e052842d0346041482c4d0f161a6210303004202050440750142c4400c511200d5020304103000d4000721402400308602000301042035a81c00c00038101414404004203120303185074811180c40d030000740c14485a1810411081c00580c0c50404460544205000d401d4598503603104050050181d840c440fa80303e4004203944040700940703414580b030100214410300c0303566a82c104070820 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 824433075 1250 824431825 824431837
    0xe150f010b0f040e070e0d031e051305040209130516080901140106030504030c050706021e0c09040f0c0801060b120601080402010210091b0b030405120307020c0f130f0c02070803 78
    0x107a032050004101c0701080c581e03113540c0040c90341000c2d40440d0004000480351801048210301140741c1881c290000603010120b19004009810107909d040502c10020451001078801c1c140b0032030300042c26505540f640c284119886a95000c14007441c1400c5c4020a01107142c1c1808100150b129000258504014017030010203c074010140301280e400e041c42180a4000140103a0a202104040400194081008100a0140343d02501d50103651060b640786416a01403081002da1280f0380900060352007002c002d130044d51029110400d80854500311142040c550300c404507951030540002802010500180843d001e030340d10065640e910180152200302d404e0314081e0059201550700482d140c459405019914041c40b25032602100313442c40120132801d15017100004040210a00c42000170403c03070701d038500c15454150b03821843c00d03100003035962121040702e612440e610010354074181c5800100d50750041a24901703200406040c040a409817080c1c40a1000622400c20006914000401590b01c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 824434325 1250 824433075 824433097
    0x40f08150a1a06030a1508010b10020708280606090504030e3a0212032206020607031119020705010e0402160b100b130312050a021f0e150f010b 63
    0x10030b020309003d03c100740e000141144000c0c1d54400721032603a508207860700343c01001c10308000300d810208803007440301485000d04c01400b507510040051010240108a550000d003181010b00840c0c0002c4110244019890b040506000d14040c00400e580400c0e130400f074441c0c2c2c02500e0b05d041803031180c400c2c004403264a8500e401c1079a45004025504010074111002d060720600500c6001151500011203e6400714100c1c4015440020107409910150410b89031800074544141d08032454101c020352104401011481010707590200c05042402d01401d48510074140382c030314045d500c00c00c20b01035611409409918041184001701ca0700c141f030140200c6d052010120139082e6090410b689080c01000701410441c0080c5240700b000c281c2d00780c49800f800d04d120104030b411a00b0341c5103041103843d0064031928401080b80410800300c00703030b800240c0100a880c1241c5000c484900400e003090060103c21840d4030940502c014032442801aa80403a0141c041a40304284590b41c5004015a0344100401c0ca4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 824435575 1250 824434325 824434361
    0xe01020607091d0403020c13021305040204030f0605090a0c06020f0f0d05040521121c0603030f081b0301090f0f0b030d14120f0412020606031011040f08150a 69
    0x7001004034076500135000b41c8a401203030b42003c18080050350700c1c410110380e00f00c120343c0407601c40c0010b071998000400400c410b0304c0442c5045c1c115102c0c1e20300055010805400039880700081907900004200742c1c00b01503000b130700548440351182402501d4900c1501508003a200f000030300c500c6914040b0314104221500d0b101c15141c180b801c82407114207510f0304500c00c54060349007141c481c00081401041014088644000d540d20743c0d000f401c14030700f14400c00c40310703000d80b40a00500001c0e400804403010821107040825155a0701442c4401582c0140400c1c4400d80010000281c04101508484d6816040d09010b00114101030000b030211079099505942c5030f8030481b25550940e0190f441c241c20340c815031400e1403030002c078403090322000750041e03e442a01c00390741e000304010300000806690300d68205202805075401e04200280d41c8044c000c0407940f10564900441e1000d60280381214001d0800f6404951010742d02d20005844d1070b050648040c10b414408002880d020107407042030808a50b144240c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 824436825 1250 824435575 824435609
    0x1008070e010f0504030602030a02270108040611210702010b0409020f060f0c07080706120b0a03060203060d05100905060f0f040b06011209061505120316050c100e0102060709 76
    0x4440b0520341082450501000b0007022001c94854002948101c080c0003000da038401611517800c0f800c0d5a07516081032420100c120f10041a0fa000951a070880e40000c0007040307014142110700454810090340900e200c450017a803441e00482c07131000070311501d2560001c0081c0150401070109948401400a50150048800004900d0420080c2072040c558180481c2802e292000c00c0c0d19101301500300c00c10a41c41114200b01583e40a114030785250440b11050100c1d00090700460800069800014690798000c0000303034050312034030905004507070007034101c07400c0070200c40d4503000402d00484181c0b6180506000206803203101a03040340200d8280f0544000307660307503031505280b038807000e09514104120084100001b00b2140504c2440e640600000201d020b10710b0010503048a0981c083c500500c0c442030987c62a810100990784170714003124bc483e00d03025062410f14148641c0700b11441d40102c0900740d540202e580140f000e1824002a000c550303068442620a964001062095000d820082e10792 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 824438075 1250 824436825 824436827
    0x5220309050402180d053316030e03070b01150e06070f0201021906020c010c020106060903060b240309010b0904020913050a05070b1201050a030203250815061008070e01 74
    0x284080c0c03444c81040c40c4407420890014400300710042055403294480801c102d00840090311500c182e5818440c010f000045051015100c15001849449a0041c24600a41090082c0c000300303182181c02c0d09895944d6002e141c4144500d500303002d62440e2400c2e26100309980303802078022500d0310704014072003414207a2030394601900c220b0000c01241103004e8004007084a0301c500124900d1188580c50150b00c0d010f07107403055800c4480303850315030045a051a0b020401039801c88103100541e0b42000303010503071b010342d00b001c2100d110002a40c00c0100080c00340c04201240d142c0c010718000c00d414802030010440d40c000304104080c0a0364040d501410003804680c0503410f040728041c03010b1155044d10228447c0d0b03103a050500c64650301500d04454005081404160080000c0380500b0048a82c1c0e000d00d030a50f00400e0395089590306500c1e154402c0c80042180d80303800c1804000a007050300895041451012504049090998265000d01c207591542d190441c0140b240ca441581c250740c800d0070443d07042e00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 824439325 1250 824438075 824438077
    0x301020703090e1801020403080702101d040f142802180915030a03080601090608240a03050d020a030e040b0f0103050c090a030c030b0903040e010506030a02040e090105220309050402 80
    0x8881d44d2080d030201000c2003010b801380044c100450181d084142c40c7d034100d00502c651880c4c82882c01c400c00042c0300c21668808030303030405070130b541109a40c00602491080216002491140c44071007032011420104a02031191094421990801c800b00541001007811610181e010b5440351070641b404501010202e414034203401c0d03034000c40c03060402c0000d80f00c11010a040c8810140e0540004030b900703080140b6560031610710f00040c002407500440c1703440c0200340410310150382c880950365058008071040c941e64a10300c05001658100080c1e400d0104075040c06560344404000c1100480e21018a801491401e0b2181d1444503402030892002f1858990044006010041c842c0108160500041c40240c4813021400c002d144a0302c196005103056007409054000c0040c1805215131041206101c140801e159050440c1ea0035030310103440ba260b003401d120207070160b50002032408000b08100642144150005400f441e02030580c002d14004004810341407a541d014081c003c10144e100c208014140340d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 824440575 1250 824439325 824439331
    0x30108030307051c15091808071101090e07020609010506120c01081b0d02120f090a1704090203040813140303041208250312091707050a0605011509050301020703090e 73
    0xc540380080107148814130088a08030850080110203461003800301640d2807007815050300102211403502c2080d992003444034441c42000509690440c0b8410005274050240c1c0c40182c001c2d107180e950103282207540259030b203030308483c1780c1c00e40e600782004101c00742000d0810022144108001c0d103020507540c001920303107050180015000500388501108844012000382c699030054140269940e050401c001c07043d050098130f412203c40d043c405000d5001c170700180c8040a03980c002443c5040c500020100f00304c500559000b40c0c0064000010401001a814000d00020080f41c05185a0310784603102c40c01c4020381c2841658240c4d000b00418002c41401141e604a0184110034107403801c034040748c01c40d01020869004140344030418030944100741d04108180d410601e003802c200001c02140d201d043c60120160711240c3d60290015210b410300c10107004100203d07400c000705000e00e5039a0305440003103600d0300203142e00040701e0315004100b034581802240c0701b282c0c0540e600c20505007050040300102a0103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 824441825 1250 824440575 824440597
    0x251805090f06010801090308060a0e010e1306051005041d0601090f0b1504060f0e030606060306010c05011a030c04151422050703060509071e2705100503010803030705 73
    0xc41e148401c1002080114040c2050ba0300200c1d21801d1850040d010700c0c0301074102c6214080301c120500c0f0306802400d00504440f02c075180c40c106078031030341448100340c07580da04058130141c00c11003005043c065280c0320004442c41a10b0130000201c0480740f00b600c0c1100030142c802d06801c20801044049425080003090200302840029090504400505600c0f0b110720025080344010030100183da4100190310410001030805c83c9050070b4a500082c0c0f100320041605116040210228145074071a000c5099580d500400801415021000d0f4142c0d000360182c169100307200300310f458011420a406001041c1300400704036000c0c181421030300c00c00d2185248200d07400c80e11140c224801c0702c0c00038954174080f69800c440010a81800b403801010307a038071500a00d001741844000d0083c1e10743d12050702e00d14042030061032740011508040440d45a002c50112000b0200540c40c10711591503000700c204100e0740100d41c10200d0740040703201554540024440e29440341c000303000040c2070030b00030f0008080314440 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 824443075 1250 824441825 824441833
    0x1703190f0e0303030a05040c0b0301270b1306030605010803070f02040c0e0306010605030a1803050706050a020409061d130f0b040201020a140109060e03040b09060c010b090925180509 80
    0x6141c011074615081212200002512a401c0c00180071030700f80e036980038045840525245605250402a500c0986081d6802145a91801000d2041e080e8814000c000c00140440d04a40340c620340c61014155901050366a5072406000181d025070000443e288a0b0b8002c0322400401c03480c3c0c0820008004c500900d01c00d1012450491510350b0341400201d011381030039201d03d41c407400c0a0740311004540039403509000d10200c50b00b03480042900a01601d4000d584404d0100319980e0744950240a03015640c040e62000e800c10801083c22520104403040d410b1510344c2c0584146c0d1a003401030318a8103482005003101c101c01d042a000b01350203400e00c07584140117004aa00c00780e101d07135400d00c6403500b107800c130221139540300d5120040001c203008519803610a0720046090508003c00d400781c2c0c0c03042c68070151040b034000840400d843d10030b40040307680100082c0641464544601c0103601d82c2039400c04021600c0002d03194000000c80340304650207490005600030404c440c2c1417451001080702822048003486 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 824444325 1250 824443075 824443097
    0x6060506030403020a1a04030c1515090212100302090103080d090231090b0a0903170a150f0e0601050c010e0703210504180207081306091703190f 64
    0x1035800086002c0c038402d80c014019580d031030604010038082c071144151070316050804d001c0407a0307120260400040d080880d40c050001e000c2c1c0c100c001440d0740360429801006c1000001801c40d00c0390302a00710368010412400d5196203c00c810301401d10a400001c1d4419103032001400842c1100c009040c40128416001980040c2a00020b502d280700d8012400400c60807600070340d55821a1401540380301c1c20040c01d00c40038855a07a05614132200500540d5a40d68039030003403050504c00d011207400d1485040c3c0960782401e1400d0148060144070034041c660340c1c4103500c001812036114200c14122140c1513002103081d10381d500116100d50040500799191b40d00c4203002247c45106001020081d4494420302c0d000c40190481981d0115004403514103000c0c0c140410444030b1100010101c9600110800503a00e005a14110a05000d020340d000110000b00c50003107021078004e41c0e48000c0d80c0004c90010884c1d5500c40080356288108400da029038800100103410039806260307605070503440f904040d00802 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 824445575 1250 824444325 824444329
    0x50402151206040b10171320090718060c06230a0c050a0c020d03030e0d020607091220040e2b08010b16170712090f0f0b07060605 57
    0x2421006402078515030400601c28603280030b22131085640c00503281000c2e00b90700071401501456040550080300c5c03040703000050030342182d8001000d103990b0060070401c1c919a58120205a1244d6509280c000d42542d00404d44950007900c541d04005c04506060f00000c0c20040b0449580740301d54800c4034413540368681171501501034050000c0c0050643c8100c0e06030f140120410081e42c081c101c403441440310811014205990003000030000c40d0f019240c003000345c489449c00b1030041c812248103411900442d080301e8001d55000c950903000f4040750340c1d02028551111803040c031611a6441c0203040034002c1040258020b01e641b10b860442030014000900d06074194243e07800c1c55880003820440c02070a84445a000c00d900c07100c4c503402c071200d19200c0120360401003094000c0c41508030802d50120240640020403040c034500055080e1400100c648403481842d1100f41c800c04400803c021030640040858881948030f0700c0b004a404c1903203290011460b201c41c0c9a01e681c002902960600d031141000300b016 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 824446825 1250 824445575 824445577
    0x4061d1201091505060607080714010612030e0103060b090d151806060f0311090414070f080105090d050f090a0f030f02120f1b0f220e0606060d05040215 67
    0x180340e0000801c0515036407500b810281d940c01d00e1600e8451a1005005981e210b0400f524039441e403105020342c1e261080c0c1061065411110300000840d800c01c0341c0411640b204100785003030603120345c6031340c2e0042c4003100042d0161101801000c03038115080c42001e1851400410149007a400b13821400e90f070112082c10007041e11040408080a940e4108041c0304210711031240700000d2902c00388800945003176540e128850b0000042c03603480380e04070401003000c0c4101500384d40c0d490640700d4111841c007030f502d004020320307032105100b01502d0303510b80b400003210342c0404200d102440400c0e64840785016140c500309480c0740c1129085a4014070290408610760310702c004a440038ad4001c5c01c0c01060301645204010b5094001c4100001980000240b44d1112400007101000c0c100b040c071002d02c1030308001c030104408413090341e0525400821a80c0302c0c83d10300c032881c06a00c400b1015050074440c180500852075586c480039115540c00444c2040300c494a000240c0c0302c583c00510041c06d015002010303120301030003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 824448075 1250 824446825 824446849
    0x9010908190b040312110318010e25081b040b100f050d14190b060a0c150212130c09060503071206021b03041d0103080d0b01020f0a06020909091204061d 67
    0xb42d04000081c031003c41400707140d040340404040004d10ad40c8014082454550030660800d0100014040c41c1d00c00b0301c104d0948a0b000303000100c080b02d00c44d1415042e42d5990b6206401c4041c0107500d09442ca030076500f0101a012a101807a40b20040703c81d08055007101c05901c200780c10392640c2d94501d10181031160042c00a405001044859642c0e0140421542c044514841c200ca01c0b40c20b0400280480c9504280b0f000e1003503070411070060461b408000444080d00c0340040151112801508000805e401d440c0703914081800b40f6410b41486440c4c074001e004540c910b0040c658164840f41042085d84600001c10726032a106440150902d1041e07a5482c0c4245000885a800ba402c0494103022280c449001d00d400000442c20950803540756454100031442640c03080040d40703885100d030f070109034001c00c045001030810000301d440114950803d0340094012454035803251009501051030342d040040c090801e1402400d100340740515100b02600c0014002d0a8100c00080302002c590480e6180b480c151300d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 824449325 1250 824448075 824448101
    0x3080f04270605150a0c2904171309050604020d060e04110604050d0b0a06080106030c18060e0628060302090406050a0803121810020d05090a08340809010908190b040312 74
    0x1f0505043c5011044a00880718031880b18000f0301c4040781003201542141c0c11280041400034654403900e0108000e4400e0401c01801c890034040c0010300d25401c407002d40c3c03260b8000d07e009030700d071101d400400c080c500c10b0748120351380030350000c40b030303c0200740800740d09a000b04d02010006001980d0b100f05a0130f5400c5036109450415501c18100303c4608113000508920681003810003c00d82801a410340800b409805180104d41c11002651070b01e07010194480d8060352000041070250765404001c1c042d5110340c001c5d50145050120001d224205515440300b030320b505201960400341e050b4010a019a4010044440e82d900b1f20582d0203030143c144580303c02001c0c0d500016075503442c072048480035030380c000d041c02101d648801c65020208a000c800d4460344850762000101003543d549801220105000b0b0320240d20301150700031010000600001e11203000300380c0343c6020240d5241c0307410340c40310f0f404142001801d100c200ca80c40090707080c0c042c0320b034030603c242030006140f00b40001d50702c12a514000022 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 824450575 1250 824449325 824449403
    0x19150f0908181f0c0236070507141b03060405030901050c07091e0506011803030f0e0306090d02010c081521150f15010903080f04270605150a0c 63
    0x6419030406c521004084203840e03400c5c440748440340050701410a42e02903148514001c00c804150524420000c5032403e680251501c004002401240c0d51076051900404103207882c070703805551140c240403e0031803042e07400c20051424019508015601913001c02007100450140a4000c280310600d072040307a0b0786001180030b10b1110004000c0920480d4000b5003018103110b142085100c200603034212440560b81d040c9412440c0c03001208003990300e42d120940d400d40c107005020030032440070320000718002c007200564000e0103020300203c0705650b004010750f01c8900201d003002d000f811a040ca40e024082280b9214904004058940e14190070040c00c01c28034a050001c7d0000e1050700d082c6510400e40081c40d000620400c0310051001070104615803100a0a13404042151114000a14180c82c020060001e0f210790741c030440844002c800b01c48540b1740744a01d28054010520303007010000110031504070501c2503d0903030403240554900d8011002241c0c034600c800b242805095402c21818103030305031200d6075 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 824451825 1250 824450575 824450597
    0x20100212030f1317070b1305061302061314031204062a0b070c02090106110c010806030c09010b071202060408075a11010f0219150f0908181f 62
    0x1185900002c0e0264516204454000c40483c802023a401d03089a201c00c004000302b04144086801c50090048109007c41c603580001041c9040c0d02e00c510740c100c405c80642d68036085540106149010301c0c020b4000140140c00d030000c04200142d849050030a180301527800d0b002d030956404a0710101200c0180c0010041c002c0c910840c2000c04000c1c2c013410080c203000450403a502c481950380d040b2842510304015821012585a89046c80020440351028103100e100713603151850a03543e9400404101e0745c81c20446c03040c1900c184041001402250702041003850400e09031141030100000800048030005544804800b50303250794070b101c502041d220403500ba80c880c280c40350a191900c124101d60780f202410185030000300c407000302d0000700c030090070042400d00c0301c210224981001c441c0c0e41800f2840b951484010701460b41c4680e94640c00c000030901610700c4040d00081a10b10426006102d0501486154050743c17106030300c4c0c01e00d844090203c10401d210b0058074108001c908143d40d000c5a404850 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 824453075 1250 824451825 824451833
    0x3141309200f0f04030203011a180105180405030d0c030b011404030209160c0b100f140907050d0b030a350a050f0720100212030f131707 60
    0x3808041d400011000c00e000c0c14100d080701c45034419403072000d14034000001d0300382240d44990141c03000b441e000b500821000d01031064000c4e480b52003c0f50248111903481001550403801449203050710030240c02803038460f008140040c030150026004480c02e000030300080001120b14890a00300a401e0b6030045808010700e00050601c5a404048200c8810308000500140e11960f00d0660411840403020480140c01c00c030440e807090403007600810300e601d458144054841400788000031781c1c0b0b0144bd40c0000e56030b500007190644111540081d003001102c40001c0f4428040c9014101180100d00042454184500040c0c28410402da086490002841280c10640c21003d0302e82407070305104c0403805400d044081c00203070600600d0f01000c00c121002407820420401513059820301da50007180e00b41e001c00481c00c0700148403c2c203803440c0d010304060030285003180d10018003503100e1000c0001441c9140c40708110b0000b041d0004100408200d02c402490700065141c2c1014241c06044803c0f2a40300c86040c94 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 824454325 1250 824453075 824453081
    0x10906060908060c0a030e0307081207051606050603121204050f030a120504060f050a09050c0603070f0315050a1e050105120a020a110d05040509060603012103141309 73
    0x490001c010054106010b4607000042c0642c202009204c0280c0b102d1180703c1c120050720390a07111400b680008108002000f03c42000760850039541164007100c0d81d0386800803181405841400c000b103d52030360884001c10407030392025820420141c15071f8048240f151001031f80e50301c6242d124049030300c0c4404000601000b8031050061100e114081c51400c0880c01005000c5044941c50220b1140d44d6408038040203002c0e8000c5290b010080010b21a924244054000511501c2010758181c000e521034585103140c108222031048c0c4594445010000342e002c821801428400444107402288520200741b9944003118040208405058101d09844030000d1030748100d8254011414880284000e41c1180b1102c1100c5601880a40c8010388440c86c000d0111410000e0f09010500360060b1503c040325154818000d005a030010b503941c0020f504d4210910060f44024414100140724421a515003c00c00d4003c84003010b000303180070782d9488808060324141d0340c0800315000306484580f00030015102540 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 824455575 1250 824454325 824454329
    0x60f210f07050f060307031b03020a020606043303020402031f120b01060f021e060106090f030503030a0207170d060e0601020303100501030b0112020408030403030806090408070f020a0e0906010906 86
    0x503000d01030040ca008007050040b0704004803c3d2181d40c0110000d10b03458070039808083e2550b510103040060700d8200c14058000d6003d80c030000c1c018002c24001070010b0405002e0036881110800116149180b0028074588041d4900d0205005210301b2000001594580c0080c501900081a030040c0c0c04035040c0c2920b000c1c4845600414404145c9203030308000c20902d04500741103403000d0611076003500001900301c5c02e1032042001070790420502c1440e59031055000071202d042c5d561688616807041e8590300181141d01e5188030042ca00e51040001401018140e0090018107104101c44174ac555000d9601c108035030040d5095081040d40c80e48108072104294030004c0d00b003070003030001d1465800c00612107200708405000e02c40c18561104a140c1040e4411098243c050400c1d00c030440d190b80e1070312040d0f501caa00c00d200c02d80028202001240e05407070105c1e07500e40600d900c402c0d030314640b064030780d1031803030b01d84170940180e038009600c503c00510303842f01d540d07428451091000600f4440d0f0500e01c0e100200d80703440d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 824456825 1250 824455575 824455603
    0x120604060f1401051303052b03060305070b070c120605091218011107180f050108010b0d0b0a06090612030807031506050706090501061e0911040509060f21 68
    0x800410002d061260a581c90099000c0c07a1040e0b4482c0f0b441142480071509610043c5240700e01010707801c4440701703e038544450402d00200900034a0782d2400407000d8030030034040906646c004500400402030b20781c00400300c0910881c4d0403800e80d56124103040080c0f8110314151111a2030301c0c20032004010074007108188481803d4900e08001c0302c42010750f41540b02400242c107024071000600d501010402440b801002c24901851240c410325544002a20902c4441c80c1c0103800c0600200b514941801010382c1900b01911004000805032a652004803001d00585400790f540e21000ca01c91641e07020308070141c940400c100c40f458007507182c001c05c281401089001050b28000d0403800910f9a41122404c885072490b003141c8400160414100800034054002c050b0f620703140d0005206090380030305542c4012010481480d0a40d0748180d98283c800c4065034204842007000240a07600e0040d0b44190003c5026000325982c480100100381f101000c5260f417000341c0d510084102c854041040114148000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 824458075 1250 824456825 824456849
    0xc05010608070320031203071101051003050a03050f09130608150c030c0a030e060703230709060f02011b08060f040b1c020613030c0608070e03060402040b0d0812060406 74
    0x6103844032801c14940f8007000301c261512a0b604c111595003040b001000c0480a0300360380d983d0610401c00f03442d0110960098080d542001c0010743d24403218155a4101c135006005001c007401c141e5812101036200a40340c104441090215002c29100c10303001c06890b0b1220400003500c68286254240f525080d428001d0b0704107403c81c10003007182c00740800d5035003000b0f0160f121074403a000b101c42074016104015011181d446440100300000c0c4d810340040c1e1105844020305000c17042283c2852150728000c44414000c540000c1e0104035040c4100702ca0075100b401480001541d8600442888900d2461098000011042000e000c4903207452202c6101d490012241000340070b5410001c90400030449407086081d0520038140801e5407070b40b00807250040a1420070b141901d80b40d2805288030403a0780998000503940100003458140142840c248881006000b0300701543c9a03030821020301118144a504941810400800103681c1405000702802c003030344241480c5480421712040394400c0d4403450448503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 824459325 1250 824458075 824458079
    0x30306030c050f0a031b09020c1615020a0f14012903031c0c09080f0105070e0405042312160203160e0c13050a030510050f010b16051005070c0501060807 67
    0xc0d03000c0395103040703e03031103201d28615a44086d041c01c03144920303a124801141c000110003510800100300741402c130704a22030b89070890380c0f503400d8020340c0c1c42c0606d40e107005039000031240008610500b40002905200d6021b1704008000b51000500350f81440c00e048001c0403c0301c03064004071010803c408a528801c0c1c0080d8103213030140f542030345251100d1200b54011542e9a040075080d9114400b80d0014143c007008940e13900e40b150440900074402180e0b00000194a03050510321442c10340281c40c029030300000740300100014a0080c41c03c021080083c00400c1c402c021540c01c2d091074080180c91480e0201c0c014003400280c500501d402c010000b401c800701155071100c288440d4400c0c00c1d4542d080903a814620b07480e0344590440803904c000da6003041e42e0001c0e0799103001007000b00c0001c0000700655079a5050005880d40400441e001d802070083c1d1a02000a0124100070030b07841300c0c002c0f000c0b8069800c4a14401c40d0b40d281e0307011604241d42000c0002c803d091a5001d01c04240030f480010315100d0f00421900d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 824460431 1106 824459325 824459329
    0x1b021e1002040e040c050f101d04150e0901020705030a0f0c20011d0f121510080f0d0801181e1512080f03060a0f03030306030c050f 58
    0x500303800402c03139003083c400f075440480020340001706080b0412350903101d4aa40560b040541ea100d204400100c3c0c0c0c1d030340240740e10042c1305140504110700b0200500d0f54850020600045070f801005914009100001228a00e800c01e240940690030415812900403040f2280a400103208281201074400302c1680811b5508007621791500160801e500720314001c44651507240e02103100c440108060910040c48074590139204160361945503112041c9810b91801c0c1c54920810900035800d10405000700181c24228800e0740c001c021140e001c92005200b50710500582640c0c9002654045080c022070b00035039024000c134441010f11151744241c0d41c6c0144070f400034084824008420014407803040511000c0030503002603035103240181c1c11154145603803001d00f450740c109402c410005204904014020b0196110f60f60100e402881c60a085070807048a4002c203218542c41005a00d0036 = true := by decide +kernel

theorem cover : BRFrame.Cov 824280575 824460431 := by
  have h0 := BRFrame.cov_init 824280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 824280575 ≤ n) (h2 : n < 824460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
