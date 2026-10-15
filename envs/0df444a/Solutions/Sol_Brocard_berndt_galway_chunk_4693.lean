-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4693
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:26:04.053066+00:00
-- url     : https://prove2.me/submissions/e8e58f51-9a83-4cae-a500-fa0cc61a5102

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 843884892 ≤ n < 844064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 843886142 1250 843884892 843884903
    0x307050d110309010603050d020f1905070302180a0c2d121a09061203072d1a09030a0215130c181121060a05040e0a0507050307030b0f04 60
    0x11161460321141400b40d8000d003028400000c04070308618100c0d10300145021094299842100245d200c81c2e00000e66121043c10000140019011442c183d45800e41d2904002d601882440c0702d07103c20a0f818108034030401b0241d100340320301c40100005603400e001006083c0360102040e070300542c241251817201400305a0a203030440381d12428018010447e180740c21a070b11124424003000d41e007482d010b0700c1c00c1d40044080b514420030072601e040761a520b106180e030040c56115058042c2da080c2c200360700d01d0661082c8204140316824150324204400c100008419488043c2c1c07180402c07580c240000a071459080e1a400900305c0202c0760791a0b07603001c4c034000c10f0004604210044280002d40c0c01e20300200034018401030800c1b0700c000c003141c2c8050750050b08540c0d00348802400480700c168004502c06004005400c1841203603142d42011401d02d44c5540c10198001d4144078280a0700c450005107030882034000c500303440c03410383c0700c03010541c0741c180c40d100180c4503094007404210400340c80f04540f0303000791084 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 843887392 1250 843886142 843886151
    0x3012060a0306020a02030403020301061e0e09010603060f0b1930050703030c0b01060f1202070620090f0a14010503130507030f02090a020306010c03030c03020d14150a08030307050d 79
    0xb075035858140e0740138800b04001600040b80400440c1424020000a88400b2504140c0018035010741c54101070b8920414030112030503004145908420b40c4000090740d001802071000030024045840130f00f84d0f03800d68038090203840000c0c481c015000b003000400d030f600b41e5800d1080590b005403000342c26506103960303081c0c107000c0003580d400150080013030b0700c0154800d44801c01c0120b01c0303080000e106c0105902240c1440414040035100780e03400f6020300380c14195124011303100c00880c14043d004100c3c1344609014a03040311003084640c0c2030b407409051401001c585420404101c402070010600941c804c2820100700c6c4092030243c0d41c010741c042c3da030180464903141022261a1107003807400c03600d0303841514071001d241540c10030350400790021903200c14003007800d501e9414940c0000740071520f4a01d018040560b18415114034078030907011507e040c02060f030184072a052082c929001c6640c01e4407080c40b48180f170300c0e201c2c255007805580d040894641402031030459403002001d803580d501016035044050b03540d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 843888642 1250 843887392 843887399
    0xf030b040e0a0203010606170103030318050f070f080d23132702190c1407180b09010302030304140a03210815030a02060d06080607023012060a 63
    0x4a100c0c0580c201c0c4004001c0c410070000340141400c4031607036000f40b01040030701744d8442c00700c01241492a04582d807510b000100c0304100d0314070038402404040e0084c418010300f203149184c80390024010040d2a007501c014225251340f0141140d075012450321807004280c43c810b1000340010815440b00c5441902a0414580043d5a03464100d4401e95000100802007282d00d51100f1442003a144034a034603c040110314082e07a003694000380003202c1c601c0c6001c005a15910404118000c1c20394800c800c103c100319104c10b40c581c1c10081c550340e80c01c51200d50040c42d106c40d0302c1c1c1c0d518100030038604894003e4095032809040603007101d041350039201340c1034008000c0c2400200042e8900e6030010240c0900c8851821640c510307000038540b040240c0480c410020301c2503480c000e990040741e0041d0482e41150465030300c60520101c40043c01290740300380c0c3c1a0040d1420000860380106625004800c3c182c6101c111000ea000401c000d102d09070b400c031000f00030900504000718040900b071600003900038410031094ad076 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 843889892 1250 843888642 843888649
    0x130311032b0902060f040f050d021309020d0c2603071e080403050313141f051303050d2102120403030207050a02030a1b0e1329070f0908011a010f030b 66
    0x400143c201e020b000000341081f803480300741da605015080480d1300c44d0398014150006001c00500380d110701d1819503a00402002c65940b580030403200d40d031100444150503518110880510440c811b050200788491001c0f0642d1400070080704c0140394402c20031101001c1072001121441c3e55814212a16a020040400070580800242c50401c6225235000e21030350400d00c1c4220487c8070100c00d1070284588402d80d540352803010300d9206900c07190f031a101b038954001031032a81f81c1001c10340c4060014010268030440c85940000d210351801c0d0403d20142c0f84000d0107071314038224400c8001039080e030442000440d0010303109070000c3c0360040c0500304035000c804940d000242021244c3c0c01c1140c0003038881030f081180348001c8844c5c3e0020000d405010b0072600d0a02ca020920204000c4001d2940d01c80048d140c2c00d04440e18111175030441040d00d00c0c4c1d8a4600808041c040c40c0c81d0b00740b09004504801800502d10300d05014076501d0f4400c05a5030072446103e07400640f00700e0504c1c62034905144d150380001d2650f80303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 843891142 1250 843889892 843889897
    0x611100b0a08150711010e12090613032009010e060f0105040b0a090f06030e03030f040203070e01030303140609010303121a03010903030902040e0d05120a060e130311032b090206 78
    0x900c0d40b81c0f00021401c04a8014001d0070072000c0c501100d0341004585c0e9803601d0080b56800c9180e82e10010382d41c0d195050f01c00108980b10301005000304d2901d10b480841808082c826401c803610800c10103100400c081020002d03820424861501c01c955070342c00183e414100340e0418007484006050890030107444d060412413580015580c030001895108041000d948110210001020181410000708008504040d243c1c4001020306000038030020100c1c003151010403503000244002c0301c4e04032a55840e854010090034450010548044154000c11854503206100a0480f46e040d1265003e4860080020000d401060b0071446141641401512152400c0c05a8104140b1942d40041c80b000c0900c10003040300c0003040880c2079540100344a4104c0d40c0c000d0b00701c2c0d10782c4003884015112555010000307000340c880c50b08100041405801440f030341804210864210a110703440d041c2807503410700c07102ea079240903080340b01c4807045070041c00c0d06882d52400c050071002a6030400104a1108940209900d903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 843892392 1250 843891142 843891163
    0x11061b0a05360102060a38060c1e06013b07180e07051b0a060606030b0f040905060606180a060f08070302030c0a032403050c0103060611100b0a08 64
    0xb0604860318690390f80c10320990b540968480760030071040c0c54050808180403002449007682400c0b1001c030005e0300c0300704404101d40c0e142c010001603440c15680d036050f0300c6864130180301501000c40088030401200101301d02d4142c40107a1b40754480782d642400654003618104882c0101c20ba2107105071480003074000c80b107910400c203e4646801d5455220405510011983e00c410759101c000d605202284c2d500c00704543c042640c215809101d005000101b0b400c1204268009140074540100055010741540101c81c0600c0200c80242807076401c81c1c10700040e10054800107200e40c00c14400556107141c46000b800d11450070b09003500d840040b80c4082001107505800800210301e4441e50114140c0d0b000302d4456101150303207415429800c242c1c1d0311038424050b0500239400e058858034100c2c0307003594002c8040f141e0000d0380100d5000036503070300b040d945070050003050500007070034400c0108890740249003038410a0070020081450400c986032400c010401c00108070b500040341c0200086241d810402010301 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 843893642 1250 843892392 843892477
    0x207111005030610170c0705030408030d0902041d0a02041805030408061f080312190516141e070305070f0602040618050907030c09050d0311061b0a05 66
    0x201d0901e4410420900d0007021000c0812808085820440c1c0035105c8203900401a0302c0240d45840c1d081c942241140190f4010f0581484041802018518580c0240f61828000d48003080412880c0d0070710005803d00346045c0c0411350140c0720000045c10941e2001c10442c40c1d08000720303c0e480d4640d0b9000d00703541c0950302211403584614240b140c40c407694511001c00c08403084908000501e00707540745840e80a010383c2091070380d50a00004607900280f500604405400c0c420401c11442c010342000f5201a1007910030000a5031603048603000d0000f882103c0e21668a4a118584102c0c440820b4681c0d40c8000400c80800900380600d40028401d100c2d9059414450318015840c1c50902c080101042c20b2280340703507880807001d4002c211b40d444074901c1d1508008a81b801081c0140d0303588065801882c0c2c0e52200303400154101e0a102410752107105042c5040340401502c54a858004c00e1400344000021742800180e010841c4041260194004000b150303a079100f014480b0040410260300e032010445071062 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 843894892 1250 843893642 843893647
    0x2030328111210030b1602070905010308031f05060403111c08121e0403110a0b0a060f0f0303020d0809210703030b010c0506150604081b0a120302030d0207111005 71
    0x109201001070b590701414460307090103072528540341c0d2130304032030080c0c045105415840307a80017440d40b0902c59280540b2030707007109003c15692858135010a034000c135942801c1d100c01211b0145c01141d01143c0d94226103000300310390304242c00c0d52900403035038250015680e804130400309140191801c0040c8045800d0003100d00c151601e00503c41ca5074441c034002c2c807040c0b6541c40d40540c00c038282010f078050340d00181c140c600200003920300c1031081c0ca40104800c003e401240c0f14800c1104e690195000881564403980320710728020740e60034251510035042d000080250b0000910621800d1090980c164045c8070301d000c0341d1481da4036001c000c2c910039160184010f075a00000b0600285a018000e16541c11820f11305904400e090751100390302c911002d40401401d10303812030180b1140e521501550043e04028041d80c0f85250746051b00116180d2000442b030190070318400000350304c209082558a11034050700a0b6180031040b0203801c00a5000803006c6030690841601038801d5201c0c2c44880c6200a026103c465 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 843896142 1250 843894892 843894907
    0x18150103021c060f0e0402010c0f1401060b0a0e0d080f03070504150e04060816090c022d0f16150306080a0327080c060c03070b091c0c030203032811 65
    0x5400c541c00d900000c003071205d0b81041c4030060340c1c45401080c4654000135450102002e40c50104420400f202f160302d115030900c44042258010880108070680c15900c900414a20080078400c203e140c0c4600502111001d0000003221818a4021940440e02c2c0c60850b182513240d0b90740180100780c0c40007680c0007910506c40c0041508051003000c001c2c101000041480d8108000c400c68051058018192410780702c1029140141c002c02c44100000c488ac400d1300c0c0d400081da80c0c03500900c060304140c84028810094900b413070f424085a03440881c03014105441c8201d0a212030000b02801c11000002010742d1214000380c4ca00c803d11141c546207102c0d58078007480c401c40841440c0c2140c5c56603440d0500c80d81c0d480c41040110702c00100d000070103100751940c64840d680030128038114050700d0400b600405804007000042da101060144101c0064017858962900c40340e011501a8904e501c010050f0307200b0404200b81c3c00c240d4100001d00540c0e4145c0c1c40194000040c5601606e541d0545803a09500129440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 843897392 1250 843896142 843896159
    0x20d03200303041b180f020d180501050604050103050d0309031803061d030903031c231008010203060d11120102130608180307020d0c0806040807030e18150103021c06 73
    0x940080c0100101e10160904000746002691a05170f010200317241d46189200300c005c010740544100e0000c1260800151800114403000c401d4944030458035546013400090092800b80b240d1810303a5040302c0108507000079001c05030300420300000d096051000c481c81e43c6840144084a032000b4511422020a006040d55800c84403542d681c813644030b50380c0080c000c010a40d2000003d540100e40d48250182c404543c0c01d442d00e00602d00e01c40c22444450303c40254030010708200150368020804841e40d011620396520a00c1d081340001d6916070381c4003d4449800700441c00c58551030f450940018a101200801c4210312822640041404411144024400c10801d900b0aa0140d4041c80611649645d5070b40b5203002a26813140c0e1800910a041c03400c101014000002d030303490058101d407021126a800c050a00d082c198005e03060417400261006141c3c0010b051590441c2c1d0742a900c0c00c018079294803104981d003c0b2030642003089040540c00d11080040b0a40e031040200324a21a50300062050f0814110307 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 843898642 1250 843897392 843897413
    0x201e0906040e060a11040b04030303020901020609120405151c0b0109050a0f030803130f0303060315021e031902041d01291e1207030f0c0804020d0320030304 69
    0x100307215924244100c0700040c40400c80b280e0203c00d610000900010001010a440c0601e400c04003452601260200400d41c06500501e1880d030242c0807100d00390f90305041980d80d146540d62060b6099400d000410060a080c0030021020003d500b203182440c00c4041900c0f40007480f11a1141402d840f00d031640040c0d41c0204070310019000603100811010300384000392015558520005200160000015200104e4000d85110f220b500c841a1199005681001400b800f100d00058880c00c0d506801130748004007134400c07180c41d200e61940c1091016640703542c100458000402903840016641c10480300b40b010b510052025008052201c40d1091004420158055050300000400b05810303502c00310054203241c460703185100c20520356a0f00e02009000000e41e5400150b41c24407401c02250702595030035086001c62280001d81d904000001e0020000c20659690307903602c20114100902080143c141091900c801c3c50180c1000e520b044401e101181700701c0400035000c903441d0004000e1104010001c2c11 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 843899892 1250 843898642 843898651
    0x905040c12150b030f040201090b0a030501060e0f1309051207060509010f0c0c0f2f011409100c0f210210020a08010e04030201092315040f201e09 64
    0x1c101c03581403c1100c80035451002601e00507400d4404000942161300c41d04a0102030010080c00940380c00591001601816080c02040701003486414031032010f0503d010800c0c01c00000030145404604000342880c000c06482d042a40d01e4003035081c0d90000d04500d1002403240c940700b000005010310b0a59252401c50718500e41907280581098112540d055004070320100041d0082d402652040c081c0c60030009800310700d03401000c2c0b580e032400c0407946680e858682030711028080c0ca5420512810390b602d003c0798499042e00b07650050600800c424045c7c85140d51a007540c1c412500c05050b401c1d00e885602d030003070000d42039070344c98a070080744010242c1c0e061120210300c07000500d00790704003208144040c0401005020384884c803900c1000003001e06200750000707403410fa0408168216640924521040c0c0c820302d083d5240c00344121161070940610980f4840d2050f81c000c41c1c850310300300301541d900c8801c002c00751007032500b604011a200c090ba50f8240e11180342c246800e510b25032411040d414000d08101c002e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 843901142 1250 843899892 843899921
    0x10050a120e0a060e0606090c0d090b0a0e0c12100c020a020a0803090a0605090315040302011404260f03011502072103080c07030c060c1b05060a0e1b0f010905040c12 72
    0x1814420310752216031a10303230001501c0007080e864044102280000300750840014003403904c40c07401c1c002c42d240d55502050a01c0c45080a907600020404148a0b0003411902170041c254005185683e4100c600e92000144001a10559031429102c0d00010f0392000c441c0c10404854000003815080b515094800e100101442d003405400e041c6080e00194403100c1b01a59107820004141c000f4041520070341c0100352400e07621841d807100e4202800c24100e4001d0441060340c4103a114100d03605110f03000e206840c28000e280301e440c0c1c5503030308040606030000075080c0c0351010344c407600d480071854082d80b5110031404000d4800f42030000c456428024250000544010701d450001c0010002003a8880303c1480518ac000f440429810b004500407501c04a81c940c80841d0801c900d40c0c2c80c02009800b080540c014040f0b2030042c040c1c1c02c4112000303501c94000440400c07444031140001680340c1040700300001c0800050400c0c0700401d69402c08202951100720041000039003049440100c4d04180c49944044d01042 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 843902392 1250 843901142 843901153
    0x40312020129010305060609131a04022d161a011d16051c020909070e010f0e0406031509020a06050a021f06090c02030c0709090210050a120e0a060e 65
    0x924641440c0d240d440b45440c10075031244001601d5880d160103e401c001005401c8522611004044200a00f5644c114080c1d200c1d1501c400c2d1007615150080c4d84c844090040c1100c00d40ea18544000380c02e440120030600e8902050041c0040d4000078400d048200380a0411b044051400030412000b14105800030304185450780c19074a40c40c01d43d110b1181d40a001c18400c2056205c0c200d000341e5050050b51240070440c0448510341001e0300058003d8211a441a210b9510701d8403600400d0b81c810001050307117400102c00c01010146e8500c038a00c0011410b00180c030000d411916501c81c030400803a10644a001c803511031401e5803c42c10003820001c024a05443c0c00c900f40700d11135400940f1103d0810415541c500405002da00402c00e41d4015001800d440c0002c010300f01c0510006502e82d001081140d4440c003580c1000207513404180281112603500610032004071035440390030b6071103410050b203141c01c006140080100e040003034480c04a00341c1004c0000c2040507040c4c904a01584d54810010711280c01c207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 843903642 1250 843902392 843902441
    0xb0906101509050604080c01080a02250609050d08010321020303010504020c030909010306090b0c0406120504031b050606120c09060607030c08030103110906040203060112150b0403120201 82
    0x54030060544181d500010081003800750200c40d80b049070f4020710380c0840005000540403600240880c4000001e0f29001e0b450f17500c030401a0b00307d000d1a02503201e0380c1220f10b150b0903489003100281090910a24002610b450345444161400b503114149101041840b0018824446903607825032910711100e21007820700d1801d080007501d0b408103200d028012074000c65004401a024800c1d25000680540b00348141d41e500d0411001074814080265003101c50303440800e400002c01c00840b01561030b41d4645220300401d1200e920002c0200030016010010150403103c6030940c01c2e1086140030340103030000c12590030004100445800b600d50300c02181d40c0003015504542d2150000c1592207407040711165158250340c00c0c00e961070700084500a04e030000c000004801c1000e80070003603030005002d9441d8100ca0b9503010901080f84820b41d030140c0030034030303000117046101c581d60006405ca5102807400b00b1019a90008411140c20076041100c0c14100c1115103100d0a6091103034100c1949580f610640723000c030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 843904892 1250 843903642 843903661
    0x90610081c1d1e0a0f061b0c15031e090b011712030907032d02040b1306180c020d09060c0503041a120108070f09090f0506040b01030b0906 61
    0x20004503140911080c10128a21454100c1c2c44480300c00c0041c0c48209403034011041100d000a42400d401d114490582c00402c10225120455003a506561500d40a6044101d695030000e900d0040444400450840125011020400c07020703044100ea02c0c041428100f0f20fa4455502851010045a49107850412804525160121703411162178903804074003198035040c0f0b1800c003041e5100c503202c00340c0c0000912840e1800010080c0031280503000e203030000403158a4114600ca407442480f118010104003510141c6415807184e031940e0340003800070a159416014201c00d440113070b44a90301d100302141201d05030001c140070747d0141d01c0c074910150145c2038092030050250000c40c000c40013017100180c41001004001c1040700e0141c80b48060a10345007459100d401c0855200107003a400d00c85046000103210640014080d0580e98030402c5846c129040c000700400030003171014103a07103540d106c1540728041241803040d40d024070301a004801c019810350034081d41080010380340c454070740e211108002ca0b2a2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 843906142 1250 843904892 843904933
    0x5060d0303110c030a08040c0b0f030121061506030b032404061401170d021c0e150d02072003030702011b050d03290303070201030905100509061008 65
    0x1039150500080d028902c541e074042c0d41c05210442d120324407002940380490768110140511942c0b14000710490b00307071103050b80246030040c0d800a10000c80d0070300c0140560003c141c0818040e115030014890b04600c1d50316130701c003510b00418000301c4002e080034060141550500503c81d091005600409090580540a506041d89080d00b00500300012001c64100601900040c0c00410706d481304002a50f110ba41d4076450b240150001002880741e0014591224000305a1054141c0c0e5408070028110843d401650500b510b440c48544c015001400c0c0070b440c502d80300182c2494405030400585807002454848407158001c0b4440045602010f6450050350300007088804884e42881c00c610b400d19a580d2400386007040d070744010041c0c040d006003c42d5113036041d40f204090718004140e4110704c0354107090700d00804892100c03480d003580041169070055402604042106403064084400c0503500072690010bc500c26103828130315400c60b4082c0902c0492140000d0060041361000c1c090750320225900e000181d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 843907392 1250 843906142 843906169
    0x61e1103040e13061103010e07030e060403080603150901091103121611130c020c0d02181008030706060e0f13060e0f0f010f0c090302031e01020d0920040506 69
    0x15440e9100080c0c00400048000f40307000d41c030007004c0c0708202d2240c00c6114550800d01032001c103181c4034800206072510034010300c0070040f0031201138070180c0c80ea518129012500200f0b1680c00d8461480d00a481e510000c5041d1700c1403680500003e120031151410b8071550050194503032296012448202c1d01d12154400c4510400d16611039148150303091401840031000d8181c0254400881c21180300d50583c00d07005040c0c0019190300740c68008400404004c480d100c844d81c069000000e03144050310030b98002c8000c58002100034250140743c1e594145007071070740d445940201e8031142c136000c0c10007131017000d1400e49030450f9607030b0a0f00700f0520b003c002070482440302c0d02d0701824031521544041ca01d01414070046040315140f406442d25030099000c0203010341902070303038504442d2900c1c0150351442d01c54003640054075801000380c041d8079034000b198202020180104d1083d95420810045003152900c5602442d40c86010b192150301d00741044029041d1004078298006d030709240130820640e8070000e440b0381070b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 843908642 1250 843907392 843907409
    0xc010819020d090b0c030a14100b03040c080f15070201060627030813050f180708040501060b04060809060f0402011e0905040510180209130b011107061e110304 70
    0x40e9450201c980028024814010f00301e0000b081c1030141001c20140254407801c10746009011a82300007544162918044032040c50031452000c1c28071085503088000c60700540038150041d43c0036110329401d400c1c08600c1014542642c055010020782030540d400b45640511180000c0000030701d04603001d0a040e00070030307604010200d00c88a00341b081855140341c070082e42d08072000f20b407107058024560302a20320a0142911440c60b28140007594a08039000c4e10010031460042021034880100548205601030811039075552154400b01d000c1b420302c1d0103080202259940c0c0c4500f420030000c21401c0240103400c20442c041420f041202603600142e0748180300c05e0000c49160080c1860f40c040f01d20080c19004554068100000d2004140c035010380801510f52980110b41481101c49400b0100e01c609480e00d80c0000e40080c102d0720840715944072002203034060401482c8025504d00c0f190820303a2a40080d0007258482c400254080682000d10a07003152904050881401d40308442c1d07540c0c001c3d441158030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 843909892 1250 843908642 843908647
    0x120307051e0f06010902030105130527031605030a1209050604330f0b030a0f0206092709010e1207060e1204030b01140a0b03071d03070311030c01081902 67
    0x211040030029041020002c40a84400703584030b0b51041e000c1c1d4000e115051140c460003140c61240c0150744500d501030031a1032050342c0c45254001c0c4001803800b00502c1d611043c0420701c44202d000c4a001203694400d441000030355660910042e002d0100a0086586404030380750451840020300300184143d000b6030002c0b5610b01500c039002e501c80407500120300c0c4401c41c081d001d0b403c100c9002141c0010f503907096222028000c0100900c24113944195100300501254101c10807107002d03090244c01001d0350f020141c405080310034850320b00d100300444000c1c0100c00c20b42d01402c1280c40002886200c18101a0382c010b824401602d03040c1d50b030f00c1d0080d07200140140c1e030798401404590354104010f25108a004621a85070740d62414083c000b0700f0309105807000389000300710702c4082d40f401c1c805540540c0e40b003070111803c40e200c604003142c20460101c140303244115181c0030075040c0d40e01001448c000354400d50104c51600840818107050203400400d090510bda00030034001c524201202c41485010001070040c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 843911142 1250 843909892 843909943
    0x80a1101060519180209060414060d0c050c01060806061305270d020d0e0105180301140a0603020f0619080712021216020a03320a0c0212030705 63
    0x1801040c440d0700c9a07500c2022480e01c11025039030a68020104d505504203542d24038100010141030344142040d13103a00082c200302c24017032100e03451142001ca02001e003000d0b00301030701400c1c0b142c21101010946404900b002c0780b11002280c090091201038800d0401504081c1040004124003466160701c05030b01a03151303c005200382680c0002c841150b0213602d01025800e003600303500ca40f104420b09640d030041c00303080980800c480c0503d204c0b0104d1a01a5111480d10140038682e468001902d09855415501e6009100b20500c0000c100c5008a0055100264003440c61040000400d0000609802130100b8001100d07802d0542c3c20b8218101c842d42040400da6845210445030315107400d4065180034230115462040b81f84804400e84183c034000100c00c00824094016682c410350a0801400100001010f900340ad00307428200d40800e02d40300708040d001c100d4000c20701041d04083c800d500000c12000245095250005141c40c80031a1034000e1485c041d0140c49294441d02d11a41c00b01d02e0000001882 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 843912392 1250 843911142 843911177
    0x50702060c060705070b130b04060903050d06081f090c0b03090708060406091e021f0c0f080306030c0915010f051213020f0301020c0303130206090a090b1903080a 71
    0x16442681e1907030559056140c00710001e016034210201c02e0760103500d83d200040c0c4803805040982c1391150010454505640c450751040e0107403070f00780700403030400c1001c0c48820f454584500070710000d405000702405201c2003c40f0400901500e0b0441200700d941400b08020104060144200070707102d12901c129a83d54440740c00303500e0f00107158044c2c0c11fa4400c090401041c0201a40070000b0144254502c0c120110100100519541c005801035884800c003075000d60748181d2110180e4420740c06040c0503034095015203420000522400d42600c1012000003006034501d028090181044803c5038284554142101114413100110008070305101003c150701c000140607005451102013103510f51201c600e030043c030b004005407031400c0403800340740c130790404125130b00e8180203940207000b003a0300942c1035030340d24004240420070204060f40c002c3c204200c51300c40c07601c4100384800030b0101c9a001062000c07402c014805240302e01ba103150556501d040081c030000b172184040390300c8000c1c1ca1070071141e44844070126 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 843913642 1250 843912392 843912397
    0x29040b0102121204050712120e010201150f0806092a0307090603060b0f040513031404081c1107050f042c0f0f030a08070f090812190f0e0105070206 65
    0x2d4000c007080400c00d15400c010412806204a106130295003499a0b81c0d112603144007000c41d4010110000205840e031440c1c070a03402c031503403120144004170341c140700600341d40b0701704d80d40b900030f883c400c034172041d06104c080300801496401c001c00c00000c200310134102c00c50301c540c501e10051a40b868501e80c91aa8042d9070100901405070070030fa002000701035501e10b000070042c0305048080e800b6010401c98403034103182c98800c0e1403007071240c13100c070a16000301c580c3c048618400d4458540001c440c03e02012681440401466500407000d8000c10000420480060800c00c4115101c001d603501a401c240080d840d01122a03816140a440c04520303840184120201854442000c0078000d190300000c2c2c060308000138009581000c03000644807001c10001d4650f40300e00c101c028520214920001191100c1e115201c0c003104c00340e561809550440c2c490a5190404001c1d1241c010110b101003a51510301262841000d03200d8261300301580c8401491001428940145440340d041c0200410401c055484007402c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 843914892 1250 843913642 843913663
    0x609090102120c1c0c0e0609040608030d05040c0f050d060b0f130f110702090121050303010807030c0e0f0c180307030b010905010806042f18060429040b0102 69
    0x2030340c01d05151900c0b841c6440e0700060820b42122521400441600c4580e05c26020100107a41d10010452144000c0c07001ca54410022160420b07540c42e40020000c0c030a0024090b052a9640c0100b03990429041c03070400b0003050340080460041e034110401c856510441c4601042e039000c0c0010403016013620000d03c14222a848454000840d50f812500d0540c0031390080c48103030441c050401411403c004a1960740c001c5080082d0002500760050080c010a000111400c20700788040350203290059980703c2c01c1d504203910824180c2d026940a004011070b084520b0041e081140c01c071951071410307501010b036980002d045900c04030f030000f401c2c84c4165001d50b207800803d040501100d10700d6580340382040310342c0703401d209000403680303840000b2070809008280c0c0d600464000d4058110200c3c1c1039514120007241c2c100c41c0140600d0070403000d140f070b01d4001245181d03055110045a031450010140300541d0020800e000301c0b0410305080c2c44500542d41800b90132070a003504c00103600190400180d1400316802d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 843916142 1250 843914892 843914917
    0xc11011e02070612060302030a0f0804030804030605011a0a0c030c02120d021608010209031c09051302030402040b030105071b0c0902190207270222081501050f0105030609090102 78
    0x2034140c02054000488a040322044d542c0e080344041c00307a0100049179101d000084d499040b800c1008081050105200b840714050000c03d480c05070303a551080f5082e070180d48212516901c2e200100100b4a252112002c20b05100c110180303802d9410000034101405c0b00c400500f0701001002502c07c0d922541c0c1100030348001141156481240c00001030768401e20404241e0701034420034004584204c045c001d9a150300c001a0003000001e1919241d0408007100340311210400c104180c000401e0340c0d030a130710080007400314480143c6d02e05050040c0b106407010079180e00c1c0039078100710503c0841940140490391043e098a102c9981241074540181040e8081e8400c4070140c1c00032800155260390401490304410013030f0202c40002c7e940d40f0001d42101740384d030207205000c1e24048401c483c0a1943e00101005008402427a8001000c014900d80e042415080000036512240d4409902e01d2135003041400b6000489900703c050181c400028410300c80200f0713060250303010001144c20b040c1c094055a03051101e00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 843917392 1250 843916142 843916187
    0x51015120f0605040b150406050a03230411010e0a0603020d020c01020a031416080a02070807050714150301121e0f050606041a01020a260318120a0c1101 67
    0x620050001d06024010584a18505204040070f0714180a086c0715880400301300a007405c0c030340304069419030000090f80080c1520348070142030614080210900104030b201000d01d070743c2000d0800202075441a101c4605010f204d1402c000c030759a0348403186045404901e80543d54650000110b4041c0c0a42050b02c0320560000c502c52054a4168124440c648a601c2e6144040d5651078807c02c140901800c800011a076060041446c001003038001b0404036000f0075040d840c101c000d070b44003480c220040d44007000e29241400d800c02c07249001e006541324911030a10f05800c40d41440c00e001c1303005071601070081038008182c3c0001404009074441d0300d1010f0300003e4800000c0050306019444110032038103244540d02d8202c01b10880e03200c80c01080c20b00d4006a000f4202944207640b4858010031f036070801480700c12848545072040700d02c840154420002001210044020007001c146004030548150020b440d09103c0030200e15032110707542018075040841010003418110041c2c0d61103c81754131415003c1000d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 843918642 1250 843917392 843917411
    0x5073518121c050304030813020a080a06060f0501030b060301290c0706080f040b07080403021c1805030a0b070309170c0309090f0c0a180e1e01050405101512 69
    0x1103086041011a808007070385055402c40304484902c0101d41c01800704001101240b01d246811002d00d0003e8400351070307005a96158900c187c54081c0701407044400c00d40700d10702400071844140b429401441c01b800c0901202601e4000541103000c140240c0880d030140040b8085075900c0180181e040701c25480b49260b65103005062561188240e014810125480101040d40c20442011281c4190f07044404680301d5258210111044000a4810b13411441000b60030051401405000001d11007a62076081210400c9420354241040070307400940320350020540c100109036080e9002c0e074049901c1c54005040d1401e4542801c5ca852041061104a40c01003900b00ea907075000802003001d2103080313642082598907412582d100a600b15002d8079504400c0c013100c44094080c1e41c0c803a01c1000703400d80200065469155031a011001101c000d40d1040050fa149210101c00c0c0b5071460161805035000e2281e89031003074200c0000320b5140301d03070045102080751040301c29104544080300007079900c1c01440000d09 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 843919892 1250 843918642 843918679
    0x1802190c0308011d01060807120c0c020102060109051611100507030614151c060302090f061003020915070201020109060504060b0a0626060d050a0305073518 69
    0x300610101e020030484000400d4841001c556201d40180e0009042503503820954200c1d88482c02078140310a014007000031455007141401022448410342d6144010291940002450140b044c0e0240510750b15000600c5000107503003001c0c020450207810200006040e04810514003518940b0502d07113079107000240300c005503264002008441c0809507030780d5114903080400991151742d100300403141c80c04001040d084041014810000300c1c00840004d5801e03031720380105d02403540455154002d0309030390007000f00c180380c1076041140010340c5280c00c50030300781c121010034400341d0054908a0390101c089546021a031003500721040f0a0760000003404241410b10b0240094072081128038880c00c094a00400d002d440f8a00c1850b54801010010303800300640300c80d4403400407018000c0c680198842c011140440c1c02000113038003040c8695500e0b59910140c0c10300314184240991316000408c075580540c2c10f618a03d2100500c51402d4400705a40c59544000c85040d460340206036a80240381da4804580805 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 843921142 1250 843919892 843919907
    0xd0f140c0108101e0f0f090b03010c0801060e010c020d0c031407061b0204020408010c0309141b0d02040e2416231b030c0f06010b0f0f09221a0a180219 66
    0x361100404e0040d0008d50040500780c400806c6080b00240b85080100a440d100e03d1034404240c006050200324102c954022800b0140c40c80d070259108050101c1c03c00400030201c1c00503040d031021030003900480c2d061031402020300000100c00c1c2b041001c90305002d825507039207904a900409415001300100010f203503020f4050b280c06101a03500075207076002222034540c00300e00410203d84e00a42e91400384102010000260000d000c140c0c1c1140d1b80380364401c1200c1301007002990704108085a540543d9000d003002064401c002d010f040c0e0f1181155030024640c2e04507000041c0700a80840102885500c130021445c1e034060395908410454407401031200d000e1003c001030655441d0402900d210340b004105c0705641d11700c20310848030340810030440c03140720205010140280604000300d80d403828600310006051100c601c4849a42c1641d080840a540c40e22403180c0284010400302440c41000d1000002d81e100f4041d108606a005105110807100c10042d411551101c00301d203084003e501071250b0040c0f03140f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 843922392 1250 843921142 843921149
    0x6020a020a09061d22030810081c05070302012009041505060901050d020c01050a14061e04090f0b040501020a080c03040c030206090d0f140c0108101e0f0f 68
    0x200c2200201041141c60742c02054144d03252000d480108200159a06018850003403a4850710041d69160143c00c10360000d4803a1201c0c000d540b85507807030802e101c071062a010194028090355000d03036010005055802281001c0c8880b6051850316480300d030800340d0151240110040c0420300400706104d1030040b2a02800c030341c1030140d030704016150b000707912944d00030f07540d00a041c1d0007082801081d20075807042c00180840407014070003500b40181283e20b9825079009680e0040c549403520021000d0085000c9125403041c0b0480b14583c8610368507103400303404003400c94454080c5803100c0c8071006100d0800c1105600a41c4000080900d241c203060460007174000c0c81180001400c21004910b0f258190400d0700d000300d8000003411207841c42c0d5401c02c502c9034000e90007640c000c0c4100100c074001c00c007100d10f84a0814050b040708042d0f2041c284006090444400380345041c082e443c401d01c05e4960400103a0410b0f0b52000c180480400c0c1c11010240308118a41d0066000c4850380e040410b0340b81c1013543c12000c6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 843923642 1250 843922392 843922399
    0x180b09100b041a060c10060b090f03010b01080103110a030b010b0702030610060207120c08030705010603060f021c05040201020309030a11031216110a090c2c13021c0606020a02 77
    0xc91489004000540f440991110300040708410b8529841c94010020107071800e40804030b80d1109044554601900d03066400700b151120049403451880c2070040e802d03680070f1004c4000f004442c202c3d00000e490300358180000750820030100c58104047d1141c00814002d10f400c01400e00480d030f52980081d2580d481325000300c1c003074001c220110341d41c10000740c400c209407400317074000e055928102510200074080071071040d03513221508080020000028401000401e008034000301d905400c44c00c08074150351008099039071180c81041803491401003000750105988070904040b49540301e070b000413803541c0140001a6418050145170307204210074000209020b01c0c042c0d09503681000c814010340c0e2640101c0140102c0da043c40a888000144c5907208e0351240c4500900100c07201ba1202145012941c0c1102c15001140d40025900080010030f0720305242c41c80d41c000e035041c40200d40b201156544e00e200c2038a035020368001c200c80c1c0c01c0751014551840c1405410000b000119660b0700000e40d1664501c4c0142d01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 843924892 1250 843923642 843923651
    0xb0a0e162c070c0809210f1e0316050c031204090c080c07021908030a0f02011d0c1c080d020405040b1f0f02030403060c17090a15180b0910 61
    0x40c03040000c98810320075507041c1c454500f644401d403101801c95009049003503101400c0908820807010040705a40307520440c000400c5982c1c01d180c203543c43d00301281030004000c0a02d901d403184407800002141c61286003d2401d0886065614024bc54000135228a50740350103680019400c02c0b9031a80541308a0303d40980078407500c2070150b1305a031043d400307a0700e1307403c158010400302001d420407013142411001c12a20074028a9544d10101c0e05507000020100c0004100080b40f1448903030900030f07600a08504069a0b0003c81170340c0e4556607074604038010030301078000d10140030100c80401c0c80c05031040d50840c041c0f940d2910a41c980c10001e5005005140c440c0c2d24000352000350741403030b01200200c101081c5a0302c80074405c40005a07058448445501c045110403c0040000f645134080c000d2034001c240c540b05144042003807030541140c0c006048007001e600c85e52000b07011408000502d1340561441c400001c41c0d10082c80e2008070020344100241090b4419000d005121000140e040f000c1c1489050400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 843926142 1250 843924892 843924959
    0x90303071209030e060f0c060c03070207140f0118090c050702010f0314190204030602191e050a0509060f0c100b0604080c15120f071b0b0a0e16 63
    0x1012918602005400140f1030440314201d814517500421864500031540c900b04681c0641d02031400004443e400c00300c071804001e1102141d010800312000d840e401c002c84a802004c2c10102d800c402035040c1184c1003001c0c119180ca04150741c01d15960291500001c10b008046428401900315849601c007280002d030840012607140340f20780b003002c050603035102c8000120380b9182d080d0b40c0714002020f8040047d075400c100c004000398542c8014228052040e280e42100781c2114800361605030304150b071040744848600c4040c007555118080303030060074840c2030254488814101141480c02449881d00c00e004c000100006001b00000300100c52400391002807010074800c0050007403038040c61040001c10340c000610300e049441c1c9030103040e003180010340d0964100f410700307207802c107094000750b41448000300c030101405800c03980b0864094051522310744005546038aa510b413646c002005140720380940c2d50700c072880c51003042841000701880012601c1019a5118068400e5030041100d905203000750300c2c1e4415 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 843927392 1250 843926142 843926177
    0x30504060f03050c0d091b09060305060903030108031624020d05061518030a0b0421031406010c03090314031c06030f0209100f15111513050a060509030307 68
    0x710b10449071303401450704010b1100302d0b1030007a02c068841241d05140d03010303008110105001d01700005204c003600210703616146050490408901401034905a00100014016104000216415042101d2a1510403849402c1582454800c52940300801069111860301c00017542c000e417107400350308141001940c554000b0442c030704020703180042101100344644c0e640b0101500070b14184000250540711243c02540d41c4245103401294112102c0038440307103188403d158840c049000c500c40c0d0070b04000007003020340405114000208401d0402c10756500010406214074064001103500c1a9126450341c401c142d501c0e2650040529154440d43c0c980e07000c100402c541c050142200d402c224120b00c0208950240302031500d001304000e021106650300024110840c1c680b483c000c08a1036005507116900c80c0c801445400784005041c00b503401403c0c4004400006501c02d500008040241b40000680e13140c46404d2412014028142c68a000b00f008200140403008621502141e40c8140840070505c004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 843928642 1250 843927392 843927401
    0x9130302100510060f0e040c111209090408070227090f030906040b1b030d020d110306030c041a0603150306091507141603020717120d0c0e030703030504060f03 70
    0x3c4811503c8008001c1041501451641e06001a41d01d030444210004102080076115a60100b10002d11454050144110b040c003601e000941c0302d4540320301e0b021901c0002000c001001e000504155000100fa0303003159030303400d42c0700c154013245a4200d00000c503101896060800450b4404810f0044c0188a00049800310440780c80c40c40c02003013141094148126684c854020a0200c44041c200702001d0403066020405460350360349840340969140580c5000c1000d40e0410103003100610010301c1440800c2d039001c66120b042c41c0d4196400111010346060250308801c0450301c0c990070000c00001c1c041c120070510f442c54004141a421510310340c450807011642c2d82501205035690b00ea5032000b00c0d06c55031013601d40c20009845100c0c0380782880c040b5802e801c07140000030000c8015070300c0103004100c00d0020a0b1440d44070b50b411806805442d6103250403000c28803a68241c2c64030250381e41041049c09020303217400c511846c0054110790300e490310782c900a40b6640c010b0190700041100141e0518040c2d01c01c0c0135 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 843929892 1250 843928642 843928651
    0x30b0a0f0e04080304020103060503150a0c03050c18010302130f03060c05070c0e040503090a06050318070b180409050102070b1f03201f03060603060f120b0a0b091303021005 76
    0x40c8840c81d0750b454449580c5500050001c034100354681e01c001407695000c02600d40c640782141f007209281d04080503050300312400c034a040004d03d820801000314440f080d4055881e0007000c4040d90116640a40040f4000d10802d903034002080548200402c0c52140c800803001900d1048070100158000b0500a4480380644940100814155041030084907d85a10749800a20400c2240d0900a61000255520000f40c10840c00900b010080154004819040c402c0110316900a014000e00385400308280e8442d010500d44000740d00d10040080e51030f1944043c0340590014002c5440312780380e2400c41c0304000d09481c60000a141001c403040320740c040c0c982030011607501081d00e80d458810750341540d25910300600e5240d400340e4003481500803a01d0311002d031549054181d40c00a80310b401c080e8094221661904130884800c84c280f800c0c000540d0716882c000c2103e130800c0292440340e49414001d0301a040801c5400d400c41003da013407040c500c071251000d101840c4680c003940c0380040b2000403441103d10444 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 843931142 1250 843929892 843929909
    0x10315050a170106050612070806010f08180f0a11010f030b1806031603050f0f120a030b030f011503110d050607030b0d0611130605031b0f0712030b0a0f 67
    0x100d041010390240b140e050301240000c0004501c1503900c2c00000e2040c0c1140049a03c89a039034000c2110040d0300c0041d595001c802400c004c0c01d69240003c008140c9a03000300502c101581c0900000340007070040000d456032101900032280e600c15075260000a0500540826000c03821019a00660740d01074000c10301008406055062070701c0081855029aa001a01d529050b0140c0340c0d8801c0e00302a608412009903001d18000c2001500420340c8500c1c281110107064896009170030490300541300b00c0c0c00c0728500081482c01082c40c0c8085000a428040c80d5646040c0c02e6181200850454520105110840f40201d10b4644023440010900c0000c900304240105290005000103400714000d5014079801e040103818541010309542e038131002c0300d6a15010070f802c80e1010403080a040c6140510303402410746460311504504003000c039400c50760f8038000807140c1c404002c688140c20980681c2900c0d00c0d2030300209480c00d135408104010300204500c0d94104e0240b0360100011614042c1360360303030f001150203d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 843932392 1250 843931142 843931159
    0x1050109080309010e0406091d0d0507050c0d050313080c04110a02060a09031407141b011d010224040c0b03060609130f0203090303092b0f140a03020901031505 70
    0x2a401118014105038017203505c140d6411000c5040f02c154170429400c110b0518a020071705c8141108149031503240f80040c1d042010400c00440025004100700b2000384058405a21044c4030b46016070450007a40140009000c441c80000b540c42030014108c0d921030415079080140d24000383c1222004e108410445001d83d104d1004203002419035440404402d00915003005c031034007480c0000141d50300c1b6000c1550140381d0036200101020091001049038400c3e0000500c0041142c000a44142c00c01e00762188400703c080f0200c0307420303400be00200312581e85440300501c40710000c241c08142d1032010ba405550703c0c01030800105800d01510211790155200419850401090714100001b1a81442c4000c0303003552030715070307000d28010076001550249a90002a44c1c8038500001070b03501c0d0200ca02c2c041000498030008100404040400c10040c400350791411007110000803d055500072110080c4602c60100000c85c0011590f06602030a0360030b80036038080c0f003011080c050384280c0203018040c0a034440d411303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 843933642 1250 843932392 843932407
    0x121504062307110a02100504060315030f0206030a09061d06091b1302070c0303020d14031006030e0c15130f0e0c0c070f03150c0816110a02090a0204080105010501090803 74
    0x101520016901d4440c1113503104141903012500f2851103901620104030086020f122054150103400c480705003207ca020318a40c515203403500d00080d4102d003e07000c2c11b800004a6480005a00000400c40e0482d009001c000ca00701c4103407680c008416901e01c0180103120101c2c10710803000c5040b40750700c1003800c082c1d2075254500c0304000d420b185208c60224901d6007000f9007000200928a036800030740c061307005080e10740c002e160050907601c81c052000c104070b40c0c02c00401510300c00300440d0005850a601d000150b500c02c8603000c901e0400403121469118402409000740c40c1402030040140d400400542c02d00b00da5034408a000070401800762040b0760b812080040e8400c0d1210780684204c11a1104462131541d81d050409214a1507400c295101029000c0ca0380700500580120f0310340a01900e0b00e40c0311031800c1100d01d0109201d0003207540400c114840b00c3c061502d001c110b194a03003900140364a40c0c03400c00705003100080d0700c40d02c105c0b280b55081c80300006040d07000700700702400c035007003000918a48484c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 843934892 1250 843933642 843933647
    0xb06032a041803120e0a02041d0c190603050c0c0102131401020312040f050a0b13030e011e0305150a24030b060409020d1407031a0f06090609121504062307 68
    0x200a805e420309403180050b10070160b0b840307001350004080b130060034000790840250f00f14113041440100324010407000d99642ca01d04241c035107030301c100c030210b20740082c0c9130b19000c510817207501c21204c10b0602d641c004604040c0604106126004407034038089499a5141030b00d0040e40c40e8010586815800d504000c00100070942c424002003026208009450501c400d964600c45a000142c4440814801d805002020140c00c907542102144003403d08020314071240b090402e507446000d4050307080580f03e80104456a50401e00e0002eaa10020002080540c8a4541140002842803140000d1600416091545000b407248178000030019264030710700350078150a1000b950103c00e1805416541c0d61114103010000c0300011b01a5202e907501081d20b0300d081011842002039a502248134491401203190355580b4002110107a440c150343c216100c202000000d10090090b00012105024a112200040d1110b0010620451040b481003001c21180a040940c0394110b40c0011128032102c804100c4060 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 843936142 1250 843934892 843934901
    0x1060e1c02131409060f2503090503030a0906150b0a080c090301090309050909070501020319020708070306090b010e0403020a08090d0210030f0f020f070b06032a04180312 75
    0x40c0094000440b100c0c50360808012a4228000030318201c0044080c8096024140241c94010146030036202c0c00b41002d103c03802442150769400c0381c24102000f0500e10490094120383c0d410b41c7c0103401e0300d4685c5040c2c041c1e4130141009150886146240170030b104004c0c141c500c00c40342583c1116452030300b0402800f000b40c0e110305001e44040c144842c1400b03400d00964003400348514140c03095443e420b410345000144058024007410700700315a003218809100c0e599002043d50310f0168013001c02d9489807843c0d102139041c000030340c0090f0201c0c05000e0020083c4400e5800014216108044043c41aa602c0040054104003981c0080060708010401004181800b020340340d0004c005084600701130311342e40007600c1004a1402d400119490b90441a600a00740c07141d1040b03190144400d5240c81d41c1c0d0b01662010344203040e0002e002e4650741d070104900740c070b08004072489805c1d0b40010306000038802a0101d00c101300c04070507920941c20040f080d031580c1d0101c00c0440313060360315440b81000440292054005007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 843937392 1250 843936142 843936199
    0x9031908120c0c070b0d050604020a2a0c0f0501021203150f0f090405100501080a0201020703200604081f020a12050712021602040605060301050d110d0804150801060e 73
    0x46000b80543c21030390000340220307001005c10100140d51840d20542000c19181c0042110b44214410700c10540304c6074000030300c000240d044078000303622010081e500007907410800394068180103240e8804144002030000c00d0007543d101f6000c0300d4480d03105411040d264032040f00c1c0b0385600d942c444114401800c04050281807060011f00d200000400040441c8107001e0480d02506d990744866030b8010286002e103e032070301410210001d131000c4200c540010b55900035510004040c081400042001050080004003c1c0300c0d00904041d55a1381d142c1c00c490741c8162000b03808039020422400b0500d017052030700c04c8609030a9039840e40c6800800010718800101801400c480a0044554154501240c1c42c4002d014a00c2888420621141c090041c0400c5403030303c0d004a406001c0c1040107000b591b6500401000150740495002d02c03e03d509004200b00180d482801841d802020401043c0c04400c882c508000159560f96511141e036140300c21640c102211043e180c01c218a8141560f00c07000420301c0070401c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 843938642 1250 843937392 843937411
    0xc080a2004020d0504060b090f0123030a05061315050613091106130e090a0b0f100e0f09010c180b0d090b0c0301170c01050a08190e01020903190812 65
    0x2442c803d04004010358400726000c5403600d43d1103031103e40300d140c151b001c0c6801905010b0207010301c0d0706044540a0400c03201613610000d000c2d04180300450f07601001000301250b4008159200b07400c207030001d200901c0e00c2c524100d07108080038031143c4916150f84580ac0c4680c20003410071444504801c14100140300400303007558489104103d80d04603480d410020240560000c11011945141144047c462071002c1c21010315074210391482000f080811203002d0300400590b048a080b600c800c07200c24061022a4080b40f01c0b40403d4042100d10002c9010007031180d80d45000a001a15040000b1141eaa0710100b04244900c0003490034003d94948034060040b0643d50000060050400d8490101120707085401400800300000140320004412400100c071290040042c810901c5108c00a022401510300700e0b42007148100002d00c20340c40380c041038111404004000c200000f10500158041e41c03017032022500034899040301c07007541c2c0c2548001d0151184c1081141e414040d10080d80108098041c3c2078140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 843939892 1250 843938642 843938647
    0xb06120d0f05031906150906030b060a18090606050d0f0c0c060f020c060901060303020f16030b0403050f07051c020c0a090b01090b130e0114031b1207030605040c080a200402 76
    0x3082280b040030050400030891908402d20b00c06d0081003168141c211104050900010070031903180c100c2920020003c80c14050795010031300502c2e00c0c41e06203640c000030f001c5040c400e0004e0790340c1c0c00c04024610109210300c280b10b8284490105d03c1a0780c400d8140200149200e0780442c0443d4040d4041ea61390b40c030440e4090310780241403580703520704403040d201e1800595680000f00100340e010845681c0f100800d402421418210890035080d054880c0b102030a031005000004081502c184203e5240d07100381d0b002e0644807052418600d2707640002d8541801c001403401c004411481c0002080e2100480003008141d08078200801c02028010104c4001d040c000342003408140d50024402501c40d00c1e060280d0040807518050007494420f4042c0d10031140154181c00240e026100403030f03002c94180d0f4140c00a4058815500030992104072081c2c02c103120300864402104114241c1c015901031806030000210281e2503403110b43d158150721703000500080445003046400340740c40d0203180f486000100010b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 843941142 1250 843939892 843939931
    0x5030a141905070810050705160809060304141612110a050d0b070f051602091314030702090c0903060615070503030f2707051c050102070b06120d0f0503 67
    0x1d00c15000c84044445411504007441035040130480030701110300702d03842481302d400d049174080d10074481e040c404081681c0e00b5410909000103001155950b113809010196286040e0406600200c411003081040d401030741c031400c0d0006164200038007504d007525514030710b850255407100c40503899003101903003090740e4500002c4c480d6158508048d44134001d561000052404110052020602d100e55006020b001e000003000304040c007841e40403407541900d0072803a503107404940040c0582c0c000307801020000b00081c04514002c020000c2c10106200362462107968441c1106504c007130040010b416010380c0458001800ea2800c0d00d2481c9810054800180c40c0c65020345805081d940700311343c0b014100d06000180b01000b1403d4611003800c25000321442d4101c000b00ca4815110103480c82460320523440032040e9014a0f80c441204403400380c0c440000c550321145480c10300340d40742003114800d200b08018041c081640d200420281b0307801d40da9a0381c0407003514112001380c2e13041c3c00181004803040c103041246c0c1c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 843942392 1250 843941142 843941173
    0xf06090d0b0c0a02070608090a1410050106091707030f0215120c09010e06030412080a0e030d0b0405180316033c030207170306040b0d060203011e05030a14 68
    0x42c02941c0003400e50382d07109008080686000007681c0b02208000c150810081030369400b08140c141603510800a203421809078140301d2602d25038540030084c0038607282c0002042030f00942c40e1402c50703441d110328100b0501040002030300d44082c1d00c80546040309100003030700103240c0210000b118003d000780c102d00b00350f60100039643d420021100e4510901c1c0000300c01e003940d83c110001d900703407200131a207180c61407400c1d41c1c0d207a02c0c43c4c800d4066101405401004500301c9003a503046184d07601e82007000c59850701d044405140143c5440810b80340117900e09030204025405255400c456030162a00075031600c001c0d05101c41c1880040764087d010010001d031346001003058800340c406840b45c2c6083c3e03241040c0040202ca85102020341000d01418810405500001c481c4505804020041c2c20030300d0700d03603607603c001c54041d1404030100c0fa0300040060f0410304104942d400395052315040796401003000d04071651525040507a009865041e4401801c110009045034003d8004200c0c000649019094100750b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 843943642 1250 843942392 843942413
    0x60c0f190507150219030c1103130905070c02014407020607080601090e09070329070302040b030c031503010e0a0b0609011d130804060c120e0f06090d 66
    0x1680041c00024448090001c00b8100c50401c40c40e03810214641040400c1401103884088078102c14562181c0581d810b16020707010400521515005803a601d8803090104842003459002e2100007500c1c0601048440b48981043e0b0512035040e164020305280f092000c0c9072a400321000341c080e0944680504603600e44c020204000300c03540140f0f4200714101700c4800381c1020401040703041008007a004100a40ea40409424103c407500c400d0b081c0340d92950000c06003080d22a80015182e4507000b00c9014044000203188054520002d00f1181280c607003050032401d900c1248289401a03409201040080040000454005149d5100250b2000d06000440d081d100a00d00811050b0023508030314091055031455541c1c4141c2c1140c44001c9581081031555801043e030071500c170740c1c1d558100001c03000c43d80b000780015101d411080c01901c032076840030002c1454202c0700c0c040314a0252051841542801024441c001041c0241030400e00000c090a100490f005800c2c0154070030049103030803000c5001c0906 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 843944892 1250 843943642 843943687
    0x705030418060608130201140d0f0203090c01020f07180216020409110a050d0807030f0c050f06060a060f090e090106091118061201090207020a0306140a0617060c0f 72
    0x20105042e032602c000a4541d69000b86103505051014680b00e0050380d000031045003986410948a44030040b03003000100801d2880c01c1218214400424065500300c0001c100c3d4410200745d088401d103018180003252100c08038440c1a500940010204064040f5500900b458052084101418500a400080545030b0341c0b03c0640b41e28a016809000505110304450041c2105503080c80c0f01007625030701c82c45203110300c90018041110040c1d40a9400c0d104a074120300440d040012030b8081c00d2040320564440405487c01d62003558401000694217000741641501d103015900c1c1d85580358a0005440440b031070042070105655a00d51001c43d101e51a0300c12861403040c8140b1103030f19100b101d0060b4014450422040e80300d10014030070001d00f45d4141140390306540400801603101d070410b20102da40c1c42c469400003031600c1c1c28901800000302c10415643d1043c1e2844400b806901c0c2d4031040c1000b00900c1c1500108517412505c0010514030502000b0104680e030300f101113151541d00f11501c65440c40840 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 843946142 1250 843944892 843944939
    0x111060a0515060c0705041104180507080105010c260405060d0501142e1205010608042f010c051c02100c08011508090c040e0d17010609050607050304 66
    0x70a0140c018074011000a401e03000f581e11520f010b0010680315551512441071600ca079440d48410142600c01405440052030001100c040b2554947c20300300c0501021a400c5001418003000020a9032180d031803006210b030444242140e01e40c0701c084c0c1d06142140324640c0c0c07024200800c0300040d541c4031000140038000541340006401d5040140340c19001400f60550b5104510b00c0c11a940d12800701d452001c4e0309280c801d59403c511001e49004d980e61141c2c08051080f951500740005411504000120f01c1030744100381c8112000e251002134603400c4242d940c00c0280401400d1100030f1540200209800c4a00401c2103540c510381c404104074050085208210050301b00f09511390103803c1c02d0003840081441401d2a0a540d030421890513983e0540582c1030b010051028007082c1f175003a0a008103c0010005041800181d02d6082020368400c0183c105400149203410301c00e070401035500080d8140c4107140d40e5242c501d480e000c02c100c0c15420001c4103403110b000401c400601e80e91a0f020181c0740100c81d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 843947392 1250 843946142 843946151
    0x60b0603070e1203090307060807140a0e0102060a0608030f0a03022502100908031903090203480d02030304090c0905010807170604020f0705010614190806040b060111060a 75
    0x24140704100c3c0c0c44014407540381c0d006000c2c1c40d0131943c02103036603410742d002441c14442c150fa5195045820100343c03562240e040c00009201c10103554044400d54035104280c080701d040352541c840c0b071000c907020361143c07103007540083c4500d05100c0840c0005000070748542c9005800c081d0700c560030240c0e0042080c1d0040c8081c00051042c4110705214807501e101010b1800c08003015440d14451949920611460305000c07610400f020a01d18007990100c1e030300c25000313000c0b503141202c84040c0900d450aa0b002e01000c400803074426660700f0206580c10807041260f810b150b0150744011042c0040207500203000c030b905003c103100219545150384141580d901190751003500312880c140024040311342c050481801c000280f104007800d0b010000329517800c01c20a560044e075a00812030408114000c0042c01070403542002c000184486a40a15040c044c008442d080e01d55801d5000106045c0711034402e00c480c68000c000000c0108181501041d4849010304002c0e241c15003814809007030035802c903000c85026030385 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 843948642 1250 843947392 843947417
    0xd021206090d0f09030b04150c030c080c090d0204150e07020615040504050606131e020301140a0e010902090d0b04080a08010f06090314191212050408070f060b060307 73
    0x1040441600300c0b6038100700845003c2144024807070340050102030711049950000c41c1c00c114000000c0c180182ca420750400c116102044010042c1400030251400150900042580c9403a000e044030152040140480454250742d400c1c4809844107050b280301aa580c1c1000140364241034202074420809d0794090599484c1000a40c004c0303400c10148140110b16010403c0000382c1c0000d292900080100d83c0e40f8041c254184064025065007004107105024643d204074003542250003842c1690011491030f98400140030510600d0001440f03a48090241240100b000c00300a03401070039200000351072513005014640ba840900082501c080310719001c0050f1401d80d90782c0c080580c038017402013109405a1146411070040c034461041c0000303031a0210100c0300e1407812604000110009a44000300c001e411502e00384a6000d80d1080103007004180504c0c42c158a018080c0308030382c804e980c00300c0341608202c22a101c4040c1c00f1800d0f00110381c825521968416155130321000f4521500d8941d0741c40c5c810510 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 843949892 1250 843948642 843948661
    0xa08040305010c0e060a0e030f1e0708012a02100204060507111e270103030c051c0914030115031115180d02033a08090c0603060d021206 60
    0x2e0a034807500804c40081c03050000c80d91a00304940300500c0780c0c682046002c00240000e4240803801e490f02c900361181014041c0000c0d004d5400802d040280c0c07003a101000d965200e914207030340021302510102c840740ca20025221200e44c80034011200b991048980300b1244080540072a80950001d0000c10001310b810340802c0014441e06c01d1001c0b01781e51490031100442000c0d82464540c540c0103114203c41c08a0100c040c00440403a00348030b141030b102540e075581d24240035006d0300c9505000c0c0c1d8903000780302d05114861030115000700d0000d02c550302d00d4400c3c0d1900700a42140c0c090300840c0355055423074643c0b417030048100d01040301c06140100c400c900c0005181040040c0800480c4a100c9401401c1c841c03030502501400d400f4040d04401e58200803051000c0c8002370805146080a800100001503508a41100b07030306100e510304002042004200000001036a02060443e290112903114501504180c01c004000e541c210001425100d80c60840f139000480b2280002103a0003c0e92091041010048 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 843951142 1250 843949892 843949901
    0xb1e07051207030b0a180908131e030507050d0f141006052b0c230906011d041a032b0509090112020d0b0705071a010803040306050c04080a0804030501 66
    0x9443c01c04020007a122070110f000341207688260400d40220544074503404a241e00400d00195004603441c1d5503042c1e40208007031210f454040c00b9400e03511850b002003041c2c400c60303041043c0c1380c0190092016507c0c04040160540400b5403c17079181d01c81c0350054000612803c440078035991100e025018640c0d9061402c001c60b0f0003a80103511410420000a41350003e000c41c101e4080c4075580802d8005541d400c0c4030480700401e60000304450408032495040403550130070000c02c000c1c1101d9080294403200011114100c070004841c0103c3d1002a0418031494194400610070300103211551200081c08000383c14056440c00c0480584c501100098510301034135034503001c500d0107040403424001104042522180705009400204104181280c155a50300110905285c0e200c5d038501e4080c03030420307401061070300440000c40b216217a9250100b04441030044aa06880c00710000b50f06081ca141c03105000b402e0040e0115030f6004081001050980d0107000000000f030282c54241e50322031640c5800c50855 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 843952392 1250 843951142 843951151
    0xd0912030e0c01030c120504081620030706050f03091c110609010c0801061404081204032001080c07020126041505060307140f04060305010b120303040f0b1e070512 72
    0x1460017001e5280c1075000304004401c101d01000000e0aa695071901c000107104042607454888181c01c1120108100081915009025408ac200f4803001d24405d05a80d51340764003885006c50801c0c4515140015048041c5a0041c1c8080480304501e1003407650306c10142526032000001412840d40c418460b00c10480980c0003d0444000c00c200440c10400401c070280c18044c034820800124103000c1030403440d009a401604018041c0c0c0c2c1c4c0c0840c5000590503952003031000303c03140c419130b41c070143c820b21511030322103000030040c0c41c0c0108558a02045400d03c2d80b0091089040c800109000ca0b590060000000c0c1d016008001018141c01d00303060061255061094645d003550524007007000e141c03000725400003212140441c3e104601011070015134159000744031241c000c0c4c43c08000006200d4150000c1140c0c5505542a139240c80720942d40544911007182e002e4020200d5140d00740010300d4030303500c0d41e6204810030103441007030001030030070161040c0c11789410000030310114944074003010411106402 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 843953642 1250 843952392 843952397
    0x20702041103060f0f090f06060d0f1d03030912090303070506011e080f07050112020d020a031b020d1707090e070809010b0909061b0d020408011505060f0d020d0912030e0c01 76
    0x104d001c410000702c40d004003c01fa1340c01040c03c2e101140180d03c50070265080c3d0340c00f081050203c1140192540300034100450f122015031890005880c01d26400720847e070040b01401c02810035030801c60090303203003980700a0000381c0501c000c010ba980800c4003070022a02170520014400c8c10018105042c00100845400044c0641c20900c4443c943d82000540c40741190001c2c00c012194550300c00d8580d00a01817003032003000300c40c00018000c0f07960f035250780000b081034100780d102c1d681510100400ca030740301c009044200100b40d5160718850f01c1595204641c0d40070007145004c4032000d455503a483c00300c900607070f41d080100340e0380810722125030400c1c0160006040180c4411086180402c507203075860340d0142a181d001000c03109080020428001110708026884000f50f544640e5502d029008003620b4210070342032a078001011401c0d2030180101c0d0005440484100c0c00d0242031003910000354002c074144000240d8410580001441042202d4450000e5032000152011804070240c14140b050002504 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 843954892 1250 843953642 843953659
    0xb0a1a1603091d0f160512040c030f0f0b0c0a12021e041712070210120605090702160b0f0a1412010e0109200a0f0e0909010c0f020316060b04020702041103060f 70
    0x25000c1c3c1c8a41520285480e40308145a284c4079820b00070340107640b5420160001c03101010003000e006003042c2d0050410711800b03880e80c06680700c82e6483b0035070041d56031201c000760720022860710050803500580600560303d1201c00300c4411104404000e0380c4541d011442d060103000011481a1051040036101001c45078035501d400001d900055904681c2260442813141c05a00c07581c03803508980c048005450040d10728620780c02e120502039036451011038214500007031060b010460044071005e40c2d25550129040c141404540e02c02614000d00c031500c50f0b07018000601201081c4880881414024a08201d241142c0d50414203420141c1e100c5005c2c014196910680700d038a02207194080301d03500182c0b031900d001151300b001e02c1140c000b070820316815032002e01c1e5420702541501c198004d8402800c03c1d201c46a158404400580e128080c3c0000c000f4109014503420000c11405d40000300324240042c40180780c03283c7c43e4006012a402d41c500a0109030000c402c012040c00e0a1040c890a15000c480b01c50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 843956142 1250 843954892 843954931
    0x10f0222140a032a030b0a0606030608060c0f0c0610051203030727030b040c080105090a150c111005090615090402040f090b0a0b0a1a1603091d0f 64
    0xb641015a40310041020015a4500b002d5203400112808040f0004030b011440c50b5880c2801400c405055840c0b07d0000c1c54208001210b46c001d215140803120780d003020b03100c2e965550780600391980180306034505e0315008010020b038480060200078483d00aa10b10120540e04280c00d11a845003503500d050f2031a40204284602240c0080b25054581540b500b51406010860421064144550700061111154105000801c00c180341000305031100580200541d98036040401d5840300041030140110a210700b003052074620a40207921114102e04014580026a0300c940b803503e074400d881c50700030640e6402070019601040c041c1f10742003039014201d00c10042844000407803a440c041c200038855603490a4918034a69103801000d12103801249021152524a5185001c0c01d50021034070f2003118514008034018a80c004145e084e507207260507850400c818207500c007440303129032201502804020000019003880340c51080d0310002590440700218200707500116402103024081000044002c0c8604 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 843957392 1250 843956142 843956149
    0x50304050d0801210203071206020c01050703050c1801090f0305011a010918020306180103150b18010501081302061804060510020d0c06060b0d06061b0221010f022214 73
    0x401840e82c00380301c81044121301d2002034908038003603101048101c650340848050020f254080d100c1140450001c1c00180e5030204114120b41d030843d1031650349181880711458007000010f09043c547c906041c001c040545643c804400c044455000322160780d10340d4180d40c0503185980d59003039501428244600701030305150580726004018000714088903404400103116070741d0a25078100190080c81c0c1d80117903517168144195908101c10080c400d042c184039a0b282c0d81d003071092a40c2a040c8514550990341e0f42050011204114044c2504040149030210040035a60300801480038400340e4005a0f900e0300a041031000303850050340024403c00701c003500000d5950f00400e009007000c4480c0351860424480380f80140c000c18882c2c0040030b95040100304451059445d42c0400b084d503a203605d58980f444400c114403404118140002034000c40611509076483c48450011551420420000300b0102c07420107110b8100d03042107130a00001000c148003a611149212110b00c0904000c40e10320b03038540c9100001c07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 843958642 1250 843957392 843957419
    0xf06020324090a0207050c0a030302030901020f12091c230705010504181e021215191502030c1911030303091203190509010c0e03070e0c130e07050304050d0801 70
    0x243e00c10a5000144a400c0100600410290387e100074860420142c0f2030900943d01d070001d00107540544182d14031000e00c960001520309051030b25441c100e240c1140c000c248880d00800001c2503503080351041050f070010710051084090391071290b2507100801484030545103001015803205060200801003800940d85280d0030700c40b95520b030600400d240c5880e030001a003003074205014842451004c5042201005000b40c0704d4010301c0061190440b03112200308100110103c1e41b900807448440c0d1004201251003054801200600380c010b403801d00d040445014102180300020031101c0d500e0441c070500f0010004200070000c1415401141145050030000d580c52041c1d07001c1400010021000501100c40b40600d4040c204030b0f0300c020f2040d41480320166010701251403e04012032503103008a40242800142141110f130083c02418864036403607140c048682c80798a22a03a0000d010304e002c203c203408103450901821040d0f41d601c0e41d074601418440d050000c0d46607600c080106080040020500c0c0000c0d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 843959892 1250 843958642 843958651
    0x201080a051807060804050c090105130903050f040906050307081504030c150c0509011d010c080702040605100503070f030c08040308070309050118150621050106030f0602032409 78
    0x8000a203034450190109414407a03a4582c01103100e8841c022840550010505014900c10303801c03549454054002c0010300d00c400d028480d045004000040c030300400e150010a0240d0103410141d26090645000c08030303650154000500c41174607540d0411031400e0402001d8001e02056001c1c14808400c2106060301a00207080070301048042c0c0500b906202d03404900300042c08803d0000c0000d070808010281c1707e50801020107011a01c1105e440d45007841d00c10140c0c0114a05030741c4d0f517a0309801980c410342c4d99008050280d0300559501008034158030340c2c415031706a400058a50a440c0c1c0b800034401010112050001802c040c10030031118200c54108450542144d414100402c02d44d4459000324000c0c41c4444001e0081d600380700b034100d001ca903c0c20ba082000c50241c150400400c1c0c1d0210800c065501b140b0500803201843c00d852840964902031003200c5d07a10400010414030340d41d481c2c08204901c00d039002d89549500005015038a204e0f03c841035076008212000c04020200080052641c074801032 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 843961142 1250 843959892 843959911
    0x150801051302060c010b22051302010f030f0f0c320415020f0601091b02030322140a0507090f091502090d170702040e0304080309040b060d1d01050c07020108 69
    0x1303020000780300a4020310b46022000d03004034025460350b200d030041da0b0090228015100d140c000032800d50b142d5003100768070b101c0c0c043e15010b280540b800030441c010424085008805a42c4545070f0304080828000c003d0085e005595001030b4000022000144581c5061a5030707075900e1980c919071125030b425055a08850b00000100c15030980c550f0207a00706208400d6911f61402044000720303886c10301d0740c04107120005410405111200c8403134240d0340da00c81035030800456038031154121062864140024a1540300302031165400025500705c5141c00303603440c400c540c9030700210f800f440804950f1048031514800d40d0014424211681c841d1094224042e40810b502500000d155040f6218034a081d880c45074000c0030301d600305043c021011415000f0b01c204070300c2039041003682003030341400200340d40c15100d1201c05103160000002c1000028003100f001550048000c0c841c40000a11502c186042a02d2200d2480340703c044502c185400c4980040c9000e0000c9020701524001d40da0216060741e02000d0b92 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 843962392 1250 843961142 843961147
    0xa1806260a061109220f0b01020c040504080705060901020301060f030b0105190315061e03062d150e011707200a0209091c020a0b040318170115080105130206 69
    0x3c1d111640700f00901e8942185c0001480f50550a4041607000e94049550080008100045155041e90075a1500600503446520031303000c41d01d401d80c4401d820a1160310354a00d0b1500c10340e19141400c80c104c6a610960b503001c0010000c0d2134006042820f0180e03180340410000c000400081c5c0315002e00780445114407480e0801d80d102602035440341420a02c90b20000c03024666640e00100a2003180d5a070350348060104002441e82030107070140e00c090340c8200c2d03100c00390b481c040310008599040c0500300ca01c400c0c9040d20700103a000e0b04803180b911032040c90350f03c0e400060180c01c00507000500c4001060f0380c0b02c66100400c20415446640c2c84a09211029820351240354406035525168401710080e501c09046018881000b400242840304810300414100d5565200007050740c032100d6960300500700844000c0003d0011380315010b402c401d141040007000800340ca550540951032440445000d850790f55012000075285402140d200428466000f44030f80e2402c28100122610030302d00007801420301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 843963642 1250 843962392 843962411
    0x302010608160308090a0512210304170d0b0d38010501050f0403080c1f14040803131b05131a010509031c0315080a020f06090a1806260a06 61
    0x10300d03d00706c0c01050003c20074030700030456043c03440c1c64024020380e481c00f04000034403030041008036409580c070030381e0000e9000101c9110303505150702661065089455440d0349140c4003105a50b00c410001256014202c00d29400c49800240210309003252080085040035079a0b540d8103958100d0082e040d950b0a01e09070b6110203180c4031007406401641c2008214090104602e685400d00241c41403a84240740c0c00400c00109041c20b0703400304c0e180010400e610400b01000140480c0340c035402141c0054038034070034000c15003807612610300c589180c0c0220351134030305686020000e52511703c2860303402c075031000d00c104500e4900001032020b66000d82100c5040c01008070300107803503981c2401034004000f1521101e02190740d18aa0040c02030040044080c6482c500705400b00b800040020755410300c55010b0305115025002000b000599044003000e2075100c200050003040c41164081c4510f50103000c0135000c00c2c4c4606141d9480901220240d840c441050703c2040894148030020b100742d50582c000c2c0c0c00043e42000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 843964892 1250 843963642 843963649
    0x4081f0e0a1412030f070e22091a07030608010e030405030a2909030904150b0703110709021614011e0218060739050f04090506070c030201060816030809 67
    0x2d5010a0031040f200100800c61420540d0944900c030340300940d5a401401070b0f20f0108800720600e2a1140c41c2381042286c40c00510189611039104180280010907007289940352404d40120100c0305c0c000001c0c0c850781c0401c07096400b400340306840705000000c6c6043c03a0a01c40441d55901201c4806841c80744401c0340c084551a94541c5180e05480100750321585107400685e0f142c0c1c990154412600452901010129000d000b00c0c00c801611441c0b10704614011054404441d403040d49042c3c1c0c8078a010f01040046c07040d219100601c0d50b14007409040d0074101181c2081e11060b607040420342c80c56414800c1a003002800c050420425035056800141c4401081c0c2d000201c2202d840401500504009003070030a00945196444c001c101481e400a044d00003282c060340c04082c200c01c0300b01c2407040e12100740507918011070154814031002e403001800484031380311341d031602005030356002c045980700400f00c1c18150f0a00580b4054110301c0d0041c454459151856490f201e0984000303483c400c008a200140340e0b4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 843966142 1250 843964892 843964903
    0xa050f04110d02040f0608070212191806030f0501090207050607080a0207021e031e12071a0c120c0406020a0b04060e1e010e1f0c09090204081f0e0a14 66
    0x14207002c045455944500e401000e0440070b019840c0031480441c00218502e01c00608090880a011185802c0003005800322034510103014140b0180401e140080d0001c4c1661315000004090680d808103400c5d000c407800c502218010707046480324500401c0a10042080041c10641041c241c0ca4000340960b6001201c0b8000d015178580254018035403a899820700c803011400304000036088068550700c81514030042241d6010806400f1140c009010f2001c0300d800500141000354025060301c1d90801400ca060054280100c0708100d0741d440100d00c4000320580b6841c019480308110191030319007410210040c5d901c414410700201810240c00c002010000030703030403c000128091003101c8541d80c201c00440e5900c00214901003080d80b030410040c50103140010081100400c041039044001c9801e88110b0142c060f504800083c4400b0010000d05100e0310b100400c001c10100010b00b00700107504002c014000c22003002c01e0300700340c100b400401c01c50134003041824002c1c0d0f2080103080c0545055209a0030f00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 843967392 1250 843966142 843966157
    0x160e04080c0f062e15111209120607230409051305120301030b0406051b07060905010e1513060e120c0105060114030f04020111010c0201051602030a0215060310111201050a050f0411 79
    0x14002d091f110003000640170050100403200701c0c0d048040301c0402c007596950f92000c4450340d0010742d980010030390b45002c04104000d85403012240c585001e84803c0c0031002d0310000d54401c410540b1418000c000c3c400c1c10b01c06211030f070401400c0c0c00d02d503524507150044160300140c000740c225662180440c50019809690005114008100b261540c0060500d40d0050940020503103880d4200400c0b40a00f0202060b8850800030003a24401c15807118000d0a141603107031a01256510368138002e142e0855000c108a0300c5848031840c0d515600c10f040203140c1e081d503001401ca641802000700481d9401c1962405907a4000000715501c075050360750b400100c0712900c04481c420255440c04000c08403d59040d0445c51181a000008a08100c41c08030f04070780d80d2041d0002e50f4016040002c031450095118101c00d600064003c2c211100c000416010300304070781030503401121101002480002c5500e00801d40340c010001111138082d05850140491400d42d1030400d242d21555940344042d02e08280c3c80f050302c411 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 843968642 1250 843967392 843967427
    0x171b040512030a031a01020a0b091e0d12020901050f09150a09030b01140d14011e140702011b0f18030f0212160e04080c0f062e15 57
    0x259102071a800c0d44a0b48252120740001e0b00b401c8800340c02000c60241c074240e00741c3c182d004080c000c820307440b058103101d0003601c0c850060042080e05495407200b0f600030300f040003a8001409140c031046001034044c2c806c0010101d1160700500040080c1d030307080415903691002c1c0040c03460303071102b0640c00910b1540440760780040046001c02c00014059000c00c9102c01d80f4070450041d5400d0340c075444038110791200e4000c056800800826203400241000c5500c501c00c200d50320001c03a102c8418203030b409440a415114a20259441340e00c5519100001101c0c1e811011600081103510203403428180320344800700e80c03502844000500002101e01c00c0340c060380a0900044240c0199449242004e01e0226841c02644181d0303030300008551450000c81c46100c1491000d149035021440d00340c1c1084410001003040d00e400c0414040841d01160030f100f4084107415003c0684080d2400e1507050441c500180407011b582503002007210810b8070360980d584180d0f400c403070207250402040b9000b00c0390700381454640b404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 843969892 1250 843968642 843968659
    0x803090109150c02010f0204080601210501050702060f07031812020c041505040501060f080105100309050a03200d02031b010e0a030e03011a0315040201030f02120115171b0405 77
    0x100d0852036032080c0c0c0c03101100c4e402800641e2441c06504141d00503402810718a0700410b004002e4201c0348810015003841d0801401c1c2c040c441c50b1121401c40d0320440c2c415016801045c1000b0211400710180e95000070a0b040412460755403c2800401030b80310900200f88050f00070010015a0003004010304201c0018400e01c00032201d032007480c00b07694480c0b1401c2d00544c11309002040303a03401505446c0303002c0c03010780d83c0b1442c581c41e14003081701120380d031820301081c15610030101020075014000080b0300c0780681c0f14030950707003002031030082003a040c808019901e8003e4000e00c0d1450303070701004480601103010b8184441d0002c4215990040600100d0703c0410712030442d802c130030190000e00510817804210020407001640440c4200e0081001c044140e044c1c2059282905d00f0306c2d44000caa80290062400152a10078036400500b242e00039200041a0600074004000703200c41c841c41c05900104070f1600c0101c2c03400409c1c034080000360203007901313140c5084403500c20010001301c000d4030300424000340080c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 843971142 1250 843969892 843969923
    0x3070c0f0201030b0a030c08010c020309061603030f050103060e0705030c0310051012300f05031b0d14010815131e150c0215070c081c060608090105130803090109 71
    0x140043c01505c15031b0403a50030180ba1404440c00800dd484446002501c85071400200024000010742e0b003c02c100c1c00c4c10b0342c03000f4680d0008064801d03580070b94803c41d03000030218001003165103800160780c8510703c86ea0040303241f1000c40d2070200d4a410050380048000c1165116000b200000740e42c1a00007010850609241006011000c0c6281d4000030000050440940c1001408141140d4801201022420f80b03410700d04c0507440780d4001c550000e1800d4100000100194020400358007010095030003540b0340c440742040e44c0c04c401407035006013071304d0f0f0040c2a013a401c00c040207007580000308580b44c07680418000c030042c80200c44011080941185013a07059124500c2d0042c071b140640d072040d000d050714042c031400d0300c6400001e91041c0c80d0b0032000c03401d60681d00c0b40c1c021a111030a03a00c00f02e4103480240444440f000740c40800d890500c00f880808959207040c041c004180b0a00146404000d0781804148400444c015070550212900451a03c0d640c1d1b41f50b450450140820303180013006c075803104117010b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 843972392 1250 843971142 843971153
    0x6360c080d0f180b0a2604110315042102100e0d0305061002100f11130303022401090c0e060a02150a09150f1103130606090203070c0f0201030b0a03 65
    0x18000b5111a110800a5206841c003099050104e02402c0312000e410051800001c1c003600440030002204900f0500000c80d02420400082c3c043d142210006042e41d40e20009160601072034030350f101c0d450900c410901e042d0721900b0810001c6141900c4043c248021403a10910038800e421070707084540c40900201d00c91110603a510500b1525850010385450081180c3d0300c2d0144c1d140103641e40c02d03801440c001e414490183c0c01010000e654041075950b44c00540d81407041c89002e011b10041074901600c0152540c1000307814148000c002c0c0a610042a4503030400c02e80100f206815030ba040c00c80010211407400090f33a140802e90304456000f0f00200d034203080305500249904200c0d16036800034140f511407845113000da0b20903c1d0300402a801d4035003e403045800c00d0b41f1844901c01c201001085020304210b101030607600649800040d0503d0f0300c4103005201d014000e000003803501c0c40d002c41c0345103814500100b402207000c5009007039040c0ca2140c3c2d815a840394102c007004c810004c081010b01d0741d40f850076 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 843973642 1250 843972392 843972407
    0x1207060c0905090f0108060a0c0c06240b0d0f0207050703140102040b03010905180115090b0d1a0a05150f0105070c030501050a0c020129060a120501060c06360c080d 72
    0x49a2140c1f00b40000192100c0340c50040f80e80c2e550013134842c1c0300e00703081c1d40c3da50070040c02c100a059078041c800d441c40c2e800560ba89042020047c00c00700c50752075865450003040b00a4540030340d554850140100400c030000751001405404685c1c000050081441400780d100d40640b003030764040c42800501000105810005902c00c901605a030000100d025082c41a0300d800da0b10320102030500000c880508114a603525001620382c4000284a114074161659800f2556840c4881030901c0580c02005c02c555003110384035503600006003d40d00c14050ba54080012204124000c00030304010010a60300c0800880e03c0525024641c0071009000d00d24000c00c136440182003e0001000541c2007081c0c9401309030b0019505a0a1040041900103503070840303042c805c0315446054082d00300000d03001c004e403a5120310700c685800392405680750b0202e803446080c02c80940d400201d909428140002885120051000401003403d4800c442000c44100c81c0c1400c4802114551114945000381c00008515580c0481e1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 843974892 1250 843973642 843973649
    0x7020f121c0b091b040302030609060f09030324040902030106291624020a1d1905040b0d0611030601081303050a1409210f1207060c0905090f01 63
    0x181a0040150781d00103860065001d19002041c04003c140b4540d40d00156208003001d8428003850541e403540880d2504000301c1e035a9800750001404d000403406031044090f000703141d800c029825400c008030300351000303605d60340b4802c0014262003ca04035030700ca070b8000340307070300c6400400030000340d5034645050481d103034120398640f4080e0860b014030703403c0e84142058508140307800005800d540c40c50744d900280303110107607044828880c410b2240210312042c0d0008000c1480c6035a600c1440c03101d1141c180051905210be10303032040948002400b5103114800d5060202c400c2140c02248000094000c01c01c071000003580174050320b041c81c0c624101d217400b000085000b590282c1c0d8928803903807454030000d04082113110040005100f04242c414251240c00e0311031405181b10300061070000781c900012030b40c040404030500e14140011200205c8402800190b00c0c0d481000d001c0d0000740c4080f41411140d04c81c0c0d640045c2015623494000e104503100340d0b40e007000b5040290111325141480c240b44800b0300030911 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 843976142 1250 843974892 843974917
    0x110303041506080313030807170c0c0f01030c171906060e0916050d053120032d06072d0503010603200d0c032a050307020f12 55
    0x140c0016940f44000100c41c0044110703504000d101e801e642c2d450400d5804004140d87c400078103030401122000100061110080307040c0104071034442c00d030900034001c034440c81c41d82c141440c15400690f55900319040c2c421040c691101c02e441661044150a80c4880007036150704130754076040c8041042da421000030101a00c0803981c1c20040c0d6121040465005880202c960000b9414070500c00140c056030030468012109040d1840000d6000e81111203c990020031180e25400780c1941704c1c14040c2c4207084564010115054245242c1d510307000c00c1c1d5418a030b64910404000100001d240d1000e4044103400c0b141c0c1071000d0740c500d82002c0c0c074010084e014800e00100111080c8809a403100460201c511203140103482e25401c0d81c2c41c0c1034040e0010a121561005000d51015403c0c071658541c000828105140d18800107030f91140c0d6800404984034203806c107451034510026010703110020010380324003c407140380c841da41b5641c0300012421f10103104a01c040612aa12900c1c000000f0540035140004245 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 843977392 1250 843976142 843976151
    0x27060d021c020c01241a1318060e0a0b030c060c0c06121602011a33041d060a090b060c0604031211131412060a0209030d091d06011103030415 62
    0x500c00366802c4052446402d0111907440c050079440038001e0081c010709940d80307c1d50080566034820030228265140000f0300c58130703900c1b0000d00ca00102d00c285581c2040089074104104642d66002c2680c5401180c00e45120300000b0520180320710003000541d44405d03016050b652180140000d00c50043c405603104e00003400d0490341414003038414400c01600788051001003078a20020030900003011003440b000f15003a106099024668250007014042c6000c02000d0036503078600d0f22003443d2520742908950041d2888040900070700717031307900840481520f0440702c000032400b00c0c0c0c600080c00d0b40710341442c40301d40b8050304040001345a0072101c0741c049108a03100a00c0b40e04031440a030301140c41a45c040c500d600041000c00c0c80701740318440c0c02850700e1602502c0c00094984c0d020005d407030300b41e0403a05040c03003070b40001d079412460409020030b899040540c02d101d80c5040c00c0c40001d45403e1701c020b1030391403d06d03820000503045a10804c0543d0161007981c040da580c0b41040e040642140c04803060242065040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 843978642 1250 843977392 843977441
    0x5180411010206130b070c080a1706030f0a1712010303020d02060703050601080f040312060f091404030c0b0a110a031a03060919080c011127060d021c020c01 69
    0x11403c1c51042c5503020000d03101c402c003a540c4104403c000ba000000304001020100f0004403032000804c26500c0e0794565424400035441c1404d44001d000b00214007940000c0d081440045c00005c4030070b120390f4080a220003809d0800c09800e254040d5140c951403500c4894000020b140d0081000c540204480c5e09a51480d602d02e04240d0a0707480c103aa000c2e00269103180040d01c1100014840c4e50801c2c8640b60034a103c4034040c00000036500b0540243c84407000900041090854620424071140c81d0003112000390710f890385001c1c11492a4610281c5100d0450002482c150911b5124203100720540c8001c5456082c3d1031301c010000d000e41d0540000e0f440416111701c1182c40c00240d410311030041a0001e040700000c00d014965081031410003100d1120060081002d1480280900350300a040c02a4154941c43c90800b255200d003074030142040e24941e19203024401c3d8503401c0464000a1035000e001d40d8903903000e042c4000d020110070307803240705d14030201d00031b011503070190019019035040880701c0e24034854 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 843979892 1250 843978642 843978647
    0x6081e010e010312030f020d1e151a040801181a09070501110106080d0203070308071713080c011119020606090604090c170102040609060e010e01080a02040518041101 73
    0x20a0140410005041004000040d44140e07101284d0b111441c000c508410f001c1740c2d00b000c0c3e0700000d1944035544d0322003001c15007084950103000f03500801414240700d455191106000d00c00d0807802024143c8100d03402c2000c503104e140c401c903070041410600820a660014200384582085500102c50000d403010803982448180f01c00b050040012a010380402e03443c00c8015148145c41040740400703552640c00c0020024001e00444080d60000d4010715a5050710780f4000304080c40c010191010300413110001c142040300c003a912940306000c40610f860544090900c0c03402400b492900c60346941c240240600c0801e00c0c403015118610404945410006130044282d80350f407400ca414a400444090000f8118070302500210100c1e80215101d007201d035101c0c41c014081c03c0c00100760151507074000a04000d52a4442302600003080740349080040c08010100003440102c608840d9810046000003080b0f0003020b0703030304840051000401030402900c0b40c21440442034412202038416402d41c111130200da50 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 843981142 1250 843979892 843979951
    0x411070f0b090a080f3c090409020301060e01171c0509061902070305010b010207052b020a060203190f08070f140c01230403080c030a090f0b04060b0109060c060b03160608 75
    0x713083d00c1c0c900003500101ea04241b05030300112080e9a016444089060143c0ca00f80715000c080e0201e08081082c0d5810a00a00d119264904c0e14010302d600102c5424401c117500c0426403030302c03075081c034102e0b41c3c42601400084040c00f500100c1c9a60300701e600c82444044c4d800040300c4007101e10800080c050300c11050700591311450548a03154121002040f8444886103e1000d006400502011413982074440d03004606048a941c100707801507800050842d0305004105240121f02c0d500d03140500d25100500401407e0010160000003800036800b80c00c0c0410703005000100c01d9030341c0002e5468030303030700601e2032207000e840340382c400c00c1160859941500d004100c17a206079110719050b849103059a1103042400d0f04503880103112110403a078800c3e80c0000580064050000e550158a485280342007034104403085900321403009040c40aa10b20030007110350400c4c03450202d240c0298002030b0b0120b200c03011a051403004104c40f07000c051001004510702c0d03006628103016611003031285003040358413a440c03080c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 843982392 1250 843981142 843981217
    0x72307090509030405090c122406091c063209010b030a030c080c06010608010302040c020f0c010c0203010e03030a0516021b040c020c0d0c050411070f0b090a080f 71
    0x60300100002e102500f840b1500d07c0e04809208651440c10280700d021200d84001921420007210050090041e4217500300404140507404980d124501141c3c00009504a07046c440d0b039a602e4544e02c203403401800110780c021540005080d600c0a00045083c9038240e0110000304c1d5804001401404164003413070500c10701002c624040c00401c01845a6107003544c000c0100b030002c82e14070904200300c3c9480380003848941c0c008d0506813100101541113104100990301410068002c650000c030a003244c1c0c100010b409804041c0a00306090381d00702e1800468090441000b41969620001003445052a01c0da4403051003109540c44604141c2035a11f01240c8404002450780c11149484441e4841c2d8602039100260140c254011945148080c00104003501c5c403940302580c51010300d0204000c18140760107014100b58945030150315207121940c0d03039442624050005048401040c0c0001c021160400c5101741554001e1207030f6484080f50486215158012007003001000c0366041e65100910f1940c5061542 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 843983642 1250 843982392 843982411
    0x9130204030c060806031c05031b0a0903080c01060e040b040201030506151c18120f0504031a0901020903150108010b01052a07050d260708030114060723070905 70
    0x14503d00141281c402901400c503a40c180a840160960141d80103a1a00c241c0155202c0d19100c0ca00000e51000c1c0400c080440c20042d01d04102502c1c00c40d6001c036030700e029079034890216030b00c5141030202c450041526402098040500d14248414170040c01442c1b4070840c0300340d80c2400300e65103004c1402300100740c01030810a400c4c820b0200c02c0c030107403000b41d062200d01c840f26030004a1a0b41360f80c4000501c152030205545080c40d07124280f03000d40e444034812030784040508000e8901841d55a5010b00d40740c00e40041c21121540c4c2000c1220520290100c07151b4801c02812504002080c20621999000030f02c1445c40307542c40d08215a031554040d60603512005403281c0d04e0810015400c12440840280c1d0801c410700c1e02070200085865580c800c0c880050740c1c002c2441c1d0061b0001481113080800f00b1070340189410a080c84418001280d0320100d905503058400c4500a80e135103400032440c039000d501801400503051381013244007010003414001d001c4401700304451322656200401d804440003551440f48 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 843984892 1250 843983642 843983663
    0x106090509030c0714010203130618080d050a0c0807020415080705090f240310063f151424030c040b0d150b01120b010f21050a020913020403 62
    0x50700340c1011850b480d0f80c0317060054a00d000c6107c600d600946529421040103e02890000c004942094070803401501c010401003000c1c10007034602400d0b90060803070b91401c1010f1507074140d00300716624040e1490164007400601034083d4408a070606240b16001c0d005980c8251200000c0c18a4103240792400740781d940307501a07010340300ca11104007205000d600c4400200800840764440b0b440410140c410756500c0707200080c1040c18085800c00340c12171802070040300320081201c883c000c400083c48040d101060004d80c41d04030001d00c0d18040d0341800100004480c0c0ca0b0200b000716004562203511711802e0b6401110042e611401d0360f2580c050245903203190107501c0780c0300381030090605602841c0e6200004244401450741d5641d004403649072400c1003070356a600c070100d981403541c01008621000501d00d80500030b406000300000c10b0121241e40e20070401c83c1a00f201c80c80e0801d840040e00d01640da40405011034504002d515019501820000380199045a000c03030340c81d0620b02c2070703400740d0358048200392 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 843986142 1250 843984892 843984899
    0x15210b04020d1a09010203071206080303010608100b13031203051b0c0c06190201150e0c0904020912010516170c0901110d030e070e070f120f0e0106090509030c07 71
    0x604100c001a085821040b030100c0440703c0805007810510070070f0080c0015a60f85040754005200e840c99008803000c0c181040001d004502000c4152815185145002c030301564500088826100d0300703510404400d00e000484000b20030680e40854180ca0003011084da4001008000303c0450303008640301c800013510303100080c2d501c500c640000d00c9044803101c2140d400d40c0c41800003648652080a40b1449801c00d0940400126028001c01c1a5812004c1003040c2840c03816004403028603004103c400103d00000319030a03240c0c1d46905660803400064841d0001281a0700380314001c00381905d5081d50002e44542120100384141008001910320b840441125261031445d0710a9810203400c96041c409121250303400010b081240c24a54641031382c010804920102c0d41e0740c1000041d0700290102c400c0141088074440c1c00166580c80c85a042c94030340c180c1e4200c08160002000000351844210303042c000ca1050611054101c1026940c161707004014075140c1402e003940e64800c1140c50b00c4550440320041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 843987392 1250 843986142 843986149
    0x604020a0f08100f241d090d03200c0f0f010515010509241207020102121f0e0910060b040e06060307030204080312150f01081909050115210b0402 64
    0x10201d096000e03004209030302d015040c07142d820111401543c854603002020001c082c86d481c45a0014140000f455141e8200740d082c01c2c0c4c55011082c3c010b02490786801e071120381c810303403e424103d0048158aa2507156440f2802c41901d640c000c81140a0600c154204400403800620859002e004c507403901c03500d0907100c2c10040d14990007480205074450103007130121005440c5110303010401d01c0000c0c0403541d0703440c5601180c4039040b806815003085a1042c032145503150902c600d0b281d00003001c6040701d0021114106298204c0c0c4850304901c040303465080c00d008035041c002a14030340b00c12500d1014040c4070340380d20100c0100d002d1172054045085446c8041403140c10700f40001c540152280c5005480c5c141c845010b02c2c40d640c42000b003551080009000c0180c2210114006806040226038440040001000003044024042c10810300e4043c0b821a03004800e90b240c0c000c20203964003c00902408a8400010f101441c2610805640103400a003900c007811320000c441c84604d902c01941002c40d15681c0a1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 843988642 1250 843987392 843987401
    0x207030216140d050f010903091e0e01050d021c0803010603060e0c03161b0510050c0309100e030706140708100807061809150303030f0603080d020a0c0c06020604020a0f0810 76
    0x80d00d13140280d500480d080102800307034011190187e00d404405600e130030800342e450240c1c00849514125408030500444a20000302030444008440e10301140382030340001506841501d1f2851008140105080d0401482d074020318100c9009480400c0440d83c0e070004805000d00480e0060700140e0208000b80944030241104a0810503a00d8456510600c04100d8000040400ca00382c0310742c0e205504550b40740c440c42c0038840d8000c520300410f5045d07042041c100c0d907889800c049604034842d1100158160190100203544000d03410650600c04100e880340e81e501400710a4880e800069401000115880e1402540c8011915000c0007000064903240c8100c400e81c600d040380c00c8200c581040c00103040b68590007010450030b03640450720480c0d8a10314000d01150407007001081024181030b0200013081000090780c0c80c3e038500070005030340d4440300c0c201241c0480c84100020118024008041561a40022200c0c4543c2c8243c1c2c10040d050303291840d025001d107980c03103a0901940b04a95203004c4088a410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 843989892 1250 843988642 843988669
    0x316080c0a150204090b0d05031e09041d0c10080a0b0609040c030b0a1a090105130905070c060c0810031b03051f0b0405160828020703021614 62
    0x1a07607424031050351840c58215040802805080d00440e00303101240c40d62250400030b440c103c510215260465035290380300e000e00c80120b001c10b07841115103400006001c0840b10701d050020002c1080442840e080f0000741d2204100c00100e00c0380700c010440d2400c000601d0045000d4640f02c3d080990340300b0f01c1141c09041c420103001c4d0002010b201850050f1524002d0700340140d035945003ca0b80c10004014440d00c19010f500c81d002500c9441c0c01051429000411150030709020b10b0b00580c2d41240001c010000d183c55400820075030300e0001048407650b40211407000d101d1003550284001000b0a4040310716038029031b8035030480382d0324100400000310810422503200741d0a120f400710207030b9240c130340d14102803900344030b4003000021108003102d0724010301c1084813019040f90100002d003800070440403640300c0700c014101800200c00120303203142d9040c2120f80c4840000c803400340f820744040e40050040e42081d4011009445401c0c21103410402e000d41c41000d81e00c4080c112802c605a1004110b49082080c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 843991142 1250 843989892 843989917
    0x2010e06130902030f0906070c0c180902030708010509070b040b090d02130c03150b040b0f070f0c03030e011b031202090a0e010803090a0b033309150f03031608 70
    0x700c009409001030010f50710600c0380181c20411031074500c1a05040c4030008001001708012409108000303401740100d9001c1d610040d221008121307401008000520310400d02035810301c14080c0014000c0740541100340b04a00f0a802d541401d130b81d48100c404207008a004196200c50b0501c000d10050801002d81d01d8954002042d00590301d00398005201210010580200040d03265140348000a0320340440038000c00e40300200f103103445e160a121801da4000c0814904281c1d03c0001d01e0317801e11050342d865050f81500040e240040e95541e24001e446841d41c2007005020645034a000841595001d990b0600150107481c1c4200404805095070000e502030142168000e14006010802054900380f0074040c0c1f08000045640d400d4480401601d901c1e2075001300d07881803040040112742866803450f024040c0c1c070811402607940003050f0840820180f03190003508500030314100481d9919004940c50b0250041da0000f0280c2c40f00c1c42419143d20654141541c520440e18065000071407030801030078902d1011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 843992392 1250 843991142 843991177
    0x307052b05161416020904020a0b03070f1803020d02041d0109081809060d0803060102030f0d0906110c03040e0c0c120c0f0a030c060e1606031508010902010e06 70
    0x10400c10302190415900d264039480c20801d108502ca4100d034402c080400c05085240c100460003906220806103542e000f401008614007040c00c640700c07110b40c1405040030400a81d264130b0301d10001804650312255000c000342032404c0d4003602c02e00040d10070090341d80140c6100703483c0e007894007848042c00074101a00ca1000401e0040c0002c2002841030001072841610801d654080120901c9442d0801d444264400d0202c1020310055585091407800c00542c0301c50450303180c1d90707040c005078207500030306151b9100081c000421901c107540075846040880d11540040003078007000c00f940600c1d8014904000307415401008244851091385040710f60100180d1030715440c0144002c801428140303000c200d0320b003003040407aa0000510b814007050b002152400010300746c140180d2001001604d4600c03010388900e5541182c170141a10034403003981d541c07102d5003101141c0c0c1c2d0740e81001002081c0703124200780751501003003021501080c10f006c1c07103190680594070003c4c2c03104180c04001040c2e020104c50350411000d03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 843993642 1250 843992392 843992467
    0x8010e011e03170403020103150b120924010e090d0807050729240604090b210708010e01060503070306020f0705070f030606060e090708090109021206070f05030705 72
    0x80c00f00d40b0402e1000780800d903240d40c91440090240d52541d030701e100000d2007100e000c2c0407422881003500c0b0190221b01440c800c64039075566050415100c052401901765114904618400e08002024100c42d414942304000b5560081884c1d152201c5c96010380008075400d0200700d010f0b108002406519000b4050040c400391809400c0661030310b0040c109440c000e0000c104103103521722a01d644811452120850801c481c80c03800140c01d4407560041000702551000d02c40d0541e00ea07c0c02d00fa8020360005000d859080d070182e102580e0341e01c1c81c0b0410305c10b5820724964820902060003881e007102d201400600b48203045a50381d0029410541100c0319030702c028040c00d40812010490100103142c111a102801421402d0070001e540b0160800c2d0103200b1048415032158441400c007640c0451580f81000442c1c80d0003100e04d001d00110310f406584041ca0002001849a01003041805403d8907203681c2070b9100340060613200c5002c03c890090214a0038040184e003100000350b1903040130261102500c44410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 843994892 1250 843993642 843993653
    0x9060f0718050604080c0f0111060a15030f201e3303010305070f08150a0e030a050c0601080c06030412031d0309040e0106141504051206100608010e011e03 68
    0x42941321140ba684143c1b440c0c0620700f882c501c1c1c025007410a2130300e961000610000f0340d07502d02c80034000300e032401d0342c601000901e001800c1c17641c8080c641c41340e80c4a0407924181040031401c5581d00300800d440d01da01c4940c150a15002240c807804030401400446804854010003007400181c0044402c94803400103c10744404902c40446003485e0500d0b05140c49505600303255250401c0c582000c2d094000c078081c240074000c00006e164210003a000f000005980d00c0d001c02d28098100750013214140e00c008101015401e8102010b0180310314007008403440c980e40c440081c0c0c0c1d241011148150000b00420224021856001c44000d214403241004510316a01d1484041442d542e0300c4061610f4101246020769480c01d8011100c1c2200204c000340001428071745100c80254014000d03030310410030110720f80d1552207603005a07401050018480801d150101e16641c0d21644101d9015541900340c05020a9050152014a050b29000c4000c42c801c0d0b820301003800d52441041e002c10310095111540040080c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 843996142 1250 843994892 843994897
    0x3010c030b100804020613060f1220030a090501151802191119080c010c020f12180306010f290a0c1e03021b031b041509090b010e09060f07180506 64
    0x11070b603e09e0400c0501540003000340c1c1043d01a64045403c011002d02400d20560722035442150310b18125950307455044140c0c0c020008004020255401c1c140f000c26a43c0540314148111a64104510040302001c6032840480c41a0030724092a105858644007105204111082c00d40486800300c40b0b0303000c20a05291544000c044c800c45128800145003642d5035028000d100350044580002c0078015140c1c0d4250b40c0f10413901c10a0491500c02061808500c41c0000103e40480300150580320556100e521704501050140203820b010b101b000880f408030b1862201034005801c000082e05e080031030744402144c00c9800e10a007a2042103103441e487c2012030518084141040c465001030a51300c0c2c4071500c20030b034403450800c281e11035000080e00e4034115002c400d0440c80480200c80c0041c0c0a003c5689090000000760040300f0343e9458400000f00b003008074070103503041c0c3d4203072101c2c0c291725a9588040303030781d0300005c650203d410322205000c18105405000c115060300c1e64007504216150300c40c008501c1c0c0340c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 843997392 1250 843996142 843996149
    0x2070f140109060c02030a0e01081b031906050916080615120613090503040504111209010917030402130527010911010504121103010f09030e03010c030b100804020613 73
    0x76555001c0c040c0c20485244107800e5a8481070025500300401a80040c01c000710084240c0d050002c02e00024120003484950340e00f007403101405964807800d05d605401300031040351865136a21858460302003071f1480c0858903d40726441c0030204400a0481c4c0b041110903000141005800c00c841c40d4401070504014809400c402c245408a01424544070040002d44000100c41042e02d900d42581d100100368007000310b5003034903011b032000b24449800d0452001c0d64421203c108100e94086414001114010f41101d030701107000c0e07602800401c10402040c1328611065600950040490310000b590840c41e82006901c8201d40990801c404958228101450b891500c0c05219954804030501006240701c0c140c0030014007860481c0c00c203420111451407100b1422070141c84101c10560068240c3e0b425004440c40c40c0f2031203018007074440c80d403401601c200301518605201b542402d5484540038443e210b62a501d406c02070143c6940c6001c048240d800030405401683c02440801880505260340388540e00103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 843998642 1250 843997392 843997433
    0x614030c0c070513020d051f03140307060e030408070906060f0e2b0b0912090d0f080d090b0703051006030207031404030506011a030402060a080702101a0406050406081002070f 77
    0x860308445075240c01c4800023001d0156010800c500d0710501550303651440d094950140d0545076810350304440c186103001d4144001c0c415400c243d0102500400480503100b166040c00c2105e03a06074031204a0002d482c6d150003048005150b10805c2c21a9611850304000d03000001f402108112003200d040b841e0030b00c04605890b01407031070a0b03011810003001c0c9041e140e00c540c4c4400075003411505101c1440c05441340500440c4910b290903040800d00020719134a4510a80c010b03e011303a100016004007005c0e00f16840182c41c0034505000045d50103000780104ca02c00c0300705514140c026800c124064000f5042180254204403105c0803d5000440f0140100701460140000f01469032514011092501d0b483c3c40b040e50318003060080c400141c40d0a015502d41c840c0d10700741450550343e134640c120f25225105180b1440241064000c1d2452201c2e031a6440ca0103a00740c40a016882d101c509110580345503120b00340c12544258204041c460450f400b500701203115400b00f0707030081003980312040181c00a8503018138 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 843999892 1250 843998642 843998647
    0x21b03190213060f180509120c030412060b040e01051614090306010f170313150e090a0e011107030c060b010c0c060207060201141501031e02040f0806010614030c0c07051302 76
    0x91402a82c0c4d040340d080015117090101c3d280c1031305056102e030344070a0721041c01c04010a00c8201c080d018425100504892082001d40003080d0801c02d004e0310000c400d480c004d91070a42000f2001c901070003030f140b203505021001c200e0740301810011103909203413507541c81001c081480503c80c02d40e020f0055500901c01318100721141030410680108101050003442d60b20b5104108104100c09243c00d00e42c201d901c0200030201080c01c0d48001c0d107a00191000b80741e800314540381081000c0321950311807078070805003038000c0041c46240070390000d1601c112400540442c40079084d035000070b02d07250010316281c00c06151844022113256107030045818030f500801d0150304213a40910420b6030920609198641c12104544940ac00b41e0201c000c0c500e04800305d50415850f0380341251981c040c81707010022402000c1003107542d00d40c2c440a105100819004007880c60152400000d1541d10998403070b5900c0407110f0881e482d503101d440c401031507a400102c01c4102406460303000141951007000c2c84517100c0c254980542e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 844001142 1250 843999892 843999899
    0xc020a05060a0608100b0f06030f090c01020c012c0a030507030308101a0a0c2f030309060912070914011410022805010e0c01021b03190213060f 63
    0x500740701c401002494090315040c003c100e01200028001001d48105e580003c46d000c40c400407820301c017042012a41c2124000043c00000740d04a0541480780041c8801e682c503461240c0012a01c2d0f90740d03040500d001505143e40c05000ba400c0240031617086050003e9808050711301e0300450901201030340251440c3d040201c0c02c006140c0c2000441342e100e5203440005038854201050868288035204a40119540102d423280095004d5041400100c2d004500d514108054142c202075031410001c10001400007040625070b2800d00005a40c4128002407105080c51080014412898004810460360b84661a030005480103d40718081004480641a0072250304001004404e081c0c04505507024260342101d4241c410b5010400030181800700c4011100d10320300752031514000503a18400740182d440c1c2074070184ae1040c00900c1c3d2010342c03c20380a55200000070341105803490415102e590b01a080f61094400610b154048142d8540c402010280c2c038454004000040725120b4000314103484200c1d2060 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 844002392 1250 844001142 844001153
    0x5010c0f08010603090b011a09090109020c0c151204050a24060519092f0310120f020609180906010302030c040e21070b04051f0207120807120c020a 65
    0x303901400f21070034184900340072983c1c5d0300c007258014410013400c0e01d4402843c001c0c0c480d250341140c4e0500c0c002000540c2c2542c41d000c1850095002c070391480b039148200c41d44400c40e8100300d00d0242007c18260803040c140b55081004035410fa00082c0b013180c250140c4002c110015601d00b07600c0c8a050341030a2940d909803007081607027007154841e420041c810000004130007240c100d1540303200c0c140c50a0034404918252054901906a07426600c80c0899001c40700300a04070003040405144a50449070f0800c0740c13165210700034107003408041b201030300340c1944034180e1016040603801003400400c042c0210f01001e00399100d200c5c00140c151000ba000b40c000c90010815454100116424000200d408206e002d4a030a10301d42e4892a1b0440d406600307500550b5815980e18a5080c3c036880341d080020200305141c0b5181160b2100015840c0401e05114146031504161151095031503282e03120b080503001c510b95520a9070030010041200b400c001c4160600b003940fa800340035642c41b8055540040801c0030561609 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 844003642 1250 844002392 844002407
    0x40c0503010b0103020306030613020a0803071407090209060a0c11090a090201090b0f04140f040c08010806010b070c06030b040e012906131503150b0a0224010b0d0905010c0f 76
    0x28504041c014414087e50f99000b00e000f0f81c100d20b800c0d101c03030521286440440c601190560219800f0b000c04a1f110f428003092800b507481031a0b41000fa100010788480c8010224024000d505400001c2400107005803402080c0082c0c0c528040c000c402900110075001800100c021100c3ca1036003615000380d07808550300300c1880d1004d001d180c82500c0c18116200860312145c083c1d88180c0c580750060f610301308282e44070600940078486000d84203010580002e03801401c10802171285d24442d1185c0d50000540b10400c1099413106a80899450b4070b891900340200c001d000303010441503000e0782c0c60400d442d6005091084c6855414510036604c0080100e20340c28642c5a076200c0c900780030740c4c2c00b0070640e1886040350b80f541c0c05403101d01690910081207a88128001c002d0303105140c0d601e4603400000704004200d040980a0303001140d00301c801400301c0352128060741c0380051042a521310310720014081d904c0080c0c0503003001354580100044141850722481e003505c401845140c04680300707554503408590b21860 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 844004892 1250 844003642 844003661
    0x80d090603140123040b03101b020303070815010e10031e020c0d05031b1303110d0b06010e1203030f011e0b030c0a0c1b0f090612020d020307080303040c050301 70
    0x1019140d032515114281d00a007076040c2d5081800c0d00b074044205a600c640c1b1075190300802a086070f05056240c180c181c0141990b900000c0300c1c1080c2d4079a1801c1c0da00c0041201d1040815948801a07a03d88581900e00980a010154144141c01c6a50b907000c0e11020300595030203034030b0780c5e011a89200000b40c0b251a90480c8000c2e80c000c034010490800000000644452070b91114600141e4950380c807041410744d440c9290b20340051510001303415a81c4008a1505000e8a0150303802c540e0311035503141044040d000c031842c010441440580002c0040d1b01441d80c80c00c0c0074001818542d0915000b80d02c841c25a1310440d000c9200070403000052107501b61450142841d0414030040034002403c2100595542c0070052081108000004504810500c03070030410303071120750021003018044884801803288003114020039241d0109040d000032500c0e182c2c011070b4125001842d8070100704a4540038006400b025010603a0103200c2c0d400005140b1108200a40c4500d02030b0040944041c20181050300303403481c1030b6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 844006142 1250 844004892 844004921
    0x130e060604030305090d0203120f13150f08040804050d2a0e011e0f090e100c140c2d0f011118040f05070c050705120703140106080d090603 61
    0x2d0000a0300041201c402c8901111100c0c03191025100191034051042550041030802003500c0d02409005005400d01840c0d25104081d2036441c2e584a241e880c80d400001000244907420001017507004da001d21b50064001c069152900307488401154032400b40f0340048520414040140301d2000c03405141d90544c0c15000c403482d00c1e00703242082c0c8507007100040c012142c0c50309210402a00c26280580c402006226010001c4003055803058100014859a00b03807400c140901079807003803a4240b611403d012109540c98200506150340308a0009800265513229070b40700315001c803069140703120b4201ca003c804824003504008015000346044c20000c810701c02d000c0c2e041c01103003289222aa070640e480ba90304100b02d03002da242440c0001700940411003c1040f44c500d80390a103c00f16a106100c2840c00d400f80c8101c900c01d60f0344100f0322902c80850502901c294015500c00c0c03000440d03202c00c4010010b46e000c0041103141c1c403400264245100d803c840800300700008401c00c403c42c0c040c064200284140c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 844007392 1250 844006142 844006147
    0x6090c06040320030d09090f0504020a0909031826070e07080c1c06060e032802030a05121207020d090b09120a0620032217130e0606 58
    0x21010800300d02450000905845070140d81ca24003100b4072840d50000000101110504000920041d0100c410350003210486410861101254a403900899000390783c0504500b402d946812800c1c030041c80c03030800480800243c800d020440d00400724100c00134045184031070310303242d00a8003040100c00600d41c002c00b031904860700c01c101c00100084040ea1143e190b061441c101e40d02e80d07140b043c20340b02d1000306428400070524290514145980308005403541501c07521140713291801015076505031002c0307030480d04050807640e030321000a40c0c8552113040e2010701101c91140781a6030f964245042170408541500010500e01c2d500c00100bd01c0c03907042016800608800700d0700242c020701c0020f05000341e2201040019000d813040e102d8400102521039400141d038581d070118609031002d03100092240f0180902161080a0300191304112408ad0200030300c000c0084041d4000403004000d03012043d40d44101c910500d10540581b14010f02c0100024130130b000c0c409081010f104030351440030300000e0046409 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 844008642 1250 844007392 844007413
    0xd0b090408090d022e11010e06062704030e010e1206040f031103040b09040b010206010810150b0c0c0a080c0f041e230705270d12020d020609 62
    0x5140482d09880000e45a041d295070303070341c0003144002c040380d007440455001e4000d03192400000740f039815100040b40d544038904001d95805190903542e11295802c0d850700a080400c03075901d004058607908240c0e090000c288010000e00400c21210120b4050b804980c14402800071980d0050000700700103000c070b96514a204401f1441655580020b00042408644030440002d05000303c09800780160880200e075541c5031141010307201e45d005070740300c6405607041c080100320660011844c24183c840c1200240324080c80d462940e409803040c504d80c0723580002d89860110781301c0c50601c02041411070040040c1400d9000001780b1041c60f030302e03600403807941d00108100207699503002c8040358100001c90f80414080d100011680c943c86a480300c2c0700d0228501000440811041d6504401c1c24921f0f01381ca1410fa560180295400e1050801c50f00c032a203000700c48040300ac250443c00c00942c030b82c0504050b440060135a240540c5000007800940076a00c2320b64564103243e8100480c1d68010181c0c1c000e0300340240d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 844009892 1250 844008642 844008653
    0x20f0301060305103b130203070509040b0c16024b100e0d03020f121602010c050102120109020d0e19110312040f1404090f0201120209060d020d0b0904 66
    0x1d20f035080c6485c884031000a5a8001c0005291014015a0040417001d50502070300541d129206450100d0003405072032400910352905095103480385070440e500c4510380e60340c00740007140d59002d00702c034130802441640c040d400350f1101c07840c2d802c0100c1c0082050b03c0141c1556a100e1151031818044000c8140c04c1e07030340c40c44170f5162074021030b0b40c0744055070100c11200702210180c820044400319141c0014a1070790490901d6800a00070709440c55060640e0f4184000084103d01442485c1a034400364410744007190040d445681d00c00c0301c0d80c0c0901c00060030880048070700c4945513801e9100c17011507600402d40c011003480c2c0c1d12442c1d680248040c02400d0003c445000d40914088103140944441d45070403108801f904d081c01043c3c055885e40b41d1296035180c440c41504040101c0d4024448211601002130101c1e060520078284101e40140d6610101c3d0403d0b8011190b8041c1e00d02c0c1820240d800340070a4590ba00c0b03400c0900002142a040541c440300c029114a044820034503101e445454002c00303000c041078 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 844011142 1250 844009892 844009919
    0x10e0d0e0d14030301030b0c041512020f19020c03070e01090b0a050d06140a050105060715020415030902030d05070f06090203072105120a0f031a04020f030106030510 73
    0x162141001203100c84120002036401c1c25021000d00003400100840181400c00300085040e00e01c900e01d262041c0c1c49129101e07001d401a4052400c089001c010101400ca0152031b850859032500c0d0009440c4c03441c9122000d006400204c3c0500b004c0300c0e0340c182100441d0b010301083c00c0480080d0000c103207043c42d151140204280c10702c10042150740d03c01d121003036922004000c80140c038010b40039104010440ca00400244a11104d1566404448012820704041c07030040f40e040315401080315041007078980710808190504010001100d0b405c02002401c02800c00c04a140c40b2000d8500180070b85050041c9414103801200b148108102000b2460018004103801c403039454000000082c00308640c030100b46811801e8021040c0030a8500801841d08540c20000c5585485001990b071400390320105080c85000d190889804134140850001842d4481d40c480840c0401007803402d0006c182c7c240c00300e022a804102a001441380020050001e103805004407a040214162602003141c644030015000c0d6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 844012392 1250 844011142 844011163
    0x305150904050a02040504050304030b150f1002010e0d0504060908060705041206061208181206150d0c0b03100b0301081203090a0209091b040e030306040c09080a05010507030e010e 79
    0x10240e400108081c003030200500200c0681c054004c0001e41090b0500c241e4070b40140c40119552001e41d40007a41282c01d1704400c00c55182e01038951120142d800041011400384030840d0001c40d0360350100c0c03a00d481010403122260902e035454141e921400e100307006040c03640c0754000900030f03801442880441c40e44034048400700c5004203104d20110a00d841d0070009030009900c000c901c01172110340001484000401800c921265940c0ca070004c01d480001e110107082251440c0a141c0c00c5440011a164004c0d441c1842e403440080c001c00b0800f2460355481102040d81e00128000301000c0200058032421807080c101414848110324103561414640642d620f14014146116034030200c0401c0300c6500800000c107640da402400c2c240c0e2494448402580c4201014803002d500e00e40d0b40c8842858145485581c212007d1072001d1840c40c1d84010911000e0b102c00141c4104003c60540d001802c500c09200f8084034910400003c59642800d400c018182c4801b4020750392075900d40048003016503000290202034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 844013642 1250 844012392 844012399
    0x2508100b03040c0e0901020a0e0d020d03080a020d090609020405100e040201180819020907140405121903031a060a02210412260f03011406070c24030515 67
    0x725551450140210002da0f48103032114801c41c401e1140c1d48078190003500f0320072081c0ea20704801c81307000e00811000551070303030b0041c1d013000d02911300d403022903c1059025030100395880054604681700c0301d040111060b018080e00c0d8282e03540e6004045150a0150340e8000c024020b000036201d0402403203035064007000d04000d062041c0004040961126102d02c040101a000107882800845100908194281e914205d00c9983c405000486250003140340584507940d02c04107505103402e0074280310007072100d806400f84a00c80c1c20980105102d0202c80d400721107200e0307580411907148510091600030581c80c035883c4540c409000c4c09003590313400160703079000451001400000c10b0440883c0901c500c99074000308207041400030150b09010008440c8149900c00403107070200f88080d4005c041140c06101d603c99209102000100b1030250361010000141e200100010300c2d00420713036908003c1d00a15409484506e0304402c0602e201c90400001d201a0b1b08141010b0059240c0090003042465011803850b10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 844014892 1250 844013642 844013647
    0x60702030a0305220807030809032b090b011d0109111804110307260907230405101410051b0a1a220203030a08130b2508100b 55
    0x50601d54507034030300080350b91004c404d2040d03c99003814001603000c0601540454024004298800f01c00000c482091104031903840a81c16440302e0070041400e402080d941c055280c000302c4010030307501030701d19000701000000c0d02104180608100b00703003001680910325051805044049481c03810f0704481c2c032881035842c089070313414030070001a004003484d20b43c00c902c003400070041011250300010781044006111164118880c0785608061180500f110329400c0c80d0403030301040008d5202d143e0807078002c4210341d80e11300c44540e11601103030494504807101c060080c65580100100000314039003e10596043e5440780f10040c000501401c240310306564604d010b031000a0381c050110b0f0612103042060340c08410301d08030340d141000595400c0383c01c0d00d52001d4096010000c3d031003610703000000c0b034031380740d014001d50704045c80e080d0250307820440180503000c981003511040c0d001800180ca00c5125611210300e140c0d801100c22200b408403513541c514102030005100c14804420f0034540568120b03051540c1d2941d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 844016142 1250 844014892 844014901
    0x1003110f0d09061407121a150d09081804020a1706010516060204080d02071d1305190303060f0302032a06040603060536070306051917060702030a0305 66
    0x2804041c0c2c0c05000305190403140c03c00107062403801c6000d4280c3d580c0321072158810f4808242101d0011016400c5028486460042410004021142400541034013414002c555203c0c0003624207040e000c840340700b00017404403500e9014203940301d83d03400c0903141141440d0072039002800101d0408280002001d800307000401d20380c85002110200c0d2802c868102c0c1c02040303481e0000194100340075481050050f9581412482d00c00200348040340e0030740400d0110580d880c1030507a001c0c0c2c0040c1904103020071020140340030074010060404800f07400e00441c40203c80d03d0070011300300c3d0b1a54221000540300901c04101507500082d046c00340718034011452942d5510b0700f002e043c46034296020690009408a80003400f07a81543c8100103c50302070b5505074181c074002e01a140818001d8024181c41c002010f484081c1c40c11a5803060381c40015401d00240040d2181c1c000781111201400028000b0740e401d10038040c014000ba0f0002e0000480d200500040c18501c030f000e91680107840b80710041642d1800045c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 844017392 1250 844016142 844016167
    0x9032c030114090d0c0203070b0a080f0a0504170702010e0d03052206020d1115180f06131407080f0714100507081606060f03060e0601050306192403021003110f 70
    0x8c0041015180140c0e4400840e100900780d00e10803a0000342180454001941d1901c06000c1c0500c219804107d8958001030007282c6005500040805d904100c0040360031402c6840c0ca941c4150341390700a40300c107520fa40640c40c03540340d141e40c0030240da0094007802c18208810f80e00000c00040314029410b0515a441202041a00d003400d01700800000c0d0138144140404000700c030101c031010b540c0c1c10040e29041ca0031107100650b210020340340d001c202c00604407410040341c1c00b20f5007080c22080200503250810340c0c8440041c0b900276224450b403078580003450204608800f611451000860590340c00b81614941f02d0080c10728040e01401420500c00024450150000300c003910300036552180080060585603c25100c10300014003088070303568a4041000340010700001d0f40750480b54010010003007640c4102e0788100490710300d403c040300c19884403460580c2d44c15840c07810030080100c40020035820301c0d500410030400182000002070500c3d090714040c041035414111010b640e00b1303030802d039503908411005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 844018642 1250 844017392 844017403
    0xd0903050c0703031106070206070e060304030203090d0c06170402030304062003210708091c0c200a0501140915040503061608010506040b040909032c030114090d0c0203 74
    0x40807024014500c001c410140c02c144204071441842c0101d030f806656420342a6990f010584007078011401c00051440149000e0004540c05071203803060343c1c00c021141011420702e184454045881a604100c184001c0b40c0c050407188000c010161408003600307140c0c01294913413050f0b01601c402c2040164488464004910080114800c64004c0702d0751200a141080000710440f05a01e8501104c2130229402030320032071600c0c0c01201c42001501c902421101843d007000c0003201440c0030300c0049455440800c0d03c81a04941c1288c582c00b00207030b014103030002c0000056164200c43c0c18060080700f42001d4285580554112800170b854020b0754807003403038000e1003501456000b1607040c4a06407c0114bc0b036040704000c0000291a00c03a501d03566224800c0141d6800340f03001d8442440030511040040003804c0e00714400c2d150103400c102c14040c10307100c4030b95050040c01c1c2c5800555540b001051616090034414099034101804400c0789d2424200501a1142c240700386483c00c11032126031000030340d13034140507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 844019892 1250 844018642 844018657
    0x61a090a18060e070f0f0f09090609092a12081204061e11070f140a120f0e180601090b03070c14030702031504140102070b0610140d090305 61
    0x400420038400904007401810103030040800705650940820312481c05404000d4108106031a0b0460161510400319400d4a10034030950422464000c00600703480341d44240c50261500c0d08001c2003050a90a04080020888a079900b0460840b8040d1600364103e040c14019034a14941c050748a01d41e6040510150045e98446141a04920b0901080004550010140c8612003140800500c807981c80b01044585040051240b201d080029500054000c0c12400340544600c40340620040c0d041921450854520b070101c2e400c0d41070003000c0e01c401c0e400c624142d6100d134403807901d030030346074280800320b944010607104800c140c55410011507031580c0110032100140401d1400c0944a140c889401441788030702c00c205a402961040c40909400404411100e0103030700035004084a03820144c00b0401f182c0010000e0711000d22050081151820a000814040c0e0284d40809643d0400000304001d403178004c2c0c04441846032080d000804081c08400361aa00091980005130700f403483d0070251414070900a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 844021142 1250 844019892 844019909
    0x50907090e13080307080f18030a050a0c0f1a1311010c020102010b030609010c0f0203130b07020d1209030c082109010306031b06020105071812020a03050610150201061a090a 76
    0x1300b0460b00d1540911420b00c10135800d44060b0803034944810b42c02c0c440b40036030820b40c200d800c10861880381e40e000343c2c01011949450701d071051000d0303140d4441c0012000d00000c100d030008048040e20140300b01801c541d0b40c0201c1600c1000e06918060340d550414240098902414421103001c6402568001c0d0b001e44c0b84d614002c1c040d1070051070800c50701d41c0205421240c1074085100c80d1100c0d22414800001e640541850680c0461070504200c7d681c001c6804c4404100e9000002c9184000050401c07003080e40d030303c1155100e80c2881821490328129601e0399401c10b65003a80b05989440c071044070000ea6000c0d6001c6404041c3d03440f03048000407409041107420203044102044d0110b141010307003400d408101d03a0789500800898941e041d0880e0f0060318804558242e0054420a210001401c0c1041111034401400d00018507640e82c0e44a00300b440031a0000031013000d100702002150750070380342c0c0f0703160340342510003040050304002d498000c8aa40342c614003c046408030b0030311110f440d040e100d0809841040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 844022392 1250 844021142 844021147
    0xf050d110f03040b040510090c0909050c06180102240a050a0b041103060906040207020d1401091202060a0b0a1512060801020f070501180807030302030709090203011707050907090e1308 81
    0x1400d251306800d41c10b0360100c0c0c1c0c0344500e861045421703580e445151001c60b40955030041d1180307032540307000140c14400000d80e2240911032503500c4d29581c080c010002d1301485c049105a0150f4040068108800840f5a4601c0e41c042403c8409203240d0302507040c1e2269081c7c100041ca91100c100c19002490480340c01c940191515680354418128403024502c214401c407449042551120f061000368021188005c0d00400b4480314000007802542d25038000101560000810b007000d61030744182d0045034144000503810510900c04142c2d254002c000d41040144c6072409410302d041e801000301800306081030304210743e022035045110129040030340204440002551148100c1169100c15809140301300c0b099880e100b440c00d10a003a00c48240c0606030030100150504009450035000381d07000030a850b0401c04407e5012540c0c05061015602034110a04c08003080c00d2a0135180307180c001d058021a03c200115010825010343c00141441a00e070803480c0c601c00b44d100c130399560800743d246403070091542002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 844023642 1250 844022392 844022401
    0x15020318010f0207021c020306040305070f0c0f03050f01061412121801091509030f150c020f01060e010509010611070e010902131205060c090d0506040602070b070f050d110f03 77
    0x750007602c013050003142d51400c03016824100c4444281010707402901504a2000540440e000324040e10070f10780240c0c5c943c0c0010002d40c1d5400001701d003540182c05a840c0b481800e0040c000c040042e540088224402009103a0610401c01d001c0e0250051451050340c90a00701561924180803503003010b5140030350300752503801700062440d1020b000d4021a00161420340001500c280030080076580040a8460407203050541d1114490500a1070741920326001c0300728411843c0d110ba100310301d041d090faa4040e00340440303100e5065094a4042d031104203608000001402542d0b600c01d6000c0c1114454107003000d04102c001d14903810034046500c05c000a603814000055a960b484d0000e041d04804403c04040340358481029281500d40070202400030380c0240006a500c281c210001c0182103001040c0f191000d400d541c803a458054203c80403614150041104410000c02c0e500c0e142d04107486040c41040060300d080014841d00880220440c5903442e40320243d030b00c0e904c07082102da040d41d11400ca0341c2d4a140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 844024892 1250 844023642 844023671
    0x6090f041821020f160b0a09030b0703050108060612060f04020109180c171302010309061b0e0405070c03080a052517010506041a09040204050d0506221502031801 71
    0x100c490320701c80540110180044d01c40c10101c1d2104030044100c480c411098107100d5524a1a001400c505c4180030b511000440850b01c0140b480380b15100550780407500358103203410281007100c0504840e00510001c1409920307507101054070ba91011010200c1041c0e80d0f10360004880b0030b4030b20750152a814503015400700c0100300c1380e08120f1070040035843c1c0260303117900c0326030110320640200c407000440404505040300542c4690000356041d40603050200d10014450240041588050742d032401003450100b4111050815005455110080d810010100b408949001d04107000003000100e1083d61140041c8094415900d0350b1414461200c40c1200d01c0040070018241c0188080480c801c1181030000113030500d0008125020f440e040c006645114452401014954008041d080d070302a40900c008178440e212500054546400f5200900b0207091400d5406800040718118002c0068580b05110110b0040c550032224410441d0005941c4d0b9074840f11440903038841545155154240001c050301003a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 844026142 1250 844024892 844024943
    0x8090118051b15090f010314010f05180105090c03070207030b150103050a0605211203130219060e01111e0f0106051f08060310050a1a06090f0418 64
    0x3500c400500d00c070400e105042100d0910082c03c642090301040080840174146a10b04004c4031700306050203d010440b401207002020000d07000003501036101d2004100c0303403911442550f40080000b60210a55061801240300401d000700106211a00000420380f014420402c02c801541c100c13540c640c95050008842c0c0344a441c04911500090901c0b02041100c40544904c0003200c0c2c00030200701410384580c46083c0c2c82008034559128900804000d55400b00b0321a0041d446a0703101000014511891300c104a0b00910070722803103444200c10081031043c0351300400710107140082401c01c145803204410900b8545424401e070700101d100b0101015541c4000000d100340c0600c1400d0003403090b952200d0078048078440303034140c07401044084504621070038080d008850b04080d002d1300340c0705501814090841515001e4844a40c11541c5d8200004490b00b00c00040e903007868104d44071440e0004036000200749038804001144516541c1d00d00462111421514080742da60042ca00c40381d2880d00c0e059000c03c070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 844027392 1250 844026142 844026163
    0x9030f0803040b0c0c0715050c0f010509010e16050121022b140f070207240f0e240c15040209060d030c080a020a06060306051e01050f010809011805 65
    0x5400383c002042e03d41c034600f01524501e081c4580240901843d0005842803400c0100358481800810000c82c54000400c0c80350ba88200d03a00e00022070780e070401301c000600f101c40000103400c0c04c0e00480f501c070481c5502e21180384101c980c00d1030044c8112181d5202d11040361500010250024800a42c80c030342d804800061a8030303440d144050550450000c1c00440564200d42c0750480d180c1004000107410000421850b03420082074411244043d440381910b64980c100ca080c01d0480950040031849040d0340304210307030f004a05514000c051102d4a83c00316064007006030107880c5070580d031b00d00003038104040c000799a08642038800b01c805080c0c1c00103051060b00c43c256400e0703000e10301020000d541c40c2030942e00303008100e5242d55040300c005140d4940b07401c81c1d081580d940c01103000b500d09010108002e4040c0c0400745003d03200000b01420001502c40b031654240e0400c0b841780f0009030040003142d640307007100c6040f62420f0902c92101d039078000c952801410312261661a141484070030100f031100000741030344003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 844028642 1250 844027392 844027403
    0x305220f110a0b0a1218030908070b0a080103080901020c031b1507112106012301020c0a090b04060b0d061a030f0a0b13050a24030b040b060109030f080304 68
    0x41c00102014480c00380294040c402c0c490740100043e0024030710814050860300f984940c00143c1d241028000404038042c08015400a81c1014060007810307020b0141e00700a06035203003160301d40402c40f0346c094071031f0324140305c0644510804241c940040e40280081003001d4402420744641e80c4060030600781c0a4062000d60703004481e0f0404112811a262f4215102650441a480d01140c0c2c1030b42080103c0100039811500740101c12241031102d40300b0030070b95001e0107a483d2100e45030700b111f44070742054000c09444030341103600031444000c5e141c0301c07841c0250680c6c2c00c8803c08140d900203580494003400301a031101e1104580020720041003001e56000c3c0050381c0050082c000d1401c60b9060f00c003243c6c0025640700e0501c01c0c1c40f001249007001c02e60700203401428003400300c0e01d5284421603144129041140c1800001d034861850b8541014122921901c4212010041d20742c541540c4482c0760900d8014001809a084a404103005a02514041004580c01490700110750180e281c00c01e155001034808480b07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 844029892 1250 844028642 844028663
    0x10e010f18170c071208120601021912090503030301122906090411120c010806010c050a1211072403060b0a030b12010e06150a0e070305220f 62
    0x81d51201a07800d25070503000950510764070821003086a1541c01218500316030f01c00c0d2140051004211007484080c075001d900842e88592005140a0301c000c4010070860454111140e50090038650051202805800124144001101d0001641c00c94899004035915100210000070030207116900d00c1c40da107200f80b0ba400344007420f101c17601c42440300f11003024041b003110303000150160401e0480180d02a0040b042e00d9030504840002c1146031030350650b102c000341c00c500750410f07065801403040c0d078101c1c01c2071a01c8520404035440320b5894641d000d40c010074000e1441c8802d28010f00c0340a581e403031103801006680e40247d4420646014142e10b104540d1449400e607940030003140203104030703401c035452500c2c0c25141940d00c260440041c0480e41c6130036407000a50740c1d02c00d40200700344a06009032041c0030080c0369504100c0c0f201c0079562400c01c1e24501c2240c200c1d03000c0c495280d0f844003035a00000c1c54280441c46458040e401c541e460300b0100041c0340c1d000d4404002d02444030b510568510180a0000d041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 844031142 1250 844029892 844029911
    0xf0203030d1e06080d09090903090f0b070203150702030f0310030c0e040302010b01031104090f0f0612061119181508060f0301090804140d08040f15030501080c0f03010905010e010f 79
    0x54459403140100c5006c074603038610070410f140254206404840c417915144800710b841c1c10120300e200b08250406040101c011418004500303080090244c0d800710781c2e0541e95645807954000351340b032080740346004034185d02202051031390940038002c4010b50741c04071142c502c007612481052040a8201d4080d001582482d1142c03409501a100c0c400b01ea0005240e2580789c2420100d08074081d202d40403852500035034034004640c5030b200d82d00c079042c00b510000c20145d0b01104141082c0066a500c0c001c5002084020450004038000b4224030003061482420b040103815000e0003103d40032101c5d5800800083ca604083c00f0405511895291040307008640c40450702c0c4840c401d05080358403210004103501e40800c4280046108a8030b000103003c03008000c8540080b071503a0342c03042c640250340011410103842c2c1081c03146088454040710010b01900e0100202e603d0600345a0b503405003110503038010181132041d0b422544082d00802c2496402500034008403080301039060087c810045800021860940b019 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 844032392 1250 844031142 844031159
    0x23703050106021903021e0714090105091611061003060501060509010c0b0a11041d01062102030406020f03040b04031e1223010b0315120a0f0203030d1e06 68
    0x380c161050ba60040c0404c1112410200038001d500c8003d07020752042c00c030441c0844112040c01c40c1d000d565040a008624608001d001680700b400c1c40a600c1200ba80b03005000d0781d1614184940c0c010f002400d048500b080c2101c003912010403440bd03d0b15640203000810800f007030013580d0341d000c403403182c0341c108403a80e80c8600885550296103100c60004600308000d002190f14080d481c4d4200e9512803001844e0365000304400b240341e000c0c2e440480314903c48420702d58840c0e902c01d0028014411801d1017440308050003603800c1d102d00600316104107690302002060a2001c0c0c0d0b8180c40703021403c4203507a540c03400c0506103103441407000c580460004400d244131115481049440c0c18440c01280c80e00d40724100a141d55501500a00c450105e03d0b501c0482c186100c801c1c0703e0007550081410115040d503038248000040c58070121402810700510204c10035892883c40010404000c64000c410003404020a100190a6125000d44480c00904240812092035aa400070305461401d0841c02c000040da41d4010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 844033642 1250 844032392 844032401
    0x20a0b030115030b3001060602011107080a02072312010c02070302221514040c050a030f0e06070e1207060822080f07110f0603010603020c01023703 65
    0xa0754900e03070702c00030003466150190b002031003c800001c0c40c6180b281180e0341d05c42d0364901580c4140300c40303000540fa5800506820312a0744007400280c4024000940c0c42c40200c41184120100101300140001e001c03411144240521405004605c10b00550402070400da4800e884203c02c40b20710580600300d00c401001814030821202d800c4640143c42050700e07540070001d203101e00c0d0307a92000e1442d1070307500c7c0c12031a0500c0c1304900c0101c810025124069051469821851103011200e6005500d80341041110700d4001041c0d0380301010038500400d800c220024000302500720783e89550400d100c0c01e001e0014064101c40100a580810380e0300f0342d242940340e41102d50311405846003a000c144064041880c10031135070340316001c45000c881e0f420758882c00c5546e641c4030b40d404130700300b1130140002240d02006c1004d000700010300c41070700b11800d4011000d07240c00038900d440180300b88028998000391000a4180a40554005580d00d005050300074002c41681502400030300d8003c10315101c600c42084001e40640305 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 844034892 1250 844033642 844033649
    0x10318020f0d030c060504050106030546020a0b1815030402090612060411090901020a020d050c070e1302092512020c010c02150912090d03090e0f04020a0b0301 70
    0x8018125150405200d040b030707092a0240e04002c0d1411910001c80c5482c01800e010724030840001039034034954200329090174000484455855901c400101502040f91102d809500525614410b4845004640c0201c03040b040c40094009902100000c1d46030f4156028100d0012076000ea82d0f4800c0b00d8004000503510f0b0080c0301210f4650501c003103001360801c0c0c20450381c0484040c0c01a15484502074409140c542c040740c007240c1c4d0064900c250801d0307040901c8030b42d4014950344000c2d418000950310180d160031078800c0310010003401040132400c1031803c1200000802c00708002c1611410700380c88001d40d085820310241d0241e4080d4000c50450031091044060084159112100d4128207903801c5440c480d184c00000041d44e001c0c0113003c000070081c4075000010034260002c2c61403164900034200c1280e8000e0000c11640c2007600d00281417181001240d0503003a0840d0840042c0704686015581c942d119002604400082170030400403421102d1035a01541c005ca030145403650f40c070031070218544400d00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 844036142 1250 844034892 844034899
    0x405061603151406070c17070b0708090904150c030203010e010b1c020d11030106050a020c0109051011120309062203120e1c0c060509120a05180306130201031802 71
    0x4111109801e0a2512000c074004c001c80d2510403980c44100000c401600040304841e04901d020352180f80170440c1400900800c0306c268100340301ea0701c440c84140600c10f0740758043d12030b410000c0c0420084900074150f016912008210078042c4079030040c002e400074020380380e0500c1003000200311180f0340010303540c506131459804950408000224000780d00700f0814072030141d4940303008030324042030341e400b560103842544c0e0b80948404070400d0088c940034040c0c03607a6052243d0003500b40080d84070080c0c0d21142a00c9410000e21014150a00c02c0c501080c22400060202010080c02102e4501040050140c2c14505034040e80711410f2131441003440c0214001808200820044800d103080780e0020b20019000038161041c1500401100c55880703e1f4a01c1c076400280c090b01d84104000c120303c246900aa106402801c1c900307851b01c0e0102c000d22994030200c0c1881404916088080030688084c05030f040081c00340d0781c45007071940b4540c508100c0000700b00e0119090020602c62125411b02e206007054004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 844037392 1250 844036142 844036181
    0xc01091a03041401110d02030405011d06060f01020c0901141801080325050604151113050f060d32060a17010905150a0c020d020a02010e010c0b0405061603 68
    0x90340e80b200310100d0101801c0c60f954031080140301304d030b0102c00540300d104000380001d6a40e1500349401421101219180c2c0c071410001d10300702038030032000a010781e0721070820f0722030300000f44000005074a8802030398042644842d80a00214034507984680b400040c0e002914400c1e900f26801490070040b010074001d0841d103501c02d0000202c42411401a241c106070410010309000c0115192581403180c2110140c07942e20b05014240b002d40c1061080821101410701e120b07082190952881000401a100e05449449011200d5076030780e40d200308590101c00340840c00c015058800101d0b010900d01440c0d00b008030385410b199502510100c0600341e104220041c200340a040c105000001240030000800381150b5036440d40c0800103108116174001e102030443c0c0e21400740b402c030025005480003514840115084100003014050300010410203540d030908002040103954001281c01c41c0301d0140147c1b80b124100244018030a0204840303000c2d02c5910420711001f0a41070701034066840b0b2040c14400b46189 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 844038642 1250 844037392 844037401
    0x3021c12030504020f030a05011413020f04020a050c030a0206061306060c030804051c11010c0306060f08041a010b12060f18100b04060906030e0705300f0c01091a03 72
    0xb544070541c010300c002e2002401d20141da022a25004a0620468041e9074400e4204403000e81c141d0900d61140c0c0d901401c4c03071280c09517400f0481307502c640c62200340143d0300450a41c403a680108191800c04409408803a01d80495050080d07a9010031360b105402840000c1c01c503000605140a51400d0300c4182d11110b0071042182e90840341c80c0c0d4018170a4500340269000c1d00ca50107210740120950600c81d0790303160003114030340243c2800c41e9204845141414503181c020010180c01070822105d4244074180204590b840341000010140031185060f29880c44000100b000e41810707028003003d400000c41150701d50756120501c900d03200030ba1317030890b4042154444252840450000c40303901103c0c0301001520165180740580203a006500140d02151803000c4c2408803d44c1403095410321503444009040c400d16180210364440c0f648001004860502000321045040c3ca907030021042c59048100c2e24424501d400c05034442d200745601c80d000900350500080c040070265130203031101c00701080c540d2843c1c86 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 844039892 1250 844038642 844038647
    0x402090d0b15030f01230f0c130801020a1d09010b0d090203030408240a150302101803030504140919091b06031e050411060a09030f0c03021c12 63
    0x5008048482400140e02c5502060700c040c06003001c02c100040c00802c040c5004420b9101c4111054280c80c8810007410800030340340c0014803015001880201c40c0d40d6504c00c004003da0880b00580c001b07140d158000158941040d40c061410b20909800b000505200a007040400c4011942803040d80c00510040c0300d1644249400ea200c29840c510080849180a665140302818031420045881035200c981c4c400901011a103a03203a648403101038801c2080114100100c001c0410b80c1c08080e0240c4200742c000015a401820307548440250041d120010340e5036450011310540c030502441c84905450095a611400c0558540340285840440c0e484041119a1500020010210151920114821840c0e640300d041080c640c05000c00344e5001c90300d5000384103501380c0c2051004000900620348810000450404007984103103040841d0700d035079a040c2e400e0f41241c85500302c0e00007a24100d40c07810031100308000d900d44403044078400e0310b12031002005641e01c01c40482c404440034109115140a102c591407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 844041142 1250 844039892 844039913
    0x11070c15050412060902030d020d140a090902031008010b0607030503011e15270b03190f060b090a080d0804110411030703051b030115081902130f050402090d 69
    0x38035600d0420b08290b07440340c0410312848048800d80da030b2035881811740154202807003800b008011034001840c041d01e04403002032030000031440f01340007040007080c52042c8038411000c000c001d28903418255101c0c141442c04030340c000f0051003034030500c0d880c20070908002e003098000d4902c5c20340c0503200d172030030740e0310345a641f02031000380845d070300112030880c07101017000200600800d40a40c401c7d9540440c41000d8100c0c0c40702c1c0001d07251103400f5094843e004006000c15002169444112480d40c03507011a114050480900300c6580f400443e18245036000c41c4403030750403014025050088401907030540d600c502c89601da0f611803100c6000510b007031002030081080794608c1c9109400c0604005440d101c2980e9940d03041d00284d40c0c2e400040d84070f5080c005034030300b03004007800c011841038103280c507552500900282c000265036002d801d01c540076001500710203a01592417290a1152415941d80001040d104001ca00b0b07070089d1f04906030740e000046030300d060030b02c04e4842120014080405000b89500c9602115 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 844042392 1250 844041142 844041179
    0x9061f06051806030705030f13110103020d200a02070e10060f020a06020703080117011e09060b0303040909031701080a030305130c0b090414040f1113020a021011070c 73
    0x44820300703070b07225610381000840c4681c425640d100d40300c0c00c0c0550b100c0d91502010f45051b4022107480d5840001c19182e5507490980e0341c0908006030740b11b107200340b050b01400e4100e45185a1f0b40c104041110034100c0c10004110099065090f10804c684420303a0740700d10300d0b0a4404550340f926201040c095207008842c40b1814040c1401183e2990440d0780d55002603071b10244080780001c2c94507004000c1d0100084101c881e0740a8032000703020008094031240380c00f60b03281d110003a0702d980716100101032200c5039001d4068800054192580d45880d6041d0202030b15907500210006a14200c103402d0400c220807455048c0c0e414440a00924012610b04401401010b0003188280c203c0b801d110b0001901101c28400405500b4261178442c0c1070101004101c0f8100c085850221484408000000d200c0280340003030f00368403140403054042e01e0008603507506261070a5104051000442c805000d4000030340c034082c2d902c0d0319000d00c91007001205c3c8103498010310500803d0503c0109062040526000503802e10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 844043642 1250 844042392 844042417
    0x21501061b080a0c020f0d0215091201050103060c091e06050f04180f06050103090807020d260301050a060e060d050603030903030708040e070905031513020a03060509061f0605 77
    0x16080907218490399601c100881d402003040d00c101082142480070901c0c660486c204c2d100c2c2e181c02c0c1e450f004540c08450703902000c1c00721000050111100d581d68980708179032014800c000c225940c3c581c82e1401c01070440854420100e1280b041c000750080c0e000401c0781012a00d03904000034245448070581309600043c900c07041203542444007084001104541580c0d8a202c200007041c2c03641448141c0c0c00b22b03a2079400c140d04050034031003480c001c6074120045070606a41502c9803002d0003450b003064031140c0303e54a801c541f6082c0982107045075541c17400140d03060f1101121540c4060303603103c0043d16400c4c081c141050b006070081c0400c12000c5015480349a000c900601541c0c50580380a001a00315070021008550700360b0041818403000c03603945401c03540000741e810300e10300c41814000000c0e40c551002050000c01c148803400101d1046004520820843c1c0c003501740c0c0d000a459182c0103018117011100c210081c420710b400104030301e030364501c808a002801000c40b101141406c90840c1d4551108000c0b645 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 844044892 1250 844043642 844043687
    0x30b102d0e070806150a05071106300609220f17130b130e0a06031a0601230a0c02011b11011b05072102040c020606030c0102150106 58
    0x1e6400e507200800e0321031582a0707600b40c858070b07142c0c00300050403484403144d8079244024040c0041c42078002c4110b90280f50880c214040c2c1c01e490000249240c4141d840411800001c205e04a01d502aa5900400e070884110401840da603910001d00840701030880301907500c02003543c40460751800401d2003040090080c03444d40c082920945a001100388180022100408005104400a503003030b4a044041c0001441d554502102c0e05002e160249079400b03100000c420940c08075a404683d9400417006643c02101180b01d0044080298040d0303134121490b9020902815114034507508020012081054007090310703080114480303084404100d201c100702d0601000700040d1400691440300c03005118890802003c00410480005000c0b10a010b00e80f000e0420210007100019800b04136807050305c485221050180c100d04140d0741d1019640b080194005141100c608a40369010802a1154509404440707250943c40012a039600002121a0394194258014041a445000b4591800c40086000c41 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 844046142 1250 844044892 844044899
    0x102070b180d032f0312180a0f020405090619020f09130603050f031303080307052809141807020a020a09201216020f07090501030b102d 60
    0x1108500340c21016000314940103044c6010403444d000b80c5002c03841e08485080d4030349241d01c440b0f94a0080c0d0340b0640e00242d0600015044000310301101c0305000401046980d207190b942041984180a210140e02885c249000030f043c1c148001400c90080345000c000142099005618400a411681d0802400e26040103035441e5699414500024030a40d83d000051051031881d16601c0c0c04030740000003440b500140002d1172031050b0001b5580c103c80e004031800c0d07906c0d5500709040b0340c00d2043c0685c44c0c07425294000c80d0079071201a03c0100906c40103132f40b68144072a44410390703802103184201d200365000c0c1c0e03c200403180280100780c032603030403810500480341410304c1680000d0243c04160090b14040b80d0f9200d5400e05c00c0d4212841080904c24694041e2400d50b202803004007409000b03004100042c1c5189941400034420080d000c000004072080e201082c1d160800d88021306002c1c40140c8051048201040303250000603080300498001080358000032100c28500015490070030303c080b64240c2c0c03800000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 844047392 1250 844046142 844046149
    0x106172a0325050a08061609170f0615060a050906090d080d14040305030a0b030c060d0204061101060f0509041e2301090b072016050a06020c0102070b18 67
    0x140781940c60200c0d11503070342d03030346080840303103540e540c3c082ca01c100c8018004000e416004075146400c1a00b004458070036290100f829a003201c2c25500c038500c0ca440420312154510404503000a0030075200c4151440b40e00c0760078541d00e0118030406803a40c0100c08100c8100ea041c040d00c003e00704454003030005420038102c1c1e8000b40c051049180d040e030712000c0c005004208014148224030581c1c0008211482078241914002c01a002c01408207403201d039500104d413001e944c1040740c0c0c840c0220007405181d590700701649104c081c1d0414441c24002c034110081d1601038800600401c002d481c50501403074030391840c0c141004403180b006003059641010401e600d01e480414904010842401902d001054622042d4682003c40d0390040e456402c0c3d142040d150b00081954011a80003c2d5500e45030002d410051000703892240c0d0040c0800e06441aa441502c1c0e18124500440444804580c040e41560b80c80c60140d03110440d011400d0700507084540280304490380d0381c002e0f0941001c4403807010140716209010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 844048642 1250 844047392 844047403
    0x20d021f020a0e37030b04060f140c0a110c15130801020d0510061806080c0f0403210f0516081c15170615030a020d0807050106172a03 59
    0xa40c84001389208081408a45408181e10036008540080758481c0340da00e44041404000d400101280d8481444003915042500f000c0310034806440f1000d140e080222419490764400340e10701011a0311252140c020039030200310700c06400d2020701207403e608500d0400d607200340d05c0b00300440044598800c007c1003400003403001e40f22003980350100091508024185a0581e03010b40d000c0700822100700c103e0307048031082a8030002281c0f86400c200701240c5603941414201d00a9004290700c2e118003041c00070074003110a4844c44415881c060324102c95000c1601141c44441045616010034070800440c1c5806000b005000c00c4a4002c40c001410203000c80003440c904035080d11880c5900351140e100d042405803654403c402000600084c08403062580c441c80e880300d00c01468460704864062806180e034805000540c00745a00810810b0122001d00e403010035030700000c80540d869803034010040380b0301d1070400c07203c044103100b00010007010300303113003560496885c90924807400d01c0003c118151054600704103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 844049892 1250 844048642 844048669
    0x1090b0115030f18030804080f161104090f0b040c260c010912030810051009090b0303130b0d0f0f021b01050c07020112090c0e0403020d021f020a0e 65
    0xa581075220040c50018190b40c90000620442850300072a040c40a000b0002d107800310f541420407114590780d904080a0501a92240416006000030403d0300d14040312003140402d4480e402805581c1000001c2c0005c40d0700d613447c010001c06a0400c1c0b030b00420882c015290344248100c1406400c5900c5044078882c0444501c00500200115801c802c0300303c00c21b10103c60100020701c0c0c428151032802d4217003104001c0c1e1190140612500c00041910a50312821900c00313008090075071188001c0f00e000003088110548504e0310071614005d002c0c2d07250320303002c8100e80c041210290001442d50900c813000d60715030701c54588418403951310f152480c0510982d00a860540d4150500180c950610410074140c04040c0300413040740d64985000c02c5900c055090944d0340302502884c08200103021802940020807000030064514100c12800049108510448510941c4690f0a0701c210100e80201640e4402d045c80d12521000503000c03c001079182d455000d490788240b1443c0090080001c0700114004c00d0500d207 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 844051142 1250 844049892 844049909
    0x8010903031b0c0203031812010e07031709031e030d051501020705010c0510020a050705010504060207030908010b0d110a2c010b0a0e012321090106050d060e01090b01 73
    0x7084411040c000c1d2000300841c04072814035a02c03c0700103074000b903100e10a920310b5160709186020700c000c02d078584407004103110308958001c000744e0360b55000e1181e40300c0c0c003803004445d46580b6940d47c0d40001555410740f10901c1c40a00100b580840303c0e491100b45242d40c0d00c004e403461005206002d0030401c0f41c003a85028804c203000315040158410002800c0032001c3e040f007414003640707090b8100015000950005803180c418401a102e00c40303158100c0f1075114162001d000b03036003000e041c00248105a4014580d0f20f203e500d6a525441e61042014260f4004110042e401a5054041d502244944130005c00481000f008190b015840700300403803030100b0150b00185165224420301194002001c540c1e409400201da09034105810000001e000c0400440a83c3c100030983c1c000f071654a103071605880601000d11802d40d191010301080c3c400c480da9108240c2005440c1d07402007000c0300b5040c03040a059800140c0390703102240c100c1d200c100181c1403209904407190b507915584400b04509010f00ca001e01a00d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 844052392 1250 844051142 844051151
    0x17070525060b01030c0207150207030515090d0c02062209021c150f031403040f0b1315200a02090106080a05010e06011718060a062405030612070801090303 68
    0x103060200403142d4032001030341031500d48041081e1542d000500c480494541a40e8211050320310802281040080d5100921521440030100f030401c840000c07151044c0107c0c802c4611003001040304175421540141d010b90030010030808495081ca08164030315000c10251034011071143d07610440030490303100b540404980e0b91818a080c199511302c5c0580c040e02207544001b062118284040e1032014145072000403e00e480d1003a808541050500a4030003d000c0250f1400d50142d8610302310f81181d200000081c203510703400d607011030500010146085032201c41d44c1d0700c0c07030143c540f0b807403ca000b807810010705000351044400c5e04005903588541240a00481c1c0d96034102d07820066000c00030b0740c1c01a00059070800c1410204030a60b44d0041000340310103c0c6402a4150b0b44409002200d01c0c62510641140782c0200010412861196046242210004141c02e1005141541c442078002d1054140400040041000c54000d02d055154020280050b0f81130702e03589030703840d904a0b00312154504100d003c2902c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 844053642 1250 844052392 844052467
    0x81f03050d0e0a0b03100527012d06120b0102120d060e010801020322020105160309080f06060a050103110f040e160e010c060c02011d030d0608030703170705 69
    0x146032080141001104c41e0308504210f041100e180c40503000d01400380c0c200711040407042c5d11750400781c2c8404210890459995840f04007503c44507012004440310211a074840d40d00d807071a4085040c3c2100c200d55101501d85078030340a110081d02e00c03000c01c1030444c0b10b00021282c09184c010b00a0149444e2172400003549840c3c045614040d0105a120010070303481030040083c002412840c40d54000210584034200800910044c2c40b03d0140d900e8100700301000e22280800c05400c4075680042c1c0307821400715845c1d1400f68080c1580d4403000c868090708100c1410080102c1d5009800120034500324403030726800c0c00069a80c0880c80d40081d4007c0b203284280400b482807213004031340c900317041d071603079240440300c046003034001078101c6004400c0207006c9640d4002d02d1200c14401c0d400151b00c070b403e0412551071b540c2c41081c0c50742e698120030b61601c02c2d54684280001e5001c00003040b2000e55034940c0313402c9030008009510b0000e00700020401000d03c41c04112540072807031500400203218803a401225403400c40c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 844054892 1250 844053642 844053649
    0x30a061503080f1209161401121a040b0d030e06030406020403150207030e01050702090f09030c0a0f0218060108071805060712080619050f0609090705070303051303081f03050d0e 78
    0x20151508485401c00300c07410746034100440412094032401f02e80c10b1518126540102d5102e0507540039261202c0c076004030b003e140258480010000303401103a00744020101c003010820702071075041000340410081c00c1d040301d1070305200c00559885030181200508040c2c3d1380d2102c0750482101081401c8a42e400156003040503009040304011810031b10b0064204101035001c22041e9034064006a084426080003034100038040044804042d120015900c0f91885450401c012880d40c0d00e040344541c0244c2455006c42407008102031140c04140c0d85d20031070b07444421064600c914120305500d00c075000e00c10041307200d80324100201a00ca12170002c1d0011145020b01c018001a0094038191050000000406582d14907459460589008503a901d42c40c80944000035103034441e9103091038009400c0d0040041560304070001c0c20400d40070340c0b420300590f51000700f0b0000b841880f00005000c80e10303207004251014580c03101da00244018200882816489032101813406810782c005400145020415843e00d04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 844056142 1250 844054892 844054927
    0x10e18091e0d12090c09021b010e07061101090302031e07121215081f0204121103160602030a260a0c02160f031b0e01080601090501060e030a061503080f 67
    0x103003020000c01074444a41d403034405e1810548150201550040703a01c240204868846847c2801440001c10140e8111018241c0b2442103204110101e1200302d05a10041018010720384019410360240d842e120003540d1820040f018940c0303012070361070300340010400a100c0060306101d005454494040140940e00d070903040d16084a440e640c101440541001688400606940c80c2120850060340350518814904004d000310b41c0110800901e01c1d941070280281c40202c80c0c1a80740c16001d40d03083c0109140310040c403c86a109041c0141c1c01002404c40c8144a03461300c041e0041c002117491214803100d440700710312200c03c0c0c40b0042ccc000d544000f620788213501040028112500b58182a81107803500c0b11200907111207102c003820604c0d032841410118600c051803000034090405e00d4441e0707035840f087d81d555641402d00461100d94a0580003045a60007034400f20305500c4020004d10994040e070750303000d010707050002e40b41d0055004078401000203840400602840400744480316120300074914042c1e004c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 844057392 1250 844056142 844056167
    0x6100c0b0a0c3e0114070806062701021204030512070f053a09030b07021e1b0906060316030608030d0f06060c080f03070e040207050604020102010605010e18091e0d 72
    0x107030f00d00401c510004210300541a409a21402d0105c0310b588c410000c00c140d031041c021016a00c1941e0307a070b0402100e28440c120360341e40c03000ba42103c5601c0440104400e1512031804003401640c01404a20310102c0344030020020944101041c2014811a40d03940f49041c40c101e29a00354000c2e84030030401642c006081440b895000d640070f4076005601304002030b04900942c00b018007031801010000e02407a0080000c140c030900c0d038420070851015802c000d6900e403842c00f81412510001805050b480d8900188071a00602008100b180383d5158152180b208041d402d85410605403527800c0000c0ea110107002815890840700350205019620200b40c00480e0f5480c0c210300c00740040c0342684d9001c1184481030710013130110102036035903030703101c410041c1e819410b90014694080d0000942104000300803864a00881c402c1c0c00a1103140d4a52005403075596800807802c0d0031440c4000d1b078200b102d52a20b42c45412600c2c25054512800c0103883c1c03640d003200c2200406841d90b1040140c1400140e011a401700351 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 844058642 1250 844057392 844057517
    0x40e01050a1514060d23091c0905060d0908160507050607082a0304060504031e0203100906021308030301050a090e030d0e16090506100c0b0a0c 63
    0x2c2d608080090103101400800180914030200306101c1d4a0b415910216454206c0d1100400021100d0340e0958030701002c4640d0780142c0140301c010829400c1001c1e00074420951512844841824601840f50782d070420072002210035241c00028010130700400c010594115039000ca040502c2d4a8240a0718103c4154070960003040200300f1000443c120030285c6600c7c02020002100400d0000d10501c6d03503401300000f036640e03030100150015545400c00c004200320380c03117180d40404402c1c1c114520f0840b05403414029425070044004070f83d03030200b43e030b001c03681d40e611411005041c60303181842a003150465030480c000641c800401400545008442c18006000c0940c081c40303401e030100b10154503800b1f2a1310801000307448502c8500f01c031505001b10301201680c1c1a94201d0243d941c40c5002c0905000d44449008654800c0c001d4000b61148049644c0150019401c5107142c40c0c40c100030005255049a802c104002e066075090011402c07043d0490303040445902c1010342d0070701c42c0c00710380d11a150000c2052 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 844059892 1250 844058642 844058681
    0x227120705030606040930030b091006050307051c020703020c03060106091509080f1e120f0c25060305070c0b0402041d070f031a010308030a02070501020702040e01050a 74
    0x1180c0d90001e805135100d6010303900401c500c42d061900d003030307403c2100c84100c8145268000015200e05501c0680c45010a180d4052120036138410070310007200307000da840810400159400f88a4107014100841d0040b03210302d40b070351811410340e01409140080c1c800c032081d03064000a818061650400125054079012006880035524200001c1c0860b0018410100080003555a02c0c04443c010200d420051071118151240c01800120854560403201414900d1025042d0b00a0081c2c200103039803441141801c1796945000c18901400c082d0360800f0ba480441440b075001c0001444103e00310b59542411f80450440003030f400c00c1c03000b509981c070003800081004540040c1c0c1740411049000700f50415019280000c0108117115081240304100031815001e203d605c2c1c0000c1e0b0105013001c22000c980c000d004401203a1010304644010000c04c0c40003400c1e903101480030900109069009200306481913000514262441e4003240540d400c09106101c5a5541c104100b005c80d020701038800d00c0c681c20400c010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 844061142 1250 844059892 844059899
    0x220b090f03031e0714010513110409060507050d050a060b0711030109081b100516030e07030b16140a050714031921150605090d0602162a0303050d02271207 68
    0x1801203c0341d007009842424984200c40c9c440c0c880c0e0740700c202c0c12038210320240031925094802030300720361001c002d0f1a1510300c1c0000040510f10544261400d48440851540c98a00d42d0744800c05502c07800803500c0c3d8595038540310301d4001210b91000740366a09100070080c0c1e0094206400e00d00b4124034146002c1130504200401140d074084c10011205a9041e09002032090303c1c850555107040c40c5a0001001c580085051046120480e40c80580721a10fa60741d0080c0b10301d101580e21094040c540c1c040700490402c0c0070b02000944010f0ba081960b800340012a400c00407003051070040ca0184501320004202500c0038803200c5c0d142c8414402c100c00300000203104003175030702c40d00140c00700151140e031040200120b8040015628811201c6015170082d40075500c42c0071418000e040c1007002401102d8800004448008802882c1c0d41030b07824454200364400150300e0750710300ba81c195225003003007071000340e0030003610000781c0208000804c0040d2050701d0b0003942c03074108140030707540031050140c00d600e900154040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 844062392 1250 844061142 844061161
    0x41a01060e090705160503130506042919050d1413110112090819091d13050f010516020a080904020703020304030512220b090f03031e07140105 63
    0x40c1042082d900c11000b5510594119000e0041e4540f494070410300e001031005120000010f802d486a0303030030980d010181d480c020068107100d1032081c020b000700d0410000c4803000300f10400014203140c1c44406840c10020713003030302c140c05038410351401c000c60800300b4440701e030790b00506c2289600184202a0f000c1401c21200c007481f6042c10001c0141180f0b2650b0024185900c189000020b02c580c0c0c50051003045420710302680b0a8000d044540c50030400110151501481002000225100080104103090510034103451200e00201000703081c2e00022a01c00003c0c00400c03554102d5000ca80c0005601c2c2004500c018501031020350000455200c6070603000415450702c100c0b000304108440040c0d54031018038040e41540182d80c000b0b40507001d01510000d0102911008001404003060b22190031800300e402c0c2c164a284601558a00860901001c2e4681c204070800c0081171400804403820404440d0910400c0c00703c9840000011102013000810400c01401720084100142d000b8001c40c60018901d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 844063642 1250 844062392 844062407
    0x702030a11041b11060601020303190209030a140a0209061e0d110301020a11280305091206190e030a08041b030615150306050a06030b06130806041a0106 67
    0x10380110268803006041d0369450340001c11071041c0360b110f00c50218803001c01411051041c000300b842d500406000030265031010048901c60003c1c0d2650003901081d03034400e98020f400c61140c494243c4681c15600001c0f031070f00b0b1072503119901d1b043c00400302080188117010341e03464080c0c41c03913016806c48070740042d070051186191540403400b0f941c0183d101c0b45908100c2240840100065095440011155520b0354018004241c4108160440d603e02200580201801f00150031080c0c1c660003504146002900c58402006e9846000303003041403074460340c072516061800941c0c60315054040300c1c0c00c0c403101e507059014900c48a00c01002079030405940c41d0029148a0006000034030766000f40b0145401c2c040f51440101c09182c00240c01c000c242a0480c0c4612a0341490140260f54505d030901584018480c1c0607800030380c5c0029000000ca00c2c40d02c1401e4020700808081d1950140080c0b004661100c1e071030346450001c115103c001c0c000b500b01810551500c01e003004003040c080241034010b102c2580c01404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 844064748 1106 844063642 844063663
    0x609090304050303041401032c07060c020901060e010c060207050a0c17150a180507030606050a062a050a0507090509031e09040603082d070203 63
    0x81260340ca029600c109685a8010041404854135a0080e20441141810f011420303110b1222000203826103104c0e058084480c080c000840030300100102c1d0004c00c041e0070318082c410200d07000300e18035402c14003071901440501d007a4296164803901c8060400b94110300304544500c058540300e6205e00c41c040c02940d9200c0c0000012a03030141c010007104102183c580103042138242c06c0c01c01c0302c8407031000305082c5010790740310b1484c0c0600c00600b541001d9203200c1d0015019090841c07511038216841a0040b83c002d001c18081800441d07000040010000661842c0d072110400382282d030f001807482000c00030141d0150000603410888000781250590705114001d208940d00c103e0400c1c1c0c2d074043e00c250600707600c80c201000e070807001000c001840002d10207040428040c1c0c0360f8480701620b41c40080c2148990940380501c0c01894082110b446040c40c2d85c444c0180740c03001c25000070703603910b05604 = true := by decide +kernel

theorem cover : BRFrame.Cov 843884892 844064748 := by
  have h0 := BRFrame.cov_init 843884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 843884892 ≤ n) (h2 : n < 844064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
