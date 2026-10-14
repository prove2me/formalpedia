-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2027
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:28:43.724907+00:00
-- url     : https://prove2.me/submissions/c8b0cdf6-957e-429f-83f2-b9bbb7c1b6b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 364388489 ≤ n < 364568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 364389739 1250 364388489 364388513
    0x9060f09041502120907171203130807030206040b010b03090705041e09050a0314030c22050a06200102182b06142a090f040f02030f15090402040c020a 66
    0x4c003c10300380c54150031482c50114164070000d510103c403408403240500110341026020342c8010745aa0300e607681c50000e0198440c52030014403000300000c14000f8142c1c00728100d4000c0c0d104640324040c60f60388501502e103600081d5500e0301c0700e42107c4020841c510f803550281c1d0740040514180c075081c101460940f01210350614094a840c1c0210f0800b408056100c04103001203240b44550b28114201a12081c82e140a070400d484942c0d028640c9080b01e25144095801c024003006080c00003c940f40e280003003011800411340c40d0000018280c0003104c65041c02075a4400c820215665840ca01031810003590211450711040c80315180a10400b40207044440010543e02800f0046001040003c5141031890010460310200e69024600d446245107228021050700301c0745115622010b0050006100c080048180f03503100b442d10f1420426480310382c000d103210340c03005c0400340700640c2d90724000c603010440f500d00c9645c04801a8000f400610301a44a0300311040144100c850603909030740c0310300710300075 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 364390989 1250 364389739 364389757
    0x60f0f0e060c06060102060907030b040b06030115090204060201230f060d050604050109030e030d1205100b030a0e19080304060213080a0308060f0f0307030b0711030a050c0c09060f09041502 83
    0x48542041300c9542c04120803a040000c0800414403d80345854061020300090001442c2c010002c2c041201c60740d09412460072029040c0055940719a5040310301c009500c503104903005035082158202e003c11003100c58031180034105800203002da4840200090016004007a540e01800109451000c5401004001c2c8214451000011040e2090401808000c42c140850388240d01c10702e0802101075000009040026071040d000ca0705d620ba40a94203038252031604500b07401c3c1000b108000001307070240c018005143e2042d0603960001c0c0001d803014000c101e0603502a052013800c1010900007503440c2d005011490410200c0d100d00c41d00c6004540c01c200d1902010740c0091062414451a0b1505241c0019101c0c02200c1d98401e6005030300110b510f420321840701074141e48004000070703c1c0a008200710200c45140d0b40640303035a8102010007600c65004072668851502c80c0c8480c004081c00c10508840c050040140303c004d00d001e440c2c003000498803005008490740c0f00a51351450b14020340d80041c1c80300714 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 364392239 1250 364390989 364390993
    0x70b0a020a0801050603070e010804020303090d08120a05090d0507110d0609170c10090606080f070801050106021911031f0903031107030905011d03100e010c09060f0f0e060c 76
    0xe041c1d51401400d640301a001030788681d1042083c809069040600140103071002c1c20044000e6559000003030960048408050b0007800000c0d502c0c00b00103403a00241180b141c0000517400540700d1020480c2150b03000c9030f0140c0310341c0c000b500d4a030000b40141c0c082c1040601c41c003d8040c400f0306c543c0128150061281003181d1150716603020310208084096510480c824040400341043ca810606550701d5003d580603060700c683c2c038a807900500038950440000b500602c02201c001115500c0304503034071621485898030b107518003000070540314808940c00c3d110211070000f00e48508042d032201d2039141c42c00314a055051048003400304120515101203603c5120304070000440030070703038100941a54103a07401820740c041d04020000c00130b50020314440a451081c030782000c020540d0600e20551181011000d94075110f0380742d00c40500c4555402148018280394000d01c8800740404080d10008005c0c091000841c3c00d501418008034030801004010070428a44510010000c50100d10590b00004a401080e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 364393489 1250 364392239 364392247
    0x90f0102270909030328060608071101050f04231b040f060506041401090e040501090606080c010f050c03090406230105070b040b060d0204021612030e030301051203070b0a02 76
    0x1c458003003031065000d4a4a204502c1d00d00102c0391203200040c50515412284050503030207002c0c104401c070b80194072403001c110050710b82802510742c00b03003220400001251001264034984060085501a10610340040c4264607140d0ba54240a182c0d03031554015041c0d4001c3c4840160800c00400d0041021805071400400c40b51040c402030310042e803c0781c402c080c1010b908001680350741045500300c0b411840308241d00740d07003200102c52034030180d4010000303411030070180000c2c00b2040d406105443e105071340400406583e08551510b908003410700e6404100040101058a03001354000c2002d456088281e03442e190700307000050101e030a15044582001c14841740000070006545180a0302003090800c941800d001ea40c031034180c003000a00003040d1120f00c4011070680d854030500c00c240180d0090055450320155100c240001880301025642d0602159421411901030300c560320a000369074002c0c4d841c5a00302005e01c5a000e240e461034880ca444100101d001050b18940309034010400300c0700150762 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 364394739 1250 364393489 364393537
    0x40506010618050d0812010e060f0a0e04230a060603050606040e0d050c160803340b04020d021504090507020d0f081003050d03020c060f06090f090f0102 67
    0x242190581281c82030029521000741020001c281d4841200c40481e09a4401a0249025541801201101107074180e45100202c1c100543c01200c911981d0b0981d00384040b681d0f120304000d012401c601c0344945503507004000c10045103c4044001c881c03e42d40d10f268040c055a104494642641d2200c141c6d5025030f02c0d241441001030905c80160051012a0305000034070324400b1007034a601d0150b60031b4041c014001892850140140000c047c3d403036490b003081d0f074000c0c1c0d560160344e103e41c4a6220302c1c9151818030100310641041801100389510f80c515640901820340e6904902400c020381306a0f44941c001c481000180e640302210046c14036510b000c07035150740c500402caa05448001d000c41080d5085170600d00b281a0344aa1081400070f0203180c0481281c4524001324000d21564001a001d4059040c0b011402901038004008101801d0119041039603800c02025038000c094540541c007815200110b03c50701c1d24800c0395600b2803049016169038603038003540c246c01ca070311440484c0314030000303200344600c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 364395989 1250 364394739 364394743
    0x8030a0c0306090b0a05060a140a0306061107030c1403031b07030b010e0402102d0504060e0a0b030f060102030c070603051b0a0f030e010b030304030c0e090f0304030308220b0405 78
    0x8001c003103d90b001c0c049000050002203100e003003401014000d00c404940d415041d03210305a0b000308140a000001d0340c600e008030b001809441c03240142008260030201207601d1b1040000c00608685e04005d141111702d00b00020744100b2000282d20035410b20050200314000c030390004426134800c43c0b00b4010702849103580307071070010000160b102c24000c1e0a1942000056240d6080d510a644039074940494454104c1c661180100c148500c1a11303d800501c2c0d0110066401c0801803003550348549466000044010410151003c6030103400441c90090002c2280c0e20b00c5090620b42003e414016641400c01c219200b91400410354440b400081c0c5500038020304030100c1c040e1180c0790380e50342c89091901c403a1510113486011803000315403c040d03a030203050b9074641d429806483c410800500f92940ca60766030a000c0314640c0540207400d4409120808650410030000305645c5403000e0700003541c2090324507201581c00000c020944408081e00c901d81241d800c04c20002103400c00d105400510307541c02c03c2c1c10014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 364397239 1250 364395989 364396001
    0x160b0901270518040b040605060a08030c010f110412060207020d0822060c031b0309150806030d020102073801030803150306011a0c0a0605090304150c0f1e08030a0c03 73
    0x7124840f103450610010a0452a180341d00c141c2003800410b040d1070354804600300b142258410705482c00081410500c5000c1034000c03811280d1300c400144454405080310ac010f40c410383c400d01c80055052510680000d0840d0050506079000801c4505002e8658a580005a002261081c1e00e018940c4100036244882000080909024034084000003030a507005840308111340e0741503a804200388203041c01c05206411a601401d00e80030104000304204801500450064030650710034001d400030705800600c144250790355180c00116000c2c16250b103500081480030401d0301155100c07031903e20520306103009a2414021413041b8940d554a141413141d0700040c00400210368800d0300001c00400205410035208500c1125501d140381d61021a441424070b00b80180740020800782c00c141c00c20440302000f001800c1207480ca9140d0302225240b008007101d82404400d00200711a51038252140450301c3c1c82d240007010b10300001c0b41000c41c41c0c281c036011aa034200b20340000c1e8080d00c6010035512154940180 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 364398489 1250 364397239 364397269
    0x9040c06020d140405090a0f020a02070807050607020109210f0f021305040c050f06090a0303030b0310021c02070f050a0c05010e24031e010806040201080108160b09012705 75
    0x11100f203a06618110031030b440741e813092522408111000c02c404c0c200c594401c6030484070269085545495070803019440e1a954482c0c0e15813400f400c440084c030750601d0002ca0303144540c144e56142440381050480d424055640303000f5a403001213044c1410000e031080100501d50b0340503e410000e14031003481088840d441182e280383d070035401c040500000420611440041d1102100c8141003400c136240800c05500445420a6110340c814400000781034040d8407030300e0700c84d80030350a44401078000d0305e0881c182d1050509075980011a000d0601400c90b0540c040c1c14a20b10450441c840304040c1c5d1a00d0389030a00d0a00203447e90710915102b00915078103c9681850342d041550141c4da41944001d0080c0040c0070401d20101240000001441003095110100100c40b1000c04c20302c01541c60b4008150b407500122000ca0100e0030b172400106410780d001a044030f203000074101d440d4965082040e23000d2a42c101c00005414001c0500500c0c40200c0041d6100e02c030201e441c0f41140019242c0010888601224081 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 364399739 1250 364398489 364398497
    0xa03020318030a021c11150a230a0630020a0b03090706020609150f040c1509080c01030216143a030b0303030a020c0307020901030b0403110d020309090405070509040c06020d 76
    0x311b10b15009000c9000720014114100d407005d5540d42c00040320240012402d00e040003101070b07803501c90420340841d0301c40c01407a6800040003034035211036030f14400c1030110b0007000e503034025803080084070003001c0d001203011480079040d80c207055a501107442c50380d0020f880c2c83c50309810284e024040c80d075040102c0c03684018082e00500075203c00c0300344800101c07006000e003810b00644000040c00e00c418010001c0003060b40301889040340711100c6000340072024902a45415002d040c1c0101e000750f11034002d80d6101c510b0030146450241a42e078a659021a08851440d4540100780c20700b04a030400246c48843c007220f00c4041c03201984400c01070002c49a0204514050500d0800a0046504c001051343c0d030001580500603035801c04410502e18500414200a500100400000c0200642c4942041c0601d129407070720940021401d00403a2550048084000142d0081c4216080d40c6007004410350014016400c1e81c1070140c03180301241d0300140c200c4081c0e8154041c807400300314031541000340d149039103543d01d8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 364400989 1250 364399739 364399757
    0x4030203190f1d121606020601050d0209010902220909290c0d060b0d0605091005011b020d020301060b0a0f02150a0b040213030b0610030509030a03020318030a021c 72
    0x9000350003051980400c1c1d8801103c0d84107160b041e01e68500000c40c0d10401001c0b03e400d16129140e142d04003c050181c80010b0107a5000003485091950b07501ca61240d008015015980c01c4c01e02c5007000303410441c00c00a040c0c40d4100c8503c041d01303008880c907014003403a4030041a64009030400e582000c104481502400c1e00c4005111266011038450940208410301ba5039602d8a040f1040c0340a04006d4220f41150307100081e8241c00302070194041000c81d101078800d0b14860b075950030601c07a0100d841c481d00d0701051215060750010810b4000803000c183c802403540c2d41c2003449402003030031140c03540c0011082400000d100304070103410003411034180c0f056200074031034041140e94542074158088c0c001d154498440c7c40c03180c22595260140e82e44441d0700f001000c181c554a0800d02141d0400780c070224012805030900d501214400d001f814810402040150314001156400710000d40c0000c003688903000840300b0701c045400c0107100604901c0c1d0994000c0090380000165890202a4124000e040c058042 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 364402239 1250 364400989 364401017
    0x11805010510050105210c04030503280e010c06020f040807080c031c0f0503040602122e12200d150b180a090c05030f0a050f0321040f0b0403020319 65
    0x8140068030300c5005030351030281e03151304081c584540100c0c0c100034241e000c0331640400d40300d800c00f00d04214240300488460f06901180050300c8030003801020500140f07050f4202008119030341c000b425a40c00003090b040c03400da560358801d070900d00150420f032240d80154603c0c040500d01000080d50105800540300000c4410300005042c4034500c1c42c45100303002d0301100080a014a0340d06032000c10284008408840c0350564000740050320416440300c0190998a054044002a002d010b055440c44004e460781c0070940d4640b0404c03030a142c1901d20482052041503c201e0f200c0c1700c00100c08900c42c440c0e0888019409000c0000d032913404c02020b00906c04200ea1a40003062040322a030800042000003402100505080440c5221a04500c0c2c00d44111488104564800129104450f00030000d884e40701240070380d115201c0c445c3e0448010040710321286410361405403686d65070002c0c42252180c491210503030f50034030707008421501640542c1021078450780500c85d400c00011724043c1440e18a184950360 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 364403489 1250 364402239 364402267
    0x12070801062310030f1401060e03060108010c050f0304020402070204021210150e1e04150303270303110309030a20090103380109021b0d20011805010510050105 70
    0x20f0240e10301099101d045401400300964454101c902035000070078a00e40c1c686001a180c0011302d18000d00034440c540c000500c404061048503441c40c590355601e0300d011404104401c80ea08040c00a030380c01a800c10070003006a96a100810004203050407007501c0d8949100c0d9001c1c0031480d030340190b81c0700c4031000842036041d80c4140320405541e011900307003480c1104014511910320381d80e192107406c207182024044480d6914000d60084030300c2940e481003075004014464006020343c02034a260346020000900c0081d00880c2d0b4122548000000c6034100030a5400003882c0030f80c070103411786070f441031843e40c079070780294085e0a04854041070351040300b03e5146d652449640c022041c28104102007800e44490a0250803800d044a00d12110007002e02d56103400c0144c1c002d62044104020030f0200f2413501c20262404111500882c00320784503e8050400041003107002100708402650556844100300c00100c00c403200b000455008400004503442c1030250703501c00d03a2040e041030381401801d1000964644075 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 364404739 1250 364403489 364403509
    0x120b0f0703021806070f150506100302042312070603020a0f0206100302060f0c0a060b180108030a140c010213090c090308090d0c030503160b0106210b120708010623 72
    0x3c1135801d6560f5009600b8003444e451401d1100a2003181000c038902e40f072901640201d030050604440e0a0000c1c0c5905900341e00324856445050034039900d6000a46101d000c9804580c8424409003510b0100c034181c1310007a04040c029040040440d42c045929403100703502c0b009240081305c50303000800040c00d1501054980d00f0851100a1041c02d00180c0d20035040c001c41d041d14412480902116100203980c40c1a101070440c9071a5036001d41c114443d051041d407580340c2040c0c100c600310320240d0704d440c40c030b540102c1302000820015568002e04000311400310800f4402016100240c861203c00d4905100d1140141d03100001c01c0401c0080340042440859039000031507000f030b80115680d40391311100e413800302810701299001500c1c90002091880360702c0001c40304039280912555400d8190381e20740c1e1301581e00c13041c0d0031100d4080c0340780003900d40c2404044cd804000d881d4402401800c3c4241c4003240945000f0040c0c20182c0313140d45030070041204031055600d44424130210311001e41000180808038054800c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 364405989 1250 364404739 364404787
    0x30f0a0c1106041d0405120d050a0b0d1509030306050d0f0c08030309120c0705040203072712030309050f2a06160f030c0c09090b0a05190c0207120b0f070302 69
    0xd01e13540450b08001081000d12804850110b10316200c03161320610000400045407a030856a045c90205416854040800e071300321039011401c10b0940321001c0110004151210085050603501d80b401300b0f00b86d80b244072101109100d00b40784240003807940b502011804003a0310049459200380300340002c1000c08070300158403100c0d0301b07905030304c0d4415010254a401240d40c0410f8009200109001e03d6541c004103180d03207410200d021044207a0002c510001a511034440c0c40c81d46124800080c001030300c02e4100560307050240c404c841c1000d0f2044c66207410003808c42000c00c80e0303000c0c801100180c2100c50303001200400381191400c5c1400c809074140b41a20440c1800140301c009047d054a081600030b500c10300700c0300d0300440d0000c58991206c001c500100341964041d603c03641813200148500d02e903806003d1144030400641c00d10904100d00311005880c08000010230f5010300c0741c0c0401d901840c418854000c6004a034500d07a00e00b04844210034614018200504040c0100304170b03103450a0f07049084003032003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 364407239 1250 364405989 364406039
    0x130506040f200f071a2a25021e1903021309152405030c010c15090b090102070311060106020a120c05030a080105190e13020102030f0a0c110604 63
    0x1200088000c402c0c0c0c07045510050494400c07000e50500345012840c2c061190f20380c46c08201801e058220105c212410041c0c083c01d050508005242c7e194802c01c0c1200c803611001c15442c107a4810503030000b1640208514900c1c105410307060705104502d030068160000840c4e04030400811350a5401149242c1c03d0141d0140300075807140c20203801c01c1800604178240c1c1007044410001801524420b41080d04d00480800030710000c4e00c0c01090324600031607183c83c816130503181d070f0b140c041c4545d45610103000101070700100c1c00e070b4422260f40403d1100816a119002c40400141e40318401d190103005455107003034072240f035481800103000590300014007903a104c3d0402c0801c0144843c4100455480c500d81c44010000e01001c6600062140c1240340b07281a1102203c4001003001119912109021181710307284103441c101c0045050f00b148040340f54800ea00601c180e074904912450181d01c02c1e800446c050002441001c01d40341441901d00741554034000031034540f442e062800c08112404a16422040200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 364408489 1250 364407239 364407247
    0x50a1a0306010207030c060f2c0d15020a0315060c030c32060415182006030c0705070603050f01030201110705040c0306080708071a0711130506040f20 66
    0x20b680200081401141d000b07a444040030b442d08401021000000070840110319241c00f0340d05c40a040c0c202e984c8401001d059466410701c000020442c0380c00e2001e02c142d0707103204000400c2100045500041010211a480100705200d0303e28846c03051038061784c0400c0c20041110b42c00d0001960205c0840d80d4140c03c0000c0f0404041000302d00d210700c0031a503402d41910318904560140002e00400d48034032860003200d15192407032103045108151881c46150194400040000e000066600c0c0040d0000c05d0b076002c501d1450f45043d0020404680c0255940078125202041410170400104007070805004280740a02c480d06001c2d00541001c90113000c024140310411f8108200380c081041000c006080042080c40501c52660000d40203054074001c440c8240107488001c01c000c0030020300d8400b1540220480152449402d900740c5d10350b00300f00000c4072118030001d0f004465940e455a249840c058003040000c2e0350604000b080116401000b4100c42d0b2420704416100d881002e115880708001c96840107a55 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 364409739 1250 364408489 364408501
    0x902040f1e0504180303050601020607051e1210080f031314040209090c03010503010b030c06070308180313090c08060f040f0905070f0611070e0615040503010e16050a1a03 75
    0x100341c049811468100e460025034240014100403941c00f401e000c0c0c5c030104502c3c3c680500480e01c0b080121040804034408010412020325403e10301200b59400d01c0401c2d05042040340012119542aa2841509042c009017403003c00070a10800c40208134200045207031885414901e00a0452480b90010920444034030100310780700d50301260780e801c0e0001c08500b6207203130045580046410a00a42c2d01940c6020250b00240c1400a840c3c860aa00205000e051080e01c1c0d404403a07007080109134001e04101c8440800000b4010005011000b686000c680a031074107083c520000c480503507200e50704021002c02400141d0301c401d001034000b005c0c01d0301d002c80e08890b80c04443c00a8501c10500070f000d441500f10010320042d40689603800c1d64015541c6102e9410070200c0c032580c560007809011507140c114000310b1001e00c1e00015036407102c3c000d40c40c40e07424295558006401c50750f0502d01280150015089070007503001200c1841c2c081c0100700c40c600a07260600308030f0407810301d101200c04a010400030100308 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 364410989 1250 364409739 364409789
    0x61b0506251b080a2f0d0521060a030506070c030e09160c060209150304140d050a08100512010b01031b09090f0e0f030d0506010504030b060d0609080c03040f0902040f 73
    0x140c5260001c1e5a8000ca9070080e11135808178400380050342e0580910b00c03a100071284600c003100e43c8000c59802c0202d0150040588512080d07015010035404802d2110000000b60f0030300503284108090380b205106902c240c20041c00b02c04080100e03600c075003d0070b020410304210680880380401c10514100c4440307005450f16a009106908542d40d114600d21010760f03d018906005502c60781c0301cad211010421044c07510701d80d503603030211003124086002801040e0701c030740c0309408083e8460101c94034221760301d03550310200d0f02820788507043d01300e1a5102c0c5c05480d06942c26006070450320101c54a1600300c1480000000c00601c2c0714029140102d444605072421040c0c5038004041341c10603c020340d49030602003034000c0d03682e6102d04041009a410040050202c1d070048041d1703011690022000d91099440108000303c0070400041147c042e5039600b0304501107800b1002409044001d14001c503076550402554607003031005c0798402448140100070920542c400042070304100c0d039007158a5040380789440360103e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 364412239 1250 364410989 364411007
    0x9010308030411130c0318080304020915100f0807090503030406050d0902060a02010501180212010303030b0d1208100524030402210c040b060a0207061b0506251b080a 73
    0xf0780e000d4245200548403501c644d000f84000c04542d1401c216048840d072640941d03282c0e424015201240510004001d41484070070168401104c003101d8012000031030028441516241100c000600c070001c02800154000003a00e82060284c00c00500c00c6250800295032403246000c0e40b400c200e00071078900c1c01c001140d0044030000f5070040c09562104403880c0000e0080100340301d6580007a050f103c444800e003609100310303800c81c01703511041040b50b802c0d528150003800010100ca0740182e1007100c039501041400200324100707a4560303912a0031f1b00307040c02c5524006400c0d410180c4181c030620a180815803500310420b212250407100d5940b240c0e110b0000941c000d0031004940ea802031840c1c48610100c10206104c4c2c1c810504541c01c0018561450500559003d00c40903900560b2100d03006000c400e00694103403a0751100c00003c481001880c5c0d0b55035041c02c000703807080101c00084072015901b03200802d100d00d51b151810700d8894104442c495000360091034100000c0e000800010b584915280304400e11 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 364413489 1250 364412239 364412273
    0x3030e07050d1a100b0904021c05040c180e10050c070b0118060b0a02060a0b040e070b0301030203061f060c06020d050108030306151603080c070b181005010302090103080304 76
    0x80800c55000c1d041086082c03903041c40f821501c41d14080012000132000040b0000d4509140c00c26040000f0710b8144170003540b0030180560503035000e1090501d968654003030b50b0701c500e1140b11384524852801b121200c85641411301107101c01d09050031154480300000d0f45000d01e0414071008a1030351200110016070b8440c0300d4000d030503484807400101d00c61201c09000341c9200901c040400801c1c0d5102051a45030040c0100400140c0000d030205c1c001c6c00d2140c00609242200078400a608512039502d0340c0f402c00a58044645407601000400c103500c2c0030700500342e0001c0c0b008500c0c0100c9980d81003040c0721240a003e00000d101210064034184036656056503800c00c0124020041c0d96162038100d566904101c031102c0c8241c00c181d2044a0030b511100991340c080c00d89422109040c01d0550701a24141700c020030200d032240c0c00f031004901013078602c120309001d03040040c14000c0070310003e811141440038103051081d4050a02c0010801610b50180e4541105c1d00011807a44030348951401c426040001455 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 364414739 1250 364413489 364413499
    0x909060607080703110601080a0c06231c0b040203090703020907030e0a0b060f011707050d1103151c0b061315030c0611070f0611030708040b031503010905060403030e0705 75
    0x2c08100345e040950b008000340c4400440da03844e03903511a4980d40d818002c1000b00a03000408081040c603025030325805503500c2c0c032419041d807000c6800c03000c400c42c0c00c07520084241503208103490750b2086007440b8081101c0004c0d03409601d1450815030107996010203100003406101c81100207541c40d40320381d0003d00d82e5122107041d03031980007041c00d10074244a0195095407040280401e101055801100420036950091003030300c6090780e50a0041e502900070200036005203032a0f04555601c803505200541c8160184404c5140004815007400b41619034800443d403441440d24400d008204131200300c40c2e200808444403c00745100343c5260340544803800c0700c1c220286584801008214044801030103072a495604c0702008502401c80c45d550315210b11403040050301003001403141511810440311890100d404403850325440b1b686e044503d51045d03000c003010030004070a21803010041c814000b58941c00f10300901c0040c1c41a00c6140d1103000240c00101419500c4144c1070081c6014400c1c04020540180 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 364415989 1250 364414739 364414747
    0x20f150c01050406050a090f020108071b050303010905061e090606040302030f010608010c03141305070e0916090903021f0e0d0e03060601140703030c020106151707030b06090906060708 81
    0x1954a002e0903040c0c030200da025040100040586a1034450080c445410003020141400039800540d00700304050000410445000030aa8503446000400340b90207100b0310040d6525031400304803504840c40646094840d5407451010034010841c451421074405040350420026110300000130b1480c8038952009405020b0400c0541c1c40b92010b500000c100c0d01100c000707014100d04e07a40708070111408040c13500e02080380d02001c03a080d00500119503541d123120320201d0b40750030380300c64815100c008101e030740344803030781c4030320324a040b42040c031030661001b49182841803000c6103090340c020b03480f900c264291084200300142d403585480c2c082d81040b0040701c880f0040e40c0b418205924000d02c440308240b8501e0080c8244004251a5480f07601d01d142d1350030100c91a0b9007000600d5400314041c0002c101d40d03400310b64a619002c80c054408450842030441140c6950341252014504848140350042a481c00d0501e01603c4400945071401100c0c1000c800f00c8895195070f84100c001072142c000c3c0d49004d01910310120f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 364417239 1250 364415989 364416007
    0x21902030d0507110304061b050604350901080601140301140406050f0a0e0a091e300e1c06140114060913200a2703020f15 54
    0x840180711144181400b03208030390300c281041d2605241c202c03e00c10290300800c002c0000b107202e885060800140215105e0703031155151680303407a18809440c1640d104180c020b280c08500381b844c0d03d41340042c1c034a421980408800c0c9035042e140d40110301000e41440031000c005400e41c1e00c00e0045042443d038803c40c040d26942c403412000c100025403051140200d1a01c100410507181940b01b807529164000c124010042c00e081c0317050300c806405001c0310b090035221031000c800507040c10358455110388080569010307040c02c1d09001e19145150b014282c480340060b00d00e80880301d0180901c001001d1181413160310b0545410101e2070601d001d2103150840c0980594003c200030103500506ca0f01240411040580e90b25040c0603041003820100480c0e200ca82042500240d09064640031036002400e40001802810300c1142d98504d4400d8107800e9141000241031044141c10100301216400700e00000c0c210a884544a100b01d240d2900000c1c1c45416001e1a40b8200e076103000b404000c44030030380000c0d500c441c084 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 364418489 1250 364417239 364417243
    0xd05010b0405030705040e0a06150b0703050a032f090a030605090604140607020c0d020a120b06100e0a0b1b12090103060902091c05071a070c0e040f0312021902 70
    0x60181901c6409100800181c40c0f030f00b0f02800680040047c050280c1413010f540382802000d080200f1100100c0c40280011801e02000141c5041406515a15500c170b070417420080403180d05141000c6140003844400141d0f081010030701030000141d07600d0070754416a4a002501d014415440240203030304010400510100108241d0300442c4a60303071440c070544c040041d1035154202150048016845011016094a4200304c2c40c800240068082611a0784076441a040b15000c0c00083da008203d510500c2080e040803455100500450310f00300062003000e20000d10100f0385481003280071440440c588411160103059100c1c60850b42c0121075010104890030020b940000b08442e02103440c00000040c150000e0003181c00343c04004111884050780ca41460444210782031050f202ea11403040b0110f00a085140c528070360300c443c143c459480c1d80c114501504481d03c0707a0407603c0c80c1d1030248244030024211642011081d90b043c01c055401c0c4803032865003002801914130b200b00300780042000c00034441d00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 364419739 1250 364418489 364418497
    0x60e070305010b0909061e071e02030307080108120703081009150608070801060f1b050118061a061b16060801090507030e030f0c01061e23011b0203030d05010b 70
    0x544d15940a81d6550700c0d2103894100403240c030510765010320f8020041c402480d2905a00c0f81043c1801b0300b803402602c0c0941e003584810850354001d80c0c000801d004070140c00490050040c54640020703e00c0d240a40f102862038000c0c0c440090900000d00007091440101c1e00c3c0da10013030024500c1c01c1040c1e0028003041521012944500c4000c46c1000d03000c0b8440d18800c10046050f0348036500c5000b00c10303010440864800441d903e5601c0007010078046030300050381c00c0c092400c2e075100700200d04085030f0290409204642c844004a10121244c10901c0c03d942ca4440c2030ba10100400d1000d145002e241125440c1080400d107174280345411107200104855420010b2281600c4c80a1070821069441c0b14080e02181d44c40e4060030a0350307105101c072a140d1540440100355100640c0000b151141d80c5040c14560003100d041c040c00c907020a05020700109a802e42080c800603052a01d694196181c400042c04070002000340b400d08101f60320b501020b5490030021074030328410001c006c1045681d0345440b2007250304 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 364420989 1250 364419739 364419761
    0x40e06010510020d0f0c03210c02071d070c050a120810050316090c030209152d030c1e0c0a05071406030f070e15030a11070816060e07030501 62
    0x141c0d20b070940700c041c40000c00030707002015500c0d001040640e135241600c02e00a008011000c1020519490003081071409006680d1040010040741c00c104520300a422f03c0e40c035412803000a5916403501108800080e01141c1251b02e50810b007a00700c000e401e12606092020401500114034960303510511984603800d203210321540da80c0800866242c0c0209034868071002c3d84525094151142030014803400d6120303003d044100c1c01d00520300042c0a002c41c420740480c0c0c41c031a61074000454100e00350003142e203002c000012140074000c0b500c2e00700206042c0c00d00020704042980300022424542c0e44048004222401e0190f06040b40c95001c1061002c0c0e0300c45040404071407038021001c0000c0c00c0c1d014482462030000c0c0c01400c086c115500c07200d0900300f424000f0060402c205c0300f108005c400d42c84401160607441102c7c0049a903e1170840f10f9a001eaa0741c1d0052500039140070080180840e1303810041d80c0343c8114541229030700396258201007018100084440c81c003030140380e500108001c0305500c5950204 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 364422239 1250 364420989 364420999
    0x9020c030409330501120501030503092806020a0c060f081302030a300503011202090603120307080f0108060106050f03040f080409060302180601091203050d021801030513031b0f02040e060105 84
    0x842ca6606d40584c6d00030f200007441d952050200400d0391410900312004003183e1040e41300000750b45030740103100c8641c560040c000350b000303d00318401740540000e600010306024144610342c3d0044c014010701c019001010400d0948001c9592411582d041c00103400f041d8204101c0a00324007104c8208811803005c000c42101080030320034a0240d0390240080c0c038100e8501c6003102100c1040380d000d00142650003071025625010f12001c68000d420f00602850042045a984109a18010801c201c40200681017054140d1107080100500c961200c2202c00703c92030419420740320b0700c0e6464140340c010314000300104850350200d00413800a5440e0b01c145d08480c0221944c2095030f100c0c0b01c41115000042d100d00740010054241488820384a4080250040c402e1810030300d890398080400342240c10510702410203041da4201c1a40c2c0d13680c1401416003002000806271000c43c00d1b903401902c0b2051819482900204c100204014040c040044681550b0090e000b8480d500f034002000303440d200d09008040c0f0034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 364423489 1250 364422239 364422257
    0xf0f0a11010f06051e0a1503090308091504140c030d030e15060d0204050919030305160f0807080c04080a08070302061f030213020702040f1509020c030409330501 71
    0xd038105010700012102c000d0b0120304005038002441c41c170708401030400354015404410001d105110804e04042c8485980e40c0022410b08528004100010281002160398028264a1109105590450f41041d40800b507170f0781c3c0e000215480d80c00c100d01000c0c180d0b0f050080f004480300d0340b9012f400c008440305814040c0c400203507064844112140017510259003002c030046180780142070652110350880c46c00070882e122200c0c1d206815134149d4100f0411000280c4600611204040039120000b800f00641050107105511400082a0280c0145a001040044008a421400081c046070042c0200b003041c0e40c02400242440030080d407090344100c005202e040e000403400b900c050007280e0004545c000d2100040e24607002c03c04044104441030b08000e03030070400140140e40328410030114815111000c12065a0140d1810510216a101d040f9250040049841084d408021901903c00c4580b0000d200050000d0381001d103400c00c074200342c040c480c503003c800746400c411a440c001c4038400d07a150216 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 364424739 1250 364423489 364423511
    0x40f0311010c0e06072f0a050a120609030e030304080313050909030417011e0e010b0f031e120424020d2f031305041406090402060f0f0a1101 62
    0xc950700e035488a000507000c3e000c1c455151401c0c000030f2042c0c60250220240e0425200c101d0060074600710310f1601c03440b60b0b04101e2403550420404000c01444d044410550303052a00b40c446640c5c10940d04024009640c4031100420540034008080300001c0203811aa220f540340e5440540c1c0354424210410300b020740300c1000560740b03400c000c80b922800001d80510f042600d0004100200309000041500315500d4146a480c80e0b400c0c4010303202150081c11003c0307081c184d200a00307400c407482180310320b000d25244c0320f142000381ca000a1104a41d20f440001c0c10f0005103c2e9812800e2404c0498884a20040001c1c0040c010440000c015520055a2a407800d54141100240c1e5680725120900c4049480d50102d105100c00e029098075104402c0e041c00601001c000f590a8119805010300a14005c1070441c1030107281001e216100030005031000301d10481c1003501c0041d070324000c0240003e10030540040c9030405c80002009460741c60036160343d0315444910044000d0b02c1d145d542424214158601044400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 364425989 1250 364424739 364424741
    0x9080c1501080a021528030b1f09150504030f03030207021504060909052503050a060911090d021207030b04021807080f060105040e10050a08030a020303010501080a090b040f031101 79
    0x4890b6401414600b05c0c2c0266907641100d6080881e81d80108080c95001ca0300b01945540a41005d41080d075001508402403010050034521004d0a1140c101080c0e019900c4c1030381141454050302c0074400940744150640074200c800b4404d40e0001007052051540c02c1c1c081640603000b42c03c2191003140d00c208400e0400b13507800c1550003503108000c00624403400400940307000d80e000d07540000805044003180240c00c903422180e146403084400c00030f540c8500b0000d4151491042c02c0282010f000c0900c6003011401c602c2c0d003603001b03110702c462061440b00d02040842d6219040709858420301c6003911001c5659081400843c0310484090340211a081041d25182895190317841c8140c401d078980041c10344858042c40080e010007072641c0d0500000300008130b5101012400345200348890254a80d0b40750034401841882485a800a011540140100501c0c01d8000c0280c034151030f000c0c68407000ca560b03000d0356503014040706100a03165002d0641440309000c10f4034248000980244c5800c00080c85401c003540c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 364427239 1250 364425989 364426003
    0x111611030d05071110090302090403110c0105070c140621061807021b01020f032703070b0a1d150910050a17060a0e09100c0302030402061206030109080c150108 70
    0x100481d10300c10502c8000c0c905803221910802040c680b00038801e0316a4003140062710305450641c003081c164549058140402c001e036101345802881e1090400400d60b0f52540c1462207030050100112240a400e0390588881080e5214000700740916240301100d10305500704214296641805800c0710168020311460360004540243e0980d401080a100750600b40b040300394860a0440c1140944280003221020130809410000c403404a084101c3c0101001e01001e0303010006068080c1c2c0120fa010010b070507a80381a104504c046081400300e613624030501c080d4201040404507030185490400d215809803950161003d01d505448a030621099050195058014100300a0000d52481030f100340064000c6105a0041070140c4540311154840142c0030f002c0c0f800311100395103944421441000c9003124081c008011203a41000c41c03650900703402144840c031400c0d1060380b9000344000810388a4a095102c140c1968114130410b80300e06008038030275110b282031510904048500c800109011201041e55 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 364428489 1250 364427239 364427243
    0x1103010501080f0403020f0f161401140f130f030308100b03071101091232040918050609011d01050f041707050708030a0305010801140406111611030d0507 68
    0x740841e90341d05121803e00c080c000380110114081c4400c604220034007041014801019180580040b05c0e500d4084c1c04102050350244181030a021410600c5076044035035013403400050481c0381c3e030304c81b5444044034451050f0800a911000c014074006560b07444c6202a20949210741e40380000d580300c02e110141600c202c0c0c09a40b03101401000407410860145c0440611040c00c180003140f00d0941e900c8600d40b060500a500000c240ca01040460b052010040f032405207949010120500f842109000307182d002c0c40c000e001127141d94050f00c1d03142016001c41d01d030401f5804400c03501c0d20300e49894400d019016014507070310044110403c2c5120404103016891040c0c01c0c49180080c030f0f41c0d0300d413101800c4e21482d0051000c10101045040d01144042c4641380191103507500031543c485440c0d034000d0480310141e1000350a0791604040c3c1d500726100518558010740c10420104411481c041c0000700740c0304030540c0b0303140c1002d80220041000b0515515104e0501c1c1241036803910300c090182030b1080c0c0f00d00400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 364429739 1250 364428489 364428497
    0x28030f051609050906030a0c0b0309070b121605040b13080601080c0303030402040c030b102c01020a020d06020f040801050915070c0f050c09040501090c05010201061d0a020c1f1103010501 82
    0x3c0c801810000055944880014101e6070340e40125114940c1c030040c1c0740c00c2504d0b2410004100072040400f00a01070051103040078007840d01c0d0882c400704400120191200f00d07001d0140c0102c0d00c2d060f10500c00e0320054101c070030781c299907401c4005800c8040034081c4901122030042000008481340c01280082c890000613018600c1c5669a900b00801000e05902502c14990385200d00d40741a00e644890030084110b86d1144512842104100c82403002c8540e40d04d0301e1155102e013141c4507640c3c00314a00b40c1c1c03183d041d10164041c0c24145409006401648094400c450000c100001c081005411481c00b07424034a056800d210b045280b0384a00040840340307400881d1058040400007150410049802030141098640d2004034500241503940280d07000d5425030746510314242400740d0f61454400074482400200309582c07910044001c80c200310368190741241d02a0000559681807601203802c071240c14403d440300f9902d40802c0040c110b0000b50210641441c244070741030080034603c2101d041e1501616 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 364430989 1250 364429739 364429757
    0x501806061507060b04060f081f090f030e0112020307031d060c160c080712031e020d0c050a02100804030215010b1e130b03090c010203030408090628030f0516 69
    0x22280040c0141030144c0303400c1030351a5000241400903008040141c6510001303418400208580e0144654240d280803460707601d0510700b0300000301072101c0b440409516052410101d142c0100603142c0c00300075465400304034000020890925031540c4143c3c00b024186610044a144a1951550302c0d14202c9139000d0b0101c0800002d81101c802c0c0941e0401184545540c01c22180c8070000742c0d040c034a16030700500c85404140c071103404054000180420b080703003020480f12400f05034600250743d042c070a0142c00500145000c0c0704140101031003103a000d40c0d00038100c2c410380203018000900c40d04d022902a8014000c0005088203001c8000d400e40c1250741c0310719107504141007803415411140c41100c000c0c0880c14104014140c2d40c901d0001c070002444162a02510381c60310258407800c060b070304041e0380d0441d001001003100144002c0155250240203036252a12000841c1c1e00c0d913480c032044401d910380005084411564198142c00c0003420007032040e014440d0f91110b6444030010000b120940d008107508103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 364432239 1250 364430989 364430993
    0xb0304050712170f1308010b0f0114090307030b0f060102061e070302250c08070803031803070c0801020307030f0b010215102106501806061507 63
    0x400d400405005031420495515950300d80f2003940d204503540030320b500022604c25400c41035400140014a01c0e90002d00c84e0f038100340000b0750402c070b00c400d1241c14042a120343d00da00c00702100130342ea4100c0f005401c907103d0316101c0c10084084202100c07000d0500c01d05c1d02c009a4294400f040140c011882009880d10040c411032001e101041c0c020b254008255091211000c2800d04180351070b250007608000f044c900301503046c0303604050b8058001591940c001101080075000c00000c0f260701001c4815218804030303000301c165065204401000d045502c40e000701064119065001b540105800e460401c46007070700d4003400e41074640424899000d45c0008100386001903003600718643c0000d80c1b08102003010788030f0581000d640030080d8401c1c4054000701609040004034481d661400c542e500c202c03e10b681e00c0148081d03200c048803541d00001e081a241c844d450303444c1e01031076035a441c201d0000c0c1c8100d880c00100da02440a94214484030911446010078018107110264400035212012128a41080340e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 364433489 1250 364432239 364432259
    0x3061a0309150a1a0a1a22060504210b0708100915030b0114030303040f1103060a0b0301180803070f0903050a0813090c0c0b0601020a06061401090b03040507 69
    0x7000c07003165028804456491440d41c0090b50300c00e00f0311810020300b855a855010800360a0501440d0003500303a40d070180500a20140151408001d4100543d0740b100d08181102800461000c03515142003000c034081049504480503000390340c40702c54815900c0d840b4401088412407030f104040e0020903140017103116140301c0d20803641c0c01543c4c9040d00c2045559868035078219940400410241240300e03c061080010596001d40184901027958105003030303032400287c803444040d20050190b030064091400700302488010403c0c161005081d1203940c9802103200e00070380310003c0f40c284a54600350003a2904e89180020030007054100110070700310382e256841520356400d220b2824083c03000f041c0c00000020700c208a00c1e15180c0c480c030b03c0244c94204200c0310000d502d000d034107c09402814440f40c0007542d648203882c284e00b5034014041030540e0711401d00503824800c2680d806420a8107080c1c000c158102000c80b180d120f00800e03179030f401c80b080d40d480340b008190006990042c059001440c2c20480991a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 364434739 1250 364433489 364433491
    0x202104020105090a032321031f06030603060f050709030602090a0305100b0102011404030c1b0b340c140103021b060609100e0a0c0e04060e06040c03061a03 68
    0x41810210f01e00303000d200001305a04c202d544116426082584c40307110800c0004041c207103c68000b0000c0030a50307070121070300c0f05218540703000448180b00803000941502540c0750815169440701c01454000f51a0b10004014191900041e202c1904002c1c6510000003240304243c1709030a175640d040318042c01c60b580c84001c2d42c4528552a0f008011110100106034140101120088043d90008803001d0020029003580c0c2d2004030030329000102c00400c000710350410b4103079000680c0502041c804e40e0a44442b03a0200d851501700030f0041101160010564a40d01400301c0c042c1018102d400440b034800034403159080c0010341c02450074680400410407502042c1c0302c51240f00c5d0505002d41040000c10180003000308080c20480303030780c0c88a4140480b50070b00c1c00c1c03215000442160f03c01002c0d4104021004ac9601c0909040b443c9503441049c0c08000c0e00c1903e0200180b80010820300072695180c220b0381d6002e40c00c0d81d00300c1c41145884519207200703000344215000c6030062001c810218460900d001c803207400c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 364435989 1250 364434739 364434743
    0x60f02030a12110409090209090c1302030a090c1e090209060d180503160b0106080417184c0f051c09050105090105091c0e030a06202104 60
    0x5102c648412120403c88080d00c05800d8205001810001a004001c1c840c0d002401320b9109070808400c44501d03442e40c403045011481c401a016a480d10303550341c48401810300f0f40300584128503814000c680c2e000d000c0e00d0303854000c8800280401d015141d8004604900c180c850b4030764451810422000f0034031041d0041e050580d205480c07044030003091303140d040c1150b0201c1086607030b001e8030030521401c001c40b008030213000d8001441c00c050b4516240da01c5403003540074842d0500e0841c0001c15401e43d00201072800e415440300283c0202c44034a641501044040e0600d150b240e504a4441d00040800485022050114404403184107503484855020b403043c0d0341d07503034200c0700700b010401c900141142021001040400250030019200c42d131070401ea42110b40280004086905000500492440025409015040c000c0b12180702d8801c0c174402340c2c0c0044032840041d8050051411210501c5555840405800803401110740c550b0940c64800d1424810320701c01e241c0c94914203800c1740b450455100101c0c0d2280c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 364437239 1250 364435989 364435991
    0x1050a12080c1501031205031006142710030e030d0e070b04080304050f04090b010b030a0204082b09060504030b0a1d0715050f09040209030124060801060f02030a12 72
    0x10700200b0040e0030420b043c01c0038242c0c40d0f02080100100715400b0030740c1c0a40c0308140b41c005e0660030403c04110317400b0001d1142c4800c10040c1841c2c940001070400491300701d03c03100e280828004142200c150007242081d80c0c4188203941d510302d80000e041c00390055000750341c11032025500e01050804c4c010010254038070181d956101e139610120303148900304010b001a090550065480d0b606c0c2100b000841d000007a00070f4011820f117035220000520000d90141954200e080741032301ca64506400d0402809254000d0115200c0c1e8a8080b41d4030500b00c400303500f0880c40078a81e12a020054605403002003c9101d4840050702c00c000410200b100342c00541e4000002c60340203d07012880c0f810030301c1080c0e0103405c2880c194019100170400000c1c9004070364410031042c100181001d820810707046072800b070b980d50f15010705c1d0001852030440d0360a5010f601102090341c403151140f05c0184002035113210900500c008196020000701c2c840c0d0080303182d01104a050350086147ca5120582114410b8462000700181 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 364438489 1250 364437239 364437247
    0x1090909080405121c0e100c0501180311010c03200d090f030f02070e1003021201060f1509090207020a030615050402210c040f06210603030e040e0601050a1208 70
    0x10b41e600d0912040615080c0002c00046555101407000141031517032510074042942107041080e04d40000b181219000350400134060381483c28414003500400c05001d20302c0048154107010540c1100b8540c541c244400002c00c452100040b00380c04442d10600314a035000b940c0803140ea83c0c0e206c0f101c01092106c90305400480d1450456480006014070040100c02050300300c2c203c030000d40d80c10030080004080311840703040141401040350741d01112900010340200c00300c2000e01007100003500003c00501c03101c0c02d209001380ea9020303018101e207150702a00001170f500402c001180391490007505d49040d00100282c0000e844d50785e80900400160401d800c440e25002c80000d03050b901c900c040e2000c05014101e800c4c00d412043c140c907111034070040c60b40483d420700348824000131158402c0c241c19144c450420081d466001c102c021090b05c81d0100d001442410003a0103c00c0543c00328000700c208605403028840c8450665a154072880240959074201001020800c0050f82a0030810b030303c2070150748038900d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 364439739 1250 364438489 364438499
    0xa060e06070611030a0e0d020601030206040b1b0d0c020a0e041a13060e0106060e0603010806011a270a0b0922020702131407020a05030f090112020a020a030e0609010909090804 77
    0x5541c00c216402c403011035403002c5108003086c0c02d0001a211245a101601003581554002255401140100401ca400208802040c58850600c2403a0b0510010845120a014250040c81650792450403801414080d0000960034403e00440e0700850740000022032024560700c502c040e020000b0100491714804517a14004102c041c400d2544000200c0b001083d03841c02c03c10050801d00d43d40c1c880c0d900503442003004111001d400700c2c001e4199203450304500010f22202e4a03170b1036203006000d9021403d0031005117010750314030b144525200140b400c0d00c01c80b07040c5964404220050003007401c920b4201c240c11120b4010b0b00c1000314004003000342080e0050524220f6004680e60b2292000000b0b10360381e03100e0b0514409007034504d40341d900601e607100401c04e5005695035151203004001c15800203481c0030445000503802490809100402d42030110344405040c00c0003503803180030880c02d4001c0f690141c0c1d0604a0b05029045038200c503010303141e2440302c0f49481c1c880b900400704480d05072140e11062002141e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 364440989 1250 364439739 364439771
    0x7080a09061b030605150a05030c09121501080105010b07150509031303050105040b06060702060421020d060209010e030f0a022404260a020f0d0f0b0c07110a060e060706 74
    0x2d40340700e2a540000b003a605120910100b12409240c14100803000d015048403d40c0c040c0c1240e50080c00b28030f282d62180c880d60040390b818402403400802c94054640030180703103e811011a812621464003d004690703070b510084081e8410980c01074040350300c02c005407800c20010f800c42c43c7c000758454200c0b860201c050400707600b8132105400c1114980d4459003400280300d618051190804001c49210f80340901580c00140d0340e20981c8030300c0c00c140311403514004910020750818001581c0140451034146101e18201d0001d41c45842e913240451400310300b0014a0500090705003603144018010030008030140c0070081c607100404c1028286060070720138042150415400741004041e40c9981c07443c04604000c140482c0003243d84000e000354041e40303040703016a032944401001c400c403e41761044c140801d401d04500c10016100040d00d0301041400303201003404801d0061010a024440d003a07181d10051003044a100028401d40d800652021602521441d2910040c28114454500003c0030652151010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 364442239 1250 364440989 364441031
    0x30b010504060f230d0b04050601050712090801020a050403121817101b1403060d0b0705091906090602060c04210f08030a06050f0d03030b1207080f0106080607080a0906 74
    0xa0301c2c0c804c021401c0b03000700c40079020f07681070a00119810300040c9080d20000b00b05005662001d09690078071810410a64050b42c0d080000d0304061303009550f40c030581e03500604503922900c0101c44200280c8104503503180f02e155890010310901105c00851071803c2c103011b402d007408846007121401040c2c0840b903028114070405089000c042d07200303540980001d0025041034003291084540c54410401c2200760303035680c1c095810240e8032201e54035554031403560485603400341c0c070105a0070608c680500c0070441004003225084510598508240c4c1d5142c0e0001c90f111503003035076003080c044d1040c00180a0a54488513101081d031280380710640c174a8498032065054140d003801175400c080c1c0001031190070301207402508007404090b580750340402e5400010444190f103007080a800c050b9900200c0b000b41c0e569103514100c23900c40404845090ba2503003030b85512058548685500344d841c05000140b0b0798000b103003841c880c40083d283c0921070380d03681c400f010161055220490b1002c0d62034aa0a0401400034861 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 364443489 1250 364442239 364442297
    0x10509120712060b0121020f0f0c070e160e09040f02090c0903060610020309040c09050d151a1c03170c03180613020d080d050405030712030b010504060f 67
    0x8201c0b02210342004003c43e264024100c1c10004400460081c4d0750500343c0c0322000b51481e02e401039a6000325014000c040c0541c85c031902d607401001801307250310b040008581042e669003c4803803001da15180b0340008021826012200420116040c0d000d0510f0000c400660003030142910504c103007401d07400121442c03021115000d0f03201c800304403401719060030401c2c04c0c1e0016040c0c8448650900d8010701a42c0e0703014008507c0d12540d00e0b4844081160f2140c81600c00420000d030031040c0301704051030f00d50300322203400103040103103840d01c1e0310203030200d00f00016501d0700c0d10042c044003d0165092500f0200036190a4144e090010a002040c0c0b4a601419010321400d10840c070245c90741040b211300701e448104503444520702c4c0d0026085c40050f01207201103c0c40e4a504941c904e4550280e4600b44c0c0c0140142c0c150800b04610b014200010300c100031004000d11803082280350144100460b060b4103c844410038a800600305000a0007024050000c1030481525070422001c4103503024079200c4e01071030313410407 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 364444739 1250 364443489 364443509
    0xf12040c0303020f070501120b010216062303010b0909220b0103050609121b1504030e13050c07020f1f0e04060f0b07021c0813051201090506060105091207 68
    0x2082403650500c08130300c101107008007411080d8908000280040c44860100120543d42e04d414a0380360700030407031a600150100441408199580b0014044403408421a801d400b80c80110150340e517444000c89050303801c1c0c00003441c100408041407111150004000d9980d11015603444414114072031500c055075480390f10300e40040d44c10741c64410300301800506209401e13032250098260700402c07501981c1e01201d1000407041c040d4890101700d80350000b039110b501c1c2184032030070a0205065201c651652200030950748004c42d01410403000c0d08a600894131803034a51f005100b142c005180400c50b50700503030001041550120025502c241f14403401c180036901103501c0e200300c80300500b41406140e0090041130b5030011402d01d8101c078103100c1c0c458001e00030b11820100a8162009005e0140b0512085c0c2081083e5110400311050041001d854007c4070300c1aa2440b80c403508007401402991000c561002c003400c2c582d2152001034599402020076240e001030040881e4070040c03010000c0c00c0081c040c40340c0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 364445989 1250 364444739 364444763
    0x7020312071b181803021b0f040e01150501050a08010501030f0e100902041a03070e091c0207030213060605180a0b2a190803280b01080f1b0f1204 64
    0x103c0a0708440c00c8450b1038009606202150020940100b040074030345010300307089400c0c1200d0000280707120301c00050b003661161406c02984444001580840500005569210394403a140c400541d440e0051000c10400110b80c800144401e51103a0010144488854004036562002d6008a81007644a19030440025034070148841985090b0185050b50720001000e41d2080f44004040380d110b446038001d840c040010517010407082c0e2002c0015604a281e21300e01c1242d000076500303000303488201e588070a80c03158034040c03c0da24240074a07220380c104035a16034491510b400b44100b10b6051541c50040340c6903000068000c009005a0100000c2507511880480e44405070001885041e03000184000040b483d072015808064282d03414881140094104010b5620b0f9a213007000480041620101c00b00b090b03008503283c18100d4882d4000c0610440240c0f10304a059450040d00186808200d545083d140c000b452107031842102400102540429655500d21b030040c041d000d6400f60300d00b40c80454400396946 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 364447239 1250 364445989 364446029
    0x20f070f12090603060b0a1d03060f2a1801090b0409060905090d09050d11150307031d060a0216020a0b03010510090501021c030b0d08030108011107020312071b 70
    0xd568102403d0780341420090743c3e045c150032144500854007090103020320b030741c26900500c461a0a4000c00a0700400311003540c540382040300440c9600352600014001c40803404060380c2d05c19900491440301c080700240c200b44003a100c0c2d06018000910003418800c509501154952007200103202a04000c0c41c080781c0a0700d404c0b840002c4400003000546250410901c1c2e05030f2650128219007150300458000704010b2260921085030b800e800075140d03006050164818560305100c001c1e500c1800c280c0c50400400c1203000002c41b01c07000121806090303409c08000a8448a4254094100030112410801654640358080360b030b4007040d80c00c125058000800100607500e040061031072224250f0ad030200c4240c0c507000000c0d5440c4280b0440c40c4100f480200500030043c401d80c800000c0c000010300d52000c9100c5404c00c0d5945a0080c0a0b100844d400c1c03e80001a079242081100c1042d503000d4020704104034405030f44002a000302504485000c0c0c0305040c0404a0001d0001d14064640e002c48601740000c10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 364448489 1250 364447239 364447247
    0x51609060207031203090213050702010c14090a0302010522090b040e0a030e0d060207050318010305060411040306090c081006060f03050c0702040b0a090f05090615090a020f070f12 79
    0x503511500442d8062001840001c04410300c0d1409518103040100348050360f03100003407000511031250406030745481c082107101641504540c01c203980f1354540e0180c60360030554501091140c4009950001c0c0448400c000651295000f050b04103080900100f031480e84050786244001e230b69004501d610340305c2c4000c21691034584913a140108240700144030b03140441e503000d464070080850303042c4141c0e60760641d034003031100d540c04440c610380d407040640c1c2c5d07070707440c2501c042041000c4612100d001030328120000c0c8071400c181c0f0408041040c2c0b500b800f17003002d2455481b0005001303120811502d02a06c220002282c5200300800c10f00503100710400b0400d2420a8801010f2004a5000b07004250130482845400100301313040740d01c1c2070b4040d2400b1030440c0341180410b0040c0700320703403054030645d06e00401c4c1517941a85034829402048124240c0f01c089e207612400030221030172000901d0b4400000300c08103520741c416500801a0591070b0303102a00304940e43c0c1b984001c0045201041e120382003142c052009040e40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 364449739 1250 364448489 364448507
    0x303040806150105040608160203040302090c0a0e060405010207140a09050115021002030f010312110d03020d0b0402031e040f08070305041d01240302070b150109080a030807210516 79
    0x2083c0b1307151307040a29240c40144445405402c1440d0448600b2010303981d42e2080c000ca4000e1900642400c2d21420f202c0302034126603009a01000c00a05a070580c54182e1a150b81101d00300c0710140d00601a89040c0b00341d0f03400b1240300400aaa02a8861200181104840c001c031030080c502002010f031040c4419030041d00b001007000d170b0300100ca4410010040380d1301d107501c0f8603410360ba004107450705120590342d0f0650f000d00f1030054402c09840ba02c1840a0815455002003480e20041c103070620000d04c07043c080c44141e020079180e00d4000c12006000d14400758120a096520500400c1803904d0000c003034884058980c0041008c5e00010700002d001d0042405001a0300d0303403506121443d41e03c56240108400d051201c00c1c2c0c0c0424074001210b034104001d4429016904055088507120320356081010a080904460074041404038082d120002240c0c0313004034450100b15016101c007400c036521000c0480301c0701030b0341802c204200300c0040b0f111f10030245407207620311400010103100d000c0100c100c0050105aa = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 364450989 1250 364449739 364449781
    0x60615042601020705160503100608060403051608041e060815120c0a08012018062107080702011a22020c030a051305300102090303040806 61
    0x18003044200000c0c0151010149000e2403800300100c405200301460740a8450248050024070908401d80f4441815486010031988100c04490104000c44041c2e420b03210148076100c899045100010082400b0b20014070720f6071a96100d030503c0d4803150b039640c4c20742e4125805c000c0248030183c414413170313000d1100c080340d020341311a09282d60340f440c04a1481c3c905280c604203042c069070f141036075005850000c2146a03d0300300300400310701c0a5612840741c24001c00b0040d001c043c1c101444104000e0711305c01c0788100c8001403400c0c5407401c45051040d040c00070b0b961142d21960280d01d0016071504551908006984c0500700b942d80d580045d0501603002401c0d42c501c8602210030004c1410b41c0c0391981c0c0c91014151024444500d84000065203003c0c800081c000c8007040d03112400001801c0a10700c2d072110003080c0344141c80c0344c600342d5540c4070b02c00d010b100c05155411500404444031242c542421156608404034101e40016241045241c00300f42960456030100301581e2103032381486800303d44515010b4500c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 364452239 1250 364450989 364451029
    0x3020106030209011a0901031a04060b130b040807091a06160204050702030301080d12090210090806010801050408040303030209030a02120a0b2d040807020a15020f2a0d02040504050606 81
    0x381511001c080da44146d00c1024107042d540c5201c5144460210894030080e10002d108015617540ca07808420580d05c02c180301458a4442c200203d907140c2034505a6064a02140042002d41c0c282402d1000802044111b5015200396190048903542c86c1002803050b00311075480c007852201144144415a0405001c5a003950002d100502c541040064009084801c2d0b28004030206521040c17036004000d90340d8040d4000203101c100006094110315035404841c2c4003011030700944c3e40c4420060882d802a100100a504100401c00c0031900c02c0d0068841400000e050b1100842d06074001003e601c0c08200303400c3c41c0d0304040c00290a2042c03494900d903004030040c0364601141c80d000100002c24100381d0f0400c0380921007202080901c1800405c0d2401c10341e0161403440501e032101d400c0c210800d5800d0541e801403180c1812124841d401164400c11120101c80716a003c80c41071668221540c600103909400c031040c81c440102507034941c000c090056015001504460504c401401078962650905000d15 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 364453489 1250 364452239 364452269
    0x1006150206220c080703080319090201020a030f02010b090a320c2a0319020313060f0302090301021603020c01110303060603060402090d060c0f09061209050f0a0302010603020901 78
    0x708540c4030807480029010100b000920302d285000c01c07005010350001c002c1e0b803207280c20101c02c0251501c0210300607119001003044881c0b0020511341034a5080030001d0040c1c20070400b040009019000b4209203010500002c1820441c48010520820003140c5012900f6152401f604014201c1100d4074002d07003c41d8002e000894020803842c840c04000b81c10150480d40c000b13042d94116088440036501c688040c1d101901c04041040220b680380c00090b948500c201000c0002c100c41c070b00000c222102074095040601804d403400506171055561500d1034018140c007044400080c0c0d80a100500c90100050010044200c8038100245000c041c9624a41841148401c203038030740c440002641c2e84442c0885285559580b0758002c0340190007882c0580350060107110240c0100000b5810011900c0c445903281d415800d03404404072000c9040d03120f1180031a840700306458034400290030008415010b441224489000c5a0080346486040c000940060b552443d06000f1441c0a10b8014010a40f80d2a00050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 364454739 1250 364453489 364453501
    0x5070e100501081807120b100b310b0a20010c020a1b03020405280c0c02010311130308030106080c040608010b130803040602250303021f0207051006150206 68
    0x2c81c81c0d01a100c5909007489407104d480040003044080040c1c140f440e0881d40304141440c012541c900c007aa488151b901250030045841c0030b80c00107603450001080203801c04202007125000c800780340141040b444100030207000c10000c6211000385255100c550314654030301d2070091020391005c0c502c25446070590400c00784030038241d400a54421895000090701100302d04640030079a045882d40e10081d00f0a0403c010801c010f0303504464001c0301c1290742c5540b480c006000d869481110302c0e4400380c0011524a0140c5405544a076010414449801103014a0322540120750b00d680b00040d0700845c0c51080000052148550003001643c00c0200c0741a43d5007003e04002018210100c14010b21926400201d400d580c80d0a00050040040410506480d038481d15804002e450303400440ca0204c48080c05011140755644615a08003241d0709035002d4032342031035030300c0e2041d005070944024510069002d02891010880510041034400314807400041e085241c010042c3c005840b034003c90095410050030410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 364455989 1250 364454739 364454747
    0xb0d061410110c03060406090b0901052205120d090201090f030804090b01031508010f0b0a080a020d03050d0c020a03080c070c062001060b03010302040506030a0302073005070e100501 80
    0x10a80d072050910b031858444200c1e4103440c000030050b00c41c0d0302d44105000d0100b88051640a11080c0e80a902c40594640c1c030035030254269003099440408818101a0030701c00000c048507a6204a84100c040d42c101210b45a0340d840b00d500304024407000c89a4070b42040003150f0b0094219001400b407090891b201700e15684030150140a070b8414000707aa521000361502582c030a501400c8207a410071465040143c135884081d000349a010344201035280f0300f02d5402041d15003259080101c030306d514000c0180341c980d0350134424860341c0c500003201444001d109888010915020f4041c1054060307000306414841c504004106d840046d02a0340c143c441040b5090228a0018400069410714203240d90050304c4070205032400c981d513981c04942c0d5440d04c04c004c0f54251500d80198100d0f4005c4406000c6900d03613004250300d42c4603200700103001d81d02070141000a21940a80240e403500304000c4080782d075003e54031030300450b608003070102d03940d800c0064203100a0000034900380d00440c11420504141b4100703000a8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 364457239 1250 364455989 364456009
    0x110112290a1809110603090d020f0109051207030c08070b0702100b0f0d031b05061005030d0819140c07060e070f05010c05030706111c14180a06060b0d0614 68
    0x954059150325074030050002013204208a024094103055492608240090321560903032022801405100c0d001106408140982101580c201026011402d0380465038002544031280840c14004045489d1002c104040050302c80316008018801c510325020340000c5c1072a0000280d260380c24a8040710f94000d4135402103110000400b5500ca01c4051075904055440059148140018200c002c1c408820000302064040c09115080441d4007160740359410103407030381a50030001001866800000c0c080e54001e03011212195070508000807580d103440d0b00100645011181d80c1d24040780000c1b071000f00304051041000c02c071005005480210b0420f040629240e0051040b80d042210141507103081c0701c001c0c401c845030f05030f000408101400c2031100b103902c1074101d19048e000e01038490b4890301c0d04800c140650019074228044065069445030101404140c40c0b27140c0c200544551074006002404500c035142c05808001c0c881900d41259854030029280282c01500800c4241132000085403101c498903 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 364458489 1250 364457239 364457279
    0xe0a030c0b130f0b071211270907050313080d06030213060f050f060c06010806180a050304180f06060320041208030402030307050d0e0a060201021204110112290a 71
    0x3641e13031500d681c1800c9030714903090000c14221600e0b0007030000d0818500b40003030580c1d0211110300680c948040c0a141000000e002007140c110700c07000c0004110030701c60700065600c0707201c000e0100c0b1461280e0b02c43c0c1c003054111200004040340c0e10300c42803041d442d001d000090010031801c000d116442c1031000e0050000340030b1007440e014403c1707002510b450b42c2e10340c1c0c01d940708600d101046800541e0343c0c021a5944140550b070b1002e031290950144600680045402080190044003e40c0361524265404601d45445807004c2c001c159181e4102d81250100d024000c020081e41c2c4e40071a09280541c400c122040081481d04803012080000b04200400198142607054002c80d200751281e46074000301c0c0c158030650400a005014424500e441e46811030420745034600140c2d40038481c2500c821040c2e0803485803202d4109180340c0c1c00700240001e900d411146940e04011714144850b2020b000030001a1030490350105184c401c003d0030844120083d54908030080030440d4100c0d00030b841e114a0032040401c0d0311007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 364459739 1250 364458489 364458503
    0xf0e100504151701060608070512041101050705060702100516120506010c0b04080319051512030f0f040915030c0905060f1807031a1c060e0a030c0b130f 67
    0x440411040404202c004005822068000020054905000701051b0092802164021000c0360505201c0c80554020b90b1030b036119100c0d151503941b10300200c04882021141007090030003c120021b0303010310280d405140039070014100c11000c0404042070320700c003c0a865452014016400400d98001d50054020b00811400a901d40780c1400481e80c1000000000e002c2c8040034007404100100c4800441c03055488810402c200b028264201d400e4610940d14041010306910b880d81c0c041c40e01c480d01d480c4001c4000100c0f0f1904186280040d070740e811155656008120114042154200c01d0281d005941d11654680c000942113980f45090070402c0d009802600c0c1e0794500003001d80c1c89030a4000e5038028001d041601028299200748170015041304ca5600003400c02025405401c807864880181100003060070086014061100e88022007000b41911055124503a00e2032003c018000c0c0c0f000300e8000d6179203908032020f0342030071080214007502d825000c9203012100e00c0400d0308207808100361584041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 364460989 1250 364459739 364459751
    0x30106211b0b16030807051c05060d05100c02160602060c03070e031203040311060f0c0903030d0e06070f020d09120f05070f0f09050c12060d05060f010f0e100504 71
    0x80c21503000e01d500705408000002990448041c0070150345400701e8071a80e541445035940460072940e9018409641090403c8421904104201a044680c0c8054040c2c64483e4005039070700c0b0b851515036861141d501c003550350f02240f01c0c01d41d81485180124a090f5004618007441d000b0025503031a8010305c040007000c80840882c0d0440c0c8a8241c04241c201c00a00300c0e04030038810040c00c4540d6001341d07801c4010504941500040d100c2c0441c0652040d03041542c21f140669070406109810340c8012152941030208100c184441e04840c800e202d02240064010095850003502c0a41140850107894066520212011042950044669080d14010040c900200f8660b18004902c8010f0f03200043c4035000340395020605d0b5048440710800c803610544448a01035880004604842c1c0a5601000300b2004208005c690705148070260340204010f0100110104c4645a041c03d01c1c1c8283c1d84440300c0030b899001040503c1c094640100507001003100c41c62541007101540b02154024442c050156841d44 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 364462239 1250 364460989 364461023
    0xa0b0f09191205060708070f0c02010f0909060f030b0c030f041b0b1914070c26070905100e0c0a030c0e0301090c0305011410090e010b040207050c03010621 68
    0x241c20004100c000b207212200229440c000d525900215500300004510f600001c154a10503c074101d0107020305c5d140c1c408818099001151280d0420342c3e1302043c130047c1e10303000603466400d220340e100418403240c4802e404e50031480d210020650140041354801d40500a00020420805c00c542d0000d41c051100040701c0420003400c01c01050560000e00d240c0004204646041300300b5000e001440c1d4642e0303c0c070340c509918940e0076040e400f4501c40544181019402807100e500c0c0c6490304100c40c0c0c84440303101c0d098000c0782107962418205130000e006031500c40e414403600d00c0b120b000603c06010310000d6040c6038504192411014090821500100342e101c007810700309a401045070407041c0d40c1c0034000344202e081071304010320034041e688000c1b01c20f90700e00321110044002c01d00c06107019910900c80c00c202c56107071a00550142c003405a14500341d55031100c0901c1156140d01c01420600d1080000d4168107036007408150071550264804400000d001c041c44051582c0c50015a00e0590311040e81c0c1206a482 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 364463489 1250 364462239 364462279
    0xf07050702060421140a05101b12060e04050d09090203130b10050316030c2301050c010b06071109070f02030f130f0905040c12020a0909030c020406090b0a0b0f09 71
    0x8040170b48403a42801302c04000e00c0e404500c2d103242c640170340101ca40d5001c0102100d01180da510b4610b09041128002c40f041951248000030440c2c1d88604012030042d031501960718000304240d508440541c8410403c8003116000f124000003420208002c508514100c0d031000420218807400a007407000031000140c4240600449c01d02910f809001c460541c243c03946264511100ca00040d43c441c07440c1100000e02a00f8040700038424660700312104280d00010005403681e03080306e21200001d5484008420854039400058800745004020b00007402401d0010f00610341c44c0030b032445041082d801d6400942e0b503000811541c680070f42c209440d90350f490250800c444001c40d038104540350080c001d400100c0a81035013060b409140a000d8028005d50344001c002864290072000035004107070550f081180403030f290b2200d89190f00909101100340d903d43c1c009021141d6070303040003414036561000c000c0c107402c0004c0b852000d001030000c124a00604451020107501540406c42c0c8a2500380c1902c20b000d00325 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 364464739 1250 364463489 364463549
    0x8120a140306241b03042301120507180503060402010e090604020d0e0303102306130510020a06060803040e0f06010c150603020405060d0b04060e0c180f070507020604 73
    0x44554520500c000d801d819200c035070f002c00068600c03121000700b030313281e850380200880c0d04964048114610030000212004000b02c0f110303000505000510500d000c1c142d100d4004d1038412141a900c6c4000000c40c8941003050201a400c89406913008804000050760080706c600e5100c40300700c07620b55481d9240400038010340306408007500290b05201071607108600000207075000b50408155005c0c075640700e0400d8201601801d848144440b180d5284ca546420210300030010028500d2000c3c02c2c50b80c40e1000300b042c1ca2601541c00c0010380c030040e0403605103c4148500b00c0a0001d01018500e07040c41c0c1114000d000c5800340c1900e8080500700d0100319036a004030000c1d00c3c3d007640300c1f040001c0202c81010000040c5802c2c841030303001d6030510000400d18600380e040a402c00e03600c510b1240301e0391a1612144014070541c6545d00b2280f01d407044213000e550740c01c40c44242c480d080a84922180c54003081c481d0000c40090001000d10105028200c0180d0340c480c2a10b0a4407403264003205901006c8007800c503041d40d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 364465989 1250 364464739 364464769
    0x60f0f0305061f0909060504050402060d0f0f0c020d020d02390a0e09010e030901050a08060a030b0901090c05030d2010020d0504030f080403050d0b0105040b040602060108120a140306 80
    0x4800c3c6185458000030f1301d40403138050801c1000300f07d941c1c80600049d2901145c0095008200b007080220000e69541300002850000790002444001840e030300c001c9456152020700540e00000b42c0303800b815410814000159030034070140121011200c0c40c1d401803048542c5043d14401121140d0003d0325030061a01611840142190112583c5082d0042c10303520035280944254240759800c0b400740400000c4071726030001030350350914100060100300c3d082d84025101c00d9211000300c2c0d00202080c01e0a01c0503024009c1d0300c0001600b20010300c1c10004241071980001c0c040e1b004000302c00341850b004403d00040720314113489902c010b03510a00e210305201c500d10740b220048d48086000043e0092035806076104070b2094035805258110030038195410364003182c0040c0065010411180c40000e00d4000c98070986040c1403041c106a1550322002c03107900580c1224005034804401080301c0c100402640408031355414021b4a088607041001b000c0c0700c23194200645040000002c103025454961401440c50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 364467239 1250 364465989 364466029
    0xd0e06130f06120504031b05010209030d0e040c021b21030c0c040c17011502070b0304050d02070b160314040b07120906090807141206150307060f0f030506 68
    0x949500703110406505900440001401d161a450590010b03031203000c0c0901d0301074540d000310381c18002e4000080c2d0b840481c104c8103550240000c000b00d440421441d081e100e40d50700d038200a54000c41c203100c221203070102140215440300310f0403c540580c038280f15000c3c4100340d44c0602c004c484128601c0c1240c80b011821003183c800024032070107406000c100d11001d8601110300788000515040221001c100501c1503440400c9008010080505050304105842640f030043c0c6100d9507441560030b003640c008039019145904801200021654180001c0020345940310b04581000582c0300d10a40900f05151b0080c01d1088400101644454070b0301950001d0507010f4243e81c1c0e5070b001c1c1c07402542e10b0320400400408188055008103106000390200c01c2925482c0c0004c0090303c2c070f80042c404c1c1c07110300d012129420810745558041c071004140311440c4240c024100b428180d103600000d15244c0710460740960101320289448180050b4444000070302d100b6146008282a15a540001e09510b41070f030341000c0350 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 364468489 1250 364467239 364467277
    0x41d0f1005070503060913020f030d110609010c02030a0c0c05090103121805060d051b0f03040c05031f2415110f03030c070c08060f180f0d0e06 63
    0x484000100c0049110008009100e5525405001d940f0344c042a02c115902c10318400000c0c1596203a0300040c91402d00007003071100c1e00c00045001c03d0500c14040245030001d4012200b0600140f8100300042d00325698a008001d0300c54100700003500c038040e42c5895000c00104151036020702844408140c00340000030700181d0b103540d6030701d400800b01d200e05920401148003024a00c0000c0500c0350080308690300079144034900780c404d008803801032000400c803105501003035012101149400c80540600c02004000550300d0901e400d0141006580b43c1c040c9210f80d010201103983c05141c2003045480149554010130040340f101800d0044404440840c40c0c414000381001071141d45007444040760560607260340e950700c40c212a5554035031101c2090015580d108002003002480f50030000d000f8030b4056041c004d5103030b0704c0340d58645c1000c0003030b94008408625101405200812040c1e441c801100d0200102207003810b4140c0c886c0ca4141a545071070500080c0082064152645800c44d40c172458144020400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 364469739 1250 364468489 364468513
    0x31b21050705031209010e0109050f040207080c07031b0905100e060f130f0b0d0503030114030304080a06060302010e0603040f021e041b080c0705030f032d06012c041d 73
    0x150086a24580026091f0143c1c102a5000d00b000e00140ca00140a810880b5621010310020b5844a442101d001d90104020b90f90002c0612807080998416094106112410984030301228210f402c40c4895504d46028420b00490b0b0740c03550303001ca07010301d10100555641e03000001e54580030000300c00e8001d09035140440000185910040340301294100401c40094603006104100f01c0c1c00301c0c0146140c0c02000140111401600c16410318000282140d1805840303d035803e0404c1e003441c030201c41c11602e4190500456810030072907103546200b51400c1cbd003180b03070988407510401d00260019018141c070400c0d41029170004044508040d4000e0300c14464114580768400e10b5104007101100000d030b000d00420751880d991b008440c122a0081c00039414080603114030780c000d0f480500100c210840c0c10341d48020801d0345074400903185001100d190440d00d40f0710009800c4440f100c03280a4030041149503250f00880d400c0b0281c407522001c0e200001c813903003808603155141c1c43c0300454140921440284c086 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 364470989 1250 364469739 364469773
    0xa0b031030110406031a15040905031207020106170307060e030c0601150c0b070203090307090c0c0602161407080c0f0d150908040609031b2105070503 66
    0x4200c0300c0440010034802008410001444007018012500305031030381a08011444010100451810080001415540c0c0740e0f500801e01c000c811a100c0141c88407410400040c03110040c4503000070b425941485591542d69610780c0381d00c103003a001204a1030f240301180600f0301c00d40c0544040c2c034003c10a82e18481c01c40030910313900e4010740c10883e241030400c04401c101038008000e46440c900c0358030040ca240e900b0080a000c1d8640c0711004c48081100c580d9044000c14182204e0502911040e0040d6980300d9030300042c181005805c4d00807440080c04c040c40c0403000b6500038240c0e21110303080000103880b1103000d03801c1000301c0e036007500203000c401d20101601011013001c03034480100c50364107084a030030615050500440c2080441c4007a070001000800e000400c0503015000311154029200003200c003200c0da030319035560300260483c20028410310014000c100c03406604e00d6106900300c10f00311381140b4101c0d401e41403040030041656070740d010640d1b90041240c10441c1e03101a140c018151056240324003507201c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 364472239 1250 364470989 364471021
    0x1020d12052e0806060a0b041206020d020a0302220605190e101e030603050319030e0d0f020f070806161101021602181e0709030204050c040503070b0f03150a0b03 71
    0x800315000344000f1542c1842c6c4281044122150810500c2c1090300e00424029160a40981a107085800304180420710f80383c0d01c02041c003c0020b40b40140c0740c009d0a0105888014540d420220b503051a810074840a9000340541f03c83c58080101d1030450040f1a404840301c41405612035003003032480c005920358603085422140043c0540c0c4581070b400760280c40c11020303204240300140643c0c00422030042614011981100d01d40403604010030700c0c07103104103107a00d0030700d040020750b001822038203481550b81c0e4180718900b0b8410b0310388000c1c0401c80c248441280c941c60702600105415503c00131200300580034111007014603807501c00840d15240000c07800c050f20510340c3c030101d01c40e412503104c1a8208410350802c5004442c0080d001440f1103d10f4102000420041c107500c0c20f01010010000050340c3d1405201e10611055074420344a51a02c4141403411500d50440c01d40c2050512066003003042e1386e029650700031410154036480104c000049500c824181c3c001c585258400401c0010b00100a9050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 364473489 1250 364472239 364472249
    0xc090c030c050f070f1106030f01060806100219031106010b030109060918020d0c05060406050921061f03141b01051903020d020415020d080601020d12052e 68
    0xe0040d0780c00e440e01150284991103846800503400d1160340301007000c008620038080c2c0315980385101c1c41c00440c006000c03600101c03208904008150700610030316601000d0143c1009050340c82c003e006c041000065224403841c000c103192465140940403d00d4800c1c40c403143c0c00c1c0d1070032017524025611024481e40c564400d0060295407400d2410008901d16107100d80103001c0743e04a14490214030036820015902c040710002d4860408040d00442d840d0740d00801130005140c60780b145e0f9542c2c0e4130076060040750102d0300e000030702e10802001c13046c4083c0c1010800c03540c041c00e443c180140c102044841500a04015080500510400d80310301101010006081d5000008690300011800004004403503d2081d503130402045a1584881403203240250081c00c00a4074641c4003506064442c4000c0c0c2584000c00c0038640140d00000440100b5a041148a5008082072002d456104039418028114842c06c03441041e807156580001006400710250404000c00054a81450000705404a511b40001d034060 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 364474739 1250 364473489 364473491
    0x20601030b060f180a0f020d02130e01050303071205190f0210060605040603180203030a090e360f010507051b07180b01050c0d03050a0516120c0c0c090c03 68
    0x41192443c01ea8444008200010310840318403510700300d80b98580601030140c1800b1616080c0c44841c605882c005004080d070310003401600d40c0315480440c172480075260300010120b100f800050100b51400300c03c4400c42070300000d0030303c01100301040407211803054000c1d030b100c807404070700c220080940d12101310320030600e00707074201c1e5502071454595004641080c8180004900b08200400840d070094000c424490481c0001c04c17600020fa4021a04607030100c07444c1c0c0e002411001c070a2040c0040c04c0c00082e0032040042e051a562040c0200f550314101c44010842c00c8100c140c0b0720040301c03200401651510361103282c024022410441409441e50700300c0740c00c8010410026104041c0f0354000a01e4508550b110701e40b000020641c000103200600000550300d04100341040704c00d8807070004000c4404000b100e650700255074504249600200e540181c1541e40340c9543c031141d04143d691103040c07014020565000021005a0380700d08ae01c1d85507070140014480c005c11003000884080e1a40100b10403081910 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 364475989 1250 364474739 364474741
    0x1b070608010b0a02070905220b0609160903020d0618060902030111130b0901020102070c140102070e0c030403111009061517070b030a021b0c04060821031306020a020601030b 76
    0x2e40350aa40900380c0c40780d00680c041082041800c1580c0c10041c7c00c48601004071200043c61107060307840300c2440b80190b80c200008018004141010000f955001d5500d410f1039666001020000b082e1006521000e849070080c05444424401107034020f0284000342407c0801c040c0305440d01d030014000f404000d034882e510300005000c20f44840c400b107500703e5044604007000c041c10204010102e8105a20701e504640d8240084000034171100c8400020b1321442401d03840c0954040c00092034181c10307400880c600c003048414404c00e40380c1030042d60b4120b541030a240c841203880e260744618002082058100181c14051624140801d690255901c00c4080c00c0044459454480c600128040102c0c7d039120f561103880c00f001007020500140d5000807800d000035180407580ea00071420305800c640301d90095000b80e00d50001074170341792103150300411b0002c025205e07111503604c0326102003041000314545880000005800089d41d20035441400e43d00c030404544552003600700a544550901003261015403c01c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 364477239 1250 364475989 364475999
    0x36010c031409030904020f0f030f01080c0102030f090d020103110a030b011409100c0302010f090b0f091b040c0207181b050f190e1002030309160302130905031b07060801 74
    0x9001d102e00c2d0044011850720071007900b4000290b002c11009188441c0034000e4582c1c03902000019030240d01d242c45181e21a5050401e0f02c1d0070300311010242030540d8802c015410741032401c0c10a82c1e50190040701c014004410500041c1d0142509046001c207a050010f6120300b0940c0590000350310020a03aa0451708a2140003011168401c8000065010032040341c04102644140052200a0310900c00840d0050520b001c034020f0304c0400c40d08541889800341006456100300d040315034000c812100034111010950100c0351040c40401c0001d00032074903604050651030003003020100a0591140415031040038900c1725004103811200340c980303c8001100c03151401d110301c0035600c1110100c41014070381020007901d80708401600306810b007800f00c400506401d641d5422410341f0740e590a034000e1a0b6070300d4081ca01601f403004103404040e62005005081c400742c0c849000d45140d4003000c540c0000c803d1218100a45113000b048002c0d080d0701c1a4100520b0400d82c0428480d040b03078029150003900d070340c0759 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 364478489 1250 364477239 364477271
    0x204270b0901111c09140105090309040b09070e060307031d030307090605070c05010302090d121706041e090c0503030703030b010207052b08040503030708040e060109050936010c03 79
    0x2000340782502220544c6501600a400c0d400000c0b840c1c421240301c1008603d002c0700c5402c2d80c0e03040314001159007004c1840c1d074841c1002d00882d002d0982c21140715041b0310304034074041d00c0c031000300032024051000480012001c038002d90145950800074114a40c5c003050480f00c1903541d5000300d5078100004d0700f03040c4c0041d4071400340c000d95414607400001d1450450900700118000e4101c001e03140e034010607960400b00811040b4005000c010460740d20070351103606035502d254010341c002d40414011403801030a40d05c0d0220000b11190b2503400c5000105462043e400c2801c039480341a0020780d0305000000700e82c8201500355200c8501c0000c280c0075140d4260ba2901040080039582c0180f58042c1d9007091401c41da1190f007050366503068802c1d80c0780c600302515a00882d165820100080b551144002003e001e41c0c0c5d40b02d801594400d000f4649000d4160802010405403000640032039484210a51610390211703146c200c080400c1c200d01c404d940040d000c000c2e0707140600390549000003c42d00e8030081041c0c02c104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 364479739 1250 364478489 364478497
    0x1020607020709051005090103050604030806060408070303030b040204211b120305090a18020403060f0e120c010b102006150f0103060e0112030807110a0204270b090111 74
    0x180c0c000e40301c0540342c50a0140900340041c25030254110301d076001b20340c903038402c03106c3c0f8081c2d8013440040c041840d0524029203024405002c4910800703051008000e010400501e05003a13a0f898a00070420303c0c84400418081d000700e0308901c800c0f03c18145020140b49001e8031131100d1900800d071454000070b81e80264020440a0f0080001141401681c000842d0092005006240780036015500740c595510480303010201d488140030566400107010000c0c000309004110f42c00240d03500801220211114455981000581c041800400428422200030086d441807015660280c90500d50140302440148417005520508014040c0c15080c1100ba000c0054228808e0030103000c1b0210744000c140400003880d106150840c10181c40d61070225299010144d014000d04144012a48851070f9280181c05004010180c83c10000d000c484140b030b22800065034000d007901070b42d00048000c540f5202c40c4d81c88031042d9144c1c43c600501c0d01940c040042241d41c8a10400000c002001521110780380c043d640c0c89 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 364480989 1250 364479739 364479751
    0x150306030a3206190e0a031407080424030b151309180b010501180e0a020c0102120612030f0f16022101150320122a010206 54
    0x1001000001c005a10002ea000007880e001d000d001444405061600e841c9007081d4014819400501c1482240e000c001c8401c0420780b0725050a00606410071541966015000d42c0941001002c1da080514242d40404a42032150004c035281d640d60780700c084c144030006004012250700c0c403001090114480c07091094258208000746203503060308250107003000070f8001140f41c1c2051115004e0010b4110502e02c18607600d5800d0010082900e1802d0030300309011103050740030505102043c019011410780b90380095042c5d1b4500d400d44800e54403071501400080c00354070007039115076200142404c00742c200400303424818042199507100e02d07900b003246a80c0381e0190301da010b0b5406405000d05814804040082c0844041540c4914018000c50300010910040b03c181c4c4003c1003620081030701058028020425210755801c203158a04e03241d586e801c1c040d00b10304180c4024600c003400c0340482543e00c82d00d0800411050000301c82240f205540b07400f140c0300c000403401458410303e03040980c90f03500104103284121 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 364482239 1250 364480989 364480993
    0x1c0204140d02040e0a0c090f1104060c0302150c09040606032018030703081305030105040c12050709060b04140409020a12081207111006150e01030f0203040303090215030603 76
    0xc6014000d01088004808003281d010303445207000c9184020401040115501484801c0c17082490954180220766800030225606d5003040000030244200d00c0444d403c0368468913059480107110f080803821700610700007100032500703117509004010320880007814509404036410481c00d030b40d40c041034048a640441c0c2d40d03040c1098110001401c4071803c05000c028403143d8102e070311440d4103c00a070800010b81c0045840410104240f68002441d0038540e01610064000f0411420540c890441e1069644903c028070403001c0210400c02c0000d100082c000d19643c0c400348031082c2c41c0c1041d14034030342083c058520070492001c4141014035250244030241600a081c580711507081006084500740c01030026180d0400c10050406040c40c04072490740300e08503a6440d000d2a24904544c2da051007c5180c00344a41420704005100c00b0f00764520324010201d150424180f510200c400507405005900100c400c01361004c0200300030f064040e000410138502c211103a00c8540c1e2281c11007134650006403090340c1c040e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 364483489 1250 364482239 364482269
    0x181c0801050118150509120f030304031101050702120f09040e01021905070b01050f0d0f030903021e2209020303070b06030105060904050706120f15170307050309060304060603080a03021c0204 84
    0x74170f010303e00034000000090a0075449007040c2c00001e1406410401a8003982c0c0000200001e15911020f0003c040f50301000a00c400d0602c000c000795a0602c20300b00c4900f408000a010181c210040101c50328444050400d00400e0140030182e4000d4000c50710703092130300301c1c45400c80c2d182e1445036040311001503104000210a9090038180500b11601e05565a0440c9119901d0800f0030150109525994401e41e17419034100d085105100d80700100d281c01814149064120381e07042c0d524040c85180b4500d460109800c0303580c0400740302001d424800c0010b505404000b07914814001c1d4024843d100b07030303419802400307592203450078403040d42021140541550000c00045c041d1900c600c010003190000351502146000008070140119000401a03031241c10345402c0c10015100040c0040f40c00190707850180d41061500d444450701da100340a00c00d071049500000003070811906600c142e02441d0480e019070785440c4c075454050002c8d0312040240032280109805544c60030703014009c86003070f1925581a1030303130 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 364484739 1250 364483489 364483529
    0x6090d140409020f090d2f1c0302012706060b1908090307060f020a0206010503061905100b0309030d1a1e0409060e030a0e03010501030209181c0801050118 68
    0x139040002d83c0c4102003001c0041d1070103540d521001780e0015002d00e20100c800c07514078502c001d59440345c00c094540510b00040f560100d80c0c1e2800c491911142c14405045285e08a00e001c0b40109484690b031031070b030002c5071003c3c0a4200418041559144900c03010841340343c0352101900c050148808142d03884d800c0210b40706026100f00300064000050718212800c14580c0e958060945502d45c2c1d44480320360b1701049041e091581001040d005180541c0500070740c1c00c01d030074040b440c05c030080b102401c07063300c81c00411080c2c000340b02d28400405441006030b4490500805280c0c036684182e4440e114103081c03c5000b0941042140650303940a0001c4c06105c07001002e407a030a010a42e04100b2590040d0384a20910205082c0c1c06401c40648001e0040e595801d1000409001c5500e01c3e00024002c2e07140070014001a2140340105405c280301180d41d81400c43c20342102444c4c00d142151400a00c00c9008042c0351803038000d40030506070341003601d9003007440340800805d1500549521a403012151440c214440e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 364485989 1250 364484739 364484741
    0x51e0a0f0503031c061211010f080106080c0f160501060519060909050c0d112a2d070806010f090212061909060e0a060503060c030a050709031406090d140409 69
    0x300c220744d94008074030765948210311210b2a546440a6450280704034462402d036a0001c003070340c08800d450410707400b10b50400100030b003500320007420070008040025242c81c1700c5d90a242928541015080010490000d91407c940645611b10405000d6100f48501050060f00c03d40020103644141d561b0503001d502e071070f04210151401814182c4a0201007080040300e5241340180000d2490300c2040307590b1511501400441098043c0000d2504903545000000981c0049031000300c00c03080704a81c4894070700d40b81c00c00f02d01180d0354070020590300c03d00f100020040c6010400390b04840c8104050786040303507140041000d9104807083d10460002d51000a001c41c50030307203003040c144004510300300c9101d0b440e0300620003240c0e006d8001080c0142c9035820400c00d0030480c00345001419050b00605100e00788070680c070105000103003c403103440d07445000080d45207120720811001180c0001600400400040f0500e803034890a490510040c02800700d010300300740c01661006160302180580034a00303450800c03c20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 364487239 1250 364485989 364486027
    0xd0e120306060307032a020607050f040302121501120b15060d0e0c0a060e03010b0102010207080f16080a080906060a080d0e03070f0f080106050a0b0405060c07051e0a0f050303 77
    0x241075507605010003144499940241c0c0046c0441d50044419441802a00d0614010410b0003081030070000a005c0000710026102200d40c1030315103072611064540703007601b41100c00c070119801e10540000064110a80005600002c0c090206c003403494441500480a142010f04801e400c5001004185500015944031000540c00329058408042c81d00703000801c0303000d03130741d2081001408000c40701e0102c2c5800c1c4188244010240021071620255a0f80c1d60014005d00c20307603140d00200840c011f1241c00d41c0084c0050529408081b89a40d8081e201000d0080403040d42d00078094030440001a07000e091916281c026108010028095029035240c102d41300b06c40e09604d290075000341c040c000b914180d09500800548121104d820f41281003190060844c0c400b41e1002c0d105086200302046041d10400465041e2241510703441c3d46c51403008125454500190f01560f0001c4480080e480505420300031144101000c9824803c0c480c4d42e0100c0c580010010700496a2541003040007c41811070a0380003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 364488489 1250 364487239 364487251
    0x1020a1d031e030a020609061303050319020412150506061606090f14060c070b19021201060806130608030415020f0a0309050a06020303090d030c030b04110d0e1203060603 75
    0x160b030004050041d4408110400c00c0e2110745620101d0741c0c0400b0b40e010310009503c260310000512062820f0201c6260524031110094240b00780003000c00e203025082c0b1190000d2850300035080d5500c070b07980e20116444e21310344602660380449005014442e203900b07000700c9006843c024035990030070142720011070700008128012284581d9400420000038445114a10301602443e8000d40c81d040c0540005c2c18000024461a600841003203284000b0f000d250100d500062011340b900440c2003080ca454000344a181c0c00390501480d19000010090351040d916031254400b641c0308600b45040348042c405803111405031841c1074005110521028413046001880a01503204991000581850f600e08150300c454081c2c000410341030007440b0a080c4804140000d103103a1000314690b241070b54042d512114003600c16410540ca5944261040c0c0c426003241c41c00c180000c0040000809209841c80ea951100300c44850300c501300500041a0303607000c5104da081c0d10f400a0410b145503215410080d141d8002440703 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 364489739 1250 364488489 364488493
    0x170a061a0c0706020a030c03080711060a1d1612031b080a023d0219020c1f0c0f020a0b03090109021908030703050c10020310090c0201020a1d03 63
    0x5036440c0e01250960088036600399503565401081925814002503400100075584840c103c040000c2e80004001902a0180350415042d00c0c1d0040c21034a01d88003524580301ca204080c2031103910000b613400100b0710074511039003982c0c128a2880c020307110b01c941e90f80e01025081040c0704106024888420803032030341c801e1400c0050940119000703504d03091049405c2c1c070700d418049400c1c102d02d90100900f0360b044011709900b58000d99041002c0041e00400e05801c4a102050310300c0e00b4640b2100e405035400c2ca0701d200381d0700594401401c0001d640b00c0d003040d1228400d80c0b004403610b00700800c40c68010030b006415074590340aa0b0350f030741b25400c541d03210503812078101240510000c2c0c40080030300614080c0481c40f0003c50000341500400001c400c00b041090070154444804209020b800001c6510311945800c08a03154040668254144480d24007804031050002040121240d00c80c401d03c0c0988040d110b08010081d44198100d080b4000c0d8043d41010580e2550b0702074010800d03040b680758628000381 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 364490989 1250 364489739 364489751
    0x12070b0904270c090504080a030c11190302060a05150918010612061505010f030b0310051006120c02030f09040e16050324060609010c05030304080d050c0a170a 70
    0x4072002c00c0c02d00010140341d01c18940380034004001100401e80000c0009503001c1c055030134507440b4400d842c03103080d40032402e241d0b4440207241160300071441c0c2007004403424281e500e04a1401040603091400700000c60041c05940009240c400007441003901512880038110744880c0e0810601c490f400707024251340300c10210840d6003100803c003402400080c00304070b9045c428814007803410500740c80d4811500400500c147c031081c442d0703991258014078100403034640880d1480d98035002c80d042500031000e001f005801c003010480340010070030000040701e4140d40c84038158040c0c0c290b884210341802e000140140c000304500040b60740318001515080100a100041881d00c60941070315051807240070703482c08803400a0820040c5000d002500154802d42d690b4621002d4055040464040c0100b48034860b0102040780c082503446107841e0301d45245d04c4411640e0300c2c00d1505000480741c0100803019891814a00055000340115041c0c880b6070080d0341300c5080018510410041d454001001c0c503c51980e150 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 364492239 1250 364490989 364491011
    0x14070803010b0a0807020c0904170c010207080c0c1813060e06160f03061a0c030903150907051f0c06021e1c05040215072301050702070512070b0904 65
    0x220096008103035801c50b4942c0c441ca00140501207842c01071524041d500f04881442d1582c03520148681e1041c0e000340300d29038514042140d04494001d04440840540c4003140400410003954000c5c440300e02c0d110101c0340c101e107500f0100310401c5130984002d4490a066030204101480284200c0011840b4203c0451140b440101032854007008035110f00d203e00310744982042140c0c00801d5481c002d0f81c00d10b800c1c00340714148040d61001c0c44491200d0023104000048803140d520040c0280c0b2603907400101034a080108040400340c00700c20139204030185020704c0d0307000201c0c1e18001d8158040d03011120300041c00001d00741804c3c0e07940550000305076a06a02000002010b041420b855410000841c8103d44c445c0440e40d164186640340400482c05185004184000b41c0e4a41c0624034840c210540c24036070740c921601c0e241300702103d18039482c00c010404445044401c001034014901c542695400c48001c1a51102000004500d030303511480c00d604419030a02140480b00c0007400080c0e005800410700c6041c1c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 364493489 1250 364492239 364492253
    0x1003140114071d040608030a05130902040e07120606091e09111c0b0901150315171006050907110c062a010b100c051504080d0b0402031005011407 64
    0x2101d070b81001800981080d0020699101501c101c0c4030300b070740c04010a50030304046507601e02c640312803901880804200c08042244402c00403015203283c40055444a039100100022280d05481f83c40205000b05107400d200c02040c8a000103e5106946007402686070000700700c0140740b0200c511030a0603499001081a01081c010154100307408075845a54151004580103072501c501400500941030000840c1c456440a5440e03040d2000003042001d8000c050740c043d0010007144102c00c0320ba950b0b2603c005272100b0407888400e420310780300041e0390594401c100d13103404031741c0540256a4400810300200e400c452050464080b0184c4100c2100d000c64604000a0a9a005003106885030449541d5002403071a5040b9119070612004000703011034050700b400111038803c24030915003000018a01c99091150401000e0580c044600700850380781001d0402c0700ca285c0c00440c265207000d007002c40c411a50b04080c0f007268420440844130466990401c4011a184a15040407007140042480100c002c110340c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 364494739 1250 364493489 364493491
    0x3020f0c0d0e0f1903120c120207031403090d03120e120703170c041211040513030216060e040b0d2306060604060203120703020c030703050903070e1003140114 70
    0x103a5168045035a1000041162941c3d411000c3c80c0035007110749030182c048071820688004d03607900010200b88552089000c0f6040480500d000d4607440c0070042d0501d41c10780200b400c6013900c0c010080b61090a00c6448815940d105400305507420804030070b10720002c60700c2040305042c0800d4a81c808500c40051804140c81d10301c68044c100c4407000b000940004240e08568011654403441a0080c036510308842010500d001d00d00c540711114100500000401c0810079025090172002441000755040c000e83c0e03041100050103044025208409210040715484a03001003125450394440002d04499002e000191012141d02600004981c07605000580c0494a4402e400d07140f0003d012054505480c03645018806820070740242000c20041c0166035002c03045030080c01c0c000303000143c15220400220001d1290190101390b9000c080f5907401095031240081810101c110b0854550503140c0481e260744100c00c3d250700200c0d1500303400400000f043c204528444410b0800006151340740c1e140c160b140c841c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 364495989 1250 364494739 364494763
    0xb12090708010204180e0703021c0201050714031207030516112d060703050114010c1a0106050a0306151e0c023d020606010c05070317041514040603020f0c 68
    0x4211550f05c6501e0942d41300b00d161094594000b051401c0c035640105082c50440034280c102c0031108041d5405590060007114000359110896034036040c1c500f150903849810000c0138000f4a070100703020403015031084c0140c85c081c00444003803c5100d0525031040d1450541001c02c6802402041d0444141681d60749032071091040700e07015807038a03441c074140d500d080c00e1005265006040c0b8000c014840d500468061200135882030a206807510341504021681c4001101c191035840c2401d000030800546c008003805d241e0314036071000d03c880c68039031050406040d143c6102900080b80300e07401074082c40445c00e0094401c001c50416150b406603640110b00a054116901070b81d08445404a04502c0340a488690300c40c41401088031f0702d000412402901c6450141c191810041119031080900000380880c000942c1e120011208030007002100a00c0c0e03820074880c100c0b075507074040c245030707280b50041c0c0c00d016081107140390162a050519034280e009402081d058026040c0a10400000400070000241c80344 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 364497239 1250 364495989 364496009
    0x30b10111204081608070b09010c15090501020c070e040206030703021c060f05120105040f0b07200d020d14120a020702031504170405130e010b370b12090708010204 72
    0x290030f000003c01c84c1c036030790081c4101e030311403501003001e540c58006032901c0c40424a044919120785040010202c1c154081340c504103441c000484040141c15401841e03517601c0c0c0310035945402d43d283e901c004800403c4030080d42026040001034200740c40796004100131210348581c100c8504445151804480b040c0c0c110150030070300f6a10134017152420402c01c102c082c04040081c4014500b40c4c1d1100340a04040c5401460b04a486011500307850040b81e0000fa1146d070720781141207418100090541d140740320841040580544401c015003d40314189100b40d001d4240c0015140c280c941445844000f0001c04079182c0300d609020840c0160b5081c4600c2c0744a12003c0f524442c02d052070b0811a1040c041c0385003203030414030200720400070394803100c0080f40e11013008040040ca80010000d40d6000d080d02c07501081d8002c451b89080800c012072458111900d050384035000710f09000082003030809107064081d412409038180401c0526a551864940d0300c059040c0545230714942d141c95245c2a6001074101001031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 364498489 1250 364497239 364497253
    0x6090703090c120b0f01060e01030b01090803070818030c091317070609060b06270d0c0b0a110a0816051006090f0e011a01270e01060f030b1011120408 66
    0x800704041d1415006003105d004229954903040001e0200061196524145600c4883c102c0d03d0303078020030140c0c0050000d28166a613540d420310b4400520341c03010340003c80310840c81c0c0c0f010025003400255451081c0028040d0070040d1a03800304458003408080040700da2600354105080d428400e480034101241c85030b040482c00041e127180c804107484211400c107000701424059080f4180c6080c0381c22603003114590844204407000000f00d02640003854001c0c25118008a0004001c00e014008000380c10141d41e4510204000c880220340f5140f408001404551040c8400c00a4004111b0341d140d109206004540b0686041c00011003940c105074000710070a5030f928031040304000710f4001c11001d002400001c021840310481018041c00351941610b040101400d9413244210394605200d1001880611004415075500100c4c00685402d000b0b6200203000c5040000506000b07000d00111aa8014400009003844040c01c460b0b50b040190781e5140c5100302408407500c01c00000041001e00141c001030510 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 364499739 1250 364498489 364498493
    0xc0f0503041404140702100903020124051002060103020f04020f070614160c05030a140f0d02090114130510021e011401050a24030209130c030b03030702030606090703090c12 76
    0x201c40e8034804c8607100403044000c0180e0564042205541c045aa0707500040f40f16081c00c2c12801081c00f00e0a2074444074120304084001003600098008450048030741e0482080c1d803420482e03c1d61401e2000941007650303e6607402c42c926068010f400740c0003400241c0d509080c02034895005503070315404403144070001e910500030004a05c1c22451300e83c807142d0402d40030b2a8040e075501c980d6407050bd04d00404000712410b185400c42c0805003140d4203c8c140c0b000840e100e03217080c50010001e51041d40d0003030114031154560729041d0445429507000c02003030180f0f002d100c0e144c05e06200c4420401c0e00c400003180034441c204102158a10101c1040b01c2c0d60000000301e10440001c0540b40000c181c05c29442900701c24800c1001b14008490402042c2450000700011144104140c010780258005140e00c120005001e0700f80d04129404250002c0890350140180399292051503140d00c100030000e0b4040c0c00201c00194982481d101e0ba58001c0004c1c60b000444200f540c0720700c1031441c030f290080c2440c0b00d284001030302 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 364500989 1250 364499739 364499741
    0x130f0b030706020a0f02040b04180305130e0106021b01031e06030203060c0f04092309011506030c090b03180a08070b0a060509060f2202131707060c0f0503041404 71
    0x400381403240001e201d410003985404140c0407417554002d1050782c039916010701c00d85450304030a940d03d1a500c400e0740d900c5594980603090f50400c8092049a00034941c0003c1d60310654400c1030b0403a070180d000b90001d048a804048a070b4070404a0b000c2c103050303ca02045400711030f1402c5990780040c0145000481604505c101400c1160240c40f0103000d0340c0c01e00101d0392180c90b2100729030440d0700c020781c001040c2d090030040710310000b46001010141900c1c0f100f00220700006400203003810300501d058015641e11244160116040c038011140001e403104024065091004011a04404003140401e00c011101c040b0034600495080c00b20f0303200c000441d98100b08004482c0c002d40106401100303105031814100840c8200320000c1c040c0303101e40a01040314980fa00c8042c2101d424601c00d05207410042c100b0b41c00500a540310040c2c0e4011070000441c001602403c0d1404401c054011602070881e80f85000c4e42214907529030002a10f016144200c032100203203003080204000c02c07004c02d28240c00102041008 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 364502239 1250 364500989 364501003
    0x60810090611120c030a0b0402030408041410020304090b03070b070f35180d0506010812040e131e1203060b0a0215070c05070803030a051b0a0e130f0b03 67
    0x141d6945803e1150101441ca0360080b40d0380914407001d42c0341c41e81c1c1e40c103183e0006880d0b100031030ba401071710010900c8107001c1e200340281f0540b100e88080b40d42468028060007403400007090210016041408284030b00b8885030012603411381c001b0700302c3d01055220340c8502207d500c040021240300f42105d10b01000c0040c00c81c41e07100300c00e282055400d1404000f8052031890b001d0030241141000740003c0d281c130191042c841d820902c1c40054007142c00d0649514005948020070300512929102c0ca00d100e81c00040c2c400115410f54240500790b10795521440445c0031841c210100880752003681c5500200141680450f200c4800c0c000c61060500ca101240c010741100c000780c200c1110b021080140e04151600014001600d52400b144985159600041160034240d035103001006800f8040e000030b0f4a4600002131401000c10321000c00140e00c640f40030f061070740300c6030418001000313081c012809410b0103846600b40b101406056170300c02070503980c0c0d45422a003410741401c45a5903607412440741424100680 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 364503489 1250 364502239 364502261
    0xc06020703050304091112131e02010203090d0f1b0e16051909090f020304140601060f18091817040506040905090106030c06050c0c010e06030106050d0608100906 71
    0xa811036505646545480384a2402220340381501c0d030000480c0c01d01444220b55151019554000c142e00b017130044442080464031080ea861405850005024202e0f01c900c900c010340e058000310b00d0072100c081131241c2c043c0d40b04000d5804512000d202000728500034071030800d00c11800f55a9415600f080045c2041d014090507203030304034907646d251007041500f150440d000740150300c0305004501c620344000c5550601642210407124200070a480d000a900d401a41c00380e4414075803036001105403120940c0d640e6003441500d000079107200b02d282c0568050740c46030380d15450b4071400c012056112010601510b0124070081ea64203101c00001085c000d00180000c41108041c90795803810345810000b9006004e18040c3c061032a59032404501a0002580010021036011091110181d07903200e0181954101d621000340c18001d03e85042c60640c0f10740558008004000c03e1b05040d41d09140c41111281c0003003440d08006a999100424845010443c80441c0c451a0602061180e0711780b61800030307141c8030f1600d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 364504739 1250 364503489 364503493
    0x33070b1806090a020607140a02060d0207021c230f0715020c030d05031803040e01031a010b0903030307210e1e0105220f0606060503041406060f06130b12040c0602 71
    0x400c500613545c18046a055980044000d001c0351302007036200d4104030680500a600c00030005070000c020110750040c3c26018021180348082c4000508080d040140ca02c0700148100101d1400c03d02180400c001c414442e01540c0490b4281095000c580c1c1ca80b81e1140c01c83c410030010495005002035040100c99007650b0294040c00942050340310203040c0723010241c00681c4035221004130b0706141da8204185d90003442e442601500950b52802c140c0700b541c00d8030a1100c1c5054a140000c160848003c0484480751400340041d459946e60030002c644103003001c060210ba4002e014505560489280500c1096240e0007000c1c0030304800c001940260304890119940c5964104020001c03440300c0812140e0b04c40c0e08403c6508a007040c0f034a0421820f50a044d002000c00b842c0507004501103034098041c40c4940e114845480340c58014040c5181e03681012a841d90303200c070b03032141007507214148032000e0112400c2c0d04c154000d8864852080f84941e8006501002005e40750f00108814028000400d400422280c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 364505989 1250 364504739 364504753
    0x90f110f010f030e030c1501050f10050706051005041b020d020703050a11030f1501060f09122406080a02090105041107060e210a02060633070b180609 66
    0x20001c2e140380d5805a440c0d0605035141030503400e002e814400c40e6101c0c207460095503045813614042c041311840c00c2c001c06018401841100c5498100300641184034451925a24205030b855500c0030058607009180c58100001c038100010a51110302075400b605403050440100309000c0302000303242c40c010525010443d8004801000882c002113104611103030003a41c0700c1d4418003030360042807808014031450180e520811544040c0c100340f4100150580705503669440300007010304000c698a07211401405411044071410704001400c03c10640d00008a0f0300150300d0380c0183d400100304668140d481250950000d519070760462602900301e501406049804205030b2030b0701000002e003800392070700003042c8556a402e4800c01c99810840404158a41950070712540000c03010b12000345c0041e0103080244c03107000003044d401c0c9401040502010340391003024120044188801602c2101400075504404042000d800030845000140e80300e008864541d803040203004c1c0850346400c0008000c140039400c000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 364507239 1250 364505989 364506019
    0x17010c031802040f1407020601080705030601060f050307140c0a0b0603060403050a0f02071e03140106180c0c150212070c110108250207090b0303040b040603020319090f11 75
    0x5091803203000d405480010b502991246100014540061040c40001c050010400010740c00a02303503040c0c0b00340c2410b890040e50340d02c0034941c0d510020302072080800c29a09001042cdc0d84500041c40d403040440c50401c1c944441040100002e034082186030031250071281030354040c0200d40783c0f042d8100f50103500920940c41d041d18003c00034000d62a0403002c0203401081100028420800c1300c0107081e24480c007400d89030850780f032001c8000072840121032641c2190281c81c2a4401031140c0411900a5805809410700d5001c2940c000c04034840340320140074009000b100462104025581d030058070210040e640c0d108a400708001640c020012400c01841000602c00242210702c5000c00e0039007801c0ca0365003911041c4503140d0300844a0745040d69005200c0d2600d01c4203900207000000c880c0c03900410050854a80306068891280d130188070346201040104022240c440e50003503501422103041200804c2c420380d034010580f41c0f200c0c004c2d5017401c82c90320581c0c28004400e0440581120841d0500f5846440e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 364508489 1250 364507239 364507271
    0x3030d0e010e010b0109080d030203100f08010903120c14090d0b150109120c031b0305010c02010c09120c0314030c16030209150f090a020c1f18020306040803100306020417010c03 78
    0x407423003000c101a004004254189280a81c40d0003801041d50a00d08007615510214004d2214000036000204444644084201c2034483c00c2c0328120940d0341c3c0403c20078400388410380c81d030202040d260481640c20030700000c1504031640501070050781e50f501c0540c9600d60001854040d0a0304146030402500b031010b400550018441c070200d0b54001405054181160325009001840f0361010b0b0032942001841d0151990662002c037588031292078034040b054450902c0d0f80c1d14100504020300364243c09505001096498080780e0303600030500c040300c0c500004410481d08003282da40b20a400504164400e108501d0300300c24a60b4415010080c0d0b0590360a25000200e014001d050b100340a103807400041110001243c04496403400420107c400501754041e4880708940b03100050400c0d00c0c036003001d01c18500722a038a4008150b400800508407915a521280c1299102801c06203403a1a489000000181c0d0350018000030060401801d401c2411803602c6401c0d82c040440442c205450001a00c0040000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 364509739 1250 364508489 364508503
    0xa0c051005090327130b0a080609070e06041506080118050606030c070c0302060307050408060c0c1e0c03060c0304032709090602070812010513050403050a03050603030d0e010e010b010908 82
    0x4200b0313802c0d0031801c5030700d0043d01c10004a60141c00002c00406074402d040f0540103885601c0d401c1d5010102d56589000b40c1d40c5030034068031200b01c00d0300021010800c8100b1000d800c1c0e04140000c100282080486040111941807503010304045150740c00100701c6c0c5041d43c1c000030140074941c0f50600851400c400000e400d84002081f0344a100400704540f001e00100e080b402c005142d01510843d0349007000c0340e000d0300e160810f10030500c051203401c0c00686540018400d5480344900f01000740700714004c00303500c001d10f150443c4030461548075006981102d070390104822f0380540c80d0380700499960b0509050083c18440c10000000040308411805800c082c006180601218020940041c0c0080300d80383c04030292181c00806800200085440c1600c002e540407182c0c103c55007120300340001c05000d0702035003d5800440300503010a1050040206040c002d8001d258040300c01000da03450b104841c1c2200c400c85003a4a40200d4a13952503a85140303850007403140500c80309090810150a40c603080d40240e82c2d2074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 364510989 1250 364509739 364509757
    0x708120a02010906050906100603020720060d1a01110606090c0a1404170f0d050d021b03130f051801090b01020a12050c0d0309050d0e13020a0c0510050903 68
    0xc211118034403c0d0b104008031030307200c1418070039400d084100641c0d4160548560070964402400015003900900c00c4502d800c2e403000c0096082a0205c1c4d03a800d001080d44c1040707030005000c201103600c100c2140f1a15105d042000d89070f601c1d11644200042c440000e5105001d040cce40b05005016107aa030703070615180e10000798980e0542d208001c0400320382510f00c82c0c0c854000c00f00d011501040f0680380900b001e008030345142c1121841c4204031030b03035603451010b04800030208408004809100e0982d40050001e031014641c2c1c418104070035412103107554008400300d614144641401c0c0b09280c210400d041c01014201c82c417410360300c007418030b03915094818807404400642e075a1400310164004d0245c2404160440e64a01e02a071805c0e9001d0700a0340042d41444840c0501034100b000d450217440b070a51840d4003d00100b510840718507080d29400b1580c1b50059010744209640f82c0030030024002010400b0aa541e02107200390b5901d011392820110810f00a10355081408021108000105840e0980 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 364512239 1250 364510989 364511023
    0x3070e22050f1909230a02031510060e0604030c0315050901050601021b03151306200702040c03060e01121118060d08070206040603050f1510140d020706060e07020708 73
    0x4003ca2800e04c03120642e600d14078440141c551000c1c512045c01150300e1003000d00035425500906215401d22042d040c08980004588131040c00502c900b034403034061a80354041c090300c0b140c030f856141d8a60003100e0b80664011104050070302c00a800015060107001d400100b080028002824038600107901d4541401040704855640740c03051380f187c1c0c1e0800c4103400043c1e0780c40c40600f0600340352103a0030180e820141c081d50503d080450b0840c2c10329000b83c90f18080082103078514141811b80e4200400391481c448580c0805403902ea000c2196a0014000350080030488071040b2166034918100141c1e000001603188103411a401c0070518500410388103500290884400c81401c0440c030781011a030042540180d0003500c00300b00403501a40641c45240104000c05c0808142c1d034805030107242c03082030500085d801c890207aa168194a01401008405402c540c1001b400c01c81c0800711501243c100c0341c2d00b40d44840d111402048a0741000c030210350041114070160000030706249500f0350b50140020007600322 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 364513489 1250 364512239 364512251
    0xa080d0318120f090602061009051e0907061404050d060c050415080105041413120309200108100308040b180613030b131703070e22050f19 61
    0x1100c5003820310700110b035000b16000c1020030280002010040b090002c00003040b551000403961900005405114488102c1c000465508214000d07025100260070b040c04100e03e02c85c4072411001d003904640c030a41202000340b414034500740d0000c1046500000004100100700710920940e190600c00d440c2160b0000000324070300c811401c0403190303803003260700c40c0d80c01c1001600250112580100c2d481c0c100d8600f1101402000c4079403207002e84c10201920412045081480d06100003003035541022507441c1e0a04000a218900e030300c0c0d003c0110443c4406411000c8903c04c109025030704004069084019140f0102c42c450650f070351001c6c0c603c142c0c06501d00840b8045001668240f580c10039120558025000948030b05480b14201140500ea0100301c46201040300040c0c46071001c0e1005244003600f10030390411102c1d00b482084601e07032024106a080121400d901d107100d45400c07004405599000c00690450784068113818100d42001d0240c41d00803c0140034000d14006400700740018441c1010b0001d02 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 364514739 1250 364513489 364513511
    0xa05060a090f0621020a1d0102010b0a08100614010512060609040906050411040e07061112070311100212070807030e0627010203010303021e07091104140a080d03 71
    0x5501c03650b01452144065500c0480c4440d4001a07541c540e100c580b280c00418007241003c6002d80c01203078490800540010584600134160542c8260101418000010994030b2000441c2403e1610f410100095000300700d218100a80da1199000030001d810210001031130b0540000e26030b111340190a107005c0b07030101c0071590741c2e500c0d40e00300c0c2c1c0c0554000b401080107090602d0000040c0078100c0b401d0b1114040170006504600f4503000b000c0d5000c0070000070f01005414510140e424003590b54680c00c1c64070402000001002001004040681c0285c40e0240c0402c00c01c1c0c030051400a61100001d40e41e80188030340138001881c1c6286a400101c141001c6849039600c1c5000c038010904a1a4a07000d4880c100038400498000040040b000303a101d107034801480402031046003070340300c00c2c840200103a005119191044808455a156002c0c440e001d56401c41c1c1d54000c0d13502691580c0d18007102c04070002608014070b6141c0d805c6600c1e0303154295200c01c0394500e4240030603185d00355848071505140c0c8032054190 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 364515989 1250 364514739 364514747
    0xf07050312071b0906080105060409030813210e10020703050607030245010503061c051515130c02060c130e01030803010f0e0103050a03050d0b120a021306050a05060a 73
    0xe504640c10f4034102ca240e5aa2107400050131841c441c1c0c50007035180030082800303414240621081150192201e214644607042e00341c0c0585c0980c0c0c3c00340d414503409448034441904100d0072102c036110f10350b41c591030307000c46504010705014032420350410b5600009080001803000b10740355074403040700d0030016102c0303c908407000c0109070030a030751001c0050070301c1941880035022400180f0000911407500c0040078400b0041d19944025604c455104020b00a0403040c040c0111022031502e10880a072000400141000b8010401c00ea031a402004501c0c00500d0707550409c01e000c0549040008014090100351040194440d440a0450710408034005010a0103540c0c1a5003507000789594a41600700d90f03940c1c2864040c03034000703000d502c0c80345040c42c0c0005a203211690100b81661b80000150420750090f580c2a90f25611225088400f00d4546034020741a58640007906000201310014101c1c02e50385204010303d4040325100e04610514010051285440f9903042d0401e480c030035140c20b90740e03848a8505a13 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 364517239 1250 364515989 364516013
    0x5010c052802030d02011d0109050705310905010b040b0d0303241409090c0105030c0306190306050610020f15060301090c06110d0201180206071103010218030f0705031207 75
    0x10390584030799004403e01942c150700003048599003a4411210301f9641e20500d00360f80d00b440d4003400d184d0200000b4400341c50000410f04c040080e02c8580485a246041450300c0c0104841030340340000d07a94180070003880ba080c040e0342c015520482d803c021081081000980341e00b9209406800c00d1784d540c0d201d0084c10007241c002a8145840580031181c00c0c1c0d12040c8100c1c020004071501d004000c103402040210800280320380e0100c105849040c15943c07441c108a01e00c1d08001d00d1a80d1126140c000003000303020704a85031020b50701402000c08c0318640360b1300740125441c2e030401017811540120005c1d03468210118030f20322440c0d40450481c40c4c0707843d9580040d01401d070424010b0241c50b400b4100241d0960000f00d6000340c03802c510705a4501208451003070b4200c4a842011480000c0c400000e50010310f044801400018811b6981503011114640801e08a8014403003401c0c0300341c207940300160030349000c120324028003012600a00c816800c0c180860348410780c00070100d489850120300c640822020402031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 364518489 1250 364517239 364517243
    0x10e060307170a061503031e0e06040e07180506041202030f1c08070c0302120306130504080d0b060c0c090702100c0f140306010212180405041b05010c0528 68
    0x78203844030b112070f0385850212070202c50042c54900f00d02c000403e0151100202c0c0e400d40c9130318401220400302e81c82e11100c203013061020004114248602552241c0143c0701400c0111074080151400600c00340c80c81c1c1030100380900c002011082040250349001c100c5042d134a5000c0300180c521f600d440440d2410181e0000080c29000d21020001540c50340d01c5c150041c1c49190b500ca0410303464109060b103050410044c040e00507004030285000030161b100086400440180c0411070410301003203d40d00721001550101c03400640000c0700d00e001066401040e010788421900d06150011040d90303260380d2500d08001c80e0145184000040f031803402480900c0b0151411a418400480d2084004110702c1e4558800e0000c24120300d1000e40c1ca10580082d24480c1301c1c1a002000784049071544824071740c001c0c5070304070f41d42c10715030889240f661202e01035030380154481c0200c41d02003a4951610102d04405821160402900320500f002041c8001030041c920f04611810034040624428488002d103185600 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 364519739 1250 364518489 364518509
    0x30c051201080d140c0604061802060a02100b0a0f150c05031303020907081608100f0e16022406030703140f01051506071401021201080d0806030c09010e060307 70
    0x40c500740102c0c00949003d9242e5800d02c400c210140070310740078003a5000340030055000c42c0000b03000411071b0f406140d1a950340300024903140100e500240155201565010060b000814621012130300d50094030012a4101c50007030000e810080442d00c1c5080b1072107071100e01c0d9072850305004114043d400854a680d0800283d0b81d44000c410740d25040c100080c40202d020303121020004442602c504407035800b510701c20000c0781000320031001c2154503200141c05010244e00c9003c1c006200c6000c80300d00700c018150030056240c1450b01420588840343c50030002c00c15034016081c064002290041c1c2d00301c074100c9140c840c44050311004e010034545511504020032904079252442c0501e0710001d102d1500400102c02844140e88400172103000b42024a02d55401c880140b18450000c0d1740d900c80704940c0c40607000014280b180d03150300310030008400ea0000026800c40b4022407441544180e1003603100364140c0c024002c12a030f940104a0080d41486074000300b41c0c0720408500c0954082c48140010581508 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 364520989 1250 364519739 364519741
    0xf11310e0106080d080c030f011202040f060f060917030901081b030f150a080c0d110901060512010801020301120f110d0c15080c1b0a0506040f0317040c06030c0512 72
    0x18401d90b81d1001001c1c60300810070704170000b508503031418103c03031107060018082841641384c00307105080108006400c9a005031144109459920180300e01001030000d5802c2251441c64488044c0103070314540c01503051448038014140c1104000130440e4103d9000f0b03c0c0c001100e80d51309240090420804044940712180081402061000c0c024030b107000d451465030a00d4400204800c100d5188407502c10b00c0040d030003450001c0082e103032600d403050071a4000c200301c0d43c3c90300f0300b00000381c0200c000f608140d000c0f4201141c0107600040b0100c50501418104d0002c43c0f03154103110b003a0340314500c0648000e01b0389c0b00000102040250340d01c440c6070041c5001e005120390119600c3c4c54243d151842c000c085032110100544220b151140e99914000c031036814885250074803840c1209448003841c403500d402880341006010006804110040c8640c0c0a00d447c0c60041d140c6150040070085851000104100031340284404103110800b460220b401a05000079002039044040da002d001d008001c0c0341100b8044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 364522239 1250 364520989 364520999
    0xa140c062e060207171c03020901030e0307050304140901080606060a2601060f020d0504050d051c08060405010501030501033507060b241909030206070f11310e0106 72
    0xb5000301655081d10607002602c2c10110890743c0c13601021451b038050a500040c43d8071300d07806540140310903c4180350114400012104240c07655018800807640c583c4009410410341341e013032400d02c0314254120b0f042000b0f541752241850b690340e800b802e034502c030303400c0052400001b60284000c14040042c882e441c44116803030b03200c50740c4030740c00c2441110046140b641c1507444651020811611042942d2119401c003410716040c001e00c405403a50883e10b900c180fa501074040c070f92266100d100c0c0c0b05581c4c0c03240221301d400c07800d00c0b007500d0040e4085c0d0305040c207080c0184001020100074036160202606020358030454188200b081c2d440c0031405101385240042c00758188412a084a03200c841c0c29030702c0007004403440e0b100311080813545425400340c2509000300116500c140d0b0b10100700da0401e00c2c10000703403038681c0c001402d1613200007401c4032441c2130204110104200c1407200c00d5400030031100d800000344443c1c04480b9412000b400035820408103580c034070034100c041d4010040f00d1141802006559120 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 364523489 1250 364522239 364522243
    0x20312070305060102060609010b0a110705030312010303090f0510051804051501020105100e0c070510110309190302120c0a1203050118060f05042f0a140c062e0602 72
    0x6030f410a00501401e00000c1040c145480c1c024101c40031495020325018002004a84207031141c2842e41d4540900340d400202c6540406c080e28100c40705440746200c80d455440c01a1802819901c00d4500c51074480b81044195105c80010032880a1420290713911500040310b5500000001c100a85c0240707000203121206805540003801c0d80400c0e0000c0120351a00d590350710003036a5030f202c0d04203080d07201000128100b08a801500641e407164040780c840505091780181036a00040c68050b039100c4c00702c1080960001002000460000300351480c440141c0398030000d40300e40c003006149140c1000000c414403480c000300494a000703a08050307001002c5a404034010b01400d020301c0303192100142c0107020110000c1520420003107402c2c0440d00008940f0740303418403010703200c080101010481c400c40640a075010041e0004c4160086455055a0301c0c100345018050620315004006a082d0601002204080000d10a03070402c084060500000600741001c40f004048217080402250182c0b0001600d43d0300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 364524739 1250 364523489 364523491
    0x9030406030c0c11060708040e01140f060a0e190515130e220303180c15091d0406060510020a0302010c0e03210906070516050118030b07020312070305 66
    0x40d90341c18072924010303032402c8910f9403914101525250341400c0b0b400a40ca4401c00505200f441170300c541c0c0c1000d58a03041503070140c1c002da001102c1c00da1500e04100480c038000c036120510060840d5003508010400100402070016000700794060548200b200190f440a04000030040200404050760a25580d001c085607820040f9000303c1c8840d00407001c1010000340700003070b03c1001075400200395a0410300312091008022035090f0140b50303a88074080c0c0114500c1c20000b20190140740c800d04000e00d0701d0038001c071a0034402001410411440c400380907841840301c020704207038502c068a24035925030740dd00c403004000310780c01254800c0c854041ea5000310b4001c540800918007940003044042c028081c02d662003428030000356230503000700348402406a00ca6040001c24488290001c3c1007409202c040344184e0300a02d000d80c0c656001502070781c0104803003444a4003508081c600303210404011010501d480c540750100030003a100c0000000c10052007001981e100c58201c907052449420300072000340c01800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 364525989 1250 364524739 364524749
    0x3011808070618020d110a0914060102100b010507020d060209031f110306090601051e03010b0c070b09060f07051002030406050f0633040e150a09090b0c03150306090304 74
    0x300b040d40d001c8203482c00103d545640b07900540f640941050a0b911030303e003440303120025a1300c0f45000c400400d152205102d2100d0004a82d4000d803054102400068908030284000303409140c10b01d410b010150340d0001c01d0342d1029074103a0340d152005c51740e45881800b900074651001d805102d50117081480d0400b01103020b1035034502c01e80c04c010342c4d05c6000401c0c070603120850350745030080c6020340030403642d51045c0000c3c1540da5011000380c209201030003960351950300a0340580c81c80c1c140450201e440b460140400c00080601405c407629080c5d081c1c01040b0301e80140b005a020801002c12241c06005c0e040c004103002840f400811540e0b403405252810042c0400e413001d41700c3ea03017500c00281c51410080c003008905848c00c98440e803200703404a40be03840d0010403850966558010b00001512100300b26159002d803200c0c0c40d81c80500d150703032f07418032607604d101d9070107043d80c07074241007c9101040e400310050340c0001c144c120705562680c0301d0418421007001018240d13010301c50a0704002000384040b01a2056403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 364527239 1250 364525989 364525991
    0x408030a0c031d1809011407110106061b080703090905010b0d0506030313150c06020c060f0603191e1203200708040918050613030f030c0518030118080706 68
    0x8420b10f01240d1100f400202c995400c016114200031041e040e11159550105e14080040344610701d8046043e0300d0442a14004041880010000303d00d890070301602029003402d2412203d140424900c02e00111070140c009403000e20006074200a01d441007044101418414106010700d5035201c0e00f4500580c03010410b2003c0914102c0810b20901e070110881d514080c2c030861884242e801e00e402c40c8070603001e6192030f0303040c842842c800c2c40024189001400c00010080003400d240c1c90f2182c0085099400103042500c26000440d00c206042003e440605d160741d08003d00801840105000101c0302c00001006404000c0d015110340030a540340d044400e100350115440441c0e07400d42c918100d0b590040d8100200444418001030000c1491035001414020030a0021002024941c942c2c900303003079003514000c144503005030614050541002100c400a0010b140130021301c5000c2400820034040d403210440356041c0c0c6407100c103ca079825000114610912114140184c450386812025940305501c00c032002d07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 364528489 1250 364527239 364527257
    0x8030103051c0f0f03060503010c110c0102060c0a260a090c08071208090409171305010804120e0f03060a02040603051308040e040c03080412060f15060c0203030408030a0c03 76
    0xb5510325034100050388441d44542801e40c9480c1401c0d102c2c0d145100180041603940d03400000c3c0d5607024001c8000d64607440d118540ba00e4900c02d4043d041c01d240303403141415503200d101840410305075072040f203804040518043d42048022603040d40c41c4000f45a210944e04001801e21140740c05aa0017004510310074030b408044540e0312000d0545510507442140311501101040f20046000d100c010854140000c00c0001c507404984d40e5220901d111180c00005800041180c5400b05440305d1031001030030b001d00300901785103003c1d40c13402c028008181d0b00c0c0040062102e00c160090700d40c034042d4120310000400780d81091030700300801d000a4100340301c1e010002e420b01002c0b5443d508101000355421707421142c024605803c019980070000f402030000c42c1c00000081d00080455445030280c00980700d00b400440408209042800585050b0340a40984600d0032000d280c850488000c0c000440f070807400d181c00c1c98800d5000003030450290358442c10240c00000303000094940e10007400000b070382c81303a2192200707 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 364529739 1250 364528489 364528513
    0x60103030c38061e1e1009081014010504020d090515060307060804080a030b03070305030c030306094804090506010221030606160f2609220e0601030803010305 70
    0x20b8400c8185122180c4030200801c00703905c3c00c00f0700b48450107500c2d01042e40300500484021030201d02c4850b40b4100019140d017401d0100507420301141441e04540401401a2540c1d0240300d4442c050600c0340c0340c42254000f40402c600da0080d0410843c49801c2401d80380d4280c00c007080c00e04000380c02c031911032081c003645101040d2540100306580c000d45e0840042420107504050517030003050101c0b0740c2540342c401d5410000c00511304100503d907a1803584080e41c0c583c101a41400345810029080042d250f40314025006195010394500f17518400766005102d0f039100d100c170f5000020b005d44042100c000310008010a81142c40d4020601400c001c0c0d00f15440401007041c20070407541145c0c42628503038000c101103540c925105c000b03007040144861010070f4071407507079031551244e98420504856001c012a2000c1c22442c0c800d036070780040c4204130b02092a01e210500040e40c0340d030042c803075044ac40c40400754006000382031750f1040300030101c00401c65007556103d040041c400c0d042403108840b0303442443c0c11680c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 364530989 1250 364529739 364529749
    0x306010309112809022a010905070303120c1b0b07090f0f0503060601020d0504090902131b11070501090e0a020d110c010b0a06080408030a0e011505010210020705060103030c3806 78
    0x1900c404a40f498034490032145680038400703e00c54004555925400c2c0c00010409c1840288029840303901c868401c021143d9052084d0343c003955200c803e01954840b402e50300500810070800c0d040d0b0010186045035207080d001c2d07a01d5003140d003204600212440d4041a0070800c1058501524401c500311007059071000e004982e1900305601e95000100280810000c00403650440004944020808034040d11100b42c681c0849401100a504001003d54046031160708170795810784030000c0300003400f0310b0340c148000078118005510074040211488000902d2461a40d81550400c1c03881c2031007440401110041494a500101d1000710a54a03020881103149415070010382181c410b0b440760074250b40c40c1e03111a4125080100f5450a6548515403107010701d0003031007441080148604d04441c000d06110009103841410343d20503b18901c10080403000c601c0c0040d401c2d0460340d151604c0611440f80c2d20302000d802107400145201440703241305408041d046c0340000c0d9080280111082c00725900e81c3c04000c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 364532239 1250 364530989 364530997
    0x90d05010f06080c0f0d0206040506070c03082a0a051f02130602030903120702030604030807051308160504060e0a09141203011d06100f0c02091f0602070b030601030911280902 77
    0x392300c1407040004118a0400c00301501006008111118907140c5da5140c50006034840031500320003000d00211307104880e450810300760600300c4d140010a0462155664036541d455412580040018482000062030145030100d52043c2c403403064000800e0740c0e40304040d581b904446074261084c014007015200c5204034000f80d03905150000c000745001c2c4c0315034a069580a0f00600070741c04001d030801c04111000c40300d81a10780103020440040c61142e0304400044010700858101d24403403070074140104404140700b80596000f80c02d09100040c041010b00e0708007199000c00011000038007421400100c83d684000c0914100c4404001006150019a0b8113143c00c6138216102644180116450103c3c50300c20003945890080f107050201d29000650001210404221038040c00207100340d2081c00104c01c00100380c4020803503400205611424400d5403510360000a00c6281096035465a030001d004040d1041c004101024204181c07000c0300ea0301000d10341440c146080e003a154964800509842d21744215 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 364533489 1250 364532239 364532243
    0x13050d050a0f020117130519020d060b030304031202030a08060a181e021215010f08010b0a05040e090a02030d11191a16030609060308090d05010f06080c0f0d 69
    0x3618045086a03103804101000102c1a8100688030301101c180f0400c100ca880e00883c015030b5240300802c81450308070300c1d144840c07440b25100c3d800b401401c801621b818a080031065885000850404101130200b0701d14001c503071000d80281c0c9038095120300e480c0c021005004503d8070f03580fa81a19981d28003400f2200246100b661035100302c82d03540b5910000079500402c03600c03811100c0d1604041c854901d903c160380018180302c1c03045061b0418040c020341c00c0303a44002154420f00f828500750030901c401500c8480140b06450008100190301e1034100d1188049402800050803c40e0f05420700d41c4260360b484060385000c074041d1048035100034001d0b0154100740c2a082800e03004104901c04100210026240110f040f00c2c0903014900c1042941c3d0103180880c4140e0303180c450b1010a80380620700505440d5268420f103521468010284046842901110311603030041c0d41582c22006540741003401070001c45c21301d1482610f0050701003100e042c04a846519141c0440711202c0210180c4100200c0030707800100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 364534739 1250 364533489 364533493
    0x1e0506010c021e04112b050c0403080c150f0108061b0412020114070602071a01080309010507210905010921060e12030705070209090303060915190b13050d05 69
    0xc007021828103210543c0100000d040824403402d96064038081e40c10142c07140c040798071071526498143d441c42c841080d038a0304c0d024080c0b295041401040c8542d01c901d010207040b10380002020303a0b00c400300700b010043c030741e034905031210072407903d0f4600f407034000b100380240d110320b01800011030303141003d030802034890002c2900064902841c100b022484e540041104905000700c0f00081c401c0b01d01c0b4027000c0c06c1d1043c05214007681e622a640b624007000301107020200c0c500d01c00000180035110000040c0d0304000c00a0803c0d60762650306042040e10f2603c1107480c000f41e4202d031104880c81300e80c401000b8003150307401e032503200c545c544406000c5d107150484c07507240540c504020040701c04205240c10200d00c0381c0155003561500b980300d45142000358011908d030000708400040b1a0114103000320035a03408100794024500758285040000c0c0c034021b01600207071401c440b0b4034918000d5901c036080d01402080b0250150340300350b41e500310032041d50015907400c2014448184006100d05010750590102e65001c40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 364535989 1250 364534739 364534759
    0x30a0f0c0308150f030a050c030d0224070e120109060e03040522110a0801260a0609060b0a0801050609090a0807030f0e060c0a050c0406060e0f030307061e0506010c02 73
    0x112603609000d03105201e13a0700000c03404400c816903c0038000e01c5000d50240015002d100b02c2c10b014140341502e0b581e00201107500061916500c0c2d0350000901038928248244282251a03851085944d40f000d006d8041d0301218070f6000b05540401507004601d03070381c0314100c14840c445003502480c3d120301951107650341103260044030040c601034810034604541411038000484041e101e02d841101d422811591020a0210b40140009440c80711041d00301070007017084019400b10780490940392180220003d0a10340c42c1d88603d020403006401070050341c1c40290020441668402e503460107850f090352014040e01d203180201c0c10b94440411205101604196520f150020a960444004c640b12080e0002c10001c1e0b481b820780d5a070b604000b030a02201010042c520f01c0e0090601030f0500705000d03486441503203442c508000c80f5800c0b080c11080300e407084a040c00c2c0e030000c120100341540300c0e550004021524000000c900d200304012503c0c40001c8801c03080225613590700041d10940608003003c0e50141c4141 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 364537239 1250 364535989 364536001
    0x506060402041d0603030c01020a081b0304031d130c02030a030f050603030f0f04030611030726011a0c01050a060f090c200f0604060f180f02060a020703080705030a0f0c0308 76
    0x43e65032030f080080a0101c904e0150040126400ca802c503103c144002100c0d101031018049400c40b402581e10301003902d40d481c50909542c0036003940b5544250441010303d28000c8a410350b100c0196400a54800b40140700c20244002c00035140d900c00d030282c9000c07030b140c00708102d645500c41c81a14403501001c2e00039844c2c200545003415290f0042181040006420480440068a81e0103409200021070045540700d050501019100071021408030000c0e448107000da00c80c02c03140082407811216210700c42c00001c0c00702035150300f00d80714585400400d5802c04081c0100075800f940600e0031561944800040b081c1c989c3e004d64140d614800a101c0014041c0088001c510b002d0001c2000030020381c000c0340d00200d1440c190078205282100d0940d030080c2e4407940116440110b006c2c10403200048405031980945640e80d03422440c039079043c0a402044049402201c0600030000000695000040300391100c00e80c0c5401b556070391249125000154a441000c1e984078021404004400e51545030604142c5d41c1b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 364538489 1250 364537239 364537289
    0x20f0f1201090302013615140c0c0d0807050307080a0605100f0e1c060f1814010b040c1d040b060d020d0c020a0201020d03050702030d0216050606040204 67
    0x9845216440305800381494180142441003240c0c05100e50000704100061082604500d030520180c0002201e1148215000c003211604a400850744107404046401203400090b004112000800c0600000c0d01e040c045d0656186026014444e52241110644042c29204441244040c4ca80c04041417051010600c258050865181c7c460088000020303403aa0b20b10005518000d0600f007000483c6480342940504e60703204900807803034002511100c44904d0000080701884e0341240024210350740e94480d961a440c440d0300030401c144550703000f4825910080c140000c0a102d0301e07401440940c07809900c400c40717043c039000740c100c1502d05468110300e01c40c004003480780c1d04021a0745591f011780d481088100590b9100d028100d03801420303000580b600e0b03507801c410049441440c104002d552011704608010b0780e00260a2944140d645804206038441d0601689140181a10300c0301c01d03070010441d80281c0705030100e01c6180354007900031501c0350307203508050204900c154002c2488107660354122a035a003082c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 364539739 1250 364538489 364538509
    0x50d0903051e090103060b2b0b1210050f010e0105040f0908031008011a0616031707080415060602032706131703030903071403070203011b140403020f 66
    0xe0524601d8280c0103003090030a285280382d028120100454008180d59051041741b01170040122031034908201c85000c01d000f841005e1964031032032442814405006495040001207000180550050f0100411519110100081c10b58a40351602000500c3c0140107080c0724102e90205d25086c145074203081c24000074088810380e055145031030303102180006034510f00442c40782901c00c0c0038106043c00c4c078101c182501c42d81e0400300b6406101c41034504003070340c0305401c03240b89042849400c1c1e1000900c1c9011f48020110800e04101c001241c002c20200300e401c100c015104610900225070060345045c420000c80b4214091040186d1040c84104030204a000182a902c50181002c10b019038a000015815501074034003122064401d00e402c21410078090b04007c1c41458030342c051415454440380c165502e01070203c0240115041c001c1c030720701c10b07078080c8103d0b9942c03038001e03000b40120784007028401d40081000f4007140001c3c07240c800ca240102d03016004e81e02520b50040501c422255158100100104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 364540989 1250 364539739 364539743
    0x140325050312010e01090f1401260f011d0d02070b03090717010902011b081c021605010c020610030f0b06030115030302010501140411070b180316021f050d09 69
    0x100402c480441c108580c2c00c010700a149000884e40300d5810036228405451001011104040c20900c200c11000c07640c0710028103440490804078640440109140403040d41c0310a0b040d41e501400c006082c0103401904500c00c65200007554031640710b00c1d40780d8a81e6034103440d00c1c9500140c01030710041c86001c44460003541c0281120045810090300e500c2d205004140d091031150f41a952402401c0c110750700418081c804990000b1090354080c5103032161662841410b8902220b0760a4010b101c00d11846603050300c07031450f03800f000d2800480051501c036000740600141c506c0540708010005880381500401e0301c041d80d40c0448000c000011070754640800e494050400c075451354948007400c0c01c5200705888440218000e50010401d9490b180c000c0805100c075042c00303409070713080046840c04c1503101401c446000b5848031003154075659502040c2800790301c20700b0840311400300095421000e040152000f1440c1d000310350a207002d150862815010035052602803010581c2070000e940301030b41641c400b4a03214 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 364542239 1250 364540989 364540993
    0xe060105090d0c211703010b19021203040318050f0f010503090703171804060f0e13082106191e0b0307050c010b01020c1c1a01030c0314032505 63
    0x107480d2000c00381d002d401d20742e500c1640e031000e60b440c070103125840503949100e25940003170f00c0c07030344d410090107903414890316a000340c0600305002c002a115208205442450300c0c500d10701c2da103a041c5840d0007011100c1700541d960280103c22004205072410000007050340300001d10f9403034200b404000640b06c581005059070114068038a000000c02c2020181e9140fa4002450b62540c6805400c0c10b450b01c40b56a08620b4001c0346008002e01c4200d8072924810140c604215a03800342d65948412000ca042150000428002d000b10300481024403000b034903c800404070410001540d14501440001d6040705a00a1900403031901041f00c5098010280e00ba02041c90840c0030710790711048910300541c01980c2d004001280000c80c42c900c604d0038440c0300c04082c402d10142071030b036040d400094100c400c00030200c44101d8800c0c02c403100b08050340805207160034461490b0310b0300e0740e07481c00c05000c011191b1000741d039015018450100c0743d40006c403c85610091005440e8420b45240307480c4210441300d450b00b11218 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 364543489 1250 364542239 364542263
    0x106031802100302130603090c050d0501020d0c0f0f02060c030f04020d061b08070809211c061a030115030c0507050105150f030f03191b06150e060105090d 68
    0x258442d6142601d407482181c4000d0703526080303041161410501030b44448101440c0150281c00649215400c504940040301c981104003010700b8181e0091103408403240800d8030b4150207140181d08860065809909503c400b95420110403060307881e8917003101c0c00710038031400708000703a405000d8021460300540040e041c225024525521103084600c1815142c90b400344c803040c1c0341112603016500b59071011041c60a01e01e68100703820029070366440002c41c5c215218001180c03001019403d429541d40d9118000c01c0c64100b595648000020003081c000e1800010300c4a10040f000c40c40d003000c582c12101c02e10407440951154110450090180a05507410444104040303030101d0800d01809018004884c000c0600c40c0d10702003040240300c10461004d0280d0024280b10368041804010703904c59201e44a00002e80c2201404210360b10181080004007040d078446125041c40119031161120300c140c1b0b04000e07006912500c126825a2003268120700184040240f04000d04056030302282c680c2c4103036641086 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 364544739 1250 364543489 364543493
    0xa08070602090a0909061503030c020405061c2627031e0c0909011107030e061303030225030c06050d060b0a0507051902030606090711030f041d060901060318 69
    0x2e40300f40d98454042651601e0f02c2d01d041c0440e42c0711f0480d950450f0030749400701d645182d41c00f4005429808001c1d102d035648000003849502c0d01046e800c80e8000d41c2c80d03110003c10f010f241440203600250340b144400802040c07001c2c4048148000c840e5411100c16444400c0030440f031032442d06042090b88036826015500080d41c00c03e20360385520000a45060150031220511414414110030040c00b040b00c0b603050804200070940ca00c0d084801190b0145081160490b06402141d80c921800f14100f8150068040c000b0902d54045501001d0f2441e00140206000401044c00e41d034100303601020b041149900000c100c00c3d8007950040c841d210300345002103056079664140e81d00640000b511741c4040350000808000300300051101d1901c8003500c07080c210020105030003296840d100245118040c090800c04500524000c2c104041800c0384901100e82d203001d01c0071a00702035040391141c1c8400015094903200c60201c80e8090600c14900a852048a40e10b845e01c214003410401c022043c60820010f94540 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 364545989 1250 364544739 364544749
    0x180102030a02070209060a03020f10091707080f0f0601090c020c040f0c031104080601060f050f1603090611060c0f0403140d0809060c030103030509060405042c01020c0a0807060209 79
    0x1100300c1400600507103901d101c0c01171240131790004000a1054040d4441800181d603107008070350403090140e94130042c1006981040c1e400407415084001b68201508003503162000015155007036130801c0041d59200313480d00120a554100390000740320217030000740051001d00c50303a0b0b00c1081d50089501c111080455038401240840301c403504000c400036260125032241c0d40c0c040c0601000e04440000c030030f14061030045640d0315464180601c1c41000540d29a041440e0300c24419140d4111590800703a075544884901001c07004075004046011031064000054031902a002c450041e44000003e05040e503505500441151f100301c1d22803100420178040400031440460b11046c40d000050003e10328aa8400c10280800303600400541c5c00340d1241040101003562201541d0440c0d41c1824059120303449440001e50a0050b030b0070568016180101c0c168034417004004100e0a1002840301c02c01e6001031850f95800d03480f4141800c18558408003841d4001205440108a00b070702403a401030a001c04680003031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 364547239 1250 364545989 364545991
    0x5060402091b03070207080d0e031002030402030a02190e0609041a040c09090302150a02040807300b042114070c030501020c060403020114101223100609110f0318010203 74
    0x4c00140e11041003400301c4081001130855106840c24101c0c0b025880000113039a812408602d2030081d46c01002007021500c2c20400100f00650042c04003056684088038584148441e11481961030700040120f000750800c02d03402c500503034000c1050307045140390f110f9212030500086d0085030300b100d09940000e10444244901c03078407584030b41d010781380daa480314404c1d9003c0040070342403c06032441000200000c0c1c00014503401185c0c03140c95450b0107503013032022030019041503284650007510b0405c8546e04121400304d0003032285100b00b010381c0200c55040b9a0806007800d800204011030700704452021013014650281445034071408062040c03940b69519282079030403008003808a80d0007601070008140d028010340741034040281d610001031a108044091a07141403040070b40b6910205140d2050003500c040c050030b00301d02050ba00030304100f12030001d56030b940c00e82c0c0c8000c0400d00c2c000c40032a2580c828014013641c1c2c060302030349034180400500580044e9101070b000b15180c0391500c1c20196544004e0000d5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 364548489 1250 364547239 364547251
    0x30c0408010501050604150f0302091c051b0f061b0115030203060a1b050c010209040e0d110a0b070809100e03092701180902060315030106060c05060402091b03 70
    0x464445160034034a900707551041e04031a01c60002400140280c410880701202000c485d0b15114410400001080d40203100c0e4117815504071a031500401c4000813446c03070443c1c04a100b0340031645090169680c0b900613012001c2919406806940d90b072145261030b034003800841440340903010200c000c5003501030071960402c807059215000440100f05500d02404810782c0580007103001c0c082c0352010740d80000e0520401c0f6004080c05004691004240400d41c15a5142d11010b0310410844c0324804c40165189040e40441000034980308045824801c08251901800e1748843c00787e2598480340800d40e041003001302003041d04d208a400120520b6204c0c011049140c001d0300103147d880600034180314103205100d00313003003420500341080c0c201481000580c0b0f04582403081058035008400d0f0301003000d4400c1c07440180d07108802209210b00080d861041e4075008034203c00800245a503140c080d58071541188010f461500721800050250078070340b1205601003c41001f458142c03d07140f8103010030750010307144 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 364549739 1250 364548489 364548511
    0x1002130b16020102060105010c0f0b0c0403240b0d03020a060207060b1306080c06070b04030c02130c0e031b0a03060e0705090c091002060613110c0307050a0c150c0b041703 75
    0x42006550301031117681d0141100b8601010441078a0b103410300d00c511149001015800ba64002039041e004100545010359401000d4812264000c1c0e100c0c51251002c01c1c42c0100f0600d402c43c1c580e024600044003041207941038020b0314404540307440d000d0094100c03038825901e040e220460b98280c2e40d25a55100c44d4500c1c44180098181e0404449902d0085e01c446036030300821013000480041415603007910342c01070349494400c2c01e003102c910106100002158040680504011400b11005d8101420881486c401d40841c0d2854041070b001602d922003410078587c100300c10740b03000d10100300d185d04030f40c0d030300f413440c60880310b80c4d60355400810320911003101e40342408000801e2251491421244a0040d07640b035100400d520b00700031000924144402e2483c0d280140c0e40c5008070000c1c2c200c80240d5580755a0442602d48038070190510341d4550410305003c481c40520076101050b42c040030b840103c50380069036100680101560365803421804041c00c103540e0800d444041805081010004501c04c1c03039000d00b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 364550989 1250 364549739 364549777
    0xf030702010605010923010c0b10080f01060f0e07030207020907080619050a1203020f0708060f07020f07060c061e021b0708030f07020a08120424021002130b 69
    0x20080c00c6642c1e40e0000350410610302c1041101400100590401056081c09010340341065001138911018041c402072074000f02d1010452610050300208048841040a407141108880212801c84080d40034914030750300c902c40c1c1800b155043c18081d9a014a45080042c43d01c1350740c0e000030f13060100032030700740300050075440c10420355082540c01002181480c0e00d920312014202400960010110300031f030507051080382006d4080c948208683c90130000b8200607501c0c0c85407600102900c680d0203e5810301c22000c81c80105100b0740c8001600c948611850000c1c00074141412812100700d810000182c400540f580e00c80d505456030541801c0d0702c00381c00c0f000140c7d65440514407001d190304041146c58a900517610402032100301104880106600c4108540d44150a00c001024074205402c44075081c4602c0b9099410440b0758001001031b5001e00400355004040c4110780d0440e550042c0503000180c000013030350074803404a90003401030705040320b0351084001d4076989030030156004048003060303000682c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 364552239 1250 364550989 364551001
    0x207030c0321021636060e0708070f12110307030b03071403061519080d03051311010f0e06210105090103080403120e180403030506010801061d030109080f03 69
    0x994039100c0002c40c0080d00d0051030340000541c03803070801c1c8290070f03034812100f540c030340c4198203200c1c0000140e500079440a0b640154504400c0280004e0040074010501c0c02c000c2640f0303e0081c0c008071300c07460907a5100c02da00c0705000000ca5a40c4c144102d800c2d03030544c0322200300400c2c0c04010f000e184100e0f030a5800160f00c0c01d02e14100740c038140c0c0d942d006d241a40f44003540b2055a03240411025446080781580407160113203000031070340410744400c10744140c0d0358030000481c40359004602011402d4041e90244403640700d83d58895940030384505d0052540102d107640c40c4055004104840c020202404c003198151103060104009500044c090310058003100003945813004066192805044181c0d01d0803401d40c110361701d9040c00d1069020251a40e041444101c4202d80702ea03007803001c0031760040e100300b882015208080c00c2002003a18101c0201341010000743d2a54440c910725412500c40341e850130106001380544000c5a0007405d996034040d52111030340300c08121160020051000f40000c05d0343d0f646424 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 364553489 1250 364552239 364552283
    0x71b0305010e0d050a09050603040f0f0b040308010e0c03070305100806010b0702040501170a0206070c0f060903050f010e06160311070305041e03110609040902090412030608010b100e010207030c03 86
    0x80d07180542446018050b1800701540300d0400340c240c401c140e4000c0c9d07407900c950030000c1420100507402080d02d0491101c040c02c1100ca402c8141c0074034429160700700180d884540d9a82c503180100d8018440140900009800e02e202e60001500554032004030040140c480c0c059034200f5400340c0141c0c3d00040001020000c40c24a0700c170305801041e000070340102c1c12508244070f54a80001d180081e1041801080190a0100205080004003890465030308030a03500c3d503014014480c144002d403042d01031040070710200d42c01030140000850720070001e0400e41d0f032200c14180344045a241d2010800d591003c03040010b11405e0014a1403030f0194546a817030381e1601e110081402550f025007003001004c140c0070000240d282040061b004022116030f0b8442040d900410300a102c5540043d512644040900040c00700a50300340c4800511584d0620286440f480300360300f07a40240c000640c01c0200451403e4070248900a06e420031007052040e507040a07504c0e19081721003001d030b4000392180c200714480303c0740c0c6040d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 364554739 1250 364553489 364553503
    0x1051210080f0a0203071e350c0f040e0f100207111e0919051003020307061403040809030c150405041d0312091903050910080609010b071b0305010e 65
    0x300d40010401d0a43d550b0100752150004d00c244640c1d0880800e4001b03010700e04107c402c01500351191140c010f420641c00040c003500300040101103082c00c602102200c1c07440852004540e80000e000b03400d04c4001038040c840140b507400d00c1016030b4081c81c80c0d45c950f100d00900103c001c80384c0c40301002d40c89011505102ca034200422040e00e00c1000b000111010071400c4500503100220200e404032100c0e03541c140c0101c80c4180242202c00c0360380c0791404024290210558038070590307000703800f04c6c0c0c0c2c4562510010390304d4803440c0c4030104d421541440050700250307220000301901440a01034841e82000440414010b007003041c0c0040798030b40081b0f401c0c072a90030320707105d001340d1845840e01d682d112405111b40300e51a0700c202d141002044220744001804000200414034440c43d0b81424603007090701c00c0c28010200e40020220920400c4409000c02d00244596042805501d00074400307842c0364609041e8140c60340c8a0101200c0700c018800c071441c031810000d1080402103020b84004900c00040315986810610 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 364555989 1250 364554739 364554763
    0x30b0105061306080603160303020f0601140a090e0309060307080121080702060c120a090f050d110108040521040302031507121e06150908030a0c030804020105121008 73
    0x10080c000d2440b048018840c500448010781000c0205844520210341007030740d2200b802c06017600008001041642c0007039a03c080c240d98005581040c1d0301c0d089802008010190040d91004504c0428000d90b440ca1344510005990703282160300d048260b001054403070304122036000108411000401c10002102d45408910040c40200c0000c02c8480c0d80d805014000c903100a030113030101051044001108005030f041d02201da4071200c0e21080780b464020401c40c070034040c40000b483c40f408001518145619990f0382164483c030b640d10203001c401c004560036040200203840a200d0920403a001a17500f00703140c60840300402003146d40c1c5042d80181032a110040086c9100b8104650802201a5011003004901d100d64000400c002c1d00c0c1106c40c9072500800b6645060321450040d0001e401c0340340e01401044944d51f42c550101c450340e2000c0d41a181e001305141d810118803a04c1c20b08000a22031711a05620500c1418864281710b055004801c00c10f1003114085440c50380a00b0901100b0b0080204c080486 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 364557239 1250 364555989 364555999
    0x1103090102060f0c0705010608010c020f070803030a150b03010609141c1203090b0a141b04090b040204080f010e010f0b180402011115150a14090612011104030b0105 72
    0x24800000039a80d1200828243c4081c401c040883c01540c94882103505445d0460024071042c0d4490f04407500924660300040c000d44a06081450000390105000040740c42d903501950070365682c03861290180101d004004a007400326800864503140c5580994082e10f015945d1807207081c20b01c00c0c6601c81850301212240309440a402d003a0303031f000c840013150340070713561102e41403100013581601580503149804004001180e8001000560a1598810381d0445c0085c42c03a1109a16400e0f00c0c41081d2008842c030503420107003000203200c41030503600012806200a000103241a40d56024581043e4240402085594651800f11003140b002d001c2c0d01c00000301400c0400000601c0c500050a01c0584444640c0c4c0c0c240a00002e03065a001f5099454a14a45d900380d4410011010f540c3c400c44508442c0e800540120096400c007d003040410071040d0f50903000a82d04540c2004100004410020300140d07014080c440b210f03134641400c0c011055821003e9840c0d40d181c030304518240c035440c601608064095 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 364558489 1250 364557239 364557247
    0x315030706080a150b0d11090a09140c03010b0304030302070512040303050c0f030405060904180602120f15010c061d0708030c1e0606150c121207030504050705010f0306030515071103 80
    0x4603071002228106074104000164a084902e0003441e03a000b14011603a009c81080800244c0e180d41d50444807022040c82000030b4285e41c0c40034250110701007806036218030503041c00007400181c000c1d4001c1445d00d001c0e804403004071001c064441307840c1c3e0040d00f04800290003c02d20719443c8000300408207410b203204000d981080c0c1000c004c02c0031802789401d030b540301d01e88070840041e650031049804a03107140c0140c2c0035541d506682207904004501550b40048003000c0500241c001095081c0c45110300c0e40594034a850b00980e926504058101c0380b90007007100d2040e540020801e9020461750307004022a1000c2e686400a040d200d606000c0400e0440124080f801e56012a0001c00f04007158008001c40e1401c140c102e0186140400c2d018482079520103101b01c86201c0c1001c0300b03000151004480070000302180780ea446e04120306944007030720010076941c030405061050750700030340302542c20741d00c0c1d4600003580503a130b900d41c6450110301640b1008800c411805020f8859881001180030180400c011498 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 364559739 1250 364558489 364558499
    0x40f05010c1205180d030c1806030213060306060c0b15220b150301061103070615030213180204050601120213030c061e120b040e06061207030312020315030706080a15 73
    0x181c0005143c50700415036120b41c05060341e4041c80424a808481801d90b1120580b00c9c00060300a43c020001201c4c80c6245810001d440e030320a0040d1411780b038560340c4120000c0c41959400903040380c00761043c0303d0400854460152500e48240a030001c41091281941145a9404182c1215198035046000e040d101c590207020344117400440f811100345140054428010303031501d03810740c0103402004010340d05022004458101e03660701842a0b90003210101c01e109954142c0e902195035a83c03040c950100700c00c2d1003002524059001c15400741043c14080540e1101503d20f03812070b44182c0e6107174440c2d0003850042c81440382174800c442c0540514240035411001000b501c894a41c0b058400c0c404100c03a191075024a41c00941020881650240c018003d103003030403500a80360102251218080c15070303420b011007440000501001101c0d010307291605040c4984038060040c1d031000300007440e0641c0c0620b10003541c0d2030401408008014558038441141040c0250030251151009980e019018038903003404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 364560989 1250 364559739 364559743
    0xf120213140a0e03070b130c081c0801050f0102100903050405041e23130f0614061e010e06030c04050916110102040302010e100309060e03340209040f05010c120518 72
    0x141003280042a20747d0390156103080310091102d03801440030b50141c2c1c0c444a080c80c100314803040400440780c0328141d040c2e80321014032121202c20b041142c0182d2000703155900f400c6403079000503a603034001d2425629064031003000c00e0036074140e00c5004082c812842900c441c42c119500c141c0d00040710308c0a03408035052b0447c940800ac01806081084401c490f805160200040655003001e4694443c000740007084881070800c00f40c5000f03d61540c0100da00da01c41080000740c0d540c40070f12500b4140c545140d6000e82505101c2e080e000100421000c0000b0000800c0b50b5540b80303901071080c144c1000001c48142c014000a12513001610011816070050006000603030700405e0352500b6410550703603c0d0b0441c0d42c2100880c040c3c44204405480e007450503100d4121a00040000c00f80b80303904c0050760030380000b480e10345071400781400f01040780c500d403141d560001031501440e02508140a00550841b2007400e480b103c0c00c40f0b940c5182075004c00d09900045441000900895520004e0542400040851690000e03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 364562239 1250 364560989 364560991
    0xa142a0306011e050702031501080c010206190e0a050a050a050d0905060d180c0816081605040203070513091406041803050c190c1e0f120213140a0e03070b 68
    0x14110007203084142000c84d00c64000e4456982d001411154016284900401d40d806c080c0102145400b81c0b01100740d15500018036180202c4c0b401d00c149800d040c2c19540c2400901d03036102d011209001d5082003401280d401c01c500e0148502600281c680303510315152032450082c1c3c0352542d40502400500030030141d620b01c2d040d0b940c4400861302c045000c4094460b050404040108d000f84000080a4040740002000900840c0400c0e50000c446106450b2074825a54440c0c000c24207003100f407509410300140c20503401a6821003006c1c145181030114a12070b0841c03005c20764100d00c1d0030039951001041c83c0c15980703c00a030800c1090314100b00c1070040800c03980e00d0600080c070240c00d10a0000f00e500110300200030441e18580e41a06d0429400f0b80307840c1c0034071204d8040c455400081500c400c40784180b69030403201000c0320254000041c46900c1c1c84050b882203981e11805070390011403c40c041020500c14060007500715828400f04025140c0302941c0c008070341c04002d0f86241a4824000200041e604400305 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 364563489 1250 364562239 364562267
    0x10050f160807030617010504050106060203180f0a0302100e030c010f08070c03180305060108010507020321060612010b210105010c02060c16080604050d08040c0b030a142a030601 78
    0x2821071036951480075001303407100d075005044458520850070300c4503c0c19481540503521550092003e20395072001283e44e03002c1c01c40e4182d100e5844a0720342c400d501e0300301c2d911552030034040c09000201c1e07660380000d2a030910701d808080216644450702c03011f51400b8040d02100d4002424201c02c1800342280c003c009920061011003403240ca10442014980181d02c600c0d1031144600040b10210340300e14146072590002c2c0320300d1a06600300300108003410300100c01d40d600c801d007161502440699064102000c04800b421068001d0b20400c05a1100380c210401107019286034203a40b9681c03c40362414882c1c4d41c5c00c01d43d0071003000e1410030043c070aa03a88860508102c42c0c0403121903403642c109054150a0005018111a401c2e41c41080000c06c02800324895104030301840507110b100d200c02406a41900d8100c4006140c0b43e84031a051204483c9000a0760300309440c20b0f000181c4180840e40d2203a620700a64009911100c5003060040c0240300b03800801c09000c46a003002d045040c03903c0061b107152061204 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 364564739 1250 364563489 364563497
    0x903022b17071814040f050c0a081302090a0c0e0103060b03010b0f0c0106030b190203060f1002011506020616112d011802040506030c010f110a05030c10050f16 70
    0x880c241500c60021050760010f4543c107044416550803400f40c0c0590181c149500440c01d0089141402c4494400d0f54032414901081510380310980d070040381c43c101f000748881c9900c0c82e940c40040c0941c8030405080c0c4101a040d10002d00055a02c001030190340065016904050900100f4810b4406160035a81160300308010a40c0700c1c410342c036542540340a1003070300100030340c038200c1e00100f0300101600c000d001e01780c41c09040a111001690403804d0744012030300c00d0340002040e01c50345d0850408920b290b02d0707641c46200001740a283c0748504980c803000f6034009001680504144407081100400e91460b036501402c11a2a4040c4d1020507525018261642d00d079000300d20038528005100548901813007103820340200001c000005250050b03c80500003a80030350300d0704001414038200098011001d4005071944007100c1d1280c0c008407130303c629a46c0381d04854062424208001282000030b4869200010060150304070b4903000c41e02100c400030040c0550740300280501c0f048070301140c403480d41c0400e0391034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 364565989 1250 364564739 364564741
    0x3020108071103070c0f0b120403120207140d02010506060c0705060f1308010f0f020909040212100c0e0405072609070f140a140a0512010e010903022b17 67
    0x34182c0384544001c1c41200d460100180e403000300188400010142d0708595a2424100c0c5c41d010060a0b9018803000c1d00c01500085000c1008039015043c000e1220400b104094640303605580d8140d480c404400302d10126920407400480f01c582c080c06002d91080c1309580243c00c1400c1c110105584200510a83d0b0040703100161012801c40c200c002c40e11010120f541c0340110943d40c198080c001c1410f000f0b150440f600d08816441110818006c564414070001c0403400107032195020001804906090321102e07118108500c6485102400340300c40d8042691601c003c1060325009100594070014149001c10910104100d5982c01130150781c020f90501049200c03c03980e0716410503143c00400e402000301040d0b203403400548049000c0422801d56010798071038604a9440b01089030780c0410302901c1e0b501419840d024041070500700c5401900800c1800081142010743c0c0b901421280704140c2500143c01c44058560664140380c000041440c050007103009100707000710002c0c00c00003500b8540820581d064 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 364567239 1250 364565989 364566001
    0x270e010f061e050d0b0604230a140105060304080f070f061e0e0c030d030b1503040c0518040302030706090212060106081006020f03160215120402040b061303020108 72
    0x16100214203040c8800c2000210780300c2c2205080e504051440c800802c0c80c0980224182c2800328992240720b512a80c50241602d840c0c0c10007003e008420f01c0d480c0840c0c1a0102c0c441c1c00c0b640161014081e24003580005404000620b5008403000142c010340c2c001e5a040042c0f10000725081c0440301d0a083c0210466156281d903d0180740810702580040e141c1401d04840c0003091000102803c070915844d842040010040860369071204151600550306400c801c1071900501e000e80c120304004800144200d003030440d0100c40c2003143d0410754040e903421018440601950500600110207071200b0400070079107142079035009503a03101d890802081c00d503c0e00e540104540300c2c030455007203003c5082c0a5400d29030f155000140b519400311000c00d11b9995148000036860300100c2c11120f144e10180c069403414074510100400801007800498000b400301408110361004800a00540240041d1205c0d15040070300410007503030007900f00907208007401c0104a0781503000070090b804072070b42802c264035240d07030f41 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 364568345 1106 364567239 364567241
    0x807150f02060705031003061d010606140a0c06090605070e0a050d030203033409030507060305280b030321100308030703020c010b060f13270e01 64
    0x50301080015125130300030740d0300411089250084503030b2503032102c049441c42c4000c840113100c544008100d4040a000341d1004104034540b4011a8161598003c014420407100000780401608180704001e100c1d0060387d040c5402800411261608001c05420900d6401000d84031340e800c5200854035140c00b5801d8846140c05500540c203650b1401002c0c0414041e00100c88425084500050780034414418044004180d607601c41d05810301e549002031400c1d42603040305043c181888100200d1106000c10303010048103800c0c0590100021082d4074000740842d0100c1c42d0503000009108a5000c3c650a450548100103490542544e40e0440020010516400020000501000481e60b013500c2600603101910450700000350025011000400c240c2c02041c038883d0411002c2003215050602107006001020043d801f09102c82100524146420001150f80c4009a680ca405815100700f = true := by decide +kernel

theorem cover : BRFrame.Cov 364388489 364568345 := by
  have h0 := BRFrame.cov_init 364388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 364388489 ≤ n) (h2 : n < 364568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
