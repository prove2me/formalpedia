-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1186
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:39:25.087896+00:00
-- url     : https://prove2.me/submissions/476b44a4-066c-4dd1-b075-a013797b7247

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 213129496 ≤ n < 213309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 213130746 1250 213129496 213129529
    0x110910111501090b090106021903030506031203070801030606090501030c290c150c090a06140f03040c0501020f011a010e010e04090506041208090601030809030a0506010f0501021002030f0411 84
    0x602000181c500000e420110013034800300c4024000d07030b132603840807030342ca1043d80000080c00301404500400f1a000340d00664100300c001d030a8980b1181c2d03030840c4031515402aa10400082d42440c01041403007081e126030009407199a80a2141e0b502d10f8a4401c07200510707008011602180ca10720408e011800c420b910400c001c9480074644581a40090b2500d962140c8001c1914654100001d800d0881c444100c51030307000020325240ba2a410034800301c445400b01c8040083c2507504001d0f401d5412124800b940c480d610038003003810b031030341002c00090601707500c0c0c000c1c103071140c1c18020314003a020406030741c0e400d03508420303c0d002070f841c000200101d9814207100d0201e9042480c003001c00044c881c3c0400c0c0c1070700c1030780a24041c4240d8861480200d807264000c4614412a4200c0001880050325a200419890400908076401c00000c0e45a0b1030501c0c1083e4084843c08000b00e6040205580500a100000548240c114258681b07850356413881031005000808408512081d21a155a80e00d1248500050f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 213131996 1250 213130746 213130783
    0x10b0a170c04060f02160909150905030304030f02030a0f080709050418020a21020402160b13030905041104140102030c0a0303050103030e06030c0a0c060e0a03020c0411091011 77
    0x8081c0140c44440e4000e00070a40025400002da008860002580580c401c1d120701d0f8010282d46000b00101c02003020910841c1d030249040300848220845004400c1140c3c0194040d5507a414245005852940501c2c881000e41d0014003100c081e442c2c001510341c1c00707181c84e4281140c440e500c08a0449417080030f42c1040e64041c0c40c044000e2100c2200d1410899414402e4074007110994031403407001300203104035400b14000d10540103918010b00300703a00907144d488810302240b05900c40319552424500401c95150f000803000401070400d05034000c00140c010b14041c0e0303003085020484010f1070264402c078007602044401740004800140d20800460341001c9180301a104e12515528008019207401c1c40f00f40c00080d20340d0441c0c00117140406c2228000d401c0303560070910702451784e10160740ba0f40700b036070007500c09903500c40c080140450180002c0422034400e5003d802080141c608002c01c481030f80320280d00040c0c0c144104941510b400d400011802c41c01d06080d0745e99005440241e00d800001c0f120305a0108 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 213133246 1250 213131996 213132001
    0x20604030c0c1a070512040302060f130b0c010c020622061e020f0c100b01050d09020a080615031203060907140c16050310050f01060e04090602070506100617010b0a17 73
    0x80b0712019090711351080007607545c43e10742c41d4000d442d18000c0c0e00000e54082c0f8208000d03c00040f60000400784810001803c0903016582c02200744030b03800c01041c518aa035104c07052140202c2c1d05002d03c0390300040701003004440307111481000100b40c0625074010300c03c9690303a594207085400020b1038445105954819552400300103107c068517001811030b00201e12440c0a0080a142c4a0180c10440c02040c0d40c6e00d42024000c0c070000d005030071104c00582c0c120074652000b00340300200348011841840410320070074000c0390700801e0500d010801648107103814000d1052101c560790743d40405802204626014000c181c204a84005078403c030006014603110b0254220400706034a003003e404c072001203050740c1002241910f10010b40c0c0045814520260510005000541c0a0b00440121490141c00090700d1036040e600c42041b07a00c900010b4425a010303104008802494075585005052145080d440040204142c00410340040c0244046540f01041c41140c00c0e1140c4641d0548041440c5501c0079030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 213134496 1250 213133246 213133289
    0x10209120705090106080108030307081302030708071406130608190606030501060e01050304030905150405090a06030b0c0406090302091504050f0402010908010612020d0201020a1704081507020604030c0c 89
    0x20300c081d102d074038025080301000298550159422038101d400c204060343c0f5556034451b0464503100010078120305500c424120074003584041000034007a11404005003455401c00301e500e0b600c00c0d00d0003041c0d8400e91081010303e801b810074a4001c01240c1250030080c44e1a1154000000001e450391481e00c4a1880c140380002c52035416003003241281c3d101d4882605410340070b0011105840121005004141110400c0006050010251030701803889140542040d40b18030001c3d044070400c1d11400303001c03500d80340203209210406030b080e0b4200314070074a01482d1902d406405429240c00b40300191242030342100051500f0010f814084d20070500070070402071450030742a044900b12082d14180e0011700c0c18030000ca0300c00c505209403415240218415008015a54204607000198900490460046d4940e0300002245006a600002c2c240b0210f10349450525110a03d8162442075404c0320340f10f101300788461903802091090700180c05103041c0d18928424107107100da101c55035000000c00395010300c2c5407548 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 213135746 1250 213134496 213134503
    0x20d1a0a060603020a08040f080c070905090c04021306030f0f02071a2d0a090501052401020a020f0409060b10020a03110a110907090803030a0e0d2a0501020912 70
    0xc0c409400c0104074840d120b0500320100c0c024800c64202042c459400702e0042125100a00a0a441388450f580f51054449049040c050301c0d40c400c265485c1c494080c03210307801040c0300400e01080c082c1e60441c24003a04650725032030b43c5e000340f28003070916686081c42513881d0065040703000f060103050401d41d903034501842c001030150150055280151240341c041191407070710242c010310203000d0001918844544061a130591072025100c1d0448681d182440c100040c020700035103104000c55070600d1a480c441c051a0800c4200b0001c00354110b400400703034140183c4c0c1e450703036000c0d5000c41500e000402160602c1e2010050011401c80c40d4003d191015149101c0d0703001034100001c0348607a4401300011030050320160348000c0d00310b00401488d0340d60394458035402c00100b59070b401180d03481c084440d10f50b1000b48500b940d10956600e02c1c4291100d001c000060400c1106142c0d009480c50038400803c400305014205c0b00d10303a008500407201034907802d814440c09405441004d88010001002810703202c48550b40c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 213136996 1250 213135746 213135751
    0x70305010c050d0f050412050913060e0105010210050106081b131e0909050705040e1e0303071d090105010f030605060d0212011203050d0b15030f0117070311060304020d1a 75
    0x3c041d003050440c031000035081c080d160060703074000c0505600440c000c00a4034940c204622403904482c0ba48002100080c0394002c240061155402c86a259410312000906240141400e036181c10705120041042e0780e4410b4407030303a100c09028100b11a0048440b01002b4a02c9029001500700302107050100701c814442d0040240e070060314884134581030390307540b070401510186079021300b0070b4120860400103402e042d046803205030468010b0b6440792864540d00c80740b582c10004100312551001c0100020660403548129170640485425003182c0caa1200248207074005016280c10400c10204400d420390003a003140c409810001d1035a03444040c4401604000c0d0404500385000c1e40118000003a004041030204c00e0041e0140d6031240b801d00c582c48503001500352034650941062084180f0200e20b18034801a5004102d00b0300c03141ea5a500d0303d5481102d81040510400050300466002c10000341c041072400752105003550aa5160395071400000d84d03650342c40e1405040c0183c01d40000e030429480720300840c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 213138246 1250 213136996 213137017
    0xf0314060903072d052d1c090b04030309031b080d0c02031e101802010206070509061c091202060105030a060509100c090303140702090a090501090519020312090607080c070305010c05 80
    0x742000080840d40400180380002c1d5400c1049079031101030f900747c1d101ea0411013a08240c040b140d40d80c049140c5a6000f1783c07098001504083c0144108556048101c0307074100c0c602070803c01242025007060719428906000d00038046032032080030441d00c045c006980020f9154020101c2910420130013074a50344070036542001d0f245883c9516041d4404140344260719034040c1d000305000c0d03944160560b0194010300903d6031003202400041c001807a400950511a07044c0c1e2004101e1544138074105403840002c5105c4825500703e40014400d80d100003c00c4105242c1142d408641600d03000003040c204861910701e48143e5080c07060b11000183c0114402d02143d100f9901c0f0301d0b0030051040c011038540a0684025403180701040841c10032070064022180d12401080002000e20b00340ea0741c02c1c0741c2100f0720500c1a40b1012148c0c80419403031305010300303812503441e080745038601055800041c0c030520602c0c900800140c404107074a400d10400300481002307194880002c101c208003a40010f000d6800014214 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 213139496 1250 213138246 213138283
    0x1e040204080d0215040506012d06030f0e010603081c020d06030c050a0e0c0301060f0e0306040c090e070b07500d0e060a180f0314060903072d05 63
    0x25a0583d160742842e62080f070300b041c040c07c0c01342d081500c2c81d40c02e54400010103510301c07000e0001c542c04007201029800142103c0d100081c001030040c003800b050f0f841041c40d50781113074517200b81040030411803002c480700500c60f9542450711243c1d0882e014028055a01c0e03455002e460301401000300a00400c498060b540c08032460728009594401c00000b602e0129038500039000103100411115009089410485c1c1550a20260039802400440d00d0720100321420b41c5d82d00000d20b030070014103603148502c40d50070450328003401980b814100a40b07540c1c0702d1103c005180401e2221403c0182911019102050489050060b84001c0d6249001c41000070504013413411000740105148004000400548000503500d82062000c001d80400080340c011800d01c109000501c0c803454405140802e04101820416052081041c15410200250462807451006651001e02400340142d0008165481d4662080b41031b01200f240b940140c0c01801c200300c0e0728141c00390141c417a000300140842d142d995646a100c0703c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 213140746 1250 213139496 213139513
    0xe010303020f03031003081b0102120402010315080307020f0f030a05010506010e0405040218040c0510030912020a0201050d0b010909110306190f0603180c06020303090c0613051e040204080d02 84
    0x2d0540700c1c4004e903a18400644034500400000f004100609444018160301e08a101c0318540540d082e030740021a0b0100d01079481c4100811982c0610400189601400e0f81250090074544a0b42d42c078404e810000e44030742d80040c0d2031800c41e81c90002c603295206018080d0392000c580380c07a002d4060310003650f405001c41c0b80740c403510700541007070300c207140c0f14540050060404010364148a041101c0c05002512410203100010400d5200c078026103800183c0c0da903001400c1c1915003001e290104802c100d900841d0018000540940c2e8004180c1e00903000d440d80019007591584016105503040d40d000d013010604041d10901f400d5050320195201341402d0f22159000514141840120f18403806402da400c0040c441c14480306102c4c1d8802510141c000c0300f1190881103d440e4016030340032603440200164000010848040002d00403010030703101c183c49036400c00d240b10081c0d03a02c0d80d0b29409054003401500d40114034409401c45407007404c12000d48119500d58071508925114851041e000000d0321031141e8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 213141996 1250 213140746 213140773
    0x11403010c08061c0209090d091d07050d0207020405010b072003032205030303040b07090b0a0e01141215040b06160b1810060501080718050405070302070803010e01030302 75
    0x14503004018a40d0350080d203603a912041000c2c040d41101005030b01039810140c4070042c1c540124403805956000000d041c50345d41d5000090070510755800808141102460ac0c101c604604085590004044e00780140c50350f10036007800c2c00a0040c2d110180d40541010300004490519000030804640240703152420000440c404030102204084519010745c820402e00d540c0711854038280505281d00910442101d9031080060b156400648040d40d0210868042c008001c5e0001141001454200b803280d0a0501c0500c014002100c03541d2030f81d0500c003680d9000c01040c40540115a9002e418030321044c5c0b1414030811800300c01c00342141c903a00841ca09000c001d19447d20034241c40500c16800b40c440303c0300b4129070303520030b01050141001f420796080754800c2d049090240600d440c03107070361010001407552038078000524004001d89090b051040402234030141c2c00544401c3c10683e00c0555010510b920341901c1140280301e5108007400080c0e0100002c41d502c101d603030300141224029821169000030002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 213143246 1250 213141996 213142001
    0x80706060b042c01050f030c0d060212070c050c09180322050315010510141603090609030b0f0903090a030506041109010806151504121203020a0f05090409050f0601140301 75
    0x32080d10b000f10f800d4010011460051000030041c48040c003542c8108489102003080c26041141c102c54203600481c03012003504e40c50341c02ca43d0080d0310b4a0024219034254036110303162062005446d000300140d10014407054180c981c00b00b601c40240040702d0303031440c040d14541122003003141c000044e08103003140050107142c00a0008105414205205202e91034034080051002c0b26003d680240a8028a0001003d00d2100604440100400585d09910303080c60014a0200d44d070f000802802001281480402c0702c81d05042e0780002031b1803c00c84286c03105039540746135009881c2540c5e4002c40d01320000c8108800456160300651084580140180c0c1748030401c17008100900a400c01a4406800502c164501c810601101003002d0441c903041103940c0c42c3c5100b1070703003e508946111420083c64a080003900300c0c01ca0103844040c40c2c00c500f000c000c000c0c000e20300685a505e5000304007010400c0517260385e469108081e4107500c5012112200c046241d00b5488020034410000b10701202c000c00e115506060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 213144496 1250 213143246 213143309
    0x5120c0103050906150d05120f030f0604020717070606030512040e01170d18030606030f12030902030d030e030909040620070c06050f120f1603090f0807080706060b04 73
    0x1045c08100041c8a006d2101c00d588550096560b03200d10252000303c0c00d01d42c001403a0903640203800355960300d4100038038080301001500950050b84100500001704002a0125842080380f030796240d5105a81d0a0007c040c00e001e80025005003d49400c2c03400285456005000321440aa50543c1680e80d4030401005000141c0541d901c503009031003640403a5104851080c9035070403101c050f2807516140c0d180c000450344590070454449550702d40b00360502100c0303140c030240e1840f00d00c0c0c240322051103031340460b0b2907154104521052603280d184241c0058000d1003514011a400780408a540c0f6040c00c0142c09000f94250b8141704581c480c4c01e40103e9940041200c40040c0c102c41421159490400120340716481400140d1111100303200014040d03241c49800c500034101301d21050114105210b0103d24681c90f000040241458443c480000400074403400c03800541042c1840e4440860b402d21841d54840c011008106a01d42800820b2014403040500142c6004020386410300c900c841c03000c942e42110303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 213145746 1250 213144496 213144511
    0xe0708060a0207080f04060507060b100c15060e130b010506040305060705090604120309030312062301020109080705010c020c101b030909020d061e05010f0507080405120c0103050906 80
    0xc0001075000c401980003080600d01c50010145030120100381d50150f44c205e40c02c00000200005003540c02d105d1a4083c140c03201074101c0725041d40880c1180050a601800700303000b0b00c98a0000640d14001d07845d0b030b003c403004007a40040c41955150415140d80b0191541c241190801c9410001203254200002903405076070b400402814035031102d20040e985030f0405040c1a80c002e40801000c214140d11041c0344e45510311039100e070190182180781c00b07050205129600d150240c80c0c15000c005905000c1c1142480c06100303040030045e9500040104d000d090b0104c40509000000102e138000c000c0154004102200c099081d41c0e031440841c806c000c19140d04d170b95400b000906002c81d915004001a492041e501e12031300f0856a210341c2d8440321400d81c0c1000840c511050750701c0c0810042d041c074485501802c03d0002e049140700c10300b004000703041c188031039004404000010820004100100045a024003401050940c400c0303e40081503a8880500e450316001074109000301d48030541c00100980a441c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 213146996 1250 213145746 213145753
    0x108060613050a0618020705070e0603070302150405060309060a0e0105062107150f081303080c030717010308091e0f010f0c0812090d020d080604020d020c1f0e0708 72
    0x15a54980020b403401030811182e40d0b5031030100050306106410b5a07001c08103007941c0540c03500002c2c2082814903441c1c1c0d01c1103503103ca5260800401c0e5034082000f4007525812030380007200b840f54180000c2c030340c020b541006400c20000018060f0b02400006c0c51403180000b05014455520700130341c000d0980b502510b487c0d820020921078800b07080c283d03a039030b2440c50034010201e034447c50795003200c410070280c030015a40c0465284222040203a60080445511000100c0128042a82503030010000940100b05418541c80400030a8a9610032101040d24a900c003560240b656101c2c21b102d4485d60000030140e01c40c00b000d40043c0b0600e0300407a000080c40030010b180080e4101d50a0040d075100d160740da0117100300050300b40c2441c0010722107800b500080c80c0d0620520f22500c0c0c40300005144c1040040c5882c195400707003944075503099000041c5c5602031001c3e1001342c2c4840810203110064010304c02c0f844014000e0200b51400e0010305c1440071400807180b00c1c14026a03d000092a46030040c90041a80d43c4c1c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 213148246 1250 213146996 213147019
    0x6070f140f0c010f05061206010305060c0a05071b1814070503071107091b0519050f07020405040605070e060406170c130314100608031b030c030d0501030b01080606 72
    0x49240c001d441c682809844403460800c8403003000c1d007141c8011003a200c00542da501400038504140c0e50043c00d228510008201c0b40d411525403c0d6141c4000300107441c462000281c40100f544600b05131515a584149100700304038a0302103004858000703000d095001d91031000700c004140f8cc940074091407058a8018075195440703074101103405030b1004001c1001d00c004c00840c64001c0c41c0400a02008140f070580000702c600d4108040c842c0f14440d031408000308801031011201044034950074100315016402d1640d5280400d10800340303940103840001e0b43c09407420040006008254010501c9506980d0f281758400d00414100545800386000c0c0c0c50002d06108a03a210444a403c0c000303400484181c141410410312000c41110246035810807100300401c0c01c80039051078401c101c1000b2240c1d42e1842070050a05040f06103541e40501406c0000520500b02420340c0703a60148122814a080d0400b034aa0380e020001c0000040c0c8800c1c40201c0d1450f07109000041c00c20f9010650304c2c024140103162841c0030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 213149496 1250 213148246 213148277
    0xb011b020f032104050406090b010917100606020303180727020d02190305060a0e06010c1a07030903090503030c0d0c1704090c020615030712051f02090306070f 70
    0x1201240c811640500c40d000008050f09101850412a42c2d401c1c101559214109018401502c20903409246114208040c0c1c010503178220b1540c106a5440e08107040d1204408a0320614007060b8103000e461b407900e044004503040e6408001188203500d84000380f200300c1c82d6069001e542c0e00386403040101803820600c14001d2114a150320107041c0c51401c501506000310007006400300da006848600c1c070001c01165001c81d00c3e0701401000e0b8440d50413500c803903038140703051341d90500b00300001c000302c0c10400000d640c9010460494040140c80710207000000c0b5918141398058018040d044043c0c0106881d9040040c103460004101c81148590b0406460700642e000b0f4151050341101c01c1c100d0b9401104008101c602100d10060f0005058024020030151080e400c0a4140320703010344000e111099414140780541c40001e014421590458124030300f80c031090030b0140c2008580255000ea100c25800c0d018444110341d0094540134004405850b001c1e00c1d400b8042d182441c3c0301440c100402c980c00162180c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 213150746 1250 213149496 213149509
    0x603120e060a0e0a0306150e0f0609042d11330307170a02040905010803030709030206030a090501091a092109010309020405040c15020f03121b0301030f060b011b02 72
    0xc290015007280038094172555404162090703a2601004917121800c10402d02c03624607026500b11044c099082c989060000100e07426190041026051440b1010303600d00b040400364500e5160244e40360b41582405580c40d14180707007800c010445100348000340d040c00090410100d403014128a1180e080c1301100c4201d800541900010001003d000c020140c2d801100020030071540f1500c1318050040e80c0d2070510000404039841a000f900e0b840e8010b10801040d03e0b0001448820703250101c412039166034604208401403c40e0702001000e95080501490812115613202c8d040f80300540320404103a641c4017601981c0f480b203030b64082414004011070300154002540100318513001850302295204d020b0700842c1c1925400c0d10708490b074030b0044408018989640f07012901c1007407a80301038800300d403001c0c5600303640e8000e012804840c2001720b004101244004285c0a18001101440b60784075a07490614510705091a1400d44038641440c60240c80c942c8284100a0741981c5c14840d039a1f203000c641c003481035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 213151996 1250 213150746 213150767
    0xa0504090c090803040f09050a06030519060b0a030f0b060102490206040c08120702041e0e03070302010b04060e010e04050f0f0d11120301030b0406060e07030603120e060a 75
    0x14402c034014003143c50102400100050000030f03442d2603000e4545904c2d6400c503200200901c1c80d42e80303060390602c001880824030f034100d9800c80d201340f1a000304c2420400002c0040042c4e813540b111050320004200001040c0f000c0c0283d028800700e2081e80e440e4001681c9407200800ca07090f8100d940c0742034009401d42003180b2110007071038030202c82180c070b0b02100500000d070f841c1c0d0354040544e00c03140c100410015070081c480098020b6502528640601c1341e015050f074090b080c0000d00c61510ba000d40442c040b501107084090510100b030070700580140d40c09103a100da00c039010580065080020302c0b552418203000d8502203070180f1181d04100c1c0c7ca003c03034900440b400908200ea050055410100ea03200b070421418038480004005402e0a140f001d41c040c10090900c646a0788581240c440c0140d104000410769044a03001010342c68141e80d0740c60701100a28046c3c00001c0c5000c0d8102c240411141c6c0342d84450103583c440d00280c00a501b82550030703681000c0016603598002410808041118070503214002c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 213153246 1250 213151996 213152021
    0x41b08180106030b06123c0304260604031202070213050c03010801060618090905031606020d0b03010b10032d0e210d050423060402030f01020a050409 66
    0x540c5240c6140500c1c2900c6003a4010f68015070194207000e0b182c83c1c80340300a003c81c0d990384003d0880d1b145507501a08000c14004d030b080703400146004900b50400f080469071800308807070403c0c3da0391261107041d200d0289210780c0c1d1509a400ca85002810490307400100580541e0705a281c40f20b680061040300b0011350700140c0101c0c0c0011100342001c800d11003500605004441a20b02c40e42c4940c1446403640c212406607021504202f0740805200e02000aa1260419100103200201e5015414108030b865031140c014540d804091100084040c8645907021344880c0340b04050510650980380201408da82c2255a40ea0703106c0c00402030031200c1070196101c4001d0307000406030800344452072554000c08420880140402607190b4021110552081c04901b0700fa01042441d52681e028900601c90b0030702822441c40d840319a154041000d101f0b010549444030b0440f0324101100007074074076055440c6d45085d60101e010748112031030214048418003d9820741002503941d40c1c286841c103204100074044001c1d180 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 213154496 1250 213153246 213153271
    0xc03020c0d020f0d0308060103230417120a0501030516030201020c0909100204060c02091b030708040c0e0720071a1c0513030f0207050117060a1502070f05041b08 71
    0x402c41c03030726404d1500544d5030080d150130903e0701c0d01070005429a0302c41d1101c01e003480945185801d981900c13915450300b1136004500e04032240e200080c8894030788612620508011300e404104200e0107150b4000905991048041d201550003498407503008416a001c002d0241c0c101202040083c245039031034660100010080b24050441813908000302c2e40250440000110160071003010760810a15440d0441083c03900b004002d0000d02285104c0d000c0036000034104454a408201440242c145030380c050f100d140e6250ba802c1c10820000b83c078040440c44003064841c10042e4a2001c2000031070104210b41100641c80c46c1641c910404020b11f9200188003100740118010300140c0110a110703042c0303d11480c881008089400d8240a0102882c0d000c9020444d4070400e02403105980c0f09035842d12100b6200e8178040f450f12844005525160745410010b0b00880640c41400c0c41903000840c04100e514220351802581d40394424042654407a42501402170000520201c01c03603c1242ca0641c420055100b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 213155746 1250 213154496 213154519
    0x1122050a06030b040e030711060a1205010e010e0a1505040902030f0d03140903071e0f020d0501020307031503170c03040f030b070917070501110309150c010506010c03020c0d02 77
    0x16100d40d50036040180040c0d51035440329054105807254049000c4820015820801c050351554400c01803040e00364010b200100c0d001c0e0761140903007440e40c480c03680080103011541e114015980c120a09103e00219003582001140601e00d1901c20219101c6507011148585810700c01800042c02d1000c0e0102d070540304550708410210703c00d104401420b241c40c3d5000c034403a0003072042d000a5050140c4070003070b1034100b00005070000b03211255441000014440c0b114040700d1a017020500c24031040e5010350040c2c400380b100420854198015403040d4140c0d102009035181103000c6d0002d422150000600124045000b5085250550042c003000c2d11040b040342d11380780d00da441140b07407100194412215805007005100696811100c10000b800701030559120b0b02d0f2920519990300d428501ca10717810b03c03148603210307030060100788212500c02c00c0140481517100640300541d0b02070f41c0f24500d420303a40d500c0c210118116621071540301000d550503078014016000c201040000c0300c180a8800c03680102d034100d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 213156996 1250 213155746 213155749
    0x7030b040b011409061c0e010b060c06071805100c02010305070c022812060623130f020405030d02060405011a060d0b010504031707022803030e040e07080703030210112205 75
    0x401c0840c0c0c150411000c110501c880c0070041c00d442d89d0640031031180ca82807210180390b403800180e140e480f00452512a604451071010f16401494642101e908001249044d003401c54020620340c0b0414800e036410481682c0d00320b411641c4946011000758080300d95004041e000098020380b10300c0000010060042940c0da8242c0c0c044194950411211641c450404009640440d007080541002c15030503a03d460848400041502d000482002c612680d1410340b04010749a550654000d4100a0300b00c8801d50052a406907071514110340854841d82408004c3c0c603140414004d0303a10b81140334022030b0801682404170805001c4030381e64a81041000d110000216840212201d84841901c40c0656a60440e0040c840c0400e8514981151220351207818a0120b002c107280d04100ca40601d00307024144000c2d00001c1c09450403089a000ca80300c1d03003101062418011500400302d074407a40844103040b510a07418000d48009961030940c06030300f0300181800c2c0820f20400c400c4c4010342d00209454a44500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 213158246 1250 213156996 213157027
    0x504050403021e010203011406130b03131103010209060a110a050d05040e0708010b0f0a0302040e04062f180d0203010c030230040f0218010b0307030b040b01140906 72
    0x26030540c010b900040b80c040329800c00c00b200320b503a0b011050082d49150b0400b031101302405000d9031654050440007070b07070304400540b400c4980054010f01c0101540c908090750300410030400a00c040e14079400f01c140703103203807860144219142034401030111303400c1c4141d04109031200454940c0380c0344c1c24001c1c86880e00025070144000c448019280d29455255410070300564201000100045d041c4000e0200610403400c0d5074090342d00c00010900025900c90500030100c01038040e5a0048440c10000820300c810032410b90009844c41450600d00511038059481582c00040b509007404a204030800c40549840c0c0034004a805022010302980009162940070a00711010421043c00096011880e40d40b80130714619050000c24403c1c10b1408080c464012480d20b03090003500080041841c1c4240004644441d0300ca107109407003500c450021927940300d01d1044180d00072284080000c2c0381c500b082090786440d120348a030410b4103030749a03195444600c1c1c0040b1554040d0790707440d03031011080c401c1710002024070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 213159496 1250 213158246 213158251
    0xc120108030720091b040b0d09110d0f0b070c0b040b01060813031e0905030d030504020307061e0f0509120f071d070e01036f050405 58
    0x10000e6540d0030090600f10580d9150381c10b00c000141c41180050042d41d2440c1185410881686240300c42003528142a040c501c11303540803001120000c607603481c4118042d4032958506000d5140ca00881e20142d00308040104100c0005100000c4185e40201290981100c2c65200d503487c10152141c030300070b4882c011102c1003114129680803508006000c0c00364080b1110790003a001c107c0c00c55884105590180c080c2803424100c0000b00c1d0384224425015114662441c0105800b40c00d4034481e46c40040c0c02000360104070390590092003008000122180324121528480e0417001d0b4403c030070700601b68101d6012100b02c40400400000b40301100c020759a1a01d6680c00d0310a18009003240c80840003420300740610f41d4801c5128550f06607414840c80a418690b541c001031a2a000301061001c40040c1c00a00301166040417201001d000c00320440407403100d1340004002e200e42105004a42040022400828441300d90300c0002c40d4070850045011246920600910180c40d0b400942c0707806c0071a0484908 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 213160746 1250 213159496 213159509
    0xa0c08090a0f1704090209040608010b1309020f0a03140705060306060415030f02040f0614191407060212061903051903090513020a1d09070e01030e0f061501030506090604050c1201 79
    0x41f5507c240c602032007014010309030301d0000c3c440402d40c2000030300200c1c035000322f8040c06034036a4403920456542010440c4c07072000080240034030070381340e0410003020006071171246201d00c2a0800410181303086c000b580d101d0000100124a0181020080c0941700484ca03080f20074107880b00306d00d040c1d4075000c3c0043c0c000740c03822000c03c0030b050b80707080380080881c00f140c1f03003407a032000c03040003490201000343c1781c81c8a443c0f100f410003a4034100141c002078454440d000001d80303403906c00702d00d01e19410100c00149000301c600311004e500351030485481002ca0503039440018265030040f030910407070751003180d690401c1f14040c0c14001506561440030507001e1030312283c606e40155000035442c1540390003884400b43c4042c081c0120b035856001c0008956009006410b20b0705001c020f20341789125038425000702c20b800b030100e1305580d203c04070304009607a1100c003070301c95041c2d00200010621595100b031181a10540008108034010386550051000400c80901002042041002111150240340000e14001d004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 213161996 1250 213160746 213160751
    0x61a03070311041103010b07060518010f050a05090309030618030f0403051c090806040816081306020607030c0203120406060317030402130504050a110f180a0c08090a0f170409 77
    0x2c4240411040320120303000004098400d00050090740d00e8102a50340140d4060000070b015101c00c1c20415000c08010700440f030a6007080460140e03904107410040c01200c09910138001500c031044516224000c01058503055889440040d00c481c40e0380045607001c102c00419070b0700e000301455117490235500a40060342d40b40c3c00201c6880e00714000403c60151007589141402600781440d26481c1c0b10b140140010b050244040344104100e01c0004000304410703801b81c18644d03640c1100c1a02203810920703208040240c096100052882030190003407c41c0e81c007080e07016524010382c01800b0001c440700a00256a40303540c030000800010705d4064400d400d0562503c0383c40d00d9107054410010741002c0f40f090580e40c14148024400040c00000b40d0700c003503650201400a1000c1080d000c01c0340c02c2425100254091012403410990a03d2802618080c00e66a90b0510940d988510300350b4080100b642c081ca00c41d4498100702010401d924200124984a1902602103448007030084801ea00319821084945a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 213163246 1250 213161996 213162023
    0x12011401023c010e0d0201021c0902180a09020a0503060903042102062b020f04060804030c0204020f041d0424140a051509070e0112020906031305070906050a03061a030703 75
    0x50f82001140b172080c211748001e51501071100754100500c2c458980440040d07403980820f004540da9a580f07013040150f44583c0c0113092501920010160020705016402800c1030300006c203c41c1400328080c1c2c4584200c1008524007890000541a03ca21a805098190250b03480e00700059036218010702100e1040e9003140325803011200303291052044140441c140d14810026540550307003000a88089504500382a1104d56032410140d8082d801d0100c001d60007480081c84118a1844030054802e481300c0d420340003066001e200141c0702101080e54060705000804500036000900d0060b82c0848202d0020041000400c0411801d80750744162000044140c49104105000c41c2d080f9490141c5070085409860354100280050920340200d035440b4100300c1c158404500040444e011901010806402c0a03aa45804a044001c80c1807516040790240243c0c01d0000b1868854010340b03068540041002e0b07911491540c45600821201c065604102080c040d0704010b40c0d0144040310046002d0911000000e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 213164496 1250 213163246 213163271
    0x803070305100816060e0f03010c1d0103140c070201140309070510231e03100906050d050613020126040b160c02040906090b010b12011401023c01 64
    0x1031429006800242c0c810f40e44891100210b0b9000d13130884549061140020041c0c5002c0f642041c20f03011303003607003560a000024000652100c0200c0c1c118218664040304070351318000450994407594020b900101e840c0020520602e0007200034107081d4414102020b861241204400258000729020401034005103020015402e0006d0740c05c004031110319040341441858282500c045401d1030182010170340c041609540e4842108011307018400c50300f00942c40340342502c803000c00356005000d00e024060611400080c1c90070700d0004804030382e0f448000340c0307030310fa5420004455800121509034100503a201e041e030296403d00c60002000740700c90402e190b01e0b1406081242040780090024034501d400400308400380380e40011403406840d81102c0100b0200118204070002c2c01000f00068031701a020400080e02481c2c80b4010b190100e0b0020341820140e0340d80c08000702c40740f1604401c0c0e0158024613002d04040320a00c4800450783d40c40690407200c01500a030a90202c41420426001e90b0f540304640d6404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 213165746 1250 213164496 213164521
    0xb18010b0c0606152a0106141003140a0504021f0201021e2b060308040b03071206180f0f0e0f0c0d030e01050f040504020a0905180705041707030803070305 68
    0x3d070081c2c5000d0b003e1a018603000046200c0c2e03003400400e1840744030f50414006107902080000f801c845000307200d00e41d03c800c4031002c2c0f550a6481680b15003a4603903c002c14078042d000702c6400c00d0b140c04c1c114109982d1400040081c290040c000c0381d0200c9820110007518401d46910312a80c240c607400140c5410b030414000e503003200200080d000c03507031042c840803003551043c2d41c542008050350145240d4500b1400010005415603410081c1342e50400705000c04c10b1003c0d14045c40c403541944d92810701018044401400701d900501551140c8480364000d8400100150044008244440400030b0403065010800049031600300c40685250003085c0c640513403001c208018811481c044680d50440038890b40c0c09403148a190703a09a0600102144001246070042c0c164de0040c1000f81c0103654808540c00c00400d140c041d40545485047c0400c181100072800100031449900389442e10f501e85401d103004140d07400303030025400c03900d40304a000203c00118648080d50040c1c1d010703200801c01c2e042c2071216041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 213166996 1250 213165746 213165751
    0x91c2105090a0902120f15011416060c020607080108060114180a020406170c0307030b010215010f0501090b12071206050303040b0903060106081510090b0c0703030e0f130b18010b0c06 80
    0x28111b00074040c0705070700035040300d14005a0713030074281040c240a40c0f6841c4203840c014000c0706500b200701c400b100b40c01d0191a8001082090701c3d40c2c25a03513140c0d00c19a040d1b451400038054620f442d84048014403644e40070031901407141070010100e05589501000d440016003040740c5c0c4414990300800d00b00809a00315011005280c4886141e9609260841d1780788110b0000504640c20143c9907803d1401c0c6034000d004e49540301d1820300d407141080d80c40b22058050300d4072030300c05c60b4005100c4080004035041d500d802d40307050072000b0340407100980300c17007404941480d041150306d03800c240d4501000030a0380c0d04000900040680868203911a103403842050304062059000c0400e03c5240f0b4200441080801010a4200701c21a1a80c4005c4a951404c0b104421243c02859030300500081142403c0c0d40000d9200481e88269115224450b0b1801404a001c0049040c1c0d40c1003100c00350200242c4045802800b190400030300103018000c0c0190040e19190000e81c01568680c10008005200b00800c1c0900756 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 213168246 1250 213166996 213167011
    0x2010e0705010507020117060118091e050402011b0c0803040e15040605010921150905070504110a05032203050a0f090612090609060e03091c2105090a090212 69
    0x182440e03821717000038105000c00c600e060041410310380042c1c250780c0254000d080e51404c29000e000c107903484040c5200105209030f1003040303421011041420f21040342c0101880381383c0c10b070350300500030300514204444440c02c002c08a80c03254a400d4003040310f880403c080c2c4014030f1200c00011150800e00f684415405250012a0207036081440c00d0040780d802c0704160701281d001d605007203003590405164001e840109040105100040175401d008008150000d07160640030314150f9241d01e640300208001c8480300c0140c01e94080003444040030581c0030710041e41e40490b20076640000c030751441702c08500c10511284114041034001c503c1600b02948000c0e00000d02801c0e08044640a042c820b018128008400b41d03100aaa103034450081001240c4d0001d22643d5030181052081d0450341c1a1192650080715a0381e000d2811000c03001082c2e191146a00b20040c1c018104030412411041061138096250300e480040c480c007007000540b152588070542c0000c2850f0100103850301068004100038407800780090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 213169496 1250 213168246 213168257
    0x4270c0e010e07350a231302010302041a041a0a02030405060a02031309270b1f0b03010306020d060b2a0a0c03060204060e09040b060d0201050909040302010e070501 72
    0x50005600180919030024100c1c1406140101c0704045003a00e04c11680320342c0c524044000a20021316014120280511902c2c40280125244c417600e04201500ba01024000300e440040820540781c0300341140c3c0080c030300600d805407501c0e40350200409a24500d6601c0c4821030310003e420403203c4461055001141081c0c5000d92914800307002c029540d001d0b5000c5c4912039140000c5000c070281c02001101e41c0e19200c181075807c0b550fa1412400c0090078254001241d40c501605120181c500703c501d4010303419030044103048180c4584d16085030044d218140045121100b81020424500a0380030394000d510490001d030b903644150b95240300b070390015441911398000901140d0004c03215203110805085140d6415101036203100c145519118155401038244918403001100f44280c40d001041590b000d5100e40380060394117010f0101c0e07c18111009400000c0c10404541d2920303020102c41c402900515159042c10000d0b0300083c00e016044e50100c0160395034140e4101310070000d00444000b8902420304 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 213170746 1250 213169496 213169499
    0xb01030b180a021314070914010c05030d050c070f0501020d15120f0302030d0f0204090501050a05060f030702120a030b010e09060120010204030c030803090106120213090204270c0e01 80
    0xc0c0d40e1141035100921590030040c1500c601c1600d1743c000c802d00719007401c090003203082c0000c000d010181d060064a04820080d1759404c143e50151040e40c0340a80d0000042d490100050f11440040c44050800500880704008030804a40b03d03070243c0342124010800107903105021040f1904490071031182411600d08101c080104801d0818110051a08548000360740704907450228114401d200702204103520b050110301e1000c0c040d9003d44296014810100116600c81042040d03800c5688911340e0300120800071958000c0d501c000be07540005480c011100790030740102c030100d4150070400d1204006607607500036141c1c40d80c0c884102a031403c02515407614504007600002c00c0d50000445030012050301c42e0300c44024800035030440e07008540045140e10700350b03164030301044240e1003900c18000c0b96003000004611002040c103a80d1003541e0083c03125000401c0c44642c3c0380139101e0060140d03486642d135080400b0040e0050120031010808000303050304140e040ca00888121400e030042130328004a03500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 213171996 1250 213170746 213170791
    0xf080a0603110f012304091a240408060712150b0a110a0503030108030a09080601050f13090c03060606110307050d0c050f0307050d030c03140718120b01030b 69
    0x140c8841d10303042030720351a604100e0f00e001070700c110541303081910300040c08a00f1000003000d22070240060ba1283d01e818403100090100c000180e41c044000d503a801820042030340901c203587c82c404002038a40008031414943c0e92003505003005000c03a8000c010540e8061045814a607034460912030181d1601c0c520041c40c10b210050300c0c2c42c014100c0282c14004075400200851504001b100c0344c0c1c6600c00200c035969a1036040182d03d0350020301642d00403e00c440800b2800716404545241a904e004d40446010119102040300d103812694568003032696070042d84010031440880ca4002e140102c4000c94818900400100711b491240510381c03550308103010702000540c0215000c1d001c81503a16140401054900b04141020724a51000c40035100008201d07042140c0802c990201c443c9a071403c0003120040305060f003c0c0c419000b54400ca40195400041429004440c0e160a4090f01021002d200e42c031035001041036280600c06031421410380004000b0481c40d150313880e5101c0a0703958500000403403c030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 213173246 1250 213171996 213172013
    0x60f1506080a062706170a0f06020c0f07210b0c09040b0d030c0618052a1002100f090507090207060b1806090a021809100b04060f080a0603 61
    0x3000100041e01d00462110a403503003000d0041c240000e129000b040300c4690786a003006004041036016401d094000a542602070404411000c920001d002d48018030341c0e40e9001e442040404584d9560300340900a941c110030400707e49005504d80c014100c1600385501085403907645c04107441380c484402010800511394050454010311104200743e1105100d0001134042c200c102e02607a00300485041d4802070551207075140ca00b00c6e004050070811140d290b845036411700030006024099034003802441258580c120b03408080e1601c4c00b1000e01d03501018000054184859001600c016406405a0300d02c03444503105056444075105400c000d0a02c0950310755890b20f159205d00901c0c0e640c080361500c24043c00d50000c0c00302400003041c0300034169100700c0301640c007081600d15a0080c0d030300400007400e02c10705200b21040d20070100f16a541c00d144200400012103030080100e519030343c5407a4000340021500014201900c62921b80040060342c101c0000c002a0300141228859030800c401040494202c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 213174496 1250 213173246 213173249
    0xe0606030c120c0d0b0f0106020a08030720030408070f080703030e090c0405090406061404050f060d020604032312090603010b07020103020c100c1403103303020403060f15 75
    0x2d640984601045100d080d00303241c203441c01950450070300c0030030f5420010b094084c0d031701c5101c03401c0110489036201c0d8000c9a459543d990020000d075402c0022401e40b80c020130300d1403800c0f041c1c11002e6800302c4210848078150b070029444526243d010f44014062074035090090000b81040c0d400602e18549141c81c024100b03d60f040a160107420740b9404619155140401c0354090034021700601c0840c14540352900051085121300400100b288032110745614040c0200c0307019500c0510100682c4d198032081200440e01101e040361b021004020001c0020003546444030110191601c0c688403016002c812400c0c500303014210000220700304280303211580c804042d01d041d01c0c1510f881c00d0f11907507144010703002882008940c0c00588500d00f00b15800e018540c0041603608107946d241d409058070b08900050600007558940c24010741400c060008158202c05142662010321356003202c1c0e40c00c0307000d080304480c01661000009400043c01d005000c0c0038001d2214401c1e403050100600b46e00d0415690311042035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 213175746 1250 213174496 213174499
    0x917030a080c12010b1b012309010902030624010504080d081305031803011107050619181109070f05120403031b0818010b030303010b0304030504030c0608040302010e0606030c 77
    0x2207802e000d2000c0980b12807251a80c409082541c40d207680d205640c109000201440215075042e0000c0748042c0034081c1d00c00111003081980f00c4c07a00c801c0d440c040c40004d0141d802c2c1e43d070303582032400503a40c10003115002d034503035054085402c50340c10b41d41c1240c0c1034888819410300404100c00c0114101c0051050a943c21034034203c041c98444910809148d803800e03202134002d03c0041141490078585010103120260300320f0007005268141d1240080c2801190070140407074004800003a5110552a115000115000c10016240031000c0702007403c0c00c0c00c1c0c1c0d8151075030f84c0400081c101c075043c03501010341c109409042050a50b88403a40c02400c500c101c503541a81501c403807012800b014065088686032190707048821407080d600f070318010540f040885da10954070090505407008502c0601c1141160000030300614a16800c18400400756440075204404100e000c01c00000800c840807400c0c00601101e9880c18160306103428028255440000d803030341c40c0d40001050025070741e000a01c1c805103500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 213176996 1250 213175746 213175757
    0xa020604060b0406150305070207150f0c1104090c080c0d0209041e0501020409020d051608010302011808010218121c0f0519020a02120a1502030406090c0e070917030a 73
    0x901000c24060200c681c08400448000c20302c002e40170341c26400584c45900a542202d83e925641d40980d0000502c020203500458003011146010600c11f903503620056010b01c940002d40c01251010034202c0b05105010f9609503010201804540c40610240a0100080303950410010698000607902d07040a031005000407115000110200040464211000c4c0c010f00219145e40d500c000d00006940564070b806081494100058100320903150000300da00a0f640d2041c2c103c1e070a5600540b810b004403540b4241001c00d19400040110090008010305071340e2441c03811851416000307104501036038075141a896000500c040e803040d454051032051050b40da10304868910148102603c480c4185010160307801228001004002d03000102c51100c544240c81e050000c0d0329504c201a2912250035000b81203501c11260280d85218580185800a00400c0c0000d607010080d950004801c8a40c0c0c4100d00d1941d14404100215412a0f5840c0c0204980c0650590b070f21941c205064580c4203010900d410f026 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 213178246 1250 213176996 213177011
    0x90d0f0312091e06180b15030303090d03021c060f09050a020903120901030207020a080f0606060301060503010509041104020c0a020109141c05010e0a0c03021f020a110102160e0603120a02060406 85
    0x22a0340000d90345c02204100100d4003141401e08200c416022554403441254a030103c8429007000422a0300c102043c00c040e00c40f106410808401950000120a40e514094000002040758034031441c401416044410140036207007043c282c00303840d0000c001041180c81404a4089520086070704d440210b03007500400d9850b2001d00068009000c0c008000e508051001c0c0b02080803c0005801c182d010614411a8401e40d10131040280030720090007910002507007400100501d040c6030f074142d900300303104903d90342001c240880843c0c203d07000485605940d03485003014200f9540c110841c81c6c06495101c003020107040802020641e104400d42c08030f50562048070ba00001e000c020340c030036810b610121082e505c200030607040088003214540810382c400e8080320742d0103900840d82002c2d041c0c0c0100d60307005000442081c0c0caa50302070f000020307002c1d4103501851061a8080809003840da0160441c024070300a40c0c1041d00625140c03141c602015400034204002201c24180c0014074198010303400400440c046 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 213179496 1250 213178246 213178253
    0x30e060301050f040e031e2a1b0d170a08150102030a080417030702060114240703020f06090d09080a080304140f010c0507050f0105220602090d0f0312091e 68
    0x61003007007104e5180e0040e103140e0300d1224468078028000040100d2a4014800001d625a182c0c8c40c0f04910700c581c50303400076940030100d5001000100c0680c0008082000e801c807513071100d448141c0700000c2840c140304001540c410441d0404407070381d00505042e5a50010108085c0044d599100e001003c1050011040003d0104034403403c10600d100c0d01c0c00382403526410901406991241c007801580b401051700d6082c186c1b103003000c101e038105210b864500c0a00351200078004039000e600c0844250b0031070088071860b006500c0c0400003e80108230040040c588030507103081c000d010310042e41224441e50071054408000c07071014400e403a0040e41160603406110b076105241840d1240450805640b5401d10003805a0150403001426950f4040d0040d500e651780341c1e4104e642240c00c12220381811440c5e0160f080e80c981c420b0005d80303580700d06c20f910040c60256418001740004200031802c4078160143d0012804055004910144008058a09000305989561500310320407541101c21582c56444031040d0071b1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 213180746 1250 213179496 213179503
    0x3030b190f1a0c071d0c0903060f04031e1107080307150b060c0109080d050108031207031d06010b0903150f0c13090f150f0e0a0203100f12030e060301050f040e 70
    0x2005500d000b1566205d0341d600e80c6002c03464a281d1521110350310040050b481d2040c001c100c070f09058009000d014240d84c0c0c00c1582d8000c00000e00309408020055400c0c240010b07080c0c44e44a0340e11783e140c803000a06004141841d1a00d0019000010207801c00d118141c0059065800320380d0040290f140454a00115804544940107841e2003a20541c201207046051102900042200321030104003444260f80701c410243c7d4a10801c2d0407a1201402500020444c0340309a200011070b503488900c3d440801400700c0c22901e00402a0000c020a0900240b0380c5100d10341005644490028210820300d580350007019a001e82500600107030004000251101030b000e006900c0350050b00220008204545000701c101005001d003004095002280c12804210070801121351f400b11207604400709216514a01e250b8040e410141c6207500c032505842e00881d40c04040250800902100005400a0106810002d1500150400182c01103100f0030051090303845121000d0a04c0c80c2c02d940120319202083c1c0f0640c035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 213181996 1250 213180746 213180757
    0x1b04031101111b0f060703050306041d0106170616020a120504030602030109020a0e15180406030203011b0e0108061c031e02150a05060f10020703080703030b190f1a 72
    0x100d0081c41d90f9600d10200046019074142030549014404c9400f403c188801482041400303408036030140009050343c5829040300d08034045120a910052420551031425102d403038002104101072140d81e440c0c940000c00546620220b440456030840d252590080c1d2030b011100313030161112402c018014980341c014012a0b00841d4400d20465907980d40b0300c4c441c002501b00018040008030404403821407841c040c404040303082620311460f0300d400800d40080d1b200741e200300c980d02d800588500000000d668280f145007411442e419030048003680e40e100040818480401d040c4c1801000740600c1100d865412101010030f014801c0c034445015103082c01d440280c84004000f4041c00003100d80e02540c1e6011030000c02031100407246084946070342d0215000e0f80c100b22142038000c04055401203003490004c1e89015090480c2c016503441c1030701d0351582034160b03210103c15000b082c1c1341c0c02c07150840c1c201103000f0300881d051840b9150240341804c0c03820013400058072400030072080c5240d080c003005e030041c800c5a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 213183246 1250 213181996 213182027
    0x40b09150c10060303020c030607050d0905010906060b040e0c0705030405010302032a0c07060207150c020a0306050709140915040b150309150c0315010c030c140f061b04031101 77
    0xb8849404005900050403950104030300500840d071810705c803410005071103402108552512420003c0307402041000b0708804800707a404d903403107000d48000702d812403250001a044035000c0f10360b41d45c241490143c190070003600b88400080108080b03400b1500100556090f41c400f46005aa01d841c1c0452000c0400008800701c1070410364102c0c0c0c1d100007140c00340108015a4410150354290741d4800c41a81c0b5031240344140b0310180d20318486004614807440141c0322052006214075051074803509c3e8038044440440310307007010a00e00305050024007409005074115000841da406143e00d000503928510040190302e450190791902820b0820baa22284070030808142010070365201d16000e00103603a0b443e030900b5550b05a00086011501017a64942140c0c400c1003080304104e0380440703880c01110b02204c028415401c0144186000d030004034501e0b411208481c02c9001014134501c007114160900b200680703c1070740e03444030188182c031050100c0e0980b000c50f038208828011a040c000c0060719801078040030407 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 213184496 1250 213183246 213183253
    0x506060c010203100602060610020a38010f090506010f0e0a0b180a080604020d030f05090411070201020c01020c1804060b0301050702330f130c0f030215040b09150c 72
    0x50100c0c4c0c041e124500b01d901c0c5500300c450310307182c0009100545c00050758680c01030b009501034030b001c0782c203503400c0000810555000e11803130720b03204591030400b20b510700b405144e4040d01e500402048881040c0b901c040d2010b014108170904041001805c140e40151500042c4010081c0e5400d0b0381e40c031065010700900e40b014085954021500d190b440e104413481c0c10600c61900c002011511610008405200b5903015003101c4400c240c07501c0a0740e1034074900754494108103040054002c0c686507401400045200b0405480d00c85070750388006428281c0c11146a8110341c0a0078820b5083c0c3e0b11243d0010005110024007421502c50341404009042403c2070241c1560910040c0000103030b00040300031400466806d43c4000304050392092803141d01102081c4040c04d5400082200c0142604c007094110001c2001040a403c481e9544102c280895103c40c50001c0b03114820410341c2004020621260350309940309113440d0800789c50710301601401c040b103070103802148140c0c001048414200c0303d1008265088 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 213185746 1250 213184496 213184501
    0xd020301110f0720060403080f090a1205010f0b0a0b07031412160504060503060103020c0a170d0614031c050403060f150806040b0a1a180a050c04180506060c010203 72
    0x750301d0b90b0f074000d12040324008010b002000c00c0d803c20400003807401c00010903040ca020b240da29101d41b0354214000c0c011603054100048200b176590102074000415825030800d8a010050600034211402a2990500c513030078000302c0d04c1556100050b54040c2d58551401c0b9840302500d00301114103405120300420003510000301a440810004003140c41401c1c2554503a801c4001c40c40200c43c107024521418000c6023051003c40c4256000780c0140a52134a08e000b1581c00071132545400c043c0d850642c40003440d0b00310000c2d03c07200c1e400302030080c040030f04041d05905021400e124003113543ca400c8803540140b0520900c00c859040e078482c9085500071a04a00f05100154008101c0001007600a500c10025075029000007802c140120f407031445160071940c40c0c0040d90b01d030007076000a03000c010241401068041c950036401c0e0b40b0311142c1e00c0e011b900442c0c086203602d01042d020040700d170f01030549023001406010030001d40a14282540c44803049000126850700c40401080b423034040e01c1c50440c3c203540007208 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 213186996 1250 213185746 213185767
    0x427170f04120c050109032d0b04030f020c04060302090a0906140703020a020d090b1b071d0f1807140a03060207030503090c0a05060405062a0609120f090d02030111 72
    0x54029482d40100c0c039011002c4e6441c0300649850304c01c5d100090165000c0220308194a0521070300d403c5031000c58643d00e01e21440ca90725015401d604071000c41c0407898120b04680031030340c1001041117407501510204145411500080d041610003050891444e4403090810304000d9160084c00d02250420604036903400d0215000c0d010b5080115080014410b003605a103144d40300e141440121005181c000e032030325213000a0a09040500c0051403c240301c0d041c000034004000055000c1d04101d030880141080c01c00500c450303200c920160401d013460b0400000500240f01c003080000488003400d160b86507031191340d80412102c2c0465030000c0e29480c800300b941c1092540010086201e001d0000940c0e0402c010b09041198507010313409002d4005030240000d04c403d0900c17600034088050846034080b0100508244050041040d881c0345c2d0080c0c0000060003030590040051400c1003480078821030804801c91001d03140e50050101240c400c0620820f804103540b0207504c41c000c0c08149440903541c9000e50320 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 213188246 1250 213186996 213187019
    0x90227061e0d0e0c0603010315090209190615080c030406090503120109052a36120307030f0c0201050c0a03050c070f050f0603190504050c0427170f04 66
    0x18940b10340e0502d8400b0040c0000480d00e000281d10060816045900395110b281c0016000c0c0b01c840b00c030942d135801c0240942e44503e500344c815160310240203200828140c484041d1142988400039030078140001c2924650001003c6600101840c0c03019182e50b40d6050000c007500003200041c0443c000020003040300b00240401d82d069660400d000c2c0300d940c0721400c100c2c9a0f00d00313080503060b60a5001101040e170b4400100200b482c101500c000004000c26242c5840d9401c81e00460200c030066006551322382c07801d003030400e0b0f40181c2805015500f400c006031030180c0b800301000c2d4000100101e00c1484421a8080c8098414207403212080390414041c600d0058040d5202d80c005910394402c0c07441c000f415004904000341030700e5002c5c08004a5604070f0052000ca904042c11604201c58900506091180c0520405210b10b010704e0082034240140300900048a1444d4042541e4401103800030140140701040112a03992011000b0780e06022244101c0d050b0003480c401d05100c071070000d00001e480b440031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 213189496 1250 213188246 213188257
    0x103080a17090d08100801020f0c060606040f030b04020d122a0302120a03060302060c0d0311090306190e071d060103020c0d0f170a0c0801090227061e 66
    0x19100d940300010307107950391006030304200e81c200c10542c0007486400050b0b11514041e5003084040c0310b400f0071252200300c1d20f800c0e42c2042c42c800f10248030108083d18821010403003e500300b94191102403406080c0b0190740c00e02c88003404042c243d8039600021500315111080035152850704441600d0340030034041c50080215212a00e10440030410401300b4050303240d0f14002d084803a030f02d60020000c15164180404042e00211400420300d030341c4000000158071000001c2050301c1114001e040c0e0741c0081c2c14041e00f00c50710251204880d50092020250544002038580d420003012084640703a41035000e803903005840690500c0c80b860040d4440020420400d03812442240c5205002241d2a81e8042c01101240200c40c0d600c000e41d808803001103035450090000030320303174551840c00181e030303415080682c071071000c060707414404042c2e5507a60355110030f61100695014242102c0e0661030100482e05100724007040c80c410182402001c0c008801c3c96540c1c81c02c94290903400106102d01c04241c1600c2000d80d0001e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 213190746 1250 213189496 213189517
    0xe0307020a031a09011e150b040b2101060507060b0f1302122412160b0306030c0111030904020f0714010606080703050105030607080c120109020415050702090103020d0206040905010308 81
    0x300300030416425041c0946e842d9540542d02c075034464402942c650014201340c00b401c010b03425030b9190208803441008024400f5000e40c00c851584c6e180f00108141c4044c02130100ca003c40c001890051005503401001c44040d2a001000800d100700741d01d000074101210200e80950190014030140d0643c8441d4002c4e01054a141142c002e455a8214052200600c02c0d00c40b10031903010600203054130700d0150300742180c200c21402200c11400d01d1441d95034000e0301c1c0380c0008038607240200401605180400003085460001c0c6007800082801139413290f034070701402222521854022908801e4100c4d1102620b000c40c0e0800c0111401200711840c45008026a00540c0006013200000801c80c40c000e0080d5412900084d006050941d145030007100c40f203101500d13244001d20f0401c020044c3c840010350711406000380160040e921032074841c071900282d107150135001c107100c0305109500c096a0f42400044c11a40c054070485038500c5144002401071049411a00d0010300e03000000c414040200c01034514880c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 213191996 1250 213190746 213190793
    0xc010f06060908010621031103030901020304120c150209010c0510020a080708100e06011b05011a0d05190204090b130308102403230a0501170a060e0307020a03 70
    0x111859000e003611001d020306c1205002031035140c4c500458504244000500910300360508901c4041881d040d6401995800e03100da4000c030501c003d22010502e01c0c0d130401c0c0c0900b441301742c0707401a5a42d00b1444124403c0c10741c88503404a040e00d82c0c0c0c1d009018280d01503a000044d00c40b403403c101c034014000d402490500b40044c80c0e54000405547c0141083c0b030140e003544404601480c40d0000b1550080790041c00c1904101901012160400440340e0f500c001c01d11030313000421418a011003102908417007143e002d1144440f0070081c40403d13001701d00c240500d150424502840c11103800802d02800d0a0800101680d010704208092956a084007000ca40d10070381d60031189407200440038148a540d03005070200500c47c140c150703070000ca0000050b03508051608020500050907200103c8440312104c03240c00e4a2202401c01807043c03041e109a901621401d0000084040b80c0607050ba0b480080c41d4008141c9581c42a170803845100400a44958503801450401c1c110340303a1400b1442c014020407500490711 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 213193246 1250 213191996 213191999
    0xd0501061a040614030408070609080c010f051530030d0c170a02090f0a090902030f03040609151119021c02100e13060308250c1a0c010f060609 63
    0x5070701d081100e046071615921000100a065a80f52055101801c1200c941d00101308420014401d40039000126000e598040d4540c941000302d5820358946417800725401d031a01042191510342c0c0c0000100b41c510666000c104038601301c0f00822140e080a60f29950301ca0007444810085500100411841a0b402020700200080c0c0300182c4048410082e004112405400064406420340d4007901520030002c2c0031001086d00c0c000490001c0260307401c081d120319101e074940001d5082c1080b1103603410260704000d500d010301d81407000705410440d01030244030710580d2070b4600e081071056540503120500c01d0285d80060304185458050b0b8182514204c1c0106500c444a14080c140c0e1110900144c2e0090b00c0e42549888103e41101d0b60100a22901d602100d0310905810000940c030a00340918490b40d40c4039520030046c41c804406001707009001e201d02e51081c00c080f00042c142c420480858030000354010188000c000107468602640041800c658602503c001000d0266009141140d0040c1c641e0402035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 213194496 1250 213193246 213193289
    0x405030f010219020703021305090c120709060e01030b06060309030d060608060f0d05070501211b0e0d03050a030908070615061e1e020102040305100608071d040615050d050106 77
    0x290900d2001941c0b10151f20b000442250301c0b42c00c27256104580b007003501d0700ca00002c0e0014a5401d00c40070f5070b4a89511031030041c0a000320a2140a020340b01a0302c0e042d882e58595561103020540081800340205004008104000420816251070210445003400001e482c0d1300700030b0008200712000c621604d4480000c00d260f081506501503c04d400a02078050326080000541c0c1156400032200b109407915107035034802d14041d200ba440400340c46096401c8034116500002c00b4001d020307800c0ca1185561f07008110010703403c002180c00c1c01d070341800d020680d582c150401841e075008269000c3c10a90800c80103041c2e64604e00803403006e403811515004010081514075001003110400800702260000500052840c1c0d2800c043c0028951440054646501d0b80c2e60300b0b05000043c4004821a0340b143d6060040b4032050146502500b81203007c03400c03000c1090f05600c0c4d0724402070310103010703160398000c0c0360b4104e41d510a20102408001e85103194200003440d00c43d000388590310031000000c0e1a0f003414400e6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 213195746 1250 213194496 213194503
    0x7030801050103090803270709050f090c09010909060b090405030712020601080c01120e03042403021303030c050c10200d021e0106080618010c090f1a0405030f01021902 74
    0x50903017042039541540d40340e6400504000b2005400a80101c400c103102c10740440401514010b8507078614045282c0c1001058041c0054002e042d0707401c5078000707242c4514030b9107804d03003180d044407100074011a40070b4117401d0000043c15641101600445448100014030000000602c5690722804810514602082c2c0881c0c54010a0264405c56000040041d00c290b1207241c0101001020040010b881c403a900a4107117141d100c0c1e4040703540c50114004181700c1030400d0200302d0344105c041c01e00390b01e019021246101800c206000040074070004810100c20f00108100c086603003800900740b901c0e40c0f01c2c0c540c805800490107040b10606010030f4240b103000c9960200304180e503500181c000f442c080c0c2c080900080f24801220108142e0f40d40c5000024000c81c081080d24010152200400100300300305a440f425110100031101c180641074801300b22a1140021910403075214030350000000890305103132240780c0b0a581c4a164980f1603002c0d007511000044d4001d110354021901044d144002c03078281682c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 213196996 1250 213195746 213195761
    0x15050327070b0a0807030b0913050102091002160e07022e11042c220b19050c03092e02040b0408190b060103050406060b0c07060305070e06071e08030c07030801050103 73
    0x4100492341c0109404010003516903180d9880384001504040304a0f010034040030044a8440050748003141031551040e45c0d1200c000a08100840c2c07a1a9140001c8003035078075004030901403005000403655040c0c2e203a204c802c102ca100441401808681d0740544d166041d0b4110340144000410740c240c030640381c082d03021900403100780a00203940d080d0f0340b00c00741a070482c001c250b00020714440d88888000081c055243d028800d5856642c2c00c0810b042283c03038107088840040c19061407440801c1070000e01c8500150004001d00003a28040480c61080c6504001202d0822180c082d00d0000c1000300d0240110f10281055980490480f00070301c01c030f41043c0b03200d5200b0200240403240810f0126019500c02d40150794458004d03200071031070356075520544105a008012020700c81c4c015110034000700350f0600885820200c2454000c200381d60080000d9150310824000601d400301152000d035401d19400c41751520107400c401d01d56260325080e059803400d588141001c41c00142848008200c540c000d100394031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 213198246 1250 213196996 213196999
    0x1815030f050702160506220602030c0606010f020a0b0a020d0204090b0f09010320030c0a06050c01060609060504050402070c080610090e030f030a05061f0905030715050327070b0a0807030b 82
    0x11038040c41c0c113007401440d80c0720031f0000644144d0040301407040c103c0d2009a9004116903802155140e0400c05e1a908006000e040300341017100c1491213004441d800a40b211010b600080c00c140123443e001007000092240c030f18904603e500100f400140d200c1c06500000092409070f07900103290202e4001c20140540c01d00004103400c01004101c1d031044142c10954400043c05000c5900d0700c80300000141100800d6030003500007900c00030755941441400c0c00b61800030055400c000c2a102d05022024205002d6800340c540a1680420403038180080785034080f0042910105480701810700203403800b01e402c198002d2050040c10520780750b04684000085860505440704210708649139000644082c2074003800b9180d00c58141210482604104c4807082e0784520540c81c0c03000003500d0030003490b007002c880f5030022144030080d25810018540101c2200e600040142d00c00844d101c80080d803680000d40e120401819124802011440c2c600c540c0013400c100c403681d203442d615680c4041045090b199600e4109 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 213199496 1250 213198246 213198283
    0x20a0801091a04030e030a120e09060f01110c04060b0406020607110a061a041e06090506030d110a0803070c03030b030c130f02120907060801050319031815030f050702 73
    0x2e05030114042e10454129119180c40c61148264100103443c2c00c030140b00a40790405444591007200740c100d23546014840c1c098510124610380a00020804284c83d00b5090602103540b030f071008078071828050f6020303541c2e00420070401113032100601c0f0640e80003070007008054810074000c2905640240340030204070740100700505c50141e055544601803d615a00c204040b49016040c00070b2355150b00603c00600140e03900c507540c0b0201d0002d91000d407400c0d0744c04814000d2400d814440c0381c2c0c0b4081961440c0448034248843c00402c04280c40d4507140c510440502405000300500c07034100e511031100c1050b2030296074144421280c00302010b469000c40d88600c0c0e070003501d8103641d0031401141c1e04a440500c0000f14014145070030b40b11008090701d012565081c29800003c414800260007130700c0c01380500415802085208040301c003c80340001004005014030080e0304505c0b2400da1001d0b2080c003e0400c4203581403c41d009031401030040e0070b030190001d04807402d04c800240c3c03962001a26040d01098000d18 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 213200746 1250 213199496 213199523
    0x50703020f0604080102180f040903050f1605030319060e090604020d0507050d05030c0d0201020a051204021c03030b031b01020a24090507060e0103150e07020a12020a020a080109 78
    0x1c0168400c09841d030305410203020b0000003003054080c03001e0070886403041c007000c1d100001c560400c90120313107911303165208a28100c030010210740d024003514400c00c40c4248aa50303a00750700b140840440303102100200b15102c00020044010380702205550072400303244041c00800d440711240c00c2c1d4110304440f001c032541e20a8000801501d000210075002d01d008500303845503903886001242000707009000c1540c16600008140c140003404120b064026004c2d44001c41c14a44802e800406a109185c400c0a036404582c000c0f4040d56501c251542c003030440001144a00100c2d8680070b00605010800d0b02d10a00602c840b901d0085d581d001d2056090605070b000d070400081c1959055200c2949802044145801000315210700c2c695208000c03286000340014031036203140a9000706030402040c2c1e410304250420300b40d1070604014601803c103559046d01403580c0d42d5030341007080746022000c2360040d0150102c0c9001061954010881c0c0900c28001d4a06850507512100b11a0a84245010003005202038811 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 213201996 1250 213200746 213200749
    0xd0506040b03012f0a0509010f091206050a05090705010f050c160e190605010c06050601020118081306050c070e071101050108100c0f02070b091504081b030a05070302 73
    0x1046510940080000072000901c20109003102e00e0000c00741c080c1214002c10381110901884029860300c400956603181c1021200020424060109003605100281c800400410300a01102c0d000d480101740d85503400c8503609002d0054441a20310900030380c600804560b401201182e41003d03200107131030340d207204220032a0440e0b066100081902c4940142c05000d00c140620984620041a490004c0c181600348a9a030805904490410780e01d028900002040280d8114007844006504540005182d90350000140d0240c441941c2c45810303480240300308010131198070041c120901074096542d6000f61504810303191441030300501c80080d400180e0030131119000d204c2583c1e1041041c0350010f44942508000c03401d488080e0440c1c21940c00290400000080c0f0303100340b048902161420301c1500c00700450207515032400b07000341c16542074006003400007a100c10000a8040c005000080c1ea100e654074212502d416943d110f039001030f04004445111490001003000c41c107900b05025007009440c41d1f0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 213203246 1250 213201996 213202001
    0x2120f0c0105130b03160e011b2909010606090b04051c08120702060103051623010306080f0a110d0503030c0a030906020d0b01020609010507210e0f071d0403050d 71
    0xa8200c83c5100300c0b40d5021940b4038542e8069406006000325078040a40140409402d0b02c0c0810f80340390410000c19000c4036194200c1c6055118190845100d5040014896030f503001c0d2080032141140f00b0a2074002e00070710000541c800c504549159460031030342511103020000c54450340c41100d601540300b02c04445044180001510400d00c2008000c1c60b20408901580391000c04454040140c2c00c10b00c010820302c4030a03c90741d5085494242c1c1020b604e424104024a0070429040b800038a844c184000040399010380c0c00100506070071811181c8003070f003840000d030751100720703117001c032403004800b55402c407d07007841c007200c0c01141d50080145080d0760b21602c0102c115041044400c0c00c0503240d498040c0855103610040801245000000c1030a040b044006803403c4400341c20802d260f032600d1304000c10b20740e000500094030200d035400004154608011500505000c4104040d180181200c03010f40c0030002800104a40101030742c0080d60b0072011070400340110846003c1c002c11010007040c144c3c0d00301613 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 213204496 1250 213203246 213203257
    0x30a0b16271413050408070507090605150d0e030d0c090e060307030b0703020706020f0409051609062f0c010207080c100e0d1401021b01091e080408030f030402120f0c0105 75
    0x14140070f01d00000b00c034050b4151401500d041e01c0d4404002540740c1030000a11170440a011030010a000403841c2801054096070301d000e282c0c00b11540469840540889074000d0010140c00d003086a48a00414485100070606500c640c80400c40314180029640895181b880c8518030007005020160315644a030b8410040090503182099800c2165100140741e40c0701130280308280258013516141060024800c80324080c00391010850341c0301c01d1608850788021000c040c0d91441c64244104c1c00c0e460490400d4000f0894407c0750743d990600c03540700031180010038004d2500243d0840d9001c681c0c0d020340645408801060a8010301024002042e0074000c03480c4031403c074005000841004c40c0b03901c443d00080e00720010102265000220786010150102c80900007004d241d0080064064075038441051881c000281030f0294050b50b400f4086c04130807015580200790400c162175072000300d0210825954001c9130201c0c45541103d10281c603101c000100071a24141e10f00c000e10403a000c0d0340055a03030b03801c81e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 213205746 1250 213204496 213204499
    0x30a031e111c050c16030c05030610150203070f0b0a060608162a0f0201080619030f0f0c0f050102060a05190906020d020705010b1c1a06030a0b162714 66
    0x100031306100b0443c2040351205c0a44811303283c404ca00d00f1854500746140382a40141e210b688040140074040318140fa20504441040d852681e9490b4136400590650140003405400b06d040320860200340301d0304945c02c0f403007240700716010851a03481d8082510200c0003a60001c500c1c400076221079a820780207010358111041c064400850210909075410f80398840b07903000301c440c41804a030040855800c40c8880380c200d038048039055440d50504032030000501461001a020881d01040300d01401040b14102e05180d070042164a041303034440c10b450010fa40c991003181e00500c5043c000400010346886854010310a4140b03800b2a0300101440d80007038003903c10141c0b8510390030010018440d64520003041c103584548000b044095141040025004116042d207000840341400c2000082c1099462002098548201c216546030600030900e0056207a1000b4030b41003a030002e1203030754140c095015041c5c0000d980d505010111080c00864003080794203405070301c0140302100b84070130000704d188010708100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 213206996 1250 213205746 213205757
    0x5060a03030c0623040501020d0c0915081b030c03070e090609060d110a08161202030a0f0c09060b04210c120204090501050f1b09030304090b04020702030a031e111c 72
    0x200d00344d01c601e01c0d04207036000c5801d0780d030009003a20610a640980d12400c0554200460700c01d25120040344034a0710b80c4821800c1002500c0002c82c568000500c1480e96260801c0e000d4983c54417210700d8a00307500c140d4002000c2080205010040e1504411a510500c0090405c060381c0e100c0c0814400307080144501124035042d0300801c000c0603141c00603883d000b005004000c0001105a031700c19245030074182c00c561004615110b004000d610001101d83c0510b921402d00380c0300d1010360400d4001041c458105850182c2000c0c0005031402482011b4000c0c2e1304210f1704844142914907000300c60042c09503005058081c00030302080781170300a26511400c0c43c00034001044690407540c8013400c4400482e043e6260307000700c0003807014041001030a9a40030f42800c00d000d141107207d00c0060780c4c1e030182c0c1c030400300081e45031903049485440d2a010b8446076580501110b40c0d4000d81d00d0090b182121562001d081145000000782005115a814000c003010343e02c09081d890041100001640e81c01003c218148407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 213208246 1250 213206996 213207041
    0x7060b010516050304060f0e0d0b2206020301061202130306020901020f010516080702070b03010915050310090b06150301050d0206042c0a020327010e010c1205060a03030c06 76
    0xb00c182240e207414a11400c0656540c60810780041e04444c107240b501c104011003d001200d564958460203d50190046504401030342c1c4c3c0941103401f0032044c08030090f920010700300042080801d40256058807051748070303895882100d50440d022400307960901216a0044403080010880c2c0d607004100603030341881075a908440d940041801e4580a59081c0c0b017001c0a0381f407041e1240d5128801c0360308030b1680d20103003003454603280449245010600070032000342d50b103203d180502d182a100c40380040401401380d42201c448040003400601400710181e0706403405000040e814580021030480002d4403000300c07404d40c0d08113410310121028000341280c01c90700810000c100d00800b030080700c10f5010504c421400303843d0182c0c12020301b03d901801c5d8100c2c0c1401841032224903200303041050241100c00c1188610168503d8190b40502403848100c00c0c15464002c003004503a82c00100f00c145010100000d2003e52901d03401e0147d48a01440701800107200500803070300141207a0004200000310031001003044 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 213209496 1250 213208246 213208267
    0x50f070b040c0f14040b1816020717010e0106150c0602090616080403060f05040f080d0f0614010e06090312030405160902030a0e0a020a06052a070611010207030507060b0105 76
    0x25038035400c21042c4c02543c1005007140d00d030500940005000a031500c0d82c0200700d85a1100703105401901d41894680f01c140d03904e801b24806c02000000300560b01d00007281c601030309a41c42c028045100c072213825500b0500003060120784440c4d45210440244d031410304036901912404000d40110216950080b420007024048108006481001500410185664070700d10301d4a80c1c01c03190302070403a0801c40e041a080001146070341c05101d00c1c07240c000d0b62942e600d03965040f0000061034403401410402d482c0078004510f02c0811043c002071902e00f030720f0346030194041b0f004120f001d00410001d41d82c540e01c000810100c00f007400c1c000e1070700300d03204100321212615005182c6001040302c5d0014060240e000c800c114111503103005294500180c0c80c040c100c101c05580209071000041e02511052241c00905008440308040222460b14071000030400e1034120a8096500c030b10ba6842010001403610504035044c01e41842220342d802c0c0e15445862401c0300564980024100c1094400d050220511011002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 213210746 1250 213209496 213209519
    0x3120f09050a140901170304030f03050d0c2006010b090402160807050c01080609130803090c030601030f060c0f0905040b0103090501020d0e0f0c060909041707050319050f070b040c 79
    0x15000c001500008400f00da001c1c081100f070164800002056003030b44a4103804c1011045405aa03040102c1c888000c4503810140d43d47d21503a0f04d004a07013489c014203243c0c1e1039801084040306404456080c070403141504412030350380d28203005084004204100078121840c141d40105508501110003100004e0310b522448142c1d00034060944894020361003070100c80d82e000302e00981c0800704484403401800c2441e6200059494000e00a02503d800404034120304130130030042054110080403147c00f0368407460148046e01011008803043c0b418001003a0310329000b64449012001c0a5440040840c913282c01c02c0003800f814a00c1e641070581d11650580411000e00080c40b030700c00301e100d000c1480c0000c0c0c00301500e004040a440440780d0800510b0312000c0c1d84140407140014030440e9001c4140d00e4a0604030b288032018084010f43e80b41c0050720078200800400a0488440881d280820040c4000d10554251140030328101d0506010801c003000110009811900140100b41100e04251210406000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 213211996 1250 213210746 213210749
    0x90905060d0212010c18060c02010c0305090312070516030b070c020a030c0602010504020f0402090d0311030f0735040501030e160906141008060907030b0301050c0306011803120f09050a 81
    0xf5944440946a0b441e80281c1c89002c80e0ba140190007140d9850100000e000c1d42c00c4500c000d040207034038003600c01414401d034203490128400038145e55180a680b00c040c3c4d055805140c046500e809131b040c21408004080202100303d82c1c01c40d031036041c6540e640008548144072848100d902901001010002c215101c0c84500a4101074000049078241401080008036808000307620441c0104401001a100c850100e04d5040d4103042c4100c600c1208001141180541c075141000030001207401c00c18030040741e80d0380c0d64541c0702048401c896199900a01401800500009903d84080000300800c1d4800d6010b100240181d40545000c0700388940756030103030941517010f10711540d02e6101c140841e00616110300c0d42c00408403084030b20003071150009403032601c00500c403900c20091000010119806034004003582c47d4028020012443c040440e02e0a503081a0f440e035002684614425a43c0c4c04440e0400007526008200c1c3d000720310710084215441401c1402080401c0302c130030000201915640c1c480790 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 213213246 1250 213211996 213212029
    0xb09010f120f0507170c0f131a040302090c0a020a080315190503100e06060616060c03060f05010305041a090f0601090608120412030507030329090c0a090905060d02 72
    0xa52420600d030010718450401c10480c0d40030f240c4405004d040312148013280c8000c47d24152403515448030185810060410303500010703540034070049451071000e0b0807008009980c17084030ac0342181d0701c510000020a020f02444070003d640702109200100301001c003d598088080482464a4034658000c9034010030040c0110007074014202c0d040c0b04c1e42c50700740b00070703018880210b00400c2001e0090715015a22100070b80304501520f40080d1030501498002101c941c0305804c004240250045101c0041c0203195a104a954225503042c1c00302d02d941c0300380249801ba5803c80b040448186400391040944080503090300c441d4450300540d1004100d051041c64003d00b000c00c0c00003051460300e140103007042c90003002746032150820402486003200a004588030035405113060f5843e10628030b001c0c0d0090083c40601c0130903541001c0080004c46902080101c0c0000507a002c000317985604070104264000c11075050b004c140e03811004d0007000342a5112991091000301140b94202054000c5400b0b00c080d0481d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 213214496 1250 213213246 213213251
    0x130e060d1b050102011d0a1220030306010f1d1e0307030807020f0405010302060f2118010c030612020f0307171e0304060507110d1b06030f0203010b09010f120f 70
    0x2c10440d80c0a1203150810b4144500c2c2c101c040c2e00b1324001e1526680f1642004149155a409100c41c0c1e0380705000d6600d00690400d504085c103000703008115580e400c03ca03049d030300142042880d07101ea81d100d65111940300300e00b601280681e05000c0208100f10a000c80500303000e81078200c098489a804001540c0254003801000f41c0e40d0b80c0034010300110000050465015504140c010001610303032030100d42c540c4250790b4445031252565040c1c070300c0c410340c40030001e0f840d8240c03c401c0c030141c461100d03d002481c0a406008202ca483c600c4801c1e0103403803a900c51845891404180d802c05420520301c50750b560000142511101501c5a00c42074012428240c00c040a0344020782007406202101d0100008a848800031420185056001003182c407462000404d191307050303c09585280c031501c00003040b859018280021a0141c1c4143c08500c12036071003800d0010382014292040b80000340301700c034161419054101e107007140f0400107403070700c1c800055040708001c5d1540750003940c11898403540c1800323000c46001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 213215746 1250 213214496 213214499
    0x60d020901090605040e0a030906200717060912030c0a0c02030d08040203060a050f041e0c0816050103090c030b0714070f030e0907020c040c0203070c0308040e0c130e060d1b 76
    0x3c2c4070480d201c8900d602c0b0f140d4020001c8202181d004040c0000b1282b091405120314141d4400456881c900c1112202c460310a581c40400d111440341d0b00d031002c1e5240003084680b1a03462035801c50303a0b030320900c0c0c0d244468113041001c95241080007000b494284000d0805c0241102141d0101c0d14011490b40b4540020b41414140030861409200741038011640980c10700403410b01443c84011000c025100606401880300300103d10280c2030071402d44503030014401d803030607550b40c0403080c4c0b03400d0200c50440c01880320301c10120301c80d80248035800711190810f03000401075086076550b18000c07002500300c07000c0c000140111040c0c00d074000c000b001c0c2c092281003e985540624600940300c98506030915219480810402c040242e0004066002040468003c580030008407002e0782584140031000e040000e4610700842417088002c010811180900c3c0404403940e15030011141c98014050050740303000d0000c80030400300b4042c40250b60040401001a050f017419582ea070000514200d040d951400d030765010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 213216996 1250 213215746 213215749
    0x31204150212070305030a0902040618271703090f030d06060206010e060108040f1403070b1509061003110d06180b090c070602030c0c0303010f0819031403060d020901090605 76
    0x101c0d8001d6005144050800f0310903900503085000003070442d040e080d0703a0251001595900c7c0c01180007440c0c14420100c000c0c01310b1400d40040c0070540f43c0702c9000040c40c00c030380c0388100e08039038000101a04910014400c0100d0010301c20550f101800080b01803241c07400d000032898003400100100482a40300045403490018060300341f100503070000006402400130400c007660031180e487d0b072003988542002c1510b503691401c0240100341c02d618a810384004200c4908000c2505081c0b4050550003083c1c4905011040400000704800c0f91480c0d0040c00300c11500e841d160107a00001300c80700c40604200e0038501980300110465405070b1000010400428005c0301c1000305200303903042070324113591000107850012103440f503d20031b403000101103c0e0b000002448801e444030589440ea10508190f0381c4e2565120f0214160a9050042d041c003030052030001424450001008145a5890b4840e105812a0b2100d01c0700c013a000140100c3d040007060002d48010307a03420b46581c0c007038841407200150203400c0c6070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 213218246 1250 213216996 213217003
    0x80a060b0a05040b13092d0501030f1415070305180105040c050d02010e0a0305010606090e0405070608040f02040608031c0b0f09130602120601120510140312041502 72
    0x14051501000304000c02400709078032204440c00d0707401d41910259502a5031905013101409a4481411145840c1d0305900085041c4120756117400c1c400000400380c180b10120004561080c80001c08621119649c0800a0b0f1540c05001f991030003076003510403406110810b0084c0f07660441d1031070000380e07441c0100048641c028511520343e0f1590340080005140503600c02d0401c91682c0200c921440401c00034004680c440c002c90b290310f54000d0030181107580d07a13182c15800303001e807401400c02184c1028404200d408440f03503194401c0d03400c40003c01c039140c5421310684245901a10944210b4007150071500541c60300d0061400422800000b140d48a080c409441010100d9031160201d01e410500103202d540c0e214100e10602c100200d034140000e0710740c45141556904610002040d185c00420217200300031060005901c81c0b4801e03200c0d002503401260074130b0102c6030200da41241d02d81c200c2d00d00780511008030004c80c001c41000340031500030b1158007003080720356041a030041c1c8840405203030107203c641e81030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 213219496 1250 213218246 213218249
    0xc0418050a1404020a061d060408070f1505070b10080f0a06050601020d0518010c0507060512060a03121101021c06050a1706070302030601051b0109110a08150606040312080a06 77
    0x4038802c0400d8240366000948071000c3d032003054104100c1450452900154449145124000801c82c035030320b41e6945489502ca8003a03201b03004500c001c0c60740000d40d0a4500003d509a0740003a91000d10b000e03002e941c0e014848601410300140102c12120106440d00c0404c5207000d05403140d0021b001800d550318001059540c010441e034110b422049000706525005010341c0d1510310710050075000c03a0003070b400490381103020803406440ca01c2040b00004501d40c11900402030852034084000050b03070740400317000309002c1c58480145a01c0424000640c628412500e698107940b10200151515016400c02e05807810031440c908045583d900f805c105900c0c1000703180d002040f1141c5184034005001d45070039210700b00144034105061300000029040d0384690116800d600c3c114150f01e440103c0545034074000c0c046900c0c1201d10004080c8080228648040c00200b12140c0c02d0003001c500710091228140860094881904003005010110004030707400510415011603941d00505880c041c0d035150b055401c036 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 213220746 1250 213219496 213219521
    0xb0f250c031b15020c040b040e0712030305060f0d0605070c06050a14060922050709020d02190e1003021303020d0605160518010c08220501020d0e180c0418050a 70
    0x2240800f0016580201d03c1e64580301040740c00059581c4d003d404a00501075407000508980143c10000c19103248016504408030f00039031f0300b081141d907807405003c0d5600c0741400c200da0054010b002d100000380241c119a50260721450500341c6501559a118191303002a210788080303a44034120003040c1c6d00c1182c0343c10b500032070441c2d9150482c2000f04201c008442c0e10b10410344901d107481e0b1020180441040101d005113340c3d4811540c82c4030409060000f9000780b0420040b50341203c1c000c0044610940c000304030300300000c0c000108007171410420303402540b00705001d911400c0c00400001c0503a07101c3c2130b003281041c001c030340c00704041c130b08105081078038150b100140e000e1000600c6802580c448800350204c80038401c1c01d00c80030211550500707507024012ba25594060903003203042d084003000c3d02c2c0d8408044510030f070221000360303031003050541e0b1210f0f00e00b500d90b400c810b15504050b481c08003a070740705030000c5d0394480240c40c207034403250b103600c0b01d4034989030300c69480341ca886c24400110303039034420312081c12007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 213221996 1250 213220746 213220769
    0x501141219020907020304030503070f17030405100209150c0102121308030c0a120c0e0f010201023f04111305010302030d0f1115040605010b0f250c031b 67
    0xd10225606071400300d032001034003501100300040c1c1c0f014000c00031200503641207011070b074030f030503032403078181c0d444107074031201302d4200a001d850000580d4481056a000e203078040c02030281c0b80050320000009401070780807654050034481114003280e00840003045401034500c009a99918203050b5002e81c400060030540041c0b4000e5110004149000150381d01300640740700156840a030024100c548121000c51050054a080585064a40c0100303404c001d0b0203003a1502c2c10546040001a07080340200403400754141042e40402d0b0b0120b4050310031444102d80c40d072038103415105c0b2600300055a6011201110b5402c40c20b07410a0452521245002040386440414019507040d580444d484100c00445001407022514900300d0707080c011051061507940d03042c00c40d40085d100280f070340010036003079406858680c504000030601d082c400e421500440c171914503080c640165904606940b02d440302c04400141111382c0260000341034490404021801000200705802d07500c1c19071145108150710081107003a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 213223246 1250 213221996 213222013
    0x608040c0603020309150108030c01060b0901020c0f0d0609030921120302340201080a05010f0302090c0c010c03020301090b010f020d0513030609030816020d02030910021005011412 79
    0x4414a0392502074030703414036001d61a5141e8556161805090b8842130f103080b028200003280515001010b060200c041c1c000034803480756507990a00c540d1040e00c4075580182c200c0070344140c00b802c0401d40410040d00c09000d04a9014040d2141d00c200c584008080300081c42d0000100103103001c5c01c4194001c1d20b05400201212010340c1d455000d401302021081091540126003561903d0021001d4001c10b081c1100c0222505500c0c0c4c80b00501941080049001c03c0ca624003052003e1003511840c0d0503140e0050100c47d8140c119000c2064042c0020803244440d2400c00100412860078041d044c1003017001e0324090388a50501420000381d85000d004a41001540002400e105074001074016000a03541030042e034800c14104145006403c030b800c05080c40e030912401000f01980070f40c3c600d100703480c020581451540c228074101c5c0c4a40c4581c100500590040c401003800d854900b0458051035010f00445042400c0c00361054141c40302644650031b440c260341c0c0394010b581041c5407079030303030b03000b9007001400888 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 213224496 1250 213223246 213223253
    0x807060906021c0507050109111810121506061d010215061909020c0d140705030d020d0207050105090a140c010819060f030b04150b060d0917070f0507060804 69
    0xb060714041c42c05040020f000c1180c50a4000e100301c07012141c00070000e01c109141401e0100d00292444622406280e101c100480c044900e0b80d0000d00900704144050103040c0740400e141c84090244105858169901d0a4181400c0c0715120382d800070103c80d201d07010b4030790b280301e00842c40c00740302c0091a041d9084070001e00303025141e050005601c284200c070a030030025256515480203003c1d98115590360b40c40000c0000c842400003d2480309501955074408640d0b1a28071840c1041c0030b81d0317100802c01c1d1310a00c00c02400b00d00540150034200f106040060408041d030322140d09494007600c2211035a0001c0c1c1040c4144100183e02d040303000603a000411142420310b0000b400c14200521581e6412282d131824002c0c21620f4000c078004244042c92001607588a0071310301010b20060320100c138500c0e1070100e146c1221003580100080c03003000901d5030341041901e450100281400800840390f82c0c2951183c0249000312201401c00c0e203001da991103510141d40d1500c1440c1040581203501400003000412000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 213225746 1250 213224496 213224503
    0x120d020f16030e1203030f0c0d02040303081f030206030109240611150603150a061a03010807060801030b040312140702031209060108061303030b06070303020d241a07051501080706090602 82
    0x411003030140b4982c8c9080c07505605001c1e22100100d200e0002500005050340a011140500c0081886403401070540008480c03140c0103220081d04010b06000400c01485554054500c4c0c422051291440c00158034421141038400d40191011842e031a082c468080802c0080c4200340340312007440d42031820220b0000c0d5031404980703040304500403200d00041c2540a90313000300004000c1c10682c0c18101c441280840c03080d40090184840c24854054001019881140e9480c1240e07000058040544c88030307201264603085e88103625444036120b56403148a0740c0c5034200503200340b1241e400f56032100302c010311905007111f004d00440204d902c01c0300144101c0c040801c2d820340100403003a0030150b8800301d04d01503000d4500750711800e500c108081040014503030075400501c0c011680501c200849141450203030502e80c5240021900036640c0302041c000120000300304516210068201390410710075685241c94124502c0702040701100a800400843c0360400c190b030050400d81c1040d4000b182000002036a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 213226996 1250 213225746 213225751
    0x902030304090f090203010212070f02030310150203091806011b1509021201060602030306011e1e23040509010608070c020105130302090405010e1e120d020f16030e120303 75
    0x24480c0d0f1809060352210303c55121514684e40a07009644a801d04c401064414908680000100e00c0006c000000d462001c402c6a10030810810714071040ca0510122146450829054206502c020031040d00d09a0f20082c005a100469034401e094903e040b90005154582c01007203000c100d1b00d40c080740070000d040ca00c0da01800b1142d12000064114150000920034013842c51443c009510b042004104191701100541c46a80280c903207000d003030303000d62454410740c114414000c00949200709002c1382d5007207844010400a424034110503080ca54003101a001c50003080c210402520008080000d82003121200d401043c9500304484c05141c03482c80501458690032000703040000c00540321181040c0c1071500707400b03141c0180c0000000d00d40b5140c454020305000189110306e00c18065038000c01140c2051003540349070800090184000040c0b410318094020408442100d902400816040340d2070402418240c400440f40c80b040c0011810042d000b07a9482042901809a0750b030824400340c2d0000c2200d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 213228246 1250 213226996 213227009
    0x513090809040c050f0403052409190c08030c06041202030310060e031f020a090504230c09030a1a0106020a0b2823010b0a0c140f0a1a07030902030304 66
    0x40c407944152001c44d014403a0b03480704820b0400105021043c40800201100c05c14444454000081041c032240c200212044a82d1040c030741c40b9202e5207100001e00440e004103030b031240e0540c094107522101300d01c1c255000030b03d00071060344c8648100800e02c401040601100110b5001543c91428a40320281c0d00d01582e002e09420300c440d182c84640207450401c00407510070398000d0105401075081214501039400048100c00207034044801240c0e902c0c0030f10030b6001e16081c0d82544201c01c1105002140084001001080426404e0241a4803030f1818048805041d00c10040c480000c080f9020501c03082d207068103e10f0455119800140020b00d01c4440250001c140000d00d42441d03071200040700d0b50880e0403441e8850241032114002d02c400c541e13000011503503142d10b56040700382e072a035000f50382d030f4008c0300702440015007040d64070350108001ea02c8a43e400c43d0341805948807005c42101c410b107014800d0030221207907070414403003003d03030185c040a041e08500c2600c3d0602800c1501d8001aa0301d004600800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 213229496 1250 213228246 213228251
    0x10e0a1502210a14040b0703030209240301062f0a0b100e010b160c0303080a0b0103020c0a020f2815030203060a030813031e03030c08070207091d0a0c051309080904 72
    0x1a035096010030a54005004100c045641d40707c00381350050113074010303888103400f0326054140b000708504100c2039041c444920300f940b01c0c11a86000ca0840b030700900c15100388004801c0784281c00700c205a83c1411404000d0000c003c0003640090b2074051002c2a00816114850b40300d42814401c44444071036841c1142c61403110755464045a2501c0a214421001e0081110052900c00001c05400c845103601c1303000400c004000d00c9040341c00543c160700c22180e401c12070b074001d035901000502d0000d030310800142000e041502108494482c1841d4550580c0d8a100c1c8290807210400c07182d401351220542d03404662909504500b80040485c00100d100c2c0001400c1c404041650b860503501d842ea032000868012041c2e0f90801e046004005c0d240b2854070098001900304120f00c00f5590043c03140303c0c002c500c03e030300419095103091035060003010b403002c0040c021940ca00000469403010862001c14074051070b15100c1c4e807450001000b81a450300e900010000d0b062042c5040403803114001d5034003404050718003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 213230746 1250 213229496 213229517
    0xf05090d0f2321070206040309080109020a1a070203060c090f0d0807060509120a03150623030402060706090803100812040311040908040609060206060103022502010e0a1502210a 78
    0x1c0070b4804003034503030481860300f008200079440384c0c00600a400f844c00380e214020a140c40d50380c064241c682041002c0d40000c51402c0c204601840e0404c10060940c041084c80e04208540d40040d0070810103441c4403030820004600000d06251144c03e104040d0411500d610b07000c241640d82940d680034880c405444540d4500009003011418011041c000e4000340b450341e0b45d4245900d0242c0141400182801901944032011130100d00801d41040008070302040081d603142d4002011040c0d5100030700c100d81104041c0040c1000030b415000e0b88003140e12807120756840c3c0c0742c0b06034842d000780c00daa40a140b050b0b102000c03d251142c410703c1114156604490350148002d62000130030090184420024002d450010340020240d5200c4051b406840d2203500390342c21611081c00440071390082408a9141501e00403044088450890040692078818100221800c40d0180021a031501d180d0241040110721000c034981c5660500c9030204001000850a88000d0081c02601c4140148500710341404a00202c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 213231996 1250 213230746 213230767
    0x1e0905040b01031407020708010f0218120f01060f050405060109030809010c02031f1d030403080f0904094e0806060d02030c04050103050105120d0e01030f05090d0f23 73
    0x51003071085003103242d113150a00040003075645415100d07001440d441d100c00860f14007403500071a1011010945000300401c103900405c1a101c4003240d100a030341c800c29070403c50004080c02040000c00750f02c0c0c0b400b440c00b1700e4401480140c0e40c000b001d1071304020003294140f0001e4a5001a6202000b0038a0b0000c02125144003003490230b501041001404000343c00301c07110050b40c54105010003503001085010b0080c2c0003103002d17902d001e540002441c0500600c240d400054005000c1c003d401c50007030011410001d50389955004403401c2c22203030080c0c800030030701d07002512000c80304485030300d01c4155101c024214802c860303c0030651800b1340000c006806021405950720001920704405104408550301e09007203410241c1540b0901c94180403a040a000068034074210612442445140f009016900307044007040320b90016501100f414107a035070107240c8002c000ca00c5140e2080920310028008240c6d4100c018124140a4410300c2c01c01c00c83e01000218184900c0c0b8803a00c004c50b002042c0d8071451580c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 213233246 1250 213231996 213232001
    0x20d020a0b090f0f280302070e0c040b0316020f070509010506032a0a02160e041103030f0a05070506010b0705190218070f0909061412011116031e0905040b0103 70
    0x860140302d10601213150207581c0c0104000c0e00180e500103455000d11442c06000c0c43c4030360b4820003c1d015801501041244840012065a2108c000001946000d842d0400c00300c0c1074009503402c5003801041c0390b210001035010000da400401041c0300400280d840c1c880064130307400050044078090301010000c01e280d404260f01c42c41081c100e0f812030200d850482c85d9199030513045600400018400c181a600c542c100e10100358003a9610003180038602e07503a58803060503400e20120010742500c0100400c10101200d5405403051401d180d84080e0b903000241032843c035050043e00708024205080120380000b40001602500014084a20b800500441e000182505010610f049581440f400401c250168020300054524503a038840078400d40e21140380c001121120300070f41c030040f03007013143c8801c0900c1c4c1141d0b85014024400004503000050b0503410705560021144c90480c0c011080d0315104158200c601410301c1c42511820b140c1c8064900401003441d4200d2044500a507550b05110030240d2198 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 213234496 1250 213233246 213233263
    0xb0418020d18060b012124060315090e0316030516061e09020310110c0d08070f052503110105101409040b070f050c070603090210020d020a0b09 63
    0x10414035020000002da0704800c6802190120b151032103201c40c0e90b000d00e6134002d0102070014102c90900c02e40039140c004083d44904944c81b480d81d0104a24484140e51540c03000d003441d0754001c40c4400091660005158190700311a44840c10496a04d008650000c107540b03400780b45c9145030307082404038101a901c40c4560341d0b62940349130705070860400380700c025080ba100d0400c100755410340c185800d2102d5000c50302002d400942c036401c007010002d031340b01c5243c21401242d08000501ca1070194518881441c00c4807240300d0b0f001003289041004086500b01540441007005410a82c1c5044411507080798180321451386c5e1030401400700301c2c0c44e0525219103906401c083c0010700030082ca01f00460541403000081c898110310f403d8620701d1010508040e0500b41c00756a1005448101e5110755805403080704009000c0c800b0018140502003176040d04112440c002c103140d4900007040f09103801030240c440c1068545400350b5010003100c0041c01d5000070032008458121904105070340b2140b81c03840c101100ba = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 213235746 1250 213234496 213234517
    0xa1b0909060c080a0212010504020f0409050405010b04110a050a140408010c080609010501090b120405031201120c0e07320409060f090b0901030b04050a0b040308040501150b041802 79
    0x281269201009500c0c0e10611200711143c036420096603440384020143d00c110b180c070a0f0100112001000242003e402519400320301d01c20f803908090f00d1301c1c80c1004035002202c00b900c050391213034a210348504091081090f0b5a0703107003000b00d01e000080c01c0c0140003403040002140410140265004228816509540141c00e1501c0240103030001c80c1c000504108082d40d1391403207184824000591907000300703035038000c407038501e03403040d041a40c5031200c128203031001081500e40e030008010702e08103031804040d0103019004c02c83d0b402aa510050506000c4403c441c1c1208a0030f2030440d0501c040d903600481d103020040401c04031905030300409518030342d59241d0070041000901000c14041001e09c16504481c0a940b910914460115030f00d80030041921010140035800200e07810042c40030811100c541c40d44680180119000f00b2201d5541d0380854008a0701600001c3c071940c14801005070038001c40c07541400c1102048101810610003180900c1140319258010402d102220303c030003816010759010204 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 213236996 1250 213235746 213235751
    0x2090408070314040b130e091504050316080307170609010e043206090a0305030103170f0417160305070501120609110301030507060c0f0303020711031e0706030e0a1b09 74
    0x151146500001d81109030007846c202c0d20b409011808080241c04c0740d00c544440c40003010b0900d0180f0450100c8800500140d8403400b0804c880c18482d03a0000041e5240ca20070078806641c0d01d002d0f00003c0004a01e6816061955a00014017041c3c1e03903505100c0c0c0c192112903034800c3c2e1544852030045e01802c00380103040000c0149059405c88001c0c98022500501102003e8a07103ea45800c0c0660b22220680c0000340400c40520050000c5490000682c0761040144c2043d8a401212513095009800a5100c46240045503c0c00b00c2d404e441880441120103000b84c200704610f007540d5400c0e0303c400d441e009030742c10008403d01c40c101c9401560445402000041003c102400d034000c50030b10031340e0090009451510030310f800002d40e28490148003000e01d4008181351600510395a085010f54000c01e0296605485400420f20366078040c010300200d800090104a0a4100c1c903400c2c0d400c0001960141d4141032508686407591803020501411150b48064070b01071412600c2c03210203005166411a0440c1807 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 213238246 1250 213236996 213236999
    0xf120a0b0a06050a060c1a060616110f0f030d030506010311071103060c0f12100302040f050703060807030213050618010303090302030106150e04091103011a0f0901030209040807031404 81
    0x401c80d404071041d144103807410f195854030b59a0a0715056001c0c1c0000b019441c3e54560581902c010009840d0001d900a0516150105000c581c081150007483c040d0341148002d01c6521461400d1080303100070b08410307218081e00d1181040026154164078104805150712400014500e81c03003030380050144c0b05a21241615880319052040900c2ea2094000d8001e00c46e410100ba00030719080c040c2c403040003011072114982074007010140c0342160b0160042901618011002c0011b0340c0c1d41c064100d41080c0c201e80011203280101c8001c0c165821644003410603002514244056243c8a0b28001d1484000b40c0100c4c49071510030105030b483d94a07001e65405064250300110030950301145503400c8a0088000b888410344500002d400102821400c101144000b459045241400d0700191300c030a000720004070070101c1d800c02003401c2d50400c06103001c01d07a0318000c503010346241001600c58450790a440c0800c4540c11640131501c0140003500c054840e21002c40c0e00800c140c030912464030700c40e500174085522203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 213239496 1250 213238246 213238261
    0x1b2a22140a060806160c0c03080720040b060706091406010314010c05030610120f0203010825080c01081005030304030807021002011a04090305120106090806010906050f120a0b 77
    0x4000079650780301075506041c80016160f00024240d03015204030008901d43c41618001600c0e8840361800858040f082050000701189402d400740621a0041030000900d0441003065003142d02d0903d02d0901c5a031601c00c3ca014181c40f00001d0f1403c40d9840800040d8800301420113101c00c8001c0700e8404024821071001004110029000d444081d000d00c0080c41180000d03070b002d8500f400304807450345d0411230552565000d60b1240c0ca454000000400c00068488001c15600050764405d82001a213540041203080d00e240c0e228010f42406d1208156070a5041d080c03045040c0c4031041030107802d04002c9401c02052640a151201600034800101220b80c0c0e29500d24000380141c1003450180c0c0724083c00b0842c1620030b401070240082141e00714030000a450200790401c4001d0a201d1415401c0000034440e184509103090b02040c003034107254a45a596a21304808245442c005800001c1d5590903c0c40411550315140e964440044048a046c000b050303d40001038908440700801800e208080e0b814031001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 213240746 1250 213239496 213239531
    0x706060605040e01090b0d020d150903110d05030103120e03100c08011701420b1b030c030a0e040905031204021f080612010605061b2a22 60
    0x103c0e042500062000da03a1007110b00b0071940f95110a60b00441c4207004180103182c0710b81d0105149104521000c545141d098000d01252503041c0110041825a41b420400450411500e03000206500c0c1591556040da42d40307a4403030070240d8215042c41000c0030042d200d540d00340000030100407038400802140903140c000800b1000c0a118016035401260700e4000b0225043c000d44411900c2e101094010400d040e20141d207145080f800307900d41c13104104418008284a004000052400560319a1120600041001104114054001c0302d5000b004260880360011064590801450400751480c07004440401c014110818004109010000307401d1503840e0100510b07800b841c020b40700080d01c240c07861035054910a103805604046001d074400100685404021255448244c03400420360543d20b2000c40da454000000e802691042c55a04584100040104850800796039201c005003913144054220503024140318103000e25010140b441c4002007400780000301402c045004c011140c0608010310702d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 213241996 1250 213240746 213240749
    0x10020717031908010e0601050a050711010e21011406030715030603120c0501060501080603030706150f1205010b011707050703111b090109020301050105090d0c0e04030e030105060a06081b070606060504 88
    0x200c000000490384031f510a0007035a07001c06031030700e4180c5010340c00c1e1164884100c85c0707044e150400c410014440740b1600c411000c40c51038400c10340700040d44020850300f14255500c2c401100000c0603038004210055400064110840322424450100a4110132080300a0091034001808005102504e61081548504404c0186e030041c0000c21005494034011204020203603050760381a403090148138041001c1d40d03c072840d2264600070a1000f40d99902101e003604005502c1505042d070314200303450a120b0300380100c400d694400d00c2c00d03010030300101c00b5041504401900582c10024081081010540a4046142c080344003108680303d24002004020001d54407208aa000e00030200002904451a0090341c3c162241615928200b202440c01c2c400703186041003081d240114400d20000d007442410090358091170081c0d4030700303912103075802c24542903074405003010f8001d110888042044540c8a1103460704181300246004101d0041142144640a01040a0603041c03801500188040c2c01400520 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 213243246 1250 213241996 213242009
    0x14010e0402181009020c0316060209190608191409060717100b070c030803010315060b070b07030e010608160e07020703080913061d04060b1002071703190801 69
    0x303100d40c41d0007082c1070800c60565801000a01500c0709001d1181240c000d401e1518800c0112030400c1a0382c0b030a00200042c0620582d52182d0000d44003404e8108040c00d0710b6803401d070f01e05c84100540f401c00000d01034400240347c100c144c041c84000345e5a04800360004944c115070030780c10043c141000401203465041c1643d80101080f89400800c9410100341d410034403c000e4112004400c40c507000c0713040007580c040d010480b2508078241000c0009042000698003170b500034000414001d00c0900c00e04101c3e0201e4225404110050100c2e00018a0481da6603038010181d01e070215005403002c031814090081900309241c1402140c00c040c005580321110107080300c05504820000391600c1d42d044c4e88624460201900050b03040144800e40c1c141038408400c4211070220000d2001e984030003400d408c1402000b0300c05c20201c03400500c0244105402103407040c01c0f0494144071103540d909006551000c1600c64001c842e52050802e1418010074010b8031a1000440b0030004494106203000340460f00901820 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 213244496 1250 213243246 213243259
    0x100b04060e040605180c01080c0307020f060a020726090f0609100503060907110a03030507050904060b09040e011109190e040c0f0f050612090a0c1707120f0807050114010e0402 77
    0x4145c0c80758000b031010070b9000d040e100c0d60201d8403804090340865000130141000d5114400843c3c0c0c010200f00421441409007680050b00c41c581c0c1e01e03002c000d0940f00001102d044482c0641d09050f40491000c55551300421210400d06d410742d0008a10540104c1b180c455000003403400c4644d20a400000543c4620b2041700c16064507558548251501c91604120010302d40c0020410300000b0701035071005401c280c080c1001400c0410650008080d07814035000021509008180c5c44014100740c010740e1241d00342c0030000d2002410590b116042401142c1005108988a5043c400035899003050b2034003420290440301d510780f0701420302d0141c4400310300c5011202041034000003407001012240394243e41e802400c03103240030f849010100054001615000c014003880c0e4a0000103803000ca4120003c1c00c01820184042d00040b0f807041c1055050390081c210148801140c4000a40711211918020391100b0000d449140718107045004114000f03003404a10b00c9880081400f00c2c2c240100b0344640c0c802c6680 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 213245746 1250 213244496 213244531
    0x1006030b061206070c1a0c22081b060705341401050703020c120d021608030f13030f0f06050601211107020d14011b02100b04060e040605 60
    0x740b103100d942038090407550b40c0211011400b15441860940000d50041500054110b000b0800043c1c4d80380c2920800c01c600400945c50100c0f0f07070380441119160b02201f0342c1c0c080c0c10340b8000223152503902e12160b911280c005420780303800a42d00d90041c2c590b0310b03400030219042c010720349102c00c501103070490070840c0750042550a0030030f880e15012024103442d00c4258201400a40f040155995002404110194024100c11a80944a41401e040b5203d10140100000100c1a101908040840c0500807403c400007000b40410b0310f001089404809240906c296941a85d5451025118007a00020145052001181d0601c52099031080e906801480d04102d02d40310540107480003802f4030a5842c002107155201001098a0b900c4041c0300050406214644000d9900203446201d41e4103041f03030041144000c42000349824801c60b02240c141180c042d100320110500603507580130000d10042c1c0f00c4e44070342c0c2c0030400d9105d5801000081182040941c1c1c3d604207450301c00044c00d411940380c075003034501440 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 213246996 1250 213245746 213245749
    0x14090d0516031e15110f0a0206060405150303040302090c04051302040915030f0210030e191406130618020a0305011e050c0909150d051b04050106050901050c0c031006030b06 76
    0x2903241c04d91100c151301c44021602c03038500240c2454046400d02290511451401201c8200200098500c581c080c0a552411a040008a0780007400380c0c0c4070072828014002068800000310703010750f901102c0308105030303035280000140d503c51900034542001c00d1001d440d40348181038010307009a60b0440000e02000040021a0a9100440c400a00324480c0b0003440f5000d41020a8030005100c028900890034055132202540741011b0320b031243e0009041c1044071802d0003414000ca500d044041d102801c0c0904007800071070000d0180b54000b03800326a503245184655102e45400b162120b50107001242e00070741e241040c2e4000c2c0440d10041010203601040055611024854140304180c1002d030181866500014800d0340c110003400202481d41c020014402541c801d20800001441400203060b4501000b000411901180c4000c2e8011410a0014040640c0001c02e807150380c0b80a19120b5103c68003080b121f881e10b00034801c03068150040985101412603150000010b0713a004400d010500d8a4900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 213248246 1250 213246996 213247043
    0x3030e011b0e1f090801140603150a090b04030f0210151206020706020706050105100201020f0301090c1803051b0316050f0d060f050f07030b0114090d051603 69
    0x1041c921141d465408100018025140708041000241c01000c000b02c1e040d1a01d080c40150728003100120b060000100b0040000340a4034110811025042180c0c1c00c100b000f0940e01d4000c00035001c031104400300041c02d0050306501070941181c118454440c14202400c0150440c1020b60004006000354030701100c04c611355018400c1d648039020a4040014641030780560540078210048607d40d030204070b038401060550014104060080400064651505003004003040c07245207841c0075a401401b08184007980e500a40e411030f0325500020412036001c040480d803c0d40b000140b034140c115107003004018010001a07401102e0021040e000d80c10111904055580341d21844c40d5000d00c0b12101c051002d81000f505540400c42c001e001040681c10707a54810b030036503140810340d6010580e1103081203618150502c10a0308500303241400c02c010120031000030f00c4441001107540c1c40010015903030700c1d03948a800c0d07002ca03086d4101c03054034800d62240702c00c00c401e00c080e0f12003520003082c104003d41d101c80610 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 213249496 1250 213248246 213248261
    0x30c1a0712020309010f020c0d0e0907081303030f1b090506040f03060e0712030210060603050f0f060111010204141302040f0e0a060302060d0c080114060a0503040503190c03030e01 79
    0x98603411a0620760140280203584010080c0d030300342d502e41402a130b2031010741c00900740943c1043c0c082c1030a00304010b0020b29005650181502c2416240244818290000801034201050920400480c1081d0a00364081c00c0314880f50703141c1030f15106032441c40c080f8910410044d880f10b552054141f9607504108080ca000711301495050254142040000600c4c030b910802240d42414243c400c0795540b00003042d40c02c101581e05401503000b055140038040703228400d00002d04494142005141000c04241d02034130801465030300400b0030003000c00d103182c0c000c6040d440407403c040001e55440e41c8490411040c0f03401c6240003805403100c2c41c50a41140f01e03d00035038041d1150100c6201c980f43c58030194909880c400307000c9139041c599414011015840b40070050074004002070004c255008103c10080000c0c1c0c0503407080160352849080350090365104e104440440c20b403481c0c025100e4035681000ca04510440407200c890420101004c118aa080303400b040020f0b0181d1010082030030b210203044d090300d03607a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 213250746 1250 213249496 213249511
    0xb010e01021f090b010b071119091e1820010c1b0b0304060204242f010e0120090102340609140a050603010b070f0f030c1a 54
    0x2206100400907410801c282d40380306044020600e248540c070755072a407210070707000030000800000e500401c0c0b007003444042800310025036246ca2050011101d0720796a00040c0a08c00e0465101d203202c607903100407183c41314800d8032140c804009c040b40108240501500081c1c045840303407461500b03803404a0503d1803401c02198180c40c2c1b101c000007540c0c2d0f00270080f48096101e100442d142c0802103400e2488101551082e4820000180d4543c28401e5101d10030088000703100459819605079842242d010860420118264a111480c0c041d007680008080480c10858049503280c90340150002d201500106400c010352441400c20009486000e030b094804c4603403086c00740e48000000b030f4441085a003071190b01084108880c10104154040c0d2900000c5a802030000551401062000401c40e040001ca070202c1101c03e2a400c2c2c0ca840045003842c00140b040c0700302e145020591606001d00380329021001a0700100092000c41c0500d009001c0b2209000159052440080151032507440502c686024001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 213251996 1250 213250746 213250753
    0x203040c0b0a14070303060303091403070915091a01080601051305010e0409050a12080c070b0115050f0706060f0e010b2703010603030c0506070305190b1801060c02040b010e0102 78
    0x500d00360155a5100c181c0500c10825451021460f0f000c02c3c1002d062614403075640490f840e4a107040c014426800c98004003200360400400c880103550000b41c1e81c048615004000c29160a2900c41e40c0e41314995900c2403001e40c4c10406103696052100c950074400501c00d0f2a2907407282c03640c80046409008400e410140c0281c0110244010740c041d070380142009400800c0031800c2c2d0300c0d640e2001c0c10010007200890381100c1a0f440d0401c441d0704251699841111140351900340b51180d04d52100c19007041c0f1981d01c03448241d40040769040e103d80c0858401d2102c0f00180f0b99201d0741860640018003051141d01c2d0007021a81c0045070400211000c0c44c12607814140803410311070410a8500d038280d008842c041c8088c8038001070126910700f80180f070300a40c0a51622000001c0394104941040c000501d00d4040500c0c0408001d040b808807442c0700140c1080c00c0001649091b8000400e02c2e81180b00117038601c039840500000f0700941d02c12503045415200752014010031144070019038040c9000103800780540c2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 213253246 1250 213251996 213251999
    0x10c020d051b0c041a090606090d0b1e19050106020304060905060901091701140a0516080a06030516050f01090803220320180f1305010e0714040e010203040c 69
    0x1544500c608101408820a64011401000004044030124001d0314a45c000c40d98441009150968802c1d074044001c0daa03943c90001a00c1c001030104042040c004c0280700601c010810900d2648107074407020b1160042c0c0742060a0118900504041c2e8101007000c1ca030901c0d0000c10014404000c0e0b404072103045d203c10424034100000c200395030700200c01c4203040207040a4000380c012912a0503207001c3e92480300000d030301c1d4080c1c022a046120001c01c42d0859500300005e2001d00c407101c0580084244152401450765202d421062014041951003d842da01c01c0c0300d01d0710310250a40c6840700884000700c0e07400e40442c03403001c010b5a10f0700d083d10860009800c1072086040e0b61880c2c400c1000091040f480b0414100d0f00c076a00d035071003641d44600c0c0d00d401c0003110320900900c0c01d02c2020303880702e052061540e007a149000d150790b0422800c000c02491303512107c07114000070030600b5000900142e1040301030b0b41c4410b8659001080c03820441c0b2840d80705506041c852580d1510610840b4000c68000240c010402d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 213254496 1250 213253246 213253267
    0xe06070e032a19060224040201030e120301060305061c170f040f030f061401030f03030f0b040903020c031605060429030103080c06060105120a050a0e03040308030405010c020d05 78
    0x40320004401080e0144140290b490703074914804141d4601da240506541a042001c000d1800450b0031228107240c0040d494440240001d003c40c5921541c2482e021035900a42d00c80d840c1050030148200c0a90000800003090460700743d00080d00c501001e0b200909201c0005035889240d00300a20043c1404084103e110803075400d810050950040c4a040e03d440c00380d6580d540d441480300780e40262032510000c5800420415907009580d0816420b007002543c1c3c0d411900c9d000a0b00756045e00c01418155503091022030b9144c542c001c03000c0490001c00411840080303060194581c0843c54500d840f0b806081c45911202030b418400400743c54029008905183c1400740381c1d2118000004030384001a20503280e2404040104000c60185200741c10207520798440c1d5610903d806405010325040c0003007401711042c0100c90b00e95203680300c881c5034004241c5031140c820780001085d551031851850b000010340803050018a40082d03000380d11900c000c200c0031582c2c28080781c030752039035290340e00000d41c1c100301c500e40c0d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 213255746 1250 213254496 213254533
    0x315070518010e060c060f070309030210020a0c061b0f0504121410020f0408070b030f0c07021207094107050c07060309030e190b0a020a14010e06070e03 67
    0x1201c06041c00d07881040c25000140c0c040d0441856004e259001e002048404d101d20184290490920b00302801803170080d59010b92a80220042c0344040b9501103035094859104000401c005c5401c2a03003000b2000641101582540801400002040403581c800b840d4500c681c04507012038400322004d2000340030365500d5041041081c00385d10540e11603a41c0e400034030041d61004158410541007510b558902d0141024100380c02c90f03004e4481800144108001140b02c580c05c0381d4402140310080ea170300e140302d10010b038000219905207080c034810100082960f24150b03104036850a8168011040700c035005001c0390301c42030f4951040d8004451605e0307011000110918082d00305d4600c4c10030500782240d0040952608555900c0310000a803154040001d15400c10303520807526405485554001c88907007020804001244a03184c207110700003454a407100d02c207108030801075500104042c44c60b10a00b607424040c15400405880b240101000708400070301803000e1040c00a009001780c0710262074890305202 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 213256996 1250 213255746 213255787
    0xe0d02130b0409061d07080a0809040e030d090503090f030a020d0201050c0f120301050406170a08090f0301060b0301030b0c0301060806010e010327030806030f0a0f020f0a0f030203150705 82
    0x1c202d41c5400c9600c0008a4034000c0d00e8612a0400580c441c4c0c0707803d404000e140c801c180d8024203880c0c001d84095400300301018100d403c0354209403000b1807086204074a892640c403480a01801c1c0f80d01d88210034003040000302c028007040508403000840845000d007019100c0501d100002d5006222266440c01075028101a02c1d40b91000400d440c541014000300c14101490070b5000c4010f80e00000040c4402d103440c0c466000030385a50079004c10445c69102c0c0b220b0b61000c04002c0501901004102c3c840f00307596196691360481005402441f8195854070401c100f40c1080c0012200409160001403400c0142c0302924101c9403107544082035503c80c030006440310076286880d117042684810396108081d000800327805020708902d041511051050030020081c10018007100e110340c00080740140e5150b80001da61922076007140d003624544034a0300c009461020041040b942240a038036000403161504003170441200e000782e0a4031f000b00308140084d10340d0310048841e1720100300309002c00914019000107120303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 213258246 1250 213256996 213256999
    0x908030a0f0e01030e1b0619020105250e0f04200d0b03011104031403070c0e0612070f06110106050306070c0b0f060105120711060c0a02011104051011010b040f0207030e0d02130b 78
    0xa1804201c08c0701001d8009145055002507911074040c440498400820b403000108203c805a45144c06003000814070381d0420882c501c10588130341c036040c4d01d035203e5220090030081c01642000c004036600d00d60140d900068039038018907141c288000010300703060103540004050540085d1030181075545c4c071180c0704072590311904284400c0c400300000401554021015010a0f41041010302e003460030804084038001c422807003600440c4042010303415952001c4c00f65401800c100501000501400e4014040ba0784415814070510041c4180d19400c440d40015007070040700c0c1694207907290001c2f1820301c1c005844482c0051341c100000c080030380c000b100035500300d041c5240c07011011100c0e4419600d004000d0f40c216903071500004001c0c002907024414000310103240c0450a04080c5000300040d03c844402e803c0c1c00600c04880841d000c41e441c203510806244100a00c10000d400d61020760340000d41000e1000c030081139408914004514000e03d54880e029401482404030310300003014907025003903640005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 213259496 1250 213258246 213258259
    0x10e1801151106070e090a1119020f0706090e070e0307030f050f0a03031e2c0f10020406110f0c01031a13050a060509040f0f030908030a0f0e01030e1b 66
    0x450012806100300c41c0135290950750340203c2ca4011013044511030000c0c1010010300d15086182e840c0540d0039007130310390882e001500d0780c600e0702510b08168101131040402c0741143c0a50b04011401c10b400c41108030551342c01c2100801540d030742c200c050f82c3c0a0400031480358990320181040001807490b074003811499119509465100c40c00140c003a1400181e0300045010036200c215000700c00b40190052001031045207800e00c00c240b0303803400e00300240102c0c00300c5103100148851060760110040017514180c0d14088111500c20707021041c101c0003500607000b4440000d113201041c03044102c0c00202103d180308044007401425841d43c00640007003600c16224540b00c1a1a0001081613030341064494030007040450201c0d4505d45107410070215440d0742c1002e84210101800c0c003000c1000b121030000500d034031800074041031415040c1039890380455405102c80b4440058a00c10007940500d40e000c20350140e8030307144440b0b1004030054099a51101907400c2c40d602900b4485034418204450005900014251 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 213260746 1250 213259496 213259517
    0xd0603050f0606030d0e0109050603060a03080a08041209030206160c15170105030109031b080d02030c0a1709030703030216050f070608011220030f1902010e180115 72
    0x5241c14441421106001900008100401801c1c14800b0115200392031801401c0b01c80c0110002e00011464010f140c001ca40100000d201c2d900c440b00c41b0f2002d960002d030001d844442038a801400004101c804a03160945041e018507820302800c0f403c0203407a401401c440c00c0030039100d851400701c1760400d002c2d10300c00c1d1103031070008003400d21580350750030070010b5601ca9900071202985404c944506a11a034000c2c2e00d0000e10b040400e0f40820020081c41898441108020190a10b918140600c6455201e0544000240151800244010200c5511070744174a00c050500316240e40080c0c0d000c541c100e08a8004118600009119600408004a18803c61104507032561036140c07071722125260741245030384180b4050105030b0300444000c1c01088004c00310180358142e6a0780d4410000c0c05002248803945910409416a5013031100c026184143c104940c2500256515492070a86542c4180c0c0828a041401c10351400c1071214100300c02d01400342c008450340b034841890070007950740ca07030901006480d024 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 213261996 1250 213260746 213260753
    0x230412030615020c150a140c0c0306010f030b0f0c09010302091f050c070b040807051201090b240405090d0c020a0305010905030d0516080712061a0d050f09120d0603 72
    0x600c204001400d500604810386414148a401803601e1031000c5c0300d80302071110503025030b031205010b41c0d0502e4000c80e1a0701c404000300010324100301029070700d616000d12800414401141c40420341224000c1803036031100c2d1143e254055200d0703030669140661820411840300c695009030018810702c0000340c410703507881008900106285640d0f04a100c0000d50005001d409408100078603005050400c198914151078100c000340e035407459109582c0a18181052a02c43c0c40082d407011481d1500064030458601e0301b0301c40c407100c912004c0c4010901c0e8103412814030841c1824801c0034841e102142c0180703e0503064078803d03549805050422640f12203100c9010000442c01c0c05404e480074820740046440303a2040c17411009a880052015032501200c02c681c0c0c0c2529408290306800c6a000c2c00d00402d1012400100f0300130f0f0079240c0002c510480c0d084d003111403100700304000f040ca007d00081d0800c619240d0042c02c0c07603042402c0e02c1207009079001090700030501f00480c00800e03010040c042c000550541d2940c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 213263246 1250 213261996 213262019
    0xc0409020c010507110601080d1d03010c030605010f210902041b030504170a050d052a0403020301060b1c020307030b090703050f09060118020304260a032304120306 72
    0x310a907400c1c0d45503014840d6258100c0d807544c40b05085c1038060405c541c14172403000e68a4440d00059000c1003401405840130454442400d241c4800241c02030058403803c4001902420b41032049500159803240003207a0903101c0e0081d4660101040b11001c2e802040f40c014030080d00111409a0740140d8841100d070b9445010103841810b0101500c0100c1c0625150130441d41e0400b205100701017104007000f0034214144d200c0201e51540501010024503a103500800c04441540140701ca060001001044a100600200a0403c80348200c0090140c0c0b81c90741c10b0030b16540100c40600420030034238400c42e20320071007070b0300603542c021103510300020101300080024403810020344524000c21758581c2800055822400440c8d80520310380000e2842c0d52424200d81903000000752144d0001e50702001140400603000c0301d010284003809c44990042c1d20a50760b07180d4582c0f04800201c0882c0c60804594070002d2524000c01d86800d0415031300d11076a41d251a0000100c001800c90b0040587e2520302044845070f14 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 213264496 1250 213263246 213263257
    0x30c070e0f010f1a03040f0506190e0313050d0303021201260a050c04110f07030e031c020a020402030604090203011104051905030d050a1101060602100605010503070806090c040902 79
    0x40401025400d0000c4030440741c0006030001c500e0035810903024086480000c509088a6401351a0b266a07070350f407410442200303d2600c47c002d110380610030a1000b20086108020341030080d88904104900d01424a2a503034030480d401d4400c406c0142104000501d045030031050054000d081c017500c3c10403d1003000c4038034042608031490804800300c00c036488180d182201041d0f15203440c0142004c95040e04c0d461b5407001c259000d40d03c260780300c100f00d02c480c0b024030007a41c0450394146161a04d4400b00e1601034039440a180c00240a88500d040c02160322090003000703030101955401428800d64150280006940000c1006030403036242d40800005803002d210f12000180b071040041c1d1a50300b4031041140c0750716040040c1140c2c0086440c02e0102e030f070340810031910101003410710390398459000505441c06094680506055403070050b00040301e43d004118001c1c1100e000c20200b140c180c4030001940c1a001c01d0f102140011100400921a41461021039801001400791603060030f07a40c945032410703603204 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 213265746 1250 213264496 213264509
    0x90e0f100906051303080411010c05120415020a03080a050709081506040c0914061e0310050f0a0e06010e1201020c0a0212010608030d09020103021b160609081e030c07 73
    0xa8030310141c284221071041d940c000c10140c83e52410303105640c500030001d04c1c000c0c20150461400c2d00702400560300444c0e41100c2503900c0000d440c43c40c0912000c2525941141c890051031808200903014550f101043c10100983d040d00e440d800d42e126024580d0042500404280c140400c0c9900482c035860100001c40000568000c1d80040d480c01500740b0055a82c0c1c94040800d204100800340a24030540e154141211410384625449415040b800c6a0070f402e001200860303090f0000c14000003034194442803042c1c0c1c0e410307540c0c0c0e0246040c3c0c0d024009081d08511440440309040300110754158451420a815064007c10344506038003514251801c903482118400d4140d4000c46101c011070400441030100212104001c022451500c42541d44038414034100004181d81e030f051b4802160b0280d03058a80c1ca1040d08511040c071590459581c0d0342d084594402c0711b00500c0300c1d00c0005c0d124070842d501d109454001c005011181c0c0c2071007040f52a1012800c0384100703400103003c0000e40080c1000103100074040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 213266996 1250 213265746 213265751
    0xc080a180c1502070b041203030b0301020d0e060f0f10030605040f02030f0304080c0a0b0a0f031b0806120a021507080409051f0e0903070201050c03090405010303021e0a020a090e0f10 80
    0x72450001c1c4c41c00190b07a10074443c458003800200500d4544a110620b1240c05060210300ca0110400090080c0b080489a0b03580c40d2400c1901844907400103051480b070102002e4491040e15848084007280c40200c6048100d440001c10900016145800c42d5401034812402d407007408080c0d50000e4200041000340c0d1600d81d2000c1401c2100484c1003288510003030041d20031000040c2014945929441100181d40c148624103009107952882a48903481060a4000c8508400d90390702004143c013106440a9108016081406030711480105004414550081c40900341c2030601c40c1000e1160046107096889039001c0c03000107035240650156501c140240d004101d401008040100c09048842e00011074014005040200b106c100200302e82e14550242480c0e0b49450b88141207c0c41c6204c0e01520303541050400e0000420181c000403441d6a80b4004041c624944c009100d2440c0c1c0da5a07000e102941c0800e000c0810070480f0145e07484254082a16400d9030768905120304060b281c1040031011402c1160b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 213268246 1250 213266996 213267029
    0x160302010e0c060415050928090c0809070303080a09060e0c03070605031b030c09031029090a050403031503080909070e010503060f01180b1305040c080a180c 69
    0x4818482812800340031240f0500300ba0804a401c030740400000c0c40d9405100c000100d80d4030507564522903401c44410020781c0d0b0000261107140a0f100552071013a204024203100c5000025070181c02100d12030b110764070003000c1003071840d113080380c0034180a42014449a40c800c3c444e0003083d41402541c400501fa0030003445040320090a15140c41880d0344810100001801030100540c0e1070180c410148202032103043d01d1352a0b1000e00600c520803400441d9040c4250b01110141070341682158520842510441030314a81d20110060184510311230194400c03003540025200103041c5c3c0c03040e07030424000e282c00180701010619001b02020150001d0706e2007070001c00c5015103490400040c03503101c4003d2400c001c1e40d1403550b001030b11500000c2c0a41d8414418000c10885991044103000100198500c00d015620b5070703101219407942c403105062000f118407082c00718080c1064041c042030b100d52030303560090550fa0f001d40e0030009c0880340100c04200b007200842c00c02041034000064007503e290388102c520305 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 213269496 1250 213268246 213268271
    0x906050d1a1c1e030c0303050c0f0403060b130b0609040213051002061504061d07020a060606090513020702010503060d050a0204021b06090106050901050105130803070305090a0807051302090616030201 88
    0x3007000340f000201d00402c5180b5100000d43c084100c031010f682c0b509001c1001d84841101007018068018006091440410004203110160f0480c0010110555a00d01ca00710040c402100341c1c3c61900001d904403c0030440900030341031030b44c01868407116681204a80790f4852000400d0f40402c0c00d400401680000d0621014880340d00d000e0324244022501085170500e003000910110658001d1038094484100c0014a098000d0014400c0345600000c200710054849070045e14100c03040c06014052a103458a040032140319200300d07943d0315016103130b503802d42e178411003003040000c107030001125213001303409c80580162140d001801d07880306440010340324082c103000d206192000c0100642c0366a030415400700416222050351a0545500b0b29089651f4144035050900c0c20340782c1e030700c0005a840300003900d40c14164800003425110f0f4040720384003c0c00d41c2e5030203042d0b80d400481c01a00e41c03040101c140500151000e500400c8006000760402e4201419a81d0420840141807019000741c0d44468190720301 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 213270746 1250 213269496 213269513
    0xf03020a0608040f150207050d0f0e06030f1f0801050f04030e0d0b0c0309010b0915030111190e12100f0606030c0e0907020a050a1202010c0906050d1a1c 67
    0x751400b85407001c00e516241d04c0300d001e150080000a0501080440041041300f01a012030b0201c2d43c00ca000c58a00402c5484010964075030411014001551405c1607612864120112401207226250f0f00f0740d183c0300c2c0980c0f0041000c690307000b614804418100051001003c0c021148500900207103848241b0f40703030030081e2914118041c01880b0355103000b08800080c400e00310301a0082410710350075440750341e800011130041c5200940346030303c514000304100540d985020b505404010950081c084509044103284050041da0b5060400e00b41a880f04d40d8140d00c1103101c0581d982d40140b1420315003214003551400d015206802e18140c9458104a6100146030300410008040f14a000c00007a91034000042c005100580303e644221000c50206850610801014a9441d0030a007617480708181468001c44582d90740110328099400c002c41016200e0060411104440030754450b6484d000c0d079054044010304000d12640c0d20342c0300c148008030281e202c501c2c0c81d0f50542100d04940200302c40d10300301400c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 213271996 1250 213270746 213270749
    0x1204050f011704060f020906180310061508040602070c26070501020d0c1506061101060801060b07060c1808030406020c0301020901091a070209240a051e06130f03020a 73
    0x502401c0c50030802c86010305401c0c03a60140d00701c1c0b00051194280c01401d4083d12902200d280c0c4842c010610b00005c00c0e80c10b0034082e155074200d0031640342d00180c00c2e150b004e40321548105820b1000d411030410f213440c02006e041d42d100c3d20448005240080a42d24402c81c81003039000300c0c031107090414503883d01d801280b40010790548102d00a0031351515060000b5540d120701d110050410007604051004c01c50150702075140c03502c84240910015494600c0184404580140d1505540c2484000644d001c011b20681c400e841104800624082580c0c40e5040a0710040701c1e00c1040020710b0104400699a0b11a0312000e0080c050155507513600e0030000034904001c880c0c100303220ba40f0400c034420b6503a0b005110303401140c0050203605800428041e8250090003100c00194010307016800704042c100d02d4481c107000d014005040f81a0f000b50850034810352403624000c864018058008441108400d8a801010902c004110300d2070320090903d5940018101e51000c00781800c801c400380114035180c1e03480c50 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 213273246 1250 213271996 213271999
    0x402010f021b0607060e010c051e0a090e06010215010e060102070b0f1605030403050d050d0c030903080408090a031b03050c10020706080c041211120a02032d1204050f 73
    0x1c5500125002c0c010114442c55442c0c0700f40c5001510b8410084c4540240c403602d0900302c002c10000e4032540000d0300d140e01501c1201160400c0c0003101c2d0310a6241c106a0315110f0941d40c8440c00103081425450800d0005000103040d8031030051400001c182000c2c4540c0a0700e190348a001981c2400303c006890a4199005100418014001000014501c10590304011000015114004c05c542071140c25031040340c0018160f40642c0c00c607038604507040300040050b8030ba4a0410444820341000440440700782c000010300242e5210f0206001c91842070140070424001401e000249542e41d844554000070f2143d0326500e0500c0c01c50800600c0410320020b050070406407031003000300b40386160080d100c81150107648107000708400400c1d00c100400c429a4080e00da81111100104000d003040c801e00704d00704c4100381c41078612500c4010382a0001c00e900d6400395014008060740c982c64811800d407007420310440d50318094800b01095092031708010003e0f0039080032205980c0c035800d10b8280804400f00c00c1806 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 213274496 1250 213273246 213273253
    0x80c0c061317070b0606030703060308040b0a090f0b03241c0b090f0303010303120b12010b04060519050609030307231b090c090f030d020d0305061c0311031309050402010f02 76
    0x4001188504402d0345c1e0159003240c2e142d41d265101841a8020034203a0405410745201140221360b0078490001084012003a1701c41d03045c140c0c0d86002c15a01c101e400d019190307450700705001244041c41d05012695125410441103120812906c000c21845501041041c00311030754405070406000d54054041e4200710804044c0c040102664841d954911041c4001800c00003011004843c0019170f5005030060b0400400320940701800042250103400d550001c0381c4590325007a400526843c1c1404001c0e0000f1200450407902072802d410804181c100405440d00f600003041008005129801424501c80449101c03290b04003215883e1031030501d600b070306050460341c240c4400000d555052100f42d030080d0041c0455a075282c1c0c000100e54850b5614181c183c1500c034024007050050b0300071500280000150f5010010b550301c0104012a8901c129105c1c5000040d40340d00c20046485260700d4984241c9541c2140c1c90100e10044083c011203440c1e10014081769624140003c56a208145807070802c04e0344000d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 213275746 1250 213274496 213274507
    0x304380a02041d09101107051c0e0f03100f02070c09050403080402061612020102041d010b090d050a0b0a020711061315270f0803040b0a080c0c061317 66
    0x1003100f40340b1000e2400100000e0074000752002c0010407007903070380501c039130411301c00f20110743d4001039290410001106c0342c0c0207504400080d0031141c064005020481e0b074444200c005214107110006609810b15034060152140c80c1035409203d00580c410303000040030042e9107010a082440c02c240b4190001746041d4240030600000c02d91048040360000d0301100c800d692298001c4103020401c0304410b004141c948400280c0302c40b25010742c080c01c1102e00d06100b8a4034a0070443c00607403100000d00820720700c12401c0c44400c6490030480d4500940f64403901c1120b13150b141c10345039001c0f000400c5507039017413068001400108002d40318840704804003060b00c8142c1081440b9040c1328441441e8011111700742d44844584209901c14501d001d010202c1910348920000303200c0d142c1058049a021301c00210b03005041c000340d0a4000000ca800722103a080501d41040003120003141c1c3c41e0f02c083d1040c4298034003400354200f106000d0242c00e01608280c201c01c030031490b45143c00c5548a40d01e0220700d521000500c803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 213276996 1250 213275746 213275759
    0x11030907050609060c01090f0606060c0312090c1701020414010507020117040510020a08010f0b040b030a051911030708060909030414060c01060608070210050412050304380a0204 78
    0x80d8001901c40444040d6110b03e800e0001c00c0842c01922085e5041c0d6091110032000d0250040701416002d0040c0003e00000c1e88070002590180008440200000d211000c080c010220950000301d80620581000c500141c0d02d184400348911842c01c04001a54001f8042007000001c881383ca40800702802c22904007041c1c0c4d00007034844542c030b6184500c0088040300140401c10280484503a07104c607980d04549032185040020b0101c0024011110044240322020a80800e100145d908803080b08555600e9982c030b02a0b0100a0312018207075403840072082c98020030000c2140601110031500d134582c1a02c07450848801000c020307000c1d150234041c00c0705030709000c4803083c044211001d0386e01d14a42010f0446070783d8086040340c4200c00100c0015440e00c7c101280072584010000e00503107590f400c0f24200066003a040044440964004000300d10124609580c14003e501070343e030050081281d01d074002c0410143d0200c50320110b0051015185070b160b000202e044a003001d1303402a0000c003086007000e00700b10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 213278246 1250 213276996 213277003
    0x11e09060b030a0905070f0609080106291e040e2202030304051207050405130302100b0102060601030b12010912090803040308040902070f06063b04080d0924110309 72
    0x100500119604d4030b140800b48101049850014a01d1076140890781b690f030100100300e02c0550040014035400c201c1c4c000307180150144443c01d400c400c451a01c224500c0128100c0b240d03841010001c6102c62840411549041d05102a200030301f200c500b10b100f9454007040c040c030104540300343c101c0242c0030040c0c8200036032800001d0701c090b680142c880425120b0004c01451030a44150301c4158003504000c10804900d80f040054003103207229400303c90240d96540e0242054a540c42e00c0c0c20f00680c46030380041c1c440c3d03110b504030325001c0d031014199980402148030407a0030f480b112042034826007000c107428130082d5407201c041e82c001e05050300a54109030541d5031b291007600c250700c25202100e8000c2084070038000020034005005a200c0700800266607554119002140e541c44d540901d8021000102d00b4050503004650000784450300b0030f11283e0700c0d5550700380341d500300c0901418440e58903a01e0000050000707200c61b000003041039141c5946413081e171900f4107503440d041d2450350114084c010300107200d1000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 213279496 1250 213278246 213278251
    0x7110709020c010618091403040e04110604090212060108090c0d2a030501060801051506030604050a0e01020a021f020408030307230415080901060b1e070605011e09060b03 75
    0x80405680d6204000202d40903200d00e07000550380400d0b440911058a06a900ca55526403140d681c01515000244c0f06940340e0003130340304849406600c100064002990302d0b47d0b5001014000f40400d0038a911414403400b241c0004841c0c03045804880103101080da045170205600051200040281c015118013051202c0c0740003030014503001022049a20504291aa0003e00c4000d4042140a5aa6420420f011b800f4512525089501e00008140e050720146e031100e0034014083c00162443d1615000e110080c2001000c845405550305101d11541300f0a00040152403600e50081c08010003080c0b00340e0001c5051100004110300c100000c1029003c040103584e4021820304000300c0300080c00c0c4074a907140201c00d0a4143c821f80004022500700f00d50074422500c000c0705da50b4001155a180351140c202d51003030240c0000054148115146035001c0100440caa402c1101024200034040c0c3d80c11050700c10a800080b030000844048510392408444500c0c0107016490307040c81740d03502c2c20b8070304180351102 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 213280746 1250 213279496 213279509
    0xf05060706020322031d060325021f09022e0f110a2a03050715050903060c0915190806011107151209110103051f09090209071107 57
    0x2100003018078001319815070000c200710b0f6154071102e00a1400400c40c1000454012280400c00c0d54100c5904004091b01c3c030542207131081006140349040d08a000307991700c61a01e4118440c0300307000001c200510380700381d01c09001410041aa01004d1041000030001c80355401040000b40102d2401240045043c03010313003140c0d040041d12031401c010215050908089009028414141d140f03082100a203260f84803440c00261403000e250240700030748030100701403101038102c0d48042c80038000c99140b6005000354024030b0a0491602d1000c00100f42450306c2240c7c5100142e00215000c081400e005200341c82c103810b44404540790040310b03000d10800683c440f1a02042104800008a25900555041c0742d085200000c40f000150358081c1d010702d00081c05c441c40d0000c3c2180d62002c600c9011405004034040d8000f44030100d0440d15001103000700801071480c3e94203640b640399041c1c00d103034195418028040348030000c121801e40c0c0c0140184418013411060811a0304a48040750000105050050381c59 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 213281996 1250 213280746 213280751
    0x1d061b07080f0708070218250c021c030806150f0a0e030604051c0f0e0d0c1e06030b0604060806010e0301061e08060f01050a030f02010207230405010f05060706 70
    0x1003509241006000e00d00b6050022400001c0c44424480880c0141810794400c66401c1c48000300c4042d80c07980140191050703440c501c0a901031160b5182082e00d00c030000c41c618079095401c103115400191200d0082c5081e04851400d0300d03490000c0c55840414554410300a8582c0f13000040c0130011000e540c42802142c4030400800308001da4418894441c0c0250140003e0484116040a0500a8490015005c1070300031010900d200c00e90580550072516001100d520382084600c443c070244280104014001c4a290621442c040b03800044200b003001b02c0ca0003055001d04060038404060708a03114941c03c05d22540c4c080c8030420116501c010040c1c1e2000c420320389109a107000002003809840c82c0c5d00240100032124002c0304004540d2003001d0101d170480800c441b80c03511605640072521600b805050340100f0b65900610228085006c050b03040c0b841031046a1815035201c0c0724132035145060040144501401d0801d00d1740d480c180c022680034011a0384c48420407840c000010364107202c0c600b00101400e8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 213283246 1250 213281996 213282007
    0x1c030807050d050a0b01110c010f180509160807020c33030a0b01120b03120309070b0a030605030d031e0f02091203032508190f0905011d061b 62
    0x24450741c1034607030707040001109028074205800c100c0042c10f08081014002021412104180540096006160241a12840c90402c200c490440702207002e107a001c42c01411541c4009250780305e02269030f11410f01c05000c0940c0e400c01050040c03241d03102400800856014007000c00303090b5503640c000080e900c510b042100038844051200c120300100d005130402a514088100b0810364020b41110080050982c2c49049218a88100202700c600f6000f556405920030706071362007030141800046030861425400c40340308540c0c90f181c2d1410b95222906140000703807200030811807420708104007030f0980d019041c18042c1001c17280f0031034084070020030f0a911407612998460083c040660483e121040003034900b810150306140c81030fa4a5005580c1100c8080d4400546042142d04458811651503240e43d114025111301d208030300508040d03202d1862241d0b42c2c103020300507907500c0d20a00603414441d0340041221b419036405842a900b001407019103070340041081080c0946845518211240d91041d0700e529903 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 213284496 1250 213283246 213283261
    0x60e01020a0204090303201213030c0b10060905121b0f0603131119050411040e070e1009080c1203160803040501060b091804030315031407051c0308 65
    0x1441c1d03540081c0d00b044c40c010700c03d418141d05030032400c00866541d1144da440c03048540b20070b0031751080c44420701000440801141074680c0c10400b80c0d440c14000d280030b21071180141c4802c0840f000980750000b102603a810708000c0c864000340403100a0204641070ba40046044440381d403070308485255a1601050f0108202d501d030340c1c441001d41e1400014000f940c4919102c0914041c480c0001c60a59505612401c181c19618021010b03c5040101001100c0078a182c1300501c405040601702d10b28440354203000c00308010403070440f86881064299a02d102e082c1b8101b040c8001c6160301c4662404100e0724610a003c810f00000700129084010b9620501c40f08050000d05d05600030f09004041000000c40b9000a109400011710300982c02030008000f465502d43c803d81c440c3c07056a00071500014001044110425000a01c5d03134001c0c02410082071094000003482c01000086d00102d03000c0880c01500c04100d0f008000d80c801a110a8030514912543c0308815002a040c1000060400444d100025040c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 213285746 1250 213284496 213284503
    0xb090a171b1c050c120a020105070b0703060905160e0901060e1c05010e03040303020c030102040e04030c0f02030f030a030b150403080a030e1207050d0201050606090d03020106030f0506090d020601050307060e0102 93
    0x4001088071807050102c024507246441d030080d22841e030b10078400150740b051007441c0803820482d0315a05842c0d00d494071809640d01c801e5560018901001d0680e29540050040528060144526001c40707190351240c0003008d0141c607000648560300d00541c0300000500655070004d00b0154203881c01c80b040c0a07601c05921088514140b510340c014601c1d42000b00c01c0c0711280d4000003a2040e64443d809071040200030105250803401903104030440f15511402241c0400d0181070350032261801445040186c1180c2e0f0003082c40c2c4210700c055040b690b0300c00240000e40302c1d80340c80b801d200408101c5000c0c5c400d41c1c0031801003403140101d010141c846c850008082d441203010ba03110b012603202c03603030549101556440350b98440741c000c08410b1300d05005200d5206c00a40c410b01c01c49100300030041c8458104001c0405002c04010442011002c1d913683d000003101160000c203240084500c00c900900103494a400800c1c10901d42100f10030a550200300144442d40d008904801036a1041c5005508074442000407450b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 213286996 1250 213285746 213285769
    0xa0909080c011a09010902030403020304050103090311010504080301050f0301110901080c04120b0402090a1404030f17010b091002060702190f080c060f010501050f1b01150b090a171b 80
    0x40e41c40e08000d600c00790f08500d000038080354101c80315041a81c0e5104090142d02c011500140160800c00091006600030b038020898180a03280a545152140c40f450f801c668054405894100c40400100828070f801c007803004401c0000d030001e002180b0159001c0e03607180904001d85040c0240c41000031046c0654a040c0c600810744030756801c50041c4036040001c1c0c80360003610300303070701401d11480011b43d2107280e801224118045028070100c50750b03030f94804442403181800c10b0380c10007044000340128003c0c0d00304840d001e030251034000742d46c2d41070060030020142c101018130380a41d00003c080000030341d00421029030581505060800034070f058949102c2100182500900880012440200c6020300183c0d90b4440d005000f4000181d0762100300540b0380c2d000d007607180d032064601004607203d0803400e621004591115403001051900c00c40100c00501003e54111050451000c0f41081d007510301034a40c500104405081c03846070031030f0040f8964660b01c0d031240e28000744802ca0189441c0f83c403040070042 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 213288246 1250 213286996 213287017
    0x903120e0603150102100501150c03140c07050f01030b060307180b07030305180609030a11070f0b130506090612060a08011109011806200c04180515060a090908 70
    0x2aa03c0c80e14408801039000b4036840385006120720703007202110140030712401e03042c0c030002005401030514625007201c03046000103048003040f0814038603c50502508019142c40c200d8040581690b80c03c0005120720401c1112800b81003508140040c64a51030342000c80fa00100b43d1701d80100d45910380300c0c901d441c0306215800000190000564281810f42c07560000b4000c5003a0fa102540c8c52072800325003540c40d4000e030798000d0150410050408024054926880e0041e000816200307a00e17550100c21a07200c84640c0b00c02000240000c001901482e020100310240600301e84c5070b814010307113401152003401811450f0150702000c0f00403d0310b56a90f00c0e10640100036580090040506107442c038110390304040078642c041090350046c07801009100310707024241d0782c2a03600c42259402c0601503900c405000e00b001c1c90640600c80d00e4146a0f00c8a001b62030842444c4d4a81d200d8055003803030042e140c048000c40d0031b24440c180f2000e1205c5e0390303110b40c100000c8940038800414441c0080c01d0022192060f07800741d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 213289496 1250 213288246 213288259
    0xc07031103030f07170c030606071a091c0f0c080d091b140d110105030714040807030c0503060603100f020f040e010603180b0a20030a1505100903120e 66
    0x3403c101810715220b50100d039030344440b0751505110f0308807000c0c00360750200388040c00b400001e150b8104480a030100a0103810444d407480784100020b4140719040d140164944c0001a5074002a00c4d41b0908401510492070010164844034030b0007003881030700c004010404000064986003e41d19074000040003030300141c2d103d071019075030368030703104580400c3c41001c07024a0607441448403403a1210b06054a40e17004240d40210080000045945600c0202034100380480000380010003008070300600041c00010b001014000d081d030a000c04c08d41c0c8079030300007032096200e50100003068501240d994806200f55402080341048240c2c030074041e000d4110001005040402c0000354080d00c0a01e240c100da1f1241c80c100001001058408106000780e0f4002d0400010000428400511035001401d02509844c150314441d1840d4000c034460340c0180c46c41f060032501ca1b41c603004047c0340845d1007002840f084070562090b01c0c00380700291180c101440090a02400c1e403450f80140343c011000d035040018001c18030b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 213290746 1250 213289496 213289501
    0x20712060906140106090b0a08010b0c210a02010b041b0c080d0c030f1503020d080f070b07080406111303080d0603060204061d0a030c0509061516050c090408030c0703110303 76
    0x103c1600f07110911071307400058040d200010704003050b04102d81ca400c0860f610a42d060703007000d00300d80485e84843c01200507441a11a6088181e6002f001d4000300300c4403515031503880e54001002400d40b41c85c4d80e00d90744200c0c030b85040e40e02c08803c40e003201c52040305141400301244003241003d10046c020000c0c058030b603a0070300c03000c1400f0ba170307165014000c84e2040c2d10040100c28209000c10300e40208a000007901700078051609000700d0403900143c114403007000c1010b450144a651101040241540c9007002b1542420500c0700f00440e0740034140082148509150504103001d500400820007440040e0030030000280300c481203101c5411135800f550f00700710199a0b8a64903903008280d40b042c400a50220ba0354460885460328106121f13a08072500701c0707996003c003810301b4204000850702404107640001c201c0441489007032010003030f2061000202c81d03011f00c1122402c01e181001550421a446000c00d07004101c0000c4a1401360303504260152003250301e60500303113025984280c4801c0e008040784004000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 213291996 1250 213290746 213290771
    0xc08010c020d12020306030c2209080c0d0c02091603092901080f2107020d060e01061406030708070c0c030605060f0105091305060a050904080403020f030d020712060906 74
    0x1200700c140b038159a00c211041c00107003081c1c812400140c40e1280e164110b0902c10702140341550030440c15052804484010740182c1c0000d070212045040101e030000c5001c0384401c9a40014880d600451141d41450301d00d90510350f00050020400601020006600013802d0031000d200b0360198072501d80c07002001b6151304a402c1e8040803c040481180fa1114074400081050703880030400d445c281c035880000f48000c000d031410004050140034182a1840800e01144015a9401c0380c40c2c503015005040005001c0071204c400382c00d450082c0c001c40358040e0600d02c1501e450b1218411268000c4d40c603c0c1c110311985071054115200c2c0420600a000c26524100200500c00740d54005802008101e52040d0700142d00b50054985000e0202c825900282c203801850280907950000c1d0b60004006001d009040c2d150400200c0b54a0103540c19594240041400d1085083c820300b40d40721200c003240180744a000414000b0341d500583c3c01101d0720101c0a09984d0100566074004410080e400305060120750180c00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 213293246 1250 213291996 213292003
    0x30609060b0307050a062c0d21030207030504120507081e071203051e0c070305010b0a06080402030d1b0204091a0705032412061e091203060d0c08010c02 67
    0x82800d200f8080c4030300024492412a00e030804555180d101e0140e17009481d003030388520384021280c224014000b840001e03141c0c0d848959642d01c1d14419480f2403201c610303003e00003403800501d1114109044c410001724002c250080162030484003485c2160301402082c0c50400d0802c6004e500000640c0700c0c041c0f250740007160020f20202022025811100c82075070b070701d800f80301c0c282001c01c0103004514104052604000c03030707a00b0500002c1d0001c0c101c919201001d0300052030606650b10a8410703964403141030041e0300c0d00c0711406000384114a440e28007410140c0001c0c1d2218140310202080c01209051104a444404800040e041e0010020083c0515034105501c0700441d00880c0c0703800c48800300002c1d00b401d02035420340b0302074150b400403d809040061140d031070720603985400c01e41c0080314400600141c442086103034824001d9410064600301103c0190030850340280c80f103951900014952040c005074141074941c00170044910328020b00e00c0c0e080803a030701030140e00651600d50800d100140600d8001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 213294496 1250 213293246 213293261
    0x30f010e060105030411010c02030c030715030f1a0105130b070c05040b100e1207030b0c040e0c040b09040b180106020706020d050c060c091302031303110f0a14010603060906 76
    0x2080d10a826915003004654a11080700d00901030001c01341c500c0555486170520200052010f0308480340c51550710002413501c41158486841c8101d00e5205500807075240c0100c0401101c606400d02050124802060313000c2d48100c00f150402c071010440b5501008a603d0003002030041103200c5a580f42c15003490000c0100c1c500804d4041d0341850800070407803c0407042c05401c00503c1d40d07645942c0540c0b004105012424613000415880b8035100800803a241c1c1540d01d000e002100c2c0c2890b038481c0780501420360701e40c00a00a03003036042b00344820000006900211042c010089400180d41900c0c140094051099518101080b200b11000410708940006a440aa400383e800300c2e030540028030003c0f5603138460303001c503001141c2110004c42c01c103900202c041c20302603a0080015444402c03c1920008981086980d46030740b144800c40300041c91f0b00021202c0110070313810040c020360500700420554a50844400818080010700000305d0b1500030341c0100042d5a100c9814401e14015003403680184c03445 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 213295746 1250 213294496 213294509
    0x120f121802010f0c030c080a03020c01020f0406020c03030a0807120f1e052206050601020a21090504050903160219030309051503100603090f06091a0109020301050102030409020c070b030f01 83
    0x110b491050102d01800d001c070070907035246e40c2d002c80d411000ea840103500e1304a20034150916070240503241707c0364000c0c005040c03600d030074200090300e4504d4080001d00d00f0030100c003894065003081004400555011001c0c60340110740e810450701499824003000c004104191110b4030f410725141391101c42c00c01d0b00741d14901d0400c0694080c0b06c2912102040a070350742180b0700101c3c980c0c80100b0944005202034100381e0b44071030b0500503501a00c0c00754850040340c02034800d625160740c0b218185156450b42003240b50018103001d80d001c20140c40c007041c0c1e4aaa0b40300b02c4e80f0b26004032220020040071950740c1102c1c032840d4007a655091000a60f2460068040e00141c01014031901124900c03c48119580058074403500c6c044014483c5917280010580003000c021034242e070074442030268240814010b003c2d05a150344514010301c0c010b08181d040400521043e000707801c10900420040116a03400011745088c0c0e101d0000041e85c81c1e011a01051400c802640b01d000c001e03502204106d4198089100c240c12503c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 213296996 1250 213295746 213295757
    0x17010c090501110a06050a0906090c21081209101e0e0102070b0103020607030e041103041202010501032a1505070302120a120f0b03010e0c0307050102010504120f12180201 75
    0x45900055400c4083c441e03400800383d01c501d40800c08a0f00d15000203410a84040340040e802c1d10701d40311b420a4518402040d241c114485c3d10411041c2800c030650039510300b05901181c91840199102c8640348116440001030580c10000306601e08400d118000f0aa0b0340d0582c1044004a0181428100341d2004803410000f442c2035031900609c44180200c40b2019445800300c4583da0030b40c0e0810000b03820102c030aa00b0030001e415921800e8031148501d104800e1031030461a141e2515140841d00c000ba01c1c28068110790512004000251400c0c0408400000190b01801c841540b50345100c10f42030710b6032000301d0401480813070403d050f41110050240c9070007030303003555103076403210001301100d00c2002d200c0b00004028101030750b0444540c2e402085542e20044001c0307140c0403207100003405d450191160758040d81190b040780a80c0d00c0d0401050008180c00e0001384410301d4a61110104010316050718014440c100c42030310300c001d100e43e5a141692010b0341c2d0401030741d210140704925000c110b40c1c04074007080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 213298246 1250 213296996 213296999
    0x11030d0917060405030d05090709020c0102091005070b04080a0201090f14070503121c0603151e0e070b0a0903020d050604032307030e0a0513150501050c060a0506010917010c09 77
    0x101103003483c403a81d000307002107181000c5054498014040205581010700503c00081f4800e04140010100310f0402d00001d6200c6241c04100321120340d2122a00302809801c10100300010890030b40507510035041080b003a1191211241a800741c9030102c8010540c0c400d00c170034441004650101400c020f001e801c1202e11041d01c030b00034959070b070b050020311002d10a018800d880040c001c0641d41001c03050b540901240d029a00c1d40d03082107020012581c10001030325030b4184131110021000c42036104010103030601c44e40c1e6620040c15103504c51802440f4443c000024001c80345070050000303034011680174100c843c80e6101c2e03050043c0c6a141c02d640413000528046041e02804502d042080504075002c90070398904292035506a800060f0300e00c41d02d400110414001406075503594072051442d102c0603010170b00414401043c1e000d404950401410322206000e80c0314283c0c80050215804000028001002e444000041e903c01016500240087d2140421441d00302011340100e18105c401d9104c95106c60b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 213299496 1250 213298246 213298289
    0x30c060c070b0f04020f0a03060203071206140402090402130b1905030f0708090723040e0703050309210714040c0201051b0a090b03011707060e09060d11030d09 70
    0x140719005016001e080c1800208424480340c010381c03500316200400e40130204075108085440d0001c03179401540c0c40c80e408000c0044240d0002c0340c11043c58001d81c0c040000300e0400041604100226100901895001c02c50700001e8403507a0458400c1d9003102c0f030f1104825a500840359039076200107000b0a00300f990380c803101041c602074010741e0700400341e04940401d55036903003008032444140140041071500c20080c00141101c00710706981100207625410b4403018544a0500003569a1280d90b2441075001c420208003186020081c0d0308400d01c03c0720307640b5902e5080000c07005030305651003001e0302e0f50184000015071181204c3c58035050707190542e0240924114120141d0803960b0449900c0280d4002500c140b501c10b83c000700a01010b041e0341000c8415036150f2940d00000e4100741c00c60404445070a00c2d5500700d00c8100300d000014011854083d03a0486048007080c015140600102d004850300c0d4100780410481c046103107414403000e0111441c4000c0030310001c5c2275000718803401103088421020301300e00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 213300746 1250 213299496 213299521
    0x50112020c030d0b130e07052d060a050c060c04030b06040c0c03052109070905010e100b18180429040b060a030c081c03061508041112030c06 62
    0x1c0c480503802843c1841c0c02003c04070041e148442540358414800c00155000c036550b8812000400105d030f0042c21039900380010f00004504161109142d00110303040305540390b98520340380031100c0040c0c1300320b07444401f4902c041d6058061004000c04c0d90003400c0400c008843c14401038411a07010303c2c81400709072240703001c0c001160b41158100000804102201c03000c00d01540042c246041740d10a0b146220400e41c0c5016402d05003030360010b0503a0840141080701c19014091180900076072502c03406241001540c003400001d151158207181c0801050302c1c00856203a4000c120103030f10140c1023030b441143c04401c801d001c41c411a02120280780c9107071540150401c0034004940414020003001c0c00d0b0b251a19010070310340300100032660110520502000068920302d41ca4003c001e4007000304174510302601c00c038008200c2801c046007054030b0007200b0803442203121052500c40003039043c41c01180e00e071410502c1901020b030760101e07041001144929008a8000002c00149500c03400f038815944032152440700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 213301996 1250 213300746 213300757
    0x30c120c08060915060d050108010b0303090109030b06030709020c0a1407141c0215070317070905040c090515070302252606130303140903030a0209030313030b0105011202 75
    0x1e404200180507070070001d100c2500802201d00f11242880c8520005180e1360001b080c25842a40326401002032040c240207c944005084010710705041c1c400c00001c0500c1e20030710014210080380b0000c52425201070010002034240001c040d036484070070040705580ca148501e011503d820140400b080800d03000326161050314180210445064001810021890342e0241c001d1010400303540704800607a104040c0b594802a05141c55845d50068140a008202e000c1c90001c14005400e08020629074041184810b50301c04071400280c509120b40700325690442c075040700340c2100e05039000000d08804013002d011498840d40c22505a0311480145c00136442001d0035442c071034840e1410a1001d01151410501c60100c4982d81690085042422510f40042610a61480403164080c0390034075526000b04044051140440c41e0b030f500300f115100750f0300e20008202144041d400b01d15024242e81c2841104c0507011a0764a0454458990600c0060040203220f0907003c03c3c0c4428007a20041220b000740c6a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 213303246 1250 213301996 213302021
    0x30303190e1e0c03071404150503061006090801060510080405192a0b03011208070c0e01140303090d121b0b0a0e070b0a08070507140c0f1c060e03070206030403030c12 73
    0x441901c11b001c240b001602e000c846a0a402e000300d100030034103071403c22503144501384c0000e41d00c181600d481800b51003041c3c16000449540d0401ca414070440d250314210740d640e00198500100503030390302c0c18281d0404a40d4000414821012810781c418070890f101301f080e40c0c41c800c2c02214680d41808417040031000c1c8034402c208017820207000400c120701e0f074000c900c1c01090141c0c050130f1802c1443c0d078541d81041483d0300030480e01c181c0c100062001003031240d4185041201a4011881d040030031000920f011082a40107141810381c09200d44641d11850640200e520004100808003143c1d1030002c407000402c40d46071803294500403652040c1080022790700d04030b481e1010311518000711141c3c2103030001c5004220b201408410044c400015540d40048881c1502c50320252900042800400044000c03000c01144140c0c1500e110300002030b010850a11095485000008c0d45060305c04060f0940c01400c0002c1d601c4000030041009148d010340214a64405d00d542d401d16040c0c010114400719840c2c8040311 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 213304496 1250 213303246 213303269
    0x108070507050a0807050307080d020408011b120b0303040b0f0702090a060315090501110406020f1b0609041e11041d04200a0b04120309090b030303190e1e0c0307 71
    0x3c001182c5001e0003044083d00840941e072a010f038a481c0d140f0f95034001c450050380b00b6800181004a08002e10402d800088410441c40c4601c0b41c05070014081c0e40107900355104550341c2d05005203207544c100212001007920017003540d183c1e0707a94202e21030150080502a03009102c03400006074002c0d094071912003500d60020b000b06085a0240081c030091004040c00c03251590707074000900d070940ca603802510040c4415401000a151600001030a00042c0790f1110000301c020380d1862072583c2c54100303030382d6500c3e401d9074009000d81403400c5049000e4030001c48608441c1c60b00c442d11b0424560540103005480c04042120150040d100d07600c181c400080f14040c001001c02d55000250740600c5500d02c0004800a0491240e50b07210b40c840281036015602509000d01e802c0181d01c20560810b40b108020403116100300550003090020030b441c1c2c80300034140585502da501640b00041007591140d66020303031040440e903250b549168110482d1030040400d199074452400000c000e86170005003002950402400b4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 213305746 1250 213304496 213304513
    0x80105090d05030703020c07030f1a0702030307121509060f060203070206120402180f0a0c02210304021503041b051f0f0504030f0c15050a08041e05100605010807050705 74
    0x2100c0d03e4002409080416408102d02c181c081e00c100b0454000d140502044281c6240d0783c501400d6030f00d140110350030240f109104014019401000f500c0d0300031018100340c160186100e2059000b401c40882d07440c1c10080d08800170840b540306902035010b950340f8511081c42140ca403081641d1381c2c01807080c02580801d081142c022001e40d9144080d8001d48050880c00714062500c0410400c8181114011000c001d00010401500500d0090015500003800505811800c0d41620105d07400400c60784640380c0c10020100e400c64585402c1121071005920010380c6900340340c07a000745c0d010740134103802c440320082d0040841d992808522040c82d050841c100080350043c410703c01d880110328881c0d08414000240400000708540808083c580b61103502c800c01c0d42400c007544a40140000001241004810300c000c480c0550400840d43d08543c100503061102d14181d646804001c2d442440240240640c680b28410042d05800c0102500c90980380d000c41c9a482a6040300c01c1d0045140180495110002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 213306996 1250 213305746 213305773
    0x3020303070f02152a03091c181806080d0309050706030902062a0601030821060d150209130f0509030405101202040b0c0604050705010e0d03030f09120c03020708060408040e0a0b0a0b0d0608010509 86
    0x2151b07060f80e0762b03245010400f1950303034030020300302a0f004400d480401c1d16810031804001007032000304054591814108a651900d401043c802e004d10300924007013001e03299801d807184004040c00c100b41003002e0203d074170030f41e100c0ca8140c1294000c00f580800d03c800084a94184900c041e010074810034000c0d04c107503000032050711410407038509280f071503030354603420415054036840e02e800c0c1c000b01c160041c102040b8012401d9941080359001001e1504070b0300b05202c24421a502e681c02c0d03a60309940303072502400750b01c0255103c1001340f10343c2e07001e0201e10a0015104d40580c0010500901c00c42c002c1c010340d040b15a80d80019110740380c0c903050250788501030400c0c03440002c0c060790000300c083c044084002900c4101c0d5981c001401142c6a40300d0224642c0c0665004055040140a01030420342e0050006410540e0310101580503d000f40d0351402d1030f05001405460072a88503031440fa100408022155646101d540d9141d407185000600082c00d24601154400c414001c00340100501d000034061080c0401c0f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 213308246 1250 213306996 213307019
    0x603032b0e120d0c0c020306131401060501050702190e04060c02060612100f06030605040b04050607170a0c170c03010503010c0306050a050603040212070303020303070f02152a03091c18 81
    0x9448600340a070840175800541c0b02006600d02c42c1c0e000340c0c288281c200650600d005082c10217608a42d03681c0c1001c41c00d10699034401e059035103655050790507400340c1d507035113040000d10b821f103401c00206a95542c003008207210300c4da041046290f84c560243d800e1a111441404080344160903d28400e5103c0d0010517038503046c0307078414618031000707072000141c66440f540ca15060b584c0590382500e600100d2000d102c14000140703c1c00d9000161410a014002100c604240d03e015006289083c1030b541e4001014015006005802070113101c0702040745546010b00012400381c20038042c01c0d00030b62800000b030000382c1c0280700342400e8820003850000c4651504041102c16400100105d03081105010300140c80802003242c24060b521030707000356031245000040105610099110b032011035015000120700000d514800c980c00140c001e01001003000341c03a18000d850311025008180506e03000007008140400410b001261450413444c201d286c90389800c0031074200c000c80405141e940d0090208200042510 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 213309352 1106 213308246 213308261
    0xa1d06010813060504020103141f0b0c030301141c0308010e0705180d03270e18070e0703110a05091207060f05030603032b0e120d 57
    0x10190840700b56480101804040e691400f040c190b9100e6040741145030501850316100f1704204100b0300c4208440002c03100d01c254030700030100780010400125a070012402d00150b040d079081c80001c0f10016603e0107145d60065035008845014180c03030341105c0340709000340c44495840d03161075001d1654070341c000c0c0183d00300002000000342c1c40007001d0512080790301c1914a000d2410007880d05039400d103003e00304201030780e4400682c900c098110803164001ea441c0111020195103404c030064081c3d8a0082500e00c550700041400e00440140149072507000750302e03150109410b01410400e400a074420440c2c400096000540c1d201c15080800d0101c0194020f078004000c0140303400c10050014010003510004c01000101040481da420015a59004a44134100100014540c0142e2142d00d10b005006103040c109a40c6c01680300010038814a80c20f03031418204d103440e8100c81c0000042c03404 = true := by decide +kernel

theorem cover : BRFrame.Cov 213129496 213309352 := by
  have h0 := BRFrame.cov_init 213129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 213129496 ≤ n) (h2 : n < 213309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
