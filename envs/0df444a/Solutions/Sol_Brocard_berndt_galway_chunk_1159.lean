-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1159
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:31:09.424954+00:00
-- url     : https://prove2.me/submissions/40c41122-b69b-4ca2-93e9-ec02231dcc05

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 208273381 ≤ n < 208453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 208274631 1250 208273381 208273393
    0x90b0d14011b09031b0303020705190503010911041404080901030f090b01080c01020d020c1e040e010f150e0f070c03140f13050f0102150a11030a020901170c2b1d 71
    0x80c0000103810021b020160140e031182c1c3c1e0800491501041c00100d40c0d1300c2040300342000d641c410200b801d6a8043d0001c6454121001520100d41407a11503400d40c040607038500880d80c1003d8803504031910a03e041079040607101c0c080391405030095004004100e034402128251503070b489072555212055100400e0060040050381c0c6140d07840080c0e101240c940060040301e0030400d2881010141d00e4140540e0f03080341e100c0c82e800007103041c01e01c00e0005c03030058084040395042e401c0001113480300d50b54200c0c0407035004607801d001565212116582e40f000f0b190401c0034a03d40a81020740315284041c2d052441d0040c006140c801c0400800054400ca004070111400b030300e501c0b0f200b00460192148085801a0711400c1581c10212100301559040160b410b000101801c0601523124245c0c0100d030600010740c0c0009001255503030002c042c81c0064088004900a07091003000c00701c0f1407103003100e03940541c90b81441101140e548aa040e00034034442800800413040500c643c00c0c204812079201074881c2c0900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 208275881 1250 208274631 208274663
    0xa0206060d1a07120e070303140a0c0b100308030106020a05010c0c02010c030c150f09110f0105120a06210302121309020c030f04080610090b0d14011b0903 68
    0xc4992000d101e58407504089007424060720303001440304014140401c0000c08921850002824459006540480d45c05804603504608014008603401103030002021000c10083c0c030725950003945011295400300903044151101030b1940c98044898001901d020b10000000030030179000107c8480c402d108800a00500d03e94020550390580e4500000c0d0210300c0e11041140001d00c500d540f540c68901c40d0b4120003000708100c042c24203d0f03001c942501000d035950020442030210311500d0296008040b207510184900846c0001c00c1400742c40034074410402600c0114121b07117811f801c008003401080030114080e040d0380740e50000324054414140d000d170091141c08004541000700700c0b020000c03030603001c0994906d000c9006000750301880365a40f0f11701040c411110001d0418004000403e4a00020613042c00c10381006070398648541e204050032031500a0034615034407074188920400f5008542100d1480d0007514050160000001050b03444013484810902140c0100900081ea40140c400e04078460f40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 208277131 1250 208275881 208275889
    0xf03010e060f090a0c0308070203010e1f05090105131704030f060914060f0c0c071d04030f020d020c01030c030b090a0c03060603140412090e1006030c020d080718080a080a020606 78
    0x4d002c000e003203507000701001d1010a000304002d140c4544090000100031540052030f0b820000c2c01c2200e01d0355080e1400c181e4900840174020700d504024500003c1041d07040c1101110481d44102d6030085c581e404c105040180380c050030081d0ae00950b0820640e5221810b00e01e00301004000541c0c0403203018401640b507a2414000050685c450006e44030318500c191110040c4220b182c01900b080340d8140325050000c11a03100303007040b01c01c9944c480702c04023915081c070f8540907000c00c01591800045611040700b50303040c00d6000512512910003802e00045810501400710054409941c7c11900204030300144503140c03100307602c000c4d01c885155404020761a01c0d29402c409407080034020294000308a0003083c040392030803c520301e000d041828813500d00c5035921050007101e2011140290a0034412000300700c01600350103440244141480507205481c2442d00207804840064114001c02c1756052808031103070340d022482e10281100134202c0350100f0032880e01045640c0464030390001409240003159140c24 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 208278381 1250 208277131 208277143
    0x1523030f040c1e0605030c040302040e101d0607081e13050f0d050906030606040302130906061406120612030d09020f0a0e040602031f120506010b03091009020f03010e060f09 76
    0x144480d002203d403401c3c1d030480781500b0150503c005201c0c01c000020040c1d40d13512681c40361042c100042c1100c0103c0d109002e0889181c0300384000314000305942007184440100e21554880490b0414000c65225110304030380003500103666040704090442071002c90301550001e088950b200c1e10803124600c1c07040d0f007003944800790042e0010115006001000b21071034082c001d5540a000a071a00e400d00ba03403034000901c426810242000f1482c0d03940300c0c82041c00114020000540125103d01f4600c02000000c2002449a488041c5100074400041000c940c0c4210b010031804211401701c0340c89a4206441000900240e14224800d1810b00c58200f1142070000400080702c000001446180c2d07100c0c3c50300b002a41c001045c0010b0082c8a404580c50807100d01e501d6009011116005100c011180c030f811441e204040c0c00c07445261005004005280b2400a01074954418080001c43c00c0a110b101141042840350000c59055003010600c601480000030803030310581c3c807501030300e80c591505420b06488107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 208279631 1250 208278381 208278419
    0x30020c01020c0409060905120d060902090603151807090e060f010f0507061e0e01050601020f0601120809040c03050613110a0c0318090605030f071523030f040c 70
    0xa0000403902d0700c039140551119662a0141c44042407444030390b5030b003508260320400b424495020100315462420250f1142202400e000341045140214130300005503140001080c0102c1c2901e80d910200305610307a501c103030664903d5074004c030307600e403e2003000508040b5032030042d12540038001d000510646480f400003c0000340c10307110540a0004030328112110341c4102d03400e68082e0303190030041e0f401c510a10301c01901804403020004030f40c01440007007800e4460103814941154842c0012440815012500c8e6045605e8192a9080114640b90640042c02030501c042d82c0145481d28000c603040e05500441d02c204400c80310100d080f000b2904c0c41040750100c4403c10003150301803080184c1c00d80104034912905010f0b05106010034100c048140b90502c842c1c000c200c4240d107c943c1000036050030026480361490440250440d2070400d6108034220b040100c10900b006184403002d440782920141a010540b19907954030341e0703031800d24400110a042603408440021003118000349101440c07601c5100741c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 208280881 1250 208279631 208279633
    0x10c1803080f120103151b1d0103061a0306040e0f100518030c0a020102010c0c05060a1107021e0307170c01030c05090a0e060f090c0f0c010930020c0102 67
    0x11a0031611002900d41000302210380c400410010b4202441200480074029441750440c60b2040880585542c140c61401524a04807861500701c03240281d04020134814180034131000c0c0915414000040300a0440c03a40000714014040d0283e82c90b458181004620900040e501840040c25a945180c1c2d51000f0718280780309034101da00d0200320041c83d07802c9143c101e0450303002001e07900c01d80400c1c0303411540001c00070720f00c40d07010001c2181156028060490702030010300302140e001d4950f0b29041d481c1c1c030300205800212692000c0030b1407408649015201c481b038014041268000940d10403042c0800d51040c0135101c0d11401200280c1d20421400f041d440702c0701d690140c00440e440b4001540a00038000c84101446403e0003810040d40f5000d90344401485080da440030f43d818074505102d4a410560b40c144e005803041810016002044c10032500745940c0c8290300341e521100c0c140e0160051032456402420310480d407002840107203182041e21000c41d10a08004030025115209980e103012103c0940d000d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 208282131 1250 208280881 208280927
    0x6090606211f06020604031707050702060c07170a03090b191107080111221215020f070b04030210060501081b0d1104060f020712020f130f020903010c 66
    0x604030a60041c5420406259a5028001d003120310340451002c6a00004010b0340603000300024540e000c0c0709012000e49050741c41c2a64201902c00800d140700e1100043c0c01028009001140110708202c040c3c0100031201d1907404503552641c0580c0c603070490307080540010f03c0701350300440c41d180c0000494400b40d8400d460b4500c1c442c00b092040c2c85a95040b454000c0c1c60068110000c1c415400f805190198030f098810180e6800b81504d03400705d00950640c21160513902c1d40d000340025052900d0411034039403c0304c2c001160074480b0303100c040a0300c0703000f45411058101084a03c06c06c40341d01c050a024a100e9001d441c0048ae550005000710b804038401c0d01d0000326584040340c42c5004000710b0300e60185954480d0307443c000c01e5544240a403030699a000351015000501001910740c0040d07440400605131026014480c07804d425071500c1da5940002038491003002c1c1d404401a81c61224444203941c450106003d1000600d42800007500a01021402035007080402699140b288009250314000782d48540d43c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 208283381 1250 208282131 208282177
    0xf060f0608220204090210050301060f05030415110403080d0506090f06150d090c14010f08070206220b09150a020a0912020402070b010b0702031e0a1b050604060806090606 75
    0x60400c1d01202c081e07810550701d50002d4050b031100c619604011000f0344580e5540c6d45404401000c00c040301c20540f0802406009003c000f6075150030801c070b40b0140e0311020844201c5071115034828071860b032008124400025009801451b02e1300003a128020480f4440040d543c0c0d1000080e1243d07003181c026034040340b250200c5442c3e00d51403000d440203140a8400040c4080c56640f000070200498200c5050041c08030f0740d8211941c1d0040e043d5402040710318242c0300b81c0c20701c460040d42e02c41000d844202c40540031030b41d4610a08850b51300c9288540c010140304014107096845540360f4202d8110b80400504810005045c00d00c6802102c120300c480e0742c1c50071295803402841d52000518800c049070721a03020018200411003d081282c081d0642d000220740d54160391040504d04031080d404014084011080c00b1a40c0c3c0c0c002c108000815000b0030350300f00101000200d07c1001100fa00581c0c3e01c01004200800e600368088800c0b48905810350340703801180c07130340c40030070003540101c1201c290354041d1052012 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 208284631 1250 208283381 208283431
    0xa0f060209190602010c1d030309150f0705030414060c06010e070c02090403110601060e030703020d0c0509041202060610170403180602010c03200307110a0f11010f0804080306040e100f060f0608 85
    0x2f00e9030b0f082d05100710703013400b190840310740155018441c2902d0f139074400f040500001d070203040070b01a14034089036040c1c94040204070164841030144101c03420744c1850800504518021006040401d074020410382d00ca107024036019000c550040c1e030f50741032803103080d001051380740c0200b90010008000400902e1110302d15400c021010034261421146000c4510307000a680d116018424099842007060220032002c0740002841d142004102c10302c074081d038940320400180c010200d440d501e044074255044650795030034242d54200030708040868290500e0300010b50f103981175204481c04001aa0107100500810b45102c2d620b070840d0300304401201d000c101041d1020f0094024860241c80e01d000d5039085141a00e0b880c68045a846069a4042141c41031803402e681c081011501c05065090840ca60f09043e215110740d07001c01003400b0300441e9500d1400400d00b0381040100c4500c207451700280020f011280400c4007811251051400880c0952800702d072160103003100b540716505200300c003542d00031100000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 208285881 1250 208284631 208284649
    0x702061b0a110106061112090904080901030b0d030e270105010e120a030e01030506060703080c0c0a020406030c150215070e060715060f05030a0f060209190602010c1d030309 76
    0x810034840c40140240b000c1c4000e028580c0100b52503119042c050202101517030071700b028203400040001003040f42410701c0d40c8000c0d5241e000742c1c101ea64aa01e504680c1d005800600c088070308141d0002c51958a1010540c0c0003140d00803045060b5812051700b1200544401004048200c0d4520440707204018095075100701030010f281d1800030070030040b48401c002c07440c2c20400c682400360300046115840300030340d507014002c3c550401c1c000d50f14240f07811410b840003450f1450240030141c02c4400010b00c0d0103520000c11078564042e400500410009659203005c1405040b00d00c40d41041140b0b4845001c40c0900104000503a05965003050341d80380d940c280d003200e42110006210f50310400c1480f68102040021320803a0100100b04800107203a4101000c1d81494040c41d80528401c1c1e00c10159400054040346540c0324841d0301103c0540c540241c030b03000510503030220810780d06c0a1503142c400603142da4150003411a5004a8555140c201581c1e0011108030701c440303084a41691007003012004d070381804010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 208287131 1250 208285881 208285897
    0x20f0607032a0f05010203100b04030819110111030103061407020d0c0c0306020f030a06241101090602210702192a09060314010207110907030f02030c0703080702061b 73
    0x200000000c0c0f03544400000300020300a442c00d03980441000706644004203c1ca02400880313604504052942e503400d0b901e481214020b81c0300310f13116481d4a2515004060000010340140d00070300407503801c10b244d0400d42c2c10900c026981c0906113044401020b20740e0403003034000d017420743c05088100c2155100741c81da08041201240c41c8088454001b000c11030600c00741c452901d00304203803980c0e030a0841d101003e840b10390300010078011003403000810784000040300c0c1d400c01e103060a10081a0302001002401000180400303001507000045003800041d03101c2c004a1614200c4613034a0745034176000c408907a1000c0303d078000d044d2044050a041e0200d0005105c0f10320741032480b5610080c2844140c19003d0340501948519411515034100340100111121401d8510410000850030200c003921641d05400111440034000d2001d1004144080c0c03103900903992160155000f135590b8200100c1021980e840750f141a40001c1c8070402180840c0c1c40400c1c0c0c9402002c2e40781d044104103001b020007940300e03400600 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 208288381 1250 208287131 208287197
    0x4060918020328120521040209091c0e01050f040b0310090e0c010e0609100809210702010e011202040320030607020a11040915020403050f030703051219050405060103020f060703 78
    0x80440c400e11b842c040308410324040490070002d0ba003010300c10f12103480c03000380c003c2c1901c4c0c022020003203100b58450f400c03c6010781d151901015003400280182c800c2e01c00c0081c11001100c000170b000c1440c810002c02140034a10480c5083d01c80780d610401c0300d04a5104c400d0741c41030341d00b007850a00d01e503600c103101a04c1541001024980b80154030300020703485200c0c0342c04040c04070b89144200711001070207212440b030b07816800c0d0b20b0300c010038100c0b243d142c5144079006009061045002e15035440740d1041e0300168001e04040c600f195607a1b1281859407403000c85010380840c5022100c4107003002d08001c242103000384030a070000e00308407555076502043c500c16046504e03003055455a0580c045850900440e0311141006c00c01a640c60540c1006410140700b4410070314290300801c91714002a41c05030072074050284100c1c000c1d40701c0d1140e100140c1680d0b40074202103285170510702840280800420045e040300d01c21282c003a1110703038000c140200c078000c0e070b000a8041100315080c0c01148842c800c04098006000b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 208289631 1250 208288381 208288387
    0xf1d040c09090207030f0f11070308070302030f1c1514040506121506040f15030b100513020d0e0607050f070819020d170105060f09040609180203281205 67
    0xe00c2104a1300125015030018581c80d40b0b64000780d800c44031802c0d0b028428034040c000b148600c2e00036980d40010340310003030640c0800a1000203051083c029510862245c1d52090f9030b445408141001c05111160000d20032881c203250300c1c05901560641c44200e0341c907001c1c01d50075840700204102c01050000c0c1010342161610a0700300c0005810b00120074449500c010540e030a00703144c03050100311101182410200c03481d020049184015211100c1e08680e881090a4103603501c91000075108689a803003c0e4011405c1c170b11101c0000401d07006844283c9582400308010322402400503519902521000d002c0f683c10010004255107090080644e1070040c40a20b2038070328861000c4480801c00403840d00160495040010341e1175010408078030015003004007400301e5041c0750001d026445008102100b903a00010220001d464540001004000b44041003105074141007071103980c60040441240b10b40500d00c40182e21041c0340c2d04c1d80084440200008045203002d81d2845805504070050006100c0c0174 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 208290881 1250 208289631 208289639
    0x302060a180e01030b040803090a021c06151a0a03060509010e0115050301080c01030e0a05060901050a0b0604030f02010309020a0b03011e05011e14070503030103120f1d040c09 77
    0x2020040c6109000c03a5980d84481d05071250340000364829420400340c0c00c040c1c500400200e50204029500306801035402e41d070300e40760078000c5850441080c600a400c05040c80382008428510704081e03071410301680c014007000b50b92001c1e92039540018095500c619015041e00c0308480841c10282244a909040c000342050b00d4400040c00d41c0720903400611180d01610041c040d100c2d0420003035031292222704080d82194101250640c440e109000b14504040d51103c41e001c400c03504004800000c1d41050a0740d0917400c0a04109010306003c40b000040d050610400c40d400307007410400c5070110b0350003003c001c001c0341702a030045000e0000d0000507603005580c1d1102282d0380c0c041c640154000c003200308100303001007034000c07800e0540c3c05141d1055062081210700c1e0b04007001121034000500e8407a1070014071400100304082040d0086a00c0a070007072002200200c20001003412a418081c0c0c90340354410f60182100d030450303400455894082100e072000314246820305194002c2c0c12110600c0c10041901911 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 208292131 1250 208290881 208290889
    0x30309060106080a1d0f160f0504023603060106090303080a0906140901020705060a0b0913060e0d200c010903030e0102120f0a2c0d08120f070e040501031104090c0302 73
    0x10303420f0060340c6c2103440e1203900c0304020000e80c2c101d038801c08034800c2254580450806180d802d40720705805550002085c000320341c0d040304c6410402c2c0e007070321482400d080c030342d0320044c01b00c80d060069600911518002007200d500541a11003103070740c141e0b66480544d5400751002d0141561140440e20191a60301380710700c0d4194841c0d028440c1c20118001a2901c1090800381c3c600170018101904803454000d203100305840d140c49040d030000d84048400d003c00c0d020725010300103000c50408080c0e640600031606040980c0b0868031482c245041903001c41c2ca06641019030348440d0403402440c007250391034600f00300082c0136801c000c0c1078a90500582d107529007010b00c0801641d01803100e084000c2000a03001e156160003541280d50320580c035504550403002c507049450403524035900d0380d01c210100082101001110011145c4e620300e0500002d5881c04c001c2d07003110b5511030599411005c210000e0f1700341d2084c105403203024102c03500800042e0081d401e5105102c02402c03e20005c0d103201c40040008800360311 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 208293381 1250 208292131 208292171
    0x7050601030b100e06060403060b010e0301150504050117190611040b0403050f070807061407200901080114010927030503070f0c0b0106030b0607050a0312050702030309060106080a 79
    0x406485030600310320f4541030b000d48014154001030244400710040c0115600e480c03064505880d0710280004040c0288001a20111041c0c03d1f141d40c95030901d00402604000a60300604852003500d09105503622000030030f008254194110120358011000010300f81c07d1080d82280b8a03000358000120b808040960890a501c6034100070800c8200040410401c101044007982392111807001e00303c1181800807094640a1a00c00c40302007084001d410a41400c54204a59070154400c840c0d94408041c0710340ca40c651a007900c002032069082c070000141003001802082921203004202500c680e0030020818003c12401610510070b101140a1500c03580c030010010181d0703400b03525402d80703926013420010308440c2c0c1a07030100d040103e00f90844c8001003254240c01d05442090030049036400380140420325038012620040c01034030030b114034101855004219064085200c29007030045544100d070981c0d0307900c400d88410388141d003ca001080500d00c03500c0141d80106040070081020782031290b600d0b500c0742c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 208294631 1250 208293381 208293383
    0x15020301081c080709061112031f120314031003141011040f15050c030d1b05090906040b010203160501150501110312091230010f120204020705060103 66
    0x2c0d021030020b07110305240403071089540d442031401490503d44118020001059032044e0000d001680102d51600c05080c071039007450480c0414030b1526850a11400408007810804240e11980305c0240842d00034000c1c41040341d0680c040d11160250050b0309200300080e0301c018100001e4922100010000500d405440607011a0b040018204000a403401c0d000f00d60030312800301c0f50400f0030401004101c04502510003100c58090000d00d02e03850292040c0c0c0c040c40b5511000240d4000001c1f4440c0d9158503034030040d00b1301c05400400b0998446004103a030107101d00c00441e40d0000c2040005601860160441c400341d040601c19641000001650a0400e0020720000c6409035101c800340909034100c3c4008000a100901e00031480c0d104c40a132894a920540003078003e01c0d580c5078006900060204200082d0618881c083c2d659602414224001103043c540ba855040c4208010701c500700740240c003802d0607103804442008815207084041c69140000d2802280c000d0f4003444000045103062003514021 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 208295881 1250 208294631 208294633
    0x20070e070c05010c0207060e040e0712140c01051e031306020c0a02131a09090a120305010509130203030f070f150506090a06080c270901020901020c010201050903090d1502030108 78
    0x8682d00e041070030b4a6012018808652005108018481d80200190040c1da401d903400036400c081b2945184c2411b6035500441c4896841d403440004108005482c1c40c8003001000a0b00c404c1c0c003405004480501c5441071135440048918400061006008010b542090810810380b000e1981036036074400b41e801c2500c40b0922a0042071030b100550070408503491007181c8030242004800d2503520240d4400c0040d81905000c0c00c40070000a80d024410081081401d07000003c40d000d11601c240014042d00d0b09004142c00742c14084c020030080d003020b0300d8404125900801541c145441c0003401c80094004c0c1009542035040701d6001d4010070380321525590882814a00030400303180040a12001c144084e050843c803900d41103003040606400b0489024568040b581c000840c0000201c800024a05809500c00c040300841840240d0708150300608030a50281c080d54601000f07480107900302e0347e040342e604000340c008100304042d9242513041302032803601c90058004841c46c0e06000070201e8109800000403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 208297131 1250 208295881 208295897
    0xa0509030a200307052b0506041101090611060130110102061012020d080c150121031d0d0c0303030507080c0a050703080402030717030405040c020d20070e07 69
    0xa0340206015255541003600240350035403400c40400c00622141410a0f11806022405511030801e070f611001403a1f00310080342e80d681494200f241c403442e140da07056400b18000d401c00296050050b8a02c0c5c0e0b00d24001f0015164503885c180842c42480312038042c140d81a848841d103842c030031642400e81c2e031940717008440c5000d51003600310001e03141480c00b400a40150314076800400c1005100380c0d0b40410554141c41008004849141c00181740c0220480600030b07008965a1100058000a246040380d0181010b2021050803501c850b10250f4050b030302800147c0300785580c0341c01702203690960603982c10160660300030206039243d80361510519002180003034ac8440078001c3d136551005000303030850f5080c84a02e14001c407010010b4014480c413072009041c80340d280c00281c155901400580006e00c08000240307010748910314101d849502c43d001d03030340c071a070702d000b05002c3c000d80f00141c031040e1010284c8881d03584d400030070f0a60101905a0812603060300c0341290120341040d882640e180070f81004d480e8850 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 208298381 1250 208297131 208297163
    0xc0a03060f0e010608121c050f0912030601020d110c0603090d020c03030405130b0a090f0c03110c0c060706060305010f020d0b040b011b30020613080f0a0509030a 71
    0x580e002241c11000e030383e0610000780800c0c000403810003120321b46420415a0b405281c0001c01d08624590f2160700c800e4605420801190105d049a610a61054007a54228510480130150318002a00e005c0d00503407007130746140003403030281030720780c0c40041e44000303c0c0e280300201c10004001e03034002c072807602003500281c0d80c140303c0903010051010540d4086010354203103420400465445010341d13003c071089035250008801d41c2c5d00d0305103148001d03291415051001d11602e003c004081e00058a05200080c81d22400c0100350303000350140c941480c44038010300402c4141c0e00401805801038501501c090303589041c0000014404d2046142c1c030b03800d0000241e00c4d90080701e800001c813070b81c2032002c0d40160b0034880c00c1e0031a41c1c2d00c000503124800c0306404042044c2003e00b0951002954503a103c241c2824500c0c0043c1c00381c80c840340ca080d04450645c00c550725640c0e44002c8803d000c0140304000d01c00101840b80030321000310303d0050081c4204a140c43d07414140000c002030301d0b1000c520800d8811000d1000d07038039 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 208299631 1250 208298381 208298411
    0x1051606060303301e0603061b030207420c1b05100507020106080a0b0103230601050904030c02041806050a0605030a0807030e06070305040e1b0304140c0a0306 70
    0x2240c1c54540000034a1860424040711480140c0c02e2003103a010f41d5020802c680780d0600155448200c17809504209440c1c5910f0504028069044144011728a000702c9081541c86402228000d0b40c0c03110b103402034004070ba045003464001c4045c800b80100d14406689603034940c5882d6400314030b54040c1c004181010342e124054200740885604c00c014400c842d29010100c1c0c00050158205104017900060903580c0360720807401055641c0050b00c0c0b901402c4011428800100900340c10f0382d00880949034460040145125480d82503540c40d15281c001d040100034901d0308034296944507011f4100442000500d82c0018222006011034a80f80d41030f080910040c4002171150740c0c2c3c00380c0d04420400c5124202030019139146204900100070260014484c1c08141c800e901d0303200d00d28000b42a0343e448507814540035020340c00a00601224030007540010320040103110011511b080c0409485145444940710341c00e080e0a0420910814800d00c002465a500e42c159880c0046004040014980000b80381c42c2d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 208300881 1250 208299631 208299647
    0xb130504030f032c03040b0a0302040807051009060e0103060509090d021c23120711010c0302030411011115010909060b030c011e0e0d11010e030706051801051606060303 74
    0x11504240ca001090071204500f5185401c501d01844c0c40702014a580d68880e07841c1d442150011050759a020840050346a0550094000d03100800160f407a541e44610601c0700c883c00c0b0300000c4000034041c0d1000c0000d03502070144240d03038070010b00d0040341c0a5118800b081ea1030400756050f460350750086000340d0078aa410b00100602c0300e80e04415040110f10040300902d142e00307125040300040040703a2581441c40b00802200ca6070110014194a54600518043c018a484d5034850040d0f5090401e0741c1c198a1180c42101d200d02d9001030b5184001c50540011600e00100c075403010024480d00303000e400346c164904001e900030003000301d020413a8000d92400c0390907900d4409455002e540200c100103542d82e00a000b0701c018404040000d400d070111404100c0b5440600025030f40c00401c02d201035410f000c4c0395203a440100f40700b0b8944133810b00555084c540c1da0701c07462050800041e414454411200c251f8004e80040140c1454482d040201a00e1040c54182c0611030031a60030b41d45541c200101a005180 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 208302131 1250 208300881 208300907
    0x506130509180706050a1803030c03021603050303011404151e0b040b0415021504030503271e0102040317030f0708040308040f06061701050114040618050a0b13050403 73
    0x2803106068001c0b09480d0740e0f00e0079004081c05d0240120703085440328412070f00d06401141e0704003248400d50380d909003d00504990075042c3e0041c05100043c04582685121801c21241d20000851a6a2070243d840c0100503400361041d6109490300c41094550345030251140c050120b020b18410b81100c2801c1503000c1090643c05080212030034030080000350b5011041c1c6080303d50400794001c100c01042812800c1850040c2460308201d0b4800512040c168004003a610a5041e60140038000304501c2081c5102d80f03200c035115203a68080710700b101d0725079140d0781d014400282c040005400c01d07072650340701e0210400d200c02c0700300c6242011040040c1070410180098005d8000e08105415007003030389005000e1400100080e00d82c220041c003000411115902040052510202840e91600c140d0740c524003a010a1091644d00182d4014040c03091070103105c1c9030100e0760098554851210482422400351034020421b0385401d682e0414900642c13155001000380810320400000d00d85401c1c5800b0b0403d00010324 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 208303381 1250 208302131 208302151
    0x18060303080f0a090f050c1003020c0c0d080c2a04060509040807210302030403080105010311071b120c150314040809030109060c020a06180201050a08100506130509 72
    0x1010000320350080902034100c1c1d038500511455588803240000548898003004041d4a40c10201c441404404a08014013140c21980300114601e100b00c1103090380210241841c19801006d8040c0c010300d02200082e18051207190100e0400080d00c1341c841c00d107668800602800e2098004928818104482c0c00300d800c40c0031541080041d0422011410f1040c00400041182100042c03c00c148044c07079558400c00c0043c0800b18000d1505280014083d401c141d80880100b1003450012400b50301a006400020040040d91418861103484003045403032227905d4400480307015000400c5010729006c132004d07030034010401c14200900e0031000d80c03802c1c00e218900c2c0013014a400600031a501040700e44070707000f682001200c0d444110000019005010800c0010300c0140742078103500c40c2c545c010800c00c020034013540c003c00a40b0000310f000c6408200c0b0090090000702d0412000b1015401340a145402080d026a031903007142e00c0300d0114060380e0040380010b100e842c88103001c00c083d14007182616031181c2101 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 208304631 1250 208303381 208303391
    0xc0301020301120b0c044e060b091504020a0c0c06020d0206010f050604060311270a050f0303030c0310030c030807060b011b0b060414010f0602071706010603050c160c18 74
    0x240f58030380c1f50840c6142042c88030308200c80042240c00d40e1000e607039050b4078501e1220b500a0692035545000e0b121030808640075410461001c1c0246030901c84a442032900000c03a030100b510034004c0000030362004c981442403000b004041c5c00421920710011020f03140741c1e00100144210060040e05c0c0800513404220703926070f078500510581d19150150780444020341808620010f000c0840d0204e030090310708001a071014240c201ca51520ba200200020841c25100001d401c0c0d00c600901c20413003012400e458160f403080000c40c00b101200700045a00c007601c44400b9043d162130f42d64030140031407950300c180c1d03442d1404119141409a244250352461109083c81a044182c810803403006015110300941114003020005085403202c0e08800700c80ca1030b00c680c4d42502e43c1c440d0800d00c8c240c02940942d038010700c99a03501241641c6040d48801540400c0c00090405a01e040740c110042c1c00000e02a0101c102c3c140007010041c404100c04c0c2c25160f1280007640b40d00c2c1c1c144541000b0303c40801000c550458141 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 208305881 1250 208304631 208304639
    0x603091c1e020105071107050901140406030b04050a0c09050403080f1b04170106080c01050313060f0207030806030628020f130b03100906050a06110c0301020301120b0c04 75
    0x112000090314114100d101098024800e440819101801c688a5840d040900010300da043d88413620a205030703120203040002011140341d54880c45d0284507081500350006110f91560110b40d46548040140f02080190303c03559100036800c401d813011181035010300c1d0140c04000181c010b020142500920070010b80c601614003d1031050042c1a40c0c0080c446940440c540c1c81a40d00400d00c403501410b8299600c0d03588103188922010039035104241540303021004140d0300804189880720f04c81c165582030645c0c43d0880144001171421700220340c2240d0361801188144542e0000d0000c1038043e8842000d5441e00380107140c02d254004196010f590440e02c200220b4501e8440c4c8101c645001640068880c0d840400c14881c030301c9681210a1030122101c40020310003816001548502120070b15a040346030b50700e00a0058440c907000b0309502000e0b0201c1800140c1c852110800e503040940220351244075a90301007401c81e442038209130140b45011110005200c202a2059005071100122a19091030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 208307131 1250 208305881 208305883
    0x3040803071403072d050d0f09140a0510031e09022403070c0201090e0901051b0307020d05090402091503010f12022b05030c1506030d0e130f0603050708010b060309 72
    0x3d09403525055501141d8085d86083d1021041044075500c0401c554020801c01c1000e42006000300c0c0c0c84001883c124804a200c513032400214004c604040c1590140c01d007031004000c030421042c41e01c81c1c01c044d40c65001600d101c441e0021003034031290745c0f40c00040310740c03560040c054020b104160807540c0249031030042c2406241d08040381d40c410050301d020117050280f440100d5101030650b12a452480c200c5062101c00481903124602601070103007008000d4640003200c1d0414001201c061002d0b0308060002c40c8954018002001c0302c8200500c0180742c07114020010b103101014000001c3c030400d0220041c0300c15002040060003804180b40f4445a091080e40001c042544006d0240b01c00c1500803c0800b0003101680c00c0e0b4502c1c1c1e802000c1d0b0b91928400b0820599036504c00c080703400311845200c04280281070104641035600c072240d40740c0e20b0303001c03454050000804d009030b21a244540e84076001c4062407040d208010140d442030b4080c161031890280c1c0390b802d40e204c02911a01c03036001042070103407941c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 208308381 1250 208307131 208307153
    0xa030f1505060d060b040801050f13051504031202070f05060106050f160317040f0302010b06091e0109050303070c050f0402030c0a030f0b0d110a1707050909010b030304080307140307 80
    0x1c011204a5943c5950f15525405000702d54080d0fa22403101040c0401c5100d010742080d0305c1088d003182041100d80c2e0700c0d18425038400074220094196004014114410500c1c0084a0340c0316000c0e0a012002e281d08109000c102c0c2e01c04030043d60310720140714010003040401d0101c9401001c80b4030b0031300c0c2000c54443c0e0010305442a00044920300342402c161104150284465624030a00c85405524624007400c000c8403034081c1d0318044006520b4000318201a2600c882a203040c00805401d01107400c00840415040700000031046061000000380024666410030080843c6d500c1a070a12090301e2414050010f0b951011041c544598014010070450004e084292100c01607903103000309404090a190000500218564641010b4195003000038007191144042c290710b402e44910310100c1e69582c08800b001c60144101050340c0160104200c14a40b9100a6802c0351001000080402110002916580c0079900c8442d554101094030024440c85460421400028101031450a4110740c2c03500705100b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 208309631 1250 208308381 208308389
    0x1312080901022b0c02030a02100801080c0402070f0602030405070b03101d0606090603070905060d381e0406060e030706030219030207150e03041e082e0609020a030f15 73
    0xb000542c010130a540d0f00300034100a4030f4014000c0c811204020710024480c0c0000d000e880080d118a20062066003032520884800345c0c5c109403003c00d900301503607130840a5800500159854441d07039101103100b00079400154041d4000350700c00d02600707140c40281c6070b20b28101e40c1c0a40600c50404104002034440504540c40d400c0304a8a042e501d40c0c0da400243d802c034059800c2541c20040109070000403003610b510000742505d048950040d510320304400b5014030440000184c00301c2260701800d044908240e02d40110315002020543c280940c1d00d00030508650103980702c0700c0095900038562096060071311a80700584820f140544c030382011041c52820a030030850440c03040590024154081c0900341d490351a01c483c420f1000d202150140040036901c1c0c1050103985050310a0400d07107800c0b0b0a0140083c41144e40c048090407401c03403049040b4a1501201801c110403041c048180c107956151840703103502034a43c2d600c0043c0c6609941200a01700c0c0c0c01c0001040d422032a044000d0a0503001840c80c00842d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 208310881 1250 208309631 208309637
    0x106080601050f0415080111040e060f010e04020a051209010207020f0d0b070509040b0301150f0b040f091a0316030b0f040b0a050603010f1104140f010903081312080901022b 76
    0x5c0300082d00c00c0c0b4000d04c45a00c070b171845520703000035580305840700c1e401482120181c0c004490381d43c6840b001c2103081c075041403540b400302c0d01d4115400c2460400d84c02901400e50b40b420310034107041e4600c4100c40b2001040783e11394042d035070004003c021403038028603050700600f0650b16080640225980c6403420704028001d0b001344100801d07020700b0b0741e0f80c0c0d41144003480320181c02400a0715458a402c640d00440d0300034000c2c0c0214030b40e004a400703c02101079904954078a00c0a0241c10720b4190101300410745801104502c400d08592518961410040c0380001d00132440c98a00d00c510394101580b2a06000d0920401c2e6500d0303900b48004680c020440980282500341c00041649a08002030300505014036080d01302c9d41041110502848040c028100b120504a0a014102401d03000c00418001c15040d17640480c0c03901078144003040100e009480501c03a40080d643c58a0340314154400c07461402d80b811a0707684000541d91010756410300c00c100d29403180b83c0046000800f80814400d445e0000c9480d1420 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 208312131 1250 208310881 208310891
    0xc0803090c0a09020d0f270f0c080d0305010603050c0423030d03020901020606030a1a0c0c07090c021b0109150311041401110604020f1519110106080601050f04 70
    0x14800c24890702202250081a8408442c1e9440100000e50042c031504c000b45441d0401003001403030300e4012148001e100302a03103481134070502803032100c0f2039030243c00b540e420301d0b81780c0c5d03610000c0c4000790000050402400144100e0240c050020240c40050300310710101828042481481d944040540d03007610080100c1444403503200800342070310100c000c009607251040c2c45c039498640e41c15900404c00b0602c282d0079500a27554281c00d0555401706200000c4c183d4080e8000c44480580100049030410700d46c0b140d05142c218800240c1d850208640c0129540c140c0c1d4540c1c20103180c0d01045641c0c40c40c01e02c0030811051303104c002d0028241d24400e1040c15085500070584404484c8a07501c02254185d009480b6a121a141e0707030701003030b40909101201c2c041541d01603000441d040010fa140d200c4c680c01000d256a039408142030041821150155468908050101004103860241c4218450360b1694410031900a103045480c2560b0540c4d0012915402100043c40141c4074420ba41d13440010640380410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 208313381 1250 208312131 208312141
    0x11040b0901020307120f110a0503030406020c07080a2004052406070602070b010510140307180504020307020c1903020d06020901170f0406060b030702061612020a090e160c0803 77
    0x4291301c03640724000c102441d1402c0281c10241c12000031048800c15a82da41e41000a80d2425980c8040105002d800340d40b042c000500041c1c1c454008002164000303081d510400d964001e4a07262201100742200c600d0402082c90b088601c0011150880d0a022107007480207040a84441c00008504c0b0407551081c0036207480c11405445003422628a280c5c400c0c400c43d5510324600307181c031500c1e07028001c891041c0c03900366070302c007429100301c140d415501040820b85145495561050341c500750180840c0c0180c0d0301001c800112078cd61440558480c0030607401801d208548d0070301b006108803413042060650303e07480390103102503165010a500101d0340003000594880001c001070b180b0695581e10b41e00f090703049208201058007d0042c4d240150f01c141d00a00c44a9141c2401c3c11a5004c201d84036801607001000080450312011940c1103201c015040100c01e80c402e0411800585c1d100000c810042040c2c3c680410039001038a01259004050849001200c0900c1d500140340000e00b000107090b0800c0400451 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 208314631 1250 208313381 208313383
    0x31a100e010f0201150b0909070201020f0a0e010e0402070501051f08070b031f030c06020105060603010608061c050304082b02060606131805070f08010501140c0114070203091311040b090102 83
    0x40d0806140381e20241c84075540f12020740f440c0d0b00800c0c7ca00c1c0646c1c0740c0c101040c41640140207a400070640799200c0c1b42080c083c44401c035004203001080604009104004140c5032320f42d8401401054000d00001ca401d240c401002c1408541c078180c89000d50150450801203c100400c5010079155425030156403500c0b103c2003144c800f403e401718081d2038010507500100304124120490221980758000b4003071541ca4400300810340c0024402e05c008182d180c40003840a150003000031440301940c5204c42480303862030300c034149940c102d904140002ea02040711200c0046400c1d030f052a60040b03e111790110701c00c180c1c50003520b500f00070b40301c2c600810000c109000780c400c81201c2100608111507405c04860070141c1050054207054400c440410702004d80c9066880c0708001181c103075501a1034282542d100b05580c1c1440303511800900d11035541e5000d0301c201462903584501d014108a071f000790340b1070b2008801c21201c0e504d00c4031a040034916202d4051910104401a2006c0707490f40701c41541c9401c044170050b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 208315881 1250 208314631 208314641
    0x3060f1a011e050a050d0c0c0215040e153705030109121b050609030d0b04090b1603020c1c0801080f07051c0f0309090e0102040b0304060509010615031a100e010f0201 73
    0x111866420011000030407584010044c01c1503000b2256081c903220700c802e03040c107248940c0c092410824010000500dd503981d4a600c440c6084000c0c1500410f040c00f10b48072450b0411390700d4640418040f0f6144040044201281400504800c40080103101025035500512000c40d208981c1401b2440860106406c1ca002842410329049010303241c072454000d15413500c0b80e10903440c42040c18504140c005803030816100e401c4c0c0d0a40d12400c50011500c500300340741c0b5461900060401015000c21190524802c1801480c1244c5c211070990889008500c8020f4200c4505070403c5901d603000c402c007011010300000301e00301110310594503070030b903880c0d41c0803d21405036043d00060030b484104455217040540c04203502d0b04460900f60300f08803a050390481c0c5800d074462441844480700c424000b0801040140d8025604902480e00028809582e40140000040034480510119940d120514200c01c801c52204c00904000c42e080100d5602e0140302400c6000c8841c03603581001040d201c0d03003800302d00035885 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 208317131 1250 208315881 208315897
    0xf060f0b0640050102010c1e0e040f1401030b06030a0209041e0804060503041106040605090103020c07092a02010c0801030818031209180106050708030703020403060f1a011e050a05 79
    0x400d860304002c2121182c0d94150724458180158601204909528400c10000b04101141c0c2504207280c140c034a0308440024524144590140e81c818180582141c2803240c2c040410310300703900001c0e40d0714500303000340713010350051a0b035002360003200ea40c20059032001c06181e807040d4010501500903428598050105d4000306008049150001e00450f11a400c00065449688988809000e1400079010300c0018001e5118810108100380560801903001c0d801500455154004650b400365a581e108016a001a01c2455142c4501c1c1d102e0180c40090354502c1407406800c1c0000d01402c0703900400103100708030511014001c142c003c10604851045a100020103040080c115914131440814840c26644580ba0480c440d40a12050040b418000c80ba0701d412144c0c1a1500e504200180d00c4a0a0707d0344020800010550300b000048005886440740d082514404040020100c1d800318142071082e41c0000e000707042c4206003243d000c880313100a0408642030000d06d880e5032141d902c6182a0384500852030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 208318381 1250 208317131 208317217
    0x1206071b08030403110d0201090309170f070f0315020a0e0904081207050d060e061c030c0f08070c1d06010f03060302030a0f03172a0d05040f060f0b06 66
    0x105103c10300da0300030843e0841c0a00c2c0426549101c02561041e13003255400071005010800f42c9200300103083e03100400f144480c00c00010348840865101e00300381400f10540215145500c803403000e00510098408665685150341421442c0c17542210700545014588111184214004400142046414426540746040004021280342031400014015801c803040140020707103441c1d800a0128580700069019100203415640d007036070020032a54503450651401d8013802101c502d501c00083c11003108200746e9002e0102d00d038071004d16140000ca101c4003030b805080c98484d021540c0c4c4540d000d003854550082403d00f080d14843e1071048082d405031003107a00c041d5160045030250014021083c42d10060584a681c6044450030a2a441503104106a407031221204000c43c00c4818031061141c80e586003c42456594103140c4a40c01d140c00380c84c03040354129150440b0700010800c100e4180100c41081c25048824085940c0300d0700452000d02510400b0b44280d407c10301c140034129101c0e601d69101c452401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 208319631 1250 208318381 208318387
    0xd030b0d0f230f0f1b180a11040609050f010302040501120902040e030d0209040e01050405030d020a031b050a0207090537050708040507080c150a030f021303020406051206071b08 78
    0x103299641c0300e4209090502840c000c5c58190007007140c03058250010040001c01d00d000081700d00d1036011015500405110140c0d94806801d4040c503404d00284c0020032055a8408555042000f0b00c844148040391031814940140800e02c0180e82080400241e44041d000014600b802800010058080080c6003001da000c0041c0803000303040c0365002004030030400d032170603c8901959001c541c00c0311000ca4000d4000c1c0c0043c4612040402e5540042211707210303a02e00400e43e00803a00c81c10030200d906941d80ba0216000180283e8019010b20074400103001d1214100503c2c541928254115107100c08a044818900d200081044100c10900048140b01002c00c0104c1d1424200207003400e00151030944491003903100c0003464980c000303603400040d01d0103011400a030000704102c03d403c1e00a80008802e06448401d025000c4140303101511408c10380306600d08030b03a0b01c0d40c010311085400e981c000c60f025030710035440341201707440000740c041e0004001d2501602c82100e400d003031341d0b4814004a008100f06800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 208320881 1250 208319631 208319653
    0x2070b06120709051006140a0c0b09030d1a0118080d0e060c0111040302090f040305250b0c1e030105030714010203070b0a0f0f02210619080d030b0d0f23 67
    0x41342c0380c80c0603900d042c7c49400703e41c209040208280d000b41c8504200095202045c0e07000644449200d50300940709004807418400c401840c03200395060b05480c8601320101104040403503130302404e1421031f43c030440d00c0e03500c110f41000c2815484020030b490500501500041c21032158807007004865100128500070841c04505120540c150350140c80103038403883c2100082820990412034103406194140c40d154641350001c0c410b101444030214a030300c003400d00c244c9400d01140460700074610561140c0600c0703079501d019899549106411602580900c00248014400c07501c0009002003610304070407905a5505035000101e1840c4526180103014840c403000344141342010380c1110540f0141c40c0d205000703151140341208124020004414404400c00758103402070102c9100c00c50700300758090010300c4c40d6000030303104107041d4400e076101140e01d9101d94100584558144907070851500d081350414804501c03512004045180713100c02801040c240300000300d04200e0412014200100c205c2035408101e21 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 208322131 1250 208320881 208320901
    0x6090f01050c25080c03070e0112061b03050a0617030f1b0a0c050a050108070c02040518031c060b040f0b0f131502160f120609211202070b0612070905 66
    0x714490484c061090700c0e20341ea058900842c9003400e54a107280000d555a10380b002c2c6050a8a45c8907007074410a43c1e82a40300010b0082e041e0090394807225803008145420028880380458181e613002040c42c982004410b01c864030040119210001d11100d115160315004680e014801d11441102519225000480c41004010104c140490300125038042050359580015600f000b0101c44c010300040c80143c40f20010720f0158000f641190240d4150051081039103002444e43d8003065008281d03401055924410030b645c2d0103040007070305180c0159400c103031030315500c4120300142d4052007411142c08517840c820001241c0907140134028038500000420348d01c0d990824107000200307801c4014004c018607010400714441e03c07002103600b410101c00f03020340f4100300c2c0c0c0e212380c11075407085890a0711030101402207004803444800c20200c550312440840c3d0111400307086080e03004c0801261900600c0104080343d013203000301f94410416a001800320300b07004012824004540c2002021070701c1c16003806500c1034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 208323381 1250 208322131 208322203
    0x702030c09130302071e05040c030b040f0204090e0708280c0b37110a0803010b090907020a0b0a091a0f01090609090804030f02061c1a06090f01050c 65
    0xf029400303aa140301c1d141c01103039003c0030061010704031101c0402c00070802420540d00021506c4a103290005078002040006002d85010603c081081900810180302d480d000c0d02c03c02080c640c640780280131092809003070544400c103ca44e1013810321b41900b090050840407030114120103900100b541410342e02e1740701900407504158048007940c550503ca4a0600010300000054040c80c175480540c24140d91500b2500522031078680c1d42c80e0f000d4a00b60000080819010b07501074440e101605440321000c02c280801e5004c0209200110350007c100c0070302140395902555044070070b40c81c002c10f8011701d600b46450705420190003080c8508809081007100800841d26a0580d0517100b02403054039560410b85040c1d4191960141050100300302c00c00006a201d0790164507a88046c1045003000b0100c0c0303d9002d1424500c525410b56a00c600141404c10500c9c0e010010b11703603080750ba07030303080071584404102601072090b0424144403001541d140018002c12500c420994001c880040e804039940641352621 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 208324631 1250 208323381 208323383
    0x11040f0b070b0f270c04050a020d050f0c0d020f040506120105010908031e160507030f29060f121b0f101d0411071101080c0405010f050702030c0913 65
    0x1039410003042d100d40d49102101d000780000c00003400c40000e0b0042c00c0c6880c107a00a4004d030b640c42020007940303640e01c42d8085c01c0c0c45600c01d02001600d0b2054110481309640b0024820321a412044d81004914179140d0240c80915103400001a240c04c042c4189190034400c0f5000654041400700c1c0d0740f1006182c00d2403040c1680c0d020707031f501c8c81504c1e524103000359240034000c2c031070240e100041c0c3d07040642d545400c060500036101005060415040340c88890400a5581041c0c407625800f107803440600118810707840c40c400469910044280703e41e080c0a9000001038805882050b02071703484402651503030500900c0d000c201082d28021091860300079110055495100e0040d5010b01000a9903e001d010440e00303d802030720341081300e080700c0c0040e10922411611417035125555156699002c140d030f0001d010000d108410b42c210a03c1984009010414014081d000140080200b844140d0b401802d40c110b00c1c00c035007005a25003c2d2071000a003413002d485852900141c00c541040500c1808070031401c451 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 208325881 1250 208324631 208324643
    0xc0304050114010506090f1f09090b0f01050403060203060414130309120503040e18010903050408010e1609150503030705012304030c0201050d090606090501050a050d02100311040f0b07 81
    0x501c2c54141c140c0b107440d0b42441021390000d014402d580783da050000000700d03504001080e2030540203428a0958008007808480b42c0010719001080c0419100d40c4500a000c81b021620001c2550300d03000020441e2041d40401080d0f40c2d0048080f45140d1200e4018100400008084c140703d4a0803010a0b03940a10b08003003600010015680001c402e85e040780c0c40040b0765048000307145000d01300488516080300103130009411918141850703550792420311462802c01d200740d0301d1969491030061b21609480c00d80158451f40d4004884440f00c4040b81d5000600721900340b8008141c2c0c6900c00b82c010203646075548180d415000c0050400208034040d0b01c0940a42183e880300c10f903c003400d08426a10f00070440d03008002c100001e602c04051760040000d4030278039588510205103c8596500c88065585a901c6000d61070384920040c0178a1078181400c07009802d084e00c0c1c00d0418109a00020a1854004114414150b4900000c00c04845c00011500a80302580680c580e1a940740c0c1d87c004580d114017016501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 208327131 1250 208325881 208325891
    0x131505250305040803060910080d021c300b03011409010c090312030513141c0302070809090402030c0612010e0a020408030912030d150e07020607080106140702090c03040501 76
    0x40a0701900c1024092a0032802c01803e40d5161020b000000750003038061528081e20000004170348404101a09070f0542035806440302034001030494032900641c046031801e02c04201030052030b104010301e40f10440e40c204132507050b0000501c0e2081e001408100c0f031294040d424107810200102400300c030f542c020550030b0020403126459110807502c0641d240001400f1070f2841a9960000d4801d4004907049910086c00803c1166244d94030243c800480f0b080003081d8004c2d01c0b407041030b4220540b41c0307030504505003000e51030401140c0d5040034601c2103850341441344131031101040c159141000380c81d01c0c1381c41c0605100d64030030240313081c0e103000316003407040440b4181c00000084010080780280d034100d8070528011410f0a5041c8204040c0302c1c039408908160744000e0081e0b08950955020361401e9881034042d02e6441c90418400301c032890002041c02d001d640c000c00601c22000e600c501c0e828116441c0b4500312203400410301d00245c1e24852100080e512511120910030701100200085001d2803240e402042 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 208328381 1250 208327131 208327201
    0xb03030a02031c09170703030f0f0f05011502032a060103051b03010b060d0915111b031305060c100507111e0d05070602040504091424131505 62
    0x804c3e60041800180012441958800541e03203001c040c01015119044c08640e890100c15604c0441d0302c940c1c0407050840c2c56485420195a040c840c9034054150300c41c290b6111805914040e44c0d91140c04125509000b0003003040303c80400711124038950383c55803415503d542d40d69062644d52845100080340c40706c082c0c400c011080d1b180512a503c1211030140806040222883d0190020410700c40300f0307249020300d1041040c49646038401c06210803049c03101192604690202c002e0388000c081c01c07402c0a94000c12580120107521a158011280121203050361034014800050078405031801c8410094104030a000c5c0984d0000000105c0480040c01c950072000c6078840001d400c160b003440c0b9409508181c06034200d2a00c92070003080001e0061101600d05a9118042412103240b004240d80440c00c25462000c503071340c2442100c20001c1a24040b400300100d0f5074004141c3d000140c950301c100100d82001208120118429288202e0040c1042001c0e00c0d01c43d82c07880c900f03241101003004000044076204 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 208329631 1250 208328381 208328437
    0x50f03090d140f0a03080108070515070b18010207050a031202120a0c021e010b0108090f33070c0c091812020304080304060c020418240b03030a0203 65
    0x14000030350052880c401c449141c0c8800d0409202d403181c0e8446400f5110380e10055500400114182c14401d0351004400d616124000b07050112541000340b04111000ca21011112100300341c4503401e40101c140001c50f01e8160f50f2041c008403406031840194000704496090000100361080368601a4075903104515116240108910030442080708420414010880780e02d031030790084000102c2801121004a0030388641d4801c001e440c041031084da911030074100c1c5c6950340520002c0e04179402c072005151800703000508507120503160107100580f00001841c000340461441589030560200c10040c0f21504220800030840144103009a81907144e41c800011612454490081c11a9001d1b42041c5c10091641e0307880403000010b50780c04114070040c040880c0d030010920051006001e1901e901c118070700f0300e01c140415101c810000d9507011031808900340c0810400b803a0001a018440d18800040384000046802004100d414503094440841d082d40c0c21900040244078030b20105040600c541c036100700070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 208330881 1250 208329631 208329637
    0x40209030613082a0d030b2b080316030c0518061303060606090f05010507110603190c020a0201020c031c120204050627030705061b0a1b03050f03 64
    0x215400d41d00c40740c00200256052503008030b002c1c0c0702d4141c0c0c610b090724480348003445041c072148580c1081001d0036a502c1c410310420901c00e040384981002d0064800450004016071880c010340081050707035001c11190441007540074403490358400d072800d45a05002401c0c10f1400810141c031070210f4500070081145074020400d85441001c0040b031828003c90300303000d006079600028401844045c0b48503021001482c14065080608069500d84150030b141c640c03504149030071503200a050000401603840418400c1c0352030680c1800940c0c0059684c5c480c29407500308441e04584002d0f84510308440c20203200e80c04655000e1590003682100e240380001420161100c4002d250400095981850216800e0040100c03c3d0085640c0b2401802c10741d031000460056406103a004064040c0311030300c00592000050110f040c09003d0703005141c01810f100c08a10240f20703407a034484280f08810400422203104228900c60303281d000c8083e42005c0c0c08091f840b0b004030800c2c00106c601e03019400b00c1c80d201c00350010030307 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 208332131 1250 208330881 208330897
    0x905040605280c02010902030f0c030613110f030a02030a030201021c331502060103031d0102060604110f040906030204060501021c030b2b0b070c0213020a02010b1315050402 76
    0x1101d038007858030b0203420010300101e040e800035552500a543c0142e40e0901035a407003041d180000c2c12000b69020101828107c0003012480140410440c03040410b40c607864200d010b4009403a0b5080f100031020020b0725004059000039030520915a048007015410340182c0503e04100c0419140640c0000c00b0744180c88101c5050b0099000d496030890b0b48104031030720511400c0e920b42d1088020cd03241c401c60904031500500076000b42e40404010020140d00000070702d1000c40300303005040075940d1080000d44418010300322030321494a50b0544451611810212005d00c600416220b0b62684e5450025020346000d1105034400c502c1c01000040e03a5002182100303250209401d542505a0048000d500408044800c40c0c0c022200300103849050014000c681c03800d000c10381d507024021403540f03410810800300030001401c01031508403c00058607041244445000c2c00e220140e16511000c80c100c0c0144510040143c2c003004280c4541c0b100702c0540d0082e824100000040c8100030f89420a02050f031250140d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 208333381 1250 208332131 208332181
    0x904061a121207031701120b0a0513020d2a0f170d0507060f18050f0705030a080c03120103031205060405390f181915050c01060905040605 61
    0x4200300c04000003001402120321904008122401d170512100c0542c1c8240c1040200c03010b07107500ca6085c4262a00801e5016910141c14411468550450b03000c00c441004000c0c090300140200504000c030341031111409009010b140c2030b1030f69107041c01030b182420622800014610541c030115140510f50310b10710301c0c01009070081aa4140710007045070290301c01c2c54240c407146e50711010700340c80300200e00522000d811a00300f200851042030070301c02c0c1400b60405c00c18215604c01e9104000302d0f01e0104100007410781060150762a04260307402c3c00c0c01e41c403d461394402140c244400100402d13811500c09004a04000b4041000d55141400d00c4110790b01503410440c18034100405130038000300b481001d05603840d580180542580300c51307140117254000350001e84901201185031140b00170740c00700003443e41001300d41c0c1c01003801c1149025800030b11240148895030f1069010020010b0055080380c2255003a6002003000c5541d903039408004140580c1c080b600182486c010844010503d528109412400d003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 208334631 1250 208333381 208333393
    0x106061403040614130b0f0906150d02040c0206090601090b01050403080d0f050a0b040f0519020702010903080a080a06080f070b0a0e090c040305070605030f06091003020904061a12 79
    0x100120303660308010720850b845074441e480000d0038645010564040c1043c4003000c00c80091528100d024428000c01c040c4c0d40d654403504000e10000d00080702900440407104c860000000003010848640c03c000000e03400604100e41c1c40956580024018840c4299206032113150b42c84068500071f0360400a841c0b400110284400c1c004a0b2644000380f0600300d0382d10000840107002c2d00d005041d950f04640c1180b500d580c1d074550311090b061070b016484c02982d45020401251910686801d40c05034025841482c80d9800f054070300459020307500c1c420165400c0301406407103030180c3c60014045941244d8103030070541005c500084285000854030103541c41c00d0050312500b410000480d5860300200001010009000005c111b81d4460030f5141e8000e500030b805155030b0714150300b0050700d02061b42d4000c1c41040420400c000621405a05164010000300c41c05901500d45403403d074419421a003001c0c1d407041414040c842000f0320b03913001c446007494101400d03c50100382d104003e0550113175148038050790401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 208335881 1250 208334631 208334657
    0x702010e1e0906040f05160306060e210c03031209070504061508152710061b11090705030a0c0801080a150603080c0f01060b070f03030b221a03010606 66
    0x1000c0e002c2c1e8008005000094011180b41c0808285c0303030150f41d4000f602803082c0354003612603458010130700074201078208980041d4003c40410728550200c1c41d000035039440b01c00c5202c00a10244541e5504500c000c080341d45940e40b0000d2404030100649040d41d0314810100c000640742040e000b150101c1c0c144500c2034030310084654080d00d25010080014811a000702c1c5903601a0b076030240e0307041410580d00b0724600d001c060300400d0416400003400385c01080007140e0302000103961003e45007420000c00050002c03403082625045140d0a0090003155100764440200301b84a82e000d8055442625a40000c2c007029401010545c1c444d2000c0c003659409411044400004c1100c1c1e214a131110398800d800010020b981b5107a10003160010407501d0301d1340c6c000c40310709814a5024000d03d0050428407224030f03d4070740655110003055001c548000e080c141c41d9111400340b40e03503ca04241d551208422903404802e043c0030a0002400020010030302c01d440715882c8590f40c00e05125800595041e034803080707103452038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 208337131 1250 208335881 208335889
    0x3031f051e0d0606031b1a12070507030201090501050f190c0f0e1f02030703090e0105100323090102190e06370801060807050a090302100c02150702010e1e 68
    0x10340d442c1621442d0b00c80324000002000c01c424504645200030200740d4090a02e040c0082e48452083c000c030745103e0038059220f01041000b0103d400c00c40c981002d6039a40181d14090b03000d840d9500d8040d00383d520305401c108050342c8444400f48603411850f48012101600c0d03801408683c1454201d40000704411583c16005010f030700d001062110082408a5126120204a80e0403801442810068001141520070035400c4002d46025000c0303061215115814040481c00016041d400300c8201a190b440138490306009010102610303090006c4a42541b400500c1c0c03501035800314644225000985c8204a022031083d1150859000001e160354a41240c1d54410f040d030100d05840341088843d8542c0b23420410781140885103c154a40c1c03508001e03503141c118054080500200144103002c801c10062034000d611012120070fa90b41241c185165280501c011030703089800e544001d4012541ca805455117901320030180c038015100340d076240e0900f0040018401c9c1c0c103880050301100149a95900c1174a450 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 208338381 1250 208337131 208337149
    0x30c0f0c140102040b071b06020d020c1003110a031a060405060f0309010608030309010c1805010c120201230402040b01031509181505091e19080c03031f051e 69
    0x18280005824162200016803565104c11b0080315016940c41103030004282c04072840e0010107060001e80b0343c800d04003c1c00303504d910054500f1881824001d14150340c6a01a901c82002d441d1004041a1280003030600900100001d8031048680031486009030000d2618030201c0d410b071034025107400c2c181400003540304d040c0e0b0400380900b4000c0d5284c000109040c101000951700c950841800410710b020903000292240100184c2d1121032118101c1c02c1c00a6604913041c1c20510782d111040040d08141030504900421003945484a8948071f00301c4404d550b140329803002d0250340225001c00420b840540194129901842d0002040310b822404100c1e0707169075481000000f40b00c9190940500165a1300300b0750160340600d413548141c0e10070038401c01c40c80812500c0c0180d9242101041c1c0104c00107a001d0b176442085900d0410940101031190401c0101070a445016a0150840e0b0b1a8184012090107200e42e50868424100b40404001a1881e01240d013058001d0004000b1504607004006e00c03500d16 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 208339631 1250 208338381 208338413
    0xf060630020333060d030c020d0624080105010e01120b19060905040b06030d121515081b0f07170903060c0903010c020a051e10110307030c0f0c 63
    0x2009004009038046003030b0309280804041041441c100120000403600800c43c050546806410703c100e00c040080d03085804517003d250121181540da441b2450480041e10b112488a00b059078908041c0080101d402e503600d00f80c641c090000d020f180c2c0c844010440a0f44244500108d003c0c03030500760b00109982c2520160441c1303038140302c06881012601e880041e205190b0010aa9903078402c104003c0c440b21907451504402c040303000c0e204070034000100034044030703076aa810702c007450b5501140c01101c42c041d8400401820344040b0885414482d800c0905298021130342a00801c1d0724500c99040948000110780c036800c00d61001a082111a1300d40001246012a0a03642a0300030021040c031603904115075881aa160200280e403200c81c141814251604441e941c425580406100c01c006040854401581120003003600a040041e041107880c0465144a210302c0c0c40c50601d0380404140c5213401584515101e032028003d400030b194003120085075001200c030010702d016400900245914566001d00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 208340881 1250 208339631 208339633
    0x2511010f090e01140f01022a01110105100303080f01030807080d0f0f0501090f0902030705090406020906160201090b04080316020a08031c0b04020903030f070305160f0606300203 78
    0x1d0746401c80e1421400003a00900015030440811034014900b40c00d010700050400e2010f091401c003c13280c0c0c01084107203c82c03030109558030107030441d40f6640304480f0505101d03c0e080c0207104909051031101c3c800c2d0703000d0100b600010725180000b0b40d4103a6050752141202d910071121480d1003402d03286c01c4595008070b8807400e103a03622044640302081450260072244518888009800c2d4500b0034488215088180b40c841d12504181031203016982c0460314600b03c4000342c0f640c1d180b0740d4840c034005000b88a11201c440d400840840c10544030000c0f8084040014030030780304c8003000b60722018000070301d00541c8180e8219501c10050314000c1c0b000c6500300b44402d4400341ca4850100e4998a103542190000d0751020404a0111789183c5c003007106026560f200d00c000d66003146090b0768640480e0300c920a0340805a03451500240307220030103100c0e2044030300080301c00741135100003001e6107000150110011820342d806800e01001240110480216080c062510080f07107040c4041c0d68281d070031100c40b903441641c0c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 208342131 1250 208340881 208340897
    0x3070b06041517061f0902250506090706020c0f0f15030a020903070f050102030703180909060506041508062e0b130f0605090906040f112511010f 64
    0x500d141c210701c80003403c104001058014800800245410300040c01d034545100801681c107610010410b249058510486000d43d0320380f1145404050b1402562031081000b505445c050240300c4041920f42c01401d5990581d21103030759440003240c0d20300103c2e80b1203502503100c0801d66414a41040c82000614000d0309504202500011a4a1540007180d481c40c0e90364000a030086d0360f20f000d01060002c2c050350b4107035500441c03c4c100000d59038003605030020103003d5a01d407900e05400002c800c001c02091080030500c00404e0314070740b1902130030081e1143d90140f420b007400c1b01d092070314001c2d20006550346031004004c540c0d51810f0305c00384807811a030407907034401c8400300c4180f07038914200c0e172140507109000f25540e0300d0380480741d4180c034007002d039211134030a1030851070900100c0d500800311503002004840d018899201c0000180040680c0c0b458000600d1070800314606120000c400780040300f044031000742c84100703c690440c01800071040c004010070244003050741e0740d41c001d03140941d10002c0c5140041d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 208343381 1250 208342131 208342151
    0x20f030d030b150f031501140712030b010e0f091519030b010b0c100f0212071808070e0a050709031a060a15020d0c050f0a0b150109030503070b0604 65
    0x30525494200c0030001946601440c42d05081c1492403200a40d6412146440c0044d01c031148503c50001400c81c2918503c00f10f50004243c0c481c01040e415000a074034510364a0f2414a41340320100004003080b400720307040c00a031001035801054402c4d0342500c00b8000750303c0b0005810401451030001452a07401001340380818040b80c030b907401200c4c1c1085090443c2e4043c00d0035400d180c0e508140591010401c1c0380c04000c01e01100502141030803000c808a14003054466072059400c010340a4210701d101c00d51a0a41000403c42c1e001520340343c00144000d410708180e0701c401c0c05544692260040c6000b480ca02c10116104030301940c441c03031340a0b26a1420301211500c1e0b5444080c00803034018103800c82c0030801f003072010a241c00390701c8000421105c141c01c101035a85180181d220416141d40c0c2050100080300c1e803041c03103003d00c5401c0d43c10f01d6940a590504100303240c50482c03074505941861400b0b80619034107070507500803c0e42d041926000402035061145959035070102000c0249540c1d0007940301c1002c09 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 208344631 1250 208343381 208343383
    0x50729030c1905161506050301020a0207290307080f0705180603130530041a0901030e011d0106090621060603210e01020105010b1b0309030d03090c0b03061c020f03 72
    0x3035a13184254a0501004502040311050702d282c0c1d00058801e9104014000440c0c2d000101c1c4000c4541112008203400c0f4580301c5008040300c4014074000100d4000200164541e212858a106541a80c1d0407207040d00d603c4801c072241d0150b2400406280b981c0e0305030f54103503d800005103600600700560300003440010740d45c46003420b5044d403010103444501c80001041080f00c0e0141400441740003c007030b00b0700d4908802105041802d484004a00c0b0303001503401c40c180d1007904044405041d1400a000d10030045401c1c0743c01d1400001c0507080d42d440c000010400c000540a140d044680c400e00b0805500c420118000107141c1100003168440c0e030b82d86000001032820b1160711040d1890111094520a07140340103401c0c0368604004904591520005015100f540c10a0b98200d9103108000a00b80c485026150f14501c510000c165140c03040c024621881d1350725401a10700300f44540c0d2070356600c0c5e9640001000c40c2c0000c0c0d0700550700c10300149220101110303510100d0348070342c002000c0000f2405010042 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 208345881 1250 208344631 208344667
    0x822080a05010501151403010605030c0d050906010510030e0c010f0c06090b04150b130c0302040909260c0c0402070201030b180f0c040303210603050729030c1905 71
    0x1c03103150751100e0042003110200950704001c02032904141e0640801c00d10060024030050103a1818410040045150000c521060b030301600d9907a0070030070240c1480c40109580300001d100d41d6104101c55080b030640c03284203005ea142c507409084020600e0712103000040d01d1a42c1d2070002081005451060400410001d0040c4100709000307080199050806003011078a02c0621041c2002c1da0b41044150301c42c40d02c0c3c0340f16038101c004007d0000503400001c208101c0103445158060741241d0b05010701070041c85020f0401c80c180c10b000109912103000c50036203144c1d0300d00640c80104da5030b4205203554a207a003410b4000b410614070502d400282110303100c00003407d051180781c12459241c00ca5081080440041c070040340c01100640d8030904040c5950740040c81c1800d82083d0154156100b02d100810000315000030011310fa010050b65000b40d110306040740120510400140b600410300c5000c1003626032041140e004402041c1c03610b2070105501128109503000c440840104203081001007122202c031500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 208347131 1250 208345881 208345883
    0x618131b06170703180303090809060a02010605090901090c06050a1418040f0608120702040204090c0503070219030804020d030e04020d0603020a0509070c14010b0303210f040822080a 80
    0x800c1d90b201c0d00101c0e0000200780007400f0205051a04202e800601c00500b441c500c1c107507241c41d0100301070020b803401c03d20070f01401c2525a040000840c1c2c032014560190002810741e141501c8a010300d07514a0303000d03426900a490301038115100024240621440307000201030f0303401c541c1400035121090a080503002e61000c0b03600c02c00480c002c1d04042281c902400303900002c1803100c006000a5040c51080c0b034986034000016010000f000941104646035034040d10010301aa0b00b04114100302c011018000d58400c540034401801042031910901c5008015030140a806a0758904150366507401d120002c03c0100702603050158080c0900c0c1559924002090901841c40d0045440c83c6184140a64003803550481445200c1c00000c02061560007140707403400a07000221200400070016402e401000f890030590b8243c0000070360b203400b804418940001b0104c141d0500d0415a44a64401440c100162070041046008020034022500500048850342c00c59003450f40000e40d591f6a000e140c4120200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 208348381 1250 208347131 208347137
    0x190315030605190c08150d0203030a08190501060801090507110601030507150509030606101107090b0f01031406041a060d0501080c03120904090c090e0a0b0618131b06 73
    0x1c1103c2040600020743c0c20200d048400d101c040e034200e8000d044660028400d41e03501200c046045000c1e42d0300e0400981c8650040c1c15170381e4410700b00740c0041c40703020200e4071100c00c0f1260792041c000009242c41024100c40c080d9a81503016400c0035000d102501002d4100810011482c1e109134040400f80600d9008601c118000c0c0052440c049030f403068100b007001c1c400e084c0541841003441d262004900140d101c10201e5002c41c04c0c1407400400c1d0342801d81206120300d00e01c0b4103440410260302d10741c00107411460855811000b44520340044043e66821032482c0a4802c00c0b1001c41e09904003504038a140c40d03e000b104180305450400860707007681003109060521a2140b00422140d85c0c140844042d2820541c050303c2c20802484980c189880382c004903500880d0717910b01210500c141044010f002d01410b41007881001084c514055403101c001d0b40c00e8482507800c0001c60410314205800c02e0448035511500307042d5942d462200b0100380001c2c84e0a0340c0441d403442510b2040000100020081d01150b2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 208349631 1250 208348381 208348391
    0x705010c020709150806010e09070e07211a04090501180f0209100305060f07090f061106060901060c06020d0b0303070308040c0b03070c0602030601110706230f1903150306 75
    0x20400714241c81d0f011341100d035100d218060034483c0500c04140a419075031010700059003500c0d080c1426280021643c0121100503030f11003271020141c0d02041020401640d0402c00c841c01d0134000340c640442d94810b5003640e6080352240800c4c0281000d801c04040a070003100000741520044507640e014542c0601c0484000c01c1c101d45039030840c5000d00c1c49682100d212861541e005081d80d890340e03521170010f004411110080800240014070455160700a41951210600941d56030240903050b80d07451481c02e51680180000038003541402d0072554100d454580c3d81c0d0101c031140751a624000e5004400490000e5100c042440980d1420030041c01c80c0d510a03a1020b03110720b40327070504c0400345a541d0040c01421000300b0a00807083c3d409110200d03103a4029000607500c0d201ea00068512100080f881e5909000c5c1103030000c0c000780c02c12642e2040c0c410402c9580c1d424082005070750014400e42181e9202c45600b408941002c02c040142c02c00d9541d2103040009480085a103510001a80c6a00403107810380c4171 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 208350881 1250 208349631 208349639
    0x120c010603061a030c0111032205031b0303030a0f020f042606091c022415030105010b0a0f021e060103030318020307150e0901030501140105060a0903170705010c0207 73
    0xe807140c14440030301510760000d010303d80d0001a03180c2e090307011030a040181c07081c0d0864401109000700c80d054174841075080c155104450707151024001901c10188a805070340361038116800c20341010900504018040d40c075564a094510740100507280c414500c0c540c0c24010039400e52a0103004001030541d040180c0d202032000851400e05c0700c840308441d407007600701500380300c0f0110b400501c0260308075818409842c440368420f01246040e4020b40c0440718840180107900c1c0418100002601644810b041030305581d200105150a036042071103003440e9000e0400120707006512480c2c1c2008070411520540d614501e04c0c0f041d01c0f2a201100c032040403180c2240004104040d0584901c4410008088141c1d000400b55000030b07454106e0741c404e0b20081c1c0401c2512007411441500051700e01c1d600102000e019584030704001d8004c10503c1e602800d03000d000000420289041402d981c600d10907560380c40c030128110b07600d000308620100000100ca10b41800700d00001a020f000e0020001d003107500504100c0c0c58 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 208352131 1250 208350881 208350893
    0x108010f060b04060e0603060409200406050a050108010504090303022b140402011b05010b04020f0c0d021207200a08160f0b0403020d1704060f0e0303250302120c010603 74
    0xc1d641c42800050720401040148a4001c0c1d100001103804039105034603941c0301c502140180150110080c1050901a00342c41035590020f034040c0c61403401c2d501001842c2c2c50b902804101015801614045164000100a1460300b60810508648a49405030414030182500d000346004018084811140400e400700c44418501c542041c181070761105455506054001a103000c1c0c84464407040702c0c4c8007041d90014090250402c0c0b0000401a00c11075071483c2e0403484110303541141000111038001c2038010503070765100145000104542610311842c10440e80d0f05d802c040380c1a00841e006000100910072a941d8418080c60014900d0700040c02c08088020034150f0b11040d00d0b004840032030000d1f075080c40740c1c1101d0300070f9400380d0f9415143c03180010b0460600c041c50120700200c5040c00a00010040345040e0b1000356810440d607942c83d500720700c18400c420141c0380e0040d03150b89030500d0800b4014134940500a51300e00007444c001e006640f404912003007150420350200c4110a0560744a41c0200100b0807 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 208353381 1250 208352131 208352141
    0xf0607021606051606150b0c01050a05090309060c070305120a034b05040809100f0206160c0f06060f14030303041b0e010612050a02070309060f0311030108010f 70
    0x400c1c1c0e410075805900303202e0090510f010f1518811055004074142004001281d4000c450502e8181c07175000026903156011480e5034041411508107508240c0444d00d2103007140a4070f4090207000c0c0141d418481c81d54280180c41d00400d1110016101d040c0000010070320900c8140b40c10107e4600c03465648041000207826221050007400402403440d02c401000001504420000c001c0f40c41c5145410322141d01c184c1410005d503000c1c0313841034941018001001102e01c000c0c07104003000e44840b0b00700c52402a0980d42c104c0c4801514002d83c000e80000344410030a4103a540141c01942080c006820030398580c0b0040d2400900c0c1152050741e00ca20034052451860304400042c60200c18034884644803102081c0c4902000c0c0c4001c1441700225114940111103074240380c00342c9a5800b6041700f940e0341e00341c0240b512280309245941d8600d00804034990031042c1c000c5401071a01a103a1303030951860b10b00300315141d13444040d100701055070702e00807000e984072428001c41c0204481c01c001b003600054020740c0ca080b92 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 208354631 1250 208353381 208353403
    0xa0e0108040506071d1c020109060503040f020d020d05010207030c170f1909081c17132406030609050606030d090b071502040801020a1701061d0d050f060702 69
    0x40200c004000c00900b00092842d80704607030345003040c12106941545a603944100c80086c1e0711a84021410801c1b900c100380040301d05000741d85180480b07558100640c0d961209442c083c1101521142d04005804d111411008091024010a09800703160b02c8803422038000f001c00b00c0008210000410912211352030712144202e011003600d141000e0312450149a1040f40d0000c100c1032600490741d4245409003011000070021441514108402c400b189001c00051044c598081555050130044e514841a9894400c203040c00740c0b984585155150004800303415918103028214182001c25444014000c50f0300841c40307008003158000441c54003e051143c020f05443c000e90160480b00070702a805007142049610012442d0364840c000c0c10500b007100e20150042d603146000080c0000c148505500800c0c00b2049550f0300021450440940c0d6020f100030b22569002070040e0f501d8500c054076800405000b10f0008003461242551903540c2802c060b012525135206d6004041048851501444492000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 208355881 1250 208354631 208354637
    0x90606140f040f150b030718030314030a1e0e07050402070206031b37020d02060105041d070609061403011505071b08030a0f03060e150310110a0e01 65
    0x1902120001ca085400710030300302840b82d502c60001c0020071280742c0c068001c101c10a4240d10405490740e42d4401c0da07601c20f40e0407d00089503013400a01904920301001c042d01c0c1d142c0d88140303803e2403032403041c6c9003074101400201c10180ea070a10549041090710b4101d0400400b51004180007440c0041c00c2d00b040040d80c0300b180214010460f100c01030313850808603135002c000c20000d02e100900032a044090360060324044035401030342e006100001c800b402826100c8542404410350541d4007120200d03103070b08801da07030200941c1c030450046c0701628264001605040e00b1f60340040c07800c0c040c2a0181e10b8046640c0c403039030110b01482402e02199074400075400003100030442c0c041ca5545007a100c0e9130f1a046241c010b070104400130600741e0802452420380441d000c40d400400107100d483ea0801c503100e62103060007102042000032011084ad01a01913078048500008a0b188250350300d00c903040b07240700d401c1c2c1c0e4158103010710a01101c0381c95980c49020b02041c1d1441100e0b40310a03103004040c001c00790b902005814 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 208357131 1250 208355881 208355909
    0xf0f07050a09020f0c0109030201050f010803070f080318011d0601060801081b010c05060f06210601050f15040602070620031c18030c050601060e0109090c0207030206030109090606 79
    0x9107444007007a00c4200d405180006955079004940124503000c2d21030900365a50138014190107044d815048140641d20000d0301440c10703681c0e9a072041e50b078403c90900501c5070049500040200744890301440c1d0145110352000320300404280d01d07508403107617102c2110746c4842c5d90703a502407a25010040280504000d041c0b480003541062401ca64030449400340030503035076180003581c0c0683d20481100480d180d100c8203d03100b904260444440810b0200c400c2c0780600080c40c0a5101e02250307a5400340c0e148500d03c00362030743ea42804140420303405000c0c40e0b10f0300070050802418910445400403c001c04640e070203441040d00300301000301a0444d1040d215003840d412074030385105990110454500380d800c00318100311809507046007806442100407101e20818100f800f2814141c00040c031420742849042079130742d56031b01e89406441c000c170b040704c42600043c4400418480d10308603034050001c00a16004036820030340d9a0b400103c480c0e009070400d9442c1601d4483d0a41004424042e0101130401484030003d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 208358381 1250 208357131 208357139
    0x1050106050412020a0506030a02180402090f01081e102115023f0f07270e15040b031f09060b03010504060b031506030a06020304150c020f0f07 63
    0x20540c003850107903d40c02004911031804558030403000d80003c1c070028100ca5220724281e81d400009401400d0b5181c400740b41801202d04529143c070807120744400040c0400c50541c0084011201345d00700500b0300c0181400e1041c40c980404114032224400c940302204181854244103160b10030030301c00124480703a4000c04084c4400148404d003181c05410707020800680300d042d044414185002d03180303800c102c6141d00c18641946000d0f0784401c4942c3d04d0300c483e00d000e515111840c0322021098116030b4030000a018144aa40018062a13402e0300740e440c0344008419151102c40a05036441c090703840181d000c601e03807075074203460034940610810807800b2000f0305200c5400c00c0c0c550b400d10503c1407210b5100c41d5540c2c0803008002d520760021000c40c801500800c600d180c2450084020084460301034400d200320500e142420003240e02d09441402d018014100c42c410540e5070802a400140c800c842882d40c19885e4646041e081c8102820590b10394010242d507a21008440c0c101854140e01c141c0607000100144 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 208359631 1250 208358381 208358387
    0x10f09140f0607141810030e1504050d0806120303010603150603050f070834031803020c0607031106070e1306051507050f070e1e01081005060406120b010e060301050106 74
    0x4542d030005843c402d030303161000b050517403034903c1704070455071300455a551042281d503159000c50684c080e10421641d66800d007078412002108211130081c030030f521815034030b5070091207461029080200980084820b01d84044440d0035504241c00520010350780d002c1c48200d00410320a01e000520090500300a1800c048074460922000248008180540d00c00410f0314030000c8112804061540c500c1407014030345140340d24080c420f0075181d000c000790030119040480c140443c103840d03020b94590020244d42c2d4144041c0134468010500503030034026003244c115103d60f4140100780c8282219030380c141a0400800030810402030714150002840d24080080c461601d590042d0003c200c0c100b081c4584482451a10303a1501002d03d40b1401c4600417100000741800308854918055214034101031000340000d885044103650910984506600071100c16400446913031203240c0040d4043c1000c144507071920f1103d0303041c40d003d40007160711480c02001000b500000a00903030700a0300c2100240910351401c6002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 208360881 1250 208359631 208359647
    0xc0904020d03180506040e0604110405181b03070201050f09010506010c110411041211040c0804020d0f0203190501050a0c020706211a040b150f0c010f09140f0607 71
    0x1e0510903c0e560440c141090b082d83c40e0003c1100030300e0140e072035440700011440384e102501c1d02c0703004a00f8050b054894060003410365069070000b0f0300c26204604990111003505a0103051064507110000007180c3c2528114002c6200d100160004034150a022208806d084001004c80e601645020240441c6c0c3e0f0344031120b03a00c400c1d0850b08040208212600140080078103000804a6410000340018012098003844a8450050b0b9000718542266010300c41074555a001c0b990006200e8000100180350021285141034001c03000b0800609032540401d180c20581c4408403401802002c4600401c04240135842d40880384100600020401d030b00b01a40da803030345000d12821302c4494a9241407800940c02c0fa1100445000000d0000342d01d101040c030507012840b403485010300d0800b8181455030901402209a00c00c9803240c00341350000b0f000c80d10700140c2010814411075501c8000340903200100323020f803480030381c040da20384078602c0c110000c404d10300155004800101d0704100200f1003000e03040041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 208362131 1250 208360881 208360883
    0x305030a0e060c06040507030308070203030403020718020d1118032409030d1b090602010b030a03030c03090506041118240d140a050606010e0a03110409080403080c0c0904020d 77
    0x3081550503001c1c1d000400500468411000c0c0b071040c2d20411090010005900b0100c902946130920a9103c2e03a4040740c40788012600500136a105120412100b052a180071041c1070b4812001401c0c402c40d00034070f1040e2540d02058005209000c1900b011600b02907a280c1050f400403401488843c55401e408144150014002901c01460100048000c4c005008a545061001d01e08021041d8118400e8070300700312b0290b014001912f00d920109003240144102c01581e00c001300104140d83e860765040300a13055000c070703000805407914280c03000a00c04008040c041d40c450058586552084020301c21000040030034900c90000ca4401c3c400d100707003a4181042204080e5102d450f1041e000b07404200542215040100001028041200000b4000c0b558842c020f100d042074401903118600112a8800f03902d1040364071501c1000d007000041d00780fa40d000341c01034000e0b0022608142d951120300c11504076610035643c40c440010040516103007440301c07036010072013200c08001c5810300b038011038611506024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 208363381 1250 208362131 208362137
    0xa020a03080310030819020c0f0102210c0727020403120305040c1208030603010e0726010f0e0a0309080607120507031b050406020c0d17031f060e030607090305030a 72
    0x101055502e00d00c00d002d0f00c095170300180d495581c0c200c0c0c0c8502d03409808886090500500510090000c2440c10b9060701c54140d105078000e00301e41248641c08180d16a05855080d00c003a01004000800300c0184400300c014801c210200e03142501070503c06400040b803003100c088442c4108010300c0050141384482001d0141842c000900d540c4501e0200000c2d022504011203d201044400e0100070340c410082d0302c5498194000d100e0440007041d43d5070b80342207a004500100180020000c01480f01004100549254030004107401c0000142c0b5401c5400d98041004281c00c040300031028143c20030000d00c002e00070b020040031285001c2c40010400d900084c12a5001600d60010601081c42900035000707400d00c0078042e19210015407000b91940c1e2081c17040d0000340c000c14140740d17100c3ca081035000010607005500721076100600b080007481540014034802c00601200c0d4141180300940c840385020b000c0740d40343c010fa494140c100705407030032000800042c100101c2c00d5050001884c040b01707560729050f040c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 208364631 1250 208363381 208363387
    0x4050907061b02060d091e0201022109040516020706020c0a050f0d02090c040f0b09060f0901090b0403060c09051014030c1e07020f0603151504030f050c090601020a020a0308 76
    0x10920810400b10010003a500c0310020400100d0709049502c04005203124840343c4040c04a6402c2004a041e400b032006400b5810144151511081a49489003000d00c0000a6854800d00a00080440c0c10680c2c141c04040510002c6c3d001207a010440748000d042c49000801846104038000751004100d40a045d0007080030b00141e43e01500d480300445130043d4024041c8481d40b030711000c104500d82091081039440800004001880303105041203034902d00c0013800c1c607403a01094184191a951000f048141000000c1c0390010f082c030142030142002e54420100481d09200d4004002e0840180d9003149204205203002061042c0d000700c220302000c421140788907102d41e00c10030a608940207400c0401202c032054000300c0c49800000c0d000b440002d200b2258442100c205005010842c001240e8008078141008007410951030480c1d1501c40b4000100140c5140c2916a40d64540343d16064074100c41e80d80c0801c400d035840c1d03d04400d50f15030004c3e080c401030409c50103039000500c00075218800901040000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 208365881 1250 208364631 208364657
    0x6051801270204170604110a0e06120a080c3d090606090c11060a0204060801090504050109060c020604060501080f03040306020d090c0b0c0105070302041d06122a0405090706 76
    0xd40640c1e00070081070341041404c8116810071511281d0840c0e044400c1601c2c02e00c0c0f4142c51074420400c2040c0ca50400568855941d0301007070040708004140c03401800d105440c6900005000c01c0001c02d40300e05c8900161080b00717500312084401400581500003030051800c60f01e2440c0360365404902c540300d29543c001c00c00c0b400c3d505142d002090150010540a130600c041046039680158940d91203028100440c2d22681c2c600342d40d10201d010358040d210000b200c000042202000b9a0000340e041070103a0300009000301c140da610411118003202e20000358201d20200028060349200300c1c1d004104203000f6007044d6490164154480c40350b030000a04d41030303011850b10841445940700140550b4450031080d5255107812003840340742c12501c0703101c0d129070030000020b0b000c600c01e0098034119200031681d010550345e224840000c00f000103141a4125210005003905151f08003c3c40c28a2405803507500c484400300402c0c0c0044503130404045000310308000900040e06000a41c000844041e45801d101e80022 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 208367131 1250 208365881 208365959
    0xc090607060b190602150a0e07030201260711100501080d0f18120b1b0a0c06020706140105010f021c0f0917060a0e0f0a06021b0105010906051801 64
    0x943c101d000c0343e414424013084d9140c000900d030010004003000d19880d50390f0b00002c1070036100500e55120094000140400055002e00c5620715034040304c2c0042c00420482c0200070000d00c1c811505840084d4111004501d40341c41440313000303969402003d09114a605007240350395903041208200c01040070789a28111058800c26607134441101300741c40c80703004130342d078440c0400ca40d8038000f001d641c1041d1003008140d0806094008003001240002c40130305012001d0020b881c002204001691416000c00100c0300003aa82d124040300f0018a00480100c1e506110006196409040248007503503c442c1e5031048801c2d540c2d48a60405281d4038001241d000134290441d40e81c46281d010304070b1030034246030b00180c1d0100410814803c4407442e00801c09806100e07001995185009424421900140c144c4404242950014400403542601c0a05450702200085003141c42c02d070b0140e1451a50303880d080c8800c0c500303a041d12001084900503100c441d41824030007242d190f0070300740711880c02d02d8141700c49010300c0d4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 208368381 1250 208367131 208367149
    0x12a15060513050a0615080408031015090905070905010512090c090408070203010b0d02010f03050c0912030d0506090609161206030303090c060305011a070c0e04080d050c090607060b 80
    0x4000d4420b15408141072902c801801081d5146403245040041c0443c400005155002400746903a1f510b250729100c0c0c0c1c5030b94420350700c080c002e00d0200c4070388100800e80062050b007606c1070422654500f0019480c150000302200d4000c2c0540c000c101d071050082080303070f0780034003036070703404019910b03980055282d40b000d50307240041801840750000b4010701004140040300018001c01402034000380441d40c1030340e040000b8040040c0d03009000c41c5444092089541c8a9440790b80d2011607099060301c0c18020100242d4a808014840d0900d0350000610100324021801041e8224800303440da44400c0c1882400111154401414503800c14000300030403009500c0344e44122001030101c281049420303200c0c28001d000d000004800d40340000541d000080a07442071280034100c92400d01c5c040d41050600e2607000e86540f00d41401d64564442c0c2c900402c01280041e000c3d402103216540107540c60038041441da040c1c0324020082c2954090070300003000907460300c3c1304581449a01000004200303401c0700008120341 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 208369631 1250 208368381 208368389
    0x90a090f020c0604080408010c0203120c0c070e09031e0705190609061a0108070807090512071805071b020f1017160216050a060507051c0203040302012a1506 69
    0x3200d044140400c5c881a1001041070303e840400030302c41c406401070140d9492050b003001040490381c0b400000c119460a2010701020680001510030880c0d0311502c00301095130664039565135800014000000c0c18012801c0d10380907a42c0200c050424486464007034580f0718800c0c24914a0400a0520080001507800007110390307403000f010011040441c0200c0000c41c5050800d034042000600441d00b424010310b1847e10840055450100042c105428010089554102001280305046002c200c0c2d102c903604901d11004c400c9800a410710f0b0100006010344a80042c0b440000c074105e9285000d03840b00100d035028808117541c030208500d9440c00032180d54030302a88007a000c012000601203010910394580f45407000503800c588a02100500440ca089000d00c54150b22210460307040003103038003038405082800d009500391243d842d40e0580314942d505250039143c00503000000c05000310340c0c02851400c81c1004090003400700000c0c06103a03000741034002d074020302501c460910005031038107140c00050140c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 208370881 1250 208369631 208369633
    0x7050c0a0302010b09090102070b0a150902030f100f060212090d1208090706031811031c0339030f0e0d080a140609011e12080706050c090a090f020c 65
    0x20020030709009000705010346141c1d1007803d890000c02c240c0348050007038840036900586d814000da22800740302c4005017514082690000940d910001b0725070614400707148560103614004402c2d02c0c01c41900e503c14003507a0010540790581c1e0b081400301d01d0340007501d130b0041201c0c00b02c515651070510000408602504400400b4550014240c20364194408a1103024038200000c44031980e8072181d0aa040d034444452586900c496880a01d01242800300c092910210140075101042480e101e00364070b84141007501c0000c0390b280c5007004c1143c080c4561440440f0f034880312118040c0003004c0712a85a01d81085200105500c1e80d405002121240d40a003140d809614210384042c88001c90150801074100c800180451800d1003000b1074a5850142500c180d01c010450030a981c02c200225801c81c0c0080001002d80032032000200b8800e10b0b4812001d1103502401056464101901d821403d840005100049041090240a03100d45074030080c0000d9419501003c5030341c0105050030300c02030095650300862 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 208372131 1250 208370881 208370893
    0x601030b06030c19050a02030d09020406050a03230307021f02100507030f0605030c0a05010807030b0409080702031e0d0c0602120a02130b0304020f01110109060e0d090603060e0402060307050c 84
    0x1440030510300614840304e00400d03882101c0e418100903225030040301d102a0141e00208010b0020190076031089140380c0c8000c10010342152140042403403000103800c211035005039400408050701c2104c11f040c0c120f40e2000011450204617034086201c011076108400700780365828440c140e80c0e500a0219070b0704081c42c980c08001600e40f40c0c1c80100981140b0001880d01403514170080b5190502081e04000030300083c0c0052000c910b000300441d07031031070001c03c2c14040503540c1501e600c1a50340c501a2928141c05050f20603221844c90041500b00000e800035800d0001c460034200318654404110a601080c080c10806014401da041110181c130030003044407207005400d1308012420300d0650161504090007000a1107860321080c5849861100b5103000c0d40c0007880011b41c20b461341c464040311007800300c518000b044408941ea601419540d072a10000a181c22205000701950f50142c1100300030b001903d42485141d00c1d000004d04015000340010340500300010014001501601c1120fa800c00c845c011100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 208373381 1250 208372131 208372141
    0xf0d0203010f0c0e0f0d0b010e1f0b03070906050309060c45060307080a05040314030a051503070b030a0b03070e01060206010e0109060b1603030e100501090e03030906040b0601030b0603 81
    0xa50041300d0304032407180b94003152500300d9003050201c504180360b000642c0c45190342818400004400010203480c00000440c0014070107400c01641603000344804542e80c0d89130f0603e00e43c0030b0205a80754005108210b014020011314110000e961031b0014481c0003075941d1550300b50410281c01c0c6000000c0d40081202d04803182210f41841d00c41d50f01d4074000d010300c600680c001420000b0a100a5903030000054050010444c3c0888650000340c0280c403e00f400b1008517401954000c1e903800c212250341c075595032a002c01c803422460740313a03003011501d0480207400f90303500b0124200d0150101520300c0e08800d03560288095151010460300703025100444c00315506681d40e0400035520442405070081c0c1010420000032080c00b01d000d080103903989604407904180a6480003200b00c01000029030400d41c82e80180b184804051092400300f00320340201040b07a6040810000a03103410b00c40541c6654000c2082011602001c1402074000d64003005040032a2512070040b00a00303540340340c403030340720500100b484 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 208374631 1250 208373381 208373387
    0x40b0f0604080708011d0a0b100909050d030c0f0906051e03090718060f0b1c050112020f0f031504050a081204120807020304090f021207020d0207080c0f0d0203010f0c 73
    0x100443c1c00c2c804c0241710440c12160440d1000d88021101e80840e805480c1c0c00002807082d0400f0307544240041c1c8520305496442524500b501d241030001c5c0d40640004640c515400c1d458014206003203a1418940480380704050010040c0401d442000b040101c00b00b0102e05006a4080040352160190341240e2282080030340d494480006124146000742103100031031990075580a8142140d152510b0541c120b4605800000194420180400440c0e155645181051118480e031070203000d00c21824406c2d054244103000c0920000340506d44601000b603443e4515a03000260007841c8070308212002d2081e155890311920740b190a03240248420b00100d002a0141401200188103500440700007000452072541074031004400d90f4100b0068008100900014005802205400d9540c000051a01c40c040180800c480c03016a408001030300044110031410340d0400a81014000c58000342c001025148001060040d045900d5406144a00ca8a8080d5a800e500007442074100e502d0070f01540000140003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 208375881 1250 208374631 208374643
    0x8070e0a090e1606170a0507030e060103030f020d02070b221715060607020d1403070c0f03030f090602030412020f0d0c03060c2303090f0d0f021005060d02040b0f060408 74
    0x14889260425030005106110303000f200c017850000e40d4042c5407074031608148801742c14020400c40034103031a09803041c41704008001d40c90095002e42d450070380f80458420000c2c01e14200c410f070340045503c22102408001280300442307449010640389072081c1c2d000e91065400040e021350100c4110b103c0c2c1542500240d002003010000c2c0005d50b6501d103180ea81d1101000280d02480201941100c580482c0c080041c20f082c0e050b0414000d44012607040c001e1a580d520790318103a03074104114500d501402042003640080781c5511003089410130301d03649418200003d58a002c0e40c0f064494011011841c8000d54446507010b90b803024010741480d00200c0705041440f40b02d441071000311009171405142d00f0071184240d451014803400d140f0044204200200066240e8201070201502c9000c0c0c000b10134100041004611180da10742e40315202c0c400c001100c06400c003143c103402d40d616142070074100301c055a113818407092040e504031000155983c1d0000880c05594040e2521600312400140c089030010b000180 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 208377131 1250 208375881 208375903
    0x30403021513030518010908010608010e0f071a090a0306060b07050c03030a020d0309050316051506040504020f040c0306050319020f0303070b010b0a0311030f09160608070e0a090e 79
    0x100c1551140c081c4000842890b070006800075409000190519480518100452a05240174a24103803200d110721f084690a50003103055030364800c1c010a0400f024051000001098805000d8542c038000b071240e1204419503002c030a003d40051001400c0d5540c0300500041c42e0405002c200071600d40012414075403004905958170f20981074100003a2070000112030075002c4030b5002c1d044001c00c443c03056005c0c0406100c122498042888660400c0204d441e4007110b4501070340c01483c1407080384075903003043d50014040324042d0341440c0410002d61540301c0414046070041c0c0c1c00090418000718100d0080a454104d035a060080c849024002c04241c7c4c1c1c0c800d041402103034903540040342503003050358278403540c14001c2c80c106190380100106900c0d01c01070987c481d81400c01040107039141d04060000e900440d0061a2004214280300c00b1a004001c8504003050100b04011040d0604402134103115008159004000e6003520f800c48a40f940f181e114001c024114090000d050f2a0400988035401018 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 208378381 1250 208377131 208377163
    0xc0e0405060a091e0c150507020a090507140306011e0e10020c0d0201030b15030c1213030c02120111070503071407060e191d0f011a16051203040302 65
    0x1000c140740b000b0314402d10a140781c0c000180c0c403403552103008407403894181311400e491809607000b0000f1014000d840381e124001203956080e584058900c100101c1103505e4100e90b400c0e0f450901089403180c1c020981c1c403001000b0040d026200d540e25030048ad41d00c0d01c108031a00310384c00e44a581640c625000040d1081c0300d44120b8400b0340e02224007904a9031401e0381c520481c0c2c4203148120717510155010b82d100018034540034040d1200d1070680a000b00300e50340280c94a240d2000000380c261440f482ca101d0407600302d0000c030304908000c10161001030484038800c0307000c0d21414000c0403d0340e080c0030035405100e180d40c0006085454074442e0900c07035100d40005a040d603045900912000c121030740801c1030f40070f0f10a141c840d9821008404184074550201c21b152034107131180c0c0c0030003003049a01c0506801000c0603040c8a40c00900d0000b500c03040e1031030107a00420024180302c8940d0210500700c0113039080090001840103507000c103800c1552400031a4413000102071800020305c010b1540c0801e00c548000e44c510 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 208379631 1250 208378381 208378393
    0x10516021011280f0611030f040c0e04050c040e03040503010603050307060c090602030406111504110a06080c161a100e010509040c060f030e01061409130b220c0e0405 73
    0x103d20305925400f00c41c00240079151440c14580040e05110100f04410701903000000c0d62200180d54000c650301c20b070764510315400c0d240300b0001000317820100c1074041c1007c61142030150600b641d90a9a80060001c1c8034070454440c41c004000500030410f4070000d0030300600034042c0c07a40e00c3c203169480c1e601c0244191000360502c0b0080841314003a45001c01210043d900452038680f034284216900024600345a116000d1515450428025000d0300d50045001d0246108509807041c1006980c030a694071000910000d081040103110b03032141030307a400610091840300c000c8090f2801564640c08500f02c2c003180301c116001e0006855101d46d02c0300542d0f44001881c182a600d070750170072071001802c0701c004000921820342803145602c2050303e096220268100850150301d50200b260a450150f0410024045c1c1c2022800882c0340c078558a41d00019540405040c10381e403511600fa0f0078000802040c040d520000c5901034030010440083d00381c9802c1f1401d00040c5403101c2a00e00100000d075415102e034443d103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 208380881 1250 208379631 208379653
    0x1e0207150c05220e01050d031211120702010b011b0201021908070c080109021c02010e15130605090f0409080403060603050307062909070c150501170a0c05010516021011 74
    0xa0110350741542c003024130651442c1c0ca01001c00c0b5204d81154812010026000c80c018030b141e000340948403031a0009158542c41d590b1240e129504d455004101d81700310380c1003000000703a03646c000c0401c01035151100e0f5a034818111a00061703143c030b9284245503078442540c1e4400018000920080c3c140c01d8860010520015900c1c0340c0c05003640c2d0a14006540503003160800203828600025101d92030344181818901102c003440041c01800508800d010550130008009050414221607203000d08540c1c01d0040c205140c2001050f80038500e20707501d900a5603506e000f40180a50442600c00966005c2018000031742c6a00c1c0240d281d40002c00c040703072054109512041c107a6444540c030600c0c3c001c4150f0441d11809d032042013050f8071001600030024001646401000b08072031400341114075440b0b440105031035240841e1a800100403510b062590f030030001c101c40014161810305802c171502440d0581d01c0e03001402000082c0c400f035030002940000603c8040d60026000f52a6820000441d000da880c4403c038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 208382131 1250 208380881 208380937
    0x1090603111f1b02040504031706150706020c070b07060204030c2c040c05100305060f010f051b01110a170a0608030702150705070e040b0603011e0207150c05 69
    0x410703103440c9002d44440d58001103032032003608030401d02d11407150010440e81554003c2821944103560640010f080c08075158100c49084000320b400900030f441d140c0120840900a61090140780c00c02000e5907000119040380039000c018200c0904004108580d4138080c07032520000079403081c030040b510350140c1400060840620101c04010700c40700440300000448015000c000300c1401841211100780c0184041104e854102d01d8001c61041e45e140017901d41000b00400c009058100d43c0e80c2e0410611030824640c0c658083c00740e440501c2085020070346d469680c4102e0f809410000d86801e030400c00404e03160a4682c3c00b9001520418244150200d0b80e2240c1401c04103070780003401448540d9100300040c6005003044106030f81e110241c0c480843c10f1441e40c2d80c80ca410803005031f001c1820301c0b006406110901c02d4940b0030380e401400c100d00030840c0110014062814007207044002c80b00b00d0740490050700703015407030401b1641480c2a220030044150240c201920607040074040c002815045084003080c120 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 208383381 1250 208382131 208382149
    0x3050415051e280902120111120a050103030e0d031e0f0e01020105060f0d081c0207020a1e06030b060903060f07020f21030714030c090f01020115030b0603070e0109060311 75
    0x2d03000f40d6400201005400b420040e10701c021041b13821449010120350414428810510070f00006e026090707440201d1042d281404c500580b0b0140a5441c100041002a4001e084a00c026800b81d5030207400e0900c50509540d081c2c520b100c01c8008800e143c1d10b1480c0c060b840010710306840ba86440f8407a241000340012800c03900200c808940103028001d41e1110362130f2440a08081511400f2003510b8100c880380081d4052120602c07414030355401140600462504603e00320291200c0481c08070341e1084e01c03541c20f00c3d640540c401c0e039042c596070320f226800e640c0710030089404010029040f9a11802c00c000b0009050710101d48050060256420b030138030001e00810100000101505440400030303494210b49050381c40038000303005100b070b03019007180d07504400b901551080860044207515648490140503840182c0c1807994116407400c48100d8440881c2840364050300e0700000f0780c0900c0d980d4940030915000d034540140d030319002002d000294002c91340d04030341d054030700c00c80c01d10003003806880078015102 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 208384631 1250 208383381 208383421
    0x9021306020105330a140306010e15220e0601061e05071e050f0309090a020f0d0506040b030a05010516020a0c1203020102120906040209010f060f03050415051e 70
    0x4202c182c56500313550064540741d01ca550380c035003204105505100000c1d884a81580c400055100c2c80c60204020346002d022640c01030402081d40b038a50301d000605d001c04280e00003401441030a8404000c0c03a05004810300da800241001800c01098150592040d6078003000d10560001480300524018251410b0003000801d04041c1c07299070601a0641e2040400c1c40c03011140348595009000801c0498020020660344008500c05190b03034107a05002c0c03004000005007400c0d4041d00400000c40c0b40c0070305108890044154450000301f507210440000c000d040f022941e03c1c0d141c404d1503820410700506601980c0240c0c41a07044480007a4180000d0361a4150701c2c501818010441c4800c0140620380504448503a01c240700040c6081c91100e020081404290340c4e000851b40050704000441c20003082d11405040304c1c840500391180390510040100c000c000d00b220400d81c030b42c000708041005882c124008003240103414010340c54032040d10403c11007001c21484840c080000800c1070034040e010310b44681 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 208385881 1250 208384631 208384651
    0xe010b0619120b03030a090317160f061d0c04060905060906101b140610030803221707030f0c03020a08160c060201022709010905130b0109021306020105 67
    0x8004011030540720040b094648545003a254900030001d543d0a00003400307100400e8a90300800c034150f04010520000f814070280301c28008000ca480f08071840300b0142d0301658802c64552205005240003c041d0800f24841440d8901c4d1048454240c00c0204264000004c10707038040000380d07610001d0200351a82a500c0b1500082d0003804942c560a004c00e0307420701c454407401d21102c08849030414031809402003c003920405030342610801c030031030140405500320440c01c43c00300c07a840c296100c01c0d083e07100151041803c802e5040340c0344005040300c512150416040900e50032081c10070304c24007400f0b0b40100c000710000f03445060b03080340c014001c010f41e011942d003560080c541481c0c00e60f50021142d00c02000a261108129220000511040c1611000e01901e500158440403a186003050701c103d10300c5040d40c2a0b480f005210352030307103c2d9078400781110b40815000ca05512180d070000500c0c090810302a00c1103803d000007140c95400c07a00185072962541040780a03c55071410105d00f20794003591140c1c09 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 208387131 1250 208385881 208385917
    0x306010e060d0203030f0f040609050907081909020a181d07030b060402091003060810110f0706060308030103060204030201090906060512060a0503150603100e030a030c0203041203030e010b06 84
    0x49091054030002c07060700c090212032900781c05d00a014299001241c8103624544001801d00c14aa44010480020001640d041c916800c203802d0140001ea0014900382a0308410f18800e400e52110790444041d5a40182c04002c2d100e40310042015042c16a884040640e824014013161090306a5210030410710004050911141590b0b075043c130104c0068001c50303125400740248001d555840b108184001040d40b40015194030307040409040500381c1da65030f0701561622030840c982040e440d088841c071090812040307940d5412441d00b0b20081009400c064108c0030080004020044e80d6801081501e000341c884440441d6100c14082c160f4405000b12030000ea02400f10079020b0b945807500d1a040000101002e00c0681c6510200385445003084d1900561a60708080c00f04038101408100228071070801c0038010418000c10065691040c1c03c03401040641d43d42c440c210540c420300660300a4003c00030200d82c0c0041c40d0a0003805040e01210000480d480c040d5515000e18080b400c99800d04c50078080070700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 208388381 1250 208387131 208387141
    0x510022a061905121302090603060903040e040804121b090b060901030903090801020c1005090a120c0606090507120c020109020108130804030203030309011b080c0f03150d031d0306010e 81
    0xc142d4145030400e814000c00380b00b2106940f010b40c024a100301007506504442c2545401007066821010306140e02039040303130043c03001e000400720444050f00e40703c0070740c01080d40341d03031501501c103204076400985001458100401001203c41c0240c1540c40d90100c1d0220311030b00d440380b00d001c841d110404c05905c12020071150105500a422a01d0f88500034108003e81650300d00d821400d9a1000d10603e449402070515070444480d140b04907900203412100a0080c0d101320360780c441311030703807050000720a2048102042c020400103401540c060804035000b40030505001c10080c1002403003000d0038a00714204100000410700c14410500f085805a4403050107440b41c440b602c0184071030000695080d0820080400513840400c001e6000341d141200004070380408405071070b07960b40a0540c0034100f0504009000c1884c586000740d5000d014881e241e00d640351520000300700405003c050807034105150110132014960800401ca82615000081020301040130040584580e82400b400d4841150034011030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 208389631 1250 208388381 208388407
    0x1030b0c190f0201020c0d0302030105190f06110f0a0501060e07111f02070c23031f020a0912030e01020105100f1518030b150f060d090c0510022a06 65
    0x10142d00d424000145001c120400e65814854403404c0c031404650004010002030916015918450280c0c04205201c14244110040b050803280318881c01c1003a0f01c64031032024401885001c040700403400071903490f040646040341c0a000e184c803805000d9510700001440c110f0051038180316004402000d040001648580300e00701440610210b20156824041240051001c90f1840090041d00402e1007000d0b100161045640d1003045106000303412074142c2c8441e181d0498035400c01d01318000301c05620f8140300501180e051060351b102214850400c20320800b41900003500d40301c0c59100780e000384419a43e954a40c440d00c01584524054134668020420504440c1040d0b14102c003c5440c1901411500d100f4a80710510550416551440700c0014000355980451b00004008010760301050302e0803517000007603500d00941c0c29501d0072546480d5100200901034039040058207004010202000700f1000080d41d43c1a40c1d2002d82500c0c0300d141c00c90484a82a9206c0c0441c10302c005d04170351500f011180c1038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 208390881 1250 208389631 208389647
    0x213050c03160e0a0b041401050f120703090c0b030a0e0c10180906060207090606090b030609090c040f02210402060a0f090909200f011e02120c0601030b0c19 69
    0xc0c108220321682d07299000d942e114140c000614940f1032450306c8600703080c4030305440315007903400ca0f05000040015400030f0398420203540d01720120b04090f071169903410300254058188884010500c0c981317044d006c510070309580c01a5006206242c002c20808001043e000d0351a0700140c00036038040340081c2c800c54010321030340c03405901074640041c240d03109035100b41900540b6502d4100f0000340e081043d09028251503440303880014426454a07031000c03071420448001038030001c0c00445c0039204900014490a004028660040b18080c0c0100721422008400c48001d4000c61071116104e2001c03002e1100f05022202210f0155030024400c0e803901c18684400c0e980800c541d14240c0038400d200720009580d210a00c40c40020038003030b00500f800d010f0030031030341c000c2360350f1107051644544540c40810714141d1380100d161010011000c56609004212070003a4904040d000e403840300f581000a000000e5003021505504a0b84980e500725080d880b80f04001441740141c5007940409000c01d02c81010140c401e046d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 208392131 1250 208390881 208390921
    0x60405150d1502040f15030207170c0f0a110109090e060708040c170309180f0703020f070501150f0b0307050702010509150d1d0d1704110a0e040213050c03 68
    0x14580b689000358110401d980150340700292901c00001c041000c034842d280e07004402c0e00289004c500e0b00b481955040e030001c2452030512001c0c0b41c00b0a80c030300e02d50000c12100c03011145400458010424034035101001c0200740942c24001036000c6000220540d450043c0c00461983c03038040d0646580f0404125006200104162031a1030b81445c0002c03071070380010652480381c402c10044c55480e040c01d014040c3c0590b00701d02105c242940c040c10881d103809520318040c2c0142ca54580561380c0c054014800a06000e01c18011703040b075103880050b6640c02c0b080b99000c4120f175001107010791140c1d60b5403000034050008440f41e801141342001010010341c4940c0c0203100215000b00016441d42d02440ca10000381c20083c5560070072a615000306400b100030540c507941d184800c3c1c0007411010100c400003030101c00030780218424080000085420000c104480b60b0001d50b0142a464502d941d907680d80010070f20954041e4040d0424446140b02c840c1c0c00e0180d40d00c1041102d04030780c6940c0b00c01c030034000241c011902c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 208393381 1250 208392131 208392143
    0x10e010204050d08131d0a11180d030302040b0a05030a060504180f081c0b0910050f0108041412071b0303051603090503030a020d03141003032a06020a0206060405150d 73
    0x41c5c00308883e803003202e850200910552008105190018450b0202d8207400c0c408290480d0500c2811402681001c0384040310034151500d40d2852410b2070264068029508102c06080380400d000030000d0303124000e544594000300080c040d4540d81c00a0004407608500e2240321186542441c1d03010850155603510103512410300709240030798648092040840f400002a212a12481020b45524141080c0d681113401c882c40e45181900d0000007030b840036480c402a84c1803080400029040c4560403042e0940100c071036050307031b440c90141e51200e601039020300400c031000703130070030f10071200080c248000102a2039040e207134249001e40c0300c809003241100401088040042040c004280345d1014000f070012401d058000b8245410f034250040c041c0d5104051360800341f46404100448088100100000ca90301402c02319a180b00406040e85241c541901801d4004810280d010400001c0c0d401814044025400d86810f03440314410482a900d0a0340d00070408001c0000104c840e10300303104800c014603c602 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 208394631 1250 208393381 208393417
    0x40e0105270705180306010b0a0c03052a070b03090a081606060b09040e01090f14071706150103051e06031509150601110a17090607050f010e010204050d08 68
    0xc40c04070514008407142400a040030410401c0340d5903010003d032030603008030040d182c0d5605042c0a003049004940e006410041600800420f00d07016904071015815144a13658012800c050031020b49080c0100c80c510610400f0300008010000400341c0e4000d00d0b10b107014020b064516121029684c020ba1b821510b1656030f800424000f030076500c10301004120702e81d81d00ea211041042044100c07681c2c1c11420a050341400407940014460200402c450f5600c00405162071800b03920040c43e2424a80098015961824414241c1003002410622900c811102000c0c0100504011001d940007aa01003010340501251103804001d4140e282c0da026401030b04988034510651501280c0300420745008180e1341000c103403413a000303405440c0b0070380c046028201102c0850194180c180d403081001409844144040301064813107411030200c0f22003220041c001c50729101c2c582062904e407040c20304010f8682d8070700395461712512810b009a03021607000504c8920410150740300e016041d480b00c211055524901 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 208395881 1250 208394631 208394689
    0x60b0f0306030d02152d09010605040b010504030302030306040f061502010203090c0a0303080613110f040302030c010c0209040b041a091606090f090b12030f0a030f0504020a17010b09071d06040e0105 87
    0x1070040c0384201f00b043d00100e1414504401e22003119188020707141009010030082c000319400100b100e40010007500c0004980d5008035a00c1f0042905401c020804101d0709100d4640310760540240d8091480e00b016207800503041810002c0d40c0c42c0764480100443c4620002418604e020030380044100d0007030b10b010880c0e660f2140296000d6114041490741c0c4900414180b095003010880d40700200428240320144645580005e51414401072000344011040380c0028100a00d00e14903e031f8265103a000d80000742070128003039803500760715240da00c90400110790028080b481850342c4c800310f45401010f031800314103200400d00a00340c000f01c0103420200680d003880082c60108010305c998800002145d41300c2500100060540c3c401e000d440401d14184030904c00580c0c1c4a404074411079184c0010160341c448094142409400140c4c005a031104035001086130107030b080540c0c22840c1288403140380f8010741c0d0404005060085024840784c1c3d00d1039100501c014140f20800c1420403001040500c0a0b40b05 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 208397131 1250 208395881 208395961
    0x20a0506180106080102090a0317041e05090702011e0c02070b030c030712020304080a03020a12060312020c09090618030d02070501020909090d1d04060b0f0306030d0215 74
    0x1081e2021622603030042024414080c080c8204005002c06000030b51404404e0b2001030704014542c00054245910030b0040c40407500040d08a8004004030503a8401960a040803030080303418511405009003908000141c26500c1840b980c4400588c15005007002005001c180d1300030004000060309612071841d0102e1310712003070300144d8440c040410000b03640c2d00d81030400401c1c0c1032100f804608001d00600074000081c1c12a8180c1c2c141c1c41d02c074a07006880c0d0240c40700481d9162030b00402030161768134104001c0706200c03c50160200c401f0031a000c54030100c661030709104001000b104c290919410000210303003c0000c1c00488013841100e04100c0c0c2c145554074001c40c0481c3d001c40000c81e0b10b69800540301c902c904020100f142e10982c040064900b10402c00030103060807210041d84030110441200c5080d4a80e40c59000c0000307000d01580b4980c4035503038511040e24030340c01610b01c20304c240f00f0304a44100c0d00d803001070203461244000041d0b50f400d4884a40549000f40000b540710b080015070401460224a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 208398381 1250 208397131 208397143
    0x607050604030f0c0c0b070c050405090f0d2d02280204140103122001060305210403020d0f020f1f090602030f040608100509040803011a041208070201020a05 69
    0x405480580300d642440c0c90040c281c48204031241e8113010200800b0008101e041040d0003c40e01417408807a544c2560b03113024552040d880d0441e03a801803604050001d42000004d505d101d603110701046400d902d58682d000d8896041618040124030000800303042660700c00320a0706280241e5004031804003016142071002040c030368017003114080d0840d104000358175050003001032500446007001c2d91941980c0714003001050165001050004010400620611030001c407803614200b04004c2004540324075000ba1106200702e01500c100d40001c8804a0190b5030400b11021250b0007403002040182c2c507076074185000100c5206a030300044101061045860301402816421362118291418120380f20707000c3e00803540c03a00302d41d04543c8180700d401001c54448003100c0075036030360381000d01499842034101c4401d802c558108030f400144901c144810042d41f0005103040ea50b83e0502c2a540c883c0c00305150401e40200d20038200c924840c40d010f03e0204039040001c2030001c0c0103106840b41c001c0d1a03110705140c89 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 208399631 1250 208398381 208398383
    0x902040213030b04050c04020f07060c021c030614100203040e041b030609021212030601030e0a15050f090d05040909080909040503042c07050903031207050a0906032d0b0607 76
    0xb203c01000c0008004c02801001d0701080202c80444c181800051841e0f5140250301c4020f104903581d58068001d01d008100e44544c0c52000c2481c10711460314000d004010340310921500307245110312001039880d032070120201d0080d01c41c43c0d401142014600142d9511908020340141c1c2c1c0c400300c202c112001641034290541c0a103000d924040b40300040b9106200b078000c103a00d220281d40d0070025180e03940402800c1100c0c1c10000074030340443c80450715490981003c4115800500301840710401c42200e00890300098860942d855002c55035980e400351207611440c1c0e50f60b0800000b00704000501c030300034841d8449003416006202003803c00d00d044011501c400000d0310169041c3e8800310f410090850001e001100148061500006170880701d840d000b001c1002a261506001c800b2408100c161005c00559411a5a9804105070703410040da0103440340e48480602c80c0010300f040710120340c042c002c0c080e6042c414041c82403081c10b401100c40b5501d904903002e00da00c1556407074440c1000203a5a51380038002c5c007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 208400881 1250 208399631 208399643
    0xa0305031e0c1b0f01030b0918030903031305040605010504120803070e19030506130803060618060301030b010e0a0e0c090703020f040801061e0e040609030203070b04080a032d090204021303 83
    0x203d00600b00240c82d540400100e0406090901005090302ca4800641d0801090501520a01e1310904c00e6800e50099010320750b01480041000d285001c10141450b089400948003040215101c100454041c801c5005803165081a0300150000881c40401581d000800c0d2501480000000c070008144c514580b40c0c0701002c828054042c400e100051192603089082203a2030340405440b0b80d1581c00741c0c0002015240304140c00302e8540b000c81c080b55072046a1807401800c0030303541d40e186c0c60110310815080c040d000800d0740d0b43c000200118554494510f500d00000300070405070742d4000811a1006000344007a040507024005102c603800d10b027020b080902140c034004102c49080c483c96070800d20b8440146000451100310030410b030810324001c1c4da0415002070780880c0d00091414185c0c1b86200d17280703009001c034001c2c504200a2021200c050b0030f404045940070b20200248420348030708001c030400701c10250440310313006192000d02d82d48403c00161000d4400741c14040722082c2d060800d810703a03105450ba = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 208402131 1250 208400881 208400923
    0x309080d020d0c1b0206030615070b0a0b15040302040b150a0210150b03270a030c030e012f0709050a15060c050c01030b0d140313050a0305031e0c 64
    0x7008003d00405410070442d1801e001c040640100b20500703010a600041d010740000800300c0d003192542481c58418030303e5124800d86d01c458518140d045810100c81c1b1406440c43c0080012042c074285200f0224002c2c4502d14605190550b001c01009201c610040d55200c41032480110b949081c0d1800740800d19003e030082c00710310b0041c11000080d07030030401504c990744001e41003d2140c81c4141e82034940105c1c0d010480c41d003080311240720310900000076109012600c1500c148400f0564880103c40f4032900c60b5681e001190030650055a80c0c11410880d0300c80582e100c00c0d0601e0000e81100c0506090b2141c0003244d1005582e100081c00711007056441803441d0303840d110145400c2583e140d002d0300809051610301442c601b240c807020303128011003040c0360400d0b817644840b41c1c00750750304130082e102160020f007029645a5040c00c1d00b6582d41c13040e00450780f007001c2d4210018051070091030ba07008a94121b00954581509140c0200707218602030b42000c54050240110f50f58120104145800b074801010301d943c0d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 208403381 1250 208402131 208402147
    0xe0c03130f080307110613060e0a050115050f01260606070f0c050117011406070c180c080a02090f10050c0d11060f07050d09060204090908030103060b180708070309080d02 75
    0x400c44414107061005c0354008403d110140051b24049a511138104000040040da1201e00f43e0410640e0a4040d2030380d802c01004041c203070109407510b4200c1d40b00f121070b49641c040e40d800644245281740a041681c2d06402c00740320304100390002c100d510140013490700b40307000c4040d507541002c055007e8060300c080300c0d44e260500c03040d60422148903210103020082c080545c0341606034001004202c1241c0e0041002040581c10410012941d1001e00316094480010390b50141c010750003402c4004100d00090048000300300000d026100302c43c014480900b4185282d01000300f8002e41920380101181080420004122519020b101c2109038401c9a603c1c00250940314000c02e2401c0b002504401010a901e000e1042c016008822078a02c00c0c0c0c810400700d15891241040002400346500c042240d60414480404110f5944019410380b4420803040104c0c00000f82808240006082d01d86640300603800451109030040b060b00307501802900d80804c005480d6690820300d6001040c2d82d120890300829400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 208404631 1250 208403381 208403387
    0x9020105042c0109090c140d02040c051201090209060901030b0a08011107050d0234080d090503010e06041e0c0305070b0a030c110c0d0503120108030714070e0c03130f080307 76
    0x60f004202d00c43c0184071028035602e40851980341c9100700e00800b07008000c0c2c400f031070710b481c018540c0c079a80003041045444400383c400f0381280d01a4200d0041c00b103100e0004141c060052082d128400e07000703050ba90a000702c80f8019402080c50b0f0b006203600a100030400526404240109688050703008001d40c1c07107940500c2d04500d0111401c01c5c04080d50040c1d209103004d0b5111428070400c0340140c2112a000030418046c190054140307400c03895032805894150001c080c0c002d40c04000b10b4505034000c101e0000c0e416210ba8440750305580050203040d8a1401010003103904a0004c502406801d4084c94680d907699400d18104555205806001c00825a40c182755010301c01c0311225102ca04240302d54500c2c082809450764901c59109110b5512603220105001e420010341d07069000004207525556103038155299644c000c40401c0390500c0100c0c19204031900c0106102007101d1031000c0100b01c03900d40c4c0c1003040440c0c10040608000580300e551600101c0c005100e0f00710114040d000c56035480c00c02070781c01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 208405881 1250 208404631 208404719
    0x20406060e19080604060b0d060501060f0f080f060111120307030f0b040b01090312030f09050304030203010606090b090d15150302040b010302160f051f020406300902010504 76
    0x120701244260b02082010140c08502682c4c40b6900c10342c00030b81207071f01030002256014030b40300160680d07207000004621640c0115070704d8000401030326540e40e42000c13180221a1031344122541902001d01d980403e60325400b442007091070741c07045403e84046076044598510542c02c100d4400300001d46484e08a64019481d100d1154003290503201449480d1049002a040c0d220910006110341044000704031500c0c0b00f1b80c0803522011030b034003007800f40b4456410302c40c1e41e942145c0030a030302c00e503e0843c3c0013810600a020450803990740a00107424042c6a104100d0300c03032070394201994000c0420450b110070f48000d2040039142c0d0051a01a00202e081d40140030894040000c8035052501c108038003003182e840c003009070f40d40a92003400c1c08404a5140340050801d1014807c040c0c0020329180260b0480209030094016507100ba6a0003030001c003081180805000c00480d50700b42c11048074040748078140b150b04080906401170510341d29041d034402c498000360349a4070851542500c100e0102140003d21411 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 208407131 1250 208405881 208405909
    0xc0912010605043603030e0a030905040e01150b0705031c1d01230402120106270501030b0708100f09060317041d07031404081209060103030f0e010507020406060e 71
    0x701280c110400c1000b0140401c0c440004506004072031304410548a6003145450850b84001c5d201d00300c41d60314001d0007009140c020144900d041c00c98282c00000c051159401a80d2803001d110074007807030410116110fa200140507a59404204881507a560b03c1c54030300742c0c0784c0c020094009a0801c03101d40c0d0706000c3c0100d01ca825841d9043c50186d8440c0c498801c2d118030b4134051010861034640ba10700c0003c8042c0b001c5000d0913840c0d400d0450000e0001042418a030102c1d5210072410b4004200d07005150031940e09010041180c1080004150316074490910a6400f008594102d20745a032684440c0300508801d074428202552540424420000c8c00076400d01c40c50004070300541020305040791124000e60900403e603100d01c0010008000b9031003a0010703800e000d108a80c1d00500d0605007400501c1d0b85c0040b0b03918491404503c0410741c0c0103c0081c0384c1c1d0480ea015600d041c480f02c0c525a044070710341840303c2d0840c1008410701c24003016996500c0307074400404107901c8410f06040850103000d01620310044c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 208408381 1250 208407131 208407161
    0x30f0b10060e040e0c09010e0414030901080f0720031b031c020a090902040f030c170d1b0c080a05010507020a0c03021318110a0909080d050c091201060504 68
    0x2042000581140c04406545021100880c03251244039080340f628050070701941c0e0000c4510700004c0d908c1e01410819000c2c501680c81c102955084102180da64407070192480e00140f18500012000511601060780050040c50202080039046a440f1040f81c070100c148641a08000345500d40c0007949000220300c0c040c050040d5041c41c041d4401008544c0d00a010111490307000a11010f460340b0a43d418809800031160031519192507090f1000700c9000d9000407602d40c96001c82c0801c0106512014034110540d040040c1032241d40d0039411101c19600d0100c1c404182c90f01e001e04000504a020f010024010301300003405066020700b4401e0039104050300c0e100a5401048000700030611056404081c0d80c0c040e56486c441301c500655281c000c000070001c40c1175007154000f4003410031118a4440c54058021220303000c646855a00740c03000c07160280802800480104001c002c124044e4208aa20010400300c01b4146a60140400c2c55980b803c0c10b4001640d54a4605110900d0284038221845c3c000d42 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 208409631 1250 208408381 208408411
    0x6020703081f080c060309030408030c010915181506080d03050613060602150709090504050d02070803040b0702041d0a08130f0608010b03181b01090506090d08180307030f0b 76
    0x340c2e580d03c0c0c800907130361180101000000500065804c004440080c040b00c021a0b0360390036960403007802014801c1084611803c8800a14209551401044210041c001116200901640c0d41e15880c024661030319900d01d450741400038010341c0501c0f598903105001c0d10085043e2404074204401074111038030801c3c2c094508002880b19541c0006d920a1014070110f076840743c0e4650103402e54441c00564050b6010604240410040040100f0350360581150354088403280da07222040c651b1240a180150101d11105200c01c074098907040e00100308040a4108402155611300815420103d0714042030b20504000181554074a8620141d203000303008140f464400035007403c4009041610612410044c000b0100c049014502d120f05000300219078501100c20620305d00c14030b0003585501980c03141c04101110000900381c1020000c41d070034410014202e90441500e5600c0070900d401c0b19118a112a1242e8002c0001c2d03242040000c000d5409680c003010a4841c0d89095900d10000902c42d642d0b1403480 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 208410881 1250 208409631 208409639
    0x90204050109090e071a12011409070801080606011d04060608090f0a0b1305240106020d0302030c040501050703021006090f0e0a0f0b060315040c0608070c030909110706020703081f 79
    0x11400e981940e1074562101c1080c6c41c0c4180c984402d008a041c11040507191000004009000c076000a84042c0d0550b010855030796401c2c800d9441e4a800d20bd040e0040d04031000041032507200d4103d141101c07a00040301c000d0415001c02090880e44c240d006003000c01c040c40103100703001c802003045058005c000c4002300f0341001031755502c1c3c071401c034080c1480a442c2000b40d070001c1004414080b2010301f0b210600d80803c3e03811800400d00c2050000e00c82c000141c09950494001c02d03209000320b0380704c1c1c0d440c540d0031850113240600440d56a031001c003090b0304601604014611244545c002c0c0801480003030008101150f41010345001c940d4116420a02c1e41c2c0604150740c0050407107110100181d4004441103002d50700c10340420f080ca00705d203100400e00c030001010001003200404140060b01c045aa07205055940e8540c1900d20b00c145072805008601c61300d808201800315030304012041c08100655606040c0d031940c59070140e03000309404030081060380003003180f03203141040c80110010340110700800262074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 208412131 1250 208410881 208410883
    0xc030d06051c020d0204060b0d05060103180201020a1202010b0306011e06050a170c0c010f0e010506010503060603010308030a02070606030302011e0203060a0e060d0203240603060408120a09020901090204050109090e 94
    0x110b40c000134010324500c032160065641e503900440c0100103107100c080c1c2d00c00140181000402044440c1c3e03001c01d02e420354920181040e21518442c8603810707001444001003039110040011748020042c0300310340d05c4505e03a00b6540c8003801442d0090400c5400404000c014901c05901170b11150006410040c00f448145d100b1a80102d0031505200660303152401a00c0b50001c083e068410070004805035820b00103020806078040e4480c0501d020088000c02040d1a1030004682c144020360b000c80c1d10a4051006001240d0508010354221a02c183e005141860540c2c1d00401c0d501140d109a01607503403640301c40c07610225a6030060f80c030081c402046103540343c004000f440100343c500518000d00c600f040000c1080c0c4442c4055001981c0003005c84a210340814059103510000c00701c80740400d20344d4804a139683c140000c1c400c2c000e962008034a801d04085580c00b06001c0e07401061802c02d6500c5064400240c1c445101c0d071400780c0850311001d03940d10f08200016110305450380c07017030202625146188482c814 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 208413381 1250 208412131 208412179
    0xa080408210c090307090b1008070c0b1009140601210609021209070b030702070311130c030b0109050303070503040e1f0603020318011515140c030d0605 67
    0x648100c034140c55041c841104004030a6100144455441c41002e11032001e500c400940101c55007102260012501c1d00e0880381034900c00c1e170800303811140140040030840e029080142d80100a4035000c05840100d4994815020f001d0304d040c282c1066034075060003111128000c40c1503844e411302d80c0c1440c034105800000d0110508240f0a15845100030a8401000c156008030f0020002035100355211005031441c0b000039070090740c0050303007071081400029264510f002a02d120b10081c0e005840038030320715161420742542054a4552001c1c0203c14070051510328403030084071440c255000203802c8403880c00941000425001203103e517005004110024000008a4040c0c0c1c4400c02c111003552640c20300281076119030340500c50a480c0d03400000c00c02aa060b40070b036120f070000c1b42d40309007240309070b031505800c883c0000642090940c6414082c49180c0502c0c54100d80350080e460040384002d0600441c02c000d0701709602642168100048803210011140184005080c04640065a1010485822544c49 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 208414631 1250 208413381 208413383
    0x9070e090f10080304090e0d081308090135010b07051e1603150f1a0f010e101e050a02060106030b0607020a06271d090106050a08100608030a0804 64
    0x1c007585001800c00e00c1c40010480c01480c044003200d88881d114041500039080c056400c012601c103d10000740072510900d011402803110300f0308010f40041940f2010002d5116a8445050000048000002d44050340101c4004900c81c80c842c00100307511a0901d142c224180d000048004052004074007217000820007201403105403142c070400b100c401200d20b003480c41e40524803d200d26003c3c4004148007040c0c80030321580242841c01c004440040e0704d504211501d415001007240142c8014103103600700701d0381407030700317072005040100384100c6107000070381246801c44c00c403400107d100066078609511036030300039071406190401d50704002034001d009507680e40502c600003c1588904104900e80c4410007100c9010b0307005031099482c242c031103402070143e81d200a11100c0303019030100d15072042001c05010509445800041000e0b920184d04810800340c8080c1c650f138070035565143c00088968458080304010003004020f00307010711040340070310220340c40c0f680305007456002005000ac65552240c07405500c9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 208415881 1250 208414631 208414651
    0x6090111011104230409170d060f080d110d302903010605010e0d080f0c0a031202070c06140c011a1002160603270308040209070e09 58
    0x1203010a005103000d40140014030b41c000600180c0803c4800c50314800408400e01403904042d200c001d0b00600080301d01b0490060300002d0803080c0d81608020380300c000c10150b840c160b80882d9044e201c629179104500c8940c400682c1c2e0b40600481d00500d83c000680441a440031030207002400d03905c041c040e14082c030104007110300e159071611200c003a840050900c50764072a541810803003d01980d50038028003085400794080c1c140d90075000030071481c050094500b5540d0603946d2130742e45611602841050400c4c0d4400700c1d0b0015045c4414003c820855000e02900c0c14600e000b0001c2d0704260802030070040c0458400e07403c1e18010420302d00400c5e65141440c1c119100c91504134100785403110210500d026417021b0118a5003000d907240b4400031441c81003454120112501200d0006080341a65154403021a42e401915484410000c4500a03848070788400b070b42c900000303d808081031602c11030320300821049001c103c2c0341c010701095041040714281c3c042900c1c01c1000d020314203000007132590b1500601310011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 208417131 1250 208415881 208415897
    0x1509010f0b0109140d0c1a030103030306050d020307170111071208060118140d051006030209070c0302070b0906190503100b0903030313020f0a080a1709010804060213031e02130506060901 82
    0x812080c43d407240010501207180360b0007d0903c80340070425910a10081e00003c0c20808003098a24120b00c60144455000b03008051040c0760103030080c0c0e02e40c24054000140e540ea100a4a060580c250041c84c4861140301e440e11100038503013000c0c1490101400503410071201e411030f0040c2180488510301074881c0c449414000e45602000155001600c480c020114080d03428079200c0e01c60b06400c04e50540303100300d600344d1040e51103240844202c007205401400581c420340040086002000c0180710110b0068411440d181c01949205140116108060006400001040b800c4607075984000f000d400302c1c0500e81d140031103190000365240000b0700b01c40c126001c2c1104107411552450001e900351000a004048000d41d100d43c079907194080d0190640d400070f1402d0f8120700b1304418408950301030b50161241c640b90b4a458407094000e4100c000032408560740241c0100104051502040c00000343d107555140e1080684180001e24130310450421002c0e04080c1440010390360709040e030350507c13003e20b40440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 208418381 1250 208417131 208417133
    0x8120d0e01110403120905040e030403020d0212120c010c0311040510030b09090d0e0d03020a080703050708030a020a0318020906150d060b0c0f1203040308091509010f0b0109140d 78
    0x40103203041d010b800b02d4078900281c008200b040c144039084078507549403034200c0d0442c0c1d12014017081c0c2e0005a000c0466030410801072005207031800038190158005003040341d905812103030117443c0c401c100351102d2009601007041181500b09024054040701285400d0100c01011a507ea0f00b13802030b8000c103031040305140c0c080002c05100764019000b0040080c505021402e00110142d104c14101101c180090062520f4078681d09110780781280c0a80c0c150300a189810683c3c5408400d904902c4d0210304205042012101082884010b1405074641d9000180c0e105844940a41191212401000c002802d42c1054000d680e03080381c0a503200b1350580d442c0c0720b01c007610040c1c60800c0c812003503008061450700c0004201c003030081015069440b00002282e05141280796501e42e98003010050300b81100040000800080c4a50f000c40c1d048051b8408441c519101c008a4000c0d400b411241c1d612140c1d542c2000345501c070f074140200c5c400c10390282406003e413401e1209018140b143c0810700b5016801d010f00c800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 208419631 1250 208418381 208418383
    0x803041a1807090f02090409200402070809010c15060303080f09010e060c090307080708070603060b040b030601030902040207061b090b0c061305070b0711030c0402030c1b0c10021608120d0e 83
    0x41c6c180c40000340700b044520792501e00743e00701c406402c08600d0001c0c400b000601d02c504180c82200c050680003002e890501040701c0045071810781c181c0c0e00b00c0e412060070f03ea04071039824500400c00603500c80d031a10b03242c034501000311048004c001420f00e049a81010040022180d01182454215070007201865075101040702082c50850716a100b2280c0303100b1540c001a480c43d010030758405440142ea000d001684e03803505d298501b4083c900030860040003c0022444640c00307544280307481d41c8050005400d002243d1966170403038104c4204811050070380700481c0c5919900c840c44601a00d03045006a052120200c3c0066492400505188000300c40c0401c0d0414004208500c5000f0940d1300200d46e5980024548240840c140d04c142500910580c010b43c0000c0c6400d000390780c480d2a8802c11982050505103005003042c040016041c0d140c0101c402c0081162100101250001c003190002c02403020708140d070811117503555204503001d81101c66400c3c5c02550b844c085070f103a00707034043c800f048541c240d400417 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 208420881 1250 208419631 208419637
    0x6091009210e100306050f01050403020112050a09020a03031d01020d0c0b06120d0513050307120201030b0a090c03231b07110301050709080609010c2a0803041a1807090f02 75
    0x1c1a03028a4901003070f406254560082401d0310f0781541c505801905080042da0f40d0700aa000003404034444200480190b095a844140e002403900b0740800c1e82c0005401054030001e25800070ba0000300c0304c64940420804a619021880c40284000c0842400000c4001d1100b40404001020380300030001084041c0d03a0100c0d006e900203158000c1e513110440840b005400d991100d007201004e8510079400203000d1502081700c100f217542c0140b80c1c400a218a034011402010068002544490115000314900c041c5102d0341d00010113940340007a0003661494081941e86140001b98040712085081002c00c008032350013480100c85281c1c1007130315080d041c98414055102558220340661804003000a034030340c004588012540702d01e080d143d00380c56400c50309003691088120607011491009120414009c040ca0031103100c1000c080f07121420509648001d469401070f1010781c2d858400300103403265154486c8055810031000d0750200306507854100c40300c0e103d1006101e0110182d555660003c00380c1070755012 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 208422131 1250 208420881 208420907
    0xc0904050c0f010e040501060225081507030213151d06070605060a03170d110307020c100302090a09020301080106051c11150c070303020c24090607140609100921 71
    0x6110fa50703103421000754ad07403002070240310b40540305081d04207003a920155044103498043c00601118241400800d45804001e4204400c1603404c124164002001201c00c1c80034180301d0084d410a1040d81500401345680008590102c0604041545540e91540301311a640c4d58020408111075850b0400079008070540d5101901910000c1c03501c0e0440c5041c0402400e00c1541e1100411440e00e040b80d1000d918002212404050780c01000761038098a80301d201d82e12068207a190261404d52610081800c1164603030099880340d03004001880252428002d44000c1d020680c1d1031400d44000b2541d03603040709000301000d0401c1d0694401c00a154440382c1003200c2012800c04d0321039a8000c401e031580e80e1008540320a8006004170f000f074813107902e000c0385084241040291068034160710149010709950250046961040c01081104001244441480428075011024201f545001080700d0b04000381c004144621500c0c020042d000649612a08060040704501100d22340f140c0b5001941d00000d0a10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 208423381 1250 208422131 208422139
    0x702190f06140a0203190603030c0b061f050c0c01080601021e0c0d03020303040201030509010e10020c011503080a090b070804170a1506080c031c0f030603020607030c050c0904050c0f010e 82
    0x100044040f898000b907008140c582d2003205e0100e006401e5004582e0741d804020000b03411881104003003140941110b8210000504003000070700e08401d016401c50441007140082034003c206284204814072540c0a040828200440d0600d81000003d40744d00d9000728220300311304142c40d00800c5810410010980034005081e05004803194140a546c94104550490010b070a00d0001010000b060040d0401041c403080244541800c015583c07004e5000502406155036070f0703903913070301c0e4800c0701c4041d6000441c00b4403541c40c0d85214480c2e00030900b8003d600100b298070301c20040800040d04003c215000c4594582c2400000c140307003103040f400c00301440c001074410a602d040c152180410390b40140300302d82c0300d00b003100c2c0f610702d0010a16407030324903600d41c44041c0312a0030aa141c0050282075a01c6011010b85400501d460b140d90005002c2e401c80603050b000203104000c1c041c02c01c001041f08170b40100044600310342c645499965642d0300d1401c91070103405020110800708a603409007141a0300c00d40010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 208424631 1250 208423381 208423421
    0x611010b0415090518031b03130b0304021503100501051809190b040e0c060901170408250c1e03080409020306030606010c0308010519080f0d080702190f06 68
    0x8100141490550044541c007078a407001007917a070b19900c402c010b070741ca4409015504004201081207046007951500603141e0108122041039a103107103a02e000508940d120154490905005000080000145640c8840340403c10702810a00c501c0074003080721824a011580d401a50305615111150716000941220b6406d080c41040740b002c0c01d00711140300c0300b41c80401001e08600c0401080d180401c4108950390400c40c548142c2d03041400043c021400c060501030341d0b0162210410900c1e41080750155180d0b507020907100a40241c488a0400c664107604a107400341140742c07500f004004161203010b01d0040a4000c540520300400d80010045400c02140c64940c1d95904101002c4c2d881260340d14400d001d81000500c2c05d60203080c07068500e64160b40c91150308d81c2001e05215202521410420403901404000101c0385420040558550b03120005410300340c1030b4000280c12508060302d008150f4000c08090321000204280b101076241d0061440680745c0344d541010300042c208410440f0020070030b1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 208425881 1250 208424631 208424651
    0xc0906150a020703030f020309060f03060f03120c010b100503070f1b031107150c1b05060d020d060501050405030d03020904060909050604050d05120a0504020111030c07050a0b12010611010b04 84
    0x1c583c6000300c034001d442d490040650036000326101c2c4031700038901ea48503809010000343e0101c0c40015561110000e010780301414412000246048034240c4c40c86019000000c403000d02110a005000c0c0d031b940d068030800e0b03030b01c40d20420281107130100424500c01c2200a80e818a0781620644011034101e444610100c444091810010310300300d00d00e01c0080080c803030504001500240b02c81c100f540480c0301e46d6030403560f01203a0307105881d510144519aa1035400c00c00d022450340c0e01d07a0300600345402985801661200d81410714002e6a4469000506002092204001d00d44000c9000080c1c000039280c010b07500c603820700005006081c1600b00801c100d01e0f1001d0b60341084400030303d00340201e004804a99008265000c110b805110385002481c0072410034002c1040304030035411458020f481414240040070301c0341c074030b6072458001c031070820100d0b4403208041065042c40b25802c0040c3c80f0802010f403800740328080804e0800b07010321800c0b0030820b5a07007000100b40400c2d031041203602c2d4000e00070b200e12200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 208427131 1250 208425881 208425883
    0x40f02031005010f17160302121501060305060f04090b0c0a2a0c0806100b07050a0b0f06010e0324070c060501031b122006040e09010f0b06040303020c0906150a02 71
    0x201d004020100b00b007817484101c800b0000501101d07400801c010104014110360078030910310b1041d000c40383d00c0d00c108540d601c07940c4545580940030301050755001a007494035508000081c2c02c0c01c2480f070300a52502618001080340310f02c02d1a07200d010481c03000d5940658060032134603860011918842d00d600511140c2103400d00c1c1d04054410340c0540c0c00d0b050302d20b1700c43e0710311911004255090040d02d6002e280820603444c00704003815149004800b42c074a05195a220a0103a010441c3c25000703910700c0501b0802d00e9a040802540b054100358000c20b921035003041c54000d42c3d040e03040c260349101c5201c800a8005c500ca0800c0328000d80d8020818069540c0d6071030b2803101040c0c05660004c000d0440200801c2c0c0312208007074104490340156050b07048004884480d0700d200d818210003504010304100105e100e102034100f903401044510000141c101400350544122100700c218a44282d404120400c08039034005816608001c0840d140840c549680001030007441c4503a580100c0c4510115081242c150 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 208428381 1250 208427131 208427159
    0x7090b0f0f0415030509060708070f0e120a051009030c021504080d0507030201050c0901080415180807050c22020d090609060903020c091e10030501050c031b070308040f0203100501 79
    0x143c50380302480b064440c02101c0791039480848d03480740003d4603400000c0000d8440c4290349105885800e1588425a265001c80e44280103052000181d07440103079490300b040b404000d0070300c038040500b5082000c0100342e94010552465500044c0c81040003000140b10f8007540f00845000b003158800b02d60002001c1100540341d5004100c050b4017552a0400081c1d10b58003920441e04140c2c016035803a138841e036071580c80b0b200020310b011203d08126503500d04d98030b170340b0340e0100c80c00c1c07107d03000d0290719451300101d1521515100c013048010b40940c0290300c1d61440340b0124444403901e040d4102015894030b20f00d0080000401114001603c0e03241400d804000744290381c1e001c00d060500960995002400c14000d0103500c40f0150f58208100f00440b11071070080d0101d1400076004041009940f00f80c990b240c0300c00742524416205040d14850001c144006400744603440c131345c0c3c1a00301101c0c40c1000c440c0e4901804070031005102070024450314036075004559046c0100d041e0306d40049030401c16540c5401034100290 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 208429631 1250 208428381 208428419
    0x4020d021210080d02030a0c0b13021009080f010b0d020909010b150702091602030301090b06040803030906071e08010902030c071203020318010204051e13060b0a03110307090b0f0f04 80
    0x1000d65134980034814404000c8580c03440305502c610541440701e47d04d6582c0501c0041030950305004e003c0c0f0060059480300682c075130041c11540c0c0d2500d0305040051490410003060101200f076854070f00b4104c2d1a44880000c40081501114943d44598402110501500d141c1040c07039801036401c00031403255000380000c0c101c9039000303279000c003001e0796814005149030000c100b4450144e401400104401c5040741c00079052660081e1196081c03e60720360400703182d604142c9203c503658000d42c0402485035400341000244401c0110547c248102e603900103044440c0c107008098020740c000002a2010038241e044501c0641d0105020749031680c0007000500940054848540c810200e806000500c0014001d841c1501c070024030318508801105d040300f00d00c00c03600c0584c0781c03c15802a4403084000903031040f0b03001007010110450b03a417000a6802000ca410b280d90170380c4114018010300c03405a030f012401c4010348192041e0541d5500e14071f55280c945010b84050f10300004400200455480c3c0b4041540f4082 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 208430881 1250 208429631 208429633
    0xf0905060103020703090b0c120d0b0102011404080703080a110a12050601030b060906070f080307080402030c010f1b0624030b1006020d0e1801030f031404060c0204020d02121008 78
    0x684400d001103041c0d100306240507000640c0002c041c40950421801480203034400c0c01181c080921801c2c41c01004c5d009200318003c16030f1303140300e001010358080c06011a100c000364200d1072145882e0f65501414007481c02d0141c1005924000521041e0840c2e00c00c20300c0310100700d00c4a4644500480c010411031420010b0642a401c00000c03581a5010b8050180c016000624031814103000700e0030b000d01038001c1c50781600c40d02e03000100000450610320046005036516540d500b02d501d8640185454144503e841c94100b1100c0700c850804070f80c2c40a84202d500080490003010b42c001e608010307020301500c03149400015286011803204c402d1140b20501100c1c41512014216502c2c400c91600c403c000d032040c0d9025800801d0644c0100e0320030003484404a00c014101441514911010012034000b43c0049424840c4a01e92405140d0440e40d4038034640b0040c5100f610b09414000c005008909000d80240aa600420448041e41c6150107861000a070750b42d4100c03d5292880780181d10701c9541c4030300b03001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 208432131 1250 208430881 208430891
    0xa050c06031b07020d060e030403140a121805130c02061803091507120503040201181a1e03070504060912050601380a0207060801080d11030d060f09 65
    0x45030608200740c07441080442807810a04a840c0781d054040da010b600304903031010b12140c0460004015100e003286800402006640352801e44c42c0a03440c284100c40c2445250744003030031100000d80b0110f11500a1a0710f460301481080700524514580c0d11503401c0103600c0300b030f003441000510049a0140030203106550888500c1d845503043c3c490824114001c0b60159081000070a00c0c07401e11042c103203011012000302900c0e007030450b01e5490600c0042c00c0e6070b20000d10000f06200540da4411511044285504007800c0014030b8400da42048004203407003a0a1900d000ca10a600c0c4070403e8542c00e4207218855a0a56a00d031080c4001e040340e0080c0104000f02d801c01740041405040c80d118445da49501000030410b41c2d00346071058002c4000c4851100c040e000101c8409484040e4840007092540b403c1c020301e840c0d041c0e8981c06405c045c03040d00800b003000405070040000c07070b4000900000e407038040d0801c1d04500c0e4005503d18114841c02c0001c0c022a82404d400041c0c54003205501c400312851400c003000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 208433381 1250 208432131 208432153
    0x1713050105040b040314120d050103030909140403080705120f01050901120c0509040f02030d1701080f0a080d14011202150306030d110c0301091103060f0c0d0f0b120a05 74
    0x1c1d0354002c602445012103c148810301c006100518038075026110242200d040c046800c000141c41d6100000b01c1c807200e520b80d00104205904528400042c0c030307013000240140343c4c40743e1502c8001d441c0100094100075001010030740c070902440403110181030441d000096490018405c400d02e2400788142d50040341d006000094a503080b4644407104d0781d001c9000b03a4218544400c202d154034014000b690100540d003c101c0040e80d04015000b8081c210b03407558890744800400032008002c0c160b000c040c081d002103140401000c40803170389841c1c465010345040e86842c0010108002000780f40400b6200824036400032405170002c282e8544070b50f1085481060700c031152200901d41d8002921115055071100c0c24000303040e4010020495106001c00c00c480d070820f83d40d000a401c1d04d001550a8800e51109100200c2c1400e0501c0800c1d4003803009410003449040008036145d25209800314400e41503a00c00e02050807000343d40048480e640010110900700303c240541540740c0d0f6039120203c81622030086100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 208434631 1250 208433381 208433387
    0x17010203040209070c020d0f05030f12090705010e1305040c0e040b0a051f050f0112020301231c0b0c04030803240f131515021507020c092217130501 65
    0x9100d17550161046251501c140e0341c0e000c0d41000b0010841d1140002e108200d4210030345d1010304400e10001a1040d0a41040c00365135042001d244c000b0790400a8040d1500401d40b20a24031000c24100341d400004c20395110300f000204503000781c1060010815030360900c0180510310442034080c104103407080041307895201403442600641740d2268040d11040741e003040b0f01d14065050084c0e280041c1001c0058191000e010012a80241c004040d0003c0c00400e01c00c405d2111900d4408828042c0d9030480318141404108201013440200103001c0c0d041c460001d101010403034142c1d402164030803d203a0b00ca04241107007803602095410400e0340c0080020250400c1c0c40c02c02040c84680c1c40143c1000b2030460302050380005051208001c0c801d50214880001e1100c80c2c542010124031400d90103000c0303c40034881728100426016008104650000c0712160042c3e4503110b895400011843c404000f2822241c2e04000c02c3d070401e4000740c95440158410341210122030000c101049100c803c090b079440d1100015 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 208435881 1250 208434631 208434647
    0x80409020a0207211103100e39040209030a050f0606011106130201030506010507050f0c031c0f031a031b0f0a080c04090501091506090b0604060f1202041701020304020907 75
    0x20362913503441480301e40b012850f80c2d42448541a4081e09943c2d8143c3c0c4400007500b9180b13950184005540641d65043e513070f031840e11503174800340a4900a00f400000c003c4540329408030341140b1600c199030000d1100301d070352340070840d1019040c0d0107400c0c0d800c0741640012030f81d21050102d41150100350040c900b500610b0011460512503450b00d4541100359100750011801008000c1034141444803c2105002050003004401c01030742c00100240070750382026040c1400c212074032031140380d1032a101c1c0051881d60380209851407448200e00d400030355280c030303099441e20f5058880102c1d505401020307111458500380545075110213500b540c4980c600d100060500541a0071481860301d142c2180b40b150110f4503154101c40f410754002e000100e01c0d01600e8481040816840c001da0014580d1038800304200441d0b0300404040080488616040514114018204007010f2210304108584103200100c0c2c440c0590644001e4852000b90b421080540aa0030703000390f00a03242a4401e080b40300c0003034035151090100d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 208437131 1250 208435881 208435919
    0x4050f0709020f030f1009020c0715030b031f021e2109190c0e16020d170a05270a020102071e03140c060a03090201030b0906061e07080409020a0207 65
    0x502444c0d5501d08448040c070490161840800003418240010046401d0024200800e0440003409540e1310b40350403024142003241e1070109041c100310101820b40d80103d01e00400c40d29525104610703540e1804d2450091058041500b400e0368402102083c8011003009000780c00c040c0c1084034070503030180c80201a5080119500081984041e105010008020091b1283d440c40303040000206503c60110310310012080314815142040c03003c01400044d4104240741030380015060031103417400300c40c1e0248207105c4000c2550a086031500040341d1856454041410511800e03986c802050318283c0c882511488250010b0b80180710343c0d8030115103103450350b40c00020ba003100a002161240746580e9404070891781000020a0b00484040341d080b80c451400034000ca440d640d0300064014290320002d0100c810000115010341d10b010308002042e2203182c00c503041c5031f05401e58501d0b0902107600011040c403c04c2002442c0d10b801080005413070440343c01800c100d444940981c2d95003510b4810110042000d070007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 208438381 1250 208437131 208437157
    0xf0509180d030b15040603141f031202031b0c04060603050606040302041d010606030b04050f09061f03050f061e09120a140316030609020a0525050604050f070902 71
    0x340c600010350003544090f03c4608080e1048254050260707002c0703840d0304151701c5000429151110340c02218034070480707203034841c10505141d0411000b40c1d0b02c45144468900009144d035020700d94040600740200180d61960050f03040c100c40c003540701503031076031200b04024206010300d040900124140f030007800b40603c103140241c002c50516186400300005403001c4608460b411000f07217070a00030040e00380581c0e00580030329240892040404e1051100b11072005001c026021852014411400e0021070301940000115a5402100987d10180c89021540b540000d0181c40340092030044104082000c40c810f0b0700c0c0e4104594500008005a50809000c541d0150990440b2030021200008013003c3d100b5280c00345000400b451094520b04125803094450040b0181584441940203516001d04005031109520a604010f155000a883c5005400425400c9445a0f018201580f04800d0980071a41c01000301e03000c60425060042c0c0754201714042c11500d0040c4040070806c0e0455000704d0300200000303c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 208439631 1250 208438381 208438393
    0x60a020c0613030908071424120907090603140601120213020715090302010213050f0f0915030a0f0c05151b0c1002030901020c0a080601030f0f08040f050918 69
    0x2a01d540202c0301601c4085050181050000c0b6080b00204114000b40100202d842c1440c00c44204002c0c11000c00c0c0800030501044089001d90f5a600c58207032414014140c02501a40d1294910181000116000601e109103030060000500060a40c03c6d4038207003010042d524a80d881e03181c070108050400b00d0294010b8290030f6403564441466004200490280c10b000030880c03210b0800300705441d0800d00640051b9000300d101c01c100c00140031803500624048406d8106201e120300880d00c4036014081d0b0600c1a08580000340d61010f40002040c0c00030b10040580e080383ea43c510f4140600c500300d45007555401d855120100741420b100012030006100c5034002c1d07042010700c00740c0894004640504046034004c8500c480c0c1c3e0f540302c03100c00f98000000ba0300555169110b0000081c500b2001c0c2c000b1511800c030700b100810030071201044141c15641c000002c0481400c035820000d01c0311490380f400030004240010000780300d140c6001800d0039110103d071944243c0d100e0300031f6a00300c0d0000b000424041e40184e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 208440881 1250 208439631 208439641
    0x504060608130606051009060809010e0d03090204020c0111070c06020102030123010e0a06110c091510051209010c03050105030c03070e07141b12040b070305030a0b1f02060a020c06 79
    0x41c202d001800d02c203503000b00e601078640740801d03070407040070b18104042013045009000c400d4000700440c0d071064001c4003c101501d882d044160791511681d00001c1419a90303841a01503407550307011580b010380030780002e000300c4421817101c40095001c45403d8510314882c090102d11684180203c070f040340d0480d4850a0b0003070b202d400399450700c0c1074100303c0d034140201e02c00c040610b911460405c0d002001c075503c44d800c41141886a950030150b070704078114410081103003004030458540e4a0140e00050940b101049a040800103444611481d06581c4104101208120001c0415000824032503082c0d64140300e581d03a28014190703592101d00b591039041d006a5814044416003c20b2940d2280c41031a046545400c142510f50035a48000c400d95201d1421a45000e01030008022444124018104092800d0301c2d10820740d002e40a0188001e00b08036002000c9a100789107604102100310000f00340180f82501c8400d00c4102001c81126000580100380014080d04800d1099460042c00304003d440240c2e99 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 208442131 1250 208440881 208440901
    0x4030204151d360706020c0a0b0c0304080a0f110114070f05190803011d010302030703030f0e04021801030f110406080a1103042a030c260115030c0504060608 69
    0x802070012100e200500c1861403016a421004110103070002c07544000442d018030f0540c200401500110155401451031040c19142c0401800c2201c4115480c80d03240c8013244599800d52203030b40c0c02909248a8446110240f0130111551000070388550280c50040c41c0920054600001550182464000a204180c040385183d44140d1100e40324500ba508861100400b103ca043d21001d010b0302c00c2d010100c0140040c60814040c945540c0740072004080562440c0e002a598682c1400028100407442c3c0c0d501160500a43e1200c2d084840144150f40314405000149010403191f8022400642081080710318055640300784074842c25071855072840d15040820554217810007030440c454a558542507641c040350001d01450181f4800c907440701c029142c0340340e40038a00e02c00011041c0086141e80080001410a10300c41007110310449144080c003e01d031542d80c4a1044c0501d001c0c1203075003402c0c00f810300d03903550702d1940040da845549405900354841c0140001c1b01c50901600012510540c0402d6003040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 208443381 1250 208442131 208442189
    0x109031101020a08162907230301120b06040504050d2106030b010317030603070e09030c0610050102011a0a0506130306060806040210030c021203060a090608030403020415 75
    0x403040c011100c0918144e6a04081c583c801501e00030044401600c3c0810040e102c1410018402d856600d1341004d56005200030b84900c020300840c05009503c102c290070403100c070034491100209450040d0b00ca60356624810740e080310b00f8508894005284000034a14a02849003500842d04140242621458000c007035941c1048420350070081002c03450403412840c0e2034062103000e144078844421495145151110074014801169946800b0620400030b003510000341d4403045460100c0a0071880d0ac5002d0f6203030443c0709a1003210000c2c060700003008012391412121004807070003039000308107040562807841c03184e6442c00d10042d0b0050210000308554a0304c00003a00e003c00f03640040c6098140e80303650321011610a54030080807034001104010a5161482842c010f010342420244001200124000d4446092400c1c01c01001c4012011a5164a1f0300c20340f4400b400d2000402c010701620f4152080d501e40081c40b0883c4964141440115220351880c030401c101c40e450107084180a0068081c503c001d0f03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 208444631 1250 208443381 208443413
    0x30c17010302060f09060315030c0d0b0c030c04050301140403020c100c0627060603021c05030702010f1e080108070f060807031802040504111201270204090203071706090606010903 79
    0x3130070030302c0354404640e290750045005000103001c4030300040c419001d250400c0380d110041c42c85141c0c10010b040124462102566100388200426680ca50b114a804104c50044d41c00141d0150f1a0001001504e00500a818001c901031b8080714140c26030751081226404440e44501c001604c110442c500040c0769130450240110702001c9001000b8200090303034400c600f8044150b5107036450b91401c10650900b8801500551034001030302c501e004258560b0341d41c1c0e200c0c50034001c0c1001030708801c1c0d15a180c45074a8419044542e0350203042c1e0007200340c1004200c584280204c01e018000c81400184810f503001c825800c483c2e803601c6141d2039960b805426001001c41c158003040c512890313003c0d400160780f50703c22113100ba88a03007107410b080746010040c0303c1c5010600403410b4046c0c0c5402d40400e050800005442d1581001c60407501e40135095101050181c8405807009425100b44800400c2c107012008102c0b6a00340c03241e04840b060350380c5a03000da603107a90554000303000c07035510101407004c00d5042c401c0031044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 208445881 1250 208444631 208444657
    0x100623180f010303030506100f1805090c040f0b0a0c03110f0312011827020f100201020304021905090f040201180f05011d030c22020f0a030c1701030206 67
    0x140c59203904211035500c0844103008145800c0c0010b00400d034240c400e458002c542a1031030117074000c40e2070020744403d00300e0034220140142011808003120480081d44003500000d48210054186603080c0c140c160840c0c0103425210303082c84008101d0b2803000301540c4640c801a035800c5070840346a00c0c140d0b541049140105c1d268002e0f418501c031400000c000402a048100340703040c2140d0301d44410901411000300c1102c503200d081140f80001106c61408100c00112076461003d2481c0d043e20000f901c1d0411032080390303000400e80142010031501035010358400d0703001b5607848091002c100014001c54801e409981e5000344440041a40c21007a078250541c05881170400c2c0a500080740c4055800740802c2e8007906102854020903c0703607590001245000d0400c07171080359203129102c0c0010351900100908a8040c08503a0454503502d550510a55030450300307038504540d626802c902d40c0121750b00070502c00e0007081c00c1240090b0351921403401880750900040a0140c541d00315400c2041c10752101100c0b00c66 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 208447131 1250 208445881 208445899
    0xd050304120503070309060509090f060d0c0e07091a04031203020c061303090801021e0c012306010e09090606010c060f0e2103240102030d02040611100623 68
    0x90701d00300300300c80401940a08000d6485401d0f07481d009000890581044c020040140894a071035140d0b03a900f075800500c0b800c150191a81c480d40429070000d0408806408a0a903200018504940501560103034009643d040ca43c1a1101100d5804010846803040209010030041010820b0201e00080e001028070700549000b1803880810700e0107100b43d640c01285841d02420400305500000000010704141e0001d600b085a03440402c14107034000f04404070f50402c00160804004020740c851a500c1c81d904612510030300485200d5000308030116602800f0070007409418000f0700e4500c001d81d03c142a032000804041d0348503030045403500441030048403e15110246510300c05c44500036480b00c408c1c4100100707061035108040c8910031110b00701000703070f2840030002d0001d8a001c400150142408034074500d40790000f5507004071300c0c500c5078030780c0007400320b10200e408248154001404842c0d00441011102d06c00302d0801560304440d041d20a201405119010948901c40a10008031300213100400e5110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 208448381 1250 208447131 208447139
    0x7060e0d020d06021c05091902060c01021201080c010201090c0b0a11030408030903150601020c120f030d020405010e0f01022a030111030412020a0201120905011e1e0203150d050304 79
    0x104445060200f122025000703c1d292001c41c0b07a2650380c2566144004081c085420000d03030306911000300c0100742c0c0701d00300c1850140c4103648030082114001e07480f801c001c5594000c0311001850400f028000ca2105000b02020001c10390320502805100076001000001440e00d003054a40c100d6101c1c0c1002028844c6250f42c01381c0c0600d05001510007048540007455945500d0f0040604000014141c48202c0302282e0070b00046990000b8000b0314180c0a07100a40c044451480c11440e10100079a44001c41c0300c005080906000c158010f00b08840c1d080c4c84800040c00c0c5031081202040c1000740140c01a4089000c000c1c401c506480200005c0d003540161501254604020a080d11540703800561180c500100b80300404c00704120000018103181301070103e0b0b09165000070400d10340030030066807490b169442141840401c1d40720390712001102003036101c1e0021000070781001d80ba000502100ca1240040c0303041c1000f80c180210780c032810780d103000104004401000c01c500180c44400a54a501c0b040c00082 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 208449631 1250 208448381 208448389
    0x807030506040f060b0a140c060403030b011b050714120d031a09040605061f02030a050a030609150e10080303040f0c0315050f0705070b04141903030e060903070507060e0d02 76
    0x1340c013504001054595030700400340040c2c6110a0425407410440d000c00c2002140d0001040c01ca401c50751515011600f80b05c0700004890480c40003403088000200c2c0307804001081000690442155201320b001c00c1c0d200c4112042006003200383e6110411038000e0500c014000c0d10030f078041001c0040880e80b98403071003070007004182200c41c121401c803003031035a4a0a104062400034104c510340410100d07494002501801d00079102d02541d2055820302002152420909001e508518068281088100848218040560709a03101885000c0c099034000d8085646040400c44280594424200031480d540315030303a62520180086000740c0301110124008000910010b10207044034880d0340020a1038100300d8400422030700050400010b1110403c4503d0010b80100e40c01d0364482c0d0000c0504a4181d0020401d81c141103d01007440030035150300d02241c0415801d5270040c04640703030350003c4070070960300c3e00391065891040080244c241c5e07100480801000744039006202c0108070140070214501d01c241d02003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 208450881 1250 208449631 208449641
    0xc04140f040201140a080604060803070512070f021002010f0b010503010f06120207050d081005010c03080408030a0f0c0c060506040e0705060c010204050918010c020d12020a03020f070308180a030807030506040f 92
    0x1020005841b10f05000291038640581c0300a40441d0000e185031030800c0c0e81c1c0d2b50b62000f45c1713000407003c40750100381d50b8144110348a1201c02d0030b8002d031606500d1111000b00900908034034046800081c42d00b0000100da51050058a041c4c54401410404983c2003420540d41e03140b800001c11403641c1c01300640e0002400c1480913652420700c0780ca849400b414000000a480c50b81900440e040140c0f403009900803c0c2c1c041211500903800c2920722703036a6103c1d80d4402c405030001c6003e0303160040c06c3c0040580755551104040103d1401404200702c3c544a01c0104000e507040641d01c4109a03001c6a818015898590001d040c82041803000600c0c040c1e41c3c0002c60300804040321103250640508024522404080c050f031101e19145102030710105100e018054042110402d038407142a40c0400c1d00000c407030196048801d06a05081001c0c1c95420382d10f030003007a01400b150141c83d50041054418646000001c00540303e65051b10394004a59a40104900030a00202a0b5900903240c24282c8010b0f0b81174071031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 208452131 1250 208450881 208450897
    0x30f01090606080f120a0807200618060606070b07090e04050a140c090a0e010204090603080705120315040902010e0603090d090b04080c130605150c0c04140f04020114 73
    0x20482c1441c0c1814541014100d08081da500d03001001041c590b071a10b01c0c125807928409040690484d00d0703800c4110765800000a0001c40c1c0b82011b5080d400e80c2e44006145031040b40c0d00400b0441150f00b440079181c440200391200d50f0001d00901640c0b00042141140c030758040304520f028031100c1e079905a2146800001d640950b0300e42c1041040c141800031480c4507202000003a0700a2550b002d9400200d40980340061540032000c1e03456144c1c030303044c403800e40441b802032000304020b004040d26824803440c10b40c00604116032601c82c2402840b040c030301450990b44240e2600402c3c0c800101801e09020151180400807810001607a02000340c1d80e8a0388040d60281c21490010b00d00342d212400094148405600070141409081c8810005150b0004041109103c292011102940c15a08000140a56410840d44468600340410320726070580082c041001d110011074400c25141c100740400c403624040102c86203c0010001104e4003030074461207820910602d806000c80c0c503103260058a80c1c02c1505 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 208453237 1106 208452131 208452143
    0x7060f0b0913032f010b0f01090312050325020307060e06062101060906060f0f0315090e1c05040f050f010f0807020f0307290c090609030f0109 63
    0x2030002c10343c81ca6091650802004e030080e11740604244440c00340940040c2c19800441d41c400c6404c0400c40303030018048c0c90764480e0400200d0b03240d4002812145e0a28a118058803040c0c4071400c000d80544680c2c0c099901c1b00380528110b0250351030016600303002e1780420107010f1683e40b40c85010000d0b50007200d0004911656200c22809000b80b58048600a03103003600000e0780c107400021302d1032030348907a6072003180c0111058010340c12141003510b504084000b8a03800e110180c10350f4008540c0c105c3e590100e40385901c14107240c00107410031301c401000168000c2030400102c92401c01c00720150608035000090300c00399400013020070004034200c904000071800400d040034020b01c000b400140d6900e00b66a80c4040904100410103903003003103840701250a00307581c2c1c1d60114881e4024050741c114000c45203030496400401c8000d8100c020815490300035080c191001200c244650285148030b10 = true := by decide +kernel

theorem cover : BRFrame.Cov 208273381 208453237 := by
  have h0 := BRFrame.cov_init 208273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 208273381 ≤ n) (h2 : n < 208453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
