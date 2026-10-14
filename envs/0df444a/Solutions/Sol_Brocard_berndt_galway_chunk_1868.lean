-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1868
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:57:45.571372+00:00
-- url     : https://prove2.me/submissions/a84c86c5-24d2-4668-ba61-491632e7d11c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 335791366 ≤ n < 335971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 335792616 1250 335791366 335791369
    0x3010f14150c0a170c0d181e051c05010c020a15020a030902060318060106030e1b041e060801060e04030c06050c12040b06040e010c09060c080903070f09151a0702 71
    0x3c008044040c1a42145900005075030405200800f20000540121805a188103c007110420302c82003956540043c018020f1018145402207a041c01c9212850300142e02d86030340c00180700d1a90007414100214000c502c0c070382003000a0190b01c0409003c1d0000e408401a15141c0d9040e00040b0b9510001c055400140b104c01c05000340c0c4200c0415130054902500d03860a6015146520170181c03d000b4913101d00030000404500c00e00540c0c0154020f0400b502d15102d48030140024501c031030681550080e04d412003206000300600001c0d1801d403038224046500e42c60440d203682101c61981000703c90b900020108800f20ba0005032800803150f000d000000c4641d0307075000d035600600038503102c01400c0c529501408203000c0d0b002652805107100b1201003101500d0000c040b400c99210b12a5400810405881084220700406c1117660803402024224540042003000904248003030304440d0101800c0481440b9a0403540b140125035510b4591807114103081103034035000040030f600200c4003030b00b0028108046 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 335793866 1250 335792616 335792623
    0x20c0c09100e091615170a1b020d270b0a111b010810230f12071a030405060408090102011b08150102030f250f0803010f14150c 56
    0x1488042200600b50410f8429240c071104070003410400c04581c0034000c0740118002003299101c0e4402c1d1140000744a4000c4131222070000185240911940d9500d8140e041340d040c0110190741c05182d024000c01000c604c0040c0c481009031600b8600d10340300c42c001e48111a184469041540c9001c4441e03900c6800c0080c080701c030368071868005407050103200200404d14694190100000009803142965903442490041d841102442100191a00d19540488544200140214036900070348a00d43d440844004112070b1f005000c140f42081e4000301c010490000f40400d8861841c5409a85034610306058895070f0b6141d00180010305045800200c90046a000b58002a40320100504801481c40c2e074007406018403400312000e81c0345121400000009610200131194441d00c154100ba08081c3d90343d401c0c0324001801030040000d810555034800204403d100c00a401c103103d407000660340d605003414049408103c0d8000040071000038010400741e51510000e080c00c031201c1c100d02e5151101410042d2a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 335795116 1250 335793866 335793869
    0x3070f030303020304020a050405091e070f0806250c0615030f0501050406050601020c1e18040b22050a0201120f0c110d05040515090301091703070909020c0c0910 71
    0x2845410040000415802d40c000d103101724000c40380320140c15a0f030300070700040d41c40407210700c245604501000c0040c45111404c1101081406080720082519001c109400b40400d800170a201d6201c00c00b000110210300801040041c40701140d00680c0740400d8001c0c0c10540828801096580c8941030f07000d0201c0c500e800c40004680220707115400d42810304200c0d0090809850036140d00b070070440012181c4d40001900451719402806414118201074000c1d80750b192041e0708513500402c8541c2c0680000110310785c4d41e005900490400704281826413061400c8918080c0f40e90052800041007400b0031004039582106680a082030900000c4101300c440052240401034001c1c245000b401c1645990b001c1411002c1442d0f034411101d043d1145042503655009070310034560b101d00f072450f000300e51046440103444100405000401d0081e400e54540701c800d11103500d41b0083e11408000c01082980c030980c000010100c48204500e48148108504c0d2103120480d4818050f102e90404507000c4801d448a810 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 335796366 1250 335795116 335795129
    0x2090a0c030b0d1118060a0302210303040c14010e010503010b0915040609141e150f0712080f090c0103090c0506040308070c080c030c12010e0607020c04270807020307 73
    0x50544040d813074840c410402c0008040d00940329040070310488a00486090b004050041c440002540740d5030070025114001441e80d803044100300c540c0e41d40e00200304080c5000c0c911940310a00801c1c1054255401006109005030410107502c20352103180e40c21004407419510b6900310284e4a55116000c40c000440303104d14149a00d200042c00102103500803148019074035103001e07001014210f00108100c1f014513444070f610b500c20507010440e680c50300000911042d405001007d04204411080180b1500050015960307501903007200f02c0050350009140d41e0201800003047c0050800c4088150750700c1e0144100c41c145030751440181c081c8441c0c0500b410060100401495865850346003c0700303e50042e0b034040310620000040481d03407040100f41a4054034014004007a801511820400280c0d1100c100c8502c9550b1400f81a0341000c050000d580b103403000f6001021882c00800c180005c0303d42010900352005461046824149010842e51500300d4120007441d44035455030000030f003428210350000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 335797616 1250 335796366 335796379
    0x1e0a120e0109170a02010f020304050c06070309120605040606060c0525030606090b01110a0308070c080f0c0601050306070c0209040f03091e060f0f120e071805040b09010902090a0c030b 81
    0xb24081c1e010f80008180075409903000707020411010301c404003a400156001002c50b044101c0003811070429a004d002d0650003031910a100755503491500c0c4c0c480382001c0c0103948035034440040005024990148500500703451409003011201d6488181d290014042490101040e00880106030707601000604042c42d0072440401806a495000c04000d04030482041d01103500c650b10b40d401c072000800e00c102d0b096019202c8805a6945c000200c0f0280a18502100c80e20018401d03e1208080350028083c45130440d070042c903495041a0401d0b182c0300d0000e25560411101414041c016103400d00c059030015070102070980d440c0100e1034203980e564902d40040c103580058140402c640e090007852030048440d99202c0c0030150320000011100c0c002d0b000c4104004c80d4001460b0360064a495110312408114807044d10245a1a2002074610404401006a0300c42d02c41090205000c1400c28042e0401c205030001c00c400020340d03001c948030300c0c80204155001aa910400840a0700940009040c604024181d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 335798866 1250 335797616 335797643
    0xf0603010b030d0221090d06020309160e06030606041509020906071202151e010b0319020a090314030a02060105090a060e0f042121020705010c051e0a120e0109 70
    0x390b07155800c5c0314180065980c4280310b10040b48890850f0b031000005450101c454819844001c0a944090172080091040016111192000c17242240152403000704090150400c541050300e010760103400d89104a2502c9403485000030660b182e20120750328140056258070116000403424000c0c5c29010301071116004141910300da01042d0441a1b410344501a4074540f580324000d80820310651042e055903228038014001e0600800243d07030312124a0120410b07500c07002400e241aa0400c1111002003440d117441401001780e08240c1c1403554030401c000314140401c00c40025640c5806100300b90042e0900342c0421048012500290003400d454141c0c01c170681081d06420102d40d404440a40381100015005900300c60a2071951281c01420f03510305043c0041d01d41184181c500d07900303180301c3c41d0303508000503000960300703000b43c4100030006e49030b0986488582c0e8182082c8848010f00c0f118a500401034908180d0304009040f14600c00008001401503020380000d004100c181d4014007211107000c40d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 335800116 1250 335798866 335798893
    0x20703061b0906030c0503040f02031c03150803090d03031d121c0c0807121d0601051c0b270118050106050a0302180702011104120c05010f080f0603010b03 68
    0xc94069948040843c0c1d5103c085044850000509000440400110b03011a003034405206078140001d0548040000e084a0040c0c102c40180210021a427a440c284481c2c14102010000070070b010b401852902c1d441c440080c07603d81503007100506243d0f41d0341101c061005d2289094055141240485044480241144030b00360801040200a00e2007581d20821082450003180501c641c980c407030158907101d40e0001e880c840409040c032600d240e55a401a9009145c1200740d001460510003c0c0000794140740c284080600c2044070001c070044142c01c11400142002c0c49140c1c0001c80f4010b041e900e0030180c0b0750000800901c41d03141d002e0b44c2000141c0c194a0491882d2400c0548514000c001840d035a105000094581c1d1101950050100110060075402d015040782c1c41600e52000241c001030103e032003e52034102c0d4001014042c48170707088008001d980502c0303001501d0309090145041d00d101c90020b121410007000244401c1c11240412100c5e01d094105e04a101802000d0301e102c1642c848 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 335801366 1250 335800116 335800151
    0x71a0c031201140d02060a030b190905060a0b03040c12050c04060311120d050409090c0e04030503040c060203031b070507051e030c0a080c0603071107091a0a05010f0e0102070306 78
    0x1401403050000070f020805244c0900e444031299400703070542e41045001d8030240e008040042086410901c01c0c0201202d000c054a103c01c094004910001001c0c1230400900c00140c00360b4000e014074060800510010814010b641e404690890001003003043c45e51038818105100007116682140c01d01d5000320401005041984100005071503410b0224042004240c0d0703a460000201c000c2182000706200020050f004001450302500032002042d40ea1220404508822641a0b00042000c0140802c000b4485000002004203100560450410403801548050b040c1881d440c8088000b4984042040520012004000003000c0300b5034410314000303640c030301010074680502c039008049045030185480048001983e642c1d10060024180c408184515648058015014040c07040894110403a00b00809030103440d00702d10200b11034544103448c0140302140f680e00da20a0030b5003801444036076800511543c05028920344001542d142c040107034240719240e080640b4140c2000303000c03400362034100c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 335802616 1250 335801366 335801369
    0x30d05160315051516050a08040305150402010f050304020126011d010b0909040213090f021008190f0f050c07140714190810050603160602071a0c031201 67
    0x792402c0c8800074031070480c0b00c0c0c0310425003d5180e0054011420f00c0d105020b041c060b140446078110404070070380590700c2d081d1411f1080c0310b044455090004051003000010301c09503032203200074a0103901d1400c084c0d0019121003120040f1004202e400701c0080e0135a0b208541c015810394410000750b40d185009082000d9000c9c00340180d40030701016030f102440c850400d5607214100e4034020366560078041340c0c404000702044050416a0b04c4100c03c1c900840c1548248038900c03515110f1144c1a00010352441800004844116040706111005003044030080140e802c43c0800500f40380000340440b130703290b00d060082a240480700e9003d8a801d04215000e03104400418103580280d4083c400a140c02415969a080c9401511030000246000300d28034107001000108500030100f042c0400c940f074204040c50100004004241d8a4a40e0280700c0d00f13080610080140200d8249000c55150511070f01940d2450b030340c49141800440c9030000b40c034184401c0155100c00f9000b0b81078a9a584904c4140204024203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 335803866 1250 335802616 335802661
    0x91023040c030219180b030a0c090606080a0204060804140304081209040e060108100b0102011b180e13141207140706180b070314130f0909030e1002030d05 68
    0x502c442e0a9030104420080f10171a44001c0311520021008041c2c3d8000e0302680410540605c2034a2090380016404503a20024000850f0000342452804100030903401018010180c1c0e144100401d20200764055440c80e40b164026004175099101200421724500c110341c48480207000f40c00100800c26200340041440d024101c405014410b1040c035481e480d01c6081c0b11307485455029452a80c0034101c50b810400c5407490500001030010380c0c01d0843c00254048030f50507000910020203144070103420921000103812042c0742d00c2c1d46480d00f103d45000003001e013000905111340910350391002410070000007c4410300d441c0d1041e1205828984040380100d4190b041c0340c03e0044004c081011341c42004200034848500b69004042d501d01089280e00ba4859801641040303104004c1e400c0a154900042c9020300024014220300b80c030f001602c0030740b00740c1178000d45407107810410b01d40b001c20392110b441600100100c580e02400d640c0d07688184d15500c80d00b180820001e042100b041000e59081c1e40c103030f280070b81 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 335805116 1250 335803866 335803879
    0x408150a050106020703241a10080609070e0a03020414090f060c030f090c12030a0e061806090607050a0f03030b03210d0b1203040602070b03091023040c0302 69
    0x44a810900c00e65900f4007401d0b0059028050820107d194120704030240c0e0201d4910b00e1001d50303180390040c1a01c0312104402c00d0007080d04c840f001c2c00c0c1481c4007540200c1e00ca03031030404842d060003030000380850b40145c4400108408d54081c0b103102c2e92059046001154028010081a0070a040d1048641ca045605025501440780203480003000030809901c01c00800401c40d1441e50781450f0340703d40c0703840640822130510580209100b1510303a07040a441e0342c4c0c4458010764565414807402441060024100360084500307010900b241c08221640880c94481140e50715140e44400c000f01d2154044c001c00034000e40b1a40e10f0100500044100d05c2d00b40d10300a55050251281d10024140c3d2600385515440c0c0c54840c0042070503042060b803001e000c110030382c0e1102140320750500c0d001500b1040505c003a12056000000d040024ad034041018000802d12841510700394076004021a8451039020303c0840456101d044580500c00c50041014001801110452a605080c10306910010307850008a00808 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 335806366 1250 335805116 335805121
    0xf02071403070b120a06050a030c2309090c1504050d02040c020f0607080417070b04020d0204180803090c0103090f110607140105160810030f110a1d060402090d03080714040815 77
    0x240300c084c238015280c004508114103031070041c00781e40c0746075203e540c00d85134200586001c8950b41c2d1482100c5c058142c400c001d0403403541c030004004d1840408440040030305070401007000302c1d0f00c40701c4406c2c62203501210005003034119002d007070742411051801c072142070044104200e080d0350031054280c0628010030142c0c6550a2028444000303103c1c0075800b420010b18140083d00614001c640031a5280c8040c0010802c41c0741341881c402e00301e030032000c11a007040d0b001c0308001495008001041c0f1402003460284444d2110341c036204901402190040c00c42e40403500e0705400d40d20340004984446901110b038110010200f80924000c2c101510045585c0d194012485183c1b44100607042c0141944018047c2b03031b030320315a01d412441034400c104840d91010300d40c000e03611356503064034000101000640341c0d03010300040c0f406044501c00240990712841c41400300649540b40c0c403a44e1001c0d0396250500b5842c0b516088402c2e12054040010180170180009000c1541140800c222400c0414541c6800054 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 335807616 1250 335806366 335806369
    0x5101710060b070c12020603180a0b0112112407051501060903030f080f0a0b1507080403020907051e0a03020d060b0d110306150a0c080a020705100f02071403070b120a0605 75
    0xc0500c20081e5002d501880800c260180d074a251551400580040b21103510140e510b0b02f20b2080e0980c03140461001d907aa090003881000c2c001e46628050071580c094181d4000144440d00c4c40820000c0c11040c3c4021490300308002040000b440b0204005000d05261b41e92400010012402400120b000810f203101c0064002c0c010b02181d03000c0c054004500b42d0644e03c0d80c6074a0010f20507548c40b40d5000005190b40e00b9491041c2005214844c05018882d54550070760052004034040585080d042000c20016000898918048141c8020070b00d0041661800100400c401a0081030340c0f00686a140110000d21403040d0307401071549000d07080c4203000c00981c00c1c00b00320311404101c600d41d4000d400118200944d19a4800805d1150b50609020071952026291001c140d0003c003448405a44180d0051105290680500c0004003403890307c0080a08002002074845040c0d00c505605010210414034956a080c05950040c2050b0081d03035481d29011030030041c800c10241e40035207403189040300c041500e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 335808866 1250 335807616 335807639
    0x30a1704091a0111011b0f03060315021218190c03051009050c12070905040c0e0406020309070b093d031a0303040501020604150902090c180405101710060b070c 70
    0x41c8062900050490041046c1641c1510300d24030314004041d034441d40800056401d6000d00808038076206c0050700d5401c1c4103070014861002504280710941080d804692001d400569031025940112612050354182e03d00288200b01c2a0402070080c0036400301a24004000d600c81c0301264000c50465008203151010b0100c07440880491a0840c2c2007540144640e2403140c00882d0041c0c03007000e488601d00d0b40c40e28032825030681500d041b1000c64000040c0f00152000304030301c0024214080740d55140c07030322140000741d113840c1c141a003100749400303c8003030301d0302422004481010424a440d0003900700e01d0100010010440b10700880c8400c000c2d0040d0b000305040010a45055510603001050151526114040426140f400350141c894030354480324010b03100c4800403800b40c1d4905800d940c59030080007c03014182c0400c2a05806107103840108094114019404403c03500d560800201d40d5020860650408130308040525004c1e0500c000003c803005d07000000e0003041c1c007901c14903e6107629070319000003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 335810116 1250 335808866 335808881
    0x40e01080a15150308032e181e05040303110f090102010515030604140a051006080c18060d020f1f0207090509060c0a020309040603111201060302030a1704091a011101 73
    0x100780d105034000c2c80060000e500a51301b00201c0714004103050107801c1110f1f001562045668032407182028100200d10362a840038050714180181440000c0301030035800090b1107001c0e482100161500c01203001d150081e40071030040003680d5180f5a40f02d41c44101000d00d50300100c5814019071902002030041003d92031040e120700c2004018003255159600c4040c2203c002c0c0d041185079028615540001030801c00c80c440105510388004030b0054504401a030030000d400700c035140988495004071070031031510540c881d0700200481d002c1564031100d0001c04c06003c510050281c03c0304900004220b40c45260004e0b1070044a680e00b26040d45441c0c00742d0000707580b0150344840076940030401149840b1581800340c82204a6881201d0500003002d0005041c0c41d1140c1c01501c200400d102030034082e00f01810080c804800c00300083c801e4a1555004c01d980d00002640545440f8940000208500718102250700504a10500380280048404003c0380750301d00d50201070206041030f01d04011000c06015951 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 335811366 1250 335810116 335810141
    0x20601050f0103050709150f0305060405190515090109050a0605030a03091202010c0b070809060106022a04060312080f390f0a02070306060806010807031106040e01080a15 75
    0x1e44615420010341c040d00b400b81481c418001008404200300740715003407c07096080d01d0340e02d1101180442c80094202c030006003505019038100401c20030a80d141d0b2080c91084079103400002004c0d6902820b03083c8450040c11126440101c400001410b02d1442e04114028080d81004100180e0741d1010141d8400c03620000401103030000108200240000054420301d50041c1455040419180d40c4c9a05019040794404007113400030045c4080090104201070141c82c0343d00003401c006200d4444407140d0840c0103606074502e5400b0700d400b0f40d5034480d40c1150000f982d0103004c10026126624010304094012500c0c1d201e93794604000416040d4144000d540381510080092040c076141090209000000c0844030701109040040f0060082c41f00020451200c00da805060324500390714001e800d8074516072110103a90300c07090040c030450300041090405c40e070344140031102202c1154045022801264860b2150709a0000000744030080801c981e502507116110302612500b004102e281190704030007003803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 335812616 1250 335811366 335811379
    0x209010c0807020303210403081812130f0b03070e090f180f0d0201060f0902030705040e0907031514130803070c020d02030604050d0807080601020c0d080c0a08090a0602060105 77
    0x40d004a078405004100c4a03001905481c41c2807640b84e050400c440c2080c0c45199402a59420401496409006960070402166600000c0c640b4600c2042d525151107801c102e03d8030340003a6017050031800da00310b20005c02005030b00811407030b6550394414403608200c645001003245420700c01ca6078500000241d1082031140c2107422140c50341800d40340d10340418200c2e122144076043d058000e003001002141d500fa511940003280031030400480c1c651090740345d40203074000c600500504c80401d81120a603000d40d00d0550a100b403c0d59080f103c40e20341100c951018120303560b8207403980480d003410b8002ca00d148244044804294503041c3d40f200c0c1380d545841000d8807502040c004200349034405d1001c54109800140a01c03000c1400e50002400d003c810b80d0210f403c0d17801600d0100c0c5035a003004606521545500b0f01703405c00e140440000c3c0d1251800002e092050000c10303580c4003040556015900058904001c64a02c501d2900c0c00c41405c1d805100003520039226514001001840058220b0680b200942174 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 335813866 1250 335812616 335812637
    0xa0c0c030305040201021e0c010e030609150907030c0306060509070f1710080102030a0504030206060316060e0117090a0309140d02040e0c1507060c080f070c031b2103020901 76
    0x110000c182c0034004034114060f121640480d280000281418000048040c0c10041c4603880050454600d000308980203810000030454111008141e0781c059080c030780300700c1041c0d640d5040014109565500001d015010a02010003408895408030302900e17429a09a0255240c2080903a060090322040c00005034000310409007007031a000c0f102c0c0d00420000e40c4414075a0311580d00900360703002111000c0640d40d45808000030f02d541041405c0d040780003a000340420000040030400246094001d04003407051003100c100659200d15152801d0000b003481015140c208218403d0303c444d11004142e0004c0d801c142c0100781904212182d02100340000c0058038101c1042e400d12014106c0030528200500911040015940f1958440c020000903c40b00360ba94841a2034000102c0b074440c5100c1003000011810041210b8006820581215407030922404d2020a071400310307a1142c4107201410608418045101080340c2110543e00b0343c1c0c403452954061200b0030004900f00c4c024058414000783d0900c10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 335815116 1250 335813866 335813873
    0x3090b010f0b2b0c080412050f31030f0b010504060b220e0118140114010309050f1207050609030a0804230102120103060c090e060418020904030302040602060a0c0c 72
    0xc0c3c404825030703a001040c41401e407000000d000c4035600c140c00c0700450810400c0000700042d148100048600c513080c03560401c0701c48050641e60b8003400c84030280c0e134401c2c1c1c2e00703102400c11003010400603402001c0d201e03501c040d12403508102500000c2c2c01103c422400718004500d41c900f50203018281c50302613036202e0034803144000c07801c5584885e203060400350b0035240c0003050020301c521200380681400c0394890440e04c1d00046690445022070100300c8020201c0300184880cac0840c50384024840802d20300803403011443d00b00181031004203e50788500e0b1040408400e18080048042d158031760141098a000c0d0380c5e103280ba9520703482220f03020300c0000e0b0404001000251800c401c4205074124090401e010360314001072a0890340184039450790f102c5840010004c1008500600b500d100c1640b610000c0c1c10315124a25100d580040c140c14401c54036030b40c0e04590003c036894500d401c19001003a03003150342400c3c10098002d62243c000c400041c05640002880b18116000b100500740d4bc80d515503510100944 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 335816366 1250 335815116 335815147
    0x506030f06070f090806040501020c0d020c0f062101080705031213030b1806010618170604060f0207061103060f10050f18191517060d060902060a03090b010f0b 70
    0xc45500c14084e10103404560f060781044001c0c45a0f11500005070f44d001840c48003490001080759050442d0b001094100341a200d0002d006000442920000d4a40c03c0d8000356aa524040a07658104660410000120400005400c1301268030503815030300300d50300112071001c5c50710909941012041040f9809c00000c0c000004882c2c0c81108800c1c540310260300c140c40241403400c20ba01c0500040d000311012011100c1703112681004054000150b2040c0b04a0307280c0f01d40340c4e40020006011941c0c1d0b5500d80d50740d821a901220183c035400344080106e03040700b0401c0160342d0021740c1d005000e5802c00680071503c1c1044070401c000000c6541302c9604041e00300a5100c2658051a049846810a4007001c100c0e03486180c00c80480881003114107484604001540007143c0708055414104204a000d800e10072911011040d041007040d00c4940780c10301036050000c05091242070080d0000303000520980750307640c141d00002d85a031258040300200e9a03546a08800c46010307006800c800c403010000641e2402045 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 335817616 1250 335816366 335816387
    0x31204030201020f07050706020d0809100c020c060d06090605040504020108040b090a0b0f0603150c04030609060b030604150501230409030c080d0c03052215020702040f0207060506030f0607 83
    0x240700140c5031894046540c0e07000e42041404840702c0c0d101100500c00c640c0c061009a01c05402c80c0382c6a40079107480d1541b16940c007142c81e401520710750760704010351300d2138400e004135103049602030036082d80c0b0740880700e6601c014000c81c802e4218052415201154500d0280070f007500464050750340f03244546998440c04070a0b0310207860000c040c4150700446002030404624a8444c06440c400c9013080d1400c0400c0c50b0908000301c11000c0d8100015040002406400040d40c0031b8a80102c00042d242c0340920b81200145040c82c40c1c50707818464074007000200148000202e00f0800a903d090181e41d0740c03900f407650391610250441c01d24594403001a0340c00d0800e607010401303075400783c508040d4070407507612585078951020410b200c0464564020f1003000e505030144a4000f1030480402456685801111510f0000041d0003086007103d125800d00f00180e6030140c0d0804c503001801005680e9010032300500a5211a90850307849080400194803498041804984c0c0e0510001400d001d942d4802d0444124004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 335818866 1250 335817616 335817623
    0x905150a0b0a0e1f0503070b0a050c10061707031208090c041d010b1c081c0203010909020406060f0c06200c0304030b010b03070c030f0c06022209020408031204 70
    0x907003031400242d0b5104480c9038010400039002c100a82805641110303160315403900d4203052055103070300b00700c070307480c00190082107880c2820066191300300b00c0740880e0780d0300c25910400c1c001e1083c950104a000c12a60148040718489040c0707281540c400304065840383d44d680300c060f214410320001141040e0003209802d40c005d00710b0050300c0f80390865000080403a00401101d800b41328100705100203030482440740c001018021202d032442c007c50455085496224400000c0807000d01040d000d4000d00b04043c001003420200781e065407250b850b0702409008144401c0168825400c05c480010120b000e10f00c444031080450f0781d112542c0302142c9604010700380b6003c0b020305040155001102e82c5051201510318000d031003000c1d640d65171a6042a20034a035040c0c12640d04500c1c200107101b0101e8102000400182c0d0500708108144030340c030f20555240600100250100740000303039542415441d411a05003807600c40f0819000d06498a1920040b4084c07400752001591040040c8248010b400d2034880d0320912 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 335820116 1250 335818866 335818871
    0x27150d02060a030b19140402070f050d050d14060303030a0b0f0a030308010321050a030e0a0803010806040b07020c03031c110f030a061202010e01110c040c0905090a0905150a 76
    0x1155400326605074064815040081da49003c004e06610b000d0200c04500011805810040ca0034000c0001410f0342d107400ea54130031640020400c0402c0344d400281e1600301d42100c29554078101100c00500254000c800e5051018904559600c1c0185000c2d40c0c0c900490b000f900542c02d5590340d054110040c004601055440f9000025a44117a40e80c84034882c0236510903580c5038465490340c6041c5810580b8440c4ca455501a1110180c64496001301518032519887c9004181d10070f102925504001510030090220360380007001041d160030025078580241c0c41aa444459951494012610b612042e00701780c2d41908104020000049410035200301e12580203000a0400c07214450444542d0009044400b500400b204010b01924035101d41c0008043c6981c0d0119000b0003980020500413242056038141b00c8101650500b000b0100842038a180c4098010004403626405c09020009248181c034811000c96000802c00f680c68040d0b884011751000c01030800f41c41011118154020003404a00c40d85e9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 335821366 1250 335820116 335820139
    0x6030403080610022a04060f03020d031404090c03091b0510050c032709070302070b010b0f0c010c0822021509030f0a060203160e090604051e152715 65
    0x70100c807a84031210561a000340d1700e85400a000940c0c03070a0f48212a005411001040542c444825030300e00c540e0300d0319005102180003a22101c0c0c90060343c025a03d1103282414881270b442c0c160303003d030103003070700420200251400712001d41142c00b00178011240c026216025180000d8002c5024101c000707400b0080d40d0420380c107449007815040c00d0300043caa0f100020b207040721040c28500c0070290403090600e01540303040001c1e2240080c41d0070620481d4070380e02d80060840036050001d000c1d980c1400038178000340240381d03a1100c02070000f0b600343da09401510a9940e035100e00d04203420717103810f481e90142c540b1161600c01c03a0b40340080e03040403040b144c0501410102c10130f06181404083c1e0b180d803203040c0050b01c03401d14141c0044a40444c1082e0720a0018030f000007951952502c1c10a9840b0000700c1d00843c0035070300d500368954400c94041244009003a2031080c80f0102201c03003e40750b01604160741001d0003812000d208880749001c2e0324868030103600800420009041d035284109080b4000e441500c03204d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 335822616 1250 335821366 335821393
    0x100f0902031c030f151505040b030c0702041404060e0606120615041e0504170a0203161104020f04090c0f050a0f0207031416051e0d02040608010204150e0603040308061002 75
    0x1c0d184081c148411030602002803006c3c114115035024044098030340300d420141040021640c40c40054021850044042201c500315601d6800c88038a150f2544d0b010310007801c161401c00054500345c04908964028000003d241d41030a490155036526003c0003060aa2030315074500287c6085502e0440d0800c0e01c43d00741c40b511965688800e40e91101c0b607400000e00e8901070404452411100c030840c500032500b0004040d501b90f001098440c0c1c01c0c038881c1c1c541d001e1202032030301500410b08884c2464005002050302d0304152025005041118244841808a00407007002103854984d400d404001240c0140014000c1c64420b0481c103010120b640101c40c285516612100c0c101101102c20754a40d038010005803c407140c003035030385c00020401914512003407042c69040001590980106c10701400381000c0501c00d40d910b41d080385000348401c5008668881d20b418043c1c1c003041f55400b101000c5580300d6206034460800130304686c422909940e076441e040c0c40300d0782040b40340d0030100d81c407000314840c14000b044c0c203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 335823866 1250 335822616 335822621
    0x10219050712021b2209150f050103020117190e01020406140a1407081c0204090b010e09150f0628140307080603030d0c02011a0a030b011a0c010509100f0902031c030f 73
    0x660300421251521f50840307a140d00c240c0c5c4803081840001c5040100410050360844040070620b042d00e0b02c02102e950369220b5030041c0540d0303150385490090178907902005400c3c0650080c01903d04076580c40c1c0c5910509400219075101e400b000c880001c1a0800b0500303007040ca103018105151060780c1c0d0610b005010072610112402d001d5031004500d0b03000408210f90a098824540c00315000e091a241e0b070203440c000140d0780d05000300b40c0c01110082000760202d55541107042d02c030b4820003c00164403076900032001364194210391408054502c0e03260804c109a80100080c01c50400c45038484c42c5107648100c4e00300e8002d00080c01ca15010311050003000c9403070100b0300905400c42d4a5031300000798250524a014002c0014001c814020000031300244045510b0f081c1d424155030b6400051011a00680c50140c0907101d07900054034a03510745002e2245001012038501014200d00c40d080c001c680d0103410f400b04035140520003e40c1588040f41e46240031100c2018040081380c1e03400e000840000000c2d11505 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 335825116 1250 335823866 335823881
    0xc08071203020d050a090201020c1e090c12010501080c09040902010306210303061409160c0503071a07170f100f0608040510060f060e03010219050712021b22 69
    0x11940200d40c02d0001c602d148104c41e032207808058140059400c5400203902c40742000078590141d00d0101c070180e403407803c48624031034002020b460314a4901e0070458504664100d80540d4150484010000540f90b01c1000424000d40c05181a940303451103200400c070017442408012410305885000000d80d6010f200d10100380d034855407400d00b83d00c14403407070024121081c40c2c00c54500d0007884c61004078903442d20014191300c01300d03c60240c041c40d40c0550003547e0400203800010401e1000007459020040400d640f4400680c41d03415201481c1c42e200c1c010f5a078a003040c40d00c1800b0951a800113045580d1502c0300940103e40d0b5003400406544518483b103020007240c1165004c80d6000c014001048810010390074228035622017000414100a550040415a849000e00700400314001d40603d80c3d003981150361034104000441d4214841000282c41c0341c0128000340c448070800010000414004550a1a1608000071400c1c0400402040040d5900c403d1184000343c41c0c00712586490a0b900d104080 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 335826366 1250 335825116 335825153
    0x302070b0c160b0307050d0f0605060f190801050618040b1f180e0c1b0312010311030627010f14190c0e060706090b04080306010f050c0d0c0807 63
    0x400031110601c8140382c0506600080c42d665040040181c969480f90a81c1c1d4858800580030804450aa9000f40941100e42010703511010001d151420f00b0204801441c09190740c2500d41c0740d12450341d40642e0643c009108807500048104412108110a4030301018406c000130300018000e00264003050a200381e01260303242d12a42441028001900444018043c140800d0f108030300c00c0c00c08009100c02400074016040c0100c2c0424601c0c0c4021171075441c40036181480049949642e005480070000388400c3c482590500e21050010b43d40f4100440c070140b1138448003001c4900c0f9030b118481f0280e860350141c5030700c001c0d540e00c2903040104002030188c0c025450b030845800d600c9007003441c1d05555481e2003203d10300409144c6010f55600703980080c0d00c1060340b20300300c82e0907840f0710145c02c051000c0d11340c030784004041035500b80410080200e85805180100401e903260004404e10b45010798039803050403480396603603008500c0004441d10031902d01c0501449181d04a04060b41c95075000c00d01c044900418 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 335827616 1250 335826366 335826373
    0x2012006100506030919081b0102030106030e0a020d03110709020d060519060804170403060903030c0816020a020603090106171f0615030506150a030504050f070b0d05040302070b0c 79
    0x2040c0840155079480c042c0c1011500245907040800c0040e607903112520084180060012254003403180080c113a0341807104075800b4041c800101d088480c001e5200b4080c078000309241c41c441086480000981c5807a2a9001e0b2200c101c040c91520b0544d49121080440b2076207105090b40400e82032160300280041d0b4101803400f11f01c503070401040180311507941c0400c0340e0048032804d04000a0307a00840789030300190051011080341c85056240c4802e07101d03a41019014a091010043c205681a4004100d840140e610038001e9143e800545020030301c0c903d0a0401a48442192070261401d000155040a8040c00024569989480911a410f19003490301201c0c0c010300041032148900064210001c00c6841c82004070750706084030401a822104612001c15030b484002824a0b00d5103220740e501101c1d10700025850392212000100a41403c9030100c0380390103440d51980480d41c0000c2c040c07060315200b0055500f402c201c100f10710001c01c0010416003c62050f82c40001e440d18840004041c42050030028 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 335828866 1250 335827616 335827621
    0x3030c0304090c020613030e131b0801090605030705040e0f1e0c061201060e0111060109020d060e010509010308070318060906110d0801090e1f0b1003020a05090d02012006 75
    0x45200702c3c0e81550b040001e40d08100c040120aa000507551040c0130751506080001c0c5101c3c0010481c2080100c81c20502d06103090042c03c0c4c50b030103201d00b200c1718042c0f0380c3c1c4071003003680c9030910803003601c9451050310740540c8941000c1c001c0340342c15000117a4560361f050032076400c1c07002900303100d03d40310010200b440700d540402c2106820000a02c81c0e844c195005072060b07071420200031035400440405118213010032850400c40b0780a0307032040303c0e0400300115040441c0c01c2541c5609210000794081d10b01070030540d20f04600050329180944015040320401003106000d0303880c5413503445055101c0300b000c40030000e00201c911042c000e010311800281480d40d1303c4545040c00d040e80500318404d12050010070341d11010070516060361054419041d654004000300e084003c00c00071038a1f1068003912000500040cd030f0b082c1c40703001141d0058440c1001110030316440918040150102e100d1265801c00040d0100b100c0381050405c8482002000c1c4180b62000700312181c10340500614241c00e961842d5600038405 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 335830116 1250 335828866 335828879
    0x180b030709060e09150d02040905060a0c0c02030709090c120b07030e01150302191a0307020c011b02061c050403030506010f11070e040309050d05150c030c07170903030c0304 76
    0x1d40000c2c01543c2001ca2103400d807440001d58100d001080c540e01482e0140c180c0085407a03c002d080901540a031042c481e1101d507140c143d884030b104407820394409181c6200d01d608031380f09030302d040084d980113009009000e06182001010740340f05401980c0152a054000420b4540c20554840d0380d030083c1542d03910b41c1040c40c002402d450802e40f150940da81410081c00740000c08428090403a64119103081d1019000310b0110552122075000302c16141044880c04080b12014004621881e071035800d840103208030700015210300d504459a001c910703a480400b00014100b220040030020070001000c03c240e0804281d02040da07404450850029031581d0501500d541c0241c903241c00d40c00141010400102c403000d407503544510300e206040c2d082041c03501041c00d06005402e002d02410001e4940401d61580d400c081385e0b58542010032030355000c1c400c400101c0300e1014809070f80c010325069610b1450a031164845400100369803030400c215070010020f2040980d0b0401c0100110b21500010b50f40720307464070780c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 335831366 1250 335830116 335830127
    0x70209060906030c010c05101a0f03150a0207150203040302100b0406120b0a0605030a030215010e10260607030e0606030c030d110c130203010806150604060f180b0307 73
    0x103204a0040d03101a090020541d40460900007241003841c10040e281d440381403d40c82e00c40742c844844042c5250911000c10881e040403000e41c4240e05a4400429041d00c40a05581703003001c0400d061404450404a1514000b5030024442076010b0800d000390504070004580807079105440440160b402843c0501404816001c3c88110b61001c6504024161038401304d00300d414a03025005000c41c0401c80003c20701d504551042002d4900a4212000740b40c0e01d240195507240d0b0341110400698181d40000b90300c82000503441c0c82016481a446581490306e44900c5084142401300341d40c02ca020b00b04003070212402c100d094860000ca0b07601160441030158480d00b01407020b40254060303040411984445d48000942c031840f08494503140000301c12011200d0f080c1f03030786084444c1d885144007926004060054002c0c6d41070343d044100741c5c0c0c4240c6821184142c8040c1003100c40d034104070240010448940205103a00601c0c0540c05c00c00b24501100c94801116200743e00040c8a05201005014020798400c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 335832616 1250 335831366 335831371
    0x609030a140d1d100b0102120904060305030c030403021f140a0309050f0102190305010f060e210114010503060f04061d060405010c170705070f210206150d020604090e0712030302070209 81
    0x1044c10008602400300007500e4900380c0e08070000340000020001c45540b105d900050085402000b501d80381c0b1400e0051a449501511090344100203002c1841c00003590110004008080d40d141c4140c51160070011009a80042e02d00205140c1d036002c0c0c0c00d000c540103110351a105081313007000595441d141c0340d5440c92001203644060402d0300d07081c014414000a4142241552580e0601d2000d190340040083e2007100c419a0030420a0400c60251442c2c1e0015040b440590000b4a400112681c80e001455941d4800300c5400c035036043c5620119000c40d02c80c0d40017001621980708034007400d46500041925008040c4d4045405a42d1a00e03401348542d07018404038480c203a06800e50b0710303606011100425078010b45c00041d0141c1c2410000d00100041411103070a03140d030101d030550400b802d40f14007940342d0320111807040240c02425084231207850002210610706030f0040000c0d0a160800d08041d00403c6400068080d038801d9180c0864500d6065421100d0369100341d030f001da990100340c0f0600c606004003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 335833866 1250 335832616 335832643
    0xf0f0615080d090806182401050109050f0d1407050406031113061212120507080a0c09050102031204050f03030c0304030201060b16060f1512020f030609030a140d1d 72
    0x24480d0078880100c4c045280c50700078106000f008003000250b05000d0400d5550304107502e01000140001749218800c50341181210b1b000d89540504943e160706210b59809460076050380216101603000000352800e4a104d031550300340c0d0840f171450307031100041002c036000c036002621001400655a0b02d2480c1c82c1c400610180303a4000705101d26031074030400380d242e050140c0006210306080c015681c4107a100b4002c5200303400c80c43c03205115900302031070003070f09081d8281d4030250710a05045001c60460300454115007200c078180e000398600200729483d100c00d554094030899803806084030b1500b0200d0100080d6004405018495640f41010300d40a0700b190025407119081c4101880f4000e40c80c011800c0201100b07030000c0005c00c0e481c01c0703962004000c0660f82d10703003003010b011003d0109241001a40440240c1c0c4240c0303031a003480121008040d0345890450744221103038010066404100d21494504401100310b042490900788070040c4d58043c1d8042c09400c007807000c14240b03680d410f00803c11640c40c0d15842d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 335835116 1250 335833866 335833877
    0x6030b0a0c0e060a171003050c040501060905060d02090306011e0e060d0321062303190609030519020a0c05060a02070b0a0507020d2901080a0f0f0615080d 68
    0x4002026102c0400d00484520820b80030034a14003407030003a2003e03041016580340c040c445144c000d07401034021100c0c0c04262010301c9280c0359189241010b1140c14181e0301c251b210150740524020400c26942c0c03010f04100131154007805850002d8030200003040c06001c00d480b8600280014101d022001c07401a4004080d4401305003d225281d1240081e90f04419090300d82308400003c0d10310540007103101048100800c2e450f1240000f2131142c910103545600704141200000843c800c010150348030400e4990308240b01c9804d400b00001002684080c0f1094800e080040c108a060983d0b038824480e2590004c002d40c2100b0504401c2288004844010b010116812820403080010003596180c6500940411490001c0c0402c1030364011025658841c1d8000c00c2c0940c000315510303140c0307050b140110390f80c0c8074900300091050b407403034010103582c1c169100302000745807451041d00c40409410b503003442034179205400014200424824050300caa1039002c10b6690320b52510b84440c0303a01d484010b1015004014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 335836366 1250 335835116 335835131
    0x70303050322021c02010f090605030604020a0320120c07050c010e031c0908070504020703020a03030f020d020f0304200307030b040c0803040f17070e01060305041a07020106030b0a 79
    0x260000156a08610710441074000c41569403640075200780c040702c000e5400014019408030914001121000c424400c0c0d0b102d030003032100d140c0305940c000300e10b0080c6c0300400d030203000151141c00d2640c06403001c10340c00d1501103114101c030070420a2100c00c94200a0034520001091807440035008541c2d41c1007800206800c3c0340868644456454014171401181001840709840300e40360f03030801070381109200041c50034003c40100701000d81703003690611130294503000300000020716203410b1081e9421590103801819000d045603800720010f180b100090898541e0a00100050b05410f1000e0002010000300340ba0341e9040c85c1c10039085400809411078403a1411060102031504c000c1907000441c0e41c00703e00a281074840d03190441040555400821140c0700c0404c0c00119482c43c502410300b00e4144410b00000038410281968450242d4000c0c1401a550340e4010000d140c4a0b500c900c0d4090300900c005120084d050309001201c007401d8500400507034640d602032003804075201d400754005214920400c00503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 335837616 1250 335836366 335836373
    0x90304140a0f050f040f020f0d0e0115050112020c061e1021050c060708030105090112081803011503030801060210051509130503160b07050703120f0209030303040b0402120703 77
    0x750303403c0c050503000d02581a8120113549441d000580102c20302c02040d51180c1c2e60180204160700021022407031982000003c0001000606c6002030b00d03907200d1010804607051000546040003034400c401c500590802a8444140d001d21140340290508054411110114099964500c0340a0042c0032500b4a401082140c114950340c60740340c099042c01d100c2001d00c080c1c1060745c1024050102c0076000140050003000301300085009505a4204562242e1030784d0b03c5900446030034407000b0300107140c0c1008001c031004405140c03030312a040b03a500500200e0700306201600207076503680c133a1084010405090050010903014008010703202500c0508124600e4a90180440c402040e16450301402e0800d000c259034040c0400d8141d101c2c1d0300802165230764041c1c46100e8550442503002a102c604a5401080004d0310520031100345036007550b264090400b1811020004200015002041d654200001d00f42500d00384040d500c0f84c1e016030344103490303031919005000740b05009101c1c0715450b401800060001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 335838866 1250 335837616 335837639
    0xa0c0b040c06031d0a1205040b030a0b040c0c1a0612190311010c050d0207050c19030b072d0513030b01180605090705160807050d2a0b0606040e090304140a 68
    0x176140c11028500908140700803d4640344519000a081c0b0780f0000100089404aa0450410100d041c0c40400205040d4002224642c121070f200400d4400d0390906010360404803507006801c050001d00e03291030480b41a444600d046514a001007007006620650b005064100400408400710140240811000924020041c0c82041c1b078034903003980e010903c042844010051009c050304040d105108200c005e07280068030400394401141d651442800041c00c003440341c2110050082c480c0421449084890400c02038013001d401d81c18100708007805a60b10450026a05c000114081c1c6c0e00e10505505142d000b10810032900800e1402500f0010200f10907246c1c0003034280d000d0301c3c0f07150041d00c403d07000d42e0340502280c0c0c40308041c2c10040081481021703ca40411a120b2403107447e110505a81041c04118080714500c0036412a46146d042c4010041000384401550212000b03200e1841c0648403e54072012040c1070710102e00580c000704090050074501110503540c0001116100303049071400f00280d14 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 335840116 1250 335838866 335838883
    0x1150b070206031e0403050c0c010201140a0f0f020a0c050c03070b1207051303200108010806061003020c070608040314040806060f030a02040c020d1808120a0c0b040c06031d 76
    0x40300b00200140720826110700e082410080031022040394145810003c0c0160056041d81360103006951900407150300520501e540381c0704240b801d0040b41c1d030301c150420040070314500345040740d80c46000060901d052803005008085041d00d421880103d141030251401000d00c5480e400f80d40401014030205943c0780c1543c034100d8602001c0c0d001075448500440300d5004d0082200c07844444d40a02108000c0900c80d902138031004080c104141d12000c00c01101c040100307204001841d080140424283c0c2000248200b043c00e250801600d015144800545050342c0355201030001001c5000b80010180c0c002d0030301c803200c1842d100c0740c1d04060070300032029107410020742410f214861081c0c00545544003401034034120741d0018402c000ca405103030800ba4507650071000c580c00041c08200b402c41c0b9005022101d80a8802c070300001c10038100d482c00c032200d0035444030114406100341c01c0740b5140054100100e00d032090788a9480010b407545401000790030303524032433004d440d03c007010a0842c41c0c003000080c0416 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 335841366 1250 335840116 335840119
    0x807140405060102070e070302030a0b0108160806190902090406080a030207091e0c03140a0e070b0d0902030601170d030207020f010e150c0c2412060f0a0806070201150b0702 76
    0xd01c035203032900140e00e0450b00d0791100c1e0131400f05c03004010780d082d019800743d4400c0c0503842041c0700040c240b0004443e40c0780102c82c1c2006001d850020b802c0c040d446140d0090b80620094004080b00302280d40c1c240741d250580d800703442029000a456449410280502c500908620004042c480801d42c1d01079280c00c0315004206580350341e280c043d0074003a03151510031001d000440c41005201e402d000000c0c00b8003d19040c0c52411080500400c034030f010345104422849a030b1801400e100c9060030b00440b641e6028100d014002512a00c0e00d40150358140040703402070240c618205030b003d0081d5181401e01d160442c092040c5441407047c400036840e602080d0220040c00d1030f01c2c00c0702140c0c05002030442a010b0100181c0540e0124101c41903070030014001c000c040045560428044031082082c02c0c410020016000612003846000390240711445d16580141004007050560351403200825007900795584000e2843d8020130910500d1138081c803801c0000a245007210581d03a06000c3d00d99228400c88100a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 335842616 1250 335841366 335841371
    0x513020a2a021f022104082b081303050c0115170f034b0306090f04030e1516050d09090c09260a081308071404 49
    0x456152151001c001e064a00203031090010420000710341e0811680d510072809400c800c2e0840c038070320890491460900403144d0080c01d0040300e44058441c0e501c0c0b0481100080901848046844d210501c01061030090709a40364403407035140074115600741d411148400c2404070000500540380703c810040e40b1600e030142465540e644841d003515004110040b18004840c9000c100495420740901072991000b40b42d408035000c0140d01401c654a9201d5001c9000042941c0c2807071000c4d902c0b00c000c52042c0030160b410803a0241e040401440035052040131080c081020000404c4194500031f44075035000b064041e000c1d00300f4501941c0c084d00c0c002040c80981d1203010030320790000d0110810000c8400020b029026680340d9a46450b00964132502c0140400c041648444041640d200c1e4bc0710781d000c3d071005a030718114983c3c601450100c1881c0d41d100c03905000070001e10b081c2110303801004003e8030300e4820452542c4d9004080c0302c10059051682002003140c00000d010030407100300603000619000c048500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 335843866 1250 335842616 335842627
    0x90204230f040623190905130b010906051315060311160819020604050a030e01050403051501180b01081b040e0f07090906270209130b040b01020601051302 68
    0x1040e1400c070340966a4000c0c1840d0001c5070400c6180986034829941003003498580480904000d10858100340702d0b10000e654403000c00c01401c640d00642c4d00151042190b03511300c40d181e290607580c110260400503003141c54100030029414520140c100b40005000c042050040c4684058140c0c0d10a100e21401c068807114400194807800381251107031864403070002d100180c0d0b45040300041c0c0000500405020180f82c00480142c004035405114561000141c001d0700956542a20402c02a02003141082001c2c40302100261080258404500c642c0018126942c900551480d0404851901d4400031f0706001c0c0c00c80b013591700031004a801c6032131041140c03104110700004810307500a980c00599a1b006481c14050040c02505845005180641da142c20881d1929045c4058030079a1080d00b044c000350042c0c441030409088030200d600b900403500586849411000100313280d204034459820300707548405012030f42c502440707407440681013030016006542c5403400040082c01c210a40c078034480e400040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 335845116 1250 335843866 335843869
    0x20712080724180c09021303170d0501031110030c0203160f0b0705030a061401080a0c090824150a26060f0a1a0f1c0c0603051009020423 60
    0x81070352100041d2101001038501d604403201010f04654810b460840c0c110b100482c80034014000c40d1140c01500d00f80106852071955462414803260380780d03d1604c001071080c0144c2491038042c040c0214010160903d0b60b0b000d80b070410441c03000c000b409105244c6081c40031900300e6008001d4030741048040300c919148103600e052802c00c140f05420010082602c11081240c400d4024000d50300840c40003200f04202a110180da0b58840b10622030f00340440e441c1c000140d00d980854000702500c5000d4940218296500c3c2882d51030080f01c41e0300d0507460240e190408100c3d500040089a000c00c06030344c0030f502981441c0200d194817100d030141c202d01e154013003500004a13581d864620750b40500729080b1055807514a4603c000344909490f5444040c1c108444502c11550b01645050801c000070700002c02e55112808001d009003069071034040c0a00d05202356404a9400c021650041c0002e44010031545001c0134030f185c2c0c00a00340c11280d00c1f1f62043c0010311002d58460411a5540c0305110b0f28220b810781c500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 335846366 1250 335845116 335845163
    0x180c031c181208040f0b04030206030a0c0c0f11010e040b09070503060307170105010f05060c1e070b03040f031b0c030204020307030605030a03090e150108040204200d0b010207120807 80
    0x20403069030112890002d904203d6143e00600480b94040402c0f0700d001d8907980300000511840c440a90301000a0002c01c00301815507011b000441d0490400c490b40501503640c46200e24880c0c5810781d0800d03008880843c540d40c128800d9080329008a07010001402107100040e8601000703000d6000b00040400080c580c0d03141008810050503400501c109807946100509018100901688021078680e140004072420541e0a6071003818400016181d2091841007a403640e0008203003283e4903214400e40001c18000590046000c1c6000e01c0d10a078204a4604026110051104d50500d21072004000c0700c001c90304048005058941c110380140e602d03229048200c010b0245074010f00c0c0d05d8001c07a1241c10826400c9010740e012116884152032890b075072040c000d8000348594051501145114002800500d0243e2000041007002c00c4010400103440d422943ca030780100800144040da50300d0114200d60301041800d0003000b0500302c0c0440410190745840d028020340500a2044211000c1da40300b03507a541 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 335847616 1250 335846366 335846369
    0x6091c11030a110a0617070c0501320906090a06020304020105040f08101505060a0507171b0601080303010308071b05091f080313050114040b03180c031c18 68
    0x8040341d503015618107060410f2643c1e10200d07440b6602138071300010102d005072814102e0800c0c00d1492001c51303071402825154400c00d4074044a06540c0c500c1c1c90040e0009550038601d20152140d501210000320301000d40203150081c110329801d50001c01044911100007440704069644900301607101d0f129440147c41c0350040b070f0000d10180c080000041048000020355803e1501600014089588100c500401c4a107641c042c03640c20032402c104140d03c00b8001c00050003900d00c0340f100803807506248221900f07590440c5481000b50040081d0058030800104151805000014051459540b442c3e444514611030704400802e00d1080494140c05620f1000d2440003c1c600070305614801e140410f260104da0082035804106a01c81000100741c03040000140c40d20032070340c0494009400e0504005644802c0711036180240500c2c1048041076118003070020354040c6030b00095007090300e9030301a8002d003010100259140a13501015a811091302540302d00d1021000c54207044080ea80b10a0000413600d485 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 335848866 1250 335847616 335847619
    0x6060323042402070312050a0516050a1103040e1f062a050a0b070f180501030e072c011211060c071205060103020f030a0302030301060e060702030f010e0c06091c11 72
    0x116000e0217168000c4211400701e801a0307000c00c903998030007440c04100c410603a5000018081d00350b560741c101c0d0140e001084421a54240041c16441000e0b856141d580140c0041c0c58140b203103814400800710004800741500608503401030010708112006055650140c1180044044503c501c203030803201304410069540c00100341d820307070b01c600e041c01000c64000382c0d1404005950002003c400300e204403805440c281c20003228149045c0b42200440c00341c42903544440b0140074550001400ca9003001c1400700c1d0590010000d00f40505020480c0750210050303006503e001c050450b441c00185081c0c40b0782005120884035180c903030500401d99450040b13190810f044038010045010300f84400040c00c24105c03442101c03c0300c1a840b6803824103403500703e8414000d000d03134024001071002c00c2c0501c8580c020908090401405c1001c15000245010351905120380305941d210881a568101801a91000c00060364010302c1c040741d0710013150400800001c0211801412860b070001c0010300200c1d40c440d00d10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 335850116 1250 335848866 335848871
    0x51009020f1801030311010c020c0405040203190302060103060c1718070b040b1c020a02030f090409020604030614060418060b041503150f0b10031d030c01060603230424 74
    0x202c0d19034140500213000c1603004c00d03000d0800050b48501409844110006540a08180ca220809202c007511001e4012a4180140d2889480c510a008154610b40b8002c0d0b006028551540c14044200c4134076030713070078070030803440841e005ca600180714215a001a000c003011540c0c0501400e0b81801e1441c6a08010200500000e0000e00106244042c0c0305099450500000c20f01c1c91008100491003082504800740c0c0051141d041d05034510070203003110180242020031f0240f03540d800a5071507070160300211842039031818444040d114404160f54043d0041d07030104040c0c2d04504402800056030300f00107014584800346040030391101d42020350060501c0081049058484ca00300d504500d45119043c41c8900e0f0070a140701c40300740b500580c1c1e4403100243c2180c00080e01a102203003d803251000c07698803003860707980d42014000c0400c0240450740d81c003000041c007a03090900040035940b05040c3c10794000e03c50314140000700628a9a9070b0071a074070100820340c005014850f400204980300003a0310640c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 335851366 1250 335850116 335850139
    0x1308030c0c150c1f02070204060e090d03060e1305330f0c030118021614010b010908070605031f080c040506010302160305090607050106120c05010c051009020f 70
    0x124001800702105004542104501d40c0c20003429400f4054010004403a41c03058940c1d5401082d802007014264000640c00340c075040305a0042400d80e80d103580304000a13114401040180f400500002922449070326080c40554505a01d0109000740a400b81c1d503200c030b04840b000d04000081107510b45014130b1500f4800000c204403141c1d4103c6103581a1985482c4101c40060410a110f81070300d440790b0240113240d400e44c0d080002c4610748000c000412644280d0800c02c00c00d440d59010313588404144580407a0310211580c42405095031074803105181400100102801032400100b00d80d415503019161031a22582e0720100320400c1f04d07001d0300303c0842d03180d0240085100e50300480c2c0c0202020064906011a440c0c0e60011000c1f44507990000d0401c41d480500000020f00c2400100004403005045500f03003000790300c8150849031350744d015409003080c00b803030b8070200042d203080d104c01800300342020100041241c03155500c1c0c0c1c9210b090450540da9401d032240031581d4080c856491740a02408500d03421 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 335852616 1250 335851366 335851387
    0x8030c04090617070e09060c09010c08030f0109061508180a0f06091716020d050c040f0525050301120c03140f070503030c0c01081902120f070305010e0c130803 70
    0x10a503180c81c1d00e018040e009010174a0380c13401c583c25004111580c01064581d403010146074032a040345141320f04100c00d2848603030200b40030f90007070750181c0c8019004207000d524121208088550b0707075221140c0360707010040090400f50000b010540c0b1440b20760300160311031901580981003680c001001040700b48070481c528148400380c0d1003066041d2180300d081100e0f60150078100800e0281da048809107104c150001401403c020b04003038501c6104400301c1e0b1001c030b0307000002001d43d0750305000c842c1c4442e911410403e401c1e07240724045003030012118140b0100e815421004000348014098001c5040c8070610800402568811030342c011604406205e00010320307902c00580b54070b402412000b00e0300c02c030711380032074035280200464074488031160044c40560000b10044d610780200400c81c1d01c02d21501449640d0b206d040d40002c001410030402c0c118081d1400030510750703184d4405015902058900303001801400a83ea501c150094158202c4507100e012906291072507080d99001001710307010115400699 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 335853866 1250 335852616 335852639
    0xb0307020c150d0e1e0d0810050f060a110102270f09040209091011030108011427070308040609180b180c09030a0507050f0d120c02030f060c0a03060b07020d08030c040906 75
    0x8980c1c945e0b581c0703c1512a401c0e0100d00031003501030503912201c95502b00209152003c018018007801c0e080111104c41040006804c9800002800c0a031045104440c1d00c042e900c0c01031152040c3c07044442940a548080124a0742c1c10021f000038020580d0b103021461034142006140100c41000d00144042c04600b4208101c41e0003e100d00c0541d03608040c0784d114a0720800541a11031070501c03042c403250102c01d040718181807401624116990003200310100109080305c0081000c1c00094450101032460300c1c18221180e044443c107040340c1481c082c0203c000c4e82d54001c41c0407054440c1c03112807a013a01d849125440e40d01c00c000503144c1c140301c0c40428104005d40440d000044800440308200b481d1070041c01d21103e5400b401d80102100c00d440311469001e400707039407000e00e10341c000740803202142c1542211520348241620504a01d0b440451407030091350303050003031401070109661014208403856020501001d001c01700107001d0140480000c04642080094800401c42c101c4c00f0b0144980d205040d402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 335855116 1250 335853866 335853883
    0xc07090204031a0f040206130e040602040e0106081b0304060f0203040501060509071107031209050307030b091209010e1003021e21040203071502030d060b0307020c150d0e1e 76
    0x1d055004982544902e10701e0f50310305105007500c0d0094410f0790703074540c2040351541c031601d9488024541188041240c04144030410711540c460400103130b4803802c12004580d10b01050380b060007005601e030308010401801c14207450410700d08030000d640ba500d0314600040a00859a141020144088100010702005400640445006482d841c0300c03600d03040e50464955408a010341071651151100b000001c6200d0101104400e051030306106031512440041d05082d00c0e41e0054443d00283d01c14041c42d94024440c0500500001d441146404071381800a8465041c8075403040c45100105401d0300c5a5000c0e070100e0f9112105510f100600c100c0c1701c002d40000390001c8203500c0a40005004402c480010713403016501694005000b002d281c0d103441d00c400d00010559030304a086000500040c141d408190040301c020b440070560060312842c0103800240b82c5560341c040a8403031400840c0b1030a004a18104503035284c3c2c44103001040519820015a00d4071580500044501c0720038000b42d400404082521075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 335856366 1250 335855116 335855123
    0x415110a08100b1803010e0604030c060513230a020406121506030209010b1b01020712020c0114042d0806040b1f090906090b190606030e0705060a050c0709020403 71
    0x2141c41e1610844011030103014000c40c243c426003081003a541da41000304d41d040c4d5100084c000300300041c4410303d59007055001e843c114041459070030040c0800200d40145035115019250083d00901c2588a00c5024204154260844a070f0540340181443c000c1c0002143c0f0380d0050018040540e50700c0d510154802c0108043c3c07010800b0840e001004246d0340075140031a90010046101d9909044a80c00d89a1154044584a10740749480c0010080280090206940a6940c4142030303a080c0c08045c1c1440c030340541041c1002103409144030280d050030140d8090f220703100c9140056101d100400700d0b074000140781010140704207103000140ca050004400d0320851241054068640342c414000c08582000c402e8105540041e03a414070040340f10754044a0b44038060280464040e00702e4444880408046d102a01d110350301040c865020b03101802500018940c038a001c00004858074070450321100180611441590000f4424114500c6030b8155100d0f04422030564600bd5079a504600082d40301d84801c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 335857616 1250 335856366 335856377
    0x612040213091e06231602070b090603070c1709010906020309010f0e0a0305031306030b12060106030c0c0f030801080f03090904110a0b030702070302030c060930030711041b050f030415110a 83
    0x4000d0144049078401c1100d022001240c140050240bc0008542000b803c402c00c219241c2e080d600829991400300020b19101e4080590b0351443c40c0004003da00140c01400555004000c10100380e6440700b105014043c85140201407010f5240020b425070009a10152141c400451010884d18400f88100704803943c6481c10800c0704040400c4c000303004035445200040c3c3e00054010000c3c0b50181c1c0000c51038030007907c4d2112144c000c0d60343d0381c5064003030848144c00040145006200e80101006420918404540198100900c600008105a200500c0100a080007003000d00381a215103585802500d100585036440e894030640003592140d1512081c0d03c68401d901c1c40102c941001001ca4820f081c0103401450306850071060440b01c0c140100781c0804600c900d000303201070120301340041d00303920388189060310b41c0c405443c0402c000e03542054007070f41c2154a04510144c0c0950000b040724a40701c072540340030340caaa40301c0c1070402c0710300d000c1d085c50f00d00503041402041111704080d005020302645074540d13 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 335858866 1250 335857616 335857651
    0x20304140a03030807230f070203070e06030703032304270c09050d0203070e0a1d030f1204030306050301090f0201260c07110612040213091e0623 64
    0x100280320710944406004035609001298190740b05001100c0c00e45400f6000d00781803600300740350300015445900d110000c0f06c00070a1100862500b4412203006101100b0005558246240000c2c0c5a403107a00c4010b0a002e0b0703601121050700256804031008010020300b0545460341d840303007404502c2052403a803d014001c03480e6080e80560f0392050041c4035072255034a824090601040c030982e00500003040c3e9042c441d80320006089108126664807900340500080303840100300303000f01c0310441c0d5004181c181d6001809082d0300c0145c4003090b540d5000c3e6220700545252214102603008024a07000240c041d401e114925040c4a405106c801807140700fa40c2c0c0070000700d540c900945880707544d644070256444050700400c001e1084800030b0310080e80146030b004c84031240c581c00111240e10150034904400e540c0d004000a41c070341001e14518010200c8001e00c18400c190f0303584041c02ca4038181142401641048503000d01000b50b01032080359020140381c0706070030111440300c2c41d070000860f103208201100c5440d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 335860116 1250 335858866 335858869
    0x601080105071704141605100219060b0a080a060902090645100504150b030406020d09050d030b030c0a080a170909010902070b0703060501080a0b0604090c02030414 72
    0xd264030400e52680c412210007004010f0381c59000d805041610101d0542001c03115407141840403540c080107002544102c0740c035200030300102c9000395001d4002d540110209004181d285618012996440039001903640721000020300d4100700d0350450303201032280d03694480c20445160b02c0780109900856804803d03581d24003c000245065004515000b191814030b0340850800e10205140380003480d40500300f4042e400600100c00508568407030426207050010000d6007070511866902d07190100f000710741315042c41403840c1c0c14800503100614507a8009a4403400c4280c5a20030b8440d81e0f0300c0700c1910510b21011100401504e41207203168070a016880c07107910b0920344824001d0440d451003001c0d0031100c1068490200c40003010004400c2c03c802001640480d5032601000340c040d0014250068688520b820325000781030707009024130140740c0350400030b0044d0380c2c11440d4154450404480400e41c0101c0b2004503a242c010303170303010300f1a01d8105103524109507008800f500645c0c01d61500349509403d80c10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 335861366 1250 335860116 335860121
    0x201170709153b131b091401030c0503220b010305010c0909020903120c0c1009030302241501030f050705041a310503070f03030816021e1501080a02010206010801 71
    0x90043c1907008050320714810b40d08108000d568140442500000c1e09808a01400d284a08901309100081e4010b5005d00081c0c6440852501100007031034100a0309902c110003400d144409000e9440e04081544801901d0101108030915180e02145203102d40d40c1d2440c01c2d5000e00400800c3c02c01080c0601c07030100301400b1610968910b1040103000f07041040402401c51101d81c4241501c2d0b4860044d02c46529143d22201a034020b140c00650751000c10a01d1810001d09180342d8100c80305244d81a10030800607100540704c880c2c2c20030300314001612941c200f0310059009003101c0103442c2e080d030305000030486245c0d0080060300499a2807918091a003420104140b2107104d0710101124100460208995042801203043e038074846a03800300425036182e0000178602601a40040c08206002400b03108050340501120b82020180e10190344410010300c002c0d40b04c039421020b281e84c1104500e20048220740030032244c002500b04945400882d40c40326a00d988418004600364050700c0342c8400000d003100c052 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 335862616 1250 335861366 335861447
    0x20405042d1e05011202010f0c0209040305030c1903052d040b0912070f121107061805150a090b120402190305031b0609030403020117070915 62
    0x1c01c1850064001c004154008205406007a40720b800c2c903000407401000e00740f0401e4080c044440c041ca101c8081840014044194940c03800100030100c00d0b0140142c5038035140c00d030403030740c9405e0154a0380c0c2c881300c00242c5d5004001c8416400c800c1c5690707a200041d010303441a40600f4014207081d064040c180030300c00e045810496201c0e608882240043c022070b81d020000da411584c0d9500340c600c2420b9500340c03440150441442507840007808440741c0308102c1800c00e09103040c00c5504020200310940a091615403c8610030207040c005070459000d43c5001340822840030340300050031a481d01c0e008049000d143d400160a40c0003086100b000401c801d0002c005881e0070483d000001c0c0059941da40c2071002100c420400b00c50200f42006011000030f8007400134060f00710848500010040c40305a0841c503064024241c000036400030407003813000d80d901c00c142446da0b4400803140059500d58610407691419580d214140700071410300116001588200e103980d90007043e842201c4000a1200740601e000c005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 335863866 1250 335862616 335862671
    0x302010e0111071e05060d0c1b080306010c05010f060e06090709081009030302041d0a14090d0309050c06040e090f2802130e030a02060f07050a14160602040504 70
    0x202c0e00030480742c0340b81c80d8a034464000b0389204c00f00b6559584085500303600101c10180da41d540340e0008e80042d0b5400138500440c01e410b0342c44241100400d4035010218400a407040d81080034586150040c4102504a10140c20a010b0308009123035940082e007154070f01c20b070f540b140301d5040300b00170a054920405050f8181c17034417000a06008415001000b00506c40c1c18400c07000d0640034800002c00b00d001e017908805410100c10725060900d0104040b83c111076541003042e41c00c3c880402400104140011085051300403424001400000c6090182c50070401c800415445000004d021401c0d0020529241c0110440000c42c0c200d6605101695203c51101661b44122440c4942c1106150424583c6145590000d00301029442181580c5000c2e10078850140c0420381c400504e4103489a81040b059510ae141116080300d281070810004219101d500b00200805c91704a0861106000f00d0080303843c01c2c140b100700c01d02c10a40519082020350018801e00b03100d24902040c8402c151400764011060050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 335865116 1250 335863866 335863873
    0x6010206130309030c0605030a0f090c050415080a0f0c120330050108010209120102040f0332100b100915050c191e0c0605070f0204050a060302010e0111 67
    0x110700c68403150351080340720306404026901d000000802c030120225070182000d6a40d036503403460002409406d56041c2140c0c116060725102c003000c00300302040c075090280e8004490104030450101c0811440c08070a801440c80c60003142c5c2d406040145002031030101902c2217032454810340c1d42c1e0000300d000d480c50a1014005c90b00c80c1d411b8170220b420000d41d802885400740c2030041c165000761a20012104240c10040c040e070b5002844800d946071001c0c0c52440612180000c3d85804d0070088011200c1515200040242098100201a4501e4640c0300b91115106407003052480e254a88407603651039081010480b0607147c50038080c0c2e941845002d50700c0001c869117443e1800ca00e00041119240f084001e254100a401e10103039142e0b20045c4000401f040603200c13400d0441003282445006610759a030041940104c0b10300041c001254400301e6812180305040c000c0d10780425080c00c8155080c0104c009500a1030403080200c603481e42c2e41300d102074038000c0c0c0e100c40d03500c0344000041d00c400d500c000e00b400d134990 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 335866366 1250 335865116 335865121
    0x90c180513051504080c15041704050f120c06070f0c06030c050901080a06080a03022505010c03080606070c0305150703180609020a050301060602030307030f0b0f0603060f09180f01020306010206 85
    0xf20700a03856500070303114119051610846240143c2050139048001049580d913409000c184845210120682c04a51060900e018900000240a484c00c502010302400c0c511502800c01030061101c0e01000c98040c18480c0e550516251540c1c090986410448460000c1c902c00f141d614403900c43c280c54603050b40c842c2454480740c000155403181d0000c01c502c1070952142030109042c0c20a010078001c09101c0d40080c8400f100c901040428038401c2468000151a400020042a0380c40711000400c2901805c0c0980f503138841c4404101030b48079200003e4060690144000204200000d86650014005d14102d540351102101241940d84401e40c5284e4031807000021401f04ad01d503840b01c60028401480c18020030303511400b02e42519034a60028001d6000401040100c1d9094014003404078032800c07080280486010002d035542103803a074240e0103600301000041d05515204070616450800801c032409a181c82c403080b205105a1100b03101d00790265040000760036105000f500c0c06000160040d050301c0c1d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 335867616 1250 335866366 335866393
    0x4030f03030b040920281701020405100c0302010c020109021e0310050a020903061303050a080702010f060e2706010512120406031406030d0e040f090c18051305 70
    0x50070788803110365105944c0c45204000590102c12545062803485200c1d070b000b4800390030400d13132a400d818140080092100c40b00c2a030380d120001d02080c0d032622804071988000000c0304500a001d1504955003148046004404054020701c0c100b404901c00ea0003489901000b0808a007070340d0b01843c00a4004154060260310469141500106502d000d0300315401925800ca4003c1601c005035142940c035940040c208400c1e080070f10503154841703e112000d500850503541e0040551041d07002b00e00420900740017040945100390801184c45140c0841804069168015402286c8040d5080183c0392041c400481101c803000c0c0001511b85440d8000c1c243c0d40e80f07402d05010225811030004102402103600e0724024201c1a0302a101804055400240390007031300c03400141c00803020b00001d1003940042c9000c03007001d9110102e820003800994011800701d80002058003c1c0420b660010404a21044041540d0513018100c01a07400300050030302582c0c4690845407421001c07104040d205030050384505818 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 335868866 1250 335867616 335867621
    0x1505010b0a0206150315011221021002070606181b1d04051518010e06041a19090905010b1003020a050a140403080c0d0206181b030a051204170304030f0303 68
    0x4045c00742c0b00c101442c11640c81c04841d00f40c100500c28890403c030389091102c2e85490005c0f069800800181e04041c84602031742e25042c007001e0300501d540000e2800700700552030708004014040d0405e00d9075212826203600307001c0c1c10005400c50003c1040c0350f1a0100d10710504241d261480303003000d445048140c0206210140000810215445040106c00041510b0343d0100c81016156a19032000d00e5040050060007a08080e0a0920a5007002d580d40e402214801d400102c11a04480a80d01010822014400040e0035030010030b14514040a210901c50190030951410301d0440d0441000c1c03840303006c290100d0044403046400280c0600800c601c250081060500440800042c02c1c10180d803070ba95901150321201c0391140c40d07000503020040c0c2c1601007210a80003d02c140c00030340003400c03007552680d0b22220f024191805045d8054003016589040c01045141900101079442010f0807012080c4260300503c43da00c0b8a0214014007030344504040161000c4d46e86c094084001c0140e992000c401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 335870116 1250 335868866 335868901
    0xb09060c09060c0732011706040c0c021005040608060d0803011e120812070c02062d071a07031a01080612070608061305010308120718031505010b0a0206 67
    0x504c202e010201d0034401d45000030900d03a0590082d00c11607211704d41030a0340c80308182c19041c1404821032002403107040345a02e19a0080d000d640004115070038500c11a20030400c484007075080540c050b0400207a9070f10000030005d40310b06440d110207940b6003a0071b2100e2508102005040c02409100503c0040c0300340b01c80c016000d007510b101f40c40b903039100d9411510760800c1003402c8490070000908800c40503031040c41c155010310641801c0e030410280d6000710b41139100b8016078540c60f0100c11000340039a4a8980c0c0c20f6036071340c202e52603143c483e10246081101080041c186a1422142c0000907840034868050080341040b868070b0260314541d00310054402d40b0000c1c0150307030300034a0050045000e14003002005d004140581d21846241004418825090b22107060240020700740b40041c0007044104044804068907140c014403184c1d90b407101101e00c034851400d00c0d0f0005c00200800011311134000305009050081d42800c04c0030741d80c3c424040035644100400034001d60170490015904401c45d810020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 335871366 1250 335870116 335870137
    0x120e030313141c02070905090a120e0415080102070201081b070b04080910030609050c0708120604091a0a0506010302042904181a010e0102150406180f0b09060c0906 72
    0x3071400046882800c4003280d40e40790f040c01030b40014006c0014000c24010a46c1210510010b42421f05058a941d8589901040d04a09009801c5c40e10324080d110340c3d1000c401c41848411045440d0303190b09840e4040c0d84401400e9000565000121300218919005480c508145400561400080e6503c070902d070000200283c814400034800c10384291503030341003c2c10182413940c0004280f0305080e810310444070080e18409055509020000000350000c044900445031204400160350750a070000b4081d15604000409140c401c00c040c03120f45480000c1c01d800762000f01824005035035900011412400f50340b0030307100c400e074801086032a24400400500c0c07911025004030340c034168450484039440c4d020b030310414002c2035440d039403000d00c3c07200f07681d20220840302440c0c0f145811100400003580c900c010701c0e0007002c4510b4000400d0070410f00f41e1101985401c001d504950b500f0090030040741541d45180e06840703001e070807000a1f460030000b0030b9a40c0706214403091b07981040d0852080c4003403074000d101c005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 335872616 1250 335871366 335871373
    0x601170a0c05120c19020d020a03051b0708030d061409060d0201031b0f1e1707020f15041103070303021e0102040e0408130e07020d0c031806120e03031314 68
    0x100f110051034080b403240588101241d80c0760034450300a040f82c3d5000c881c440454101081c5528140d501107020905140c141c940701d5240d11540c04100355500c0c600010039224868283d00150001d4040042c04149501440412030346030750350940c11030103814051140d4851900000603195143c1b005600318035900601d40020101c0401038084031141c6c02a00d4140460041b861500300154030030744005506000766109004248410302c0606a8003240c0103403e20301a5000000e1a01482003009051740030102007261840c0610001b110310804050301d003540c448003804240c1c0c40d12704000407100120303585075000b043c0c5000f6182d6420101640044600b04554007000006040e52452110a00641c042e8840555a01c06034101a500000d19480f1642415104080002c00360300460324280002d840d06002e0901078241c0f40031603180110b0411070000302c0d140307c00801c040764466410030147c2c1d900b12007080480d001800d0aa17490008980b200751701c1a84000362070000e00340d62091210b04c0c0c0c03003000302d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 335873866 1250 335872616 335872627
    0x606011e0c0b0a050a060506190e031207080a0e010c050709050c130305010515010809060f0a020d020a030506120a05100e0a050d05030403090906030203030a27060e090601170a0c05 79
    0x20a10303094001c3d244070301c0407920780040c06545030781d40c03069000412045680d5490300700004008011002c2008090b014443c1d007c03061a0a82c034240582c0940400e0b442d00c8668807132030391500206640000858200140c088645176049500810040c988950000010a42c1d05d103048041c8000c1d0400612a00d000039043c4541d00d0101e03400e94084c400b0790721510011903a86045d09540e2203980c8940041c6040003880000e10030469008644039030000d642030016055030b0307220701440f8042c1c0716a005908803503100084100d4070b264103502c1980290011039807041d269005a1166540318919007000c0e00079003141c40312000c000125480302101c42420350540354054219207446007000c610a042da00411000000c1208044d03211014038043d2070b103850208401d90031a0042642e0b4001c0340d25000510010701101c1c001180c0d80021072141e802e010b68090390288d11a0300080c40c82514440300c40c081c2c0c188001050156005100d8403074400b074030214201c11541c035111910040c29103224a0030900404201 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 335875116 1250 335873866 335873873
    0xc06080c0408101508160e0a111903110c0f060708010f05010809010605090903120901060b0403081602100903150e190c030f03031409120f0c01060e0103060504050d020606011e0c 78
    0x22860021b1803010030160031030704d042a0404061001080e5007642890071144042c140da59409841800040c000201c00c50090384905400074050440c9988082c0804110781081c00d600190180341c0e45017180565203940c4032034005a5040307000380240040100410710602055205000300740d4080c004800103d1031582c0d80e80400d1800400f40c401e40c40366000060507602e40810040e000317400040f0340f802000001e00d4402142c0484c0079500004015400001d01040907012184144800a80040090603080720b80314020300356031520b101c1141d206858a9082c000681180300f07030303c40110504d01510600c070b0304841038421011044804c44050302c00c131801101003243c03174400308552842901d001440007005041c0f0180c2c134000600d083c0c450761000c400364950396a058181d900040511000c2900c42030b074904000d000d40526008840007002481c000803c1c0318007900130a020358092801c1d40e0148084a0b0b0490b180c12040f1100c6001c6407001c1c2d9482002c0044499004040b88180b6242d880036030640da = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 335876366 1250 335875116 335875123
    0x40b0d0204021815040608280509061902130312170901050712050405070302040f06030212032d0405090a0b040c020a03080c04030b0c0a0c0206070c06080c0408101508 73
    0x852840110000034101d9000e0134100d03121109400000350150415140c01802401244010510004002c0c20818040d550308071503544444480300d8601400245024004d0565619080b0303480750310300624000c04000a042d6100321910a150018111010344c211b0b114610201e241b902c0c04c00c100038002c000a00b01c002100d0313006000d440c1c000004501424100d10040c60301c9280300380702ea0f07680d24200600000840001e0507000700c1e54191030104c0c4814030080000d00405080d800650403101000e408400c0c01c00120083c44220003043c0d0007002201c01c5400c140c034120401d403020240c00d1081000340081d1410b40701c240d500c400000d00100744000c00000bc0340542d868003580b400581d00594001d000c164108802e03550203010f1303240e8a4201803950f103a62031414800360541c6910900040d245c070308140704010303101180741c014284e6951812140b45c40301b2580002c0c442c1c0e41c0041c0d041e90101e400c0c4250003040380d044071000c0b001440b03900b00e488c2c080b800510300c005041c2c1500d0790100c0c0001d800903051 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 335877616 1250 335876366 335876377
    0xb040212060948060d09050102040e01120f0f02030705040603080a0807031b030207020d1b09050a02160312201305060c1f0f0504111002011505040b0d020402 69
    0x100082e294200b500414181c0c007180b103a00001001074542c402d0051211810b5500c1550183c0d4680e0030100e0002c600450403504c41c00d10910051400d113a02d135014072074150018401c40b1b8980503008002da9858034506940b034403100004101b811070311142000b18072180c07150003000740010103075145207542e000010101e070041d6108450030f44022441c004a5074201407901da01c9a102d01b800d205460f6400c00c0c0d40694000200f941050503400b03d10a4255100d842034001f2555015002d0040c00d6130010613035108070900c1c85400c0290707081000242e02c5040d81d000f60b80c00c24040c2c1101c120112200d179425504d414000000e0421a40d03200c03014134841d131411300c20001d4084002085503481403803209102e503001040d00040e009107000c02144920200010351844040e4010720441d0300d100a41005901070401044120130341c500f03210512080c00000c00b01c0644012040f102c2c0d42e40d4080c034405c00d90a80b03520046105c1c0390036110808010302e040070741103402484001490340c3c9100c2c090364001000c98010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 335878866 1250 335877616 335877631
    0x181506070f1203090308070f030603080d15080705010207030605090f0624040504080702010c38010608071706010c0503030f1b030c030a0f1107030309020424030b04021206 75
    0x120580c400d00440b4955000e400c0440e14041c0449485602c018000c0f00c0090421401c000001e841080e82c20700c264400401f542c0c1c803001c104d0b502d402c0c054070074024000811802c410200341100000d4401f400042d0081100c10603005848020320f107464150043c40b0003400b02020740541520340101c440107004484c071078500507a1908020782d000260349203140603405218041c40c648410b00001c58101d90a950803da42483c0401400e00585001d03420051044041074031044070702e000d8040b61441d04104040c5504c286417191580e80e071039030200c5241d007099500c60082014210b8000c056a44a9981c4d07a014906050400d000019590340c1c61440c5d000701e4104100402e4002408010707081602000c0aa1540102050442c108042c00c030380a0311014018030411230380c1e4070a01c03019201c180c000401c036000e841e503220f441d400075040107005031807880c2c0228451031903c45204503403400503801d2403a015521151104150843e0380d5503100d50300c080d000b17aa21014051410543c3d200801080d84034009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 335880116 1250 335878866 335878883
    0x607111507050105070f09051008010b0c0309030607091d2205031e0c10020a0206070c0f0b13030905010338060309100b09040206220314030a08090c18150607 69
    0x58090b00101780c108144c01203449031009c1c840c461580342e8020b0075607066601c2c940589540b6505801f0365880c6206004855070140100c00401c000c07240c220800030221409003145840013074a40703810441580781250010f00c81034040d075071030618940c901c1c0d01c1d00680c0d1040f400c40789041c10f100b1402466158011100c10402c50005c0d44031072814040c05000c103240c404110942c10040c2142c00651948801803080c0100804100d4410911610401d5084180e400084000850801188250b080340c091001500402d000300400601c0354868803401700d01c0c503410400c0684900115031820550002c460900302070500c134a02008882d6211401140140b11544c010040e401d102c881c05030540b8400003102c0e100381002420000940c40b11412121041d404401d0101540002a14004102c003aa00050605a0752740c08008041400100030542080a0b4880500d59070b5120112542c458042551642240030324405500c0011440c3caa07642000c4640d80021920b810b520201e000c542007444261032411 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 335881366 1250 335880116 335880137
    0x5060a080d021e031315181806050901050a0e040602130e0a05182a03060108010c0210050103110f060c0a11040e0a0f06020a050418050103020405071e08090c090901051005060711150705010507 84
    0x2301510813007000f8042a10f00000c15854100004c81c50311203441451035202c0c24000240400400d6412a5064800c240070003e00c56158541c28007072032030840310301911525000106031031440140e00c20740340e40c01140007080d00a104441d2050a251080e20030090403111a101c0d4000e40e400b40146030207003070584000224280c80201c001d141c00301d03070360180341c6092030103005001151898840c40102c55003502c0a03201440e94002080c1148215041a41140284d05018080280d408030181c80340400f00d8003070121a4080454540300e40060b03400402200001508400060854000e001d51221604220b420142d44206071421405142d07042011035546000510071032420f40b00e8160852032501d0803070010100e2503508440f400381d0900c180305201002001a008800802005d9501a00a02014003900b000c0d03d1f407a019110a4864802e00e0103034400c042018208501aa840242c000e001440d81c1a4500c082c03188084001d004450170312400c01c00600410000d003c2d080c002c43c1da5075140590301c0d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 335882616 1250 335881366 335881409
    0x60801110c01110a0507110f041a090702010c02030315030c1002030403051504020d0f060f09050109020f120d0c03120207050c0a1e060305060a080d021e03131518 71
    0x6410082c0f803100000d00600194000e10351010917512010b6010305403800b9030f9014000211142c0c19888041c0e80107040260041d000840b100482c0241076040e510003112351540c4800b17900b41d41c0d091803503c0c01a4010300c0001c1818908076940300c01c2800c00340c01c1d00d405900010115410180605801015900004040082001c104995034180030390100121031424141d0010f416480c0c00c103000340c6400c41e035104842c244041c40d4404420301c460150100821071440c81c000e400b030b00c1031600c140e22030a814810b507402402d0146040c0700e18181d010140140074603904c0705507062030104000b174007041490200811500f00c1c034401444000e004000414040301c406040000804642d080b100c40c3c03c685070a101c0003450400b6125060790024200030030700c0e540d14404070715601069172000915205481082c0c131556004214102d800205555001c0b10b6031502c058503680f803103070300c00454151004e007000304100c804030020580030200300e2130300484007007480d500c4961070700c801e07000246403540b42090700f5403e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 335883866 1250 335882616 335882621
    0x60412030203190306030f0b09070f1205060105040b01170405030c0604060902100e01050d0f0b1003050712090209070e010c32070b030f0705070605010b040f09051018060801110c01 79
    0x40004902c0d0601005d81107503103414050300c9095000301440085800b040c0c101070107100e110040c04032440d2600040e0b503a1849010610343d519025a01c5000700000400d00781400d0150082c064010f84810203004032410710b8008a0100030300035240c90009121011480105000450040c0d01605000c11201000d0040101049501800c40b0511140303001d004880d1742c00c0400c0e110714180c0000c0005140c90380b10700e98409400000b05207507000c0400320403401c855825911450284c1e42d04ea840d0038a00508401135000c42c0c02481004c4e41c040c80110018607811311900c41c90200c0c040624204500d50760540d94151043c00c0540280314240045914000c10b41c0c00203041e0300240c9111004044484c43e10a06006274407000e46055104001840082e01060048046800b21a80030800b04203039030755049681e03182e803c01d029203d0358001002d40010040702c0e600a050103065200c041400c8186030590140d100c81c411110340346103986946000a8045083c4260148000d510700840d40e20000c0d100b50908 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 335885116 1250 335883866 335883907
    0x30c030c0501020c0916020f0a060603050705060322020402040e1e070203070b04110f0306070305010f140916210204080607030c090b09031c02010f0b010906050904020702060412030203 81
    0x4542c08a40c080404d541c400e00400d411510340c029030150803a40300030407402c0c064440d9881c107862040241c40000c10844c2d5004400700d82c083d03804c2d1410f06450b9030409c145403005541c00b045500c482044082c10228040005460ba4801000146801c1c5d407031080e60a070358411109414400340c01000c0d684c4c10b00e21100c1c00d0f42c5c441440d20185203444104c1d640c2a030450005000602030989e501e1740c0300c80c2601c03110450301c5000002404c469035440d08200040151100b40a003010700403007100001003001500d03000c689950401001700e0150394503060700c1007225204005510801c40074011092100c500f86002c82081c2c0d00c00440965194281030809241c80d90141001e1b08141c90301c0058505240d11000c0907081d1085541840c2c2d0b510070445c0000c0c9480343e000180e0b001c046c00c641d41c038010190150f0010310045030180c0d0502c800080c1744019100d0445521800380816010050844640344c668014030f5280e1004254a052035194010303401320448000301200940d000146c00e03205402e101b80c6480 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 335886366 1250 335885116 335885119
    0x10c03050601050d050c12090a030906020606011d030a060e0a020a14151e12090c0108010b0406030b0109030503130303092909030309030109120314090d1103070c030c030c05 76
    0x601d040810000b80184200444040081d50312800729440c0300000e0704640c4143c0003550701d180c40b4101002d21903228503000504601160610708001a0203002203511403189505031030b45131920f03000001001e620310740780494550502465000340b00141461050910050141004116406075803041c0201c101c255000406100300c40d8100440d20f41d100328030038401c100700c481110341780c2202040c900007108046581c007000207004140703440205030040349540b090074030340d0032140614060001075452800078040e088040c3c00030131007804000c4c0250400291800189400310300706940e0349520741180c020300c5c0d03664032030306601d1810010715034400d64080280106410501214000303074001241e881c1c003c80302a003515800b04210320300f65001d02c1a00c801b480702034000d104c114200c1c6444108403802c922810040380c901031900100d8001441d46610a042150041c40610003451003a646180129008019444100b0807003000501ca4054100290720800b5848552800e6240000310101184c000d03e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 335887616 1250 335886366 335886371
    0xa0f060e251a090303073507021c0201020a060c17100f0501090807030204050c070203030a090e0a091a0604090c0609060314130b0a0e070620060103020d06020d0f0f0b03010c03 77
    0xd0040d13903030100803655980d9000f40001c1504030502c4035444020b000b040c817034806e034440041801c007025102c002000c416208035215004184031405400d00700000e484082d00690000703041340001001584002e000314001d08100300740c4120000500744441086840042482d82c51004120103840c20040340e0250009090141000b400d106000d6565411444060301c038075204d00c0400e0b5002412401c803420583c005d400e4030780e05c8000c41409401100c0f503100c3c0140c0e080000d0001154600c2500c10500340c280d0003503440d200f0100024080c1031901e005403005074041c0d5101c590b40d00240144490200404840d19030720039281c82d0001c050708031182020600e01d1030540b0703020000240440007454162581c01608100b043d107e59a000c001009881458003a0b07119104001ca4015044440c20600700e1f102d007103000e0380b82c0072543e04031b4540d03a0a2200940010560320010001000b607005001010701b07044001a000000440e060240c0e9140040f002c5003d80d00c07411499280dd007806400500102410305 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 335888866 1250 335887616 335887627
    0xb030304080a11010302040b0a03150b0c0c060319050403090e090109030918110d0b0901231221030a0e010c09060c050a050102070b16020a0f060e251a 66
    0x41d80c54001c0c414009100c00c000c1c400d8400b0980c044d605039400792a0025443d80c5901030008081c0003010040c2a00c006190b02520000e69401010300321000000c042014040601e50b1005000803900064500340c080c023015003170401141c00318807a40e40702d2030080d90790140c024540340f40007807401da002d014002c45905007006000400e0300003800908035414203040c3c85c1800100c01c1941c0c001c0048028600040c000001d955851036140e0b0411040000f04480816403a43e0b038020400c3e54216001030441c00b50940d0701003045510b858214019002c040b078040c7d0b0750100c60b2920704140b15901c106140b2500002005210002040b442442d01c201800d1000b00301100002d21301402030003261042104000414846e0380400400344204144980c0c400c0081d5220b500030318005400400c1142c05950720406c2e808516801c91001600d500c009070040f44c0c16500c24001d4881c6009002180e0b9801500d10820310f4036900607413040b0301d80310f4070804202500d04090526425070444e9507001c1c84807515042c24001c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 335890116 1250 335888866 335888879
    0x140c070b1308070c0902090f011d061e0a02030d0b0f030c100513081011040e010b0d0924060602011a041505030a03032301032f030a030905040b030304 66
    0xc4140c0c0180c444280c007140c0800a00d030a9050340710b8804021301111102800090f00850380d005072902000449014070401040d100444808008107a0300440c0c0d03070041c10107130107418010002e00801b1500d02c0507491841150a144880340e002d0769041d4010703030001aa4611a0303000303114003d00008222203036242e211a0a00003507030341c1041c59409101d0f1046501c00b019030340c051004c41c0c2c00c40e10a0980d001405544440c5151a11f0a109820401d9414410a01244840c103401c441c01d55003a210b624820764204a410801c542143c082d40c81c4144d030f2901c240011a0300f88c1d8808148036203024500700d8002c034205031441900c4090b400441560306240c4184601d8480550604a6050a4a00198026181900c0300c0f05240d40e5202c282c1600880044006159068002e0f035124111140c44044100040d40000010002440003a085a2608221040383c600031154040000508180d00b032040f4a10f000081c1400e0a42c8000c4000c541c990b03e04003c5401c00d8060081403450413009903007803914151 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 335891366 1250 335890116 335890133
    0xb0604020f07060c0e100309110105030f0117100e0c0a090605010e010509030304030605040507030308100b09130b09010609030c0e0403020d180f0303080702010510081c030f090501140c07 82
    0x10b00040c10f00c0c1d02c42c41000c1c0707003034880c6141150581000340070f105581501c50001c2d004011800040c0c492082c10b002c14181c55004508403406009804030700d100685c03804c0e040644599084100241d280584c40720301224003568000c0301601000d80000e0800c032070b25501041010003955100c458031340d00b000d4040045e6a0040280042100700b820816030314100d460009003184119000145080d00e07000a01c011320800140301d07000d8070b10a4480341420703260b900c4c0c8000d0180d50791049141400003000328003558200702000480310762801c400894034010003000554142002d8100306d001401c0c0e075504005002c0100085d070018140903503000628107103924000e4071906845800c8080c001c034807a00d12050444404200c0080a42c0444200300320303105c3c0b40041202c20241c0302403005600b40804186905403452030507048030b400384028a10440708040c45480c158006944130306069441d03004140790340311402040f41140c8510300004075000c2c503464900c85488041d0095914990502841c4d0001c0c8600 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 335892616 1250 335891366 335891377
    0xb031501050d020609150c160e072006090d020d0c02090106030921050310140a230603100303140406140904020d02130305011a0a03060c1e0207030b0604020f 69
    0x5640700c94100c02540003050b124807413030300300d55080f0083d140c6020300e9030803001c0a0220191500180e45200308c44547d8001480c07a18000c0706c601107450004140301900075001c1c0400100340c00c40c02200101c001320a6030900c2d8044504181d070b038028a032540030056043c4a1040304050301c0c02c015504200640109a074403005000b4a014160340e2041c2c5001e200500d8108441400309071082d08480e8003049000340150400d40e000350b080d03900d60b20080340003006480384403168200501904240c42c41c11000d038141c40b02180c0340f9841240701e010021007a442c0c41006600c94804103071105101c603c0c51078010f1545600e0134102200d60740502c070a100c0385901400030124903d8421140741c4540c03a500000380248906c80c44040760510000c1c0d804408000c88028800322030165001b0046d4900c0c45401070140d2405211407580f050752108207100240c20395003c2203905d00140360401d0341d00841000c004880140c3d0f491540543d114401c00c00410181800095005400f40c0e030560030310140340d00c101c1050040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 335893866 1250 335892616 335892619
    0x30e0f161509050603062103070b060604080a061509110301030c0e090304090908041d09121e0c071e1e0b16050c04051305070918030f020c0d06020d0b03150105 70
    0x400f040705030b91001092113034183e03c82442405000d51031f01043e40c075440117104854644218001444618183c020365048074641c4001c0c0188140c0c80c0d803400c000f81020100000c0007000c20501041d800c50034070640c0c1d26040c810200c20750329411401c281a06da01c580d4041c84108101d6420030002020200544d800c407141d449010404450b2440c050741c03507020f0390b013101c148170f88800b00403203140e107040312042e000d8902c81d0141c80790104040350722aa20b01c21028801501c1e043d0740e4001410011190080c845031091806031025903485401c8e0a0705c0c64001504015085451841444802e42103000c0402d9440340342240903146142441d840658040c0064003c0c403500070304980001c1c070205008810714540010810011880c008840321000c0c0a004421b803001c1c0b295aa021031001281d100b01042c508003100042c0c44a0959642164540090b100017401c5020f110455410350300d4004044450521a20015880c0c10142d02c06031304403014004818400ea1240805a152100048244d07054450 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 335895116 1250 335893866 335893879
    0x519021507050708011419050103050c010c051e0606030d110d050f09120f121321080a031a090f07050a030b0d08030f0c030103080d020307030e0f16150905 68
    0x8942c18460b040c501c59a00c6225654200440011100301220303c461040c0c1e82c02035484c1c416490040c29600311082400010300030f07480380095540640c041c030400041a807248044a2491650303561141d2554520018490603a11900610500d03150500281c0d203000c00340c1ca07010040d101d00c040720075940d909201100c0c040c050b001400400788850702c0d044412191000d08454070b80303401690210390790351014049480d00e000e89010a941c00e2a00003c5598a140303005510106c1410400c0001c02807406450700c55100d55002c0a1100181e84807001d49600c4082d500c002030042d6034401c42121802c6035240c03440c4107103400b01c00c20121a520403100fa8200f001c44c984192140c00140c815001060840d00b41c1d58000146000841040000700c004c41c444c905503065800c0d5511400c1d02035402d408203000040c001a02440b02e07600050541e0f000d564059007903e400300b45580c0c0c41c0903440c10a440102008442d4106030b940201190300e4034100001082c091811034102c41d060315004200729035a0081510405 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 335896366 1250 335895116 335895127
    0x1030609110909070801051e01090c05070506010b0904050105010306060c030f03060b0408061e0402060a0813020d080a02060f070e091914010905060a050a05061e04080a05190215 78
    0x190a090071441000c02400d002c005042c481c1006907901041d20500d42d5035824000080c10161301c07917040c654042d40710f80c0b04e0f401c140d00700702800d4003501d040d83c50b0100300002400403c0228404100c0b140c028042800d140d42e03203800c100c05201c1a920160401d90515082c80d20030041c1a81c80210050304903010b18110107000d0300f102e000c8002c1c00e4039a00000700c825001c1004600a0000320b2103078041e4004460044280c3e505070003182447e4002c0b14081e500c0007003404501e48003401548101e13401100750000002d8004160300042c2d843e00300840070b5903400404604030300300c590104062034028000050284561428080041940d07a10701c0c81140507003c82d4001c0f50951150b8030403142c90406076138050009071143d40c44040e0380718092068500e52801e00307000c9051800c0503603500064880c060940e26600b81840f0500006034001100340c0204641709162414141c2c18038098000b41c142803010380400d14250814510302170f0200c401c40c80421603440f040c80141d17203c4403000910b0507081511900c0340c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 335897616 1250 335896366 335896373
    0xa0b0f0912010c020f19020d021e030a030e01080a05012d1203110d050301060906031d01060f05031204050306130201110709051008030a36181b020601030609 69
    0xc1d400da520707007240d803e10000c0128140c020510105110145046038001d135080002c2c20a41080d400d00a904544d0303607070b509409070074074a19840021110320007444441c0d52820101e031800c1a249000c2e00003030300417011030201d503074051550b640200071700900388103a5051102c1d00b140d420b4110a038140c40009101e207000d1140d00c5035100001400d410b03e01215440c90780c00d000e0625281082510070364040c3c04000c6511030f0081e0140d0b070580d015030b510b40b02003500340310081c0c0040100485910101110215919481109028680150058100c00c0c0b01c0c40d4a030800345850108280911480c2c15410f000c14007031501e0025920358000c0103c802d41c0038914141c00181c50b2899007200e090503502840c900807500000c02d8006038040d0400c291025900f40c1c0d50840c40b80c2303e0040c02c5010001407074400034130010350b18003000440c007000c85c081100004180c0c0484002040c845030f00c100302d501c00f030030750421075105140308021048060910500301e90303003100c0000b500c9803814000241016503501201091 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 335898866 1250 335897616 335897629
    0xa0309152307141305060d0e01060512150c0405090a060302011e05030711100c09090606020f06040b1b0708030619050f06070609061401140a0b0f09 65
    0x1540090380d0050441203000200080c05801008400c8403041044040d401c90041d1003040c807550059482d04000481d8031903128480d441220801d81e0100c0c10040841c0030355411004042114041100103560704c1e5a0034410709451070780d40068802c03000b108103078032271240c0410501742d00001c0c00080d416550303800300b01215038011071304055000640d42082048610b855072003002503034000d0300e40f0350501d030074100704822041d021000310380000c0d424004602e6503405a11102d08403d18082a00c1c0510a020b1035041110000407052000620103c0d0422034426188196406003002c0d1007d009a0141005c1e5681e8031040030780010f0001a000b000281a001074028201c07824000c541182d55420840c203068403250000d03a0058844c10b000c442c0041e81441d202844412910b0181032020610414070400c8007a070030060342500c0194071241e10400141030783c41103001c4062190881c2c909941020000c66a005078007815500580c240c100a0107000c4848060300e100c2a5034482c0c047d40c0c0c842200110301c8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 335900116 1250 335898866 335898881
    0x41703042103080606130e0406060503010203090a0314040b0403081803010204030606090c080f01090b01051c0510170c0d03020102090a06050a030f09020604030605060307080607050703170601080c0a03 88
    0x140c0e4000d07070300504009089041c400300d664000ea41e1446941c450000300102e0381306101c1c54501d51000503078100048014a603020f9442402001c00260035603450000c00d003664401c690008081c0c202030031030010180c00446902c0384207031408840c0e06003030914004409611850201811500000c40d43c00800c00f46c0c250b54060910014000b55200d65491038000080c0c40c0380c0c00f484800c24108035401c9201d03840b40780507038483c80440740c0c0c8120700d03460104010010000411382c3c60400c8010055650040074905180441a180e41000505440c0808889200d04116000f070407400311780d4000b41c0c9402100081900e521b03074040f240052030320f01d585000c2c1e009104034030b002600030303282a800040550304040a01201d28054805100c1c4103200703d0b4000c2218604d140c003e6001e902804184049001940b0481d0310020240458603000c0e1580c091624010048400000140000500c401050346c0301074001c00c2d2010000d2403403c1e41c00c06034000f03812036100078240c3c0e030340c03860205a503020f01d440f0350400a03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 335901366 1250 335900116 335900129
    0x1050613090c0308040608420a051915020613030e2e031104080319090b040306052235180301060803040315050a060b04090209040c0f020304170304 65
    0x4d54486d0340785405003410384101c1d00980410f285541c1c0c00040411410003060f03c1c00d1005018244410f41c540c3c05208851204c54241c010003810000310301910b54a2079179034104c002000b0082c0302890148070119580005001c142103402100500400c118403044408119a0504221041100381c00115a122010030100303c0044480c1c1400f0070800e19442484240c01c075159000d1026540245440406214900c600f9809920801411601600b6000900302e51205441c1a6440c507a13111013100d41508a50001e0b01c101c0c1d500d601f40900d02e94890804001d50701900b06440c401000c54489a484154828007101b0b510214101154118000a031f0401c40b83e0303801c0601c82e12501ca080100c0c49014040002e540250b1030648081400d810005c161021030f42d01c030310400324005112410744044d00024001500c401d842d0320011450700c05140c00741003c0c001080005895003001e104200c00c0d140d00801400900c0201e0394201000d0340e0200840781a00d007542102090180700550540c51446161f101c0c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 335902616 1250 335901366 335901383
    0xb1c0c051e1c02030405010e030301050d0303020d090f031d09060913030c121d121207050307050607050304022103040611250608280c030e12091201050613090c03 71
    0x2c1402da6074681c0610302590140c0000c000c207130a8104501d03500c1c4002e0041c01e510142c01d1104600292081c0c00070b0050942410010441144d02d03900d00c4c0401051000850108600300c42c0e03405101041400b00340e9519040b07404808a040c100003040e01180060800c161204810311884107140c080c221022950380d1060789070380103c0311901c00078840241c5006c244103d01c0e100700250803501d42050440000c00b80314010700004c4102084100c0c256200450840b81d6000510828000c1001131020707604c00e085a1302d517240d0f245494410130100c4950808212105002800d0300d200e03080d00041940c081d9405806c03d15504075aa002c0c40f1300e4820500646840d0280c0c54119070b250b41e424124481c100d65580d00c601560380c503490045814034030451042c81210400c2d10080c00841000e0b0014200c41041d42400580d868103040340358202800340c0c81c40b061036200090813000d1418a43d40c81403c0409090003040300741031504c002214145505940040e450f10740c070707500d024031103900c0410004540c400c402 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 335903866 1250 335902616 335902657
    0xe0112230711060606031513020301090f06050102010c0c020108130615031205160308040f1e050c03240603010608060a0e10050402030d23040b1c0c051e 67
    0x5448810801c545000c00940522544802440009020f600400c00100164110341d42c0c01d0131060041588065254045084180c4400c10b07117041c4020f502800700200c0c0801e1114203100301e00165425540103604681c504000040c010b1b0744102c0e9a0b014603424640124503496404150803003141060020701400c1c40c00440380f81c0d010078184103008603441029910301881024405940d540070711409500341d500308101c5038001031320494103c1d80c40346c400c0008040080882e2940000700000a00c0701d0080c880305400d42c0140081040b068500c0d04044000380400c000c40c540e00a0b180856200203906041100e011400640e020f4020320043c04590303048a00d1860025100400742403c42c008034054010302600d48070300c2086021b21482150040c0c0180440c54040c44200c03490031040c132002c400c0b00310800d103403011100c00320f00507c0100a95a00c040c2c8036802540308845840880d80d00c0266149084051095690051709640b21603c0380d4007450118096207500b071082c0d200d82c413003050220506054 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 335905116 1250 335903866 335903921
    0x403120f02100c090f090510060813140a11060c1002090a090c05121605040e0a06050405011404060e0f130c1a030103150b13090501060e07021c03020702010e0112 71
    0x200c001c0705c20000481900c242d990340001d08a50080da02d903681c0601c00102841554000c0c0c40e0241c00c040c07007002c2703035003469202c0e00d651018601000e030240c107130b4000007080c00501c413900241e1108618101e890034548002c89200b0355841c0914480b4581464000c0b541d440c007a544c00078140010071440100f031016003a0034400600c40e500007006892848600804911081058002c0101c00c40141c4c8a15181c6400d10f801003803a6403000344001080c5454410208141d1220f0085600034695a00c440c40461194402c0100b41c4000c0d0b0018403d1807a4841001290721800b0711241c0c20010011900510740101c1c245510f00c040d098000b0715414038041d65520f00402070400660480e800b03040c6078880c2012901c45507003680e48214805134808980300c91040c00d0070003035000320040c1e0310460000501582c1c403104014a05000ca4a4102603041301c0d0303103480080140400e101501205150441ca446c9090740040c10344c2840004090400c0000f00040350310101c29840010050066800c20302e900d41d0052 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 335906366 1250 335905116 335905127
    0x11805061201230607082206030c0f050702030c0f01020a06060b0d0e0c090406021606181a070801030f081b0706020c04020a14072a14060403120f02100c 67
    0x21a120407620741c00d40f40c03140300e20903039144075182c3d000900e500d14003c0c0545505000b13800144811510a40050008102914008060000745201d4401040c118000540500ba20b00c655004005100007000b0000050b80d010980c0c00321620210365480401c2000700040785400320305140100502d10b811008501703107904501600c40c00b80200401d10540701000c0c401c80e22810b02590991700004041c0c08a030018401c2c1d00600101175401010b140700c400503803945016100050f440304000310b030107c0b11500340200921440700c0d401c054520300859040589004050803814800a040151200c1d03103070080240a908903290300b0030100031040802c2030310540310384400c15441003e0240c0300fa20a98115400c050003601d41c190f04035141d070b110758000c01420110a50008100716003000401551007100c1c040c807001e5128101184030402412402e2441215000c80302c058240d10604c010b000400c0000c80202003496082c02d940b4003008160f0700c0708016841c01501c41d440a240750b0a00c2c03c0c046000d0b0f07019 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 335907616 1250 335906366 335906369
    0xf0603040519050f060c1c1d10050a06050303030903030112030314090609060f061003090602250606050d17130302060a0309060501050a0f0308031b030a060302090906090c011805061201 81
    0x150503101d49440c0e0303c03200c000e07900c02c0441000b0b0545007c1c2000360a1f04e03035640106a0810342c1c000c240c1001d4400042d6030305042c10309a00321180e0340d49405000d040c520f541b09440241506600030751540c148140510b90741d003c1482603418068205c3c0c00401003604c02d803c1101600c3c1e01841020103400e01000321a1038000440e002122172240d4400500c4800750305500901a080c00781240312030121814046010b480b9040041d00c1d01602080001c020940a0310410b600341d09480b002e032007000c59880c2050030317101030340d005074400c2d6800c8100101140032040915904c00241e40e0b401e0b518002001042203041c46035001941c04440407520101198054002254140c40741204000300e0380c8035030130450221458012045008808002440022560002103810000b400d900b0304504582c07402c043e51aa01c121a2055440c0d2194410421402e14250060704070481101404080c0391000e8001d40e5000034941450400c02018000c50240c0003031724081d4050070703000e440e40303654080030700e0f04620301c820030b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 335908866 1250 335907616 335907643
    0x50603010320100806010f051b0307030906020c030c041e0c031512150509030f0d0f05091b06090a090f020a110312190e0a030c0c06030603020f060304051905 69
    0x82e00384200d0245003426060005800036207400d504c54807501c0044512202903603003d000d0040802542001d42c0c141c0c0105988048500000c5036940414500108165160b41c00002554094500c400c0705550200340d0040c4000c040d5400600c030840f184000e5040c11b013030390780d00003074601d00501c0740e81c2103526401c02e03408011064000541d0595a084001c0b840401c0d807000382920500c0c4d007040700b8420040d00f1898106220104070313030500c010030111a10a0307004d1801075503241e5607407120030002e926900030a6402881031700580003038000c0720304183c014101040600e2150340002100261650f40c00341400103060303e154104540c0d03100e036487d0002507000807101c9c00072800c40f08c00381c02031803400002c69100042d80c1200d103009840b0411400700508040d4002120306840c3c084040700750300d0802207040070f070f8026071b40d1242886090a000d590a45a50000310415080050074000b58440604543c080e490640e4074540d80c4d515030030940d00b4020009004808561150b02c0441070050000384c4e003684214 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 335910116 1250 335908866 335908913
    0x609090f071b050705091302030d1107090e0c130e0a1b15020a0627081e0a0e090c070c0b04061101050709030609020d050726070509010e100506030103 66
    0x320880c007070b01614403410b0024001d43c03001c0014030190801a80305504200c00303c8404d1000c495075400a030606580c3c403000701c0040c80400c0801d40d8190200404002020300a0080002400755070303125131503101100ca0180a00da89601d6506000b04603840600c8003003816090700e415600070f15103282e02c1c0820352400000301390801c4003c80d01e00d400a14078090348040b50000e0690340029035558000d0035a124a0000600380a019030400301001d21b050744080d40315a00c9240c1d03d4442a80c98814542200348407041c4080903c0201c142a401030504482610100d035040755a50b240c21440a0610a4070300080c009807840600054481c4840040d106030386951f11582d060000da800b1150895404489513030002d8120700c1e0410118080f1b0340b06003840b90004d0110900710007161625850b114056000811130200000380501c41030007903000c4440801d1640181190071300d041d0004000030810301903402d05044846c0460261540885400b00511001d0099074596a490600070041030000a0002c054007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 335911366 1250 335910116 335910137
    0x1202010218040605030d1b05071205010c0306051518060c0114011a0d0f020d110316170106110a060e061e190b03010b0909010b1504080d0302090609090f07 68
    0x10b810300441040c0c440160040c43e403820926403c540705040c00c10006907403122075112001103403062244a010f8a5a00c041c0e003000708a61400c2070031103900d6030224082500d080002e000c55550700c0d1140091580c200041500e80428161a41c0c41400300035905500c10320004221207800c80642000f400600041c072141101e07a40c540040c0c4511008201c10008094100702d0700229101c141e0181014000c000742c01414405101d102c00203c80c0e100c8405102080007000304120b44882c3c51030000d900580e0301e0f1040154004e84071180030003206000d0070b02802114a590b40c3c01d940d080015100c403a4100b81c3c04c1c0320105503950516110001074a9070b180c0c5103d44408002c46465110009009202d207a42124121070000365880080011407003466141d52540c0c1103503da42d81d800c600600840481d400000e032117400c04100f0418440382050303071300381050030302c420882000003140f1020208410b040c0580d40e80c0e80b180004080e84509006154415034031000d004009182803a0070727105151586602c2080c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 335912616 1250 335911366 335911369
    0x10210060f030212161a070210090503010c0e1807030e2a0109031505041b08010509070501030b011211070b0103030e1003020f2a1f0515010c0b131202010218 69
    0x4241c0c40000859a1001e0001009554007844184110400059a187c200899a800240e048c900f007a40c00300081d1a281c0184101e240a2003440403075407003420910300d0700015001148400c42c11103508007040c0240d00c001182c0324069040f1501c40c1541e601a201d81c1400c5580424100031240c6040c410b24a510302070030380701d5004041001c01e0740d0308040384066021141c07005001921008004450414004460401c01c02200035000c004d89000c0f00007203030714540455803070310b406001c2d480b560415040550608072644c204000d034642d079000c504046501580da01080104d0b20075030200502101d0b422000100303156210311075940c24002210311f20880401110114140c1c000c400300744605a100b00a43c0802c4905042c001003031a804001e0450011a54405a401c003440d10400c40d140c4040381c442000d00c3d080e0740c41016400300d8401c1c1c0d055551254800020310b0380840f01d0004000b05850008600d904884103403210304184d2044d451000c0405416000380030f900f2091440000f10f20315181d203800c2c2d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 335913866 1250 335912616 335912623
    0xc1b0601050d0f2301060602010f020a051621050304020f0a0533040605450402090d1112070b0d1805030a080103110d051b010210060f030212 62
    0x495000030b081c040b4801154950400c3c00c40c0c50841100c0e042c407028150180072000550100740031041d1000020700e54030b00311001c0d00b036850a03500c2d4242c0e14410020101429002415110403000182c40da0105845610342441030340011060511460043c80d2010300c2c056000004511580c0b0a8070340c0600585000c0500800e006e250181c10781c040d031064001c0500320244000141c00c00d208891103089001c0c81c040b449116441500710310002900020500140580001d40c145484607400c40b808055a000341c64000c68607842a800074100c000c102018101d90311034065900310100104500c00c075203841d10b010707c441c84101c1d24442c0a08181e5448804501001c1112802ca4000ca07050610349030400e4101c100070094406064480d40c010324148010076000c01c080d200d0361101c6e0312541565410360030300800010b07008045038841e106440c032a000180c0045001d00c660000000c101101180307002c010307818040e5031042a50885c0ca01100050b010044220040c1107078000e903442c54407044070070450303500e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 335915116 1250 335913866 335913869
    0x2203151b050315240c0a0c06020703050c041a0414060907020d021b12030c0318060a120c031b03050412090f0303141b060417040515030406020c01050c1b0601 69
    0x820900c42c07000383d201820020040f18030300004480740c000c0c10b41039034040311103500610900703249a4040ca00407000c00c1a01300030702002d00098002000c1e0949550384099a89000d02009401181c0343c0c102a011030040c459441c0c0d507000f0082c01404100c50201c8110074141c82100e2861041c1d21207030114814a00128140078480030aa0180a0703100c41020005004a01a07003455044032903c050310721010740c18005003c0da01d007098041d5903644561052902d01e00700240e6880d100d000c04108548020b50010905900403ca80780c01281490744044141c00801d442c0c803114a1440070026800c404070b44c5684141d108a104003c200c00c0261154412140c04106004004805240700c00c00c2c40443c1c05044840e004051040c00d01c0d04e854005002e18260200310360030200142d02c150244400c0098903900c510300303509409207486c14a45020000390f207010809111902d0300740004081401d110700c54040780c40001285009101c0c60910480f070040b0b0b075028440d0001240001c3d41805612640440c0090 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 335916366 1250 335915116 335915131
    0x10207020108010e130816050a051005070e0a091a10030c0201180c06140c01150501020607020616110330010b0310030209070e031c1101112203151b0503 67
    0x42d00000745c0c4d0364094180e030110703008600c01040901c02200180c41008048000352203000548201c4440d42c00c6402550406043c00050202c5244402080c0d102d03120f81200b04c400103000811180701040c091184110b007010581d400c80d80c100c100c0240c03641c242c0c00080700107810780e0007040007040c00c0700e080070b80303c10560000705403401c02070040083c2c80c81765210f100041001b00c0c40d42d1038410340481d00d034216084d4414840d608140e10000300001d60301480b80f40d600c0106400a019030385000c1c141c0300080318160300c0946c144070749820f04c22589002082a100d50034540d0b400341c00300d4081c1010702c941400e00224200311000c4803c0010502d03032003003015280260808511170104a0640c2c1c2045400301d8020318501c100700740c000460100707541c1007020a5000070180440b03440d4008a180050821107004c024000d1a07042000b145025040141160418403200b100c480050b07014401c0c0c10090340c1c407940084c1c89010300150488011481d0740c4480300030000d20300718210b10f9510344000e980070702040b01d402 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 335917616 1250 335916366 335916391
    0x2012f07111507150509061905090a0f110306160c020603070c0f0b07080603030a021908040b030f01050f0904030f0c1511070605010e040b070c080912010207020108010e 74
    0x28400520550049400c201c1c00400c159864041030b03254100c2034000c0c03a002d0703550b01002c3c105804240002e00c5581e4200b03905401411503490600c511065081601480402e4596a0360026a410406014044034a0361102d182c280d42c481c03506000700c46039104c0c42198460f00442c0c01141105012030004003032640c2d103441d4280c15030010740803c90107800090520040c400301041010005100d40c0b11401c4c02c41c03003011450440d083c41c0200820b100c400a0006010b54410812600d034613070005240709a507091083c2c2020340240da454a10340c0380c0202c0d40403041e030140100c01d0041e102210b070103ca041c0c403800d450148151410381c042040c0450182e8000d408610502d03c50045184591b00300c588242c05441001d03040e40d1426848030032540e2040b0b00b060012004a030400410003140515401821020035800540c00c2c00d03100c02e05090300c050644403e2101c2c1100d01c6040207076200c02c1d0385080340002c00882b0392441900b035043c00f07580300c00404c81c00030300c10400100b20381518044450081c8881542c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 335918866 1250 335917616 335917627
    0x906060d0b0603120a0c0510150e0a1103010e04050c04050c0d0e0a120f080a0209010503061c0209010e07111b01050901090f0f03120203040602030304060c031b02012f 73
    0xc0001d98000502400d03054081e000d0810100040e00c0014240040a0b41e0b420f140316555003001c070300704071441d450808100e0030181000c81c001c03413090907141038460211441250380c0360071b0560783c000c020800713802c80d0301480800009501a807003c5840e210b6030145080d21140181002000b0072524112180300d50302c0000e00542c1000703511644010030290b44002200c6071a4169225208502003001d501c2001800441c9079101d1584d0050714140c201c4201c42081d0305003100b03000003030308a010080000b0b0064070808031590090080f1520f42500e150040e0504502e542c49003805220014101e03028808540c4442c55800c4032080020651142100408030b22aa114040c0044800c1d40c010001581048000000442d021003000941402006014100078900f4a10b280c00440054148074050a40d0014802003002540100c116030b8000d500140001d941800b03240180c004041122890f140e004548030210007171a01540001c44200305070312010b061000d5210140c0c0701c480c0100344802658810f101c07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 335920116 1250 335918866 335918873
    0x1805070b0a08130f02030a05011e0216060207030516050a120c0201080127050a06030204110a0518122a0d170a030e030708220e0609060102070815010e0906060d 70
    0x980d0700d50fa00ca4110f42401c20f00c5900024a0504007603002c3d5075a966840d0a940c0c0a04509041e80458030b41d4002941000180103c0c0100b80603c4031001e0803080d0002044800c052123031045989020790032038001c1c5802c03402d044c950b5030345440c0c04084642220752819840c034203000d5641d40c0b480a50594070340f1036580c28280b00b04003107074031003207002e00500d00c407032903241901500c0c01080e00c602c45101001840524500400080d510485100280301400308007014281d68010100c521310140045032500043c0c1190120f405142c2085803091a4003440c0030070380c491903041b0081945040e04030220b8000d00d07400701c00c00c025501c0048000f4082d5180042404c41806000c001c0c2502c0302d02030400060480b072141d101c5013154017129040701c11680008034041c4541005016240b82007030495411415410041c0d4a083d590001e814184240100b9002841d140c3c4200003080143c42d441c0151007006041d40e0000c00302c080d080c0600d42d981f454040000780001800580c0380d01c00e6030004d001c803141c041c858a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 335921366 1250 335920116 335920141
    0x19050708031b1c140a02120a0b030c1c030e0303040f0317040807260c0a030303020d0b03100e011404030519090e01060801081c20030702041805070b0a08 67
    0x20340702c0081c040107103500203850841c0c441444000c0d02040c003800c6004c1303580d01d80500030400341a051051010304000811154550b07403000c840400090350028480010f4940050f01c02241d500041c0c2d440580480e00203c242e014016110351140e002c1452910109a02c071700407070081c410804400d0804101040000c1204032242e14800802c910b06500d48625600700f60613600425964a64000241d5520b00076107100c09003600108060034a522082e4001042e081c10381c44041c00301030300401c903590040c1c0c0030ba1082d64400030050448500041d2101480090001c001d0310f03014a52030480440c0c81103100b284128401c50f0306580712807400301c0001c1040c0d00c4520300082c0008010312101e020502e030a420f045203001e484980c440030308561600200740c1c50b02407030280c0303280440b100d000885000c03500801d000e20106508800b100421070b00c4996686580a046006503104e410321060320020600114001805805002903490781529007826100c148202c0210100080103d070025084800c01c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 335922616 1250 335921366 335921401
    0x105070c09050103111c0201020a022806020d020c010801050603131a091c11060c4b030c030a0903030b0415140f0102030d0e0f0f031905070803 63
    0x281600c034141a00c0e50042411584241c0084030600500303d50030455140c02007142c42c159401d01034025a00e803561740000c0d1940d650000003800707055080880010307131149001440c01449100d500f494856030700d0300003c1d81c4010007412038015004911004100354441c050582c1a00d8020f1314652443c6c0318049103892181c480070040c0d03400070b4207504e908103240e10300301c1042c06110403c0082141e0380c40c00751000000144051690140601600303046000c07000480c00a40c8812803907062900e4200c1d20301381c07149001004403008000d103071807c0821410700002209440300100d0ba0f143c41d40d0401140080c185500c0144c03041c120290050000030000d040300e80180c11650b10a280c08520014204082400d5440145011860040e010f0050000918803500b013044045c080313030000c40342c001d010002303500c922901c0940c0318980c2d00d40c1c1e00495540010003c180080c1281812910400040caa825460b504540c04600c110310716400c801458601c40d200340c8140a82000e400c0340755403103242d40007e220100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 335923866 1250 335922616 335922623
    0x3070309050d03030908030103030f09050a06120f0e120705010e060123010c0b15040c082743030c05040f060b0c01020702010207120b0f040305120114030d0309050c010507 75
    0x200c5d4601c8001400700d0000c2c500030f610030b0711103041600c03000d24040c224407140c0c0c1009000301b16100e820000b469011041c031a501b04103140008001c604200c60030041e0034102c848040d030b4802c26048680100c00c03200100840c0340038070001c0007580b17940d60000d44c4400e401c0c41402000c0042001c40d604158160802200c50041410403000d500c02e00d503201e040a503002c440000452940c00340802250506000c2c002480609141c10055464301680d1055580003041500540802a514180d0210340070040082010418880c050002c4107008140500e40204036400d5054030348c00911204640420240e1345c1030301e5000300300c0e900c02818002440020000c6040d81c40302d03240c0350003002640020000007800d0081401c4009030383e401040c000a4540151540b00700b024215140c101d0011680611a4a400c2880348038585801e071542c3c01c040300c007409501d00d10440026040d000049085150780c03d0407540c90160280c41c02c504010b41d003079089440c428030141190b00000b02066a96108200a002c507510 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 335925116 1250 335923866 335923871
    0x60509160c06060e07020d030b06041a09090a020307020f06041707110d110307140a0306020a173117030a060305010204030812010512070e0c1c140903070309050d0303 73
    0x1480c1e01c1e1030703090b0351031680131000e101c007803400b8005802e50511002c22007503000e0a080c05603035103650215005201d28880c0d45c00b0206a13070a03903809003643c5002c031030010500030704031025801c043c65240001d43c001e0b81e014015100716583c1c8540b07101c1c0410360b030348603e4101903903110050030120342240c10b90000e9000c681080303180d8442202ca0351042c1c1c0302071409014410401c6090101c801341864420755400080c1801d0b400300b10341d4010342c1c441e504201034035409000941c490f01703003c005580d1000c4000c6407040403045402006000d001e001e00c24550038460301c40450303072000c80543c901040050341740f01a240c207407507001020003c401c4400654000e0880d20002644a0380c07134840381d0072600b05d81c2040780c29203c0000c10008000380c0da100580034003001c4502c0c0000d4403050ba80507640b1071041c4103024022103850000341000500605490917203100c91001c11285203100541c00007030816504100402441e1808100e00313140000540381d001e0b526440b4240901c0c104010084000324401040f000c264 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 335926366 1250 335925116 335925137
    0x302090405100509100b070f050c032b05070b060906010908070803130519090b0a0e150406172d15070801050102010c2708010e031c06050916 62
    0xc545226161191501d410044034030380c181010404150005050a8069900100305000d4198690100c440c140d60159424014411a1900341e050200c100040741e410f00034002c0400c0440c0043d0520010014401041c1c44030314080c0d41d0986241c00303181d4003d08850001d4000800c5c60905141c9160455414104000c580380d0326602d5900d03203004d0b60401d51039070304041819030f44404c180d09068054541250400110b0540d11015404940640b0a030310002d41c481c40c0706006031b12002640c8001c0e0a50092003d010302e40b90f1901101d200ea403090560145140100010703c08148003101e56149103108041c002c01024100c0d040346491107809045940c64843c1c80001d10400d040001c502d111402100d2414945003002000c0d1000310141c1c841419641003018040701e1990044425409222403c52010540b0413406009000d03d03c0d904424169860f00d0410702d0919000005440121000303c90b00030200c1054200380c4c03d90f5201d100d0241c0010034400498241d080680507415404803601d012030480c2c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 335927616 1250 335926366 335926369
    0x30c08070b07260408010b1801140904060b030115050112110306040e1c0207150216150203220810060b0306040915051609050102031206061615140919020103020901030209 75
    0x10381c013036440318055a548801508250070410180101c00c940414511100d41c50401c0441e540d444600c401c52003882c415000400700031099012488405c0064001c2005201802c081c00c0c80348141d000b040d020444c002d03d4003e14140e80d01410301d00040700250706045464145c00c0c400902511f4081301d0541c0248200c40b00300c240010003a4070700c2c400307c0e401490305a2030443c1602010561643c0c083c2190482d0b0300d071014400004d0301e04000c030390902c0480110b24213411400c17400c60048405601c1c00042000701076290491248100051351201404d41d40c483d50fa07000502c049801e21b200340601014144001001c501d800c1e404646141d011740c54005040c91010786520442d04112094203601d0740240c8000b145580c880a000301a040a00046290180c2c6161a4201010040481c1c1c0702c1d040020711a80142c4400f0700d5a002d0319809109801210348040e00f041c0900610842288804642e100140201000240c4004420001d0004d040340700041d40045020b98000000319050540801c40314666 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 335928866 1250 335927616 335927693
    0xa021b15030a020304020f091519082d0c0f13060e040b0a05071103031501110109060f0f0209060d111303050c040b011d0118030b070504030c08070b07 66
    0x2c000309075005941e80b0f040c0c03042000c082012240c550284200c04100101041c6560381c4a01996044a00c1c80d41000a0074007030399003608540240d0018064820340a48159101610440540c03200c81900700c40c0714044000d81d036071850300078070070740c466082d0041d400c1c2c41c1070401440d602c2400d00c441c0800c61a0300c03201d01c4904000261021151074039030004200c00b014052054640002d10385c64003842c003421456030241e50340800340002d0b1b140495200411143d03030103102d01845440b10b10000340603001103410440010201d031510788500038281041d03070481205510880c0ca1040000309414100360720131901e4001048030600f0704280140411100e82e12038031042429005501c250010650007948200780010340350405c3e11a41401000c580a201c281d003015100c0582100030700c3c10f2468201e00c525407004041e201e40c00508184c0d50300c4140f040213a4072400a0007501e0040c2072513035001e991404040e1340c0351134521540003c0070003444014002644600c1c046051170300355005401e810914a44801d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 335930116 1250 335928866 335928871
    0x509120f0703091a091201060312030b03010b09090706050a02010605031b0102161401110111071b061103090f01230301140a0302030705010507050304030f0c030c0801020a021b1503 79
    0x54040401d09104050b405000340740900342c03003149004101098100020303c2e025031a20981b0461300d03109480c3c1d20560035402200215009200142122030804000d0020461240498025420b00c0110740146c00c1c01c150701c60144111000900c00380385400c400329201c3c2c000c030700c0c0310045540306c80002840c2d40c2c0400c0714880404507090a4000551041c0c00039291540c110403217500340e080320f40d08000281c400c1d06010224038081c01c04171a289003035100f40c0d005007414105e40e000400003288000510149681941c49406802084640c01c0d803164070589040d10b0000a10300305500410100c940c80c20000f81030143e0b000113040c40380c0700c01481b11041140040301e08002d040e1000c048010060710700640d007004803d01064418408280c00c0d5000719460705901d004407410b2000003d0b2503410807008104036801140c00c11442100300d06140b42a120108051100340d544803484200841c500350184202c0d120700c241e80e0014107540089078010524403624000c0c0340e0748180c51804100210603460011413 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 335931366 1250 335930116 335930137
    0x6030b091302150d27020d0305030c251101080f040f030c06020a02010507090f050f0928021e04060807111e010509010e0a030c0b150d06050f061c020103050912 70
    0x1401d010807200301c11888410003e039010703840071745400b40150321480d9140344065054907119540703942d076101074840782c425000c2c043c0c80e0030442c242c1803418500c2c075801200d041d8804c06c0090040406c0000442d21200b0a03115103a0512100022800084414800d1042c503480b90034107100d1b840c0e16440d11800c03a085003e45d240541d44074001c1040322503000c00c01501602200040882c4941044c01040c40c0c50700b003070b2070a030045e213444000c80c5c1200f42801d24a00f0030500c2840700308030328200c0c20703041c3c01a4100d0168001003a022284412201c501c60044e1803e0755490f5840448590350024215498841c8161190030307805150034242c00b170102d20120300211288400041181e0a000744620f08550300202d50010a40220f501080003030350101d01d401c85203802c0007e00040340c842c0f080110b0005003030020b840e40581c980511100304007090700800d100e02c02c49440001e0b81c0e41c441d070900070802400752040d400a018142000c0041d8003a0380606e0f080303000d80040b9410383c45044084403459110101c2403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 335932616 1250 335931366 335931371
    0xb0a020c0915090105010519081302040219080f15040902010e0418030e12060f18010515010305060901031203020d090203010507110601090b03060703020d29040606030b091302150d 79
    0x41d600c50408a01d01c84c010882803814901c4d1400d03100e100c081d000302800300401002a0400412501c04941c0c2804481e1500204110741c0c2d14a0361001c0104225440801404142c5202c000342c59a420704102902c00c00c02650764859256158003000002c008030402203060020340d40074128070f80c6451003101e01c400343e06114081c802101d03040180c80e420b10491443d20a44602e80429240000840c1c01c9821610040c08030059842d00845c4200c0d10402d4a5205400c0d1b2034002041103c0320409103000c03030f50b10b080c0c030100090b8581c00148600d03440c09001c0640903260080026280c1032090b401085000780d40d59002685001703030383c0002e080d2603041c0c510f100000c3c034818180c101e410051140900404502d481044091050350129448800052002080c50b90100300051401165040f24603e1140700c1c4403944d41800440d020703d8440d08239405180100d00d40100441d940e40248118078070520000d1800320940c0d2811200141c50000c0002280c0142844024074441c0b480038010308604141038070f02 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 335933866 1250 335932616 335932651
    0x7020613031203061a190903060c021506010309020a05010e1206040503030609220b0a020417010507020d020d09050607020307050a0b030906060405040b04230a030e040e160b0a020c09 80
    0x8040c1c0300f19810200d6283d513015581c4a40c16501170450f40d0080c010001c1030f816000c2c80201341c5205805520140085007000301c503c010550100701c18082c0d0850715441080c41d228040110300700c036450300e0025003051000405001a41c011000010350000080c001c51410707072036050190a00d6400d80d070486940c0d201100344034062034010b1308a9481056400415030322445008648070002d0750590291982d5180c0e00031600d030703070413640480e8041c09110003213808861004295900a020449002c00180901041d086d070191011403a0704184015a90300064a41000e081000e40d0b1f10002003240e0501c5500e4000840d5215011044010704205030a1512883c0a0b98490306002005201500c59403400007048000743c0c41c95401d54002d41c200c3d410307069000c606860001d801242c00b810030f00a2248000c10780401d64003d0707004899400c140d5081c42070001840d842c40d034540c0105986001d41444a07014044181400040c3c2004d18052048449520b0f032500400c402000036034148074030a840140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 335935116 1250 335933866 335933903
    0x8030a080402040f0905060a0507260601020708060735131a010f0e060d0b090c03120306010c020114070c120605070206090c060c0a0b011511071203050702061303 71
    0x4000090600c4907040c803a0b031117107540300f60719808024451541503035100e000c2003410340b14000785007002540052030500300320021088021910200c6040303006100c4c0355404200708a004c50414000d0320552910100004800820440703000134403000e0385211900012031040107403500900b8040c46094150740c0c02c00c401400d2110341700007644108242001803030010448200303100403a5085405042c0d04500075100c600000300a190004000b6001d030340c01c5424050210030208180320319103030440071101042c4443d240c0c1070a0f40000c42c0d80f1408501046403050140d4040d0703281c140344c031100c0d004051504c0402d980d01e4040002d01d401c09400103600e1100c560420056118840e08406180020714481c0741c02222583e5803840400c40030701401000c1011701000d0b01c01c20480707250942c40040f5200668403030035200200b491014650300001c90508070b0548440340802c02c40305032044289620148149610305a840b5400581c049030002d10412210078084605c40c82480618450f0b103404039100c12000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 335936366 1250 335935116 335935121
    0x3031302280f170601120305390f19050a0614040629010e0a0f150206130507060c110303130609050102010b060304021e190603060b03010605030f1008030a08040204 72
    0x81000f48100c003440d954214480f000229141162072205925445101e1882c0490749805181d244034214202126000c0390941d00c0204090080100740043d0740d00e4281d04c00c0e4580e03c602560200c1c060350030070070100e0411910b0308094224240184101c1d01781595a50303498003103c10f24108041808655070034002003001c41c0c010907601000200c941000c803c2c20a0450001d1200640d40c1418815104245c0405032103c0c0c0d074000042444808441d4015a100308030010550703055450300050041d400005d440d8205441e0034410150418000d0080314100681a2070f140d06000041d948407151029465860750100001c00b40c608000c40d12035505ca1801320b028042011070b030449415a41032419041560306ca22041c0c0b64041c0c0c0441c0d45801590704400c0c507000421030304a003130b600852241e0a00c21008140a0360100700c9581d41e8042290743d5650204c1d50450000703014040001e401000807589010700b154046812187c4070702c00040d070a65591000d403442e48440450703401704040d2404c03c1700b507103404d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 335937616 1250 335936366 335936369
    0x5090604110d0905071706040c08070303211506020d020d020601080d051c050403180b0f0712021e0f100501080a080d060504020d020714010c0203031302280f 69
    0x20358051000d40c441d40c44400c001d000d500802006a9541c4041e0020b101040001074014800585d585488402001d00300e5141d1a003140c1c1524041000c1100156407180021401c0403603800d586d039021904500c0e1510400c86182884c0c030001c0c00d0b00c4030240c1d41d6103000d14484500404041d0003c160340c041908004e810600c600349040c0079034014200400c80e260700420788800d410400d140c4107540d000400e070051003200035030f84591112031a1500700010107800a1080c100c0c12004100c081d05244c0d076010740107691042d1000b013910308400348030080c0011480c01710100001c0c024010380e580f6000b2180c0c0c440b20120103c99000c666400742c01841d40102d0300b031180c042e02100d080d40a0240e5810288c1d502e0f5206840c4100414030800000c41d0a810001030344000080c1800600c290360307841c01500740502075080140103036141c44819800d540b8031041489904400251a0081c42c1103a0324050031145170541d80001b81c1c4c20011948694070022210040c101080700700141d1200c07024104641c1d43c1820205 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 335938866 1250 335937616 335937619
    0x501050601230705070f14030f0a030903080706020d0f05160206011d070216030614070c034e11031306020f0c0307050109110411040339050906 63
    0x50361102168080b40d1405505007441120100d41e5503807246440c51502d400c0da4001003050a20325004039840c5017200061900c040b049080700c0a1000c0410700a455a01c019030003400310b00480410000200c1d414003410000740100340060801d041c0440e00415100e010340781604250360380080002d40c0c4d01d210103488007107040344001c041940c107018980c44180d01c11641580c440f198440010b0259200700a50b0118a14802d850142543e481c83c0003400381c141a4008155a2288be00152025110b084c101070381940603510045048280c40d4010324011142c110a40c1456034034148035a20091604c15848502d1541004c4da40c101c2040101000c480c4902044c508070f1000b0014840e9403401602e441c203115400c40e20050380c6140e51802c00c141e40c80340c0303080c500e0a0f010128022081c02010341c09098801e009a00b0910444400b80400040314404a25550240000d01080c0041514807620144540000c1094050a0035084590740f440d02050800848000359401c28002410400501c6410840 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 335940116 1250 335938866 335938877
    0x721050403080903090105030f0402240309071406031801020c160e0109061208160b0108030a0906050901020a060b210d03060602010218121e0106091a0306010e0a0902040203010b070501050601 84
    0x5c10a0008085100182894410104900103e07003950f035102c1885900c6003206864036403003404105880c00a8008441d0081980118140054118060000740c80c109800820482c034591b01c1a0502030800d024035140c3c0c0956500340640b40b844a4100000340e4160303441c1181da90300c3e504d41081840341200503040988914104981004480080041c0c0b152443d4001e01564580002c08a1001000c0e06148058244101b81000084140002c0020050704070f45030b86011049071900d10550300d51240c0c045403401a40020106808160a0390000c1c1c41c5d6000140500402c051422800e058520f15007088000e070b13080140b011103903680512902c00101104c0c0001c2d07040050980c12008400b4894040c03900510826405030a02c3d0014010364408040010005c0030064100300b01c5070090035203001c3c0090340351a0010b00146820251485d2404502c024024815a03007070078100186c0003409404503c50541780c10341500180d40790300145010f0043c04c4440350311040c95007012400d561005e017050b410b020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 335941366 1250 335940116 335940127
    0xf0f0801020f0412110312031807080c04020f0d0908120a0b0604090e031902010e190b04060c050c0106030b0a0b0d020d020402180a0801141008150721050403080903 72
    0x510000c00d0f14202c0d80c001d5400e45140740c0c14180160b0138030846002c81c1c2d02d40202e046c410800d08182001c0d602030b129081c045003031150014000e40c0d862603107000d03c0071039a00c2124a101c8502d055002058034266410030349084c2132010080906458030060b044680035000700d13000444087c60b0000a03404002e048041c002d03181c0800c08550148558029442d006807200300c076995152040003211440865103041403007002c01148028001d00d2180b40040d024090b002c1c140d0503200d070302c2d60108021904a00d4001c050f84a594a5030010b002e004401ca00f8020144904d04080b1401c0c81410000c501880d02c0140300c3c6440000c0c08202d5014642941c800e1013801d0102025032034042d2a2542d02d81d06682c010b03a22050304c110110362400c0207201c180d00040080012802c41819000a18040000b017000340c815120b00c04404030042c1c05000e24111944031903080c00c201c1001025442d089801400d0409800c0700e09a1303081d0803482c42c420141c0748192603909100030960702294440e40140c00380091801c24 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 335942616 1250 335941366 335941387
    0x504051e1501030318030f0609060605040b033a03061809080904090201120603140c03032107120c03020a2714042c010b04060e010e0406150f0f080102 66
    0x5090600011302084661030b0300a4000f0485200c16001d10b81007070881c2640d5015141080c0600403442c81240c80034100700c4009450306240c0280902e201d40200504400480d1803140d04603507160301c805407030708184004541c14083c076090107500302c0b0f4000e64000c10303018203000c4624200d0200ca501c4901c07003403610481e02d01040164007a01d60079001101c02003620f403800d0004a9804010078402031101d864001c0c0007080001046c01c0000f054150402e6a4483e82e070f0a00305616402070304508580c00d0101d0b60000c0000115050381d03648941681465082c103a4010701400c2104d102000c0480403d5000404c40c4405400800e800c1d40f100b407500b007084601d15094122403008030140306004104402400e103a8041d070311b607000b103100d2a80059404d03a4060000658400d000080014103185500c0d05501c4401c50619000b038205542d68007110b05656403911108854a080051065034402d42c6d1b1908050310a480d900707024002c128038010002e5103400e10b141d00c0c1800102d03920110041e8410001c00303820 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 335943866 1250 335942616 335942653
    0x9080c0108040305030405070806011d0108010c1704170a0309030e0f010f140706020703090515090d120c1a181b0d080c010c020312011d06041104090504051e 69
    0xb070340c1490826140d44aa290091600c0003a8204251a0054600210b6202c3c04028182001c440b41c1141301020b99075084018201d0300d580c1102c0b40020010407461034802980951342e90400c1c8241803001010104107c01c405540060b030b04500042c0e200c40154080c103501c40204013061700203c5400e140d1031040780010f0300142101c418601480010907403a00c024805405555030301d5000b06042d035807124540f50040008406005292145400407000440c24400c0300c1a50880d0030003a044840c030a805845011450050b4604a020444200c0040000075480041d4681e0080d440c62180040c0c242007000c4040a4007881006841c0d5000161842068074810308001031280d00b50b965550302c55040c05c04000d103108000c400e070455030070f1281c1a50030b99400002800641c3c0484140384c0c0716601c440e9851070140c140120208010b02500125001c3e02d8107074032400062903c050960f251903501d1100301c2c01d03104115800c1e501900140041c0e0fa081c50500c1200d0f51150700c81026028480c9800d04581c603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 335945116 1250 335943866 335943871
    0xd050603031204120e030a080c0d0f020a0813050d0b09010509030703020a020f0f06030709080601050103021603030b0103180807140703031b0219090b03010f110a03090f06090302060709080c0108 85
    0x9203950200b4820b0040307000307180f17a0408600160580c3c070042000d081000301c0d68450002c5812600c90b1000080c06640b1a5000c014403a00503806840000819101c0260301d40025041003418848004002001e80da03002589500a1023118000c12514125a1180c00c4410050001246800820141c0000fa90109018540640c1120808002200040803403c071407409030846401003000014801d00036000002c100448005101300c5569a880314011005d900681c48002091001881441c0000c0d00a4000107003044040c9030014103001c90310401003c02d40d0321901035070740c81c200081540078403c1041c0c0c030b0a004080440104455883d594009060008035600b03080308028803040ea00c11917071400051030411600e81701c40e44036203443daa0164028103401461078400c0d844c048441c00c00481e10f00503201d030f2041c8014007504061540d40c0c01d602400ea502d1040780c501540010140000342c0502c1075000c804d010754001e281c2850b20081c00740910401d50456600c99105504120040e80e09c40100ea0313 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 335946366 1250 335945116 335945123
    0x5010504090f0906020c07031b15032a230c0723030303010e090f0d120f0b131e060b09040e011407022113030204020906070c0b0d050603031204 63
    0x19080503450b4600c030040c00b141c0c800402190001640081a040001e075100c10f890040e00da90765402200c50040c0308800c140d200b002014015503d00f500035500a0f0b003c4100600c1780c44d120840d1003a5440d03040f040a840e0441100821035409410000910544155442810f600320f840d2a0401541000381d481445200320008102c03024141082c00d5022140840c03012006011240c495840c2c1c0802d440e00c840451ba00c024910664050500c504c8c40007072030782454400c6848a101c20003140384502c0c064104032410b141550b80312143c00d8080e40b10542c500300c62400503c0c000501510071440006160580400c0301c4901d81003160900c800a09081241e0b494402190000340e03140e60044500c0c0902034036000400c0844489042100045d00410720745081181000b89455030300041110a945010f044403554842d10300d07100500060034140c0c020308440d0f000074801d0382003100c00d5856440c0081700d5005102c02c400042070504140c1558041c468020304110040c40c18804c500840b801d107590002c0028 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 335947616 1250 335946366 335946371
    0x7050d1709031f02040617040b1816031208010b07030e06031314060601033606020c061501030605010804030206060f130231080a030507080d0e010e070503070501050409 74
    0x882a0350340400c00041c180160075032002c1d5500c480030601000390486d224901c0450007020303180c1c0c0440010b4004600c1a5880240c2003d29150580c81c15004902c000b0151600d02c41c503064100039080311785d442350080d4403d100e0902d58070000c000061180f0410307400003040120a010240000c1d1b007000340c1003c605001c1d5041a2039941d40f0400020240c180d041c082c02c0c100e0310b0103808400940214900748110000e032410b00100007500031071030291118244642040ca50844601c0b04e0400020680c100e15008160143c2020005403107207061071015260b1584105d40e03000c101909580600070040282000d003081542031900d81c401a4856a00900e66031042c1c0b1441101000c1c0c0d0b55010904070042c4607054115255050342061902e032450302e400015041200c40c02075104140500d46540c295045840605414001c07540d00b5200c0d6008084111076501041c020b940040543d4032486011025580c00441e00349440402d040c02c0003510b4000c240250402c040034017680c1d8104044034211624042c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 335948866 1250 335947616 335947627
    0x21050f161a0304021e010e060a030f0501050604050f040f110a02160e04030f030203060a0810020904051003020a051c06140103060e010b0307150525050610060c0308061801090203010807050d17 84
    0x41f01c100b80e02e0011158081e00114008141c1c40d410307030000822060300d50041210340d0b214000c019141c0650f110f096030000500034090300c40c1c1410b401c0b14401c00324064011911415244200c1e9041d0048501a0010b078450410300928994200400c401800a0840c0c0310440c201a00c2c01007401c000c009c0040f0030b00d82c0000c04503a0640b03039000264001c0003c0010344010100c50038001c40a035201120305841a030400c40451080d5440410003c101c0c2d50051549805524010601401d605820780080c002c04019400e44042003150181c4a03d2415031240e00e02158194603110044402d4000007203002da240c022944030a0302c1c00a08030003510b21f5030740406000c514050085501d441094460011141c0035041602c050111000040480d4031900903140d9660320001c108200071054801c410001b60400000700110340074148240d0410300c080c0c030744070203440d120300072100c003400030303444520119130010041001423014404031003d04000ca40c2d142451131135031200c0d1032061000c0c0c0d2005406800050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 335950116 1250 335948866 335948869
    0x40f020d0b07020f160b03010e071707030606171302061b0f0d0e10050d0f06081b040f2a0201200d050c030121050f161a0304021e 57
    0xc2008945a009141030140c1c500040000d45915449280860500c507070b0040d0100000c20340c050000342c070f000b0799030b072170550b072030711151503119040940814144040414000d8507083c07030b410078074071030720f2162004141c82c1d00d4524020711624048d02c0103c0d00c2946107007030003080301d241d900140034190120384140e00c84040300c0300145901c1031807801c2c510302d00c112646c200501d00046404405800305403504a2041c80178030601c2008180040100d0000d203042100a14680d6180d10195988142c054001401a03c0380e0703003240341191918184241061140c01092540b4041c000c020114104e10014001603c09401021005081000360240107007005d550503002c510135807003030b0786d802c1e030308591240341404a02c030455841c0c1c0142c41d050a15403c00300081c03000a070317043c2101c1c1203c40c0c000081d51070302e4103d03003007010195480008407080e0081803041009080708000a54403202c1001c21420030500e400c2245c024140030045241e43d814040c01000051798070300403242c601014016595000440100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 335951366 1250 335950116 335950129
    0xc0907050c0d0810090e151b0a0203032a0a0e030f1f060f0b07080a170a0b12011a091b070f060f09020f0f01021501080c010f0305090303040f02 63
    0x10007551081c481ea070903119805500c6040d15014102501d00d24182d44c0c2c84020000a1b81c00e805203005895002c03490000014040c10141c982c0700340c0f82c032007110440d43d002e110494130f41d1110f401c2c039006a001209000b080050800104241c0c0e09801d24024159031240800c1094065420320170248201e01c3d070010040d403001c0c840d42d801691210141d400010180c0c2010190f20300c2e0040100540385820404604021059070000c1031354007244119003850150358a03103001e0b5200302c8003002040103d542c0c9824000590502e203008403403409010500c0b110a83c00c1c01b04c00603035030070f103404d40360b043c041c04603d50052078070341140c584800d0780c00000c0d594030300030b00b8001d03040400c003240c0b80a40d001a4090510081000b11200c251040d80d003801480b5006174020300f0382c0c80b1210080e60041c940c0681c0742b0f90740b4260b600700c403241806006035111400c84100c0d980f02003a0036841243c481c6c201c0c6440190a40e0b100103544004003140c10200b200703081000341d1695074080140000c1c8501d4a1045038019540c64a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 335952616 1250 335951366 335951377
    0x9020a050909010c200606060306121b03100204030210051e0708090909012a020f010603062003040c050d0206120412090f0602150a02040807080106080c0109080c090705 74
    0xa0081e03078403401c04490681c000c01c90488401d00040c0c000c108000d4603148150700095602a280062542d500e800c4100615944050400d03903218207811126499800700348004048828000000c00f14001d1a0707050606000880c0103021b1b466104000c01d00c0180e0b110f40c20480200d807203240454a900000c10202c0541d410b84040e00110000072541c035003048511002042000710549404a0b1074507504419170a90700c4900c0c43d042090440c1c9039071302402060701c107012070f51840c501c1213032111b039074400b00c2c83d00b100c2d0150020b942040d103800300e0820340c1d14080c00b180103003071001c10110310714502602c0301c0900901500620384654400c141c4001955184001e6072504090040e01d00e5a44c1060314102c1c1c2c150b21114030305808121101c42c0080e01b800c1d01403c02088071129000751030110403d03011521784c000002c1c051004107909000c00f1804074404c00071080601038000001403014241303400c3c24030382407110590b18100710303156a0034040307400007050041c01100240c440d090781e5100d490041d07490b40104c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 335953866 1250 335952616 335952619
    0xc070803030411191815051503010f06111e12120a050f06150d1805070806062e02121c050609060a060818011506080612070909020a05 59
    0xc0144024010007240c8070f60810000c444400b515860045003d004210300d00c5078070709004c3e4461100340082e509130820443c0c040c0000c4803403102911000041c424200300c000500d420a0040014002440700140c410003610083c1001e450a001040a10390354030940c04c01d43e0b10058001034220300130f00c002c01c080c030f0310040c0102003903843d2500320f1401c84842c0340403590303601800d0610001c1303a11054041d80e8540a03c030042e1920000c0d0900385803015041d8082d580b42c031034440e47c80350441041e288011b031103a0203034131490180c800701e441e011072180f500001604c1a4440d0031200094242d565107501e18003801d8130001400400e1503031411b0b00740e041042e04142050309100003e00b10781ca0004c800a14151743d21401402c00c00783d1560010b000e20014101c8010340c021a5600042c095140941101507001044854003d200c000308030b000c0b0b09441002c1004555410903031014054103401a20065022806861880b001c48110a20f00d035a21100d20481000c5a80c52003080c040d51901325006010700350 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 335955116 1250 335953866 335953873
    0xa09030c0b07050d030902060d1d011404020a06030c0f0c1509110a06020a0b010b1b0d0c0c0605070f06051906030b09010b0118051509040e0703170705120c0708 70
    0x60764005400581e110340000c840e140291543d06000328040e1060518854014001c10b042c14408446400140a018240b48101c0141c00c864011503109001d803194442c81050318111904151061106000701030300030000b0304d81003100c000b03502d99009007a214030300e84d6403510721201c90f418200354100e04181550016094146040c1d1424428801001c01c0c65080581d04d00880341d1362520226282c2c412041d00a04c2e16040c04010044c01c00c161016040c00e0494525043d490220000c07802e03d40101c1c90304040104080d500704106210000f01984024445810b0240c40c2207105da550803081100814020b020030f5840340810b00c9000d40b4000a000e15401d0034080240d00d80f06d09040510b03800807103c0290543c280f007034441031540300b80c0c20494508000d410b42c502c0ea50601080200e09541028030303415500d802d012a2106d1350303a03070040c01c500301600800741c0303111800d5003420403041284011910030001d003080b0a8000540c00100ca0368003208080700a43c031800302c410b060781411000d51200d0614403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 335956366 1250 335955116 335955119
    0xa0e060d050403080405070603060b040302101103070f0203011109010f11241009060f060804060209040212041406090705040b0307050901240c030801060c020f100201020409110903060c0a09030c 85
    0x613008000a07005600030011503000c0da030369040442c2652a030340254510080280003c00050400402107641c648641c2405551440c0842d045445c5030841c7c40c0c1915240c0050a410703040d41000e10604403041e000c801c0440c94001d5050000c1e01c00342c022030600301000103010030100445024031421110140400507100818140285200c0501050f111104048190000003c48a00764030171442140d0741d985540025500e40a0241c814500040055890580030041c04246035210301c010b201d464400b11101c0726030308040c02c0a255241c60110f0301c1c18590b102d02c043c4480301e04002240d80840d0707821a00803900100c0ca001013410311015500c01500210038200216190740c0d030309044806c24500c210040304461a49000310b802810524001d000302c2c42e00710040c0040d5100c0c0341d4400c1079034009020b86101c000c090020441c42c00d200440000180d50100d41030103040f009000d00c000408080c10000d08000300040005d48550002d805014040780018000310300c2c0d03003c0e20b0550300a5400c5200b0310340e0300703 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 335957616 1250 335956366 335956373
    0x9010e0105210c25031b05010e07120b06040b0a0b070f12091509050d03122309070506040305060a0504051015030201080c03070f03020a18080a2102030a0e060d0504 72
    0xa1304420701c03000031100c44a0000079240b03480c10902c128a90180d84110000b1500b041e4207440c141650b8054609540f42ca203100000031042140000070031010808280340e07105824010801c0401500240c4180d007400840c0e519644c031540104d041c2d51500140d695104441d1030400b040303000411008000354200c40e11140b400e0340241e554000c65003031000d640029054040119040c5510b80038803648400c030003c400003c24810036074114440d0050b4000a03e005404c0c500030316012000140d5035100d0020801c002c1414800c1c132004e4000c1c101680c2c203604040c15a03580e241c50350707802008600805c0d600c00000341072102c100301030340d003100601100f080658060054106c1017021400180e000c00c0401001c1034a40461034100c03071080d00a07550b0b03195101c4440b44120081d5001c4400c00341003040d008060004c03401034002c22802802508000e200d1760b0482c0c60031290200c2e28803404100310711800c4000c05826008002c0b5510f5141901d01010400d42610004d44140283c2d0503c1540d1032a000420040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 335958866 1250 335957616 335957641
    0x3110c0a0f0f27020a090b2b0c0509060d02040308040306020304061409100b030708010f1d0c0303030f060d0611030411030c0a031b0317030a060602010209010e010521 73
    0x265251040b81c41e544075243c1062008001c1c0d0a07820354031403105410701c00101c500700d42c0030340010317061445e010614560b01e07004040303142c0090303d4000422025444031031000b5403a441e4501c04d48504e100a21000b40149006045401400405030181d500051060101421503044034080d50344004031a8031a62241880002034204131401c4035400d1400b404c40c1da1703028107004944e11802c900e50007020700e4002d10240c0d80241c0410482c40e50944079024011a40c20400c0c0030b061000c4080799400140e0000b01c806074184030044000000c1c0a0304140416001c688020080301d900c004050b14880702d80e2510300119207854050000544214a00740f481c0c80c000a4070030040d03000703901a25a44047d06085c0c1c00300754995644a20381e540c031a0148c40c0c200001184207240d41e01400a1461041c1140e03525210070072500310402441d41c0000d800020040404a14868030b07015201d1031008604040c00c44002820220f40340407110306004011545090891b0003d088030101c040d40920402c035400d2481c0d00001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 335960116 1250 335958866 335958869
    0x1020408071523040b070302073f2307080a200f1e03010212070f090905010b0405090c0d09050d121a010302130305060106080414010b090403110c0a0f 66
    0xc07469061000b002408a400c141480f03034014203145400e2500c240403506521451003181503010301311000030581540a01c20307094512120000c84074401460708816810b0741d100d440500494490004808030b24521401c07082d110021140030303505001098658546002548400380512440c1025401c010744070a101c107840d03501e900c0c034000c02d064910401c4820b0f90341c2a041600100454007001c09601081c01100c42d680d4054001440c00c0c4202241455242e821148500421610000001c60aa01a180c10000c0c50043c20411103941414604800741c4100d2081600c9411000049102c2c2c440281c03c0b900c9035160ee0204100b0580306261454441d0300302c1402502007411509900382d02c03a824007500e10310b01d902107044403102640e03034015402500006a02c450744024404040001002002401d01804068641d007400389000d10b41500700c5100c45400c41c0c0564108aa10111600e42854480e001039160604180300c80c1000d0f521071611019440103903120030aa20002540803c541c0d0000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 335961366 1250 335960116 335960159
    0xc0a140703120c0503150603130c030b010e0f1620061e01090209060d0c0c0c0f030b060604060f11032515020304050a151503120f0212070f050102040807 67
    0x444030556080a480600003204d0034181e484024841c1b00003880d2110085a201031000d480200d5a00c4549480c0c0102c2c1140d00100c074034106844c0180038000e003000400f903109503003141c025201d00e0014802e10450b61186040010b0000e14141d4060903462000381410880d01481203d00c00c1c0340031001d140030000c00800d00501d180e0a90300100348404140201d0f6400100505080e24000003541200010180e14085030100b082100021001528501c072050051607400b466003049821402d2121500c0b9014281e02d02c104c0d0100310401126403c000580310032890381c240f20300c8500300d015066003184500f030344440ca01e40c0c00c1d1310340d006041006001d195174180140c0182e54900300844892040b888180e070040e00390392141e02d0740000035001c8201001d4203070032f9210124011000c0756507103c00c030405400840340307002104102400c46900203440000300900c0d1009104200c11550100300c4ca01c10480040c01c0c03000d0920b000000e002e0300f501218000d1a8050440e84c80e9583d44015040d0f81d0345801e080d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 335962616 1250 335961366 335961371
    0x60c330b12030f0f0c07090e0a05060a02040f050f040f1b08061503190204050a3b010b0906041502030310060302030907060509041b1d060705060c0a14070312 69
    0x14403a0201c004241c6103c00f06440f0303154a020b480181c4412240c2103180564607030320807000045a03017610fa000e218560010f0b0b074001d00d0b1440c21450420b0a0038001444210002d00c10320003040b516000c0341c84502240c1c0e0545032903103902c0403a00800c1c05040740b00b0f03910325000d08180c150100c0715210006401940c189545101640e15013804010203007290080e11030407005c003840814209501003804403549070002c000103103003650341c0f00410248031043d4003540d001e50395034000200002e4200c804501008047c0071941120b8544003802c0035401060041020b0203001259004154440100711005401b86503c1c040c42100b041038025074035803081b2420303050920b9180300022100d010b8003d403401144e6000260451505005007102d20b03030402c421103544a80c407080c0d0001000b070080f80000003004690342d00f101200c0203140e50020a96110207003030087c1020808100420000b184180d00f103900f00c01c17a59a2002002d004480800081ba00c1d81d41c510790014080c410150070040410710f0b541d15203020f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 335963866 1250 335962616 335962639
    0x29011103031015170114100c0b010e13050109060b152107140a09090b2b06020702090108011401050414131b06020102070c090501060c330b 61
    0x4154407404156140300502000490603c00c00c40100003104020040e85042100c0d90882e46107854004801c2e40100716400400088070003074109042c84004048407820045d0700408140e071032120707000341407203010000c540d0000030440701c40300c1e0180301460b1ba070400c0c001e12841146040500092a50003541d031322900080000303c3e030350160700040d03800d10310616088941000f10005e006030344a200418407401c000b06500c1c02c2d2080d040c080b020b0003200441d0794a140d03040e802d003900071013110401c8807014072a4000b517088221030070901402e4240d0441e5400402c1c580c55a0345800c00182c0107000c40254400054800400c8807801540411703c00218000c1465540c0daa8005000848101004a84034010301030700091541600e5002d0b40590740c402d8003500d00001210141c2240d2a00c5038006100503500000c0340303c14043e0003010300340541035280c3c0421140d450070300003030a2800c3c0100002d0150400f0421a404c5a44483c003440c02200344a5090b0f100c554039400c0c15008024162025225200c400d40c1d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 335965116 1250 335963866 335963897
    0xa140c04020a0503090115030203060109090602070206032508010b0406030908040305060f0a1b0509012601080a03080a0e1c0302040302090a0f0c020c01050d0b0307170609060901022505012901 84
    0xd8280c200c275000340240029900740b5920001404030080259489a020420800162a100d00031482030a403030082010481e19500000402124130902504101c072000052001914140490341200c4a41c2400910300104e45840a26405640d1010b800e6010301c41c2004001100c150380340e4843c04c05ca0208106d02c4011070003144c00d003c18941c401001032014440c400d015401400340780583ca002c2194101070858266072424010000d810001258100824030b5040641103c40d040e000750582e20240705280d50000b04035903031689141800c00c1c400807181e05001c1ca60003581241c2c01355030050603118142c90721080e03010250604482c01100103160403240190248045591200744c40140d44045c604400288100e01a20265120035410301542000140074800c0c1203141d401411000d029041c03900e40244560304001c4020319044259004000b07101a620849002000d004100100d010380410076090190042070b125120b1001c1140c1d0741c1f00c1c00c40e80358042100030070070351090740c48405e9099000d5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 335966366 1250 335965116 335965151
    0x50606030f0d09260f071d010302030d0c0219081e0a0308040204050c040806011517090303040318080610030b01120308010e06010201200307030c0c0201020a140c04020a05030901 78
    0x1000000c0c0c003048041c4407640c0c94490018020040e07004100713801e00c21a042608140c61130138002c409900052041020002e2501071151101d81421386941c80c1d85036801280e00e42d00c80c4541542040100b130101d40071541e030a05e044e005800010301c0206c1c002e458140c01907560395285414480c10784841803650f115a000100c8003201a81aa10070406403110350030320001d400c1c094400101d0003c2840042001803007040306600a104070b41d14070000912203040900007409108a02411105020401c0b506200000c02c40b50403680c185091200c03400605020702c00c2c03004a4102c110a4040c07841071004020f43e8440d0801501e000d211110402d0740e84002c0b104448403040c4008021840d4413004010401204a0007940800c0600012841003102c1c0e44c0120101803508003101d4011000c014058104c0e07062048094030b9005003045140386102c1c1e000031b981c03040c880034001d010b461702c201a1020070105126000b140034020f401592600b207052400b13421504115840c407565031a01e040c0e03041516818 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 335967616 1250 335966366 335966383
    0x806090f0103201f090302040b040b030a030c06090b0f0406060801150302010c0f020a031b210b07030e0304060207090e0d140309120706020307030b15031501020a0609050606030f 78
    0x214600d66010060b2120f5007031440342800c9a075100c1e521803d8001071000001a41e0f860152a030348107002c0c181503104100441d141085040d000724a4540c1141d510745001a8a20801e5094207001410000784d01d40400542841080100780c07104900500240b980380300c00890180d44212020f000e695280c0d100c6500b01d036884941110b004090384c41c2000594050ba0b580050207002d802cae1403a4039002c1e178020503004441648100c1d41844a20f034080500da034070310720710300250440300012003019195030100c040851072080050000d0313840c000811300c2a80288c0c006e035070b400c1c1e10b1000d40b1f445a0b601c00000e501e0b40a107204401045082491340011800c012984201c01550780c2c1300c803448400380071803210716600010800d142610941c0c148500c92070b40380025121451144201513a070f031401c031400900355261a40301d0343c0640100034202000c02102c1095a81c00383c40c10030300c00009003660f40100e1405240100140c4024509a200e00a001011401520804040d011101240d0801c4040f0303503140c555 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 335968866 1250 335967616 335967623
    0xf300f0c070201140f070c0801021201091a03010e0c04060603050408191b052b080c090307030b1009050c1e0f0d0c020f0c010306031e0f080a0806090f0103 68
    0x10a00040c0502038000c000d4103015006241141408800c2c044400241e8003155900c0032401d80810000704100340101d00c10302400160000758200300100c0300d4401c80000601482d80340c1d540311a055a840f0300140090420010000d000740205905c1c070071510b4403141440107031809141040e001081c074134001e00a0500465001c2d030054904000f00c001c444010681034440001c020580840301441c10048400084043c000c10142403001e40700580501000f0000c02d04081c00200c28082071400c64000701e4955014a0002c0e62540d01c0800c0400203080c50300c907405c01000d904c402d8090040708540225110181e40301564200400c1c0c550104900d294022440c80520820f030b12141030322540800c1b00900003400141c41100c0c28640c055541805440030300400f1801a401184038020002d0704000542d90390b102130804000c400e0130340e25208070021041741e0f4100010803242c01c19040044070351184403255040703c803540d1249040e420091000c0004d44205105130f8284002c0b5103c0c890f1200f426049960 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 335970116 1250 335968866 335968891
    0x213061a0901030608070b0a090609120201030b03070503010908040510090806040f11060d050703060b040b090402220b0a08070806210c19050910080d140f30 69
    0x42003480062aa8001104181059118900081c4101d010858080501040d45ca071135251100064003e0000b075440d40070f0010499503007810040c003840d420503104a2038082ca0081280105200800d103450342682c40603416619008414082c000301d68060b00036100c040b0b5070800c00f03021100c2e04032820009402080c0840c0c100700c004c2400220740d07204d03c2c28654800c101211010040c0d0000a0550b04940880b490041d142d0082003009070749445103401424a1804450038181003481f42c200303a0084042c4503005590018001d042e0300b03c0d280b01111100e032100161200305403290280c40058005004160100324060085036544d03019540e82407090201400407030704030822041233100c1e41101065418a40a4040c00c00b02c0c644903d903c03d450083e0b070040010803103160500707118180030000d1800281104200090001c0c81012031303048070171007480c901500000103c0059003000c1c49a02c014030004040000d02001d51b0300e003c10415450304012201c281141c02e81d175411029680c0c111015203003c00b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 335971223 1107 335970116 335970149
    0x60720030f0703030e0f0c01030c050405030d050a120b06030c0306010e031c020c0108040b0a020a1404090504060606030207050a1709060301090902030c01210b010e1804021306 77
    0x240c10002003607481c003914646600c90805010048c1015291814200150b1040c0d064038007a11000b0203903401c9401149014146074045a05500030686103e0808201a1644100c0c03020b4070303003e80218030395541c0500d5142c07182d1001301407a06000da04201e90b500c80d201002101002041d00c504889180c1080c0c034064a481048980381c0e04000f130316010403000032215070b0300507000180010056195072000748251101c0720b0740c0b24460f100401c00f08000070300d02c160b500400e000b0350181c03008002241d1907902c118240d1140c40c0c03000e062030780814010800030710648071003da00c0c0c94240c20f4605064610000401960007a07101184c800e85462001c4103602d4144190340e002d04090030710030800008814108491b00d0724000303140c900d5607111070b90b001c140d01480d800d010040008003681544007480e4030302090041e043e54240d010302e10301101250f000f10700e440703030005480c0c0100a200440 = true := by decide +kernel

theorem cover : BRFrame.Cov 335791366 335971223 := by
  have h0 := BRFrame.cov_init 335791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 335791366 ≤ n) (h2 : n < 335971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
