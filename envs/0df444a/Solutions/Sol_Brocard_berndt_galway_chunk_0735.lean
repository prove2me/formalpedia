-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0735
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:29:05.779005+00:00
-- url     : https://prove2.me/submissions/3ba2ac14-bd99-49e2-8713-b1409202642c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 132014388 ≤ n < 132194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 132015638 1250 132014388 132014453
    0x21050c010c030e0d06200a080709140f01020f0f030304051c120b03010912020a0c06031509020702030c06031e010807260a080a020a20030613080c0a 65
    0x52809072400c1c0c05a0b10359501070039210078002400760500c419141c00ba1503c28031169121000040d082660000302070646c1c80f004c00c100280212409000d100030011960300400a28202c4c00a452800104580f40c607080515080141d00e41219a40114003078042d9a201452914022001c0c62042d0702500c1a00c0450132903618440c01e1180320209070020805850100780c48651a07803008002d820302078000245000c080d02c4404070100d0719000080141c0c1700000d527034200480d5420283c000c0009007070038001002c81203114803200030f0601450401300d40c003044c40c00c10356038208150007070303248040c2106a40c0e042c2110010b405151107035084030601d100500028100e40c001a144c412920480c0356200f0340164580b1000320700050300d00009940c81901d5203003000c1031a007030080500b0b641d55001014900c405e0304e000c0300314482c4642e4640c840e028080382030906440110b1107a522021b40d00302e240082a0300d02c0c214559001e4108020040d03c249031054082191594000d96440e91045200030300762410b8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 132016888 1250 132015638 132015647
    0x4030203070918030c050a0b100602010b0910051c0f0f120c15050612070f0602010606020a05210c061e06040b0a060809031b0a2f0f060421050c01 64
    0x80798641583c8551001c0000480d20815421603294442c0c4140c82c080c44140c3c8078019804000e0781c101c0340c0780301404420801d03282c091240320200181900c40c88268503040e08100315440c0f582c42400c0c00303070507156100b031300c80c0c040209190b0049520a0a216040010b800c1103100800c415034100d82c00e000f5000081d046c0350045c607071000e2440e07009025044160940c02440060300c1c0150480c1c1d0080034080c200a6080003d1001802925018407094546072800702c0090948526030700400541d00328050000110300086000440092290004003074006240c9034110035104401440c00d031805420140405001c004103c081b04d51218149002c10351501e0080104840042480707641c4031024003020401a0700440f4000d9000403014156824500952859040c00b10b01541c603050540100448808105842c01c0c84030340c5c222512881c1d8000070158010008841384017000314070070a00644800e505036100c1c0c0840b0050410f0b120305803102160150610300c42c03a03840d40c0071580e40c01844190b002d1540304 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 132018138 1250 132016888 132016901
    0x6020a02010c2a030903080a030b040b0f0916090518010905010509010806070e15040f030b010801050c251203090611030601050d09050a020d083402040b04140c040302030709 76
    0x1400740302140f103514070029030758030303001c2800840c00c3c03000755540000458449809090a50321a480202e00d010807441003104a800c1024901c1c4030b41324001a8000b5920343c0402568442c1c141c080701041600414800c3c0d41c0044c103640041e0348046c010b4040103d80c2c440c0c02d4140c1c12038014900c1400300341d03201c408101a8040074003c001081e4010070010301041e100704040f200d0441d001d040403150344200100c000e0107178445e0f080300703d0078201680d08104214002030f01500501110008104034105804610014071072600c002440400b03418080070010f00c50f4850404180e8002002c41c0611f840c60000340241a40c0300c4c0a13210369282070f010701a61291a01101e104140580d9000e1078144191120030040625102c1078032030b8440c64400d400143c680c0ca000d07900280c05542507a4449500c0090b00c4c09200d08040410a250112911100320107510061080310381d50440b408139090760890f0100d4002c11b40d8092008021550fa42031007841d654120042060b07900a0f002d46140c20307111040941a03903074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 132019388 1250 132018138 132018167
    0x1209080d2115030204050c07051e0d180e0f0610090e06060f0c01060602060103021201060501080705090607060f1a090c040909050321160e150a030b090406020a02010c 73
    0x3021000c1501d00e5903400700c410b00400982c0340380919180d801140413039100316144c0004010004118040c80320811503007003281010105240300701c604102098480782c88005036814481e01d07580b111112038143d4041e0029201c804a0f002c120f01c3c0201c04001300d40c1042d02c0e00b5004000d400c40c42408148680140815106030201622440c0c40346001d000182e40b066100030b40b20328041c440c1c075107501400e01921006010b2640140b101d54114010402d0111080070880601c1c1c0c074021081060383d030010362041d4466101d0030300c9515440d6100c08070320203102d240d0b801400382d03240c900080da10a249512080c40030300305146a800c4c00c1c03504418002178400036202c10002c00e5040c8000c2100c544035400186d1010300c03510549017821502d0034102c450303c1c0d403004c010b200c0009000402020010b9803940c00b012081e98900f00410113a00d0300418001180c0b03d451032414040065503980d654060740080c240344c1009050010f0324a042d0421000942200c100013005508141426048500c0340120b18020341 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 132020638 1250 132019388 132019427
    0xd0e010c0b010e07091e060305060a080703060b061909080c04090b0114040204030203031c05250309021f02060105180708070c060b13150803030c090105030406091209080d 75
    0xd08162107041940c1c0d00508040c00c2140100010680d0a0324000320007010a0001e940407920b1f003400409019118000c14160140910000400001c0800282003040382c0e0014000110380c1442c00c041541c0d84100c0a6903524160b104180d4880207900650703080468030018151151001d1140400080c0c510198019249031504001800510048074880c802450014001840d10784e03680d000c03a046402c0410f80c00f0f0b105850490700c0c225031003203000d442c1c0d00854086080c1c04031482c1c030305c203e9040c1c5000c2124a040641c4c591041c0119151001d1030740d100c440f0a0300c543c1c1d981007020300081d40c454090003803a0190000184004030032440d800903a00030b07503d54580d6188d42c0d0700c1c41401c88103003054640603541180c44030480c80c065201d8100c01c00512000181c0030503c8804240e1002c104c4490741e2040105500400400082c1c0d24900c003902c0400a092800d0350381e80c5c8039402c1c00e50107007408550140c40c03101d64420001350150494619401c440040c0c00356041d0041480c000d907000182c903410002e218 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 132021888 1250 132020638 132020641
    0x2120c041b020c0f0f040e0d090b0f0426031c0e0a03210f05160e100e0d0204090501050a1409060106050301030201050a02030c010e0d020c0415050d21020d0e010c0b 72
    0x70b00c1e05107104c103801c0d034001d0019018818404001003c1d2000c0184003c2642c00400d120203445d680007800c18003030502040c0d0380340b41140d0328041c08803d21a910502c00c507414040c200d0510310040c8051030341661800d10840c0d40310100114480f260110381681d1880341890000180384084001c0781400000b5016118294808540111160101d81c40e8001c41c660303d66440d099800c0d1680d40c172544d4006c80c0701d000e015884158680002d4990006c0502c5c07103208010300c2c1c004000c03881d84a43c01d00e00300d00d400c2d035804014442c0c0744041006007035940d00c02803c650a0908214281d415a8000504411410b58a0107543c50700e0348030710b480d80c00070f0040b030000540030401440507500407001426051a02d2040300e1519400a0150f402c44440c00c10f0741c620b642118001740c20441d0704202442115100b240d0400c08864805c864082241c01845614018154009600188070900d68800964060380102e40c1a218000c10029259480203a4106c045600d428100140e54442c603a000a00c903403104144605 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 132023138 1250 132021888 132021913
    0xc1e19080309160e06010f0216030308040b07081005041a030f030a0e18010306110405040516030509010204080616051c0501031209031119080a0c0806060616030c02030a02120c041b02 80
    0x1c107401c0c7e201c074015841480119814030980c07680c0000254060b6860104501345840c20040951001d80440200100401804034568107240c0d2041103070707400c41e00000e1101100084900d40d0050303e80081d454020071300c400c0da09034404402441a4903041d078403c010b415500c0204400a51000401014441e040b401400025180d5000c0c1d03800740440880181082c1e601c030002415600111401150002d1000001d40707000c0c0c143c040c1e2078100f5017440003513050508220517940e40e00d000074141c003201d60300204010086801103044030290b0b005550a4000c1c41762044400010748400e1100301c8904244120550300300d442a07178100140c0c1d40c0882d0000c01700d5031000801c0701d5070540c4095040000c0e50307150000340b01d800400c40c400119224130001c400c07007450b03d02d0302d6040c4000184000d00403442001030b442c4401d6010742c0e664440c3e61604000408680500100c0d01e404210030000750004000980d1042203440010445a816070484062010b503040b28041d01d00340d8003602c2c141026074407040303004ca030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 132024388 1250 132023138 132023147
    0xe01080706021504030507021518030c1503040804030b0106050711010201050609010e06030c060409090b1b0405240d02040e06030109030e0609060906030a0903090b0c1e19080309160e0601 82
    0x8104e4002c0c43d040782480c4054000034058100b05000182c03030400010300c0042c240031410b03082d4a04da000c0317003c0c0000c08100c80c081020724101015203000460000002002c1050020a54020750340048201c2210b41e121003010b0140d610412f820340301c0202c9041d06030440c1d841401514450407018098801d503918004141380224030103003035117515000b01442110680c0320b44014000811010001091a031070b54205007410b1040540365045c02000c130250660f030039100e04103c404642e4252030403201401d0040c48190350146d1a82c3d031645406e0000f5180d414880c1c40c1c2c010340251550b41e10086907507200c040801d402c0f40d036580030042c0800e048501c0284d0925108014042e0950007411071403038690003100161099104954044034940c1d540038a5050540c02010782000c2c1100c8a0f845180c924280342d6281c1c2c411791f032803c003d016030b0006074218002e58140703c034560100943c42c4500007809141b07030403a503542049640c010244188503004840000480158003110ae5031a241c6000c2c0c0c032104011076 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 132025638 1250 132024388 132024391
    0x902280309060e010b040608060412050a18080c040f051009020a23070c060507151802030f1b041a0d02150304080d0f02090609040b19060206010e010807060215 70
    0x409060350341101c0400704041d80640040d150030350300001079041d00001004120b564941001070780d940088200000685201d1426140c1c1c2101e041040d2110700b0807004907480d490b0450324418041010100180c04840010038442c0d03c40110f40c1440300461222401b0200d690448040848000ca000d042110912640c02005031440501d09070900300d190450f1840c0a001c2000031220a280019910044c08140c46a66002d000a8501302d8079004a58607a869400c01d500c1c40c0d00302055580c00c121300c1c0d8814400a0b8210182c0c0501901d8003003080301009515981e0a032004414507c981034003404a10301442006240309032a4220000c55900609010401ea5103840407032300002000700740504980310202961240d4880c060444d6200700c02c242060689285801c1c5050311f60060000c81040ea4855055800d00070050700c00103220600800010210304080071102d118040402010540e1076022507030505840d0019695a61a43c0e20b55031550f6a60441c03007581c00607007003904101150803001d40d046 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 132026888 1250 132025638 132025717
    0x50a0818011d07050f030105010e0103061104050a08010b010806030d0c0b0c0d0603081b03030606040e0a0b1201020d060b09060a11030f0f0702010e010809100c0201090c120203070902 80
    0x90a60200ca410000d662920b0884101e1984076603000c0246141c1001c80d24018602503000784129450113080300c11044040c0801811720703407202d040482074050541030318020702d0000d00c1d080340c0c10f1b590015a0b008101c4403010034002420710340041c1c03142c200021a040500d0b805c4c1c0c0c5405440e505515040114500038101302d41e10301d001c001101100105c0d00400707001d54052417269aa900c4900c0044118401c080508002e680090081054555030241550304940c0d92034800f22107540e9003d491801070040f083d40b1a404010701084080c07102c415030180811409580c4100681929028040782134001c040040e5880942042001e00e201d00c02d00c000d10500c0210782c112814400540354400c1643c0042d464a4001c0c00046070034019581d02c034202455109007070070403891904000100f00d0301c0303074500039500c1d9005481d41100040301e8400d40c4200c0d85180c10280441c106a1a44861a401804520140e209128801c00030540100c50700c00c48a20960078404103da28000c9040300c08900d0721114031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 132028138 1250 132026888 132026891
    0x6010e07110102041d011502010b0102100b010e04090c18020301080a0615081f050105010e031002090a0b0d05040201170c090d080c010f0608010c0906021f022502010f050a081801 78
    0x43d65900740c4000e07a85d04130600078070304041d8140050404030f50200c1c8100b0301160b06240a82513141d070041142c0900b490440d1002c51004002d03001601d0703150208841582244c0b80510030028010094224001da0703204084c0c1c80280004441d1920a83c0028000c584d0290885601c050025103030768000c4601c0004e04d252440c2c0190344240c3c132402d03e040c950082e13040ca0800714260f6942c1c5c1749840b9207400340c44242802e803070400405001c243da9055186100307000030340c0040d0109182d43d0700540b5500a218989040f662200513980c5c000190a00f035030124003040400705001c0070fa1000c2d502d0188511900e0b03410743d0600c03119104000203100c600c242515004c800300825108d02e0030a0280518900d0301c4403002ca02d1074034025445003100c0503039441c5820010030203400e101480d80810008800c5503214400142c03150b04010034002841030007036a6190688107044008201c500442503049a4000d0702c8440c40c8180c0118140c4507489600c44400010300170b800090701000c035010352a000320045c03000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 132029388 1250 132028138 132028147
    0x30c1c2f0924030103051c0815010309030909021308011104060c121b050f0c0312220503031611010504031104050703110301060c1506030503090904080706020403060b0108060306010e07110102 84
    0x9242c01da40203810035602508090b00c1c4441e001402c05d85031210f80b801d0b1501074072900d8445940ea4400036014040741c10941c07a0361214060511506141020b0102440e086503200381000c1e0b0100e4075056481845001c0d42030012007201191000b042c1d40841342203880f401080031880e916030884010b5115020300f0f000c5038003640b41c0d2020f030388100d81081b144520010224071034283d84541c42c014181c0207982c4681c0c4120f0785049101c2e101d006480240b80500b502c58440c2c01440701c8042040d02a03001150188030205082d1094a13030310403a010005d0041d03c032468401d040c1401103a040c4114080075100329510b4441100c0c6040a90040e64004250b140009850f03400500700b0000740c0c020703030040380095001207054007813010503446032441d039209000800c0058a584d890507140d0066000c3c0034401c001d488002401c2c014007004aa1203507a010104540e955128038108000b0301940f08890700051460340042d0aa080000300c2a0503a2450a44400c0c5540c83e24030480e5025030032901d09581c5d540910 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 132030638 1250 132029388 132029449
    0x16051905030307080f130306092001120e0c03030a05070b0c040609031e0212030315010305090606011103040e100905090118020603060402041a0403021f0e0105030c1c2f09 75
    0x1546c0c8051840b841022800b0480350a01550f041c10915503240386824402600926a80111020540440403200414880c0000c0b4901d030030820010110303034140c080040d20940d16070f440001044424440d140031285500c2e940e66038030417802240101804501c071000188041140841e009082c22007000e07d501e4840c401d0b0b408500004c121107150122984044184003c1d0102c090003062441002e10b0104011310307203503d50a6403128050101410b00100c07009070300710a0424011500903002a03454440c0030305001000c4810504140f013040720705407414020486050040c0180d15140300c03226140800c40a5a40030030200e544003419169000e0727402c210000c0c09000b143c00d0303100321403180076560351240e145d80107200d02ca0184c100d48081c2e17504100c944002d40768005d2900c60004000380307050341e100d0780d40411400d0f1600c20100e20b4603401c0c42140c1640c1c0c40a00d15044501c5109014110071200300f8201c100802c04407622071a11030f0240d00344800582d508010070700724181c0c4030f00301c5030010010030380 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 132031888 1250 132030638 132030667
    0x81b0f03031b0408100903090b0f030115020705090702070905011d0a0c0e030a080309101e0207030201021606091104020a02120904060e01080604060506180601050901090816051905030307080f 84
    0xd0000351105d5240c4080c0414076402031008402009003c001a1803d40c1c4a14200c40e50b1205002c1c100c4c0e440006211082490720030031048000e010040c2c5195041c1c14054800b030b503114201e2242d0408581443d0010a0100b211078a100010304080d80c082d159484440e000c0c00906510a0b0755010803c601140801603a81080300d510340030300902c5110b559003040390707200d0f013400720410410b00c0850420064a145404500814910b500301020050f222806403030120301901c0b510040e050035000709203600c0c0030310086a0065035028030624040d0808400e11040c07000b079005180c00c000c056001501842c0d2021112801001d141130000d00001e01d03551141491400c0c00020303080000c1a80c400010801005440e11072280c0182c02121040520a1460f1241c0b000c02c0d00201054100b003008208004d150f401441d1600107400144280c5e6840c04006005008035811031103054440c2012585400b0405000d003e020140d442c050065444c00482d80c40341e05c03056000043c0c100e440c400420040c081e51440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 132033138 1250 132031888 132031903
    0xa14031308040f1e0807030f06090b190c0e09061c05010903030203090610080a02130e010504080d1505030a0f0201090f0602010b04060b03060306010e0c040e04081b0f03031b0408 78
    0x9540c3c0e400800d420801c1441c840c005403082c03c803950706140c0c002e11060304001180402ca03548030f01041e40c0400c507444c206c406803c000c400140640203043c03d000841c00040c14000c0c0c40300c5c10880c2000151580002140c03402111181240c20003003020104400d81002c3d5241c900e000500c0046003c0001d00350b581500311100c640c01540025400310901071100c00c240121a04244024002e64145042084160f00c4d1344030720754000d200f400050003084c0fa9503d941c1000d400d82460000810140c6040c0c02e2612140c1d003e02100340a4070b103401101100c28045140610503a08050700910003c045036035140f02c08400003500b40c1c1440640180003440f94030801005001c3d004035800440c0020b10182400141c490603040780740c80c090140b080040644000484a04585100d0045c1071941c4540030030800d24800c1c0d801c6065a44d400104000901098400508982c41c180280301c40341300d112607115071290351050305040143c0007000450900e0f080184000c00385022001e10b0f610f0144d0381c2500c185003144 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 132034388 1250 132033138 132033149
    0x50303040c030c050916050a0924080709031113020903030c2833020f090f06030403020d05071118060306070e0109171617060603030a1403130804 64
    0xa01c1070040c81041036001816000381029600c1c0d8080e070a200060340742504121007860101300012580030742e101c1c42104003c0c0240941c0d5820303803020b14801d0080151b0002000c01001040720400442e07002403107148200102ca4008460b10540c1540c2d00420041d5128100389001c0d25409008901150b83e003800200f14620701080240100300b0b04001c00841c0b00b044070720011449180c440b2250110345509c0107001550b424070341d01c804040341c0f00c01d01011480b2074281c151100340f005ca1040ca001e1a580000c10924000b00c4005410301038200421545210844000340160000c40070704ac0e0040c0200d0142031740c00d1140c48410081240840855060403a9540711140550203906001d45c9040501107e500f08000d80f0302000e08900d2240060140c0c000c5100340b440f4441001203807142407d00b80040c6206d40b1242415205c0c43c0d940e43c00c01c040781d01c400d0409009502806001c41c81d035250010072505101c0d115101d0080d41c071480404440550401401301100c0c421101c80e010000d980d20004001820 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 132035638 1250 132034388 132034403
    0xc0d1418010c1104150311090708130f050609070f0816050d0c0905160315080606010c02010507390f050f03010e060106050a0f020c060d05100b0d0b100804020d1101020a05030304 78
    0xe1550400030748440381001c0c0240286235480922a50301d5000c001154003c140e22030004207500c2c90300c2e202d4038810b00810080e0140c05240c0a0095403540810404100c850400340c200c1c60130307240c20702e0b03070b44035544400d0151000030359000400690522406000000f409045502100741da504c03451f40c11380b5821140411204007544820740303010340501c1841c004400b11365201d14224100071101e0349c1e5010140005051000700c80d480c1085a128004803407200ea807002c554107042c0c005ea02001803802c1c0d1415460901c9500f070320304d84060201c0c880500b00300c41034111200c4005103840148030008d4030300080c40342c165484011903e910401001a0741c02040c280e6940791b0744058104008014000c880449011508135103280d0071300341d4501082d100006c510f002c0001d180c2e150b0303500a0301c0080c800d500441040c00702144190000c44594030400b425242501e6074940b10b0b144400031039150b603007154001d5200940e0441180030512045c580d0301410818012104c844001d500c4052864100b15821102030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 132036888 1250 132035638 132035681
    0x70813061a151201180929250c0201050d090b01050916020a061113060809060f090d4d01020f03040f170c0d1418010c1104 54
    0xd0601e03210b4002c4220403100c603903041c03400300c00f003001030041c042c4188144042d5903814240e65150551018480c1680b0070b0110149404010032141c1e9882c0c40248400c500101c40d00090149030720007140d0b03400c500c01d4000c4440c0c8034420f240945560b1345da40c506a040000c00d000c02ea2611081d0b00c0303041d002902919501960350704d80410410201d40080004a440c4102998091103a0300003501c41c100f03960060700454010301d014240c0b00280513401e561724014001030740c00150a50484011341c0100700c1d000944005030b8403192481d0011000780c0b4400e000303612003c0d807600c106204402d1319288a200400707803061590a480720140700b1002c40d000c0c0020414040840c106589a038052140543e20315000b94102219000701d083c10340030080010f405001981042410021480030b040b2041d1050864591180d20110610761f403409034495600100e256150318030001806a001d03100d00840802040a41d03400c1f135001140c00315525581160f640c580500d00c02d907296510302841200c45d6a40d54080c281 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 132038138 1250 132036888 132036941
    0x10306112110210201030b060d050f040605090a0f030804031206090209210a08030a0207050303040303050a0e1204090c1e02011e0212011203170f01080c061207081306 73
    0x4882141d10000018044900843d0080c5445a022140ea0f0302400c1c005003403ca5034000ca10948588804031038250301c1c107810020002c4002200b03034011405007404010700c0c0d80e2107900c0f40d40e9850508010303103212a02c0d000400040e1040a580d94070510034075015011009407558803060320000d400c494502d0750045041c065604103690412150561135620003007914002c01d1413a00c039003440a01404070000000003a140909030b03011111401e500200307c03640c07445e080c240100100300c281c1c5c9030b075606030411126074007086002901d00014500040c00030701e011f180004034070050100318150803d00c01d1500e5080241c09003000100110301c0b1580022070700400060447d101103113a02c0102103914418401c1070404081014802d041d200d10107141c84030303201c0906080d501c00c0300e4402030183d500e202e1010402c885568649860407901004121003070340c14000c04014242c0074980149040d11a003030000f4410a2107000d0058108504044051200c5145e0311200213070740580303074126018407526410800c1c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 132039388 1250 132038138 132038161
    0x103050c1801030803010b0304080408190606050409050d03050702010e0703080a031b050301050112020c06100e090703020303070b04140a031107050607050a14121c0b180103061121 79
    0x1010a40ca0702a09007560443d503d10860380010701507030307a000c07501000050810441c2c40c12039001e010600111380702c0381ca80d900c060112401005003142d20714145040000c0d40d04140c010000a254010090403658040d044120010803005162604641d220001e015402205001e00009140110200741e41c8104003440503068480c105221008059101c454207180e13130303001040d07a041d50000d01e410f41c10750416400a030040e0041c03100160103406150240120300000300b050a045030901d068030b1545036a154801a01c0d06aa072002030b4058100f005050006043e0b486440c0e44184540012000700804182072480d00100d039001300d0101c0e44844d12801444020000c1380020142140d41a15000c0d25030348240c0c96008110b402071030100440181d000c0304506001407440164041c80c40380e03c0b1118580741191200d0800c8180d00020314006406c0164180032450306540d0107100250300507039186607501401408801410407280c40180710300712000254a940030340840c00c1b500c010300d407070401165181c07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 132040638 1250 132039388 132039409
    0x40203060606040f0311151216020d09050603060d050f03031e04030c0605070e22050c0a09030b0907031704170a0201080106120b040207350403060902040906050103050c 74
    0x9120703070b600b8001000b003001941907003429268800d920300d054105500c0030034450b620a00020003561f802080d10442404040c000034820070400701c01640641a0b2141680c855450211034000140111828000c44c00e00d5401181c00640243c2440c10040726603c03280c0c1090411042c1c41c0c5643c10000512086032700d00c40505041210b5200c6065590800b5940079200398210940204025180d1002407a100d0141301f11850500010300b080744096001146407820088606054440c0303032604001c00e01980c2e000c030a54201d800b040d141c4102c01402c41d20b40d0050000d009060b50180d10a902000c8001100b1034a000c208040c1d503070fa6562100d041403090a8101110045c4809641c804100311000d030303078802d031001d0440d00c00f030070800340b034061111110000e4169002150740041c000901c1c00100010300d81200000541c1070441c8003003500c19174009601d02012490b20381e42010030302050000c15541e600241205200400004003082c080e41c5802c02d0340d90983c02561650041c00112003103003003005091 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 132041888 1250 132040638 132040651
    0x703080a020102070b0a06051e04091212060e09030403240c0e0406060206040f060c11061e061f210e01050405010608121b03070503070503030a0c0306060c0605040c15030504020306 79
    0x501c807e60070200820040c10801c0d034050042240c1c1003204ca032503112a401090b026801c45080681d120b80d004001c0d06501905c0c40d07161800d454001c000959118201c8250301807c41400954900b5255442d10b05c502a0360401c2408664502c0c1100c800c4141148518043e0400302e440b40d044004144041004681c6198400b10554100008010028954225075048903170302c1400003440207618001101d03020800e400b01001440b420052001441141c00074042180485c410000e06541d15000e200b5040500207140c40d00442c3d0b00e403156502406080c040800e101d121a100319030314003003603505058a44030030107100641d40d9841400305000080c080c0001400c0204000c10b0542203003000a011071160f00b60040d04640e48406212030341106100700d90009800104a82c0c1301c0c040e60502549035807041e6100c8a591745001c903240c1e1660700070300424089600540711486121010340350b48000e40f80013041243c80003c40e07100407402528240b0380c00310404607030b0781c000313294a085c0c0f061510380003002d842d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 132043138 1250 132041888 132041891
    0x902040302092e0e160c08030f190513050705010f0e060c010f02070515130804150e0a0603090308181c05190c030e0a140d050703080a020102070b0a 65
    0x14009a1584500203811150308075600e03c1d0702020340c4001da40c41c20a0032a240006800600004070800a146810b000d5500b6281020054004c1d00050303908015800d4020031049082c00044c004407036903080580d015545500c050902550b04442c10700f1214111a8401040600001c90040c00700030004040030701401c0c28403124a0985010103071120b242d2034400703841808001040c240401003904555048030742042e041d500c4849624000752a01d194088040342c2a50358000a000151802c404400382034114084900c0c1c0b0b0b080c031001c09440b8400208103800d0002802070340c42d45441d1111400010701003940d002130041c0d094a0020500c01016010061580c000c10742c90b00510400726401250f08a032180c417520f4640c0c0d40c00300703403080e0085603041480b0324110a030302d0080540001da0340c41c03e28825540c81d50025100020086034802074011071b00b011164030504007103400c02030540f40d034040c0580c04655115a483d541e620071981700c40c1450300181d4012031103000300311400c00841d4004004240 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 132044388 1250 132043138 132043147
    0x50a05010f12020607051e151b070f0210030c11010209061819030506060f0d05100c050d06030c0503060601110c0609011e02010c080711060411010314090105070201060902 75
    0x3070000728000d0380100607800c8509208141155103090440301c0c030130740c800b043c0c03403503140848406c1c164200516001c0b0345601030200f196002c0205900d0b41ca2040c03075503991103507940d01d1a10103c40590041e801c100c0714460401000d001607078030305111029211907540d02003103001c034822008045501c0400c400045a005010391010b0f03940d100c090700e0301c0203500300074200f045081c88001007041c060183c00180f003c2e038046011007804404100c0d80e204032415680134030b4810340101400b4100c400840090042d40150101c0200312501344c118a04820700c5142c8241802c2c7e0782100f140450b00c2c0740d8811034181c00701303010800c484d042c02c2c0812507100009003844903c6504051701d05868100d1452814071940c0d0004400d21240c0c0140d019800d1400611640a0703e1901408040e008101c06108000403401c42c0c0c0c00241c03094441e02c18510081004405410f1a8456a1725021100001802c1c00d051503290140e854a00001c1420244500e40c0f5130000710340f90508034006400c40380b084d040340307441500401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 132045638 1250 132044388 132044399
    0xf0d0b040c050d0c0e10050d060204030606050a06050d0507030e0d0801080613020306010b030723070606050603090709020f0c010509160b0a092601020c161401200a0501110409050a0501 81
    0x1404d4000c03628109140519592802254240100300307420031765009041074104401d018459000c2c00a0301d101c0c00d020000643c981c0c0801c140c5583d148107040000e101004003040c00c101581000c0d801c81001c0c180405e13000c081c42d01090078107511504032030008180c03c0042088507010031481350400e180392034003940c10391581c0119449000501590030100030010100da0807612801261201116907011416161030102d64054a43e0208201760f500d90704202c804070325850100d0072680142245001440c2030341c9402d012a010307400110004405010500034501e9080c028011b40744180101c1c4050614961072000e03502d940800382c0c2203030030460400d020040034070781c21400401c02e072080c102801868002d130039825001514212004040d5500104103d60200d20014900e58030307142200c1d031040c134561190f1094141884d030009a6001500c940480807400120400582080281c0006d840c00502c958850509540c8401041c030014a00050100300500992248540001140d8001e01580d450032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 132046888 1250 132045638 132045653
    0x182c1605150307020f030301060f0206060a060522090203090a020a0e070503070c08130e01061209021c081308030301050f010c0507031502040906090501060912200f0d0b040c050d 78
    0x5001d5151401000804a18103038000c1112442d10180d50040b65560360b1505001407962400d04151302c054803580380850201e15200d2101019161556501814200300d60540f80c0c12280d0040c00c070011154001010a88081038001144103054a0b0014010044148103204000100703034007048031095600c050140f050b600030f0480c1d0304032501d4a810242780c03a59040c401c1c3e941c4035225003082604150a400a10302c118484800c0c101c0d009a1140701042d10110514016140074010096022144d00d86030748580d1800c0200b80c444501514409007041c416100300925842075400a060540c4003000400641c50070a812400425003031800040d5444255a402d41e00d2801e03010003020341d640701180401c14409603040c0ca00420b50400103000080e039580190004040038024800054124400401d040a100411107d03050340710800048181500c2400d00782800b100c46000d52110046420740c3c07841c0d56454400100ca40150b9444400341481c4c54061006134840d80301a005070319903400e140128860 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 132048138 1250 132046888 132046909
    0x60c03120c040f1404180308010503010e030c150702031e04030b180c0f04020f0a031b0521060402161113050606180d050109050f0105010f050a182c1605 67
    0x10030b0300d52005490620b0004001e0f02c1c2080724582c0e05000c903d03081050550102c581030407a45cac180c00130805c140000d18482d0301c910030602c00c0182a40801c0040d4010003d12054541c0201d03584140e1381003505044032400b85d4030400303002c68204040030800b403040c0411001881e0f005050400c9030a12b05610014035034652202c0031149224401d0381ca01441701d030700c640c2c0444080b0080083c2c010b03134801701440040e004100c01c0c1c10410180842040c6099014010421140031203400007092862800940503000c4401c1e006001a03001030702840324428203031141c00700181451060340c0e0581001c808000f84610110420100841c403810002030003c2030701d0300c03030403200d82044074a540e080d030720740e1a00401c0c801d900b2082c00406a611700700c0421b0501c10049210400d583d000c00090156076600c0380c611001d1460390145d141d20091800040094441c1e1020360144180c1d0304101203408691003004c1c4c1b13100012842a1583e11418000e1f25800450601411210ba01c641042d84416402c1101003900b0008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 132049388 1250 132048138 132048149
    0x110f0609030c07050103091505091203100612020c071505070606061106060a180906020f0307020706140c0c061b011d010b04020c0a0b0c1611100c1110030209060c03120c040f 76
    0x54820108424a40600045840301c0c0bc410300c042e501d00301400d40e00c0b8102c05500c52140006c009900a08059a00d4001c4810003c0d10000410049042400a9550111071556181403202c100070100c0094201c0c06a1001000ca50b2100030303010450811460805c04010b103024030406220405100c8400032610400803400103040024803281e072032410000a00c2020b0703036850703094804070070041d1003680000c0100c207413207440d540d10b0341d101d40391800c4088030b0194014004541d00701729154a141d046c0000604042c450300380341001c000150354451801c644002415080080218840c42c11543c02405210800c120035a130851a241255101c9034403036040010043c904a00200441c0c20300281c1d2095800c1c1006a40a040b4a54074901d40384800c040c0b8004180c0c0030711205242d902c00c3c3d5004502505045070040200840180080c4c2001452000782c0340c03527410305900340314a1466441301005003264140400081d90798030031490030492101001854450b40b8202003000303001d807900640800c002c803030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 132050638 1250 132049388 132049391
    0x12a0c1202010807140702040e0136020904020409021216080d05030105090c070b07020109030e0a0308030601080702012003310f050304090203040b0f0606160201110f0609030c070501030915 83
    0x5c4208035044e020b2060307820180d071080c208800407258074410343c0815505103c180f5078422a00101c21107817070840c540141065200e80d0102030303501500304030000e10351207840104002a004410f500051468008012604040c0c1c8007080d12200900c1c620500c9020b012540002c180040b48a0002019071005001c0c0074020403201c80400c83c00e515220a5940250303100040300c00724584080c1c020300034540d0500c06e41c0000c90308040244503082100071201a40c0c2c000200c00d00c1c1d541c6640040d102c6900c043e03e090210b41d69081094103042c1804610414401107155080d0b89080445035100e2111084c51545c0b40c49206405101000200e40d03401840b480e4000b0000600001c682030071400e6000d56405100c48500000c200420095503a100621480b1041c1e412682e03511b441007030040500401031061088904281414050740c003541c05000380c2c40c0848100d0304030f91458a031840c00e002060f00d0b20a020750001c03401c000b03015410b01c11080600400c0c80c08200200361502c9012902c0101801d80100b00e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 132051888 1250 132050638 132050657
    0x3030310060c1104091401150b030103020d0c05060c0a05060c13030f03090810050103051b0102030f090f0406080d111609051e150307050102010b0a090b012a0c1202010807 75
    0x40f000c0c605031603030803c005008021011103401c00050700840d48100183c60b51a003008900d401c030301c501441c81035030584200c05056a00399030034450b21003056031064035124902c8000103490b0b0b46081c014600c0d1110100944051045407910600e00400038104070440e403018804120054801c040102c1201c1c6c005109000911541c00c017551010140d400407580c0b8003841411221900032a0842d078100c038441c4003252070046101c4806120f1804100245005030410030104a46580000280c200d10400a025524082c5501c0000b411038840c2e45c0440ea485e0040084440c0d40c81c1c000001812810400303018282c0d411035041c4008268001c2c1c010701070060b82d100080380d101503003216150700740300d8205103072805401d080d50a021704c42c0f956240385210b03108d441004202540b06000da02c6121201809035101e140c01c04048a029200740e0301024100202c0e090908000d4040b52040b284400013005200c01481c0d050402480280994100d042f003401e034500c1400060340e202e04c07a10b82c4001c00d4030301182d46 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 132053138 1250 132051888 132051893
    0x2100512010905010608010509090d030e01020c0303042303130303180306051302030d0e1c2d02030111030c090d05070503101509050105030d0302090406050a090207050c03030310060c 80
    0x59000c0d40800804031400c18001003000101548140e050750310b41d880c3c946860b03a0302e00030007489850454170794105030012001110b101d1b010f03420850050312440b0000d401e004003c100a07186070811982565122440381010302e00f0954040f10103509801c03000030f1842d0070300c569201c0410401c203100060401803407044080d034003080b100800e03019613403001d000c2c001800c3c08072251000802c600c0e000c1e8440d000340506040e20038007586207083c00c0b05c0080c0004d0341c0c0e2407500702c801c03401b0701803420241c446011b00b4004101d00740d400d6200d01d000d01c070700001c82c4000a0302c1e03005050031680c03c4c1045004161041062025140c0f9103400e8a901c0305044038043d01c1840c50745049802c10f20150310458041c410201300e080204401c0d0041c42c048070780715900c284c83e01d550300340b070b14203462080c4110740d05500100c40044019210303030006c0040d490058004a0400e60750ba003c41e00810482d400004031342c0d4081a00400c001c00cc3c01510141c01c0114000c50039420006110a14400103114140038028404d00c020304 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 132054388 1250 132053138 132053147
    0x40206070803040303020d0506060405010c0311070f0e1608060612040c0312122f1e1305030d0201060e061c0f031e080112060c0e03010f0c030b0a03020d0210 69
    0x4965200034225120f007864a8094044d4002000d081180c6040c00000740c0c0c1418a4001d403400c85205940b02c0e601d52000303840c10340300a2a058a406114001d0b040c010440c2041d12402c00001c0c070544452244074601100500003100d1441035400410070003000707200c80399031a50265010b050400c0f40340d202c261103500e042d86122809600007001106900a1800c1068000010305000411820144100c000e21081d6420f440200585542002c0c40941541030400d0100003412041845031000012450042040d40362034000041c4894060b481c084103004a0400f400328113003c46490000740003c5040c805081018a00101a28050b00d60000d0032000404a050041c07000c5401c502d81e28032811160400620400c68003a29400c100681415031000d030b40b040f1806812907203007403007d1200f4071a907070700e11001d450900301020401000364100380701c5130340c28440c040403003d04081c00600126100009405d0398801d00071a441500000c104002680714140c504100d154101d80101c08890f01c0c1030150b4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 132055638 1250 132054388 132054397
    0x17030a050c030c010c181e0303032301290901080a1503060f0603020a0602030703020c040507090810141f29030c030f06040902100e060d0c05120108010606020312040206 74
    0x40f19800c04404a0728141c200c200342401d1303940300d1059061640c558159282c2c000705d0122005c0302c911002802c001180c400e60080b8410804468440301d40b00da00c80d03080c62001c0080c0c2042024840f60f00c034401c0142c2081c985130310004501c0f580d20742403516401c0081c0500400400303000c6a961076900b8110240c540c503a4850245901810070413241189248100017060300740002ca0041010700408200107000005603001681d055006200301e0b081c44d01880080c1801601c0c810512003030400224141c1400c0c8001c00e003c0c850480d000404114092105030f510001400748a8410401c11410240c0e0144c030b007031a005d0fa200e0f2072000c040c04c4200c801003502c01c80c1e864101d0340c0c81c410200901940b00981c0c00258050b00030585e498000d61900d40c00c2008440203440025030151842c030340c16000d28021100c4505009001f0601ea050840304805034050301d03d42ca21002c005000014241d141440c4056176602509010000b00926030030940c0c0039649100d002e1601180c420100d0024003190388101c00c44 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 132056888 1250 132055638 132055657
    0x100e040204080f010b040609020301150c150f0c17070507140f010203070c060c020309060405190302040e2506020604170405060a03050402130905060a09051002030106170117030a050c03 81
    0x2106060f5000301e0580c000d1404101441c0b00e40d050510004c4e1074030250080d00c0c1a5407450616030311080c4014070540c0e8550340010129110101407484120032180c51189001880041501003441034000100a100042158101060b0182740c0c0078460303210f40c068145e5045580c007010041d051074070781c924545060421404071045600010400010640c02180406083c0c0b090f24140b04032884100207986074003620031236a41112007800104134078a040d401e200d10710b02c052144192011f031a500464192a08034400e004550b02120004032a506240c109410300540460300154450030100000c2d1075020280000d05000300124880c0f031144c1c482d00840c2d004001c000d0a5680d00c2d004c80c54040c016042c1180c0c182c0c402e884129510042104c2c60180d218442c0c2e014019000950b12258041b0081100c0131040d40c080c0701d4010340140c078044620046018000345e4940040c91507940171000701e461030507049082003207003d01030640049000030540d0660215820036035101c045581e04a4a1030041c0306c1c01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 132058138 1250 132056888 132056893
    0x30a0f06080a0f021003060b0f070f05100608071202060a0f0212070308010905241009050a0e0a0b010f0903020405070e061812030903250302030d0906030506010e100e04020408 77
    0x216010040c3e403a841e285094030a540c0000001d54400b03095003160814401e65048483c1041401c2d1410302c038a00a00c0038500c00c180c5d1032008000c0e034641d10b241c80c1071810058141550b4031001e101480b41006544002c2c071351014000422b0040e036000c14601c1c000d070a4510148200d2410802c400360007408940d80107140303c042d00c3e484d00140d040c0182030850a00c56400032030b1400000c19070b5844d11000c1108810744448e1410601210303103050244113482400c41e4030402c051040081341594401031b090009081d107888034003580c00e02e02101c1c1c0450390010090390501182041c24424a500500104106c0b601110005a0390343c491009886144001110a81c0032100240100b204080310800101c80481510b02d1480308105c0404030307550303118544286500d580450034a02404241000c40005603500180001c0e8080d078030f5020074a0400301c1e07030700c600200701001818050b041c0e05219081c2c0c40f417000d02c0c010700f08000c6100451000103030b252107001001b491400e0074a15440f65011940213000c0c6104 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 132059388 1250 132058138 132058153
    0x60603050a15050f01060c0201110111040305010906050c09090c090303070b04030807030509070627050612091203130803091614090906090303060d210503010519060203030a0f0608 79
    0xb4400700c44001411142d00e40c43c5400e0104955000c0c0543c00790503110651103088034810700703400545038010f00361480c1035150340b140b00d0010080b95109c003034801107220380004190150185480401d03034400408244031408244a041c01954031405000e410016840c2019661080b0402080c1544921600036103080301002c01c0c001010780c022075083c0f2404182c5c1d41040755846c1c4c8500d20b5120002ca00c11840002d5400d20048001c04144418500b81c40502c1c0004d0034190342d070b4001c074881d904203900907400440c0070810040d01c8a0107005504014003400b403031900d5480c01003999030008100201c0500100d1000c00003400c11041082503241c4803001400709a0810707600c2003c141d0204000c0d009502039049280860404c100018200703018410100140d030031a40c4400600c82c0c0c2c0350008909039034401c451548040041401c00028210b610a991002d03600d60501c0306201d0031402400604044c068104000c0001c2540841030320341010f80400041060000c0d0030f05540508a550050a03440c0078008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 132060638 1250 132059388 132059393
    0x170a140a050a21090c030203150403210608060f040b0a0507020a06020d0f060f14030102070b0105091308070606140105070b010b0a0e06041706060907140703031d0604020102011a060412060603050a 86
    0x5240c5c02182d10031001c070b5540c580d0b00092242001c0e030a0320b004007c1501c901c1807441c1126800c4c4d80320488022900c000130260b03520449245070410907105c11040807100c000748000d00041820055204150707040501003810401c0c002599000e90300d902030305181e408100400b1540380c642245103002c02400040c0030207038a03071f100315044181910544e140000c041030740c4001d80c103060094921080c2c028045161580c030348428080c14042c0100401002c01c040400000010007103009021040c0c024071000070000d0500c0701400409603a640a076040c0301051140384002000891100e06407545010083c0e03c4031036000007943c1c85c410101c4a190b0040e80443c000c209580300c08004030302035126200b201c9841e2503440500c90171180950318240042e208100990500d60441d0091070307124480e10300050010060b01c014400000302e4482c00c070040d0003540a0206540c1c0c2400b4000c0d0a01c651042d80d507004403100005239062007684a0008131421000e4100103000c160b502101c000c42d00101942e03a043c400e072 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 132061888 1250 132060638 132060653
    0xa03120f0e0d020106090c0509060c0106030b13021c0503030414010e0d0201090b0709080a080306060d0903081f0609180e0109050d030e03031506090409170a140a050a2109 75
    0x11800b41c0040d807a0400004400486004043c0d2041c0c454403800d00d0128440e040c1b00c0540c1c81503030110350541d00c640e000030000c3c0c1c184107240e20401c4240c0c03449544650520400c0030401940d00d642010030741000d00a40805c1003c000c584d042031380702d15140c000b48003081d4071a01400345e400d603810799409070800280100b501174014801d038030302c0307614020159507402c0d1050351901d030399000d0b00549500071041180018510402560095802007030142007d5010440c50191007450a04400003150f0030140f00d4070040301000745005a5160020742c4c03106041000c0180071800c64420b0303d0021130704609001c100c0420740e1040700c3c29495080244400407442c1041c0782c0c3c0300d044001c0d40d40024900403481341211000320580e4000c000c150440d0740320942c03480030460160026903855a00554414108000032041a01e007410f03140340081c803d8481c1c50301000600301c042c9000440403202410003200e8035482e0301204940c140d80b030300e0603c4581c03155144c001c8400c80c00c04800000b43d0501d800d00741e50610030342c1e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 132063138 1250 132061888 132061903
    0x1d0703030207080d140a0c0204050a020c19020616030e0301090303140108070311060304080c0a030306090b0604030f0b190c02010516030212010b0c0c0d0b06010810080a03120f0e 78
    0xc1d001c541016036151001d55a86600407030800000e4203c400072095907411400508407050546410490150550005402c071a0280c40040c41c0507400035a84e6200a400e008032810000411390a494485568001c2001e038454001201c02a1841515000c10180540c000e100326110103002040401540d1401a00601b540080c0d583c450304004000207030740600081c02d00580b9031003005020082040c10500013584c2010f40100c819040c20b0110241c0c0650030003864803201d009980c042122031500080c50300f22409070040901801c4100014404101070b1191603180c0ba611032031016060741c9041002c060001500005003d842c2042c1034500c906038150005805280051228020512a14400d0b0102d20960740b52020410103c1d0040210a04440180c00c882d03001205881c0d41c1e00d00c13100092050340c218030046400501c1902805520359222840650040c65031004088490130458081d036102d060310801420040322480900c4205d43c1c0c0e80002030150031040d4180040388407170380d8a5886611 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 132064388 1250 132063138 132063143
    0xc030c03030105010e0303031015030b0402190810030f0809120a0f020a060903050d0e01090f0905150603040b04060f0f11030403030c020102030c09041109090403120f140a0207061d0703 81
    0x400c40002400c0c0d00c1c021041b07070300801c030744542c00844c0f900e031600c6c200d001cae40340c28800000c0c1507686510441a841e580000c0c014114202003880c243c1c0c0510401800109000e400031408402d0000d05100040b02c04030301201c1c154000000503181c0900d00001100c0820100480282d4012003c1e03140802071116240000300744200c541c1d504280c0c81305401c8848801398071001d80705901003003514201a001d00040c60980c4018582a4800c545880072440801200d5001c841b03195a2078081001d20452001d0541c0304080480d12603245007000e842e8200f1844002e4400707081c0603920074a01587d105d85600000d100380a001e41070110f81300810788020390713410858003500880d00700303500741010500c1031084034840c0d444202039506202c418400d000041640025201c442e80c0100038456003a034a0640d040c1c8a00c0c41b0303135111119003209201040c2519499040a030700c00c0d06205074010b41c840c048404950020002c1c000603241c0029007081c00107440720743c1d4580040a60742c40422080b0901050000981c0d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 132065638 1250 132064388 132064397
    0xc0801051f031b0902040f0806090703020604061b050703030c0515061e01020a15060305070e010602070e0901020702040501080616080c07080c12031504050f070c1101050c030c0303010501 82
    0x40d100758009080c241400e0050092a61041050000034049034140800b26003010541e1045515001e0010807030b8002c2c0c105010080e0008130030800308004100241e840101d44001d421010701d5940130420f41e000e1409680240030403001d5005800454403005c1c001a0340010480d0319481c2e803410090602c1040c0c050507a4280103d842c0201140e00c000750390b90148601805001c1c03095290589144024100d0b58164110b0084a020300b001c5927400c02c801c104036080100000d0b0040c69464580d26112540c1d000d024000d50420042025070b8011540700203c81020074401c400e0303a00c0c0c0c87d01c14024402d10f10b00a601528000020030301c01e20016025201d0061444000d280c46150181079510342000c4441100f504010000c460001e0303004030103401d082c08024111818003050101e00c03000750f00200c55002c80300040510340621890113004464100800a240b2031450819800017480140c6441d4040c05c0c0c88500548800e60f41d214000b19014038000b10140e80d2242242d101c481e40300d0f03100303110b00350008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 132066888 1250 132065638 132065641
    0x6090303110319020a02030c0a120e011404091116060f0509030f04090914060408190503060916020f0a060f060515190e130203040c0608071d06090d0c080105 69
    0x1951404200d81c0264103038000a443d00d1000480f102c080e5204080f10707030071804103100c0790200a808210110b46607102d8030f50082038100107000100008000080c4904100c47d08480d05200e18681046400380c400140300440d41900b45c422080c5144568125408144641c0e103030380007400300300d500500150b0142d501c144a40c0d156280810b99a010b100346d2080e890404110400200d20903500c10040c86104021045045d9005004981040d07021101952030180000703000300b14642c032002d041d00241160034504c4c02c50134000d002c6103810b08010304144d580307548008000041402045542d03284080c110859a86843d2854900b000d801c02560148c21a801c20710301250702e180a00485c4202041c40359014140504001083d2080d13007000b10f24410b018030409104090f0700d034114449034141da16a40503a40c0c0c04c003850082641c0c1c1c2d960b4403840030414200b05100c40d603a030140040c40740c040c98500c0702c07056144250010701d0034860301a1160780100c021141000304186981004201e440c000c0080009 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 132068138 1250 132066888 132066911
    0x10203070809070f0509041e0b090d050703090e18031b010b0402040312121404060902091311011d061b0d0207030b01090507120914010e030405030601090c0210060306090303 76
    0x303d070903074042c150719242c2c010002c3c402401d090200f294031a004001c0302e584840b043e0215034a90100b03103003d440300b26100c8100800c80500304821095990b80d4030340303240b030441e00d6200180a9038403401749044000d00900030400000308046660740140d16401034079500d09000101562441c1c280140310925424000c80440c285000e02c01e54085a40004420028000d2340c241140c1110090a03d0169140e48181a07168040000d500b01d1244e4860000040c48146500411101c0d01000307003220b1492181059400c0002c0003006280b410010a0078190040d92540d8110005043d8070601d83d0b820800c0807516801e00e080340c1100903100014182136401c3c8900002c402ca0703d0b40b40c24040600f130496250010003c0d50510f038050b9900100c80d01e017003496504050f1000c0c040d181d111000703403140074111440c10031070f050030302c581c1010104040045160920745004280c03150350510491039100e0707403a0240d0043c03900900c09010716442c4010b0400566480340340c510014140c4103030a40001c5e1510802000c1b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 132069388 1250 132068138 132068143
    0x3b0102030c030405040b030316050d2a170909040803011703120103240c0810050a081207060b1008100e072025050306090a0804120201020c0a08010203070809 69
    0x207401c0d40c4018514203030500050001402803511540d0309880100801c11104940c0401104c6180c8103102030a107243c2d2029004050001d103480003e000c1c1c07171604020085e220360031603284c0070760743c0801403400c09180d0032441c030380c24056150540c0c0c00031200010041000810002107060728040890300c1d0062001c4404d450380e034000d811469a40807400801840410759100b021100e9908403541c2d40700c1500c28444044c166840c1d10049030220310408184407a4802d04141e40028100c1501c880400b1403520005a5540c060f0b900c5440040300d0001d40e0000780b04450701f10400244000c1c1c400c600c08400d011004055050480e44a4810800c40f503001c0380302e0043c000d8a50180d944daa560500980010000c0b41341103a05c05042c5509110310f6000528464012402404c0315040010044155207404185402c26070007c10310b66264201e500304c28001a450800d80f030941d480c50404080c000e0a07440184d1178001c50500595015456200004d41a80f0540045100c0e40c040e50f02d420313040d20380844159 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 132070638 1250 132069388 132069397
    0x712181205090a060c170d0c030c140a0c020607020a030f0c050103142413140603160e07050c060a0f0e0703210315060903020102060c160201050a3b010203 68
    0x1940207031034410411100c0c0c80340c988407120500566110440805004803015903900c2400340c01f11268491501701e0040f42c1500c11900488541c0c1401d51f1000e000d4181c0740124820040040d040c06488001c0f0029900e4035410350321003070707800b80003450800d403070b1700f4640c0046580d084103d40c0c4030040b44004c2159403207400303802004000c8032074155460315155640c941c1c40400c0f030310020b1129401440706609503251102c05c40c030960107244c00202414486100c0c424014010302690285e80400d120041c4848400c00d250121034002000c1c2c2e6558031614800c550310b1003a039002d801c162155105000003550036074411002c600600104003c10008442074544400c03041c44094500e944604107070700c41c3d9139a44a44a02c00030f03580f80004900f0006c0c0c03c42503040400d0781002707000411542c014000c41d40c0410070241c000001804150400c0d0190b84880b072801041d00e002810088046046403995010b1141d22484401c11600c2400b0354050003d6802c4200700c10404030042d102e8800306035469400402282c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 132071888 1250 132070638 132070657
    0x70905150a08010e06190b3001090908040e25020a0533090d030606050301080307060230060901140105030a0e15010e09070b0a0f03050712181205 64
    0x101507880d0144c0340303034405001800c0a400a00003900d01101c03185031154040070703214482e441034071618500032980d041450421601107074001f41c4c15030b50300740182d644000c1c1111844c80001ca5400354070b02d81030419000702d5000b80e40c240780e89410300100c994018884402c002005c084148080142c10040307944419414014010350009401880140b11910401d0400c8540001003402c03100c8406903446c031000c04840031141c030b40000080003611549030090300c2c000c04451070b1407070940d4104040e858603071146a00050034290b0010304c0015504038982c140c10a07002d4550b104075841103002c1e03c0008070400315181c52080a402c0c002189000264034261010030b010303910f250031542c84941000040190b554546454415180d460b4500304110a0036800381042c010745005608244591618000d199004510700d210188483e100c0540d01c0400c4d840d485c005480c01060a458403641034881c11400c0389440f40c0241004400380c41e0079950042c0f0310f8598802e1041000c50700b180d5034102ea19002e00b0703040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 132073138 1250 132071888 132071897
    0x906090a090816080d1b090b0703180303030c030e1f09111203040303090506040317090d050d090f050d020f0d061e0e1e06060103021b06070905150a 65
    0x200c0c1004005501414126208030811854080050484003003d80512400c562600c0002041d2005d18118099403c400c0d411841c05c0e14010540a0080c08840142c020601d4481d80403d03000300b454480d06560100744002e07251700e5640c540300d040c0100a0841c80000034003090400d4005080c4520001d207616007240c20a205048031119601818050f12400409880760030660b207002c1c1c103564801600c0300f949100701d0001c5564510714070340588000c10980c0402d208a40031310007000480d40c01e020910100e03d01881c0c4e1565030b01c5410020301598030354840035100784210083c140304213070403262100c242c402511038580c041d5a504100038580b1000c1c6402904074801c0303070b10040d5038245620800d01c003920230074002c90720422000d62000c3d00008119007a40c004d440e03202500c8149014418200b80b00b07031504500c2e03140f030210103d0030303a01c203000790100c3d04055000801803081d0940f0b40044240c41841002d80c1c05600f00341500a0640b8038900402c1c1c89942000c5800f0340e08802d0904445031419192107 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 132074388 1250 132073138 132073141
    0x100608060d02040f020a09050a06020a11010309050109120201020a110f100c20060a0b03150411011206090506010206181c0504050301020313060b01020703020a0b030a1b0c11090609 79
    0x5108040400e50402c90700325440307403000200e0b0076241c005014140b00c180d480c039010a00e08020041c0151881d0312500030741d0400e038a1000401d03030b0124600140b42080c00c0118007100385242142c0140014880503000d03900760340103004060350640007024145c0d505d5680810100607020010b840317020600b042440b5600c4005084048401c94000009080c1142081550001400b0500e4008e050182c030240b503d404c60310411204180503c43d1044041c0203034010301d070340030707042d42d0004030307000301520143c070021401020f1102c60b0312a82d000e1601004c1d8000034001c00f55610a41e002404041c1c8041d070140c051403000800304d41e1821704580c403055101000384030603210340340d24020001c6541c0c16003081101c108804103898078240004c41c01050184051000c1c19640c2c10800d00303e60342080c9550445d00078000410159540c80803807819101c1d01400075a503503c0d1520070340014010040800d82c0c5000800117400200d405c01d0b004d5218502440003035a107c0b13800802c0005d030b0300d800c4550a44c069031000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 132075638 1250 132074388 132074401
    0x60402040f0b030a150e1002090117070c0b100909030305100605030c221205060403031a030d03020f0705010603050f070e221511070c0504050103080301051921050105100608 76
    0xc5c241900d009402000240d40d001c954070140c10286000c5041c200341d03400107908030265074402c0450750054110300f0300b82e5560031300060050520702c10300d41c050280030011020480c0004e0441201009088103041001400180e00d409805071400300c4800c0c00c0c0e10002d00c130005149004d4011288227a11005c4050304e00100514011801c14500503110503e880300800403da26003201c0c40d0000c0d09000700010502c51900349002002d89416a422442403a4a0182c540c04c58a000a41512b0103409050140e2144240003c0c06443d0145200c060305e0fa608146000003841404a03070f8260b007111040031b907043e0b0750301c40c1c005d04030004c419a03010026007038842c02ca01102c0880c41a00505a10903844107441c600114444000d8410002e082000540001040400c0211000c802402440251424013096246413603540007404144078460180c2c2c010344030002c1c80a090309044020b410700550b005901d18078113005000030301e003641080f2915032070036010a42188100420070103c0d001982c85250390b81d00c40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 132076888 1250 132075638 132075653
    0xe090d0f08090a0503070804240e010c03021f0c091a03070809160f050f03070e010e061f02070e130b010501050a030906020d1b0c030807030218030f060402040f0b030a 73
    0x4080d10100d0003000740703e500040341800103081d5903000d01c404503103d505100110b0042000c503103c5803030359115a000760a0341e42d00001c041d901c04200342820702440040781070503820050f242c4070080010354980c081c0d0310303c1d000c180c1c007400c031506e116907070071020346e0f201c607a404641711440c0090040844103100255260784a20318895100c09002d003a9651409c070790300f00482030303c1d1075001102000c4025000388080d00b001110310310713001000c500510540c1d14101440168040c107000b041c840000703110004406440c0d40f040300407410711044540344503510301c640c02500c6102d9405100f082000d5100407428040e003110700c4c0e0000325040700c514078459180800642e600d912055091046c5900c0782da220780070138000c0c80a0b02000e880b201c404611002d0400f04034000100712180c6c0814010364040503001300e68030154503940a041c0b8100107968500d0005442c9180301002c0383ca41e0725206515507510400c8000c580d4a0046c0d10907103041c0142c9802d5543c03601079400c46081035805500a801070804039150 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 132078138 1250 132076888 132076891
    0x320010c11103b06090a0e0603030910020a050115030203030d0507021e0a0c0603061d0a060510020a02040b150d0203062e02100b1c020307050301020409060e090d0f08 73
    0x840c03e01014040542200d903824221442d42e2840710110451004000d001d0344112002400e011a201441e01c02c4160001d070081909004694051350114009201600c0400c2191994400240710f0001d800c4910402943c03001c07040c0c0100c40c594241005044840304800610042c0c0b50f0041c040e509280000c00340d14000d280050012085105101c1e9009071542e8070a0560076015112002d0300d803410950811303d80e101403030383c884070416140401c10005801c890014180e003c3c0003841c030f00d5003a1150f9110710b0180403a608801e511800103000b030001709400081002038144250b0b410712004070040200400040070386c424088501e8208600c103003803512070340150382c070020007841c88982c0d000c00d8501e0303203145484100001c49030700510400520540c041110403011180007a05107d54524680032840c9180c045400c100681050700b030000031980e00b48000005460050003c40d200c2c0d50700c86440c8090203040c07040d05c068804002c082009010082065042085d80d80c880342903400850f41c040314200300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 132079388 1250 132078138 132078169
    0x31503020d06060905010f08011d0c01080405120f1c0b0f0105160b090102090909011a06030604090b0705130b0403021503040f0b04030507030801140906041d03040320010c11 76
    0xc0d00c1a000c201413030944910341c040c20024490403035460806280508484c10048126600082085c8404401d400003c200c65070100a00c0e02c41e044c0e443c1c038500035243c0b071282d4407114964000400c61a508102001c0945403200201d5030880c01d4002030440b9004482584120030f070000420803802d03a0950140d00201000c82c8203141e16044406503488140f000032003554100b003640d400107802c942915254607151380040f0000020042e4a00f8801c41d18081401050a80d01034a00030000920581c1c46911040480f5042181c0304801c0c41e200c200204181e000142d803e0048481075004580d41800800740c0e0141c1e54007503c0e0215100309100721401da500001c00403580c620300c02d0402c1d400104046060780c040c621075101e00e03448520a01d406444540c058011075881c40078401120b000d03a4454003055002207080c1c50026051201d05030111800c84002c80402861100003400000c000340303075070300005001d58103050590340c45400004580807049901d0160000b00c005113075440c0361a002c40c114002c2034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 132080638 1250 132079388 132079391
    0xf032d0e150c0c04052d04080d14090708160b0c030c030f0306090a020a0804021009050406240207050105040306230f0a0b030106050312130b0403120f031503020d06 72
    0x350301c180608000e40c0407400214070360f005822440390130f0800d0302401b508829164034540c00c065446c5000c81e582581815503460801c818070100f030510881c1c10403280c181d07110180901104c0216006022550401d07a896451403203481000204000b010a0351408140440710081d05503241c407a0114550b0009814400c441c0020440792144071010030041c07080030300300b111440d181e1504801300584620018215032140c0e00410600c107415911045450b4026812564941622800c59080320042426007249030024070381180031441b070903c0e50010103428212100c210345040d04034400c81c0c442100c1d02c191804103405001c00c0c400680183c110004070107101060080300310580e20444034414055030713194202a50301c01807041c2e0f1405400f80c0b024103002a0024420249002c0200703030b0320200410000b07543c00002c164082001d00b680700b080c00504800075425110354485c28240e420300448488440450304158807564001e0190041c120302e02c1c1188501003150740f45400784a01c107040c2540868245 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 132081888 1250 132080638 132080659
    0x19060902030309091006120b09060d060b0909010204090f020a0e1c05060c0403051b030d050d060302090108010c080a05010f030303051f08010f0e0a0c09020702010c050a0f032d0e 78
    0x1a1903188103117200c3c1d801024080c2e841484d0113405020030302c1c510b00f01034156003409080f01440e15070741840c680080c000e440d9201c080809051900041020300101a444a0400184005003005401400554540c607000b0003002225079940c008a1084402000c040b403100024241a490014180030b40c07416510a02c240c0c20803070b5501c16060980c1201e1641c100400401e06000f0b2060404c0f950340180d800c1c2020b01d20744491840020b42c0d030000903c030f400801800248040110075903400210003507501800070242540c640404038041c20b02a00748600140202c40081e41002090044078101d4031384410099613541140c604402400004060495015014800c0d2002c421505181030040c801c02e000080c0c0c0010b90008a010f60300c0c203140041050303008100300740101f84060080c03030490715100c84c010396451aa00c0165070015070b001000c1d0080c00382d15080b400384030041e0102902c0c248286c0d0342c4243d840b039900344030485003109580c06c4501c0340c0c404401000c290040320032491a040051609012 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 132083138 1250 132081888 132081907
    0x5060105070618031e170c091203090913030c0f0305091002060924060607050a0c12020a0f030b1611100f061403030a03020d3209190609020303 63
    0x41d01c0040c01d0840421800350040f906265100721200a103c25100418022600d05c06000305440d00810302c035004a040540030a0601c100700d4200c80c42c5060242160340580042c040c1180c40f508040d906038000c2d513264000071149144072003031081041d890380710900300301750a4444d12010070200104800b80202081002d0850346c803809030001c4100698010a203920349000000d0521484075420902d03028070214140c2e0700118110b03190382c8040162446601c84002d410218900b091920740a001e800c4a0710003c140000c03254410011540281c691620151340c0e43d000d0103508a161001401c0c0e0348110300440c03009100e406210130202950f00c2d01c0807003091140160f134103124041524601d030700ea50b224000c02d21025401103500a24002d071114500d031264401180d100e12900111008242d40001c00c0d586203005580a010261038800610300692179094404da06500480d030701c860300101c03181c006104440c00003496003185002e013242c650085074650f0380d800075280b0640f04a07414002484050384 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 132084388 1250 132083138 132083141
    0x90e0604150e0603010b0306152e02030a17100603020304050a05030a0507021903020607080f040b040308040e1006050f0c1e010603031d0108040305160f0c0501090609030f06050601050706 82
    0x141056520440c40ba040a00800d0300311200301d011580aa000a0f00300b01300a020700c07003510107a4074191202020b5118040c1e4100d1040d4440da0181003100349418542170207a40000980300e011666202d00c01100305405e000e00c0704100840355841c0841d800b800610205100750003135508103101da0203c03081c20b00250b882e10b045401c15200900000c00201d2080d09621f0190414480140346400605010b400d640100b82148212603000d00b03842c200203000340c40215503000316402412501100c60312240c4031b18049134a98054070070201040c5040000c42c005e4a4100001800c132151900ca962405580c05181e0341182c001401c1e415490151000d11150a240c031100c1c4030702403140b0400054454118503015000309516180748030702c040b80360b04003400d59800500890300300f501800c1003034071038080e413103034183d40c40c4905802860b28550004074001c01c801c2013640d1044d100240c0b203000065031110000c0b90007840c540b0001d01000e2900464078041801030344007a400a00c1071411502d024043e484110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 132085638 1250 132084388 132084431
    0xc10090803071202030c0906210903030a0e16150c0206040e041e030203090910030203030a0f1b051002130b0c030a090e0c1b191103010b01050a090e0604 67
    0x65144100200b0071050342e600c140919889402c0a40c00c41c2582083c800280e410b02464010600950002641da00502d100f0007400c1d54540215040055920b440307038280e07460b50015140c5100d42c0d801c001c04200060008a011242c0d2158059403080e081c0c80c1c00d0300e034034072108d562980c0741c148100f1b4000700c400341e01ca02c0014405045c0540c1e6041c52801d05140c615040e0007802c8503511030880f0b580c070f02000654040101d0b05081411602d451140d114682c02541c241d415038030013585407100280e2200c41a03000816115054025122604036108401004d015004a1007009250707420012541c203030180680e018100c1003a013000310358145502c50981001540c003031b100250450340f02007008210342c0c4c1e0081c581c80161052100581e52403c0c40c0c0000c44980c01a000c0c41c40d840740f203e01c00e0f001c0c01c402c1081007010206405105071214621824100005402c4540d500d00039424410030801550007001102e480345d5065550252031480d0103046045018040d014943c0300382c65500e004890b0174282c00e50f1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 132086888 1250 132085638 132085643
    0x2310c020c10020102040509040b0606130602060f0a0c050702092703040312050403020d060c02010b03060a060603061401020706080a06030807080c0c0d150c0309210f020109050d050c1009 82
    0x81540324006010071400080b5080c80e04110b80c0104810300032600c4644116030000e84c40301e44c10382d00f9120840041c04500503034074907140004d8035a00000e001e55002644a02490300307038031030002903100d0002007803c1d104943d041d6070100d1002c100b40c40c0141440c0794525800307031018a0440c80d0300c00c07000401c0c800d0b0201c000d030b41d2019803000c50300744140008654408904c84444c2499842c140c035581c0414803411449501601259903007403a220790754000c0d00031030382e4131900500751002c0346090512500103280d1402500300081c030385600814031409501d0081c0078014142c004000c1d052030180100ca68000c001d141c000740320f4440d03c0000c000387c2e544024144940c07040003c6602c030040d003900b0500c0c02445d4100a8070a5150704000404104100305020b0301c00f108500120f02030520030419000f400103c040100b0b080070070040405181844074182800e00e40320b54070765401840600f400c0782130b40c1c4142c002030069006617110014981c000c0c0020020780c582031060300c0921002d40d401208442c84a0010f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 132088138 1250 132086888 132086893
    0x3030e030f0d0801060c02121e010b1c06050402010215070f0e0f2218050303040204060e0c031501090504090b1b070302060a11091e040b040902310c02 66
    0x2084000c0c50244007030980414140014610390b9a00d8800515100b4184290010f000c801004a4250b40f100c025030f10803205510300700c2e215040c100202d442e881c030440b140c8022035403a00404803140c1c034000c2c40d89090303590b034020f07104442c400030344036039000f8100504201d05612030301e060000511001c04c0001d1003000c480e00c0d065000910344801600c40c122610406108521101c0500038654611100c907010300100612201211414a0600b00900030900b415059043e000b40c40c02c00c111000000714400d41c0b0035103050200319610030309054a0750040e03802d90301c0c1110500016050b1504a0400a800f0005242c00c1440c0d558890124007200d824010680301c81c1d00e40d804005090241e402d0302184290f8039039080d072030031102e52070003525528040d0284540715115404214281d07400c006980540b00010f0000c05400c7c034107084440f4099408403018046d80c00c01d00001c0c8146054031130010300315005000f40d00c810f8502112488042da41d50000f41c403151010030302d8012581903200ea03028040e4030313400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 132089388 1250 132088138 132088157
    0xb07051305040923160f03050d050901080a0c12050903031f080714040608010e0303010f091401170f030c0706020606190612090501020a0c0320071202030102130303 72
    0x25100800d00c00341c100a028909050325080001d015051200e500222615012601d6141034103007030406002d06007044221242403400728041c0c00f0810f0300d8003142e20034401c403044c25150482c1500c0d24010520070501046c0b20300e0000700540c0303282d0040f8031100b8007842e114441c6260032641300f0468038251010782041e4004402c0100c45035904001d000c00242d0410801802c0d07180c185004c0d07890f1800d0007103013040713200403505500036103440e00514054120400244180302069050b40c1e80c0f0b410074451200d6001594200159522591141000c1121880800314960303003400102d20300460a540303556500e200d030f052500b104900c2400541842000d243c0a084201d140200007880e0800103466944181840d042c60703219512000c121a040380d2080c1050340c103481412003048000c19110001070011b500004800714015402803080c0c041500c26118103840f41c0b00320050132020700304982c03504c907030361300111050190074110b200002c5001d100030005442c010b425400c3c14903000040c2d00850102c1d80810 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 132090638 1250 132089388 132089407
    0x110a0f060b1002010902061b0106051002010213140d062c010203010609060305101e08030406121a0904030e060d02191707020d0810270c02030a0819090b0705 69
    0x140074811030b00303480c80280403082e4260001030007803083c880b450440c1c03d0715014194036104207410035001004c1c0103050003400c0c01040d10190103540403030341c40e90b010300d6018804555403070007922110302c000024111484110840da0707203000804003030403008a006900d90b00c078000c4180c8404070410071b030410000035859514080e00541107a0742a04150103240c20704040215112403030140100700c4a100c1084001d140ea41c0f004422640b141c0d400a0803075010014020591907040f440821403d6075111007008501c16501c62680d180040600036a4000100c0c4085004070f449502c580420600c001c0426150900000b03e04e001c80c0d0194540e42c0c400000100051081500b041c40300000901c100c4c2c00050514140000a49605030480020207000446000c40c0d000c42028002001419900280b040d15060342e905110000c840100c40d150b5240c180170f44600d9040c0301009aa011a890740c4400046445240910445110603010031030040d503200a903e0108640c1c00c000790160100340c455654502c04035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 132091888 1250 132090638 132090649
    0x711030607230310150804290417040816030501050105091012030513090e060907080705090402121c0e1906050901020c03070b12100f030201110a0f060b 67
    0x30400e00034441c00c1e82c103041c0340424009103500701d01e8040d000c060b41d940c0c40010418a4880a0f00881480510b101c110000d81c0d4100000038050f40c080d1140c801030381d0340501d011550f0855107285602401c019000304002a0b440141c490a40b614110014107168a500d0820714105400100a2024508160410900c5028416a400f521040d101d045562822034200d07502c1150900c502e07101c0062800c09a41414070440981d10140c01c8e4201e1581c010b43d4400c58800546074000c85141d407400b4840c04200c04640000b107141c1140d06401c0504855071034903082140e4480b005000f6a00280350143c454484c04c404e001a245000000b80324601007030b046000100701400e00c0c08034500802d52404000c3c00015415401000c840030f91a041d60b84402e1000100c0c02d240d1040303a55505031007192804039020503420040d140d040501074520076541e4400b441c10015014034840e804807010340c0c0005002652150f884461011034500c04c813215903042c0d0b41d03441035419950a003540c0003036071100701000c07510b400b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 132093138 1250 132091888 132091891
    0x1b05030c011d030f07021003020403020402070605010617040203280b090d090b04060c08030a2004090b061213081207120b010804020f09101d0f100f0e0703060b07110306 74
    0x5100118144071881a00013482e00ca1010040e1240c4078125001b141144243c040310099039020f0820b540703a0400c2c0c5440c20140a082c0151004205150b2000c98200c0014075694480d68009004003541d00010404181c2000d90841000c4d12980c800700550104040d80700450245503c4001080120090704000b40204007a4110210440b4100010484564004020307541e458101d1b1465aa82d10741032076241c001c0c000c034020000503c005090a144082c2c000003e842280d205039001e001001c0c01008008452150001c0803242a007250042003c5803e20b50117151618420030b007013481c000400300782d5040c04500721690030026800e003100410208242c080c4502c426003c1c24a14180d041948c00a02ca004010b01c945005007400c1b40010711400c420350300b6100401e091001c402010740c02e049681805070f422960b40b06900c03100d9020405004207460441c04840040703242c050300c2c500b0f2218404d1070b641d001d42058205a01c800300811596901ea0062000510480880310114040410702d41002ea0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 132094388 1250 132093138 132093191
    0x203060d02041a2404091a04090312051f0306090501151710140a050705130b070b060307050d060b03011b05030f010906080316020d0512030901050a020406050a1b05030c01 75
    0x84d42000310600311074070000c0d941602e04001c40419100740412810703408210008109600c14100100c440900d600800d00c2d010242c001501400300380d65104a845502026450100c01c8916502d030810101d1025403000301201e10550020901c0340440b130440c02040541d4015014024081d4540f120b048000c225100100300c04000500080c1541c01840880910081c04030309655141c00009184910031000c80d1400c0f0312509451070700c0c03a1980c00f40b10b4aa08610400c503100100e031f20204689140010304c13141180c40040c0114090308180c0e9804018140320100180c0564a50318600700a20401d8071580701800d26a841079101e14100c011301000c084107070b0041034850f1401c4400d2101d400084210742001d06401d02c100c000c01500d00c049250380c0c0b88100040c00074011003801c0c81c82911414001c40c01030020500a1040d0344508400300c089114074898000800c40412000d4800c501070107110010004000038038807001843e80750301d400d60748664071000091359148822807030b00d1441d6205400848 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 132095638 1250 132094388 132094429
    0x30f0b0f1311040903111b0108090309101d03060f04120804030807050a050409020412050f0f0c040902040209030a1103011401050906120f0a080901080c03100302040203060d02041a 79
    0x51944607030141042c50494a40100d440b0124001810302a840b10303c0602c040504580841c2d103218107040301c00c100300ca01c07140010240c00115070f07e47d10000650b003c2c0d00c40200f5a66900d0b0b0700003425100500c2e010f50071003a140d2110201042503400f0302c80e1600c141d01140440e03001e440c16107440c56440155403d0a82403004c10380511000c82e40c0030f11441e600c10b015050071542c0b14464641910580115402610020300010300499a007018000c2e01400501c160201c80c4a40042d40c80942ca81c0f807000c683c896540e22040d1012018a45034104030041c03400908010b1800c1e440d603020a081144512050703a180440e01c4801c030307190038240305154401d80712078000d41d40ad5050600080c081000604060701c91500304222807c0c0040c24041c04501c1080074040f00d401c1d081d10316140305c0c260049018540400c1e06071000038070a041000890f807041c048603030400074140c01e507420407000303400103441c1e65005002c0f599107100603100e91203a511290709000046900c40950400c100c80f004101403014602d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 132096888 1250 132095638 132095671
    0x4061704050706050c0a20030c030607120510030501050a0501060914010e060a090e040b06030111041202130209030a0b0f01050406061202091801170705030706020703031107030f0b0f 80
    0x10000304030324050740c0d0f0718502580d0f80d81c4415442d03850681c01c00401fa041111100d44109618003801c0f42e01c1e80c0c25002e90540d0141300c4c4d184201030310741c0812100d050110311188c90141c0c4100e125400558440228054110825226265203084450440701603e280d0340d00d0700148495600200030700004d0500e0031a02c44549180c0d00020405040314075040e00036800031981c0d260040c0a4142e80c0c000d0032980d84a403e40385401d06022602000c181d824602030351a10682340003002001003203800b0303a9034440d07402403220b40607824031103180c1c1000b803c0c44080d9824040000791303a07014031150000b680580e201c4007450602e020000310502c010303030000e44920301d0030030100b002c550450008480394000701c0c1e0060711504050003103008000900807003d0754540b2a400410a5416121810840349002080755003503500c440a060703030380304180034042c00341e4081e15040002910890354803400050311800d4501e82a52540c402400a103000800c50309060410104016080815403580e0b1100c40c07030051504a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 132098138 1250 132096888 132096893
    0xe0f0a060e0103091403120f06010801030c0b0a0c0b0106030f0f05091207081312050c03072405040f03051507030504020f0f0612070e03010b090105130203180d0504061704 75
    0x581e5003285041c181a101c00040003441900146401070300d030541c3c20f0707a0383d4500c0740210041c0c00400300c901b040c002c090b0601003145940300c0c8203150f040e25805000e0700c0e000350800990701c60301d400c000804401c01014000b65000a000981041d0090030141c0b004606405e1450340b4005940d500718004400600e00010031011100c00551201c1041d240491590349a10504010103039101d6400b9880504889540004240a0343c0c2c85a00f20315019006036007108100508050300c079401d41c030405030022107a070700010a101c01404003003123640c40c0d4100545860366030a0a04102081e550003590750390030249100c011400500b010a0380443c4914042100e86030540c00510080c62090807039025541901c640380d050b894041c100c40c001003201ca0707801014607021000900c040c100008503400b9509211103407800f400c00000e2641601c8005005200060000c1030010081d04020040e459440c40c4e00c0200d541c6844c2441040001c1400369200760b6524100800a0401d500c001801c400b5a189130042001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 132099388 1250 132098138 132098147
    0x10c0e03060f150d0b0906010501080108060f04080309030c010e0d0f020d120209010903150f0f090809090a0b090f0106090b040302132d06030512030601020a0303050405100c0e0f0a06 80
    0x90141c0402191400d034582000401c0b130034080e10720000c0000caa41014044824030020b03a5a040300c009a8aa503040da8840b02c1c0b0b541c89010541f414409400400c0c00b180000c0d0010000d1980300c0086c01c21a400c211001112900750741440e1410f8546810030f04203500c02c5503014001c04090700c4907000a008100c03c01070002c1481c2200e04490002c235a0128003070f8407581c454005000156000165903100c952524400801844500340d9155020710b40300742c0001411980c060610b80c10380040403141005120710a00485036802450384600036913403280d408440c1c4c0c400c40c160b40a03e90b003902890304c56040100140214040d508050f05c1e0b014144070410059662004030600040951000b05070b2402c13041c14041c01c2c1c0754070301c0002a40c1c1040f20303107844590f05030f500c544202c83c052012600800b58811054050784410384086006801000c21180400e0180d001203400501c85c104860601c02034181d0101101c080c0424080001d0110f1003e8a0619000490308904542194039103200c80c40e0000242 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 132100638 1250 132099388 132099391
    0x7080106080405070306020f090307170d05030a0f0e10053403060906140102010b0f01091a0903120702010f0e091f030c0909031701270b030d02010c0e03060f 69
    0x10030031100c0400a000c014080c01340c18000c56102c201591500c0452a14454540215071761038001d1040400001d0101425400307403406200c154080c10488ca1803400c22183ea0380300a01c86002c0360703210031a03422148140d114807407881c02c04801030118210116800020f80c1c6000d0104022170001c45418070b8040080c4212041542030111103005587c0780740710580190400750300802d03d85150913070019803400c002500d800c452500347c0c001c0090b05005000c01a0ac1855800100d00040d051390091001d110b40c4c0d00f01c141550015201780f4201710660340080d1030817900c0144d240004002081503421541c11a000071a02072280c02c281500f0f03804440450212500104a8a030b450b48620000b5440381c002e03084038001d5600f11292050043e201c0507840060443c041084001031841044c444c800441042150305848840308600c603d50055110403034540420010300d0411690741e500084103a13810440100440c0407038001140d01d031480c92020f032800300d41c0b01406020350408020400201014005036 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 132101888 1250 132100638 132100649
    0x1030506011502010e1608150c0304110102031306031d0a0b040201180f0e011e060e010e1507060b090a09020102150711030d02190c0b060f13090f050c09070801 70
    0x611068222422405050940422402c1b1b003d5082c0d6606048014603681c010b407245001200d24010410b01d04041400d0100c170805070443c82400400c00160f0a500210b600110500c110380c20b040c0c0c0c1c9403840500049541c001000b00e075070741c800520350006d035520b03060b814041040038182d100403c1d1140200610002d00003810005080c41302a400040c2d01f25601c00b030500e8120109620b0744800590450382004e00a000207a242825020b500000f10410301c81603c82e955545544840b150f8010368075402c040c1c5000350322401480c4800a4000001c0290510300d0150302e01040081d480030030300100b840c0103469403140c2800d003c046800360340c0014040380e20700d00d01c4044071203e558240b070840f00f40e5070407031418020f03000026000400d0069a005000341c0c000c00403038a960000801e8068480e07404402e00140851240000156107141444c0c91214000000d0f2030111421201c20201d000c40b080080c045400495908024062100030004002496421390310551340d400d00d03a202070070200c01480756 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 132103138 1250 132101888 132101909
    0x7050c0625140a0e03076302160303020a090605030c0f030406060302030a0c030506090309010801061215060c150203060904020d05030d05040308040b060108070509060d0e060108010c14030103050601 87
    0x50041a1400c0081900134440d400c0c181000280c43c2446a0143c0e02190541c0e90702c03aa540c0040c0d4040b0340c086120400247d515800d003400ca600c02007401c0c2c0315070b003081e51000e48650034005280c0d884120744081d00344911a0b5030041e502c09040030040c180e0211500610100070f8240201f0185004c50011109518205041180c881c1d4039441c09402a007000c3c0c1009405000300c00245c0c0401034078515030019a0301c04c0c0c068407000d540e8403d00507900d000e00880107001030f240000421503240110b41000c05048984404540c04a0900f102c1c1c003520301540c00140014a1030f10100c043c00341d050110b61032200d041034203501e141441d5000442001d006040680704c2d12400020350200b210030811074608034035102e024412850a8100034180d10740c2180c0c181c0d0401d5a140c009601c0350b10071461548221081e0301e45034207001860040c004d003500400d01c0802e00e640d0390340c1c0c0250303450300030044107008100030360000c03034005610307000203200e881050b5104c820218207000510008a010422606503021000c9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 132104388 1250 132103138 132103157
    0x806010f0e0a09021c060e0906010911030a09110d140706020a020f0127030f060b06070317060a030b04150e030a0203040b070c0510090303030b0d021807050c0625140a 73
    0x810f00c1c19040b00c180185c029514060f0002003007001851600d101e01100700582e481030381d80303205a8042d500c094101a114041c00c00c002011001c0592040840707602440f06419a80c0c2201c0118040d62004002a50b42c11517002d000030894008101040150207144050021480b140d4045444140341c0c10906040c404804d900c2003882d900600c914030300020071114410615540c2c1040d9090b000002401e8030070724246110481c66003440c0040b241c04507032640d0742c11800c85a18814101c1c1410240c04182d01004a12001011400092005004600640c0103000310440b81c448101101c4a40742008210340040c001000e803180c0110984003181d2450b04020b640e40e90528042d0391160441e000b441d0301445001c0c050802d01d90044e030640580b0b12a4030204503440b864020400303400c22900000354040b881e00c044401582849051542060440c200700d03042001c440c0784e25003000c1040b18801000180d80400c410303070700b0500c14442c4044041c2d050510346180c1800c2c072200f051085081d035406101c070f081b4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 132105638 1250 132104388 132104407
    0x6070c050a021e06040303030b0108160c11032a0f030a020105070b09010f0f0b040f051303270e041209061d0d0c0b090a090e0a020907020a0b070806010f0e0a0902 71
    0xf500660a040041c011652961a440c015000741218030041d80041c001d40c000440021443d80031000c002c882d6102c0c00000005640c0f0516010000032101e07416028590444801c07500e8041090001d036460142410074502500c140613502000d950128400c0c0d00190803200940d030414100c4412581020203c007055440c1c03401c3d00d0142610610300250140390480c02000e41c00154401c000c1550201c2c2c09120307482c900400d45050701d4047e82c1140b180c3c0103210103c40060700688501119010b0030840d1002d42444040504c4400c04a40c0a010300b440858100f00400524410340c3c6011407150401c0030030f0a0a0403002801e00c40c9000030702510700d4988000b02100d40d9104e03100100107a1041070a4202d0ba11205418505d820688640c1e001d84095500410410840d004401507600800000c0c14031023080d03000c000300e00d40058448015030007600c0944010800114010744070ba6030a482d0b000440c00c00b200014000040510240100000d50300761200559641c000c0204171600d140002d41c0320a4080d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 132106888 1250 132105638 132105679
    0x601080406270318150c020103060b130807060c0f0605040206090306100524030609131401064202030f0c012c030304020d110405070e0306070c050a02 66
    0x8900b848844481c606410b10a0142c0c0d101420b581e00c01d5490381c600d000500ca000d11100a2405010b0242c2814489400f8441c40743c6000c00c0305500516001c1040d607070303580c0491603990010300780c0d44044124550034001d403002006680020702c86071034000103e00441d10745104003070118500a00c00e54039180403400f559070322001e03110800c0000741036940304e082c81082d028980700a03125542c040c0c415910103908286829800048800d0040e21103031071550b4030401c100040d50700401182030000d0f000c16071400320b20510049111000380500005115040001e015020328000c2e2540071340c2e8041c81c01800d4604a031240ea20580b01c030702d2280141c1c04030408016411402482c100381211800071032800d81c3c040c01500031480e0141c1c1140202a54016030394101c0e9421000d0803a0030803503004001040c01410850900c200050007203031501c149254040015061f1002907030340c400003c440002e00840d6140500c0703056003201031814527103842596030352440c8d201c40380c00e00041d00c202c07110701a120300c10031382 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 132108138 1250 132106888 132106901
    0x3010501120807021504150215010617010306150b0a0504030204060509092d010903020106170a0818150703051809060f060904090611040305010f060b042c0123030a020105030601080406 81
    0x30607c103a018014414000d680e9124004c40d02c580001400000a07401d0048802d010030b03000ca03032440441e07030b800c40d03d403900500402b01f401600c0f40d42100000458603180005041c14641c0c5583d010f540714518010041504c1e141c1e08002d20880d045400c0c02412400081c0114586206074035115001b10701c1440103401c00c001e220144915401c0c40c4004c42096419846901500c1042041c2d442d2410368485903540d0700aa1400103144003c100005000281c041d495000e2a003401407c4034900481c4525101054100b428103c4c04941c0100310008150302c8078014009a0101b42d0340340500d840d00b88006414501d49098032800340100160517140c0d502c907504041002904040c00303100c4000c04140030301d1164000d10003a00e40b5407034141914905902401f8941c00c491314000654100741c10103889080320f070440341000d4070900e036115299140800d160030300c500030708400e01a41e05685203c02d40383c00356038030508068400e8010358600e0005030382001c00c0c0c81c4c00640030310b401405547e40d0700e0900010480c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 132109388 1250 132108138 132108149
    0x71e02040213090e0604020d17130608070e011e03020702060702030304030305120c03042d1a1b03100b09030708010908030411010804020310110f0c0c03010501120807021504 76
    0x10b41c0822038003011280300881d00300040c1003010003900140652034260550f0003d610600c60f581e4240840c0c40380109520b1440d491524078035041007200f040c00d0018143d070041c00458542001c111100d5004030800c0c0480d00217003007a2040c6000004401d07022194603c5903001e040c1d001c5003071025500d0300400d5030005907003c0e0440c5e036140d8490a0240654004092039948451b131600081e190044904c1540e002c0d07603101c82c0c0c282c240b030a0101c0c0403100d561403020080c580d80410300072101007401d00800000400529000854904004401d4440d4459010144101560410a2100720810f0b0004602141e07641804143c84050703010010f0b0034a40583d0001a0b15802c04c4509800c0c005800000e44c041c5116000802e14251800019561100101e5020b503064100d00d0030000c01007a2504290505104201014940100c510032083c541e0170109000c10590300c0780110040604003441a94003410044890001181c1e0700e80d5000050301c50710700b0080c02418001a094801c02106041d10301400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 132110638 1250 132109388 132109391
    0x40c170a120c0b010b0f04051e19030f0f0204090b130b0c0a09051003021908070305060a03050a0f030203041d0109063201030207060f1b080118020313080a08010e07080c071e0204 78
    0x8104151080c00810422701c49124804072002c180c0b10048940d440012280e00c00c0900448951644504052115019041e600151070304180400980da03101d08501c141c807801080b0841c0000d900b4030101810380101100a50301c420044281590341044501d0200c41084907140c41010b011102180607003c2c05441c0c0d0241416219118280768200030840d1040e141640d0030003107590b40000304036414070706101c0600181c0041c3d42000c08500000e803d51841c5000b40101c034600340c3d807040468070780b0303407001c1c0b00c148001d490703034014041c9501c01e0181030020100611a1000c2c1c00a441001502041d4800301c100b0b09113102581f4692a4025010380f0146a0008403c000d80001010501c0191030486c2c1c4600d03180500031003051405004080c0e190588000d100403400303003840d0f0b208001c000d52000c0d104003880d00c411441c1c3d400140c5120300a1000801c603540f08000c41d490001a0354401002604100600600c1000c1010942201c800e80c0d41d01034101c1405540b0303440762903001c501c500070000081e4009 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 132111888 1250 132110638 132110659
    0x14130b060a031211010507030612081e0c0a03020606030607020706050a1106010603050105040b0d050601090b0d0b0702010b010207080a05060f0a0b0a08011d0a0218040c170a120c0b010b0f0405 84
    0x159005030f0f03400c40c40880c0d40001c1c015555103500c00c03800c07038406014104044002b1a804c00c00300e114240034000e50403d03100e140030440c0803030458510580100c0f540e01c689511920202041640c103002d00c41e0410f80c25402442c075814000c8020f03484d0b444600920302041004240e050b03145110780e107a603158880c0c002c142d0b0480d58607010010b01901c2d00740500b0b0b00540c10004400f25500785582c80314085030704078000d0001c507401d00400d40044d26006442a07403040440314108080380c0030080c030302d000307000503000041c00a01c99000a0300303000c05079000c60700c00e41294555001049000c02c40a601007450f165410191f0b0b10b081941000305030740d0303061680004024001081c51311055100c06548518201d503001200c1150300d05a0341c030b61080030003c2d00900780c03061080d50642120180ca0300188a4801500c015443e00d0a03020030a0380c002e9802044d03803142000c0c07010f00450300c2001404800318a004180202141c640b54003005040c030a100c42e43c030001440070050000e05042e5009050018400c5400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 132113138 1250 132111888 132111923
    0x51209010b01110d090e06010e041803030501120f150f09120207080d0c0204020a0201181a0a0603030e090601020708160801060602010e10050c1c0e0114130b060a03 72
    0x2400e040300d5090124242000c0407036040c00002e44160b02d41c01e61781d9114940e50418051501031107015103100e06200311032105030380e144e890f40110b13011702d84d0381280382d8090365890038014280c03141030b4408021120341c2d01d050700c08500300104400c0e1564102503c10244812a80750000616521001030545460480340b103007000600310000380340340350b03ea00f1542c0003a00c80002585403e0241741980210351303060842e00c0107040ca40c0140c4000e01143c000082c1e552000940c0018100426400b26840b4041940031482191001e030364079005104510200180c80c20741da4041e04200355600f540380300d0f0046c64002440c0e80e01c20030041c1c0207400007400b52221107803110b10240b02028180103040c0654240080800d0350b52051141405550b0441d004001e418100b03000c203001440007600950a1500401c24100020403404807c581e4924107000002c403020b079840d41d1400c66a024003144055200b81081c0034441d00102100c807511500401e0068054503400b00152108405900081501c0000380ca0b0400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 132114388 1250 132113138 132113141
    0x30e15060a0e04030e010314070221070b07020321010302090a0e0a080d09030305090c090417250605090c010e040b010909050a0203040212030403120e01030902190f060801050604140105120901 84
    0x702020f007a07c0c103200c0320400c0300265071100d1049a10400580c0310060640c82040080080c1c80f15401425010707141142540300c0c010b4146044601d0b030056400000c880c1540c010390f080135044492001c000030401c2d411036002a41c0321002508103040d860322a040c00c00d201c1400c0c04032821169001051541c0c0e81c130300ca00b01e17801428003400b0a40100b85000f0000e8803680c0c0124400300140001050008190390701e584403c000007074109826084a01031040b14510034824643c900da0000c07080101003014150300e042c1303081e681d005000780480d13002502035060750398020401150103601150041403441e10304d801283d6000880d401f040c0a90700309024040f03402101d50007103005a000356006649100c403005950703903d218901c00101144c1c0b05043c0240054030803426042440d10515000c00d50200c2034001841610080d42e4140784050b5030700c800c1000c0c1214588920040440e41082c0c1d440350f14040c0000c0c003c1c082c0c0c2c810384400248a080040446e803003501103441025905202450130705001c6102070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 132115638 1250 132114388 132114407
    0x80f0c090a06020c040b03010b0a05010c0812090709050a140a11070804030812090f06040b04020f1809070909080d0c030902120303060a0911031303020f010c0503100501030e15060a0e0403 82
    0x10f0081b85040f05440150038180921a10f500d400f4000301c0c0d00d14034100c011644603900690540300360605001944105082d400200d010b00032100c004d292007820500c4000c01c0740d0002d42140512841c0c08d041850310b02510325100d0703100190020018072900c220000c0c0c0011f02c034040c40106181400540401001040c40207030030203d44d8121004141e90b500750404c0c0d91104950b103031402c190311002c0010700003401c2e041060b601c1840507086034000c01c18900803030140000705001c10594035900d402c11490340700402c6582c0080c02180341c00e01c032039203180e164010a44120300c0d04400c0700d92628140c880d0580030b80c0050344030315030150107440d405180881a03512900155046485401404e10004101500340518501881950042d03481c2d5110310982608103043e100d000c0b410360050100e9810350341e2080c482c807402c603030a07500d0303161f0360b8900008120f00351071607038028138107040c503000d9002c0450000007130302c240c0c103007050042c0c640540300c600000b000e92640368040824407680400300420140d0000b03105 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 132116888 1250 132115638 132115663
    0x8090a172a010b0a050306010b030405010204050d030201090201030c0e010504090f1416080c0a140a031d0a060b0d0308011a0904060b04051914281509090c080f0c090a0602 75
    0x200f0580203500200020054a8415681e01d580400c0051240d06880d0004640092080c4001458a590760011440002c1204000e60141c0d42d221a00c0f42556003500540040042d545400b20003906020000b038220700440c0242d002d01d0b6641c035045192400b03d64030200c40400403812508080ca0807059500d18401d015150030b000034081c1011a441034030302010b8503406040f640f21103140040d894003443d40340e01308a448208068559989801e400b8000c1c0100038000c424001611000c05036040c903a0540703011b56517443c0203100d02840800407940c071084007810745295001c2d1001030089503520303c500b40503c0d0030203a07005103005400500050010f008008881c002c4c0e40034481442801e41801d1005010310a25403880c0c0d1030b45000c0c2d00c6207048180075100314141c13611100c20130404081044d00012a4000001d4001d1103108420780725000540a4020b0544103c2401400041000140012805040c41071200610808502d800da0a03500f80c500500b0b001e0080294503548500c025a10742e01400d04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 132118138 1250 132116888 132116891
    0xc2c0a0308070c0801150504180b0408030117060105180711070e01060e10020a03080c1b031e070507060c03050712200a020303041e0503030d0f0c08090a172a01 70
    0x4113001e040c06444150f024001d2240c850a1070003050001038010241b40c00c0c0d104142c481080001401c14265074051800b9860607500d80d030500d03509185e00b80c902008400c40e1b60005004001945e201ca005a40a2540c0c16440c8680e44520300c0940f080074107148051910b000346031000c211072404610b541c1c12645141d40350304045400600784140400c400c128140142c200b0030700c130000710780a00002030300038401104d0a403400511083c0c9100b807640d008200c2d407083d0070000d1042154103008403046486848018407074685030080e80c0309941ca0000c0c0c4074450a011023034051200317060081c41518025600401d080350f040303040020050801000e44201d4003001c540b400841e000980004542071520742c041c00542c60281012100a4103000c61a00b18141c803503d0240410141c90074009810203a21880c008100c0319400c4082c2c2089c3c0b0540c00841c400c01440d0006c01807042c070000707030700c0c0d16031904030296030b01083d1000c40e034240b070703204105000f20170f0311192410050003681c0c0c40b100084080381100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 132119388 1250 132118138 132118163
    0xa03050105041203050705090108101e08060c0f031f030204180c08030405011205130507080d0239010c02060a020718020c060c210703021b010c2c0a030807 68
    0x41135044800c1600d0b42c100150f030030b014030303180303075008600458000d0589400111540d6964903d122151862604141007940d080802c011101003000a541c0015140395001d0400b004804032900318040202060001c054911903e805920041b072000b01546e0050000c2c46103080b01d43c510448240002c4049a40c80a190400a6100008015a4140c8a05031750b40304003c45006203000207084041c0404d42100c0f850100180040c6040082000505122000e04200510230030080d040505685074072460800c0140d035283c005801503c0c40c040ba00124080214000f1114012940280b00c04030080d00050700042085107160009161004c075202e500071f200c10b0a00c107201c050141d0007441f128002552080f000309046001c040c4c00f4200c0d04912421800860003c030b4100460355009441d03003004690b00081d2141c1110744030498a103120400b2000380500000c2c00380c010600c504110404096004000008680c10b40d0301d2104010010010040100700703440e401e1002d825401440111120140b404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 132120638 1250 132119388 132119423
    0x3041a0108060c0a030e062a0f070f030201090b0f09010e0f03121803040605040905010801090201020a020f040e16080c03060103030801060e210c01090b0412200a0305010504 76
    0x1000603060780e5100d00600301c1074079458951034103070f002014100245600e41400c038150a00421400b441550500c401100840585008844180c1d0030300c69100414030800002e03144107a1001296081d83c0d01a00054850001c0d003401c03401442040d000800c111007000a0210440344051170340d0203102030500801581ca007500e02c082d0343d800f03801c0c040382941e0000c2c00380108205011110940c4410384200e910100c0702c0c144034583c00c59015811101c04114045410301003030042c1d120b901e01422031a07000700221022900007075a1110080d400030f01c907400c0c007051040070f0789694002a5481001008841240210504003a42000c46001d10031036413180340306200c031600d0001070850480b074040c0c842e0710b41039003044401c840c1c0543c048122904110010054507107156088010300c0e0105558001d4107440003480001807000c10190b001400c0d00e04144030501201c0100749000d004198000b1a86110054260600545055900003194440d0501000005225042d040760744142d10400d0000d030741c40c0103075 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 132121888 1250 132120638 132120683
    0xc0f010b09012309040501060b12160801060c0b06010e040e030306030c0910061218242003100519092009010e030703020405010803070c0e09030a180803030a020304 72
    0x142c1c054101c128003e84020300d5003850341002e80c000d80a00c0c000702d02c4036190031401d405070340310941280b841c014400c20003180112005000f000c20180d40b5082500d5458614014046103002001038110300249000c6100faa01a2403c00400d51002d0000c0c05600d54000600707450b504212029802800f80d5070000c001c41c9840051a445001d101c2442d003001401c01c40110b45a21950f03050309841691014035407105a41e04416102007403282d4208429824455107038051050092020301d2090305008580c007a0305121a1f051ba074440303550b401d42d62640e40e441e00c0b005c0500480c1d48299044856044502d81c0781c0d4020b00d40c1400e8864020003480382003500709001d1040c9550080b40c1c003001200f400114810b611640b041c04d8401c0c0001c0441d4001510381e000141140c00070b9002d020103610010f0340b441086013142602c0018492080c0942e02403501c4400151684207914501d820440401510000c11840301005406407503844101ca45a2030000072403002944199000c0e1480e01c0c5581664000c07500d00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 132123138 1250 132121888 132121919
    0x1401080a0f0b07091d0402040c1119030504030b0c120c04030b0c2101090c020f070302090c0f041502011a0409051e1f020310050a0b0906070303020c0f010b0901 70
    0x400240880401c19844665000c5009040d10b0700704503040c03500007100d1030204101c0c2041c2400072a0007420381403d20400007203030007001c0d104050243c0582200c46410300424008a801603d014400b04c200782031034121039612032078100500d011561801c0c45076002c14100030f840180c42030034000e2400c0e15420000c5025000360b00c801410f619080c400100c03d00c48003005050001558900c03581d1500301c0d00310039100d00c04260000404150b0351609805413950400c94070170040c1001d809024200d003160003145100c00010003401c03090f107001840c0211100350408490040c580320708810311000304580000d01905010040008090132032a29201c41e2415101700848554098002d101c860200088800485048130500004d4003490000170b101e4800b00c1c659600190000c1e400507a00d28045159003001c003920340000d0b008030a010814801ea012400446000e004200c0d41c6a8a0b1011480c085029200300112401d00d40074120608480303080c150880c1d000030500310b43e503421136a04e911556401e910b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 132124388 1250 132123138 132123143
    0x2130506070506150d051c020d050403020306010311210106050a050a0e1501092c130b0a090503090d08090312030c040501030f02120c040906050628031e1401080a 71
    0x242c404a400c134203102004848000c009003610181c0002600c2c0c0700c5c18461140802078900e01c04a40200302168103101c2d02540101604000d0300b03090858001c60740d07400e414040244482e00003000c039000395032612155000444072112108100e0841200240604400d11800b4048c110030107004c03465203041c1c41080107550f20640d1040d12507039140d044403052281c2c0b86005061010030172001c545215203101480d11a0150401c0c10395005103101c5000c004d000052100c94011541280300340011003060400b50010b440080101c1d100d180c50809030305610528008552041c19141660208940c038400b1f40080c65040703044d0755040d50307060300c14582480120348550a100d0204030910181d0b01961012408148090006080030030606040400c03580c1139410724482d0201080800c807420381401440c0c094107059582c00e040c120300340c402e0b00340c25189042d800340c102002c030200340005200c1e9109846903801034031300011401d07100c000c5600a10390801d00400f02510400049464400001c0c5604801d9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 132125638 1250 132124388 132124393
    0x1e0e04021315180204050a091119030b060307030506100206060a2105011812180b07300f090e07030c140d021902010c0c020f03150901021305060705 65
    0x640350314403003005100c0d40540020048050101103444403000c419115100021100145c2c3c46046c00100b212040c172690004603210b0510b401c00c2d0800300d908003940c0380f503103c03030760060341180d00e500d81500a0400800b03199000030010003000300640d41504400d0048109540829140d12440022078032884202c8405401a68140007003102d039010b8010403a02c3c00c103052140c003600810303681c0c990941d0302a110403441004000700403028030040780000300c629220b03428188001e2514080c46d0388584483e10541715071100c0400c8071410b00c902c40c910252141e0600e040d0001b0b0b034a0700c0011101c210349621a01002991070512018518002c2c0d21000a4520010100b2059903405504030058203280c92040300f0400340401007a04850018041c050000f4820405a100d402c00800c4a426081c071116420440e8100b015030740186420511224580d40c040c1c03040c030003500881c804a4a420b001031040703081c0c0300d030413010082010010b41c007a0900c04a8a02030400d020341d1203003080b08034094007601074402d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 132126888 1250 132125638 132125659
    0x7090f06050103060b0c1209030a2f0d121407080a180b07031202090a03020901031202010507050a0f030f020f040603051005060705120a033207080c04180f05011e0e0402 74
    0x710f40c040902440880102140d00300c40c00d507500e20004003518bd01a25184424081318070910440001c0905032a009940d204180c0d10192240c107524501d51b0141b800b404804201048511b80702001c45040c0e81d004001541d860000c014010402041c200500a284a8003a00482e411b41c0311070450b04c0c002d81540e00d28102c5c03040401490001e511600b61164401420600000186c9606010500850042c04064030201745c4030000380c00c0d0b40c2b008040e201001820080130030031a40000108446100c1440c0c0058403185980c0618028810101056081c080200c3c0020f105541034010b644207440b402d502e54403c2e40e0303c0307051003c140203110700182503400c18030403034bc8488482c0c0082e18070800c1900c2c02181d0341c2c103048021400c3c001d0110a005803411040102c10303210003c2640710303420400724a0100c00c90321300a00c920b241401a07029810340d41403e494044800d100d44d400000c9a6042c1c2c1004005c0e5503501c0c1210404284d055014507001c410a010015140d070102401d54425a0080c0030f04424 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 132128138 1250 132126888 132126913
    0x70503070308090d240c08160c170f040305011d070b0c12030103080705251a0f0301060e090a0b060403111c06020309070f0503070608070207090f06050103060b0c 71
    0x540c110f08a10340c4c03c414803030300150109100c030341c400c0303100008103210b80c44070301c01c0200305001e440b450401c1100b4051600284031a2600344101c50303100c0c101d18900092003e84500d403604c03041c21940050311042c0341c0031a1498240039108010000ca0b88102d0081212103801c00c281a070150500415040716003001e081003180512503001480006610b90540c4c0d00c010040c0621801c0d500283c0058070490b81c0441e00c40100a41001015102900b12071180102510b4003507e90044016000740141c40550310503400340da040712f4003130b640c84241c490701054596171038030402420744425129491052000c20042010040180301d809155480680040c0c60582543c03078842142c00c4e41b84285401221050000605c40310512071440c54074820f000140c0d4900340a44075a20780486500008029500ca4034100019600002c80300220780031810148486e40d1030790426824200160f10030013035182400c0c1c442106c040e842d4031039030695409072800c2014a84900c5190080d01030417a24081c5a448811790401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 132129388 1250 132128138 132128153
    0x10b030d03060e0c07050a0602070506011d1302060901050d0914010c1e051309021b0106150804060507030b0904050a0c0603020a051b0c06070b060901050f060a03090507091410080705030703 83
    0x80d1759001d101210343c02c2609a5400c012030340030103c1620207800050050010b14800300c40d0b031030040c0e4000a07913040c50600400900160004060003442410001a0194964002c60540d45115000d541c02c00c01201d842c2000300c000320b500c4002c0080b81d442d010800c001c2d58000d0038020f903034040403840c0046900c402c1074259215402100880040e2100c0c40b0300245410302c50004180000843c021001a10200f00e249420b448581c0c0240009981840041c41415807104006620541020002c1400e8580003401e80c02001035120b800e4204103100200014464005040002d1350310640c200d03540381d982c50104030200c2c0260308141000903420003c4c84040c02d8000741c41d03201301c4404400e481417a20200000b589541c007104003140c02c018500200031407072801030103d40c0103100070703034101303854000400c002440752146c04444c0c1c1c203140e6560f0010062020030000403002d80b20600e0100320f042101011141d50100840c0e00401c40c004840c2e000c110300030081501000c542001e4003d01c0400d08580e500003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 132130638 1250 132129388 132129397
    0x81e0d02012a0306090e0d0e0102030307020c06160b090a0302071202060703030e0f0714090906010e0103020613080d0801140d02100302090f0406090b0102100b150906120702010b030d03060e0c 84
    0x403c043d100c80010500c0b40c2d26100b45030308140d9000c000c1003560b005040103000c1c400c2c0c0e00f1006066420601c108030340c50782c01059020396000101c84803951400c0c0804a1343d00d4a441c0e441c06001c50500740200002550009074200030f0b64040c1d002c840314195944068264a400000000e421003011b00015002030702030b4000d4004811583c007a105003c010f4100c0a1800c00c0c154001d181024a001d0a00c0d0035081050035070b0340249541020b01225810046001131518040c40002d00690f00066290364500d140d1103104003a10003441602c050310000d0100601e5001d0a003d00318005440c11401c901c1d9281c88900f9801956001d801141c0e107102581c8150002d400180007241c00c0550150890185d0340d0340d10507400a0212200005123090200000a14042c001849052483e15010714030381c180e03681d9048009481d5080080a1f950107400002c0744a038007600e81051182a00c04090211a5406401110041405034115640b103058034200f201070300e030385216100d00c10340b040d4041050a41c0100091 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 132131888 1250 132130638 132130721
    0x5011e0c0501240f0f03030c050a1a01030b091504020112060812030a0617070506030c0f0d060302040e01020901080103111801030b010501021e060a0b010306081e0d0201 74
    0x140562040361a11803e54540b18420034000300b034454030141c0180035100d408040c011145402c030314242400003001441070f603400041e051040c61040d5000f04502007090080c413a44c084040002ca1820780c0402c41e49000030b010444640b80b00000107480382d5000034441034045050450341010b80c40741d0f00191400c0d060070131050021a1240340c00300c0c07040010090300c902e41001d400040d0350b900d4218180400c83c0c100b5040803042110002540c041e800d030004581081c0c82c000ca0700d080d40c03500c0d428600e09141c400c1c040c104c0b0246001090281810900c1d5004d48104c90094030240103002c00442032038200d02c106112540460701440051011030740440b4207418001d0040e005441c28403008104041581e0268403c65a04d60701c60018862035030b0510a80460603a00010001d813407039540c0140c0d03140c640082100355070715070329030f10000c880c0e110f904010010072904d0300342c602e9507105245880d480d00294682d41507074440c2065160000e81705200d00c2140b08004131001520065607030701070008040b0b41012 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 132133138 1250 132131888 132131897
    0x809090901021603021b0306040201080a240b1905091305060301020403080309070911090604030b06030a021c0c0e1e130c1502242206020408070611030405011e 70
    0x70075483c51031054004a00c98000d40003032203400610480d40280d07140c203120050080d0415002e01c00141d0300122400d41190b00d034840440c1c0c8140310300d241c1c4800c1ca040542012704691003000000e0503101c410040028529600122002c110801025902441001c20140d00004040c2c000d16500c4181d501643d04100028000b40c40c00e80e803516913401c2908103170391001c003580103e041007103055268899130b001800c000b400d85040000303000c0007032442d001e2484082c0850302c982001485542d4284005405d06900030300c00f43c0b00045c09010749048052980f000c0391407919211020911034030783c85c00c0d544101c003c880f400040446191200d0032582000c1c24208140d62500d06a200041c3c050000300701030800b52291700ea9210b104c42c0024603200b8841c140480020a003404400300405d10310020f68000184a00142e09007038a014001d0b841824140c0642114070105000c40c4056000c11030740200c07501a0348034101c6500c290041c685a1107603100c2e40303011030100882402494012229007000c81d601d800c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 132134388 1250 132133138 132133147
    0xb0d02030610080609011a09040620190503011202060708130305010203040b0a05040c050f0d0c140f181f0e04030e01080a090c0b0702030102190801140607080909090102 74
    0x820724006040d6281c14030012120000d1000a00420007564840c1551000384030050142032004040a04099024010100c500006007032010940061481c05580404d030121803c0b07a400042c0381c1e401200b2102c00081c880c0f40541d501c1031281e0706680c140c034401d03a86852800b28960801032280d210340b00131140e100d014031200303c40c1c0c94081807040040d40500c5c00584d0720b01d80b525100380310a100038074405d4210b01d0305042c04003140310f500c407540540d04240c1e1400310003000c0c80e00207903109107000001403c220100401107007215003610049071001f010303a88048611030b01e03010484d1410344140e20391300800c4140c0001b0001100c415601c0030001503603410143c0b080d2603111200001c14100c60903008680305546100321960b00c0b1030000d81c403000c3c04d4400c004402060b82c40540314089885002a50400440e203c0c05543d003c1d81203030540284102c4250403001c181d90043c0c5280e00c04d100700c13501e50800310080685820100d0484422030360014000d494007101008000030810081c200c0e1869650912 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 132135638 1250 132134388 132134393
    0x10516030221040906090606120c091e1a0a0c03050a140a02010507090e06130f0b0301140106140712050703090e010b1309061208030702190c03121707030b0d 69
    0x1c0700c0c522030080307042d0322968490500c80302c8420740c0c4141d441007103050f1900c4000c22000f5072248040d4030002240d40f0109038080020821169140260002c0f00390b4494002814040852850000d04440c070002954170328849080e0307140076901031043d00c040410070185070880003078881d000801049500313040c65100d070751201e0303280c0206402194100c40540e5607441405034041d000560b501c010014010366510501c0d1060109481d8600280c62001391500d03418400c401d80002c0d0010079100e43c0c013400030401c0c5007805a100d08502003e12070500800e20400305080d088a1050442d54265042600301f0910710180308126100d0380b0801003a4104054060003181a07014400e405000b0100d00920760740f24012411840c1d0410190f40c0321040b420301d0184c041001032915500710065a03000458580c0360782d99481c061f410908415282403251254032104400c0007840c603c01c41c1581c1c003c4d41031041000b101e00c81620903c1c03840314407480c600214400950b040f840382c0c1100302e0041d006820083c0c02c14180d03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 132136888 1250 132135638 132135673
    0x80f04051903050301030506060d110114040e0a050610020f0312070c02030609010e070b13030201080414010c050a12050601141308030f0c1203010f030f0212060f06030115050105160302 81
    0x7000403800035100000401c180310302080001e41000c400c0302d1070300d110440340c0d44030206141c5044100d414044007002e600c0c01c0c112442e040da4001c22044400d40c58030320301240f442005000071070b4501d10901c0b41c0c0917200c1d40030388001038000c1810006d100440c079081401001c00340d18003008104c001000495140d45005803420b000d054040c2c0c030b01100218504600d80000790806c12960800f03402d00e4000e2009400764100420080304590b02801c1c1030200c2c0e2103608000c40441c4001d20048410340c20300c601d8030b05059000740207003500344499403a030034442c080d0840601a40c00a596284c005183c2d81041d02c0c445100e903004059408640e00545610f40d502d4004600303581140290320b181401c0451848542501070104030081c0e01021203079880c5604008000048804900000c0c0c030340b0442250b03100442d15181410118070600c03004503604c500d0a0b2140002440c000c451040c040e50070007142200381d80a0380044415128140c4642c0d0030703c0c640801100f2072013074400040d421441142e82214208404 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 132138138 1250 132136888 132136933
    0xd110c030c07060806030a032304080a08090901060c080a033206090906190e011107050102030402010e030115060e0613030302060109051b09040c090305010606120b060901080f0405 79
    0x2540064040d040c503001028200c0348006011500031f0700030301703a068000703544014021100960707005c5030701c0340e03944000340005280a6030308045142c0c498070b461082070141d941c02a149916080382c640311241c2c0c8503003080b01d81a0302040000c101c0c04041c485401194000d422130380c0d400011140c180100460241c0b510810300410f60480d600c810024103101c11403d01049403684000781c513000349210f007800d04115071190400001440550303900c090210000d00290001003c566140300c445485441d1400c056000798415203040380469481034001000303003818000d02c030b0500b0414a421007080e2400c030741504c8806014100a0348030408024503c41e24564408072005035000303500405596060841180880d500a010380d2000b442e440a041030b0004c01800701c42c03050300180c5000c18004808141601c2c40c50300750300300030015400c024008c61080d0b07000d0000e90701030104400620210700740d00c1c1030180511605007894006208000001c440207540c071302c0d0603080391248003280e2592185c00c0782035406841 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 132139388 1250 132138138 132138157
    0x1519110f040537060306080109080a080411150405010807110309040f020705010501080102040611030405030d11030d0608030a020106060801030b011202150a0215010501030b03060406110d0e0705010306060f050d110c03 95
    0xca2004d0082c0356040c0702c0e50000c1c4c03010400800c102c8400340c0f0781071601d0041c840340b5400c1142c0400080d0030488401c803482d02c5c101020f800b00100780c4499107248003a0304a4080d26000540707040000300642d205c0c0c1d480c00300419601014500c1d15809170180006414482000020290200700d0940040c0c42407040380c0c02401d16100050300c1e82d0410400801185c040c0003502c00769030050006000590380429201c00d5000c10342841c80c0044030701b903000b50031400b0b81490118220f24040000800c400048002d1520a40a90003004501e1b12074a043e90055420f01015041001c5c010060044013048041c400300240002c048103040700800c5403080c02948548107000058001005c1d805480481c0c6074298090402424248943c0c602c0c000800c2c2c1d58600100b000d0031042d00d407102040d030540f007141115000c005c2c070041132112040c12000f03550344030024030460b400645080f038005001441940520403c410035521186406200002d001c05440c8500074448026410401d24000c0d01c000c2005003080b00c0b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 132140638 1250 132139388 132139489
    0x90a1a0403020f12120304020d0b0a061404061410110307030f20031903061205071503020306100c03120207060e060a0501050102030a050304051519110f0405 69
    0x7411441844031010300a1440c074025070b080b00e42400208004034064604840452101d81c490303445000003081180060b10190910070b16000f44101040c0f690849400d580e41708a40d0b22405404c2e900341700c2110a00c0c89080300c5000a41c018181e18505144041045001c5180041d283c200703410700c407811680508002c40104211556030500300c0d4000f04101304a090128500308010807540080e40c03030b4410900c501e540c00348842e014000650080c0c2c801400f4001900890306980c41600c1c01c55520900f0340030300412030810103203487c040b41c030074001ca84c8901030103003c44d10190780d00c85041d140441c905038101d00f80700482c001001c0d0342c001880039002d02405180e0102d80348641d000d80351300b82980540712000c51030901c0d00500013641c001040756102e64040c640f490781c958541c02c2050910344440c04000340c07418040240710303c009030703907501c041d03241d0f61035000308100110640c4542451040e43d01c401d15140083c4010000f034902145e80e01d811410007900c3d001d003504818104680022401040c24044 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 132141888 1250 132140638 132140647
    0x4080f070603110d051003240b0f01140304030201410408040b1e030a0504020306010608060d0b0a18030f021902090103020d0305070501110a03050705070c0902090a1a 73
    0x41008114410050103a42800c100f010501d00e407000680c4038242034101000d45070404034039104020148000103680080d08001a14940100342402c889041450450541002800201494942502d4450200c16103030f4550304014007108400caa00003c00650030b40d503941d20025452403003c0004465965440c01450710070301078100301c4800300900300402c1685200c1c4002c1000240c0c0c800220313000e0f100c40a6910781c403041549c11480a000815900c041415800300620144840302d800c0140518400c905a410310ba803111401c54000c0401c40381d0b40d52040412400300e0203c0c00c40b28041e6002514480003040c0e641003600074010346890f881d0110009014000d1403060b81e42c0c18000705401ca071105864207113140c169000680144018003019205564050445007051700403c103d6804c1907010000b8004d11300380d00c40c00c3c44a504040c24400104e4200700024171804e11410440d861594880c04041c2c1030360402140000079049444003070341200d010344010609188207820203019110200744180c1c0c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 132143138 1250 132141888 132141913
    0x1306060806090c0304031d0a08070320030a0804050d1103012a030204050f1302120a0204030c060e01020a0f0c08070b04090b04050105010504030605040305091f0e220e0a05030408 78
    0x403404000d00c83d060300340041c010300c40007e0344541c1101c8096184445a250f0000803000120046d916512103ea5031054a01c000100030b502905407540d041c0581d010240c0320010400d1540f51840e404009040d00300400c81800546000840b524180d4020403041c2807803a1701d00b0200742100c01c2494521203400381d0300b002c500b01d04040d5680c00141d00040c6810341c10140390001141140c905028420711038102c00d4410994030300d05a06640909c014540044090b00b45124690000d5001e80015035a02c0c00c00c040120b003503402030030096030548043c0d00502500d4055250768403c400c2454040b1801d44a4110008040350100540805042910712041d0f4640c43c1940c03050440d00741a00190003241001c004002d45ea0b003100a0310304481d0040d001103000e503154038044500e44070b8510300907400940200d91441600b01207500d0354a041e00ca45901d51110101420003513140c00100c030030700760502281c58010030b8460603040b00c001d91800c84111242040303240d680c3d500315000707508400825404032111085 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 132144388 1250 132143138 132143149
    0x60509060604271416061101050402060913060f060203090901050a0e07050a021002070f0312090b0c070206040911030619030203060703020901110a050609010c081608061306060806 79
    0x100981d040780c040200c01d126010059034075514001e034480d0031100c40e0002c401d0061000c1c0c8400804c0040b401d44030f80324910400340760020315a0140800003007048640e40414101441100d0240750010042424025900c00300454090b00c00c0c4007001054032444009040d9560300d00e4800984040d801031515401c0c4c0c1c2c0c09000000c00160310862242c04180020000552202c9400f60040350328501165541039944042c1c0c9040c0756035003540c440500c00103064050140d050464085144680c0e03035078803141c010340c1d15201507070540752016100840003000b00341c064008c84000c104480c0302408445c10b1a5035034800104036a41c006201d000a40d0004c10070185107010b00c004e500100c00305048603005800c50300070075640d140060498090681c00100c17140540e00440900c22444050400c4070020315084c03800340c1d1120400d80320614150f00300080600c100340128000d521454a91900002031039400b10103c8103500003902c056040144100110b54807030040c06090b0250440f0b846042c3c50742000e406104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 132145638 1250 132144388 132144391
    0x50f0d180312110a0c1e08010c0212090d050304030b01030203120c03071203091b0e09030405030c0d02010306050d1a0c0913111603080a0f0209090a05070c080706050906 74
    0x311440e16184140000380112400401c1d440c090320b04400203480c844019031820340b0418000d0140480480001003400940000c14015816443c625121030390380c0310000c2c20f036440340040d2005a01b01e03407002e0012006441c00b03072030709010007441c20060b0080c3d51500c2e41035520035041661400f00c0c0c0001401941010000e241540c2840800c0c03600d040984112581c072030003032200081000e41d00c60ba5141c2d40b00c1c807070703003040c5a41604442d80f0100c034480e0105141d174440c2c0310b12070400c40c42e00300da00080d000030002c0103680807220040c1c080d001c01b00032101004003488480c5012418944d440601244070f071100d4241d00c64091081d07040ba0042a0303501c0c80700c242d0090042080c081035a00704109010b64031003511008414040796008504a100c0340701a80c0f65004003051108007451040350b140a0560080700345000d051192001c010040450b4602c009070f124030211503402c01e200c100440c2c11703081e046e400150700c11982e1814418960b1140d4800c980c3c0d030701040c025200140c84405100210300e0611205 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 132146888 1250 132145638 132145667
    0xa060b040605030c0309070905070c021305060a0306020708120c0703020c060a120e070b0f09011707021e0a05031201090f0603120f0309020303030f010e0708090c10020a050f0d 77
    0x59080501c1c0c800020014071000305055103010001c0302103400b01c6c0c0c080090b00c1c06007210407400c2c041031800d02d01c0106201e00180040e48a502c100d2190b8039100d900b8811a406624007803c0c8401460071501c40070065401050b007150068420002e159400380700201060041c0c0814a0440d81c400050800a04d010b583d02c186a02c00d0008004440c0e1640c0c020800344c10080301d03980040b03134245000011908000c90b03944200d0414000249468442842e44020403041409881c0e41040414610782001c0000044800d0341c090303400034204044124107403d1f100364103040b42c01100c2ca6449259509811504064141c05240c02c0f040b0060002209500942c16200c00c0e40e201040304c1d81c5103032903100300710f04441002c001703200740201202031040c401e801c1603140c1c0d5000f40840c6c0c4d0300c0c14031100f809003d00091140c03c1e29041d00c400400c810368441c0103201c0c046d1f00040e00804a0382e41550403c015000316603040c2040d481030b14102e00004005010889840125101600d00409004c0014050b009500c244 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 132148138 1250 132146888 132146909
    0xf031116030c05060108011118040209030a03090906090501080d05070f1e1401020703090b13030606080604050717071e15021c110a061a03060f0610051603080406021b060a06 76
    0x901c580c0d22400c007503505110300380051805080c2768202190084c4500e41d0541d13050f0060080d85014035420103201c1c0c049400d84442040916503610018040701e10a000310070f03258002c4800100207601c90005800f415006e05007103511102941c0e2201103111086102c1d0304002d60fa078203a9000d1000314031010005c118210001d43ca403174400c1e44c00030703c0ea000038095001c0381400840c100060002d2101000d01459000390200a02e44c0c032201034030350f641e0045804881d1440340c108003081414040f81d03609001c800c0d0b400102002410050105403244604080c1c49501c2005140014810802103201c0c06c43e060a030040c0928034500201c60303400550740004001070100a032510704921000245019043d43c00c03100008052403503c03031100200281c03291159040c41001d05125130314009180c1140664000c540c0880320a034945400d4410780641d40721441c01121090088001c00d0084000f03e40c014070450006107081a0040d85000b01303c2c020b1002c411503440a01001000340c0350388038490160400382031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 132149388 1250 132148138 132148151
    0x6040609240c080703050c0a110f030a030b0a0f05060d020c011b0c05010b2709010b1f09060e0609040c0e090106091d010f05010c03021504060c1706010f031116030c0506010801 77
    0x10340c00c04e212340d95041d4200f0100c40d048900d080001d0050081036200641035030b54810803680024060070031000c00700e10543c0c9428001688a10307000703212048542c068030660034014a10881c4009412000c03600c503140d5200c0c40801902c0388005550705445940f80c40381c5070040c059007029800c43d1050041d56010b000001101011180318010302001000100d034a45465501d0080f02e5003d8043c000d2000d40044074400118401032a0050154842400f03507600c02c520740d50341e04c0882d2030224a029481d0820b8040065050500380341d088050000928185020300040351000b15444e10b109030700060005842c03082c00c0c00040c040c0e4400314060046642540e1007035040008203144800c152154034140140c000140c0105030090000d503400b582d48414610b00d1b0716090800c0300150580301c0503840041c40081e00d60f811741c1c20401c5101e00580e0b041e5200c1818290050007078006040d88280c161103034605002c2604540c4141e61142c0b0f06600c207648050710018203180c03091400038183c03c00d20b0f0a03410b150 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 132150638 1250 132149388 132149401
    0x9060207062315010c0512190804110108090a02120309040f1401090c17010305030405010f180504051b0c030a180e070c02060d2c0f06040609240c08070305 68
    0x51020b40000e00c51443c002d030a0b094800684210b50f05a0009000e8007800003540106c0021030040c5c000e540540055580b40c107a2018201ca01c0c5804036401800002c0f419015040e0354841c008503a4003113001412695020a2600000d0791203400d5006094035a00004003441c203800c140c0146040d4000380c00c401d00491680c000301c2c02080605019110721243d803101005656449101522002002d9002e01c5000d545c43e410815140e9000b030003000e0100e403943c1c888000003446600d18640c8504044400d0540c5410603040002402e0003524840d41c801504031400564a4460000c0c0307001d0820800544d9104944000039007000706980c0c02180000013070804105404c00b0030546036202c11285084031780c811071480014142d0080c05070480c0c085140c54a800201e01c001c03004421410782c1c0c5124203920305a100012540c885585490407010703080000803500080e5a40c003d40315051003080e0407400d0240c030319941d400c5040380f103035400740b070179121400a0082d9400803415500584280f03020f001d5840c114 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 132151888 1250 132150638 132150701
    0x50c0102010c090612020d1803050717030402010c1b08010204060507060f0207051b03100603110102060903030c040b07061b081f050a030308070903060e03090a0f0f0506070305040302040906020706 86
    0x300202045d4135000240381d8401000d562104041d03088041441c420500d041c01c00400f280c00042c0100c41810b510005030300c11084060949210720344c16910380d1009122691902d503000542c0e40f044900d0791480002103066002070024002500341640c8084d00ca030300300d08002059592802d041e0600910421404010500120b884014001507010a60301c2066000c0030074601404484540700041c0751038804010071180c032401910441d026400c030381c0c180e11a4001c40d6180d10003514035014282003004104200e0385c41c00054030003240076520000d11030f08100420040703094240440d00020300a01c003040b40f891a03064001d2400382000d0350b403121180c00c180c04202403203d81c0c000a0f040c0301015002a204c00e110340f914802a590080b401d000c0c2c42d01486106690740c00400750302c0e21480d040040800c42c0c07000403026604079141100a481c29610340414007285610400040c0c04010041001101685880c028051100d02c47c41c00103036106154107090044a141101c200359208505c1c1141000c600ca1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 132153138 1250 132151888 132151907
    0x20a05040510020c210c03010b01050901030e0a0206030901020316020703020a2601060b0c0c03010b0307151e08100b0c07030b0a060306050103121e020304030b0403030e0307050c0102010c0906 84
    0x10b40e046007080002120a900c0c000b848001c05a001c58554820f11000414503003c042403030700c001c12038a80742590300800d0b0030703901d04d07083c45070001d081444031481070b622a0300700d85e104c8404041075500f410040d0300400c100f80d10840740c0070000c0c0e400100740000c407460302d04c00820a550300c0c4090108181940d002a80c00380161160688090003174540d12105142008016061a4810005c0042c02c0da540018401600f080030711003000c0c05500011171040c101030155210f21a40200031f001e0850a000d1840b50784103441d0b408904002440700b00020b075582c15103503e039100c00c058440861624142d440e89001294035084000e800300306100600740d44000042c0c1d0000d80350f00c10b070712070443d6584e80000e00081c4000c3e44082c0400741060000418003441106050b49003a19a032043e919451a0500300c4203811408207410060b80700700401c000bc03507450301519030010304c04d14003c80c00004c041c0a1610716088403106540d2900640820b400940c0c0900c80c5210f00b030020b06104019920342440900000308 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 132154388 1250 132153138 132153149
    0xf0712050a0b09011205060403080a0b040207030201060f050a3206130f0b070b07110c031902040b0301020301050321040e0117010606030501080d1101060302090709141804151d01021804020a0504 85
    0x807200c0440d00bc0c03500c0b60810405e540300944119111469800c00074041c10080c403401c0e00007111400c002c96181005849030042d20b042c2840d0b06181d070b4400244040355880183d82d601c40c1c1103003440c00f0510399664401800740d124518841c074800750030100b07100ca00c420135602c0780e9050841003140300001410b02c1c80c43d562080040c204050018201000035091128442107540c0c1405035080d10032000f0000d5008007009802130340e081000c0243c400900d400c0384400c0c01655803543c0140c4844203015800070000e103500d4125021981003990300c6201c5003a440d02a00492950541c4024042103540248606030003000309243c01e200b1545400701850300c2d008512001c1e81041100d5208591140e000d402140040d41c2c00381240c0023130b240c10303800180059401e0041c0c0b004400076516030800d500e80018030f410442e81c00076102502d5211642c8141e90b062521070b00010103904c8500d00c000a401c20b06482c07002d036510000150b52041e445101001189901c81c50610491040c00558503181c0c0c4101035400340c60 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 132155638 1250 132154388 132154397
    0x2090901181b0f030c120c0f030605180c180607030f02010e06040b060105090d150504020a12050606090402030a051509011d0c06030c0d0903051206060a080f0712050a0b09011205060403 81
    0x5e003080741211a1003000003460307800c504020384080c0035507202884800d6401e8640e001c002680d115001c11001c140c0c40c610712144249104042440300704420000c20001c402181e0101d02c8542c00000b09081c1e4102c1034054010400031811586250340a001d10041580c412024142d45d01e055a500b00b110240070f06421f0401c040840d251600b501c0745c0348800c6903030b03803c9501d000440880502c00300160104540c100d028040c0c030040007404188030000301801c180e002010308815070300d0030144901c1c4107000340260f0781485440b8917100461814021062011141c501840043c5006d0349150b080d294403181c00b8107410f0501101c1c1c0c01c078000c0840c94100c0d013203045030740c1030390382e01c1d10b142418280c002c0c04911040c0c80e2508a1085c10560400007c02d18000b000c100c40105560b4441003001034000c844040380428070a000041c1e440c187c1c80520307079020185050804a03280c1042d0034504460048640740142959070b030103816070b450010748040c014007140c11100a0180c9507a0740c2a00c401c8003400003020b01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 132156888 1250 132155638 132155651
    0x1c080903100e01051006050703050901050901030b1315080304230301090b090303041a06060304060b0a0801020406050714031e0904090f05150108032b02090901181b0f03 74
    0x156418003803101161100c1d1800c0c4044000c442d1554000c00090352903101d058019440040c5c0d0501480c00e0b1000b498040d10781310f0401c0076403001900e80c2d6021490345410117542c0d801d0003901d99a02400a848105041c4002032440000d042080031442c0b0303a00013004e00d50040c0401c0003102d0f20800402d078600640c07010310107a1070041020074094540d01100600011620040004095000002c0c0d40300b640545041d01d40c4d0350040070403529540301076601c0c41d0400b4082001602043c101d82041802d05006002c8036075080e5110031060890f00142c01450024a0000c1c10340107000100760380c3c04442c90048045c51500c5841c0498007410000f8401c2d1a04d0b1450104048850381d455034080070009070040280781c41680f10303160840e104e010710501e101d601207509001007100c1030000f050b00c0082c881c40d030342c00d241c0d0707510140b4440005442c03030b2000c01c101d43c00704400e00d205d4076100095030080141812220710948030075110700c140c80014030241d481180d2505250752640c0d000e282d1184400c001e04002031131 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 132158138 1250 132156888 132156907
    0xa0f02011a0a03020f04090501020406050315040506010903140703080309010f0b060405060318010603080f0306030d02010605030d0c060609020c0c0307060518060d0212090f01110c0709020a052106040b1c08 90
    0x1c0e11107d0405041940f0114000a5554100c0d008512480c5600c05040000d81810100011110107495460000b01d6210060000900702c0080550541800c0121404140e40b6903070140941c1c0110380c40030940c0d46403a0300220a010702e004030300e807110040b150b203030800b400c200200390b280c04000d18030340082401c903900500c0315130300b9072045002e1a00040016540c2800f4800e445943d441500e0340fa0080c4184401214402e02c10b2040009496005015020301684280704440003100c1070000d550340343c1e60340400a484401840104152081d540291080070000c108140c200b4981d54095020b01c0010007040d01c000c0c1c000d911072840380004a5425848507100c503ca24001d0080c006802c01e81601d00c014403030b007000005162040c240d00c6000a00804c01280f01e1903070309000d00200c104403a44500010b001d20a01500541900b281c6c500e02607007848020038450080b1800e010342c15a40c6003002007885024102401046907101094a032040451450260041c103201740078409000b082d800705140c004d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 132159388 1250 132158138 132158141
    0x7050703051204300905090a0e0105090f06010b04080a06021605011e1503110405070c0c0b07030906140904050619170c032d030f0a0f02011a0a03020f04 67
    0xb81d1400a03920000c1c5103098076041c5400e04242c000e160001d1102c8007040b203c607070410303c1d001500245903100c500b00d610303141c24030001c8200074100780c00c030540310700381e0fa030509000f446114030440c21000180380820000380018149070042c1c1200300c00e120100824440c546c00090b00f0b140840d0f026000603a0b03034a001042c0001e6601b49175004089500300110318130401502c0d91403d01c0c07240c000408102000c40ca00c0e54048055962000800c0c030b0060b140d0741075a6203040e510055000c0c003141400b41104000d0f0b07949000255003500b01d4407007000e02254200515900c010b410b0081c10903411b03c0609103520300007051490107040112840703244c903880003c0c51620b131100308048800c0c00340030082c85280c80b540d101c0100381010190b4030341d07803046103048450380c0740028000c1081c44102a5000380c1545180d0700c40030b40e030f442c0c1003558041d2008001101e8501c080b00028002500313642d03a00043c03058013000080c20360b60ba011440c0305030000f40350714119642d43d08012004480d4121a070030b5403d00d441001c03c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 132160638 1250 132159388 132159397
    0x3020d020d09230d08040f061b02010b06270a0909080706050a0507050d09050f0d0f080a02070f0b04050a0f0b1e100b180402041401080711030a05070206090a03050106061202070b0705070305 83
    0x1003c1508000427241e801107582042006d0001c00d40092213103000d003900303001d00c03402058400b40c90780800c00d05070701000d40e64030030003000c240c0081c04c0490a15150403004081e502500c80840d42035034001412000d101d00c51250540080c80d00310180620300700f064004101d4041d82e1074410105603152450010082d04010080b603104896003900d4101d0990300c4041d1640105540c4800400d11000002d101144640308440501340c4c01b40f111031092090340c41d111007040e00248126172030303c02c0c07020350303000b02d0351040520200c903108803640c0b0494904240c043c1c4200d07420040c0c48610351284003d0025841c070085400f0191090b0804040d00c1d481e00b811f500b12005036000b103003608a4800540400d00e01400d00c0500039900f8282c03611030882d00d80c505d049400841c10050f501083d0020710424100c24403800060018030f00091266050003c0b83c0c000900d205096802101c103695a070b8000c0041941044641c1d0f103c94405908608100c141e4440c1c040300400200402d04108002905408141c0180241c0b03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 132161888 1250 132160638 132160643
    0x10b0d0509010b0a0308030a0f0b0a140102070b1315030b010f03020a170c070501110c0a02091e0f0105030607140702190e070305090c06090303070f0303020d020d09230d08040f 77
    0x34113981d070b480c10141c9080d401540d0900c280b80c00d02d61200e0208055004512121002402202003c0e140c030405681c10400c1e280032038110300030444d001442071910380c0501031a40d800e00300f8029182c03500b804458800130340b11000301418207101030314202c0d0383c208080c550018a03e05026a4510280d0030445010003141180b00b81c8035100d50510001c080b90b07402404201b8800c0f8020018807400d001e0140d901d004554096116038000509180103050009840e41c22001389001e4162800141c1c0503542ca046041703482c0c9080c03001d0000100170903d010401240c00001d2810b100201c80c8904115140c41e204285020703025021040031202d040741c401628600501031110011020300300b2441c010080c110548031510700e8440c0322000d010341c0c600141194003c190040045107001480e56a04d10125151030f025000d05909202030390142107140002c01384030244103000142d5034032510f4031403c822141941601e50624038524140990400242e820890791241000c5520f40d0311031030308544912121100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 132163138 1250 132161888 132161899
    0xa0f06081b0301180c120321090516140603100515070623070806040b15071505040804030201120e032b050403120905031e0304021503010b0d0509010b 66
    0x481516038601c00380c403000070400c900900c0b0002c5064090b90b2580c51203400541914176075642041500d1000351000421482410b1485003071100e2003000100c061000c0c040d840040c1c0399494481000828070903200f102294641000c440307400c041c8080b4500d42c00380e08031400703418004049040581031403d00801024000c000c8490005071816019007030304094002c4809908059000100c0010060428100b0810910141c8941c1d242c100407500c104010f04419005a903480340c0030007607154038000c84542050184a40d60b2401d0519104008154003242c0c01441881c0c6400d102c0011900b17402c1340d0807281c09103020075407041500d03440c100034070694141420b5444001001c405405a00488282442c3c88104a00b51045002214002d840d002c49000300000c488098401c251040c0b5400499882d02805c201c80c20b0a0441445c0c000d000d0600781801e44c103100120400c800c51400c121400020f080f13100046085501d088481d0704c850140314000007440c1d0310340300001e00d100d500b540b0916075818018203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 132164388 1250 132163138 132163153
    0xd020109051c02150406020325050f0616090302030a0b07050f041d060409032a020603010f0801051b12040f021801081e06060f0402040b030108030414010e03060a0f0608 74
    0x8494501024104034043d00448640204c0d070b480c060b0030b40b0104e81203a0069440d10401da0040c20030510321000e054101c1d0400c40307a280228000b00300703103507101c00a600240718a062648040240c056612192001c00110710303028801601c02142d48545107074003800710305c00c41e126440c080e44d0340d000d29958900c09050100c1c0014580007444001201c1c500d80c903040e548d041c2c0760101408262410340070090049031b035000410522640b215400d82c4041c6c0c415a034441c8a004541c0010000d070720aa00c044407070340e0707c411b05015040e02841401c1d0000101101600318800c5141440031500840840501c41242c1c07200090034410030345102d01090703900924100c3c600c4900514030300800428000d5410501c40c2405200c1038580c1103185801c441c1843d0020200d80e614201082421040c01d4a56a0460b400f80000038042051902460180c254000515100c2e801c0401c904600504a0a9a0304200c003076108640c890b02c0100340180c100c000c182010610802030040702000e0301d500d90084101c0d10807184c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 132165638 1250 132164388 132164419
    0x310150201140a05041a040c091401050312130314030f070308090c0a140906060706060e0f070801060909021b030a200a0803011502010905070b2101060207050d02010905 74
    0x62100c08105450708a80c4825103c22042e081210710451300101551b4220000c640a1806450000e9100d48a6480c007103645460390035280540384804907842e580d42c600001030145140510060448003841e40c0c09500f401702c3c1c1c41c0300300c81c440c0c26844081c5c10003200300002d0382144004d0003103c2c400c00f00e007007030a607542e003d51070000c0100303a0854403580c0e140030340b0702080d04a2500b480b8a000319001e0904c13101c0e003030310040c08101c030010014090552004d800c000c100e0004407140610300c010006003210030001d207488540592103400003003240081000001c0103110300c1d5080b00300002503500f00c0380c005850700ea46001d031503035180c2d00c0c4400e14003521000c28200c04c403e81c411700c82d40c4000c1d08245002060310702000055a5903907038590040c00c1c0346c8140014400c041450307000c8034218289100202d40801c0c00d8842c03605203a0680c01c0355280c007400081500d40c3c000c8001c0c0c0450b90b0001d410260b03060350300d0118000c2d15180740b401460b00c2080280240019680301d508290045c1c1001071192201c00c0490 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 132166888 1250 132165638 132165641
    0x60302240f18030a080c0607090f06110312040f0b090d050421020a1e0b04050607030509060409020f0d0c0c02010c0b07050705060903091f0f0c06090f0302010b010219080403080310150201 82
    0x42c1658400341c82000c0015511510640040040b0752b8180c1c41140740c1c0d03081c44000d442e030384c408108003801c0b40b1061020244211784030126130b0245008040f4001c03ca0001c1c204605665401401030a071644140e5201c062a544030045a00b25070a5030307071203410442c2e100c404203608001400f005c1c0d48204400f50118800040d450500741e620307042075440d59155900e0704106002d0240e4440c9039072206040c400400401e0203074000b09407900c4014042881c01e5194100101243c10500000f00d08400c0480c0028081007a44100c594001107070070700c0c2c04043c0c080e50009006e0400050010312041003040803136642e0703004006880245a100d03064909924158141e5030380ca03000102d09070b00c6035003c1403e0140441003400c4072280c4688503601c10746611a020426101e42c20800400c50381c9e40d58403840400422070a02805007050f1203640086408025800020719100343c00d0b00c00500600f40d00403100009071994101d0f01202d50050000e80c41c0d64071002a501c0d6102c1c154400300d40910403038070810b54503506 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 132168138 1250 132166888 132166897
    0xf0103080304020a03050a1b1a070b1b0f0a09050108150409080c01090308060a05010801150f020c04020301030803150307180902030309040c08010f1a0307030902040e01020d060302240f18030a08 85
    0x1c8c41050721416076600041c4d6011620920f887c4140b0001c00c03240340800c88403000710307901281c13200f0608100e11412141142560110101c100422000314540600c0c070350043c2d13500014079007440e06007440c3c1001c440003040361032860300c6607104944d40d4883c1d00c100079004041c1c40b00450840001c0041110320b04001d480c500c2c084480900c109094800800e0365801945124145d583c0c00c5901d403403501c0808001e03290001d00100d40d1095204421040c6901c0e66140010f42c043d40c0321f40b1106440342401010321510001c0d4007001842500842010f00000c0051038800007165980280410b80c580c0134008a4107600c103802c1c0345c030340045c101403032120402e41184490b41240c5055031031081442c0e03a0804420781d011040041c40c501c00742000400c1c98a44aa00400c0303025000900001c3c00c015401525801c80c1c1c0304070f032900000d51300c0300020801d601c0c00ba0740b10418554084c41d04002a80b140300c03001e00b5842400030720b8900c8030000c1680021840500b0300d56501020250032650503155a08040300e5a400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 132169388 1250 132168138 132168173
    0x2b060219020111070c17031621300f09030201050103050f0c010c03050a030f0e160e0906040305030c070c0603050412030e0601032d11180f0103080304020a03050a 71
    0x2d05181c00840c03d04030044803820354001c158594454142502243d02c0c402001950007244070a0020210029412200c000354600c17501c0c09010729113030341142c440070700700c1d4a80722400d000704403000804104a590b2098080b824610301114400d83d00120f690044c6480101090003e01d0440ca44042617015406641030341d0080d400c8400d076440c01c03005c043d940e259403c0c810740010100c082c0d800000380900050032038541c40341000300e000002c0035010011911203008003016030b40107502041e132050700100180d0252140125201081c600041040d41d0381001400003001c120380000081c5c0d02c00b0550080e60f02c242d6100304400140ca90f2003000402800d000c3c7c5e0240c07603400304031440d40001c0b40241700360039200c100c030800317410541c1c43c50b100e02e00046000345c400841f1071a1212404010406d82103418201c52045880d6520500c010781407050552050700100c1d007200b100c80500c41c4c203ca61000d09411264403840742a41ca58036403011800040c2c003070f84000c1c844d2042401c600308004822500b40709041d03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 132170638 1250 132169388 132169391
    0x91403030604051b09010c150203040302010c0f0201020f160c24120c020604030804021f05120106020d02120d0209061810020318012304080604050105010509062b0602190201 76
    0x1100c244d01001000304244116003100e0041212a00c0f81d40600c0300d85580320b00441502d89260050105042a07a10499007100140d544140105a1580094124506c1c180070720007141032080361440d42c1c0c0b040c481c0c0c80780440d200148a50006c204000070301e600010700010182c2050304191200c030303a00340040030024030000c220002c4404045014900c40c0464190310f9030300924468449440035102601d0207001a60800002d00d140c601b0f1020042841c2c0406116590f071581d100b0700c44602820449041e0042411504100340b0440711560000d140c1c00c007110009007450351041c0400e820700c0244181d408890f044280441c074003100d8890301da1505940402501c81c0d000c1031200c0d0100300c0e128400c4140c80448514240007400d15540f09502075446c04512a07503c11140081c404004203682240e404885594004000c00007042002c2c0545401000240e44d900c000d0709181c1c0028102016503404000c412456146944a00804190103400e580c2c12040845d622501001d0f91080c0d440741418900c050b6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 132171888 1250 132170638 132170641
    0x908060106021501030f0c050402030c1b0102070c210c0b18030616050c07050301021b0f0a0305030402090411040603121403040c050f06070803130605013609140303060405 75
    0x690000c036050811039070300c0811200c3c683c2160750f444807141c40b4030300c180c50407403800c000401c25031940e100460245603841c1d10f41ea01c4865100700a01a0b010306954010540d00501c61040000c001ea4014401c1d40e003042051818807400c06008804810b2603c4081c14913080c4810014541c12220000d2041c01544103001c3e0384200780d0024140d03209000c1c0e544101404803021a800043e2082010f41445200300042d81e45241c1e840c40082d00f680c01890141107030401443c030881605100704004c01000700e10102903c0e8668503920040d03d5800010406030040f01410001420020080c0c28a0f90340320380100104209a120b041c501315001c2c000080d40e0104075028030610318007030100300f83e0b03209517801441e00300840e0400e401c2c0184200c81880761600180140440700c002508071015511074072254254682ca10610b042c08011b950040c0d00010408070902480700701c10980c6101c0021440b45506c0300784003041c0a440640040c010b0f0070000c1d00074001e030844060900b10100007507000b11022103003480305 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 132173138 1250 132171888 132171899
    0x40b0c1801030b06130f060e0d030206070807090e180d0509030303041106070c06030b041b050304030f020712050714091003030309020d0f0f050d03020c070320040c09080601 76
    0x214454004002015848418003084940c4641c01c0304104510140131541054000c8091403200c03d1650000040e81c4a1a001403119a13800005000003c40450706554204115100a511070307030003504007800c209010740096851030146545800420044070301480d20321302954860110081b02c4c0841c80d09019030641c10b800d441c42078040d070310809002005149140c403035940c2d0210340b0000110a5400c81d80602c246404100d01403400380081c145600c001c039a00d2007030b41c1080102e82c100803070040491109244151042d40c80b000352079105506003007020550012101c00e915012940d4001010b218400ca045802c01c20080b62200c02c89904000c0000d802c1c4101042107110041100d00c541005001041000800d1280d00a0070a00e4000751407510705003016110021405003960090300c5515441c01c081d020008200030341242c00e08a4030f0110b0070201c00d4640302d616a0401d100140045254202c600760301072407003151a80100000b001003001d0801000701500010540c0f041c2ea4080c021040001360 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 132174388 1250 132173138 132173161
    0x17040603091406150f0a21030f0302031509060f040c03140a050f0f070e130605010f0c0213020a0e042a020607050f0c0c040c0815181503030d020a08040b 67
    0x90403c1441c00818041003000380017049a164003c0c0380d001d4450140011705036003c2c2c446d841c1825840e1000c40c0490b80a05016100008502420003010300c10002c1000f5242c035024445a01c50049801c42c101e600d0b402c4c005001942050a4603900500e800c01041c403854260780004540d0b0b2090008a00030360b109600c900031a18200d480c410441046000240110070f850526139100900e401d0251811240501090b44401e07580c000702d4110f6501c00084c04290381010b0100081601031801d80040151036000c1049104c0486113040703559008228145441d00aa140c000010005802000b48000d80e0004113042c2542001458502200c64041007410b440443e51901c149081c2e110545085c0310000a40002d500c10842810280111840c82241c1d50315400b81c89000e504950301c2e030002c0c1c2400e060a142c110742c0051802d21404c101d09242d201c1030441542d1a03408040c1030342c1d111400f0f1079200030034118400c0c08400480c07207100048000d511504aaa180d00817801803845818940c7c80c64929013 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 132175638 1250 132174388 132174391
    0x60f0f0607030c020105070c0f0f0b0a090314010f090b06090c0c0a0809010e06030708010315020a14210103080304060c0e060909070509030f030306040e0a03050301060c17040603091406 81
    0x250802030400031840824000d03a0001881881072520520b0030385161545110542ea80d00b0001c8070508041e810404e200070216010003500200c04418501010048043c03d21b540ba4400240f000300043c0026000070000c1d0302018010407100c8040c44003640301e280844501c1d104881c124880e83e170440c0820203010b604820b850300529610006c090141d041d450345079641d080105220f04010b00c00c541512580c0754100594020304460b182ca007825411440e040c071884541e00c8070010880c0c0b05001010109600c281e2000100007980034441d0b40315200c811140c0319101200a4241c50300b00ca100020800c81030000642c4124003a801c200500100301d1340403681c1042e0f0f056400c2c0d0100061040724000e1500442c029040070a90030030510309040100400d050000c00e400301c400d0303030704040200034803400d1a004890404804001070111844107a40103070541c041805501c0411031021414020840c002041481071425601d02c16100c5540c1c1c00c005024041540040b81c10010051514110030300001e81203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 132176888 1250 132175638 132175669
    0xf0e030406020a0f051f02030f06030c0607060905010b030d02100b01020d09050906120d0203120612032d040e0a150b0d020c12040f080708060115030c021f0203060f 72
    0x625600049444138003694035144001d072501d00880040c5a0216100114001c02c41d5800307001580342d20f00020080d071142c1005218034081c0d045901150b01c540d84000c11201000d50021000484020f41e041c56401007522514280d0184201d00a10b030503241c000030740411980d00d1000c1400b90b6000c5d0b0004a8640c00b13550b04440114490800030710003443d0450071071741d00540c00351180c03403861111902c4134508025100f2440160308000f541c4111041440d8500f0760001c000c0d1001c04115014040043c0e90b031283c810700b0b600b4000c1c42000705c0381e14941000b10515000b04080405c0e00c0e541c4441c5900c007001340640e032030380502cad01d0701d5001c0007003a60752424002102c00701d045803818100c0c554140c9010750300103511021b49015011100c01407003402405000900126001d03400c049050990342443c10825411003903d5078410401001800301c40700901111240b03918012420a4802c4001d0340f4000e0401c903d4000c41044030b4800340c12a0031035019511a40d000c840042c440503c04080c49025030424200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 132178138 1250 132176888 132176893
    0x304080a020d02040f0c031a011419020a080703170702010b030a150605090a060314120703030b06040510020606032104050f0105040b070b090606060306100e0102070906090f0e03040602 81
    0x1200c054a82420701840c482c0c00504042210b100131090f04045501d0103010201081d030710940c4403070100d034001900a18140a080c21504126200141c5680740508094510180c114200c40408a8400e102c080c1e505984803d15545560340e500c0c000c0c19040305004079040c980f050100140c1c01c03070300c14020742840c0000900949841c08140e100c20345001680001309503529140c040000300354407010700c0c85204d1000fa00300041c1032070851506403000303e0501040c240d10380c801050103030891071885c1103400441d414140000e0002c990004940580941e910003030f809951058400c1c141500821121701c00e00084041d100b00d00d01204081850317410303400307118113030342400d01043c00542443d0405200310782c4141030080c04c1039039810b80c1ca111940700d450100c41c55030482051091020301040070b290400ca003140c202e03055142034000b06204490b811011030400c02c803512200010790007071004034041c010100f0705120349030300c0d0107204020304045400c21100c0c51400d40d896400d80740220561b416030f02207501 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 132179388 1250 132178138 132178153
    0x60b090f040b070c03020708120d050106080c0d0504030c060e0114090321130609080a0f03020f09040903111b152b020c0106150815010206061c05010e1e030408 70
    0x411112004c13005000c03403c4d44501d030004500701504110760b0a01010107154281e81c0d50488800070f05440069014109000d881d00070320800405410682e00050301d481e5001690703a48a0070111003035100d5000150840340f5003034104c564420b06400142811400c2c2282400588031440c4950382c0b0b10801080c109080c404030901441c5c0c18034001d103d900242001e100c00b0301c1c014980c070703200115000c402c800c0b500035500250046410f074022070072403445071b02800c045043ca200490f081001c4d00ca800030030351085a0b51800b0204150240e006c0d071032501c40400403100a0320074170464002074030456101c54130076092140f4110444584504070b03042007a401c0d110b4400a81740113102d0145085030b05c204c4100c0b6400b03000c030a5030146c09124401c000c2032048040c0304094824a030240c4511009070074001e60349040c040044959030006001504044141e4000b5945101c85c03040c808966800100100a9400c2480c580541e10000071801810220740d0ba12029002034050201d940b40300724800c00c00f9030b4100e0381 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 132180638 1250 132179388 132179401
    0x305070b0708070f18080d020109050f07060e01120f0504080301081b0607060b1203070503130603090b010b1605010f060501080705070507050d0c0e0f04050c0109030302031803150103060b090f040b 86
    0x200d0174221240e142492002d02900d40200c142020403001000d001070303544000060a116080140340481c081001c003130100581810001070856203484012818011441c004d10141e070700f41c1c0d101c481c1048a0b00800c020500740b070314111261341d00a104803500e51040c10135030148100a001c105000080040a03a0b2030311403141e958030090101022803a034031440541004940003410b00061410520031400703596503000801d1107408529260704450101850030000c00002044004200e040da00540c0d8120b4850701c034411398640c8212000d400500c80e50078008800b01c00e10068000600b600e80076210740d00c040e502c0420440300703030180c030201074225401320304108010f04204201c070395102e0250010b5103006440d01040070502c842600c0f0031810800d10400c00082c8001401202c00c840c8003442c10341842d924648000b0354074040e5030103008051800c840d007621603a40401900c2415170300607111840d190395a06001d030081401019035070040110500040e00c0d03c0094803520322895120683c824642c880d107 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 132181888 1250 132180638 132180647
    0x5090a09030504030203031207260a0f0209040e07180b030a0b040809040903020607020706081b0f0c07030f14010516080a0905071205010f050615130308070305070b0708070f 76
    0xd240603024444100000f0015880600050014031030080c05000c82d814402c03002480540c1c10401c0c602c403c3c841510181e0b81c904100c1000d500450483c0d000305004849028040091066280c40c591040ca441c1c0c003403c00540c0440c20b0002c80b5103203d0840011800c04802c003043e90200454a645504608902400035402d80207050704240101707056810200e071040400c04550406406038056030050701000a8507070f041003000302074100742c034107030800c0e0a05a00401e00206190309060301c04074041044d04804845d4000c0d00c13413500400701201c00d01d50f41e0307003444030301d0351100c7d0301c2a9055440c0c107104041d03105050003070314002e03000c0041c50a00b000e4001d2003191902d801800d1110381645400c04000071075030800078140507009606035429078140919080d400c541d401d02055216605100070004107507a0452014081d680c0c0440c02c1d55200c420803540384400e41c250f0002465007401198900501d64800054941d16100303a000305110385444205450344041229803c001413844203a20351800d114 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 132183138 1250 132181888 132181901
    0x616020c190f0f0302090711061501021005040602030f07030204060e04020f1902010b1c020a12020118090510090e07090f06080601141816030545010605090a 69
    0xc032981961079544586020394042030940c003080200c224080d0038410742c0f902c104280d4000e07009040c00c1205064144410742c030b40750010070b91129901d1003c200c1c3e10300d034000e00c500180b2a585030400c11142c41c01d17282c01d8000b5013040d201c50000c410040d00040e42d250080c4219425500b2640300c4149d0ba8407043d0411000c0c0d4001c9452081441d400d2042c92204d580c0c2079040703a010803060b00082651055070042c010900005400c80520ba440c81d1400b9002d40c4402400c0e40c00d603411480c40401c512500e00040e10034013001c040794500003c40c3c01d0b00041e030410660150b4050300070508208249070741c8002c2541560495010203065412034041041081603e600c40e00000c82c144c2c801140381c030f035202c18142c1052000d80c0491002400c0900c0c10a41c1d2400c50300d408400d0420362881c8010f81030141116800c0d020301078070030051540d02c1001c07075819a0803d201c040d00340a01501006c3e04400140d00c2c0034820501c41e0352441e416440088085100c0c07040c01244280c1d800902103083c1a80e0701c0c12028041d042 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 132184388 1250 132183138 132183169
    0x1030603050d030b030d03060b0d0506010212040608040b10031a04030e180f0603070e010e0a0f06060e150408032203060903051b0c01270b0c0f0616020c 67
    0x584100000000c1c00034044000305103a030751000500000c1c0203052500704440d17049900201885c2610501ca01c402c84000e8070b5112201140005003561074800503860000320301d80c1d4a08031a8045070010301c00b640440d190707210b0740c410b4101002c0750b1075690004091071070314000200740400000d0a49800109568081e5019000c0d15000b103c103222070000c0303000540e025800c011300700c4880c0b042000590b41d8002d4281c000c0402e60003410414600219610b0301401070041d9601c2d100440b0210311014107980021044e680710003010807000d46d5070b4002500e880c1001ca100c43c000c0c0d41c0e1144120303841e0404400d440c02c03505110045c5140c451380c0a4040000e401603005180589042d410200200704c25104a04400e4800d480d2165908420101c200c81145450580d0881c0e6110003210312203a40d2010100c08203140d400e0340081a802d14603040b0700f0032a965008032100c840081814501918005030110502120000307640e2181c6440f000d024101c0a1203030348401581c40110802d12906044000024041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 132185638 1250 132184388 132184391
    0x81501081302091f08240c0d110304060506030a0507060c030c0b1f0f05010203091c0204050405060a0b1c02150c0105040501060e060306191a0603040c06020111030906040b060103 78
    0x603658002061248141c1d02d00601010208504401c0800e00d0a1200074103417200c020a40702c010100c002c446443c0d104c81c400c59601882003ca003000b0003030025102c00750100e039000c0c0407a03141e400911040f50002c54060f281d0360f0600c0e0100b405410040340b21a00c007504800603001c001d040002c01c0d10480c41c210307170840400c1140180c5001156806030f41a01842540603c680c0304905003152102c41c1c0351a40008680081e525420404d0341e030000112800c030002600c5425030301c40d907400ba059041c6090714010790002d0600040104002020400700d21030301d5003100400c690f00c00c100034032099001e03821800c00280d19901000c0c002d49408000c0780e0b4070811180e100307464012001ca500f425540152811038042e07444000030b2208a06e20440f640d8020301c160002c0c03501d49030107440c00851800c015043c0e80000c0e5520000003440c030425801c0301001c0800341000b5503900345441d140181d80198820900154a0801da80f4940d0005100301d9014080c101c0041103903440d0760310780110072a0041c0c41c003810706 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 132186888 1250 132185638 132185671
    0x1e09040b0606160b07080601110d030b220c0909060302090a0b061b0609120313020f0a08070311040501090905030a0e19060512010b0f04030f061401150e0108150108 72
    0x3081c490403038040240320320f130120700a0400d1032014001e45405401c3c1d40c14410740c0701c140c1e28081f5000070008400161441c001c524000d40c2000b0552218500b41c0100303041c07034695621901c406040e04503172a0f2407140d944110449554080d4001158014040258007240c40400300c1c07590f07040c5801441e250340008040f1032030001024160038050081c88014900354104608202c0d000030b09010241c203c142d001c501c60319514250b691038800401c0d24000074130550b04100c10552589901c001a8050003c55040320921341e26070400b684035000f0300f01128802c42c28000041400110350250203400c0345d11200071804c03d08010800d440000d004840590410400143e02c0c010a224090180052a281e02c4031a503600d9945a2251545016004442002010804004604031440480f803c40f40c000c0301a040c0c1d1000c2d403a0400141c00401180041080c8641c000314140b13a50018407201c0c11142d46400c08160300b0000155240c440c122001c3c00000345540159032654050000346500270540c1927001c021 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 132188138 1250 132186888 132186907
    0x70204020f0a020f0d020a0c0e0901060b180a0902090a0620060703090201020c0d0312111308030a090e0f0402060a030b04090605010f061803060c110706020a021e09040b0606 76
    0x107070400301207500140d2018201812904007441205c8440645201070102c4a446443d801c00c409090300c03950702c0040040c2e0000b440d026003075004001920000d1146599100d41c0c1844090914182c203e4600c241120100000c03141594800c449801d0700c064050006c40b864030005803821407900420454000d401040003602c0101404010f10030f01c0c01d501d00080601160000a1515040d502c00c0c40c0200c2101005501080e006484400324911000300030a44019044894080303024100401a410900c528040b0781c0b2100407015118a0201c3d94801072a81e50302c1106580711003041c0d03540081007180001040140c104000280700c12402402c000c5103801e161408201114540d5a003500c2c2c1c1680c3e6001030002d60754003400c2c1c2d0018521443c0c42070225243c200788450003040e07484014800e03030350b41104550b21800b0340c07100000c418078941030703407800782e615040651035445108c4100c1c0324030f42650301c043e05203403108100ea484604c0684802c806550356910350340c01d0b880180c030766a44000280300140c003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 132189388 1250 132188138 132188167
    0x30b0a0203040f0804030b0a0605030109031743050324041e06090e032703010902090705040e06010504150c030e04091104061a030f100506030903130b0408070b07020402 74
    0x2944560746103c0903203008c1066004589a940200c1c5c4241d051031a00c42c0841d81c40006070302059420941040c254035005c01c5000c0141320f82c2000c00066001c002002c44400b50246007020f054a11200d00000c01084201100c0611044542003032a540045d0960102071100b110100e03003100c0900300198041200c94105820101d60000040b0305480d81c03800d000c0744d800c9010760b42ea01c9001100460030f10641e2040c004072501c5c94007000400b640c2402070540140d030250460b6036206c3d00607010942c40d0400003401001e641c0a40100121b041a54000c00d069510502c01c50301218401c0d40100035440c0318050445080303028404c240c0c04c0209690584940340d840d440743c0e490440c03041c2043d521007482d040c10300050f07a03019031101c3c0050440b0110000c80000d003400b00e1768000e0280700340c0f90703142c0c2d281c0000491816443e0003c030380200010003017280d180b000000030101c0d15001b2112541040d41c1d8524400f00f0300c1a80220007441e0000c003030810041002c20007a0104030f00c010005420294200300441c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 132190638 1250 132189388 132189397
    0x90f06081e070314010c0e01020105070c080304050705060304050604051c09030213060801021614011116061811040506090402060406050a030b06310305060c0c0f070e0702070807030b0a0203040f08 86
    0x407813595440340300102c0103030410560205ea10080c0000c0c80703603141840c4041d00210f21140068248040040001c003000b00501010004d0700740149402e4a0341003078200181d07920b0041b10708a03090300c680c82480da4103020111169a89112968a0252040c2161300784481184001e8030f2200d0b1549442c0d0110b55000c0030b0000d0724456402c500c9002d03648c1f44a04200a0128054071300e600c0c942d140c01a040c0c2100381442c00c8810004070050784c00112001840e01a00512003070240b10412940340c460b400400c040c005176003142e8401120240b00c40e40391b10003084103050058500945c0088200020002e031401075003d040030181034240012040c1d1100d0100d801c80c1d1261180b05a860411500820078040e43c0b41c171101064012a10500c20909550b103040da03c6c00701400300c1c03545007401308010007021000c01604040b07402181c00e4030041c07565171540c0c103c007603004e40b08031002d0b014407a030105d040480010840100da800c10220002a04c40c00c02c018000e40c0003038020380742118003030400008550150002d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 132191888 1250 132190638 132190673
    0x150909140706111b1f0c0b0703050105040b030d1205100506040e0a05010807080304060311090d0c0603050c09010c0b1510090f0f1217090a0906090f06081e0703 70
    0x20f14281c0c607011032403e00640307410b100c2070b000c108907010038280c50b4102e0822240781640ca09402403204010140d903000c00c1d24100a04034078800c810404000e9041c0c015604070340064806000ea4040c0781c0406444010b48010a0000740002501000b10401c41d017150707800003210700980b0b90282d03d50010451076480f40c0c00104d008003600091110202203417140e1401801000043c0c0449401c111a4544a1041e440345008050b01c942d60a00038026942c03c076554500000c2205040f50300502d8400c403640c3c018070808010910303040000d904143c420f011620800320580d1148440003040d0f540460005002d0440c82191340301c0c48603107000c0e8030387e500e01400d83c254a80302d070140c6a24082c41690250511f030400740c3c9001125030100400036080e15420001c60340103000509003203c600c4140b105006009005600c401c1307131400051480d1941c0c1c007410907544404410b00020b5801d07102c641c00c0d01c410b0300c1403255662051a011107900d0080301015140b03542e000c20350340c809680340c440001c1c41e03d940c0c110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 132193138 1250 132191888 132191897
    0x40b15040e011506030b03250b0313020f010201020319090c0801020730050a030b0301090507270b0a05060705010b03032b060b04050d0201090308070c0e0a150909140706 74
    0x4078a8003c89008000001c200c0c5103000d0043c1c01541300841c1c1c0b00c80c0e4050252034079426190300c0808141c030a540e0304000d402043d5250742c0f24602404080113180303040105900440c00b540d411020341d441802100d202e0007050030300310b0307803d010414104010000c0e20410365000300415000b0500b0102800108400740c0076070300c4401d00000c0d0082e40072186d1031401000c0715050600340c04640298112040d9041d01c2c030241400206803101c4400700c1c0c05400103071402000e5000d004004219070469034140183c200140034640c0d50b030301500c034044007214000703108035a02c2111000100302900d4004000c21480348220008a155540700c004646183c00065085010101c1d041580c241c0e031209229070b030a015408481800a6440d188a1000c0391080b40545801000c2c5041001306590192907210000c65004040c01d41c0d8503814140084280b14a0040a102c0d04c1140c0108208074054080c4c5014042424030b0320b50101d1500030722000500381840c1c112811412900c490903e000300f40403c100800352034a4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 132194244 1106 132193138 132193151
    0x703120507050c0d030302041509030c1403031b010209040c2d050412080406020f070e0703050406060e070905031606020c090a110408030a0207090212040b15040e01 72
    0xd43c1d03811040c202022020140c0c554002c01c100ca840180f42d1031542c048040455030212184805041940400010703c0003c2c0c0e50b268242c18528000c0c103c9251511141c40c0700480134907040c401c50300d80d5000c1110405030401d070180300c50115051405030030008904078050740c144e0100c41c0c070010710707003410400c0c2600a0290381160040e01d05440d04081c12a01803800035020f502c14040c030001806504865040c1c01070001e20a815903803550074070010b6543e581000c5000b0640108240c030701c280c48090000d030344041c1c0c40c5810f01844040e5904184a0309200034580f51402118202a4036046440104080b5501207405100c1c0002261620b41588460022001819054520000000740000c00094041e40040205400040d640903200080d0b030740c0e00b040c4202c3c09a0070310310b402c4071440e00001d000140340082581d408207003681d032840032000703072404903084642c80d2003540039680d0350b0f03134 = true := by decide +kernel

theorem cover : BRFrame.Cov 132014388 132194244 := by
  have h0 := BRFrame.cov_init 132014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 132014388 ≤ n) (h2 : n < 132194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
