-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3779
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:39:01.267759+00:00
-- url     : https://prove2.me/submissions/c14a09c9-4ab8-4248-a973-a7d7704bd3f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 679496402 ≤ n < 679676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 679497652 1250 679496402 679496413
    0x20a0b091006060206040b0c0a050d06032d080f1c0f0929060f030309150a030b100f0e27010503010c0206130f210c02130203150906031c02 61
    0x110300181d801034902604452000c0c1419003481ea03a50660303150040c00e020351032a40890313070039012441041520541d0150b2034050011075600d00305559008159800031118009401072000c6030740c016441c0f00310403588010b400b407424107000c1008465402c012080c12626100c50a400c0542c4828015209925814200000d2010107440c2180c1c044520030003541401c0c3c07101c0c6c000089400b001c245507502c88025196001c002400500080c15481348200169011a01c1e00700f41c0d10010411010f40580c2c0c510740c800f000681c2010040110803030480b40c0e017100140c541c406200101e40718809030310302d1410191100b144140003101d24003506900d94100b6030180c075542c0040080746130900800d921103240e400548918180754214405000034104094500f4419901e940c0801c590259805460784c1d000200408011100700c000f04100980c2c201684600b90030702c4a84101c0d4524422a40900d090750480d24580c81040140300c41c00c0030060900c2d038140200840b03100c03041242040a4480c2d00258041c1c10b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 679498902 1250 679497652 679497673
    0x30306030c01080c22030209040b010f09060b030a090609060218011404030c030f030c0b0c0a0e01080f0a0f0212180601090917071110050d2f030403020a0b09 69
    0x500d001c4800807100d04000c104014802580114021240310091040032015814200d20150410000740d0f070000350450000e00401040c800040e0025041e242d0341d15140700d00325541d950035019903081d030040341e18030441000840c80104c2c555200030622071144801180500319512104100e03001000030b40310a1500040060030780d80d004480d542100d01c0c0c2c2c0380560806056845100101c0501d00000382808121901d05081c5800b48240c1c050a552041c1216001d15052000d462150130080e0404041600d9482d220b90541c09800250310507079428218003c00d554182c03640c2c0181203080300d00d241640d400c101d0803020a06a5029600c984d540e403070044054020100c0c401d150000590000c0151860081003500042c28075981010248909c61340986a041c0c0381445640c4041282c0302c02c1d402854041c00a51054001c0b001c0c0c102c1620066082150175828805128050200d804c000a8a140e0190f540754491220014542080c02031040b00c0c5d11800981c1d488421303590a4403001465801061b406 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 679500152 1250 679498902 679498909
    0x190203190e0f12040e07030905030f07061512030f0e01050708030108010c0e090f0412050909180d0509060d0f0b1005090405010f05010c02010e01111915020a02100b010309060e030306 80
    0x3655410386039000c1d403901d031411001d220030101c01b81c4290101525501e407081841010410b961400307040c00e10b203d80d180d94900d0154014800406625050152048001070b1021140d03850032485070552030791a8400c40703d0008036540034000c0d0750b040c14000103200c60750114090030043c1d030282c5459000060301a0281c40041c0c98403100c2858541f10322516020095000c0080c110a0f800070390000c444400644800340c1a51a0300460041a402502010800c4030602c1122140750740e046c0710034195009410311350012501446446129a00600100101c2c00c01e046246e00408180c1052140050800c0500b000285140d8041e14034000096000c68814028a01441028010f0842c101a00b8243d403130440060085841201d01a041c0904000d401d5810390103a48403126021a50050b51120741ca0402e072241000030604040d11200bd085010f0000c46000b88225400a06141c00911003044c05682c07040250890410060401d03072960300080014110780201d10559403840051a00c9150500a2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 679501402 1250 679500152 679500163
    0x706081311010e0127090f0c2c060307020c040525080c13170f0703150506180109090606080d0801030b070e0409140c1503130201110d02070509010806190203190e0f 72
    0x21f00b01c1d41d203002280542d058200c450310384500141d01c01010307080003007002d0f007999a6643d4542034000700d000041256442d4086000c410081044a0401940e03c0d400100c10781c49252464141852102c08082d410f018051158a584208010f0303500385000d80000c1c00c4a491036095010442c850381030b00a416001c1c006020b03a02042001030000c0841c0e61840c4c0340e02c0303c00e1074410813840c0c0c540d40e038401180c0952a08a20861000d1074080c44d00060350355081001d0041849030380590b1b40c0b9151444c0803c1c48600414860380c0401c02e960303400c2590b402c644909001031801740c0740d035041c030907040a00c00c500d0321103005002a40f0301528a454041c0d0001e5821400c049001d020f492294031250442d001039100201076076004420200c40002c0c80401d840140c42045116041001e1449000181d02002d9400151601a14400d5038010510313680c03500501d54515040da21039284400d16009960340d01020b601950b4420706120010650705101039039402150b004610104240d0800488100a14010400b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 679502652 1250 679501402 679501421
    0x70f0807050109170c100b0f0d03020c120708030301090e1006030b0a0501170a1b0f09090212061b090a0509102301051801050f0c0706081311010e012709 67
    0x207844d0f00d000c0e2900c801646414103940c1c0c60380d5159460076100401d44030200242c111002c0503010780c4200c0550304000c0d541c6e840c1101c801d4030074007072201c14542120021030040100c980410045056908042050010303100c1d1854250f0148100a45080c001c40036002c4c010046000b00c54151103070038000008416644141c110341d21400e0740400c07110f120310780003404400b0316401c0140040f014a9400450500c1c034030700c0c0d0005e0740b61448000b02003080c204036400360f0340c2280700300c0f021302444591000705616641e0407590410000f008015456409031a10300409008500034021240e1035140c03400980c070400162803031200200c1091090090380d0302c4044c001c0701002d000309003900c10b07080d4200003401841819148032015025001d841d105034002c109a07240d0004c0844100d4481c00a8203600d070b0f407110710744a0f160001c0c80003000700d01c0070b0381d04201c00c282854220b030800c50f05000600055070101c03990881141009048050580152890845110a8421802d20100040c982400a419584e00a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 679503902 1250 679502652 679502693
    0x20904090807150b100807080603030408010e0c031638030406090c060e0f060d0f020301080307030215011220041a03010516051210090c1110060f0506070f0807050109 73
    0x200702d030f170a5517008404070b540700c803041c0342c81c010030717654900030074294096580681d680d5070070141000314003100482c800310341680c1034044619001041d103070215810402d1050a100d10f40c20207480601002c1017000d422484194030300351034581000207883c007080d4421030301560181e03501d07100a81004071001c00480182000d01d020000903814600140d0040e008412461103450f0000302c20484070240d40098250240c40d110442d00c0350394404030140c032644100390840c014019139015201c4a000d42c034040e41607845c0c25a403080200265611102c000c0409080780e10354132081c1700c4007039580c1e03190b0040008100309030080400f8880d040040c1030940328090140002e94801c15a400d0903170741c0c004240c5924030b00356040310017141c55150342c070300c407400f699003084ac1c0081c10b000d21103403031030b411001039040d00174548220742da12a0350760165000c44540d03000300d000e020364540d01044203240807000b070103142d8001d51030200f003200642e58014050340048000c40b1203075110010882032200008030a02ea1a4600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 679505152 1250 679503902 679503919
    0xe06030a1e0e0d050a0c050105090304080706050c070603110c060403120c02030c190f0b040b220c0e0915130c0b1201090c110f070f080c0f04020904090807150b 70
    0x600a142c07120b0b10341c50070030100480854100c0517a0700c2034481014090b08800204900c2c00c1907007005450741e0290080c1074161081d054009203080c4200200da00c6104100d026004407400c1c4101140030740318060031580f100c2c40910004007410420311280740176600c00c0d110015a21403950407603007610030b1240502c00350b4105000b031052a180114000c1a0291080d9070a42030581c2c5182003a8100070803c0003901c1202040d0410040040c0d0217482400b0b150f080c4aa1101240711000030241c68643c038074018003a88001c0000c1290181c0540d14a07040070f00c0c0c0054402c1d541c910340c2c080c1c40c41401242c2c0d800b440c01d010004c4900740900208403902504800030306030301d400300d810800f8100740410306c5141d180560f00d100c07426960f4800e10300d083c0c2d0303c500700c401d0f2040d88482484603680ca03e0b15000e2a001c00d03026a40001d911400020400ba0702c180150652005604540c10440207402c80444690020b4540200c440014040c2c001013107070600ca8803200c0710180d8048800021a1f41001d0501c0c016145c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 679506402 1250 679505152 679505171
    0xd0306081216020909010e0a030203030403030b09070507021021090c0e1b030a090212030d05010602062a0708130612050103110d02030a0606062a08040e070e06030a1e 73
    0xa0300c00d8018180d8041e61441005e45410528500406509864052030301506402200b015804030066000301e010b9078051048205400812403840300549200010030070800900c801401d02c03a607034a40f001843c0c20700610a0340d400d21002070074480718010705c0d14191369000d0b10f01004002010b0a024100003c46448180b07044200800d802c400307080e40301b004810102c0010039901d2250015014564058a0180202a4039050550320b404c070f41c005010940c00c010000c25100d10004e900380c8141d41121070002000343d402204591910801820144540c3c00c10440c000b01b0300240090082100700001c04100c9442c0400c01091810103007010f8140c2c604240c010000b00303102d1019840340c2d1800701c4030035190081ca440001c1c03419a00120080445e810302d0300010f01d0759040511040074200c8410880e0b100c2e1f40b601c1c44440112a8201c00406c0041c0602050000c250704000c126405005410225444c0f0a243c000510a800844840c07404540312100070309102031001c0c5108108a158006001135000d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 679507652 1250 679506402 679506427
    0xb0a0503040221010c0c110312160f050a030507050613020f0411070218191b0e06040f03050c10020c0901060513090914060c0a210207050d03060812 65
    0x40640701a220700400b950000c680441c21041605103080031000300203401407000c001d403c24114140c1540c4546089092803101d043c08141c540a880b01351062070300e090000da8081880c90b86501c01611400610050400014030800807100c249000342c40d01c2e511001c05160041c5400030040c926001140700301608801a10340e0b444848100b00b0440307000c01c01c58201c065980c4580694bc1c03001e50300a90750800b07251400401050580180b070f50000e04007403910204003820558142001084060008051161103103200751440c22080c880100702d545041c0e034440189010b41030540080e6410b0300604940c4800d840d0002c110040007010b40040d000e22044800050010710301403007454140040000c1c0c40044200b094400390245c004441c00b00302d030b200107080011080d9203c860700c00161040c4004198454214404d86052011540e5050b105044564542c81032200c109402050543c003880a1b0300005c405010b8000810029600003a18516040456241003941666041000c0042000c2e160000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 679508902 1250 679507652 679507657
    0x9051c121109091005010e0f0a03080309190804050a0e0606030f06011b0b04060c180909030c230c040c020d031e050c0d1b08130f060507110105010b0a05 67
    0x84000c000040940807215800e4981c07003200c114942c080c42d183c0c100800079a410b0f010710190b4401f0799550845c00d22090511004014a000c0c460b48040400340030400564010004e42d80054004243c51142c480403460744003851440904a800384400b0409000d542440b2240f60020b008103d048007103424217101041041c0310160400104c1d47e5100c0c001001c0d0790155126051903840015041c0144019041001e003004042e58111851410a00d048040c540f140c128000c0c6005020200d90b455464006c8140c010a1828000c03828052a600c0242c081582c0031800c0201071101003090f1a1080d2a02c0345904103040c41d801a440f441c505440c1c204030710341c006a2351400980754180043c03098001175409140c1c29100b00301c0e68946080a003000840780e0284058600e140b100d80e0203000030329440c08200c1d41100440d1019000030580c200140b0409002a02d11041c030303014120410b0060281e0b181e503170a50b18100d50b1030010a055008020f00d50109214040c01460386484450031710311400c0b001402031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 679510152 1250 679508902 679508927
    0x402060a0516050303012603040f05010507030306030c120201020607082202060904090819030c0e10051e030130083402010e010c0323070501060909051c 67
    0x22401041061060850558581d0503540010440c0d890b1b40e034070041c04600b4164824511101040162020f9007800000282d40684440b00d00710710b22107040600440f4550000c2500354101510350700008041440c400000c1c000d4000d882003140c50317070303083d00000e0f18024000d021002089502c908100503008152503000c004442c5c65400d07903841e402c0f400091041e01404007201e034018a001303504c804000307180c070045c00d84044100340040f034054141e4040e422180410402c0021034414400c9600610707003e00d110080c504035040c01400c0c14282c895540c098a0071070b0700c01900000000040c0700c04d5882942c03404c0707648a004a4140d40c1d412524034003050180c0034200403c594400b04c0c400c800f00b200f6820042411600a4075038000750010b0956103120740c0700107020790118580ca100074081e541f00d05081c1c0307082c40c3c05461f040d28010550400c401e0032440c0c4c0c41c0c04881c0c0c020030700143e400140207001c3c480060602c01c1011685d50210f00f032050901e15141d800c030449100e4461100c02c1d594101c8440d4004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 679511402 1250 679510152 679510157
    0x906010903080912030d020909090706080103080319020d060e0a022a0a0b0a0c0e04050c1804021308010518210c0a120f080f090a0212011506050414090402060a 70
    0x56007180341c041100404071000c0d26080d8003010888800d4014651f02500c101b0008454007a5180c031030400301d50729081c00b0b0283c40c0c001405c0d40c0050022810280c01560881c096014812150058a0024080380c210300c00a1030709544034481084610004442c4c240c000c11030390421890040d40480c0c1102034150342d003110a41408013a4480040b8205101081d42c50303801c10550066884d01003805001000c61450000c0402c5600702c07403078002e0030b19105151007500d007281000c0c1362450500d80800c0701c1c000b140059600c01e400b00300e01e1100c0e8002d80907040080098000210341070030440d10440315801011000303491980440101d41e02c210740503094480e0400e0141106944072480e000c0c0c0b60600011040180c0201800045048000d0703102d200000701050782d40da42142c0e03441c1c0551034010b45000740c480e01240c0d805003c1c0720b03025161812405409080d203000014a450081030004081e04440d8014400b08001040030071410344940020400000c0132a4411081c0c40c09500007280c0b0b020380d155030403c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 679512652 1250 679511402 679511407
    0xc09050609120c120303010e010902070f242306062b0605031b10081b09030106150309140f06070806060c1c0207140a0b070c170106090b090601090308 66
    0x5040c8001d00000b000f101010b0f00b42c42d840ca40d85104540e907a4428880e800128001400010b2100e0140c0300303950526921401041c01c4100035200c004900360120211182c5107002c86480d1038004003803240340102407a0005049100919412400c141403000340094001c200410209880c04200020a090070041c00022410038410a0340e40707000381300d603401040d054400e0200034880d1603030607000c0c4400d07a003044400c04c403c0c50341d03a0821281d224080e1030243c903000e00300c0360011100b40400041c005514002c0d00000382d15540d88048003141c2c603070003228800300b60b032114007070309100d0042d242415003401400207101e101d40b40c40c4442c0e41c0d543c00030003003410000b03a00c0c040703051a07698030101d80b1580404001c9504108100c0c1001080c0020260588050300c16a040000c19050a005031001120002c002040f507505c0d1421030380079035000c150100c0d80e40249040100d0480058a10411740c400ba00000103542420041c50004407001908194400da841c82c041150983e0301024082c1900c0c0c0c02400301e034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 679513902 1250 679512652 679512679
    0x40f0303020c0a080f0d1d0d03020a02100f060e0106020a050c011803141f0b031506040e0703030c1b0b030a09050c0402040b031f060203070807030e060d050a0c09050609 74
    0x50a104090f000109035000006043c5044051207000d03044403441080c0400c80e980c020504201c040c0c11200c21404d007078014180b807046003170103039010b8440801b443c010b484054407210f0505007141d40907407810100581c1c0707601c188158111b00641a025101c540001c01e00340065440e11b07179440360a408114100b00c140401c1c41c1100c0005104500110b603c0103036800f07080d40920a0707035100d00202040c05401070050980c44200c4059003d024440780d00034026014031003045504a81c00000100a503400a0321142c40401c0c0340c0e0100b2540000314000c0c0d8400001084a14090004c00c1e00b45a80c0007290021450510000c2c49000481c1d03017240b409400080c00c98501e151503410f103401d5130803040d4440c0c070110f80000c4202e1940015445145009862a0b00b8801c1084002c00c8c2c080c28011040140d10500801c030000310014028054140a800d004002101210002d11550322017540108201e458800b440a04042c40c050394203d02e0f042d04041e82c01c02e00740340110707449006415945100d6140c6c0c0d203118 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 679515152 1250 679513902 679513927
    0x18150b06040e04080a020610150c0f0f1a060402091021021b071508180708011a1314070c060b0405041109151f110a1103070509040f030302 61
    0x120300520104605062500e0300d81404e20071038000500c01c4c130150144100140e0300642090040080c3c800f05522080012080003045411002518084612303035141c444503000700319414003a03d6018450301c0c0b2101c3d8002494081d603003000014202d03500a074018450500c041e0740700d010380c4040800034a00110b03441030303d4171a070910352008800081220b00c000b40701a9058031810708255510400800c642d03c06948072000e0110880820100001411600100725a0450040e58885d10b40d004000c6035121a01c420400e030840c0d00e4102e001402444a100c0d0340000e0034000c10201000c20b5a200030001401c0700c9841621000c0010410003c21035002d41780c104001003913115019001c00913004010615041c508000d0300300c2c2961000b44100c40c000c0000d0105003240d01c0e43d1524000103410030030300742640b900c2509080c01980c1e064051020f000421030040b0030030443c59903035034007422401001d070304207001341401d0484a40216014090803000c0001050081102e40170700b84e4145401a500d8162181302d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 679516402 1250 679515152 679515157
    0xe0f0a0e0a06060e0709050d05030301120305040f0e10050303090d060b0d0b0415060e0108030406031107020301020a03150b0f0f0a030612050d02060c03090c04050604060504020f070618150b06 84
    0x5110740e140c1007000c0b030703040d0020007005d204114503216400c901b5161410000d10fa0610800144507503c00c0005020b5030340060280c0450a12a080c120b0415071103020360030030840c068208800d103040780b0081004400d554100b50f402008107501462414010001240c00780b007a880000d0199070701d074034904026460f81c005403070300c15070400c08040342418207141c5000c800040c0e000c2d90a586080400100c0c840b01100e00440c100c4d180d61000311700e0b2502d00b92090f00a0a84600c0441c0003210074404036000d61030038002024100100d0f640099603451400e040746d1031044030b401c103030480d03042030149102c1710041e01f044030b49404046060303503142c2d080500c04502074500c50f00044003140407925007030b04002e000101c000990b8429002c4d0b60199492a03451501030004a0355034940380e02910403004103007481e621140e0412006040403a103182c41e50046800d0b0b9105014014004c580080d07100c061000500c5080600c0c140300d803e80c01d00190640f510110800c01c00c50380c1d84203503510b10510340c455848204 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 679517652 1250 679516402 679516423
    0x10b040903121e0606020703050c0301060602061302060418021c05010602030a080603071d160e10050d060506030c130506040e01030803070e030105040309080d021203010611070506120702070e0f0a0e 87
    0xe024a40e00c0e1741c0c000b9140c4010344411034062081c0380d0040e14520341030107801c090b24055801841903035200710020071518510741c010b98101c0401c00c0003081550071008900c1c8000b49480f070159035107040310ba000c60050703440032240f45010b14120061014940c0071080340c150080a150014481d141d10001a042a1681d440701d4a41d505219500160303022107164507218854080220390080d0700b200e803e03103025284072070351548070a0b04001c20302a180940301400840402c0f034000181c440d117a070049036542c0d00036210f180c4201004242d81c14580c04161242010300010380300355060501d03213094440c20700d406000041c682a000700005c3c15062240070b461100020040c000e0007913041c81d003009840c1c00882d0050460501400c960100581c1c00014070170740c0700d0084200d842c03071a032900030122824100481e8000e51401501000185a6202005028800c104a03007004c04c40c1002c1c80b0281c64808180d0000c02c1b81c2706600c00b00903071198001c06240d4402c000241c0400d4807000c0301c0c0d0480c02c2003030841 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 679518902 1250 679517652 679517711
    0x1e020313060c0201140a05070605181516020f0606010c0f080708070212030a200c120715020a03122c060105041a0a03060e0a14030a02010b04090312 65
    0x80300000c8055008800d11045030003a01c40009614404c0f0010445103d042c04802c0410410803ca800003031596200751b92002d0141001c0c0700341250410f401e81020b030049100c03940c49102400b40710900f441d00481401c61882400182030360a90f44041c15240c5070010b20040c18810305138192024056800f43c1c56030650340c0640f40759600d880c9482c1c403400c181c003c0601a4000d407000f503c09a846000001200c80998050b21410a0071144408a203c039059a2184030b5840c00b8820190b00d0b1511244041c0322440d1080021b00041401c00d0a400c124020b481040340071903000d400e40c000401e8001c01030500d40c50300702a001c02c0b4140e034000320900e040c0d548841010008610580c00e50f40140124910b81a21001c0b40e05100344070808075214402080920142d502a6204c034082001501c030303600203034400f01e500d030958600040e59201c1445010940180d00c83c035400026840d80c00c02d03428841d42804180c02c441c104014440383c0c03001000f00005000094040760f650301700503400ca241d81d00c86120743c45410f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 679520152 1250 679518902 679518937
    0x41811240c0706020c04020403110d02040f290307030b0a020a05040b0a0c05070e07051b0705030d081e04210e060d0c1706060a0f030209090112050f010c1e0203 70
    0x682003180c2d5035446204950041c015003c1006081c903007402100e0407250004082c1900420780000c002d603030350600740101e0f402a81c07110b41d028034100707900070a1910000301d0700030f02d80060a05d0445e14004201c40610748250003c3c08180006500d00404607008984e006006071101040b8409817441e11030340d00314070b4491174046000300b030640c0e000300f50040701c43c4214103880c01d25941e41c00c0d4019240040c0d400e080818014006c196803411804008100c40c40c8103c129507820b1369450102c0c2c100102640072b0030004402c40c00700080a6140b04200020030004e01c0346070f54620b0701d41c030b0340b042819080b003500d044414982c8405c0c0d000f0384100941c91030888003c040b559034818000002e00180b8078041944080340c08807002e6103e00d8241c036241d510403c40070748000d00d8141424400c9078051000520b101c00e042e030034404d4940030b4450030141d0f8040d10001071070346100f082c18140386140c2416524501120382c10091600800f035403120106d122541c01344c0411406d1004200c0c181e0450240304d0340d4a03d0480c04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 679521402 1250 679520152 679520167
    0x6090b0c0705010e0f03190909090f1202070e0c03071107180b0109030503090603040c030c08010c03060b191b060203090c010801060c030801030813030602160204181124 74
    0x180010650640b04800070072013015000c18181e180c200c01d10701c0491581040c0140400d02c04904022418440d0515184290f66120962141100c40030301b42502c4c440780784a0188200800c895201ca00040c95000619040340ba00e00c0c560f068010081401c2ca49041c0400030503034041c044c02800c10300441c080c0659003926250307407441c1e040c4441e0003c0c1e41d000c9410140007800c80e5000c2d201c0e01042c0c0c1d4000011f140340401c00720a014907540050402c4a072031000380000000f04004041c0040070f44034400002c0380c6600c448000800395900c1e600301c08030440040000007c0d150600c40061b04c00b1f030381804d0840b400800a840d4060503e90044080d02d5207000004002d4117100100f6041c3c15440b0988411000d41d8072000b00f290807408a100050100f8141e0380180041140c40b00038080e000c4400a0071071703a0541703a56070a000e9801c5a20741c51201d0740c0c03a8100c001180303098010759100503541070120400304010345580701c0c0003500f800201d004001c20b940a031203074a100100b001c0d11001d1141041d55680c80e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 679522652 1250 679521402 679521421
    0xa15030506030c010311040302090912180a091e0506031207030810060e01080c0309010231090203100311150a0c05150103030806040513060f1a03010c0206011206090b 73
    0x1044680c80d11a000e0b40f00e59050544c0a0b01ca1120359141101c480c9040c41e05560038000c00c5400a0001c510b10b1048058900c40010750500414170036800d041541002451b01c03061084071441c54000c0c03009c403410b140c1e002184051030380c294241e2200200c4041501d442d000082400c0126034001e6600c1e01d28006010024590003540040c016000580f42128050342c49008645a903060600382d8001289100840e0780a28108091038015021100052401c03020300b136543c60402420741ca60031a0415410700c01d10518035400d80c01c00a0040e400c00394554070b00400040d032030716414040141000300e00211941d40e0341300c54500d9806a03c0109400e0340d20405900040c01d8414030000484007840380710546040b120141783d83c0e078102c0394180c55200c9075803960300410002d000020030002160712081001b001143e158002c420000040e402c0000d281ca000c141048400d0041000407402603041207140d2640c541d0001d081380c110355020f0030034090b444141c41c120020f00000c070790144c4444e0a681c1803080c1c07200b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 679523902 1250 679522652 679522661
    0x20a0e1306080f01271a07110c150a120f060311090903070309060c1a010b0d060f030b01060311120f15041505010503060a03140a0c0f230a1503 63
    0x202c15404480e80e40c81102076403404c0e00c00c1141e07103100c03e100d0001020401911400d101125a10885000c020999030450203038004a046a25a00042c2235140810035504288041181e60702e054920345407060544101182a00c2046102c00421411042c82e004102c041c5c0c0c44030701d0303083c2c040206000e125501c4c00c010010b0011600141d100700c0300c5a000c038441040c00000c9420301e9915845645149191220035180740b040c0385001e03642c0340c490807890040c69801034140c078044d20020346c0311a101c0c1510851581255081c1d0003941d401d904419040c00410f500303543c8141126858a0702040c0342c1d03003413440110036029491600400480050a00c0b00c0012500c2413540b01c1c0c13030490010034202041100f08415690704a08504100800a03400d200075441500159807100c0058500b150986e529543d09800060040741c0c0007094102064000403c00940c0d603003001465880d5180749514181544802441400150242c28140c281c0610740c44c0e80322480450000c18402c5007481d440064654040d0203031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 679525152 1250 679523902 679523909
    0xf1f0f05040f120501050903041d10120507060f0203120c03070203040f08060636070e060c01060f0e0403020d030207030306030b0106051c150b0903071a130b09010e04020a0e1306 78
    0x1e501b44000205211000001e031802c40e644400201c11032070384081e9149078010050b046d4000c40c45e50101c04a440030059400200180c40b803070080c141e41d890501c0041000c1144c400e0344045410400071044902182004242c0007200105055583d481d8404182c1c6944225408a00f1200110100054011022442c1807003004183e03000b03400340b8110000b0030170804085080c107451081a8600307543d90300c1780c03e40c0b2592040740c6042ca0b0b07058450420010700150071566280f2000d80d1500800e0040343ca2000c038140c01081d41c15211070f42c1d07043c1594081c0d12029046207040405a01240040505109800c03e200840e00912395074119610703290007e01c0b9a10408a00d04004812130840b2a002d401c0c0c8541020741d0100310441214600341071101c00c0301e91180161650610580c0004140701d080a0180580c1080d0000c0c4903540d403082e41503d050f049010340c40305035502c02c02d020b14a22a41c004d80c040b81d82c3c50089900617540d96121000b500c07003144c201902a04100020000340803101c241e40018250f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 679526402 1250 679525152 679525163
    0x1b030f06030c0308120f060a2d1401120b010203041715010b0d18080d0f0b13050906091c050c011506030e071a070b040507080f0c0f1f0f05040f12 64
    0x7150b4505601ba0a032250590301503800c01d900050030441c4a02c072441d1310a0404101c84480414101d02e03111040c204a142c000d4028040c584e401c08a4640e0492842940701303028080521008542e000041c0d264010b0f40b0a8180482004113110000c1105008400e4614002ca001d034905584034462032a40750003608028100d5490003070710002c100c4200900d900d000781c0c4046010301d8801e40c0c00c0c3c0a8090100d0800031108261a803440f59002d83d200340750503006141074200090f9030720b8040d80c0d03075186c000c000d0411007090308407200d5810380d0941c14010720514822400e080d613651480c84c1e540d030300420644d11004049001050b000c5804c55150300a544400206804c8892154540e43d28100e000070107088000c1e134550030401140020040454903074000d020704181d07128543c2c0c0364042ca040100304541022a500203610601251400003d44a0001070130346004c85004407c0c84000c0c01c201791002c2c15014840101010000184076001715006031661940440010341c0e0b611444841c00d1804004070755 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 679527652 1250 679526402 679526437
    0x10b1203030907030809060d02071518050c150903030a0c05070603060e180c03030c030715090506190b1203071a1015031b0e0307050102011b030f06030c0308 69
    0x424120000c00d407070082081001038003c20345980c0d5290301661121031182d0700301009003c280c7c0c0da481280f010700039950042c0c903807030022100001c800089990a01001800c040010450401710b07070002056404c814065071a18405040d200c42618207004800009901d8400000ca510b00c59500151500c0d04500c41d004540076251111f078141c0079030b411800b4424801d04280000f524110b11401c8502041d40f0120a42d4003061000b00407074159840850074a040c1da200103130913410400000c040d41c8800c1268842000040043d985413a1615005450140c0d805800c1d920791005c00c00b01d911440c0d101c840285500300b450b40301a1295200d800000041c0c0d1540055009050029410315000e4420320a0012007201642041d82c080383c51031200452100300744c1d0f80d05c0040d14490600450f0f0360001c501e03451702c1d20111414010940381012641110b411641400714090481c1e2803400b500282c0d41e464103020a03404003d03100440248101d6002521002c0c11070400810710040b10010aa0384e00002c42245 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 679528902 1250 679527652 679527679
    0x1701060806070215100f060f0f02031207050d060509090d021b10080a06090513110d02011440151205190c110f060c0711130905010b 58
    0x192528402c540220168011107402500702580544c0140e00c45d207014031032a04c49880b8001c004171444160000340124816240c0c11121035041008500514180d1009500d044204807400ba04614041d01020500c0760118040d01400a650440e20141034050401c59030b528011a003c0d0751003110703100000140c0214450360a280319058a11012200c014000704008030704000101c5502100519030480f0940e41c22000c03621803031f18012140198080318401b00220014280380301d191941202ca144615510549000144d800106a1145515103a0410b441e0317400c2010210404000b207000400e5140701202c48100c0355a1003641c00b01250510490096154036041000d80114040c20304501045104241d04050841e40d003103650700105030074018949140700000301c42030b00c001c0752014010482105606150340400c001c94040d1202080041146090405507261184504640070300a88852898450340d925189610f0b0301da075414480401541c0347d5400c4c8140204004402540304110421002e03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 679530152 1250 679528902 679528919
    0x12010e1c05041a0c25030b010503030c0709020a0507021207210f020d0201031803080a110f040b1b100509010606080402031f110c01090611030c041202010203040906170106 75
    0x1501995800103840d400114a8040c5410035000444ca00302584500030551005c4440580c0c040e5481c11181c100514103402d40c6040c01d884507058005900980c0140042070a00000203110000c480402c5c1006943e0f40034544126488d00c191040a500020a030340360520b005400a0101c00b00d0b107a482c0da03c2840d41d11b0344141d5084103000c04015085214640300c5001604d01215a501110b00c14100003552115168810b218108400829070108080f13804000110300c6a02a80b4030001118080c0780c034004035281d91400d9405103010341401648042202c0342d0007001d8100040b440c1c0d0300c0004581881141381800c01c0586800c40d0100321550030144005009409015010301a0b03600801030003110001101400700c0407100b00400040c2d6488503490001c1704034250042007101d01d640004a4181342c142010426a20640345844c00301d0800c100f00040d815221040c3c40030b5458030094200029041e000403490350240d43c011a441d607107000800a0703a000210491032041c0c480d0760080c0b004c15510843d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 679531402 1250 679530152 679530157
    0x708030f220b060d0204050103060f0f0c0c080d0e03040806010906140a12050a12121404020906131512021f090902070204060b0313141f0b12010e1c05 66
    0x140c41c24121440800005811100650343c015405002041510580c0d00010141d61080c3c1c81030f1035007669281410700b02c036068082c0b1100c5100e001c0081c801c0350740e01e42008000c6119520064210300300407520020124090f0090100208101b040340c3d00c3e10b03150442d00742c07112002e2113a00003203442c0c14030000c1e00156400004140b42402005000c12600d0440503980e0302c500341c01c086032140252050030b03001a0002d12a841e02c0c1035a82e8030001c41c007200c000300c00c04940e01c1056098428448908001c01a503560302c045500110544500d68840f52515628010f0b08520941c1030703039019400c0c40860041041c032440c84045000700c0754810101500e112030758403a07503080c5075500002c401e010184070109039070f0001e0800c180302400000e080c5581e02c0d09a000c80e001903c1000b400c501c0000c8001c01d0080e58a80001d00640d407c2c00703440010201e100c0c81c05040a240b00c0c1b042099100c03000d50301295188201c0c44019170500d0020704c5210451140542c039210300b01c20080c8424003080c2c041d4081880b030030a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 679532652 1250 679531402 679531441
    0x20d0b0709270906180b100f03050c040b010c051c120216140703020607061b171f031e120e01140702060927010902070b0a1e020708030f 60
    0x840d0050b207000c02c5100405054000c0068644a496207444500301c1c0540040c117280794041c1c4070102041c1400300c4900c0d44110b550340640d0f40d0204100b01800400c0001c1022004002c00b00c1300003039160b11080c0166041c502684002c0c005005600c180c916248000030504588100769840102540c50890740f04124000c1c608c00004140469103810b000070102020a012400c581044414941e0b403640091420b620141080700c02c10740794001c03a01c50303081e292004e2015125a00300864482440b2502a00b10310004010510790400c40011640b200c483d401a200555003004200346c11900c02c0464510400080204488103000304c900348110714884c118000d5800c0d8140d650301c1c0e5100c1a0b403440000c9410880c8242e07031041040202c02a07541c1d8003070300301c2600c00c0802903010640004003011380c1078600503440141c031140108202000902020b016035404840d1010024000d000308030b0f540c5d0316408140300188001c4c070004c0c454040c0000600514030030200104244004d56900100001a20542c076 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 679533902 1250 679532652 679532699
    0x20a020c06070b0612101a03012f09060405040603061a1212030c12011814100302060307211a030705030d050c03130b03011d040c1202010507020d0b0709 67
    0x300b80c4d01d19000b1500f99240c00e079a803c0329801c0940b159110115071000d4220042a140380408102c141000c0c068003200761075140100d061690240203554070603c02400402841d440080e10b500956150400e680c06064080c004009140c1c503443c000005090411032140d140303480c40c0d0150154a0a021803c0714510500090201c100340501d912481c0d03040a010204041e0041c880800083d41c1207503a00d00a0452100060b000720312a60f4140807101d4095020104030407001c1000407859100380404100e942c19a2b01d0307652607032452011151584a4150392190000a40440c4050000c0c1d0300030000c1c00a0105d41c143d0b80348191010075a981000c3d11440d40c054103d4034080c0c9989006802600d4000c03c0d12060700d103040a0440088002e0560350800181840084018030a030028480c034601d505500461015841c201510752210369a224410507040d24480500c180440e4417400a807506a54054800e03075038a0140d01e4001c010300d1040b03401e440011100540098a1540c0400388001000c100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 679535152 1250 679533902 679533923
    0x6050318060a020d0f0b100c020102010b030f060124051801020129040f021806220e04030f080402030c041503020a0314010507050711010c11031c0e0f0a0b130b030a020a020c0607 78
    0x10307c0181d0306030f20505400c3c1d056542c0c610110080d914148166542001400050401f41d81840203d08071300601c0306044c421040000e40b254080e507000f008449034803c42001d198a1303002d803800100c2c050509285111801c0c45101d181080891558078080781280040b2070030f0180305030801c0444224098490b02401610305009403401d00e00b0090010940b5a0713514041054840e015a03075802c0851070741e03020085203800c0004100030b2540c1b0022200298a551a120b455420250002917a0310114200c0521076540d5028000345181410580304c019603010703100a8001d40e45e404c22209541c2c8200c0740e4810b550911000403525807141c411664810392140d55807403000c650200454004007405004c486141d0034200300341c0265000c0020300da00c5010b90710f040440115070031004102003501040c0170f01550b1060640c18143e0b40e0f0b55202402d403100c0b0b8202035200c002e4802980c105041a610450030707800b000040c031204210382d40080c84139140c140c08a81c00d2905150501c500b6108448010300350388042c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 679536402 1250 679535152 679535179
    0x16050c06070b1b1306050306030106141f0e030a030210050703020a14030411150a0311041802160c06050310050a030b04032706020f06010e0f0106050318060a020d0f0b 73
    0x103c0070103040d50700c0030000e41c2031500214004081c0380031a005103000c2000441040403900d800d0003113601400b541d540304210004003002040b5aa44913107005031103d143d10040706a164030035680c554000b40c000342200d032000d0040c01c0207501c80c80200c180110141c1004001a4014000c5c0215509401d040c0d440ca0340139505901403810302c0d04007400858031104400c08200b42590344900540c8241a920f085598030048060064120754504038a813200001c2808104644801d15041409207007921001580c1c94411400f1800360f80c000300802808180c3c2c80d40046a03040e4001701441c0b00c0c024014a01d032446844804010420110f0700c03005260410007400140001c4c4030703840303042c1c9119000a0300749100c0000d60160b41980107c1d000807005034020034450302c803200d042040703500601c081c04108400341460218a08140c0c0c05000c2c3c032050240000204039040002500740c50090310500a4604c58244a00564060f60041001d91011410189000c945202d948508114464001c140c0c0f80c50085 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 679537652 1250 679536402 679536421
    0x2070f0611041701110a0f121d0c1e3f0f1f0b18190c03140109050403051308010c08011e090b040b040246210216050c06070b 55
    0x200c4c1407c900400c50420544804401680144c0840300702d42c02c0703410003801c29103e800703242c4580c02c01c0e5184a6000101400e0462500d60301050b81d0341c0040e40d40090508510400740b00001544e003040e001c42941c0700d41c1030826203400300304000e10078400081d207414050b0711102c0d5540302920075902e070b014929201c65140824659000c40034801c00500901811a00810b03002c1c0d2071001207401100740c031407203070100149a07160b200e2055540d54606040102000c41c40c41042e40038014055044026a1000402e06160082d425104402c035200c500c041c2541d180d040701400b8094100c100e00c0840c00358800403c40d00c0050050313103298042201c0d131440f1149001da660001d00f240c01a0745820070b03550114084603803030303030b0005001c5c4400c3c81e8042e411501c106059004040303d03038400742c1420040306000c104500c0d4800d104101c1040c0d14131306910f107181c010490354140c0c42c0c43c00c10101140d20026030a28000754400044608502543c2542c1140f440042840340354030070220024036544940001035800c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 679538902 1250 679537652 679537667
    0x105010f120903110609150604090b0a0f0605030d02070806160215150301022b15030f0618030c110111030a1404050a080601090515100302070f0611041701110a 70
    0x3e02038503110800c004003001d0103040600030340b07400c115a0071505040c800e040f5000350090704244183c0b020002e0382c0550304d07016200c0c003016016942445d181d82091003003024542100c0040c007002829110180254100a50380341c3d10351007240224003e440c005914244075030001801180b03150080d104480e14540715034156400104150700c0c000c1040010f120035142480a49256410f0501070307000036540b040b04a6155543d1003050b49600e0802980902c0c102821300355900326a40300e0b580004031882407811801501d41d0300210070303120141c079240d80d09140c0e00c55030051004c1e010b1422030325200e000310700440f05103910b0300d4940d17401d40c001c201402102c1c5c03040b9001d84400300080305d03480c1420388420008140f1003141e44001070681c4588018012169184100d541090b00d915001640e10524030201e01525004068807050560101e51202170018407500303a1400c81c0c0c0404100002d4a44c4801540590401e018607480c1104944c0960080081440703a680c00b0314864145070300740984407600300c4100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 679540152 1250 679538902 679538921
    0x3040e01241418011116170a0c0b0307050d02070606051816110313171c0c060b060c0607050c0127080702310c0203130e2a0a080105010f12 61
    0xf0142030b00214001d061102142c04562003034091001850300051a180c03001f0520000450380201c220362001941d1404c00004aa0340c21406a8030b1fa52540410781d003901660a022101a000247c2001040781c6584620203176541150b4560311450039540e1058201c008652619000d101b0201000c0158019506000e5a112020889190016000d07081d4410045548a00d81d0b09041c86010021050284071400170206884114180741e500d4a02c0140744024100024040c20b03600c00b0b415006031a003104176500c20181c082120164104010010807940c004264040c05d9441d100c0b600484c46500c10110000800d24012094408050340355070703c03113a000030300403a0300805010703a81082c0048420320038071780c0c180c4912048114070b9507a440b109558590102000f1500100300c4070ba001d41e604020703801562100030921450703944003003e40d547c0c415043d129000d400c090441070841c00900134020001c08c41d0641d25001c250f66600010343d5003030421b21034030000c03034001607800e1000390540e803011409 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 679541402 1250 679540152 679540157
    0x1d2a0d0605030a0503070204060503030703021b04060b12070e0406030c03110d0f0c06092403150504020c07090605030102030c030f072006100b0f07110303040e0124141801 75
    0x101e50341c400083c03900f0482d020480c0c440d040401c000082d0b203454030410000b800154042c5161280c1598025154000c80c0e0809a000403070340c01c0c81c0c60304c0d2076651140c0040c01800c0c11040d502c410459601d603400908540d104001b030313842007070712059041501481c41102d501510f101c084500350703034030f00c04081c9800c0b18103a080340100c15a0340105280d0301f00108401c0c05400c250395017506055008000c0c0e40150010600d103100c4425000c1407200341c40300700409016601c1c0006044c640542500c207040b01c00e40c402684039002140101f0182004509401154901d400030010180d0324800e00d03090380011207020032440010700015030a011601d840c47d030300507864a040400d0350000030201da05019112604403e036031207902001010100307940420003910102d04030b203088c8a07591400100b180300c1d8002c000e00703041003014500c04644042062324003500303c4280261040d03031031b48144803031a516052207a03c40d080140d0440040d9001d00c110b000e1240500c0c0b119842c1a140b030310812410305a80018604 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 679542652 1250 679541402 679541411
    0x1050d0f0f0212040b0603120403020f0333150102070e04061b09150903021507050a140c0102150103050c0918010e0610051f080c131d2a0d 61
    0x5020790144002e002050083c2001e0583d0308060070300c00ca0514005050900907030000100401d803146010071f80301200e504880701c191054003400403c0c24900b100c02c0a07400001904001503040c00400d24042000d9070342c0d0480d071210713036503040d08500080801168901681002000303020300349910300e050b68402c2c021400400c1051000060130360700d0b40d480306c080c0d0010703038a50310502241898603d1402d190701c29190601507a401c64000451169440030b440039a1000002e400d41000380c02c3c044c1403400c0da044805a05406042c21480341c45909002040703006000b80c10002210004074503085050329000b03402001c880d00b44805000c0c031084054034031181c2480390702894160003801d001d031160b0031105034040e01341814964074007004086560000351180391a46103910040d4090340d000302d012011441c0080c61903d031003466103603d00c9540c96a01c940401c00710049500b80046200481e448041c0d01c2c207500a0382d5846503240c520340b1440040c480414080d444548050410000d0320b9902001c200014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 679543902 1250 679542652 679542671
    0xc070804060806040501051210051f030609031407110d0204020c0a0f061803050327070303090312031b140408100f050702121204050109020d030302120c0901050d0f 72
    0x14a2034110364403030000541d510040110750306190040c5030043c801a20341d4081803111240345d544a650b454800c015035a40e800000704258106c0c614070301c0c0c009044940c03041c0161282080c90240c118113506a000c2100802b10780c1482040400312001150001c036002601104c0c5420400050200881a64840c2c1c092046082c181028001030080070301c83d0f540502284198981041a1000c0c1d44000d6044070308207402d41e000c80d4016007245d6012040d241c40800440240403004801100c00b03098080d14400c40001004058100d40c1c401c0549000302c451500d80040441c0440a48005200c2c06e1801046170300d03102407542c000c0d001c100e0980490b00f81542080d84444a5514001e5070300c01c52a0a10b8650210200003034940c80b07074540040c202d1000e800151078201800c605885014485000c1244010018060040a500c9409400c0c0e00600700d0400003c9401e00030080e401c2408141c50001c01c9002150382100c00e142200e00d001d0301a16110b05112072001454014582c5d48448090f1948840406 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 679545152 1250 679543902 679543913
    0xc0a1a0405040c0e01081b09190f030f03030e0c0d1101020709020a03060f08030408060f090705030d05070515090601090c121121010b0f0f090315011706060907080c07 73
    0x1011112079079035260700c40c540400c001800d414028200e031622000c2c0058100e120803441f01125525482034503807084c09522480480a41c4d0709035800a5443e8040c443c01000700901031b001100418081d59060000000c0107140319100e6025940580e445120181c111002848540703000c440380384140180c40d110359650820a0682c0d0180c6007020000b50780314004c0c009182c1e600501c07006060084001c0d42402e06014616a03219000303000c002044004400003550300208001ca0800341101905440803100c0164015005400c29001207c0e01d004103d2842c0c040000d014040744950301c072000404031640303000030072001460305c0b00d001e1081240c41003d00090b0380840c01240020001c501401d543c681041003955646015010f440070300c41544001000b4a004007030a0f82c440c0b5464249280d0384614050f5407201510404c02c03074542600400d02d02c00c00844d21548000d040b141c0388041c4140240b00b000a0b15140d107811641168055a108042001c15209680340c079408468000302c80d00d41000798962 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 679546402 1250 679545152 679545161
    0x30c04150501020f030f032206060609052b12052b2d0b0d02041505040c0207120f051e0f0c01080106020316062d0c020c0a1a040504 58
    0x8100030002003030320812107560304100d42c180340760b42000510305020b00602e0305001484040c14520403c080510f8105043c001405508440b907800380040018075a20400030300000e11a106191080341c00e01d50100003e40919605015200504502c031024811a03644031400c200400c0a281000820f21104011100483c441e2000d90020214004102d01c01d641c0d00040c0c9590066000b8542c240b01e4240d001c4020455007000c0d000a14070005c20100c0700440130500450009101a511038184051000190400c5000c5803e1395016202800781103a45002aa40c4181d284100d07605001440b040c903010555050004603d00c0c454401d55100c05c0600015101065281440f0103d5800121090140b00d20400c1034500b00142801c004450358501140a900d0b800303400380d290000250030804008211059100d0800b802c081546481c2401920704c0c05a410380c0c0300c0e0000700000340b6103480150f0050000440e041c44040040801d243c0f00d04150030450304110756400c03401c0c5030b0400d12012907655564000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 679547652 1250 679546402 679546421
    0xf0c12090318060806030c03010b150a030f180210020c0d032102030f070318030e01050d0b0a0801141b04050d05010b03011805010c0903080406050c0c0d05060403021e07060c02030c04 80
    0x8400328141172a0080504014281221510076858284464a03980710021000908421520055210721032030790150050824220340341c0c08c1e14030b869805084805003800222480c3e00070f030703002e12418810b101d083e41c0d500101e501d0709510120303500400300041d00c03411501e44092810704000800c0540e010307620080e600255949001c16440b0420031010f10340c984600710300500c03160b81c1c201d4182c0490b02c014200500110503035041000000d1412180d0308190030200e440031001d0848022595110f5005000b450f8084500303d01a08040c04501031518199032040140610155980b42516000c01c03c4415500504222125500c44070140f0103a0340a1044941d42104070410400c5c3c00d078589010750071508044140c030280030710042e040c40401c1942040d81c054907540d0800d250342d11030f032181080c0342c003024003082a8025206099041008808a03005028600c60307022182900c3d403000010106144a040000c00c550010070100a02072203821700e004011700181c07e80b403400100b030300441c080d50384842 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 679548902 1250 679547652 679547657
    0x504020a022103010303050409020a0c0b0702060115022b0c050102120f07030917220b040303090e01030503160809040f0501061202250219090b01030f0c1209031806 72
    0xc041075262401c0e102107000c924080c0300b14590760540d40c0103025800ba07400703243d8039240d002c0358031080c481c000c407440c42886400c04aa0900c40c501002d00958401c001d0090388082e0510201002d2494000190200c0c0054a21040041008003080341b0020303a0403040c031902000001c1b060000410000c3c401401ba203034a5002050b01c1e480c009c80410f0800340040c00c000101441c1c6985070010801d4100c0070210310282e04041070f5203844101486040c092640a20b50032102c0501c3d0004040c0d40d40b100070030445c1c1c80380c1c4810701c00d02e50304c0b0f0010a40c1d1000348005417081c5c00c10050100ca1016502400740c88522595505041050401c0410300700c1d452042c4003a1401e584000610010307405c001d0215612600c01002e503c1c2c80401c05908070200c1e400c885020009002d01020821543c6843c0070030240e41c1c190303400100907591003000d40c01414118500502191820340195994400703030246016410340c94840e06405138138075551400030114070405404011010380c41482c4241010800401422941e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 679550152 1250 679548902 679548913
    0x312020312160f0c02030c01081b0f1b0109050d030f0f0f021c1a0409050109060213031a160e010315060909151d0912040603051504060602070506130504020a02 70
    0x2a0005020f400039103c08409005581244900599001407052010b04080c60054995201d0511505012900721254041d800c008200c6100c20101000074008401004001c015111603607014a800c07140c00c01c40242181d044500c80802c058002c1d0441030780d02c64440000119104034801c00700451301503a11001c01650006040785070030700c0c040010300641441c0002080850061207802045004102c020350080740c948840c0d00600c01c00f07510446103150040820b541e540050181861642a00d000481c0c54010f00b003140b802240701d44089a00c80d8189451a14641c40d540800380c40907025071595504040e2a0303405100003500d211001d500501c225220035000c5401c00030400f007581c0c0c240300c24100741d103c01d80d030400807140c0b040449051040d604030400742c0740c1c682c850300ca82009141c0016403110600001d0025070380364140e05c41807282d0040c00711400314000507400c000a48080d48100c0c0c0050740301c0d07002400503181101c0284400f40c0040c01840c4002d64801c00304060341c01c0481040f003d40c020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 679551402 1250 679550152 679550191
    0xa090f0f050933060c1005010806070302070b130204150b0a030e0c030c0d1506080d110a0b040b0c1b0c0a1a2a3705070312020312 57
    0x2148541d008002c400243e1510b201c0340080d4084200b40c0c1c1c00f5403000016951512496498070021206150405400d6542c2c0c46d0900e402d01002d04000e01c2030000503c1040000307075065210b07100784c0d1001540440706181d00d84424107543d007032800c86003050741e0082d501c41d655401180c10700d600d080200104001a41c407444070f4072002d07007107400550181c50143c0180c0c40d2602c0503940894074042d040c1c01190465542e101c1814003010901401600f201a14035100703010500c0c41000441e018010480d544241c0e8078a200d46945031500c0448800614401c211400b1400244d881d11042d503100102d100001d06145030710700030190443c0300465a008a070002c00320644079040181440c3c01400d00200d40300c0308582c031020100c1040c071907102202e9141100414004d903140d0050011f0004075a0340045518210303010a011a0561001ca102241c2c401503118410241c030843e000e050442e6000b00140c90341a1a580351409109440168a41180004c029410810303070200c1c0228020712406546144070641c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 679552652 1250 679551402 679551409
    0x201020c01110c060706061710060506070b0a050711010c050403050c030609060f0a090f050309010801090b21030705030301060f0e0402192f0d091403030f0a090f0f05 73
    0x8000c480d58100304100c01690720307144000039405000902911480e6031226a4100340c40101616086216800140e151380c00141c11700203034034243d0300520320301003040382c0d52101040054858454018405400b041c00161400b20691000e0381c4000c56080c1b101e038000c6100e051030708551b01c0c00741000c04990301080078400e1200402800d8100401540200a1420030413121680e0360320040c010050204060001803e4002c207030800b906050b4000d69902d411b039040d00d085502c0b80c1101342601d0002c1d9900c000000d48005034010b8a03911000500412070b41603180c410004036402034140a03000b48010454000011340c100021402050143e40d110640354421a005106400701c0c1d02e0b0034030480c010700c04400302d6014400380c020040f83ca4100b8030010844524501d40c440000c6100c01d14820200150208034100401c128060040907a90b4a55080d201c1c2c5989034003000f0303107121907056031060245d101e080344848003d08105101d400c00e48440b660790140048203007041c1e00b20342098041100704103c03906 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 679553902 1250 679552652 679552663
    0xf1523010f051e2704050c190e1011010b0f060f09210102071202160501110a0b090f0d09081c051b010603021023130305070b1306021c050904060503011404020102 71
    0x7130883d07051040342440301c0130400070b00030645400d1423807459402d1b280c0602c1c0103d03081140454040e010500d001040c0c64064255072100411140c0d40d400c00881d10024030f803940200c104031074000c05560034002100d0b07510950f908141a643c4c1c000ca16a00d0502e11400c0490103401003021300c01c00569541c40d07a10b003944501c0044c40740302081d03500c015540c000f521034444165051720307820300e0440780c240d0100d000a031800d10b48040c040c1141c0d1042c810f000c100703103003c01c0024811035000201d034010324481d80100c6002c24a4440e1100b181c20142c0c0c2d00d034400b0b034409841c01d111000e62910074104412500c80c03070858403148070003103001d0b990f46200b0000c5045c80e81c01c50803e82e43c5410901000c820502c14445258064000c02101040000da140c610726108802c6401131178014084540846e100c021000380359020346040e2004500c1d05d80f000440520000d0100440304400203111030b15a11014255842c0e04181c00c035640c4140c84101c0461641c80c02d10426004820701954000da50420740000790408 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 679555152 1250 679553902 679553977
    0x160503041505160803060d0b090a050f2a0102031312020307050904080a0c0302010f0c08061f09060e03120c01090c0e15010c060f1523010f051e 63
    0x60074810907418100000b50b421003d41c2160f81c0070380e2a5601c50015030644940c00c001000317059032505210203000c001815000d4a44035a080700d03403800e868119285d9074400d048400319407910052840a01d101203207561450b180042c01101d0070300001c01841c40c0400c210350404959050110645020341c60308200e003400030074040d00c19041ca81402e44034404513118030807002050001607901401094401d50000c0441c6c501c914040107804410080104282e030140c1d80e291240d041c2802e040710b401d040c50b50b82a030742403c0d601d610390300c6403418200349d0708462200701c1c1135410f0040b412150402002103004109008614000052101d81868000c0e800c0c03140d5003095032043d104800700034a020602c5401d100308982400c0141c0054000d251060240403800f150000305401d082a406201e44020348000554060340d00000e1010340a0651082885800005078000381c00304580c40309060040000340700301050081120841c1d00c0800c6c061810740c2c40382500a00e02ea0044150404c210764400391048078 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 679556402 1250 679555152 679555157
    0x2407080f0c0901050a091a07110306151005071b060f09061b0c0302030d2a3305010821031003060b18070206070f1806030507051605030415 61
    0x8a0811000414150252050b0316060110000348896401d000305000f03402000c070403000c0e2403600710310503003082c2c5604401800c586d03004080317030004002d00c0d01180d024410304a0b1203091014074000350802c0885c440e08140001404010800c04000c100c42092001c9071001b030030980c1e90214a0030034020f2040507500d60341c0c010400001010f00c8010390250601c0005c4c8180e002680c0d40c1e01d058102404551b81650001350304d446606210740c84240c00c0641c21186555005c4030044507d1601520907203241c400600a10400a144076041400304000200c8200b08200c0105c00320b01c40d00720001e100315030702070b049090780d0303441640c00044270202810391032038505403004070504500b0302005108512086000c01000d42c0d460f280d121515031603102900390401031660f07000081d801d005d00041c0d141c10040d42c544001801c0e4043c160003090044514449502c5034421448000d032400310100d00500020300b00808004003080340c0704030310100940c26480d1900407009991780707a140c42500316400b0242040c0d07409 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 679557652 1250 679556402 679556431
    0x1080114010c120e0a0801140612070302060f120403082703040515160605070e1e040b0111070b2a070902070f020405040b060a060e030c0f03240708 65
    0x4081e644200401441544000452241c000d044400c0d5000054420a03a0f00a0036240000940c2181500404803650b000502ca00c000c0c2c0710941030290741c101c41d0251501c035034410f200c200014140f0200510b0be09440924050420204c0b201019a106081d0b030309034006100c4506201203c2c10300129407011400186160301000000c40d14143c9a0181d44949413117454009002084c540000f030486134075443c1840d1041603c165850088000d040682c0d0850000d46006106400390070441c20345220410701caa40b170010561140c00b0400504450500981005080c841d05580008100240030142110340030407030721140044501046091040a034126100c2040740b006400d81c40418410161400c031f500c0566210b03103904024845450448000b50840d1824007000107102c00d150f41180036110031241c3c030030399036620360f0b00316000d4000b1a20340d079240e0001c2402b802c2610701010702d03543c17011014080d66648110000d842c04070710810a40d0b050061008410003200543c00030603141d000e00c81644954 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 679558902 1250 679557652 679557689
    0x70c0924080f2d01050405100506041e0f060e0106210506010c0803091c110f0c030c21060a0207020111011107021e0d080d110721050706140105010801 66
    0x15030750b846443c2c44045116801841d4014803c1e000c40403050040c034103000340300380d04003483c01c1561080d04100503d903440c0740c0070200302d4030318050140301d000d07140c648118069400c0300c500342d5000741041d009005c40541e0740d00000850081040f0258020803080d00e030b1015100a90082c058417460501c0c8202c06213290400b0011181e03004001d800100d40c2190034a600c2e81c0da1401400c1c038103214550a004801d911707a1941580560040100d00340c101548103039038444001c100c40301c0c0e54001112003564950030032410344005007447c1018081c01202d15502045501015149909104098032086445600020203100b50358101c16078007013400c000030013001031801d0021100c80038020800003c5c411280d88003c811240110140d01c140240c008000070b50721140f6140c44519680020740745804d580c00e0101130005d00340107d061311026a00500300110b284254640403007025060010704007488420300044010581501c01c40300340f040c4c0d41908604c2035040c80005444910305a000b28003180d103001588 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 679560152 1250 679558902 679558933
    0x40c080f010306021e04080105100b070b010e100302040501030b061c200a0305060f01030201110d0219031103031305061308090907030617010212010902040302060a05070c092408 78
    0xca04580c0c22000060300c13400480100d6028404030392400c0c40306000442c001c41d070f80c0819404a806451407a01c000741c45952402c040a0900909002905886400c0010406400d03030314181076119041e41d009460703843d00c982c00101210b500380c0095070009040c404218850030304c03909070541008284c04104840b070950351891140401c6049101240d0114202860151079003054040a1607002c070503a600340c6020200310126030000d03c8240c1c00640340984252851802007102a00061140d015040380d482c50b000c03140405249a400310100035503445104008101400a103019141d590801000b11145003403480c60306801404403054201407111940000300e00d6811100900e0055a12100b140d039405d80a6000740303015804404421a115100352500b04107500038680d1450415400300c07180d0325032030074000728080d50000a40000040000c2c1511900031030242a1641c82030148012094a41400d00c003a1034041540c00c0621001c0100c004c45d402d03d108600700a424910001c01c622020100c50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 679561402 1250 679560152 679560181
    0xc09131e0f080706050603100b0d021c050d1d0306070806010305090c09070201330501080415020a2c01090b0d0e1b210a060f0e0d020c040c08 62
    0x400d0804551201601007140c2692206403090b0406100d42e02ea007914100040600403c640c12403003801400b0207030000412a11400c82240302c0600103e44400f201d5003445245c10342c0a81400748040504050400903c0400a40d00340711084d55988021020503010501f412a0b03d4011522135003110003000b2071a54003403190383d4000400d280c08940c0c1d4841d520400c4c1808800c01c04203030008011801c1001094054004401c41c2007040300300384400d1610510001d04510079038a03c450342510381402c2080d136110300903847e0018043c01c00191140f10000c0740000320303400f070089440880d1800803010620941c4038044040c090148007141d035002c0c80d8400003800d120040c0201c0340014000310f80944241c3c01548940c14401c151021510741a110824104124074803141c4280b08104100324090501e200080c04c04000036681b0081c0f4019945d9900d6401034540728041c40d44090b136918130801503079403c00c4007003420340715a005002900720a106000940b0020020401484408018000c004008801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 679562652 1250 679561402 679561433
    0xd0f091a0708070203010c03060617040206070b061f17092b0201020d2f0c03070b0a0b030d0c03091e0b03040309030b0f0109050f04081e090d03020c0913 67
    0x2459038941c5145481112401454070180d0150f2038080c18000c4030703070141c0c0018185e0740540c0712442c00c852114070940b0b0110080305d000750000c900341704800001d1600c0380c1030398024100401c0450f603003903040c80076903000c04410304d0b044c002503400f59034090b01e50303901030004d0b0040c01050280101c7c811085101c4003008100c80c1e01e4803400f60480c13846c20340354401c0d07060361000c6880010500500001c2a158260510242e05054841d1283e01c804c000e481c1c031402c06c64040100d040c0140d030400c1e009841c0c600d55054018800c9000c0c1d0746a02403144550303002d0003182110451034450f040ba05800d4200202050b07859009100100e030b0b00c221380d8034030140d103021034412200e484403115034943c2e55203030442c4c400019600082c024042c01060125490b111101c041c1031716078000d420001582c0b8400700c142e0901c4140d5014040b00c0040240141c111070f01000903420a41d01105149442c0c40c541c00300d0001402c400c0d0581c01608042144c0d412460480900398001542809200c0d01c500d107900c540d88402510b11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 679563902 1250 679562652 679562699
    0x10e090915070201021e1309050105010c080c12040806071206080a020613150c060e0102090a0b07170a020723090c0c010b0a120501050604290f0d050d0f09 68
    0x10000d150b441c030075012610300180d40c42d141c6c40103410701c2e0101e51160300a00d440050340d001603100810380452a2107014101e40c2c0503914031a20201c80d4442940c95070040c40c80d054a8002e40c1c060341285154007000707000900c0810000d08451500d50300090440d000e03c099190014140001040482400a40359a44540407030300a40e9540d81810650311051890b4083e03032006550703440d45c03110340c0e400146c4980642d0007132030240882480b80650900700e01c90104181d0384611042001d100140c10100a090410b200d1806071400700c4480e4081401034001914540061740030032020700c60320800e48402030002e004d0600810709420701c10000f038145240100803400c04000440c200501c04800d4100da02000d0002e040e81175041d4072a0500380340400c442000303030b90b9507081c038012480904042c401c41d0540c5913082c2c984400800714040d01c0e2107401c1c8201308940e0084201040d014182d42c0d04030441603092285000b00034034150302c030700604002c81401184040c0460040108030300c491101c2e071320703e41800c240c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 679565152 1250 679563902 679563943
    0x40903050d0e01050c1c0204090e0a0506150d030e0f150c011a0d02120a08070602040906080610030623191b02060417040b03040b190b030304030b0a02040305100506010e0909 76
    0x142c07000340090023650304c4041010b040643d00c90381c5c0c400100358540d403240940300f03640c01503440292202c09607002c0d0b02c3c610b81180000e03107000c0109200754010001901c0080a1058400f0058002500707282c928000150302c42000070000c8480384240706402c0340405482940a00003400310004e15114002c42010b4040c1688102c0c4010343c000a110741c4103143e600c404a251164842d007805402904503002c1c2122491814001003064440080c03900c3c0710758800080780c0c070030720300796654030001d41042030a55103c903500310500981308101c0e613025842000b40142e00d056801c5502c03002019201e091140101141c07100421100a582c0443e4103a409900007800107031300c3da95406184045e00c00c80c0d00c0361032802d5010050000b0407208107180c43c001da20000032040c0300c840080880d0111003492500f03a506a1081000308005200c6ea449281c0c0310201240050920365030391151410107412038003640d0341035a5502042415078011b8542d031500075050303921101500d0b0660350265a031848202c183c028140301c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 679566402 1250 679565152 679565197
    0xf090f03170309070f0902091c08031b0c030c030d0b090f01090510050d05030c07061b031d15041e1508040501090c0f0e06150301060503070e040903050d0e01050c 71
    0x800242004082c441750500b00141d0f107040c410001d4104565441c4613101a1000c03629204404441003121900807001500c1d54a603020b0300c00380c140404114014000c0c0c180b028800d02141840540091441400655940c040104046d400c582195480740d21921420090000c21036046682c2415208801c8001440d51107480200040b001d0640c80660f00c1070403800810100301010000c0c0500703648920885030802d8039120182c85004050590b1b515118440004a001c28440d903040040340d010040400f81010030200414000d0120760b03a08030b900c15001604121000301c02c0ca0380100c1501881e1099041c5052811b00412014000102010000b00c4000306003408400c0d48021001580140d22031441d56440240c0c0010b144644a1100e000c0705001c0040c0c141c0c00c000b04102070411303024012901d544e0800301d068038150000f410100802501d031188041c951258401d00410034081c4e214543c5404490103044140c844d40072051030305904145c2071040208000e400e985030107041aa0700102680d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 679567652 1250 679566402 679566421
    0x70608181002041205060603060702031c0b130905060c031e062e09060806030c19120b0a06051905130e301305100512070f090f031703 59
    0x1030030044500000d20004000800300b210610074290544100300b590641d0b47e800c1e00301900d4807400c0301c01d280980c20800c0b0b4400008000b4101c0281c20701640c40020704181d94201041c1c4404031946103002c0195201c404105018040050582c00241d514030545589054110506550420412040803100c8080070910030f503100c000404081d07e9408203102078501110a40141c26401109100443c028503c003142e1548140f80d45841a04003a00400300f080300c1030144036854914a00c1c1030903100b00d007a0086a180c031030f6034400c888603005002c2c1d800c242c10000030600464440760b00c11445003c2440a401c044450004c0c000112482160000c00328035a80140c54040c100305800e044031401401000c84422004010110b41c81310144202c00580c01112501c0da900d1040405c12140d0390124501009185008482c9107090c0ca0325203031103820703c0010b2803a0081e044040d141c03c004213801c41d8628883d66800040c0c40300505a6035440b00f0050325640319026580c841d2040c958070000c00000041c583c80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 679568902 1250 679567652 679567663
    0x306090602221505070305040b090604080f01020c0132060f060c0f060609010e0a09030201020d0614010e012a02032104060e0307030b0a0203060a033207060818 70
    0x2401c0b0318180724842c245507807100140155000301c500104100e080c56001c0351040c002e0b20110380e8540c072400e28280c248200e41c00541c0100103044c0d8044070800c00803901207030501c000c7c41c607241500000750f08c0c0c8108402403030030346010881c51846400c18020103006100000b900c0e211a45e55070181e0105030300c440d004107949100d0700b0001c54000500059051140d8800503036425100407074025511162613050410150300028403500f070b03c08002c080070503000142540010300c47e41c468000103207005404031440c02980d060758400f100c89003028504032083d58100982d03103003004c3c0074600040c2d140c0354610191985004144508078202c006c603540011500c1c208003c1c2c40000301c4842c0240c0e45004000e1100d82c079440340c0540e10020790307000d00c1d05540d8100040d520058a5210241801958412040c68000c1d0001060950711545855002000c80c0ca49200e403168802060f88600006c02c602210ba03112000d098040521680b03c84410415298081d100d40c6d0060b44a0342c105854411104d03885251a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 679570152 1250 679568902 679568917
    0x19210e0c1c031103030103050a14070302090f01050906030a120c0f0212030318010908030708060d120f180305340801090c060e0d0303020d0905070306050603060906040302070306090602 81
    0x414031a82601c0103a0076070103407201c5511030b580c3ca0340210741080c6039540300d01080c8401031071039200030503e2001610500019544081d05c80485595940da500011081002501c0740145010400010700290400845690f4400002d50050400443d0750392080751400b42d9205520070800e8614900e4100924030780340287d5503400070000307610546002e00842d20395109490540c86120189003d0580c0720040c003410015641000a10b800c42e641e050701516440303001001c0542c4500c60124010002e42900030090025400360b0b55800108040c41020f05141c04191000400d400d4078401000041c900041410002c0c100c0d12070130f006041003045002180b8046c0c8c1403550078000c000d0010666040560010302c8090040d0a03219145944060641c0c41d4a80f209640390460442c5007030f00042f03400303070b001081280c1040c400003c100304d49032031351414040035400481c0eaa586502c14080c032840d0800c0001c0d045060300e00a05a1030804d981c000e541c5082512000b864140c6580200060214590503150903 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 679571402 1250 679570152 679570159
    0xf170f0309030301060f0219081303060c0e0a090e0c040f0b03030c0c090117030d050c041503051008010213030b15040614152d16030519210e0c 63
    0x240d0601100050300d070f4000b40a00c0c07002440d0303030b1051045248001200b074442800175245e10304039021030311403c0059010700400f0014a081642c000300050561003501f1101c211030303031000c0f91191907908109511485d5880800708074142034003c2201d0001140b0200000012100042c0c1c3c0300d400b207903000213041203454545c4e040c0008105081c50301d4000c140f4650b11141222880350580c4c0b2039441ca2991042485ea4680f903510a204074511492035038041e40d001003190b2036490074150740f281000070b880480e2507040c00103178554043c08500c0a10880b0758001d06440340c002d500301002d540d913503402e8000741c0c440600f83c1c18038240881c11494a0711f41a08507001c01900c1400b00e80e480c0c00061050711105910345010315684890b48400c00c0c1e2280a80b00380c85403800f800502e0410400f4001a503001ca005543c038890003c0013905030113117040c8040c21115109491300c0d40c4500340b20400c81181c01c80180900280b120009001c8165016040140c5d4035030000c450000d0440e0341d1080f840e2070900b0650100741c2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 679572652 1250 679571402 679571407
    0x1712040f03050c100f0309240204050f040903020a120512041a1e0c070611040608010f0902090a06030515030a03180f030b37091a040f170f 61
    0x21140e80103000d080c00e50707000788201c65001d00110180320004d2103c0c2e040c040001c10780d03803a07185154802d42003021194002e80000740301c1e44069580c032441030038103e400d02c1400da00080800030350070103807510a80c91604440c100a0240c107900c0280d04c4004001d40281248840303d0074068490180c0d09881c061242c070b020344040340c5018a040030080040e0f55070f42031194100d800048515100040101c220700344852400d50a840e0802e503075001e6003003030703404541291b292018082192109409800108100ea654621551400544000319400c0b0341020942034010000d40d91503440c2c40d480103003101c0d0103140c001511b82c3d0340480c181c001c40090503503a605026403010501850b5000001c401c1800d0440c4102417040d58581d2030000407001480002d01103028240002c00300d0841d4442c0e02940c2045e41030034145200c80544090703c010000594851940d91481c410003032100100c107001c8038003541d51459103203003003517101c0c00450b40303407404010f12200ba110400d9201c032a2003c1a203169600c0e0440c00c7d0b4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 679573902 1250 679572652 679572659
    0x7050c030705012007050c040203070512090606180103081909030f0f2a0b0a030905060915010609050102031801110d120b03030708030703090c05060a0c17090307171204 74
    0x5018000b069840130030480500d021a104520741800c03620220360090060030309506000c14000a504014403207400d021040c40074040507000d5181161203074031020050074003460078030200500c0c6421494080004080d0b040148001441e41c4200c030040442c0eaa4a009081c0380850100c4d440400c42e040105401801d16402040142c0d0000e180200c0d4840c18160f5407243e803945070820341d420300705141c00c4448854801044601c50410007006441941d260100300203620340c482514100090304c8c0200d0030b40c80002c181649825000f1a940500201d07c0d1a9481341e18240000f552030080d5901d050382113135400c95100d0260301545032a22020004e2041e01d52007008460081e00c01003500d80203401c858103044501955150110840310001e81c000f040e9411600ea80104034002e09142c4401c46c2d03071003c036110104180c1d4071240a0703c01801c465a80000b000100e15001c20504002014402c610f04e085c07009031804c0c1d4021030719030203451041c4440300b020310121400302c0c642110070b1034ad40740d084000100072 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 679575152 1250 679573902 679573913
    0x40e1f060309150905010c2c0f0609060f03010e0a02131806240905041103040b150d08071208011406070501020d020c0706020f0307020f0907020c09090607090e011d07050c0307 77
    0x1e07100c0d0715611041401e2300d844028241d0800303207c030178510710000c040c000d804900d006a842c961105000e48802d081c80000700105000d1361102d819009009004001006442407852503503a00c030741c2d940c01c298101200900c1005115003c0e004102c5003541460214030001c0352035100c08020700c81300450b8500b8030b03001600f62110030002c14501c0001407000102117240d00b080d004268078507030200f41c12031039a62191144144a40040c0070f0000706060b4903411041543c90700f104189203401ba4000a5446480c0d15003c030910154101440920440310010000c843d42034140c41e0071140c0c00c1c0c82681d03403121145003450081c0300e010380d044112840800c01003100e0100042071030a40780e094003281e82038800b1608160392402030f008000d500281c00e0004501c03908201c0030307545c2c21400034011500c09001c3c400001c3d84c6041c04071013480d1550701c8541008900342e4400d14400082c80c403074615003015418071402082c02e440c6814060009228000070806923440390f0125103851240c031080d2504c800592500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 679576402 1250 679575152 679575161
    0x3010e040201451a0304020d0b0403021b0d020117060402070c0308030108010c081b090a0503030a17010b0702090f1302061c060f060f0309080904060308040e1f06030915090501 77
    0x21110b400d040e542818440490183e03030f45098801c0c8250b810b501d904400c243e0503a170761008200700c0e08030401e0380309900014880d44e030b44c60143d071080d0003a114032805101c450010f0458601c40074415204000c40300090b0360088124013420350100b1100105950742e1022501900c40c2440040482001038030000074032000001950680341150300921405580050441d44500242c1d0f01c02e10611904c01151026034454005140c4610084c0c9100e5142e0769850000e81540c01003100a0081580c00c861440c50b0458003a280d07015241640b151800c18004d50041628080d00801c0d081100c151480886c0706084141c03a80c00c101d130746c01020166250440c090b28001e00468810350b800131400d00c90040345a0000c2103400041d100d499070340c42051450500c5c1200608442e203800c0d540800108a10599038580e0700402c1c01850299410340d65540c079118032000200c80080c41100d0359001d0b80140d18403451040d01310011517a0301d29001ca8652407a00308000102180121420a01e00d0000e13101c4c01c01206400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 679577652 1250 679576402 679576487
    0x2190b041506170a0b0f06090f100b03070201020a09080610050d060b030a03180f0506120a06090614090a020708040314070504020a080a05060a0b34061b05040b03010e040201 76
    0x300c805c1d51a4114503211104069903031300d45c40002c10300041c500d440719400d129030100b20041c0116a0035503c06102c5440e84c07064070803c0042c0d400040e0915244c0d040a54100101010001001149021201c4817203c000030f00807140719107404007903d414003240d41c1004010410040c192a405805031601a00031940c148120900d913040b20400155000c22420000440d100508150318101c6920240000c160008024400d81c545c0c508002c203c510503482030001038805c038220f202625000e54204907907000c1c000c10441c0241d0040060100103822030040e03608480c0d10441c07400060f5900903207241440c0c200c1c4c00c01500b00d48081059a0303243e91003000705004a840a10070007568030341c132080c000d030741129005078000b00b0020030001860640020040e403082410126020b003014140340c81e170070343e60012030302a04c0c041c0c0c888000202810022210303030340644860622626040c90912441e080e070005114245034110360b04001000d69000384040d100d40c40d0386c25440e0200c1c0003003c00f05005d145440303a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 679578902 1250 679577652 679577663
    0x42c0c011202070c0e250e12070b0403030e030a0b040c030b13110f0a0b0403050d27030b06010e0909160b0903070905150d05030a02190b041506170a 65
    0x156050340328110b100700c94180b03410a070505030a03030500003140200b90b8040e081e42c0d4105032040c40c001149101e12103600b500d0031260750700ca00c0c40110808001c095070581000c02c1c140e4001001c00c12005010380b04a0b400c403541030400c0c15841c44140d0019040c0b159980000c2c000121150030070081045c101c10440070b0303900c901011480c60311051400c0c41000000c07503000f002402e418000d542d191420403d118006000181f90258507500c1d500d89030100c3c0c02c558001c0366198002480d500c20b0581280300380c07941048843c0c440d0b4200306034011070b03043d40a10313100c081c000341e1461022540326441207035032001005010349285074900b01446019500c442004401021504072240440e4070800c520840d2001c01004004103000350421990310018200542007080c00c81c1c841302503d503541c0b18804802081b60285001d59211003109001030305000404644008a004865109000850b6100c42035006a004810310740c02c0d40040400200401640d04124070b001e100000c11080c10f980050307403181c041c0c450b1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 679580152 1250 679578902 679578917
    0x30302070e060d0b04060f0f02090907030c08190615230f040b13050301090c090b03030712050d1e15120f0b13080313051504030e042c0c01 61
    0x2040d10074019802500d009a0161581020601190208010907085400703008001040b1110a0020045030780e034115201c2520b401188200d450b01d001c0c0c103080c0c5d00c95140e00b824498103660040042c11550000c104100040314644000b200c0256076100001410221200001418030584050b000441d80b1000c10020301c20155008420f01c03031b031025511440214589142400c1c00c3c11075000c02a001386401c48905690f002c400240799509014540509000d5503010303840c503040c65008419152000c0c0d20a001c3e5008200c881c001400621032a400d40c4101c2c0740090b290134030b0841000c0500211820303103201c6203e054007a030040c13010f89c1c003601c0b00111101f00b2049003561041c88542d09460421701402920141260f1404100300c2e00d54250b1084100d00c0c00e60440005a0301c40000da042a640d074031212805046000070018100f028210422031341050245500c0c1c255002004d0708030440300540a03584604a1400f002510000c4c180e08581d11928044004243c0ba1034560f2080130441c50340c0001c408 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 679581402 1250 679580152 679580159
    0x907120c0f02030a0c15020301030b1803030103020f09070c0b010602060a0f0603110103021332030307020f041505030a12180605030402040218060c0703030e0f01021902010309080f0403030207 84
    0x101041c40a40d6040d40245003003400c4a40d00390760034140740c0001d90300520350f03950030440456036100840c00b0703520415003403409060420701002010b1544200c0142c6038400c200500259480c03c0200004920403626a00d13140ea03100030444000c1d0000c00020202d01c0114000b082d0300303070081007151040460400400610030b80d8200300007640c0c0c80307110141003480c041513608460b5200703400500842201d207c00f00101d598483c081c0344080230112440014802c240c90358110b01052400b5800e40760400c400541c01c204240d00042c200350603001880340305690b01d1804203507141c10f034130045008003001400c0d115400383e507050041e0b245144901c4080001c0c00c5400186031200c1d0303d585001aa1810380c0c2c0d03130341184e0f1740340c0c2844004d60040381d000313100256241c040c8003281c1d5400d004040701036914000c3c1c0500d914600d40a41880031078040103204140c2803690307202ca66400580f209184400904886010010380010f030014032003180d01505500e000540401e980e410500208100d910039800c17070340390940e0b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 679582652 1250 679581402 679581407
    0x40b0402040f09150c091206060302010801050103110d0b0a1a1b061603110f0d09020a21060f1413030e01171503120430030e0d0309050907120c 63
    0x210340c0041026052020740c28040301c003940702e03185d0410903090101103551101043d450503d41c166003103030016112101030046503813040c01d45005000a01f0300b03105a0380e0009034a00300b80a01060034411a0761101c607003481e9600c1501f004000c003500c1650628141e00e00c05004103940c0301d81c0f10503c2c4c3c504400380e10111990f0005600340f240c6046031441140f040b045408902a0a09034903e00100358140200304104c40c1060040130385680910000824849501c140b0070032000541c000512081808460341cac02040450030b000361143d0203000020541f450101c920014071114452a02160400e810082c100070000c80c4020035078001d0700d549210010510045038000c82c4001300c001401c0140000c118040c40e80b0500442d002001000d4814410120050000075042640b20801514400e10000d8480750b03c9450001c0702820a2901c0556071000d0710081c2155182081a500a2000144d0395040c14413540980703024000003440101e442c2000c0400510840804664442130381c942001041d1050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 679583902 1250 679582652 679582661
    0x10605100504140f0d020925080a1a060a05090d08070501022a0304030f0519061b030b0907051b01090609030f030c020c010e03010e0304090f11040303090b0f07020306040b0402040f 79
    0x1000a00071211701556130b0034444481d401420004408a8215900000064016500614901681d6a003001380f508200300d505607142c81d8181d003154a0050b4070843c3d6034031003d040b0380c0c501e055802c01944c0c81c0103140206815500307c800c0a040760a0100d82e420422206400524100c1c07d0840040215101c0c60001c0d0884010f501c0c02405aa0080100704000790b05804850580c034066810b68414008201104441224080c021148156030301c0b001000c05001f10405580d24505140400180001c4030100303502c0c0c1c0c8041d0204051110100d036107810841048031401074151904002d018503690385c542200901800417088010941c180031a01c2c0c0144684105140356205a005181c641001001540c800080f080142d030036540324056a44000c50030802403001b800706000000720154444d001e0005c0701d00400f032401900d90108020004290701101184c15374503c1000c1c1c594880660409643c2c500c00c01c54020740500901c010001844100762050744194002c0c4d40901240980301207000446 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 679585152 1250 679583902 679583929
    0x609020d1415040513050114090f030a05040311191e1a030a0903030e010e0f07050108010b1213061107020f0f03100b040f05010e180105010f120501060510050414 71
    0x50030000c84168034241d001341da0454052200750301c001617161126401e4940400003043c68045480601055460400c00b402803c0c400102950138843c07400d200402d2032042e48000340001c00b0507041c1440b030381c3e2080042c10a90760004444042540d50358480e00c0c0c942d90f55041e28807028811000003a03400c0040541344030410720244200e2840d40c4414070707a40288011213081d810161365040780b0105801c00d100380ba00c01405100184243c040c0a01c4048c03514405404c558100007000300104024981031080c1e030032612080783d0303039205c41c0e5480c1140c503400050264003420f05400d0408480c152000c110080902c00d0080d250400b1a1040c1410b215000d0b40c94080d868069112811001525065070302c000310764400108040f072110310824100060790400c0c0c01401154480c00107102042240544050b4102d400c43d0013440107624107030101c012a4154420503107420903102d401c0c01007100a502280107044000e00c05030911280f18002042070308107005070720441e4803181d4000c00f03d24203580d141d402e2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 679586402 1250 679585152 679585171
    0x71e0309051903020a121e1112030c09030c15030609040503090a0b030a050703060b04051e030d050301060216210609060f05070f02010b0d111807050a0915080402090907090609020d14 80
    0x1403107140c0c4030843c8c0003598030070040340da0b01501754001442c002c2000194020201c1100568440d0324610425083c8541e4500492285060300030749400c200c40c3c1816241e0001c0c044072111350581c0c0b0303810007504500c240450303a035009020803400b04034020314002075030150020f028104a80c0d99104010341c03c039216405a070030300c1c0d034043c04100647c1c907011541d0003048021524080b142080180402d10f425140050702001c03640210040c091140d04010240301200c03403035103503e0607615006103245561038000300c48401564010500e030a1000340c6e002004000e41c005010401031803110303880c000505c01600c07082c00007141f031030a0362010f80c4140180d1409a900610040e00e031101556400c0088064110b2980c200701c50209002282e03001c85100f40c41510340b9294181e85202c01d0100034a89402508090036005103442d11300410365019a48591142c0d042d00c0002850b01e5a5100c54a02a55940b003504c0b09404c0c8000400c01c0c21264001c5c000b507000c0c04600740080e808401e420b86282e030742103c10211 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 679587652 1250 679586402 679586447
    0x80a02090c0906091f23071211030a08061518090406180302070f0905010602030d0f060f1806080f03191206120b071e0309051903020a12 60
    0x40c0c080c080000748840700b002056246030010700000318449600c09075852a0020f00b1018001c030460300441e210070351403a8060003240c4440100030f014114080d5810161000044411401005011f000c0c140e000404210440c4c1d00c8042604d80102460003c03140760b070140020014001e0300340008003d48081c954007020f510700400e07120041c80100d0400810584440345ca070080b24800165075101e0950315030181d8094021707a800c2c80c4060391180402d600c444070007482e01004000c000c0e804003c0c1d8800d90084d0b178010805d00e62040c01c035405080070b904000e02e0f850701040001049210400c0700544030600c0c0500748901680c0380c640d541c46503142c50300701d0440d40017042603143c1052500c200000001003030405011090740b800c4500b0445415030042c4800c0000d20381c40b0014002d15081044e0720160034509000d0445103d41b500b032213840144102800d054490355070004202007401100a0307080c840050000080309410300950320305500206a07a0340c4024210349500d1841501c105407003000c62003c3d0034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 679588902 1250 679587652 679587661
    0x90b010e10091208040f0e010f05150708070606030c06030b1e010c03050c01090b0a05191505060702060403140a030f111507110d0203040f05042306030a0f0807030801080a0209 77
    0x121101143c0c100c0d40700b501000041001c4020804003c0500f04082000409604101190b0fa03543e54682107148102030340f6035207541e90f400040448071455400f03c0c00b03c1d141c030768a20307052000e400b5a4100400d8078000040200300c266160b44060600e40f41160808400847c0250160600b411031001d2030000c0e04804855001c40c1c050801496840d054000014002400c1e4072600307000c410031740c2d28203076250f241c44c248090040c41c1e05000d54020039800c0104001c0060001da40c452a981344074403800307160f005ca13010f815951b908007030b2801075801c0442105080d2860741e2441c2c540c00342d5982140841c9200101c100c1d101c5c4540000c01400c009400201007203501c2d030301c3c070450352140208410104408031144100d1030405002d0442026481e40041d501c580c10310b0b11840210301d440d003207680558580070f01c01e40c10303140249500c1102841042030401c56100c100109040001006020b85404070310f00107002040300f01e100030000b5a000e961484140e90702c1c1c56196444071841c55002e5403001600000c00e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 679590152 1250 679588902 679588919
    0xc1403011508030d0e10022a0607090612020903060f06040e06040f031404170706021e030306040e071e090506010302030108060f0a061502060a0501080d09090c051201090b010e1009 79
    0x9685e44e542c0507045442005c1422004005ea80c4452405800c819120030500141c41014400c070468503c4100a0500783c90700b010020240c1e0f043e4800c01c07080121000c910310a05c1c0b03a5604807054074401034190746c880d15240d00c40c02007406050343c1071070140c0d180105821240002140150045074003c00721103446001c2c0d1001c03903030b00034266030005070300404003c0098072070484080e144d11192a90060428285024000b0307040000d00080800b1140803c00202030405001c02101d80c019011a0001801d00348900c107a841d240e0190840c80d80c98540c1e00c40754200e464012440c008481c40e02c4428070050307445c0b60045082c0d00003841402c1c1c003a0f220f040811601c1c01d142003001c4c1e02018440700040c003550303600e0f04110500290050200503070090070501209403072034029140544030040082c0541c40004000600b58161031003800101680c440d26054014030079000c445207182c8107202c0404c03030f58459200034000c1503100d001c2400b04205159400c418100b10401198004035501c400d118186040c141 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 679591402 1250 679590152 679590161
    0xc03030702011b1104022b05091f23090f0a020109060806031005130204050603151803040909080c060a110f09040b091303080f0c04060311070c1403011508030d 70
    0x2150100d081507040101500c851004c4e000500c0c210100e181030038103602c0102001044540700521f07a9081c04204408600002101c1004003511528000b000d4220b20440c4010300710b02080c503600114510800704170b907610a240c2030141e00c054043d0317071100360018106070b5110038956000340490300307808040091501a00301694000d0000d4242d9804800144401d4100e4100703c41c1148ae99400840c400c040d420148140d55210314290f00800399020318501c02402c018000745100845400c2c01307a40c111152081c001d4034000e2411640500c01c240752488c0484080e0003000640090b403042c130001030119461402901450502000c100f4a4504081904403507640103c0e00d041c0c1040e120012000242c413600050340c402d61241c4464440403032689401410010007801c4040c0410f088020710502d0080c00c01202c0c110744072400e00241003d14041100341d41d014030700000d4440041500b00241d404850185808001c50480007044009050007111207009140c0c040d0801aa005100041c823901c40380c0d11 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 679592652 1250 679591402 679591457
    0x11115131b08060c0f16050610091103010302040b03150f1e130809040216320c09070e030a05011e0c1d15070c05030d0e1f09120b090c0303070201 64
    0x4032900c0c040546d1030011060440800071078480d84081c1c10804148403030244030014101c0c221043c8040710410f000302515000601002c1d20507036982c000c690095038100429404440000791800e01494000811942d19400f11014241e0b650400c0301002c400718540501489152a200c81740c01941c1c142e00d0b03540490b082503603100c0d0455030810600b80b81c0142c4450262195200c0c12407088041480d00c403480038091868840221080090b140c045800780128005008020a5071451019a10380c44212070100c002c6132a01d03010f02468104406020040d0420200c90711003c80704a000d41c6c038003088000321240a2440d90010b9403508500d14030b022125440745075508010924102600603003e02140c0c0c3c0d0180104443d05010184e082103141024031560b0b0452031a81002c900407070340c0501141c162a440c1c0e40c000384010882d040f000c0000e00540e5408041c0a854a0a4141d4070440c905545205000c0c0c954000500c10000b6801061800208440e82a80c0c10307915050518181c03030307145100c1a48c084 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 679593902 1250 679592652 679592677
    0x10818030408030d02040302031b0612040512160c082d160602160b031e13060c0207030506010e01030309231027080606011115131b08060c 61
    0x4400600e0042c00c00c080e00f4203d90f11000141d90702e24520400d40382c003041c50720941e01050003d0102d000c030f9a40006a40d20b00c3c400032340b4030440d81d41d035203415410444201c414000701c02020461015031403e4940c0b480b0b0789481001d004054030703140c040c8196621120350811064250449091202d03405808842e00644c0c2010211350138074416810f0f002000c070a6070801c00051f444100a00618203c49044000030014040250b2450812101c00498079a20103502811042c0d58000f1983ea5561104540ca8064000101300a00d03d80c040c40251601c00a20041d50070388140c0e000458406181c013641d5048a5040c7c07034494065150004440c544605107000070343c0c0d803a40006000d03442c1c542ea10090754461165550040481c1400c10100c66081d1030401449011541002400716440c00140b41303030883c4003402d210101c010301d0020607103000d8205042c001032040d80414001c0d20f001d40658294090702c0342c8060141d80c000c050131040e44810710f129122096000101161030344001c08001c11faa0203546 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 679595152 1250 679593902 679593907
    0x60c1d060a14070c0605070b162a05060c030604060803040b09040c1106070302130602010c0e1e1807020f03030c04031728031b0c060515120a02090a0b01081803 70
    0x1904d9840300d481da954030000105400045020401c0752140b81164003a80b814402c1203003a66066006100b05c001140101c402041c03001501d400e40490100c0b9440f1540c444d08441d1286801040c0c0c0078250001c0e20380c1d6000d03d06118002c01e40c2d51010042c2c0f01540c0019900c80d041c400aa404c010117401c5940901051015a035040f600f07280c82400401d100700c3c495100503944131044507040c1242e04065211408591401e43c0c4039007155031004d101800202c040300e02c03400032900345a260f0034000807441c8059202c2c4905680c0c0c1003c0902010480c860582070302034072501103044900644074070007242e40e0079031440e04110910016a00c0741280c1c1451803d51180790514100c140c9040081c8a0220322144070f07000345c3c45200d07426516000b6640d0441d0703044104000c80c5044400079001d10b0034840000c0407251240009814030322010200d10000000401307012042c512004141d442c1d245090302a409046071200003030b14a00c960161510680040e903c071040d941d118000d9000c407040d030740401c030f540340402c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 679596402 1250 679595152 679595167
    0xb01050f160213140601090308030f070201021611030c010306030b0a050405030906071a07050c0a111c0c06022103180a050304060e0102060916120c080307060c1d060a14 74
    0x55588046460082c81c20006600f2400c004d09a07a00c0780080c021410810100400e00018105e141a40c0d00f001400014a10a440d2040706034064001d903000491040707001102da10600007800f56801c20a01c040d030507190184920b100450031740d00350307000141081c1a2040880e0100001e644041d9003e4000e105590524080740700152030390388041c0041d540e1104070201040c00e038858260302508840b982c02d106281280c2c20000d5502c44400302c3d0b001d012004070909107001916086000282441c0c591400141c0222502e0400f021a8050041c000144551042401e075504d003a40692030f400c08540c4414219034480c0c00b02001d004628402070a02d0143e50000e078005142000544060280c6485071280c00701c20724002858000e0040c140701c0541e100281c1c0c045030080111902e020b5400003441945280c0c2c0034281000d8415669000410714400000c428050101c50745c0b00b411075003019540e264991038803001944078400350b5080a58405810041a103c04d03000d4070101240f010a01401d0b82880348 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 679597652 1250 679596402 679596409
    0x60423060f04140f0d1116030c030b01090203090a290901020301051206060a031e050f010605090c09010f0e04060801180302150103050c0139060e010b01050f1602 71
    0x3419200340c0c2450421109110030071000500042c0e0071208140100036205007a4402e6076a0380c0000b05400c180403008014540d404000e1101d00c128001a0900f4080c02e5644c4c03500d182e04520b20b04c010f4490075511000490a20818001c690003404000c005014104c110f841d28a00285104964190000c07920703503500c681d400180100f407041000d0301c00182c81b503240c90144840054032000a4025810540410901e03550300b0702c0003400d882c0c0002d0300402150021503070410b03003080300b100a8020710505071084600481500004180c4805031001d000c1c9071180c600d42c181d203004100240d070204120340720f200140d40c4a440c0303c0f0403587c0300030004180542d032144001d084800b10b460100114104190b00c0e018150100300d1001d0142e100e030020b100d150326640701c4580791380e00300d102203041240140304078444e4441c0310f07900c2070703003012000c03050100c01e203050b203551440941c00004843d140d0404149c0c0d6141c01041c4100410b052040e12498600b10701e01104810300e0b0f214809003045d01200c044074602584 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 679598902 1250 679597652 679597663
    0x8010501081f2d081f0209091602070b09060313080c1209030c010f0f1805120307123f0501090e060a02031623070b0a0609060f0506030411100e0a0e09060423 69
    0x42000d90fa40045041c400c0c000bd040c03d205802c90981c5680c100720f06039203916082c04584d032020103520f04118040d00340c0b070416a14440d062902407075201e10128040a804008002c02a4200480482d040101014010355140400ca40c1090120302070079107200c40030380982c0171000c0704505d00f8001e145190303d450014101e640100740d46071003580042887c5080150040b820707030300c103581030030103220306401e10f4607019510040c003181d03c0d42031040110740b503440401a403081070303826540c42041c06150b0719001030340300a2054045101e500d114560100d00302d00400e100301c078003400078000c04540700d40d681c3e0020340780b2071001c0d030889440c40140340011501010304405485030074030035a0b10084600b084600c49090700e0381d5030000012189412820062521100721140c12030b0026290244c0340e94550905014072420010604c3e00110300c04805040d4590010506029007001c0301d51596060301c44298041e040421a2248855030154000c074000c0f420807a04d484944215180400164809968090815 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 679600152 1250 679598902 679598911
    0x105031f26030306030304030219260606040c020c15190e01020601060f0f030902011101060902030a14060906060705071a1c05040308010501081f2d081f020909 70
    0x14404070508a6010864040041440003850042d0b0450074141c0000380c480c0301d2403000910921070b850200c84000d66160b403484c004c1840909004000c001300d1090303038101c40b101c079070031401e405683c0001c2d0444c03a152164a1031719620307500401c0100183d0701882442140c0681c5c01c3c01540c0140004104500c00c0c141101e07082d0856176942e4410030080c000645041c406070004024811021565529203904c403913060000c80881c0b0700480c07852110300068a81043c0e50511000c00c0d4204040412403543e950003e6000d2008148100304201700e4000343e150b07100f001c1e10115481039250303020401034545400540816400307441901d00b0705035901400141e1510f1000c12103440d060100d6540e00b0696941400a0203224400050100740f901d41e03001412440c0500400c2d040c000c20f000420040c1c00d4258010018941021003401050f8a0b800989010b400904c84035516403c10340072648813600700d0400d282110401030050101202102d001c0c0140c40351903145624440e400c0c464043c09a4480d01501c0c0103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 679601402 1250 679600152 679600169
    0x150102031c090201030c0915201e0607030e070306020f0f120103051e210c030c0723011d03100c0819060f050105090f10121b05090105031f 61
    0x148810b620000d0240c40700d505c510411301810034420010610710410601d0f030707030010740b034004c031805000210200c001c800354181800500c541c1c40c18140b22050055018980c0301c411081b03c04d40e079100482101912451190204240c011002c02c00c001344040d00500501100d0a40349418a2891316905450790020919402c0005052004100740203003403150035000311120750501c002c2c205442450381c0d101584800d80100110908404810320028002c5d03524607032200050740d9440c080618659918921170140c0680410505115065032102c28801218140c1c181c42c0e000030702d280c1440106881c1000780109070140034000c03c0b0001c041c03a40c89035441b840e9041d01c0705191400c0c0381c3c8500c426803521011540420b484c110041c061b00c215442072004480003407034241c1e950880340000c50400101587d84541215220319100d403030781c2c1c001c506565641e102030001c01902d07a034400c00201c229000b2a40c0000305804200c4a84a94491340040d503110b000c51a036039142c044026140400b10a1039880740d102c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 679602652 1250 679601402 679601411
    0x6210e03070b060636090903090f06040302011b06090506040f0618110f01020a06020c061801060f0b0c03070b011512050c04121a0a0209090f040b150102031c 69
    0x100301c07000700b41c20b402803419207501e400c248030340072031341222070700407619421140118105140c44811112849505e5102801c444c0f0581064040c0581c1c035004100c05a110f01d196220f21002400d2010907141220b4050f940d909130200f52240c4951420940c0000362401078a070080d88c80404c01c1000042e000d9403240c1d440c220940c1040c2444800c45014900f13000c1280035103021320300441c40b15650018480b4003207613844804081000180d1038800c07061070041950f400803420350550903011030b442d4072512580c40100070b1441d104510508a42850140f061500080341e818041c442c954070103005401070100889103895441c1d19181803c4ad000d90002c0d01442d1841e440b41807240d800684013031071241f0060207100314202280010418000c6008081c00313031a00030415802d20a14101150708003451003003061007820001d210300081e501c8240900d0013100124007261382e0200d807000840c880c07a045040c111807912170902603451070108407142c030304500c8140080c000012211f0403021a5003988040000d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 679603902 1250 679602652 679602667
    0x31e07020d14100e0607080123370e0702030c10051306020d0f15140f01090e0106080402030d0e0102210d0c0306090c0302040506030a02220801050a150f06210e03 71
    0x2032501f80144c1122040442d0b1402240421643d03036040001c1d510308681d4158038942901044e80c801c1c4002c0070000c50b9104a07030625a010b03603110024020745141e03006403d41c41c0e44d00138050742c0c1c5e4030516400c0c2c100380d03114104241c841c0d01e0031b50229402c2510032410f800c5c582c10a032541c40a03030304060100c0042650f1103508140c0c0c00c0091207052030321824140724940e80c51400c071614800200807202c7e0360241e6182318045100e68443d200040c013401e4400010035065850f40d500400854084400300e001e071141098000c80760b80184140a10403105074024503400412110051040d000c01810381400c0c00d040c0a04540c44195003c1c0c038400c80026500010807501c0c0c07190590565400d1400f606c14184100410301031611540102da41c081d801070302c096600c69036a505410352410301d45d24109007910b03020003c1403031401034201700d01a0b5210030f8240b04e0312250a010740032813002d034814041c0b22604000100a0b0502410400c8880a801c074442030842c6039440c1c010b81518007109544100f50400140070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 679605152 1250 679603902 679603907
    0x13091a0106020705030a060b040603050703120305060405060d030f14031317250f08040b0711010206010f05040f0b1915090509062b0302031e07020d14100e0607 70
    0x4600401d114401002c2140c03400c0d01090721030f02ea4500161004c2d460341c0b015400c07038071103030031580046038018221580650b0b00e0070083c0c401088101003500080c28240032071110b1500b030003846d02409000781103415080b44d598095071200440f010325000d07c0314034258000503030b41c50303806144a0240c100032450300c14101e2500504101502d181400006000d1021000080c2540c02e84d000c1503c1080206124001e18204402d001030309203001001d00100281c08165040c00c4800b810299104880c0a030700f828095006907200c501c02d00236a820310001000400c20352416030003c1c0d01855004500003050382410010a05151920f0000d0b1404983c40c0c1c8200184042c0b80c038504400790a518060282d5418400019a00c1001400941c42028482c2444102810107034107102c50040c05903803920403410501d000f17516608840c0d103540551011017241003940200c081100c801e0fa5008140c01c80e40c91580e40ca544029941c880399203110b01c2860445e00000c10640311b800c055120f01e4004106502d01100c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 679606402 1250 679605152 679605203
    0x170106030509070e090606301614010828060e010614030c03010504020a0302190801080d020f101d122503020a020d110402041806050d031b021309 64
    0x80c140144001d410804171040118489400000803601d07204020142c07242814000100014400c2030b41e5441d002c50348050300094030b4000c001018140c1c06406a44410802c41800d0403103d0601083d1502d0000d80040ba00c40020250038045003004241c440580120000322030703035a04502a000704241c0180a490b030090100d00c1c0f02c3c000c1c18402455850001c443d4180c600062048500950b00422001c60241c001e40542d25004003440018100641c02b0740d00401e42082071090304614000e007902e0300b202c02d00c003080a40f88041c802c001400360800400503000208503001c44400454286445242540003c1c450104003030540c544d9103454009020320350248040640f01c1c0b03003405040d40c104000180d00443d41c2d04115030100c2d283d46000101e424820004284404000e07406480082c0c0070468101d10406901442c0441104000c002d881d0700030700ca6000001c00d070160120750021070b41260450071301c541d01c40041c8060300040e01d1010145d0f122007500c80101c0100d40e0030365108070f1480c40c100c001a8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 679607652 1250 679606402 679606409
    0x501050603060417030415110a0e060a050a0509133210050607150c050c3d02040b032403300717120a27020117010603050907 55
    0x20b01000e003000c1d42c0c0d45580d410b1244150401c08000300004090144403d00401483c2484000b40090325006030f00920982c0700004c0c001c04100e00411007041070130301c04182c81c0c6207840ca44943c0d28000702e075201660700d5004510610381c015503943d00d82400c0f40c16402183ca10007510300b00c400c020403840356200e864400041140034583c03c0d150421840b240940401422030341d0940c0c4030383c3e0b298514100045405401d00c040001c260600c03541d400601d07481802810140030308002d542e03002c5100700c240c4e00c8010002182038401901c20042308030050710121050082c0340301800c0145015501d00e45105650800c03160881389406101a00542448400c46030100440c03c9014100956220040c80d00c821914500c8001e8a1000d0403c0704043c8a01800c44070744603000440284241310071046114240d1210080000c421700d204c000c580c00d83d480d03000310081000741d25802d00c14060501a02050004101002e0b410801e0114a1f00481031511641c58040c01090f03030301042615010740400d140c4201c0341e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 679608902 1250 679607652 679607659
    0x4080f06041e030f0e0f030a0c06230703030b0102030409050705270310020a0306030812090c06030c04050105093136020a1508010f0b0c0a030c03050c030a050705010506 74
    0x842c40c1000a610118400000c6003509261110518400204407007a51880e0440e8040c810400800188041c445076001214403940c0c480340014011f00340618004466114059515014070032200024040d800003c0000700610441c0c1c10513036150015010303501d0954842c40807540014440d0203101c101e031480c020045203c503400c819a81d001c4042691080c6d0001c5001a440d808900d074401c02d0b12030b4000a0056801c010800c0d101e00d4406a2807900d0f802c142c0d0107860500c00c00310078031014102001a01e02c113223100224a4141b926100055070b16030f00999000c1d5001c0ca40708008860110058407007070704030072108115910710702c4001001c0c0c1180d408803291500703000d15408201080710180c00c0001d13801b03000508400514843c1c801319a000a00f90444030706544c0c9640d200300340f06d603c580414101c0e03500071365104441d55254a900300130712030403540b50040d80000d150000440d018440c92000940700f45480c500c1c0c01070382c200d007605640000302020001040080c8030018840d003400344c04e4000c40103d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 679610152 1250 679608902 679608953
    0x204060b121b0d0c020c0a170303191b030c020609060105060708090406090e060405010c26100306020408030c1203130b0405010b041505100809030a03020d0204080f0604 74
    0x11907100d0201000208020700582680360811409001082a40d0030782004070030074402c1d180b802e080030f521820b44402041c0503203a158800070710840c04944410003e07040c040618515181ea400035440301011901d00300e11141c65080b01c8030300181b0804c200030100c12560300005c2c00309203414000d00f0a60040c0020440c1e9004a0043c031043e5654003c9815460340f29000c0760751480001c0102d0050001603200c0c100544c684000c03445042d50100c0d07410301c100e01c107034020480d09078018070581d085404400390052640702e07a40b4487c2c0c113143c110f1866070081c240c181a26102ca6803551500160f03441a04110040c5e0070201d00250000b82c200031441510620040c02c82c01d501c1e256900e442c0303d51032440e024003180d002501007070612000b90710002818401602c00d10040c08092403d108031483c910070300d03000340311402600c0d11452241130058010244031000c0c6240490039541200a90010000100215800c00001a01040c200705240c42142a000509000d1800c0d04048080101900f1051081401d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 679611402 1250 679610152 679610167
    0x1b060c020405150a12060b04020d0207290c0a0c14031b01060305030702101b0f030f11070608150a0815070f0905010f0c140a21020c060904140a090204060b 68
    0x2c0c45814420b0303030f8580c45450740d0072034107091003805040da100c20640c00610000b0310ae0841145a0001e01c190f9002e81400060681e01140b0030b1203c0c800c90f090a17403488e08210100b000e231202000189a014101c1c0b03070038000e00d00541c0b10740c1c0800342e07030550214240d40001800160310040114101c4904a924000c100780d070710b962a181c1d2284211280244074805c00c2944204141c002c00c1c0550310030132100d424051994961900a4980d00110801e40110f101800e1847c1e400f44107000d2008262800d101034a140e51070420300703954010b0f0141184c0c00c0c0115420030b110087d124454450001c0161500034401e0201c0082d000d00300350005072082c020007800c1d4203400c101c15081039110040342c40c20700c0d00d003000c4514010120780d41c11200100800c26582e442444254190004840c1c11007801a001d003405441c640e440080d169112000440240c0c020044410083c0742c010b01410b00004050300115900301c0139040c407191035004451703a035409a42ca09405043d2305081c81002d02a159540003940381019 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 679612652 1250 679611402 679611409
    0x9070c030e0f18070f0e03120703110d030f1406130f1d06041704030c0315060b19090501210207060e0a050708060c03042001030623180709030f1b060c02040515 70
    0xa00c2350a01c542c840b0009a100205441038240b00d440440c2901901d80da8a081080100a409450003025032a03040100c40c4040607000c4125a0040340000c1c2003004400000e8180b4005e0180444220121980d8266211841100120310061501904040e003000d1415280c10407080131011900905a0820302c02800050001c111403810f4903085822682d50300401d25001004d044a40c100300c6249034085050207a40d034610040b00079045198665030840ca49803001160711030142e4508401c81d038142150740140c9100d59006280ca0f6015a4022600d0b0144141c2140b4001c440407040760304be840020708100c0c0c10028003c2e640c2042907584110b00d5401c2039120103a154688101031101c595035683d40c1401030380a5404100245001d40b0f01441a620707000071240c000c003829024a000e2885070f0311030701e140e494984040b03202d00c0c160340381e0b001d119086469207200100d401c0c204079040300c5c444040109840c08601000d005101d0340d41e607100709a989206010507180090141183c08000100b54440c90b82c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 679613902 1250 679612652 679612663
    0x2e051209070305060c071b0303080103150911010509010215010b0901020f01110703110a021005090406060302040e040b040c120c090b04020c071e0e0f06010e09070c030e0f18070f0e03 80
    0x501c03034103540c8841c03c03802c0c107c0b40c40c199000c04030104903100c14004101900701c140c80b0b04031b900840000c40701036008807100040c2c0d006108028040c038980c410300d40c6d0660265026103919241807040316203407a030000c00f1a180340c3c02a0020207034100007049a030304035a07040217941241282c0c1c0c0300a0002900c0d0b030300141000d004102c0002c007449000100710b159041c04205a0211580007460390192251002014000f076210b01000d9015905000300480d019020f8001c490031246a16030000b416030300d5484000f45500068001c035140c1c140d801c40001c0c0c0f140e914030316a40080c05031601d000c0203032925082c5404c44103500e01c1c031400b0303900600c0354220f1264045255001c4441c100b24800d0f4050f001d080d070119041c2c45403c0548507103030f507005101400100000c040d00c124400c1e21740581680c072a2041082e0342c074080b621a03000403001e490000c0004d1041040203141c4c08050320400b01d142d24900001c146c012080080f5400440000820041300d034000b0f29800c0f200b4843c00c103a10440b2001c0c0c086a200c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 679615152 1250 679613902 679613911
    0xc0a0b0c011b1403040317270703170f2a010605180a05040809040906150e220f020d03210203100303030b060702040606020d140405010503062e05120907030506 70
    0x19078080300090605006200030311450500d81e07403008040c5000c4060031703800002103160348d00300c0000074248040c4c95800100f1405494020f0b44e200300100185502901e40c0d807000090f034442220600c9084200c1201e810340b4101c0e0400340e03601c0c912810324591000c0c210786851388140c1c401c031403011180d0080c0e20070700b40d03a0350402040c80c0003041030380d5a801c1c008400c2c8900950250040d00d4414480309000303582e4043c1a40140a001401484d42c1d200900d1010481c15100791040520030800c1e811b14200710380d0b0b000300c902d1140d90300b210483c400b500010744240341d0520640116060f003146522510402c255100c011510301c02c01c50540c10401c5501104001030700004042c1540c407103046000c0d580d00000d45046c00da004209210326602d50314025141d5584052110108080d4006845402c1c0400d00782e9045d9407060b5500750841d030b582d000b08500d0107007600d030340c41d40780003000407407041d2418660315090801050f40724a59170380303040780c0d0510140c00c0080040d03102c0e030003a200c280009000440e110350003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 679616402 1250 679615152 679615187
    0x20f070b090c120c0a050405070f0c0c081507030b0a03050c040c0c06091a070206060d02060f1201091506021606032c0615030d0e120c0a0b0c011b 64
    0x807961002101c51400011110550f4400d550030500c10803100c000803200b0654006441d400d960300e60358802e010903120b0640350300c4041041c0300d10221846220324520722301c160007100c601c0c1c3c00e02d546000c000e042c03110490702600c61410030713400c12800d84e070540a81d9082e81c00944100080c4c0b032458841d40e854020155190b4400c0e0b450307400c1d40b030304035119021000410350009020032200d1018900701144549400c0704150143c200300000308024008907290744a11409003d076800d030781c0141d003080b42c40d6111416900c1c83c0c400c1406030200c0c590942103260301920a07010001555210b00c52241d024050591202d02150700040082d9214800b03800c200085070100c1c00c0109000e0b009191f15501c6045a00d01c881e1842c58600c00707004031410004030240500f80280d10440e40c40c0c2040c007810340312482110907101060340380555604906215461b6454141000103a50740c180f90030000400f8100c807030703002c41a403030008100000c0480c0c1c01e20411082c000c0802c05005114001d000c0600b92004c01d90f0205174 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 679617652 1250 679616402 679616423
    0x7050309010f1109030706110a060216141f020f18030705090702070504060f140f0f030d02150709270f02030406022119050925060f03020f07 62
    0xc010209410506118a0441c02030161030781c0c203c680b0803903130080c050720f03403082c130403c0e500040003401040c4c920588032200c0064412100d8540b43c0f807001c0e502ca030301c81d00c05034901c0071f440c0300100d400c900c8a120754100400250440300c1001c0c80d4544100341c004c40b010740e446d104000303000e01035503264100d414004c42d011100600000010000e800d05000c0d920854124a2010800c0180c0d617010030003400340d0341c0c211401c10485855464051050041d80184140302003c89043c203620701e4a00d448400c2c08100415245c5280c0d04000860305000c058507410b03015074441902e40a411000192013644401c8a14048141d01c2c80c0001c9900076849400d40d51144034140000c040c00e1400a41100c89079103000d4000b13641d00d041610f00480203500022401c0380d4003200070715000010380c603964118003490744082c00107004146001c62500904010300110741c1c41c8034064117940300f240e94081c000e1521b104000002c60043c0741c80300190928603410701140130544104010300c2d0300400c0c50282c0ea2042e42042c210071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 679618902 1250 679617652 679617661
    0x308190306150f183c060e2107080d030e1c0c080f030112110d0b19020c0109061407021203160e1201020d0c03021e070503070b10030204060815070503 66
    0x401c180150030200308803028035041c8640c0204117070605100b0b20004a41e0700c100507514800240300165000361300018a4880800c03240780f4001042c40b1454010b1101c00e09524000980589421019400600c140d00041c0c130b942c614580601c100310304001d0701070140450315000c25004031500c061a00071303410312640c480b020080c042d602066848850240450b15941d507120344903107605103c10348088a01c0141c5092040080c2400c01500801c40e034031042e0318049490b6110100001261201407a01c555070131f100d00304003c0b200340030f4603008901455001801c090802c214400d201c4006003d10305652061071809032554444003269401080b2002030034540004c010129070f1003031000205503101514001d820103081c019402419031401d50241044140a060801da090b801864460b11401e115800c05034004080080140110380c4164160b918151955440300d8168209480320601040009424411400c00340300312800b401082005007400c50740c0304400800ba880080c11041004008008907 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 679620152 1250 679618902 679618937
    0xf0605090a170a0812010302131a040f110409020a17012d0302041b08010611030714030403080d020405030c0406030f030f020705100c1208091203060a0308190306150f 73
    0xf070f448650b002d2100781c2c0c0c410300c0101c181d032450300c01e0000380c1c030450041851520b0314440c0d1140b8072680310b4403084c212059403035604200082140c44503003d43c0c0f5840b8803042e66012003010040c07020f00782c280f100589804042c0001400224004110703100c100c0702100501020780d40c1c004070141d92001c0c2540b010f030215510f91801301017403943d100a41080c00c181d0f00b00602c810740310401c000d0850940e100a09a070341c0d45c2c030440780403540b0000100560030030000d03000441c1c00b0440324250100041c080740d00e02030752562011110382c003420021103995808681441240303424008901020421581480990b05540f160b5441104500004040c810b140c2d505400340c600a1000c00c00600000b0815124611220f9001d004100c40d6a011a10140c90220405159001f100040c0c01549498002c0900c1d00b80040088900c0e4809400b4a078000100d50000001404a1f002007a100d034003022100f40074104080050152001a001040000c09500c200360106500c000800039081d072500c1c06040011030071220 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 679621402 1250 679620152 679620163
    0x120030a0513021c11061809063d09031106090a03050712050c040501060c0807080f1c0e0a17160b090604020102070b0f040b090103180501060f0605090a17 68
    0x3500034211800704210100341c81e05a807080e50085d2501d007800001002004914424420104402c00a500984415007480146154442809005100c0001d240005540d040034034000d403010b8600d003400300c00c206c0000303070f20340507204803050030800d010340e05540d92100c071803a08141841c05a40041000b401d150b0b2542c0c00700f8000c6401c48255805030340ca40e500015004038003042901c0910800045070820b0810344242c9040b40d019580d40351035080c66a542d582c0f43e03401710505a0320490140903146440d05410020b204040c101c80300813402d4180c5202d18029640350b900c000d011904502c034401d010801458030490402045010590b031070040c0781c20450111303030300e48014240111980402088500009005024500136022a503400d40c3d9aa050156441140300681100000340010015810710710050000b0b00c00504020680387c942050413811041854410340e0982e4584a04004624030b09050001501c3c0030701d401c515190500000c80c000740c041e80701c1c00a00400ea080c1d2a08040818401c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 679622652 1250 679621402 679621441
    0x60c020105070f11011103090d060b01090806010605091302090f011206211e0f1101140d050f060328032a020906041b0c05100e010e0120030a05 63
    0x504440490301c3d0300780001c4448141c000b2601048001c5c8095046510000c151040200c0040003c0c41c211401e5036544060128030b04102d040c030441d440e0200742c1134010300006020304800e0b902c441d1110764a0042101c58501c0c100a809060f00c100000c2203107482d040c0480741c0c080c800f8200702580007000800c0300000c1c80207620054001ca0303000464054030144000320404240a041c2d01c14030074050b50785108864440003001842e800e0800307120f900150320030b02a05c0130a48141041880404601c0072190301d40d00502980700c041d9900d004010010040100460308540c00340d0042034207000c804a4100081c50800740c426051500164003002c043c0310300600e0000d00162840750b0440040203c0e050080c0c007020008912450490001a40d5170134540708042440c0c060140107110001d03440810f43d42c00c00d0582090f81c25024022198006401a0103038008540c0040d00004007400401c160900b150051900725480e480c3c140c641c1e58001300280d007035a03002040c8000008007501c8418130718500d09003121 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 679623902 1250 679622652 679622663
    0xa0815190605040801060b0309150a0213030f0c0e0105031207080903070b1c0203060901090f0f05090706201c05041203050712030501080706030915020408010902031204060801060c02010507 83
    0x51001c01c1956014024000700c414400080c001c1945614203c4105d000c2100ca6800d01d40c041191210315107a00b43c2219049003103200700616041c4038a000e15441e0125800c2980c0a1500c0d032615010406402c104030b0003005540041c02165040c6030000c0d8890803918940303c620070002c1118000e1050000484c2c1400800800310303141280d950341501c0d403032b4008010300507151301f00980b00741441c900c80c02100d00c10f0500a00310100c0f42e0802e101c1070000c10020a031050210760b110008050071096210f0b1b00e00401d8104000c1114600d0f00c00300909130300c400060703440003480d8404c4400c22180e00050340c08a00401188107500584944021507c138081c0c0c0e40b012840c075000080c03042c14140c1082c000e0074258064001960401190401602940d00a10440c011a840180100052803190303020761070141c811185078032803907204a80c0c0c400741c1c7c200390048038240e503584130703250210301e0200902125140120085810300c3e00d00180038007038683c14030510091020001545085a00c80d01c02c0725030842c0d014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 679625152 1250 679623902 679623949
    0x11030c0c030c01051008100c0c03031e05010e09010f0b0607020609180a1d160312020a020604030813060807020a062a030605040612020609300f120a0815 67
    0x440c031458000c0d0352080e09021f02032982641025006806540709405541d11542c44100d0503603800c50040000c3c1f80392242880c0034440240708101e06000d414002c2191b0104c6440ca41000d943c11742c00c5501c101c4e0049041460031b0408950740d124030003650045c1e5012108152109071510100c0e0b000201500c1c0c185288286c80100442d003041580b14940c01880220341d40c0c1034262240540c1d64031030b041441104203400c0884208001a0328030380c46442c001c0c19105986001542c0c0e40420402d4103d40c00868400c000400c12a0010f43ca00240d1401444540ba050200b82011100651101d0407090081c0020307480d11020002400d200d0604400f8460903025040105400c0800400500b00303800ba2070311590912000003013036080b050241404940091850303250244210420900004d101004150f034500c0b1000c05020008507130b03e15070016100c10240030180c6440000f81d0070324000295509a0110522403000c529511000e015400002458200f4400b40c5c1e402c0015000103802e0f40c9606203080b071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 679626402 1250 679625152 679625161
    0x92003010909030f03050708043e1e18070212030a0b04140105060a05030a060f12110a0e060409020f09090c0102061614070f060c080402120111030c0c030c0105 70
    0x3a9108400c0b0b41e0195641310005840404114203840341505d8910009498202080214034200009a10b100708045003d900800c3c5030354054508002004920790708034054550100740c1000e40f000f1114190010701c0c1c5028004820008903107141d03440004120380da8500004080302d0003081095100182440b2464592800c00350450180c0b402281c03030782c0960304120b8be420103c05aa2a004c0c1a907500070040ea003030410b550812a190340004011451807038446000003075441c5c0002e504800f400305601e403d11403072904d040103842c080034140001d010311502141000300c2a40f5005680e040f0703808403000b0401705090f00010324804600c2c844030794081a19800d009e03032510009121042c105082e000e8486070355810030305402c04c0c01c0804510000c1101428010380822100d0000e101c4e85100c0c10610000c0000740e1980b90480d0424401d20000c00d087e481400107614114140403a6440e003d03009120411040300a242c1c2030001800e1b40c1c60749900841c00303896a00302401075405807040c0300b008102502d007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 679627652 1250 679626402 679626419
    0x1060f0b0d2705240c2a032a0c01110c0a080d0908011404020d151a040e010b0a060513030204020c06070e1009050d02060d0509010903030e010b090109200301 69
    0x6186400300c0c2c40b445071550001c1000c6410340141562021040700007840d41c1d842140c80b00c5c030b60102d00f0400c01411035844402014501d445003954012038600255100c0481c500d14070038003c0c00c050b408a146000c9068040d02c0b0000180c4a4580c01003071800100340c3d9614043d052801080d0a20989e11401000010940b0f2100003104a0071a00307517655500002d40e901d0505080b01d107000d005081201c2034600240140c14100e1440800c0b510465210740e65040000a4004845151084000819060310300a1092905014201648007000004c006200c603140000c1c4019000303200319002e120020882c0814408400c802c50010354024006542d5030400d00e09903503c42800700e07800800308540d00041e00e02030030190400710000c03840352900c2458070305110420281889c8040101e82c032410401451281c002c0398000c49015000ea030001040205a03131034041d090302c5580079222026803600303030410034580d200705909044840d403030000075410340141c1c074450b4490b5152000a00803040003000241100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 679628902 1250 679627652 679627721
    0xb0409031d010f08011703120c0c0111040602100b0406051905040f15060e030a0f0b09071502030f030603010f1509061202010e1207052101060801060f0b0d 68
    0x10490040310603030848040041d51002001410f010000740301c0304c01406038902d000d4034041441c0c101c1c1c00300d07070138111400c40185000f607044882001502c004985180803402c2401541c0c0040f0390500000e04190070904000c2d40c550800198a0403151242076007445070f159a40080054003018110713050100d22583d5240d02200984502801070b80340603c4d180502c40075224036030701101e02200c0c0760020743c40c1403011036101140381903155041c0224007010340000c40c5904030a008512800c80e80d0010b02e403450076181084c00d00d0340001114409101110b100c0c0d03501204898030342000d603555640329110640801d006040c07044802241c64030741141d5000e100c003c40b02c40000c4500c4103a0500146e602d0319141e4007080c01000f0028082480750404501500d05809034540c0700c03181a040b165416540c41c001201c110158000494642c441503074110a0340080c003981001c1c0400030001d1104915000344000c1084440c45160300220b000302d40010b440070700750058942c0040c080028196810001603101051 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 679630152 1250 679628902 679628927
    0x31503080d020a111c0c051612060b030606031c090305030c06100b0708090d02010e0a090f180f0b060303040b030109052212080a0e0f0a021207030f02130b040903 71
    0x500c81c0b01301c100380000300242414016594001c04042c0c81d4000c401594980c1c03200a0440c1d80c0c0c045d030113014420748030502403100202155100350541032901d040407411035090b485c2080c041c0e00944200081070303c0015a03601024454003c41180c4070030098211185982742e00010001d010000e03e11050200000b038840c0604081c0010036002c55031961290220f1245080040c44444140500f00036403038401e44025156006060140000d4061030001b42c0c0429a500a1075803160b540c00305542d010020b01c243d0800c10740d100c5511042c04080c2c0c40c1c100c02c0280c4414003c101c00511000240e01c0c2e1420f10903600241003008009440396110502280544001c490120400c5c0003c1e030408840031010001480040c1c011103020f068a012000440f08448003d26001008be151803c10300c0010080143c590100c25402c045c0882205030f00c10401180344071034401e0f070700c0e9004c09070034008920150000700041d64103c0301c0e80214546ca007141000b40c120f00d0742c05903110b1702c0c005002003455003109185018 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 679631402 1250 679630152 679630157
    0x5040504060b0316080703150e030a0c0b15090f130f03031e2a0306050d0c170d0f050a1704050a0b0c0f07030e060903010203070c0c05030d05030601031503080d020a 72
    0x8604c90b00e032030301601d424640b140c82c007558446a010404a414410444440d8030346a03400301d0080486030f6000d2550340f050740d1040c005030902a0940a0081ca005681e0700081d0b0040410b19100c1c5200000704104c1340641614240a0000c0104406494070091b081011350310028000c0140aa810701030006d211501c100c100540040d0314140c407a0802c1e205d46001070301c10901c880d05151000503c030f0121081c5203500307800d06a89400118565542c003410b19200e92040020f6100a801c20003049511600780032803101c15400411500c203000c4d0003401d41d43e81c0e2070325407405540302d10300c2a0b0b003115080101c5100da4810001e550a200501402203210400c0c94094080800b5940b640c85008070544598042c0d07001c10301060021800181c0300364607000d10380c003000b44220b0414410340b00080c00c99006954810215111404050410104480c1d040003000210040c1c00c20302d00c8500040e04510000f400981019510491345100d070b648800714a016641040c201c68607485124801802075114440c007402 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 679632652 1250 679631402 679631413
    0xc0105160f05060403032409050403020a0212101b0509061c1a010e0901360c18090608033a0c1107030f0303151a0918131b05040504060b03 61
    0x480300d07001c0541c07840714400c80c07c4c00145001c4880780102005002101103001d2510017a0240e0340308070085030302c0780080300030f4004c0d4031175440c1327500440d01c1f8220f60040050484114450a64011003961900c034401d6a40307aa855000309a0192001107121880c80c0051829521081e00c03010b01200a000c035000381c03a0f54214600b0341c000c008c404207092080d01c040c00c00d92007221604d100701c0301201d0701a4000b01e043c5034405040c8104802035403012401640010340c44141043c4540c503c0003130700e00501c0482010010603007011407031500c03403003880c85081080440c81c00c3c4020089090074006482d2148402c10546944c0031030b900740140809040c0c01c000500c0308140c1c020701b9480840c118003282d50000702d1071501d00c440c0d83c0c03d80c05441841c002c00019400c284e0005456403080c103110349490703150307050141e848040e01d040149003840c4203d40c81394100301d0020040c1265881c0d200e42ca06a40000c64081b0b890b2464441220f10420342d04142d80250a04090000700491500a1045018114160749 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 679633902 1250 679632652 679632671
    0x207060b060c210c100c0e01090b0315130c0201060302010306150c0f030207031b0f06031b1815030f050f0c12060f060a020d031d0c0105160f0506040303 67
    0x1d54001c512052500d500145101c00b609072082c20103010300441c18200508025400c44a2820500a01c08038040346031503030199a4415072004000001c000242405503070742c0c1c100010181c150200810542000485042c0071000340e8035041e039100d8403034003100c0034050924484802406008a444200c0c0840d00b4420f010402e0140c80900d60f0700b03125540d85241500c030707544d02c40804002ca04070081c0d00758018460081301080c001032111a040724011103800300e40d4a01846030b02c914807140c0c0b055041500c5c068008120004014591983d070b829460901c880b18180070421980038100d43c07210041ea0b18020a034010b0340e4054000502d20210350f14200100d594000042006140495207051184010071521007000740c3c0c0251150070400140c00b880c0f801c4095804140e140d03100f1003200000d6400200305048076545801780103214619522116101904a10303c81e584140c0040141c0c140720740030468102e1810005440c01b40ca541107201007600e00e0090408580322003081d101039000a04004009 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 679635152 1250 679633902 679633909
    0x80c0301092109260c0f0d0f06020c0f030a120506150304050111181e010203090d150c0305060301150302060d0c12181b0b030606070f050a20031507031113090207060b 73
    0x9296180d024000300703081f814035501c800c0c0a10101608a03078040d800e1001600064081141007003104284000f140d075000c01d0400500b05202032090320007528240002c10010352200b038040092402d0000126440e500c135403070300074090304a041012000140200b64030100310841c12100c02c050742c2c20f4404c68403072428210661442e00c4015000b40c00b59200f00310401481c10048992420f4a009600c000c0c4009039403181201507402003015000029112418080d0300c0c5001e104a00840c04003041d8039070954a164041101c83c003548005c003140d15a07510081e82020f01407a170329902c800070301e941003116220249070f0480c010a40a030641c3c0811321420140a040714000036041501d00c0721100c2815a41d801c001c004050b4082201100c0d0b00d2281d52001000400801006034640d20030b81d4404810f60152041c55040d0003038911042c840d500c05440d01c6028414845c065030065060324002c00c0405400380b00c40440e02c45c3c2800e0a0310000171500c00a40c002469021b03202e581d116031024440440e102080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 679636402 1250 679635152 679635169
    0x3010f15050102151501110d020303071409010e12071a0d05011e050f010903060c11010b06160f0501060b040f061202040302030d0f1b050601080c0301092109260c 71
    0x216504003501d040803d8a07a4603105d444109400c0c145004004050b0703104074181020789030699000907920100038050801e801c030326110b00281e10700600508040036080001c002d105c402c12414042c3c000c568141c0051402070000d82c0290410305403d102078080c0c0204480243c1c00f0801c41c803407091400c000464543c180b4100e640c0700c00150178241400b10f040508110a0080d902000f505000e05c0650020024005014245c00c0c80641d894004480d01d00f81441804e40b807113040307020700c80c1004005081c224008a407425038059017014540e10201d03501c1c40c1132401811590051b413800700010071300203511407090301c0c0501580c5159850300540100085484240e004a001c02581500010b6075000c2e42c1d8481c070a611810040c6282003000c202008a40486403200142d054485801ca040140701000041140d46404c2302d0039802080784160a03103400810020300a4800084182d04495801440c41040c4c0c640181181e40080e0700038048074005070040101c04c00e0119164000c40d0025840c2c0c0c905000c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 679637652 1250 679636402 679636423
    0x31207030e06010303050a0c12110c032a130912030b01021506010c03090b0301080703051c050f0d0603051603120e28030503040e011a0c07090504080903010f15050102 73
    0xb041264210707030301580c031074202e01c091200308255143c8141c081a4010340e44510200c1d5502c81c0c000012410740450700303095041110a000e540198008800c40384000840c1c02d030b03418146944c81206902c030f40054200030600b0000601c45080800c02c400340710000c20078a07000d80940e00c040050440c0003006a848040103000032101a26000006842d9409100550300192080c90000c6d001500c5244a03650342d042038110b6480c03640440b405004000080102c8a11700301c0564421814900c1020010301a21501c41440c65941000c031b840410a0f030315411400203990700c20191100700d210f0004014034130025200940300c90210b0303010503501c030b801600307080096170014003247d040005041c002480000403988400d1181100200080461020b201800142c181103242103015450107203601040d400c0c2c02000ca550303250800441e407038031800180c050b0484d58054000324141e1b5550900316083d0140c2c1c480c454065081114001047d08030b035105030301d16428880c0c008699610740c0c0c01260348441011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 679638902 1250 679637652 679637681
    0x1312080405010c0501140f1605040506090609180708060a060503040b060f030a29010b030c16060623150703020c0409050a200906040908070b1005060c03120703 70
    0x48240003a51040e441c1c0442c0c03074084d01c000f00305000d58120407090b8120460f000142e081c101d20901000100c00c510b03a02c20318803649009410f00342000700142c0c4501c640010310344201000100b000c0e00c2d440310a1854141003245c0081c5002c2e141c85a80540243300441300944100125080491390034044c1c01682d000381c3e00440e26602542d100d2051001c0c1c0441a0040c1c2d0b4940b140100040c000f4114800f11a2002c034010080c0c1007000129004600c4010180c0100007640720074030410008514060070b40304802d400c3d0494490106290620b80b00800366904040c0203007504019a036150408603608842c020016540c160f0b9840c4a024545d10364090000c0050050300a2240c400c02d6140981142801310301500a40c1d00c0c8046503078841004154071a0501002c9444000407842d81c40c0a80006030320035800e0b01d05200442c190750303038500684540d0700c0c002c0c449240c40021401e107000522141c0c015000192049036260071a202055a0b138002c500741e0042499480c0c000340e0744038443e008103e00100884c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 679640152 1250 679638902 679638907
    0x30f041106030112060e120c030c0f06040302100c030b100e0310020315222306090c1b070305010606091809020d24020d0c020f12030a0c0504080d05131208 68
    0x503900c2170040c1903020088000c074840d0707401c3da440c101d101e100100480f5040d00300442d40c501c00e03c801c490626136075900d44200c2e80c010000f00404a034000c5510116601d20601c001401c40c0300f054240e000b401c800b14400e40203e90100d125074041e400c4450aa03425104400300c0307144a44c07003481182a444200c3d540101d8030100444201b5504005081802140c181101d440001d1034480070141210301c03840091019203040c07038003220a807014002a641268080e2103e0345e00f17140010406d07050740304031150600200012030b03540c0b8031544103003e560b020350303400002484203954424005200d03038941e008624a600841c840e03c0542030040c42040b130200d502510007000c0e03481c1e903220400c44640c00c915030b070014240075039000c0b01c82c1210701c010300b1018500d140004641401040091800c840d0044018a551240549078040802041643d9204902140c0800c050b54044000c5507a400f4540c020f0105224107510703841c0d0342c1d800c80040c0440380c4c1700700780340903640365075500e00301800c012040041d0025108 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 679641402 1250 679640152 679640189
    0x901022b1a010f0302160b0f04021201020a020a0f0501140708010f0605130501030c09031415070c020906090705090d060e160b0d02070c05120c0f060a17040f08030f0411060301 77
    0xf1750003a0026112145e031031001c5c191152515008079030b0440c1c0c84e001c602d02190810085240200d101b003440340c07411000314103040c1800c4020307660b9400030f900900411b850840200411009400440c155905074900418030b0411203400760211100f0b02501c20401001400440c0040c03007481034401c1c1003800241010207a1509005400401482c4841030402032074031000300103d4603081c04499038040c00802054030b00a0b903401d000240c0c801a10110410014401003c056a01e4010503500080308440c2c02c4416154001d050f50306210b010700076030300900001403100030f02415a0054603402084c905860801c080028211241144c0e4007801c02c0d5082d0900220010071764640c05414240e00c00e0300d0080c1310300e4030303600085c509844040b601e21031940b0605c0440201d040c0700c1404003001c1020b070707507d40c2400c683c4071001d07200c04036444200c401101e884c00081c062006000790000c490780c210300d145e640c4e41449072011404010885040e14240e101002a02c0c150804600301d81c101d460368030003590f03c52803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 679642652 1250 679641402 679641407
    0x161e020f040222031a0f1e0702011e050609180706030f020906070521090a0e1510021b180109020304060603081c0b0d020f090901022b1a010f 62
    0x300900040340c1840c0001060f41607103a822410001d180640c0085042404a6500c10176075100107102401c0d0020080a12032880070803410915111001c071190324280d566044103d0050510030b030100c40106259008140c00015540980d0048174156400c0c90240d45010b10003858001c48441001d00b82d015840411400d4425408400ca4480050001d0b142031031900024005070411001034519070420b0820040b000d87d440c407408180c0c1c8103140101d05020001000400b441d44a1003000e081e510400d00150b04a90302407805a8400b80080034a00b06a10169000b955908040b00301c01c2a24500d101e140d006180c0300e4407415a80c1091080b02e40c0c10780c20001400b0281d000a0011140e0b01d032510800700028942c1c202038512880e486141c0b18179040c042c1010300651b0790070401a405541887c081c000540c42c0e1808120000380240d68041994071880070040c02840b031b459449141c0604401b0b0a204104000c1e5290305207041d9000c1801130b0b840202c034900e01005080b508038007084506032803008450 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 679643902 1250 679642652 679642657
    0x151c050c1e030a0b190602060a0c02071a16080301030c17071203050d05090c030714060a140c030d020301060807110705100c05011103010602010e1203040803060a0308161e020f0402 79
    0x8120310f0000c070300d80c1c0002c804038012595011100e840d6440a502c14000240d040106540c05400c5003014820100c0d4854065220f11403406603014684104032010b8224014400b2a000c0e41781c04c02030071101c84c90605000600303801c2800100e0300b01c3d00b9101c001030303501c49280da004407842040003e005508d00d0701c40811088840d1440480c2481414041c85440c00410f11406100e19203034405000e00f2032500e800c05042c204a600411035045445101c2c90340c50f100e11301070740c8000c565418038a440c003490342400071450240f240120114403000a000902c0c41c2e064026504032003682d100e101c107a84800794150b5a15544c058106120390003440104428a003001302c014070180981171500d40f803112501c0316030070360311000c40245816500000400409a0911800a10f918608080c00000e02c482c000c9442a00c4007400152180e0300c0031002c142180e4829032100000c42d0f011001665038119100201403041c0010381c1a5a0490004030550b07485c031907441110402d07640200b426407013040b0842007200a4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 679645152 1250 679643902 679643911
    0xb0c0715020a0207080f07060c11010203040b0705011a060f0a03110c030406030e0c031501061101060509040605190501080a29071107140a0311151c050c1e03 69
    0xc59244444191030518070060441e0909640901007030340c1050303e041d01e040c40e5444071521070b0f4092202000582ea10140c02c6218039031100030f02ca40b2260300301c0107d02c0c60060307410005490000142010420038154421007140c0c100000c2c1c0240340c42010104180e90040f034811121501c400c0180d010024420780c03011804018140d0554140000c1c103032820b00e160000d810804c0030a0b9a0300303070060424801c109001411030103c00a00e000701c00c05040c0041400d040c1b2905003481702c8641101d42c20113003074010001a00b00a4005c0c007161a003800c0c03d502511043c0c4115140303034648074aa005420881c010030341614a400c000b496442d5155858803403000481e04c0002c02c4800045080c40b0385900070804a0083c02180d440d2102288210a50b07414042503500c072242d14004020041c3c56500d0344145401142c2e000780b01c6d031003210510707400701d042014004001c1c010190002000d541c2880c42e901c0c00180f40492001c10001036840d0904441148940004210310321000800e2000c07110001c002540e20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 679646402 1250 679645152 679645163
    0x15050306180a0603032d1407050102031005091b030105100e09070c230a0201110a0c0b0a030c11032a010e0109060b040911090a1d010903090806040b0c07 67
    0x9041c10300441e0450001a140140000c0d140c410401c10325501580582c1c50f00d030b40c40004001c07000c0d460b8000e854a505c0c8150394040c00101c2001e41c1d00740760040c05845200c0e4200000790342c0c0f86001450207110b04140e004980c440c1380c00d0008540c0001c010903070080081841c5a00d6407959081408000c24407042d141d03c0c8041001ca60f041e40c03d00d803680113016009824540f0381c4000041949000d003000c0c00300d0a800e02915480300d04500c5696800100d001c440380c3c0a0030310000d02c482c40d180c91420708101100140209035403000024540b114000100440203440d40c08025010700c0003000c807100b002003100b8026a6006001600001070032081484a610101044d00b4a90f0000503c20b420b580c2007030f030402c200f80d564000c81c105101071401882c0780c84008480401c20b540d0f0f44d81e101800031a845901030300401000d0000303031412006501054009400c1d40004a0645c1c41c800e5690103000b08c1d26040300010049100010078440008e021030007141d001e0b03080c0040d0b50b200000c3c454603030058001a180e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 679647652 1250 679646402 679646419
    0xa030c171f122009041e0311240109020c33010303050406090510081303030e01090f15110a2106090203100b0a0e0603092107030206090715050306 64
    0x790b8240034012148070503c5240c1d24040708014000e08052070800044450040003000d003008001000c685003c1095480e002c40d001c88880c0ca4101111250984011101a0722030309801940699840403a12548a089090a455a0380b60b4499109074002e00c0000d200035440f00c24801c070303c1007902200381d0f4444c00f00c0381d0508080240f4101030b1a404400e038425004208005414084c5981c0540030764090070064850000b2000040b4004142d058005c10700f600041100f03a0039010140f2a400001c3d1480c00c00000748004442070801044400b903e0404440301c01080041044107141303401010130300d01c043d000880c28100441c03800c2d50f02c00d02041e9994891030304100c82803024006840707001d0151001000058403880c0c50000c0303450084458000346080311b800e100313407281c0380e9100d00250340599041c2c42013512901c0b984502c5142a42c481042c0c550b1052011016490003401c0f40a855028040d43c00c4401e1600c03902002071300d4100c035001b9a5100c060700700100c400d09000710000c603000400580082d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 679648902 1250 679647652 679647659
    0x1110702040b180423030a0f050d0f0c09080114070f1808060f0105040e21070c0509090609160302090601030509030c0607020c030111090a050405061201110a030c171f 73
    0x3e5884801c0303e04036038141d6174680c030030101001008a01100c4606000943c80c040c1c1e0b8079005001c60b55010008070800c0310011308008e43c1a07880d0030080900c45448414001d80940000241c1103040900030207588d0361034034902c1207580c4001d0300c2c482c2c024842600c43c2c00b40b440740303540211181d0b1582400c03d60b0024803504001f9450800300310f614810070301410701100c5035041034100b0095960841d4507010952003005d0000190701c9141d0b104400c0b9400c0006203603140342c18540281c02000700d5000582c0100c41504001001c07502041d0f09202c1d00382030f0240c480c8006d82c5462600325240c0360002942000f21200011481e5010340d000a801c106801d084030704101f00c04040c2c1d45013840841c0c07600f0040c0c1100c1c3c94801e0300d05003400fa0010b40703690358601500300506600441c01c02d010318420b00c0d20075503c6d9000b00d03605441300e14524410030004c01c000e10040500ca4050f04140d80844883c1c40002d01c0d00110110080c171948445e002858400364280c03164584030740c900d4954110f8400780e01016840f04000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 679650152 1250 679648902 679648939
    0x4020d02060705070326070309290f1201080d0206010e070527090907080c1507050d0306080705040501080a1104110703021c0203160807150f090c0801110702040b 71
    0x440250300c662103075001003d11055078002804003c2c0344204c844410b000c1c1400280e0062000000d41e000702d0399a21072b040008400a40c0c00c900304840760160fa200194225007010510b00505040170401340000b400e0744c0e1030030306c29580c0d43c1c065a00c50040c2c201000500c03040c6000320030290484014030340783e400c2c9100707041410504020b11100c00000e01041e60b800400f410200c0d83e1a034010520406414858907001019849500382c20400e0b00c50021206a450f55075003080139101110b4100302102c1c00c0c0c0464260107801040c950003584a2842011400038140ca01400b40d5810b803402407010300b20300701c482e90b2076039a0381d66014201d5600c1074aa5400c05c61509202c00904805030003075000304000000700310708018042a407400282150010007806a424926522035008681d0061496581c2c00090a244010041420fa060041400c01c0c5101035052003d800503068180074a62103001155030705566409c0703030701e5030aa04a500105120100252500d0b0740242c3c10180090311400003d10b14032140c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 679651402 1250 679650152 679650163
    0x120c05090703020904050604020406091206060803031f080303150603100306020d090201030f0507020a0807060b03011505011d090c09040b10030c080903090a0b0a020c1207081002030f04020d02060705 87
    0x1001c00180e40407076444010314040c01388940110080e01c04610380f5040210040c181c017524090394420110354078941c020000d41c1c0d40f000f4000c10b41141540d88038140040540380241e40342d445503030750f03d4044030040b07864640481124010b0036180000c020b4020130006101c456000184110128640b954000011403034034002030000d503070036070300c0000c00484505c00503040b07440b9400c40c40420345c508000c1014041e000541503030b115411880068980751b00f46420307070140c0320041d0015095400d10040f02040c000c82c16155059501c241c0b241240d00c545ca02c1c03c044613940504600380d0040308032001c51000303400840281440c4a002c0c0c0086102102c6c040450b00010180390301e4400243e44069803002d81e41e00ca80310380d8000700e11070081e51030600150005000c114950182440031a80040c0301d400d01d6008208582c0d8801025280d00141c1881c0d042a40d101c01b910300c130b540c0c62401190303603600100129100302c034820084485503950b140c40c0c5809000142c003e402c0100c3e0081800c11081c000300b1400c015 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 679652652 1250 679651402 679651411
    0xd020d030807090f030218040f05070e0106140c060a0e010603050a0f0b01154b0305100321020102130906061713020d02010e150c0f0f07120c0509 64
    0x22145000c0c20401d400410a000c03680c003034139004c03080e1141800143d803900b841d0030051054956050f05520b560070581340400d007452004255120f00c80300011041c210000140c102c49650f21100c3c18108003050051842c45003a0384040c0582042e0002211101590f1048114406100001640fa038899980919011001909480418040c003452007044038058040d030151003405038000f1480c10425002d0415010815200315984484001d03441c19130448074491400060201024124902c0b029050b25220a48428400103400c1c000014044030140f9444011a54040020fa030b00500107800412010320780003410f01155020410211071035880d01000b400b4250021300064041c0c6003090241c0b51244104410800385100020420b2501304014205000c03a01506c20030008032407440106c40702d03400c2501072544038452044007000d10400b0006003140b806200b04640010a00ba044113075542c4018400300ba40381c0c0400710602c0000100f01c2190402d600c258800003410f074542d00001c007842c00446 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 679653902 1250 679652652 679652657
    0x20c03120103060b03070b0703140909040b0a140c090d2604080106060c1a3c010e1315061a0c1006151103090916020f060c090d020d020d03 61
    0x1030040c01440f490b03114400704500101c00514000d841c0c14843c22181c0245038000d0140309201490390180c0c8111000c5603803852004181d482603291a16100210201c02c0c2d5100f08510b180904d03144050081c02011402030314241c24981c14959100108501210311030001c8070b42c0501c03591841d1684441e032840144050032032880c0c0c0d0303c9a0819100c103084800745d500c0b540400ca0058907034404070300c0000c483c90b5460001403000c013240e91062800728100b410103242038180004402440141d03460250010702c8107030000042c414603641c0307800021441106460407d8040344c9455100c0000303000700410092441040701c0410300e190364400a18a291421894035000c1c41c00044040301c0040500010420f01c00741c110420183e810400a0589500d0010004040c0030b20408904032642080007510051403004192000c94a4001c03c8001070401c140303441c2c00944240c08001558040214580c2e129111510102c1d0604540104100e4084404c96050343c1081e08800042c02680300c082064481034001d8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 679655152 1250 679653902 679653937
    0x1c020d0c020a02120615010f030b100905040c080c0d02070c03141b01051306030506010903020901090b040b01023409140907050105181e030607230702091801020c03 72
    0x1e0050000c054a800c2e00c0369130a030489401c001c0f00003505064200107690030710305001a0403520b42d080d402044c14242403580949410040b0a040c3d6012218005480c01543d00303002c1194801c400b6a20820203480611b1788510030b000002401801d40d01501e80070380140450360000e90703a034071165000f81e0111944031090700900f4581e00c01c50162041c401e5000020300c0d006103004c1d0001311851100b0a5800b0b50b60400d0344500104201ea84030f00c2d0848041c54008100e40042d5035074400c2d03000203001c3c0300c5925000d80c0c00c2011000c0190700224940100c41d0302c011400400c41c031000c15007440c5007000e010300080001d1110010404908602c2001c0718084080c4c0c50041c00c1c01c0885a13079103461082d40c4464100b000c1080441240d101a18003040c05003815202c0039403140aa00080565283c0c03442d075190035210b04401c1108055001d515902a8581100d0011044c601c040048041d8800c4242c081d410661200115001c0424118050b184902d18000103082041c040b0720103042d68443d403000c401e03c0301c04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 679656402 1250 679655152 679655173
    0xb4c030812040812070f1d03030901110f030a11010606050418181202030d06080706051b0307060908031608060d021212031608101a0a0c1a0114030105010b1c020d0c02 73
    0x3280c0c0047c001d43e80120300d89000c0c910000080d0703403440380503140c03410403091a2603460f031003508001080550920030203407920350030100d500030030030086031403202080c0d800c00c240001c000d80500708030303030030703604900a1501090014860040541410565030071183c20039912180812004120307480d9251159024691ba507400c000043e0945500c2d801040c815048100c0c00c020094101c41180c0d481920004d0510900ba49000c2084c11070050307000150410b41405020303810070400d50011486010b03a0198800c0010b5060742c111408041100c0d4690040f010719201405880c01c0320841600902c4401210315103181c4001b40440340c0c000741c1700007070a6001c1010360400160401c8071568401449042524a146080706d11070a19608100420500c000040c01c440010302c81e1a0f0200603642040100c1c107034100f645c0c480c841c4010244110909240302c0c1088110625040c020b0354129409921118280b4001c004883c04607200130007075551b81c503820002c0d03420b202018001c0008500c0c240c0c010f400400390 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 679657652 1250 679656402 679656407
    0x4020d0516090e060a14071b020307080a0302070f060507080702061b0d030c031404020f0607060504080d0605030c030c041104170a03020d0206010e01030b4c030812040812070f 77
    0x1c01750003880c03060b0800944400c40c05160040c264401040c0c0b9003c0c101f035203095440440400301203c06901405000008503031780000182d011100b030300c00da08640b0a2581c41004036a0021503020701c1002803020410b038004140780d030010745565030008021502d0700440381c902c19240c2030103e070100070310703001500740e40c041c613404d8401c210700501c0d1400d0a220600c00703149808027101c0c0c0180000e100740c080132031184403601d034201510405644000c0c1004541400c2c28041c65540000707201c409064185400031074035040105105004480203030040100300f00c01e408010207024000303920b090032402840001740300c0d02241102d031075111a000152440f03d05909000703040029143c0100300f994001d10041001c0102140c02c90304481d0011104092900d070720845801d990444201c480c5940c084001c201d14143c26140000421721050301031764903043d41c0d8043c40d070101040d031102900c0003509100c89240a5900c41050340d01522800403645030900304c48040c0140c9000382d590300f0008881c5401d0021440c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 679658902 1250 679657652 679657663
    0x230304080f04360221040807020d0804031b180c121d0c0f0a030f1e06050f07020d050901080402131b080f010f14040b030d05070201090f060804020d0516090e 69
    0x2083c48200f0740c90a603e24003003810780c564a10804c10350440c4400020240514441504c0b4000e1f80105007508103015800d180c5640e8000340400e8501c80d0240c5030380443c10244002c8203003240d41c018441e080700b8403001c1c204030042c0320b180d03501c005000ca03407842100da420306449030203012030b04204001036050b0210506442e01c81455040e60050b810400c0754001691011200300449a0003041d44e41d007600a40390181c000c400008010440851084034001081804d40006103d000c1303900440005580314034080341e40b036104181e00d0011034000c004a4400d5407064110300c1d030290015100303103400c1b1114610401220a0304411100d60050000110307034080e401405c440d0494050303041c0480550422080d0880c0640c1031040c614118112001110700703880ea60402810060b00400b038580c541010000540f1503803008604a0000d141000c000c034143d000c408594003521383c0d0341d44000041d0f45a60070301c603169103440c0080c0e480703100ea2030318a4101c050000e204005015280000704056048144251510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 679660152 1250 679658902 679658999
    0x3061a0c060114030a150204030f0b07030c0f08010512071503021b0102040501020606060307170c0405030c0301051012080705030f0702010e090708070e0628230304080f04 75
    0x450385901d020895079002402c050b0046e0000e042d408801000244000248a240d00062002e05d20110190074046949030381403250322152024008084014402c5913500403000c20754010480520051103603040000d14030101510802c21a240f10307440350b035141801c4442031900c40c0040c0c0c0000780f01d0081c40420b034011094010300b200a50a160600e00040d460b0600180114052440400066002c0e4482c60348200500601304214407182840070780e010003980f040c01744a0082c484c01d5520407481c01d0511805205215504c10390101608010700c1c200b1801600c0b4094800d40c006001900104005000914480740800c81642e030720fa00c50300c0054185c6055903003c0348078104800810800070741003440c2c00c0d4002d0851422000641618000614a00402d2080708200d0340c101d8540600140040090390309a10700c0c0c50f40c03110200440c2509e00e002c0c81031f464074003031140c0500c0410b000075a11070203014085032801300d4900309921100414181c40c0f40701c00703d1003240c030024280b0400703914008410307010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 679661402 1250 679660152 679660169
    0x506040c0219061802041e180b01050904050a0c0e011d01140f030f16030b1602031e04090c050a08090c01020c0609030111072a1505030703061a0c0601 66
    0xc0101402c202d10b40b501010314041d20264a0b4411804a141d160103500d112070340c014401c105500f944d0006801c1392004034a0040d18074039002c84650890b24001007114159440141d02d10503a0800062045004c0041e01c00c036894840c40d1184000680211348180c00386c150554550703ca0741c50008039141882d1141d01c0c88403546c444000500c942c41c031102c00102d00ea1030540b100354180701c1c14400f0900e000503207031064406028a0040085001000d407042080b81d0140050b1000f070b40390810030103c0b00e04a984900050f034810400c0e0000d1041001081c010b814a101002d8101a61402c4d100c0c10354002010300000104001200064940c01043e515000000e40c0b0050002640c404000f035511151a0b131924400c8070003280080540e0307025017050000445501c1c4080c5c2700c900900e08010121070000c4003221480d00c0c580c560052030842d10b0888103e03000c00042a09143c103118041c5d481c0d13400540301004054644101103503407405003a11103004d40340240301e503039241c601c80c03281410500d068014021 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 679662652 1250 679661402 679661413
    0x70801050105070206190e040507031509061d0705071e05100905060c0904020c0f030a2318030307121d0306270f0d0309171309020a05090303030a0506040c02 69
    0x9600d42c0b00544a032811044050b41c074400c41c04030142e0702c7d00885ca40704c0f03034440d05100802508561540007280e024130410803240759580c59003107003800d9549a000d030000c900c0e000448001d02c4070303410343c0e150b400c500e40c0c0c1052441c0c80c04030b032203030200041011814107200103101e00c014108681041506180040d40710f042004c1c541740d503582034035000017500d080480341010580c521a542c4560458115500d40d208440c80e681c14076010076141c2e0002009030300803c040d46442110031014600011341c04c083c1a8283d845c141d022441001c0c0344e0600108142c240c801408500001031001032809071100b56526102d4808062004d0542c0c40760070710041c1e074029000007082c451a08003015070b02d0410902d00c0096000c0404030b10280d480d010400800f10301380d201355a08880c04a0b0940e000d40c590b18069003009075102002c1d00040024441d0100c030340d03585413208004020384041680503100c1900e45243c524640380b08000040d00d0354006580702c4480030381c0c40b814407586103803e105480d82041103001803c2d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 679663902 1250 679662652 679662667
    0x11506080f06031b210f120406080714070f110a08190f02190b090103110a05070609061107060b040e0109052808030702060f0a05160c11040212070801050105 69
    0xc1e202c0c4d20144803450b0148460700d404000ba96515240103130383c00d282280e4050001d0150f10f00c0c0e640c40300030f000456240100020206689101404c0703600f41c601584403150141c407801d004031005c1030301c0711100300005070074131040000811401462001c00e00070341071040350115181c100311044820b0360002d11550300181126007d1540c0a200702d580c5908003a410700690301c0c42c004103035400c05407016510480108013020032019042400307010300b41000e980030000e804400002c844240b06180c0c840c400304005029000010302582c02c00401e2512800010070201a1018030703888a0708241c0e02255400d84600640a25092600c2a20100d00d031100090100b4102900c3d69901c80b0001209000144505e240001c070f1a000200312000d20f075440394850f5505e10300440f0003911075030281c8065070002c030740201050301c0403114050307a401042c20308070244e4030480e515000d95021600f02c0301283c4142401d803800c06565038a1002c0c05a074025035107800780303a1410768002052268140c10140c107014042c003040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 679665152 1250 679663902 679663909
    0x430c062c180a0c03050c130b030a0f050106090321091502100219110102040e0f04060603080409020a030b030609070b1c0906061811030105042a030b0103230705090d05011506080f06 79
    0x40c100c070540000c6940d250ac07010414000340441118006120741441c2c000202c580c1e02114100c100d030b000e641140520140107a0200d0b60100c0c00c5070200004503c5202481034004003140f200f000744032801101c490a20307440e115020798100280450711559031140084400350440401000409002c000310728060074510a4184010042d01401000c0f1680300041c0400100390b2000b809181c200b540d440e20b40b40d50b0340c0e0b400e0203035104c003031041c1c006800c24030021950304002440d140a0000040544149410004010101d812003049075428110201140700c0d05136032403003410060340c000d42c0042541400d02e40b0719a410715000100c888401c0c41c000320000310346005025039066030340c1214003003006403214a43d03003a440d054104113560f103d515400410401e0300741e40103418500d400c1c1c0342444a1044415030f0b4403000c0084905c4038040c404c080000324281d128000400c44c3d08001007a0344410200d0340ca0700360840341441c21480c40160200030512842c0e8100c00e80a50010b5401d040d40c00751315100010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 679666402 1250 679665152 679665187
    0x504051b0703020a0803010803090f0907090911070b090703050d08010608191b08040b06030106030809090403090807120c1a430c062c180a0c03050c 65
    0x1016104802141500802d4801e1113400912a00329280f507880f0f5071100c06003600ca900243c40c1131f1281c2d2203503000980b40e042102550b8031070101600e45907a81858003100b44080c2c50800404900118200f0600001803840030140d40110307449001410345504518145203001007101401050040c81d800410080b035000f005681d00401d00c01c105d209440c1d1b2800001e026003e91441c1108000c204141054443ea00014031480740b03000d0f607221459a1540d000b85402c0700d00500010302800d030b0410504100741000040c041d000361003460078003a41592090b280782400c4154005000b0410106a80000e2019048448000d403104807611881000c80300041100340c803440040788040a01802c45041c120030041c050345000e0600c035500968008002c500920b280c800c42c000300c0360b026614101141c1c09200701580259140707213204e0111010725100c03c2414001d64068071503031080ca1100e0b80e4400c00f035030316080390086c2c141100115076241781070300203401d50310001c040c03002041043c04190804c6000209 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 679667652 1250 679666402 679666441
    0x61701061e0e150102010207120302180108060d080f04090203010b070506060f0906040e0106050316381305100305040b15061c06030812061e03030306060d14041b050405 74
    0xf18010300e048440d00507070290041a402600b0180354002030020960150020140c150130107141c0e002c0400401d0054400d50b00540e4241d03000581400054001084030740100300d03581d2400142818950b440034018240d91098015038054900460000104181000000d40010040b65042d4407034010340c0200710f0140d001441d82c0c3c072681e101c040f45100038500f984104080c3c007024055503082c900202d029464034000f03120701410080306502c5028896400b207800070072020001900480c14004258200450700002000c42c0740d50742d29000051203039901c8807204030425540c2c034049030b6444d19092600c1445401417400a40c0221292003c5482d51000b048506185000c003080842540301103502c0300400180d00014001319001601d20322010060802c544101c1c0119a80840c03004268580d15040341e400c0843d98059109101080f01ea240800107007041804c171990004449500340001c809550082c0c6060b034011907034202c01040026500400000b0b0301c0c0c1942e060007541022924280140600314 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 679668902 1250 679667652 679667671
    0x40815090606180601123201120f140105010906150503090607080928050c100c030f26090d0c0c05040504021206010f08010f09031b06061701061e0e 65
    0x400113560ba07000b090090110104000c2c104601110101321b404a500340140c0300d10182802c0c2100c25010076140003003070598114240a070f00149841c0c7e07904695114003941280c2c61a2406100c0352040f40905c0740b00d008000c948030218600d86040b040c201882105855141000410403c00200480000f0140d0304520245086003555440740f00c0d590030415070214103030303544845800480e5034001e100307245081c06c1d0050f410b03200314401d143e081000d900d114a00e441c0200c4c1c0547e000802190085088288129090410380010303101039003a80600141c40c03041000050317841d018004880020860a90100810705200da0b498450b80c032a500b00074401e208142c450342d250f10001707046450382d81e40b0503c82140c1d4401c0302d1207961101c41d09844081b260240d412658a400d8500c4101101ea00840c2d03146034040d281c0c02c1402c00801c180b00140f2500c0301d0151801900c4100010b26110740a00ca11140c4984a0000070180c4c00c0c50780780682007807601d092030078130107201d00c0c00d100126440700e000360000140d8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 679670152 1250 679668902 679668949
    0x103090203031b1914060a05041a191e0e010c0504050d1a070804060e150a0507030e030f0a030b120c010c1a0406060501020d022e090503040815090606 66
    0x10404078540002c14103550101950b4104800800403c0b44540319011580001c6d04c843d641c1c0c4640140031a0412100508909100c0e032240d19010020140140c10521604981c10001c14070307400001524070300030101207010b00c00d26400344013441c0780c0704600001960780020702000c2501d01c001805801140940707071240540c0e060b004208400640c18114032000c1d1801e00040d442c0095001e40390300b80445058503640e0a04484440404010403180700700071280390000c000382c0701e41489800501c001801310b801d2698407056442e401200300040d00c1040c1d40e4490548e540d54204030010141c039641542d0134003c41c0945498104048081401c0100c02028a04115801c2d1942440014185c505610183e955074410a020503c51550010020ba030820303000ca4851948200f0105d9a0380594a039518081403c081001c1203003085492108000654500105420b03040d034603003d003981d0040d840510300707034003a000041040c061a256a81d00010b024040c0c965842c1c610040340600841c1200c80e502c89820 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 679671402 1250 679670152 679670197
    0xc060a11160e190c051921020415080c0d0c0504030812040b1e0103110a0f0e090601060c0302060c03190518010b040216020607020619020a02010e010309020303 70
    0x40006100e506000045039100c80d0742d9650b0250081c03002d8800d0b9508101c0070141e560b8082e4035010b06607006000d50f0ba0076140c10b11820900168098511a17003082002e9048007880c2d04490300000c2c80c800340e5050300180c3e51444d001c0c5c030511803007100c00f0391014010394508100d003c0f5604c20a03a40d110b41aa0b10205091100304411100e174416a00001d00591004c00c081c6000c1c0712900ca01482a0701c500e240394807030346540881642182c18078040c021405440e0006200050841c15078440c0682c016044815145d02c84101159601490304500c0b80140004c00b00300441300f0400c48140100600d0400c030b41c41401c2e6440080d03e40ca07004048031021040000458034055030b035141354000b003c2c0141c00300300d503052103000110381e20b810245c41d0210b9820184410711a180c64801c0f601c0b001724013481502d5018850703003400340701d41051005a81c00002442070900218003181c60040c48000c5501404000145100241910312504007560405240008000c016200041214041c072944000c40024000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 679672652 1250 679671402 679671437
    0x1050702010b09070314011a1b010f0506011b0f020a05030d0c0528141f0c08010f080703020f0402070b1f080106030b0621010606200312180309030d050a110c060a 71
    0xc1d2710303d4443c05030503289500710324920660101c04030141ca8038041c09107488080044614901b6003d0115503601882c00640002d100b010103600240d1000e000c015039039a582000a04225030300d07000c0742c041610720f6111402c2001c01e1151440c2e0602c44604c3c0c17041e0540300c2c2d2078485501d04e5190300074403414500c00e04142c0350b0010803c50300549600101c0c03042c0b00c10340d08503401c084c000208000380407940103070000c10f102e48a841d0a5080c2c540381c000905207186503400308010700518901c02600590308001100100d050289024803410140d40b92040c005040405043c101e0407a0380607460b280d2525500740000340c04040c020341c004030103d0f0040b001078540c00c400301c1b40740740303031100c01c41d2561802100058258100000c0e1030308064034200054208003209a5130b40b244600b548005508a10200240c0320001c0240c8400d80001407200300c0e410012020f01080c07410381e01e07281c040d021400224110b000103a1242070000e10405c03800282001007103920118069028801d08070080c0206503100500020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 679673902 1250 679672652 679672657
    0xf160309080f180a21031b05060f090102070510050903092d03010608060a020a050f04060c12020d090513021c0516081506030a0b0301050702010b09070314011a 70
    0x350004a601e41c2c0d1103078403003201059801041e034800601084141114585013000d00f0500700c0b110301482d800c1e8918103000441500e031403a003089091203881e1102c5c007080e45607914120140c5200d5030044c540742c1464800001d44505c000c041b013145a004001d41303000548003041100070421040c0c004a01502e48200050560060341e40403500001c1070740751078421584401380141510340c00403034504502c402100b03060a0f20740e1070182d8484c0e40d00490201d19050030320b9000b03068007091440c3c41ca003054006812520b0660140c0d20202c00514070b4040b02d414440c405c2c0700c400840c46c80d4002801d5a5503651405032082e043ca105642c803800c40041c0c1404161060b4046070000000c050080c00e0745032511106100425003643c00800807039908039000301d2640102c1d0700300e01602d0620100710340300c401e4608100003a0700062407092419100c41001da0755440034003c3c2c601030071960700041080480c0800388411200000c01c46420541004112401c41c0891001e00d0705440654158400c242f5500c9845078052 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 679675152 1250 679673902 679673921
    0x182f03010509011d0a02060f09040603020d0605040507060519081909061d0f030d09030207030204090510050622090816050607022407050c0703021e1203030f1603 71
    0x55080404018041030194414000c0003c81604298002c8a10151503507803460000007e40201c2e0410110300c2c112001c601400c000320001f800402d650340c1320342c0801d140d034402c0c07041118619203400600003080f10600c1024050031842c03405030b0400445150086508002d90b01c030200380720608000c640d00a0880b150540305160320f100c01e10602c0b40602d08840180088007000c445440003a1411030140350116100388840302d60001903041c190900310103170080180c81411000c2d8480c070342000006807518050345070301c00d002c0d0000d4100c181c003c145440030341d5002040144203003080c0c0d0040502e1070b5400c2507140883c0c0650340019160550f890076044074405d1007055464003052101781410410f000a52a100e11100d03803d07510884e001299504600d0500e65a0210b0100440c0028440602c00ea000d0071790000b41504030340301c042d030326000f04104800d20400c9103808451540380c12400d061003010384103220501e0b80211b107140340859041d030844030040e04152548440300401090b0034071a40101941 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 679676258 1106 679675152 679675159
    0x190e031803120417150a0f05060d051b0a090504080307170105030a02220e030a0e1c170d0f05151c03030e0304120f06182f 54
    0x907a55540502c14035442190702c0c036001121501403d034007a45d46c0c0c010029095102c4c0318200d0540f44010b150754041c6110125140c0018070000d4a009412071030f2070b01030788070096100080e10f40071055000c007130190f0502e403d02c03046c0100040110301580480d160300441ca80c40c00d5003030341ca401c42403103216450340000001101505040301c003100e00d03800311204401941d4108148200301e551680c91090580c1c0080344e2407041a4008101c01c065500884950410343d6880d0318112111783c810500402400c0c152051500200c228003d4502030001060b09110580030703410700c04001c102c111420404000200b0043c40d47c1e0400c07002c0d0040300342c003100c05182d00440a860a5000d0141025401050704c002c1100113034018504989008407031040c050241e01c906c5505010064508007103500030fa5104000110300060449a20900d041c02c40c080d9140045900c4e0030500b04091500340940d40 = true := by decide +kernel

theorem cover : BRFrame.Cov 679496402 679676258 := by
  have h0 := BRFrame.cov_init 679496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 679496402 ≤ n) (h2 : n < 679676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
