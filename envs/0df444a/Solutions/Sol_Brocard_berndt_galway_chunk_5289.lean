-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5289
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:22:31.279732+00:00
-- url     : https://prove2.me/submissions/36698e48-a3cc-47ac-8f33-53189b8a8007

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 951079136 ≤ n < 951258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 951080386 1250 951079136 951079139
    0x3091603060504120c2d1a190501080706080a0b040c05030601120e030912192f091609050307170f0f0d031e1505091302012c0604 57
    0x20300081805480543c0c81060105668660600400c41c14031500d4124201000103440c0001701c480c048241070020385080d1b1011031100010320000c0d032552219200342450701c21454044000340b0400900074001c0d0440f81418010040d100c1e001c101c84098a25a2800c008281e031100303031940250084803050351300300d031400b606a20398952007005103000780000d0365607c0031744041034090b209542c8061f40410b002d0300200072030740140c0760422181000007480c40a03201e6641405160000e6044000d0081c1e4131441e030982c03c0482c80c085810701d075540b0301030f843d9020041c503540e8001c50034180004002200c803100800908800341c0c000c040c0500148001012640510388841c03695400748808805c00d01240300e0001208043c82c0c000c11840f420010400c0104a11081c203039048024116041400c3d8030340040042004803180c4601840910900e40850840c00501c0c11043c410b0480d0024400403510008158000051b82d10840c00034a00716016a04001c0158040c130310221214003072410342d40184002030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 951081636 1250 951080386 951080393
    0x180c030609061e09030f052a1509010c142115060a031e060b16031e0f02070501050a090308030612010e06090f07121b0504020d0e0105150303090603091603 68
    0x3c2003511300e01c40d9445040d00350b400441135a6030f00400c2c12040341140f078450309a003510703200300000311042c00c4041181c4201c3c001c00c4a46070412004d40c2c20302c20994480c801c24034115006010903400c0720301098071903c0d10000036542c0d00503292040075500b80ca1111000302e00c89502e9203441e400100303c018800755a600d00484003074010f001c4220800b180740c038005c0c4146203100e03991044c00c0031101a520068517000080d8556050710440c1700f4100c0500481c543d4526600309240a00c000b1000c5544410f81d0200b00014003a16050050b0700503410400100000041282c4c00380c2d5200499031f015003060303100e880b0300000502c00c5803806016000c0e9881c05001e41c3c0300c14400100742d40903804902c25286600007584115031145450f00540006c141c004200d0000268080288442c210101400743c440070307113440c002820780e4410012400b0f4661180503208407454288100c07a0041e06080c50b0046000744075000c00c0c0c0b030307010740011103100c2d81011001584100040c40030b180441e00001d8034003031071740e264034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 951082886 1250 951081636 951081641
    0x9040f062c010b0903060403050a03180f0b18030f090a1a04180c0f0e010219030206100603090c0308090a0902191413170a020d0c09180c030609061e 65
    0x418980c0740d040c0000002a0b074082c401c12201c42c41c00140c007520745640c468406035015400010f441c005c143d52102c4410a2840d90900d11100b1445052400b03d82c3c00c0c0c9041c00801500c3c06007442d0035030b006a00e954003440c40000121003911662480480d100c403e5140000d80b401019801100180c0c0391502c4e5008001c501c8000304242c4e68005920340f0200070f44403661040740e40304455840850356280111840a00071001017600f041d05104071520140c07000605100c6296040341180560301202c00d1009000b80324444001070030840c80c08020308501034503030078000705e02844003410301000051242ea15071070344c0036400040e001043c2c2c00e66a40c80382210070041c0340a404454000604400c0c104804c00001d01d049400060003115042c031040d040000c00c03c00e4031001190407140380305050750f407001a220b40c012180074030301820b1b111201600d4407030001c0954581c0c0e5140c509101c400d0803a0b10028540403000c20503246c000c000002c04801134a1f10900501d18107104941040840c40c0101721172503647c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 951084136 1250 951082886 951082949
    0xc1c020702040608070f0306021b25060309080403022103070f0b0c03060108040204050901060909151103070c0803060118170d0509150702060f040f03050c0603040809040f06 76
    0xb030340c003003000c16036070750303c8a481e101c2c0b41c0566030b51003054102c10004160a80c010b40740140c0c2c8403100e804100c85000d600b070301e03040f840007100700d18402c16007409500c403840300240300042c201400c2c248aa0611991a04001d01c203030300000744981900210450f203012500c4110039026940c00803640c1d41c1c400341c28401000c40150104841290014002425074150389040e00c0c00340b401030716400b01740d031a1607080202030440144401d40f113660703c501c0061074080c14056090958002e00d803416a43c0403006138203040e030701e220b82c10825280c1c0030418006c07a242d0050602000941090600780c0340d8850034012074005074401840039001c40b90341070218503101200010300d0030009041c00c0741c1040001030b4040d1118058412030b50303070101d580181c0c402000400002021301a04c000c04140c600b1400d00c05480c4170303401980007001441d820610a204001c02040318140c14902107445504500d00f40d178402981d44a0720164030701898445104c4243c0c3e00160b084500500610700035180c03885895100c848414145 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 951085386 1250 951084136 951084139
    0x2091008070b180a060c050601090b101b080310030501050114030a080307020705101d032a010201090b04060212280b01051c0e0c0604120f020a0918030f1706090c1c020702 75
    0x5008c000500307010030b48940310300e4001c05003c0304040c121804050361606003d898a40d140701610000c14001107202c8029849600c501001484090450511900710740050300800007406d0b82c04034580941c0c1d00001d03085036869100380040d942e42d031012012420b11810b1390010b03070840300d0502c005200c2508404440f0101d6208000c1da65841c01100c20580e89100714540c085841121801d022201c204402c0341d81c00b0340c4411700010030030401c180c1c1c0b0082040001c64007914450b502058880b10366580d8850f01c3d0308110801c200c4c00c480790504e5041c285000034240301d8a00325030350f0a54142541d01403c140c0704100d114007001000e44e0380c0200804003528004002d02104c2c011003100e1503251034480b0649082d2103000f02403c100480c26a100005280c1d542001c0e82d000b81000d500080c841000e018080c1210410b0421500c0101b4601c0c0280491051040c1401800100c401e070a1600000c02005540030008407210051600c0b0f01201c000248200d02500e541030301032000c45807021301d10b5001400c2c210710 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 951086636 1250 951085386 951085393
    0x10806061815061b07140a05100e060a03180f12140d02090a0512031309020c0316020f0d03110c030604050d0e061303030c02091008070b180a060c05 65
    0xc01e4840c012244100326400848a111010301c41e40500b0600301030088850007085091406106101d02840c00e00d041d4080e1685042c104c42502036170410150881c020002517805082c1c00354000310107404101018200c034040c1001048080ba840c2c460f810600a040da240482d1040703000500300390401d01403400307023601d0b4401c802c805c0390062481140b0051181c1c01001070503040145460b9500040d40c408209640d100950036001301c0c495880c4080c076015050f80302c1c003e5035a2001d41300e00f8000114150f01001c11030740b05216000f03c4a40210485000001c4600c0031036010681c0d1001542e10400f40d07404540103500c0031119801c058010861102e84080c14088810b21405c1000f05580c07880e003120028401e0f0868024640c4031401040e0489030301c400207001c90700b0000740b440d0000c5800c1041d402900082c0c4042034003025030411a00a64000c09102c0c0400000d03800d0a5140365540100d1040003400100050109650039442d0300604205000030002d084055443c10004c01356242900c1c00d651501 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 951087886 1250 951086636 951086659
    0x50c030912040833070215060102030a0512101701020901110f15100503120d0b040b01230412110102060f04050705060c1c11010c02060c160807050601080606 69
    0x6240030b41c0d0445246400030a03025648190b07a0140c1210200c4080b40403a002c01c0d0702d407a460031010740912490300d84d4000e00c15030b0100050034124103000f800803819034008011440c2215405070440b81441640c03013038140281c0301c1041402c65800241e20908135003090300915207071840190018004520240c0c1c400d606524200ca282c1e8a5900c260400c0300c0c16480b41c005102100c10040900d0380c0030b5104204104c0c016524400300c1d04288943c1c844107102100045c4101c40c0000c20b20980c0e1180c44207a138200540080d190000e80440d0481d0350030030800d04514804141640304900322005402103401c070490a10355803400c28100d0840c8080c1c18054081d050001e526103080d0f0000034800d5400c03c009181091828051009070b030b01411421840c0c1c020020682409540118240c11240841d900d88401074880c120305803c440e440e44511045400000034040044454400e5654840040c110001901902d00e040e072070b42c0c4204500200940a640c0002517120700216042e4460031055a42c1610701 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 951089136 1250 951087886 951087913
    0x2061c050127050618250e01030c021507080c090310020310050d08040612020d050f1f030b150d0213050106030b060304080d1e090c03060e06010f0303180306050c0309 73
    0xf2601200c00710341020707001c01e00114401c3d5070300301541c01440040c45154117030110215100b130300720010300c201c020420f02d22001026581c584500c605051951015240d0368440c0d4050643e2100082c0000d8204170502000c01c0c4403840000031540c050000030200c0f41441c1d14189030784003075001100d40c50003101c10b907035002469041c55409810741a40c000a6246828208042981c901001843d4002c0541e424003240204107194031031140501c1e484000d1890030b1805464441c444c1c80f0010700314085240d1328008000050f40c24003210303040740d00290340b00e40d1034600c2c03400b0a181c6805000040e50101e41101014010320296003c81d060346c89503030b0b05206244119040c0141032006440040c405001003040b00781d082e0a551004519483d0b000400098003c3c501c031034402c0d900401000d8070411a0301d00108100041c0d4840e10509a580388054040c0798034001d84244654400c1c4000780510860803c01083c000038802d40f0700c0650f03440350041100e801c10700c01800c41c40d0000c0340c0501862054082c4600e00c0b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 951090386 1250 951089136 951089141
    0x315110c030d0218041406040c03110405040e0a12090e0601020d0c1b030501060f050117070e0d03020f010204180c020f061f0806070503091608070302061c050127 71
    0x204404004518200c40c003202c2030000d50000080c05a200d01014071010503a440740a0a190010000030030401403c14a04200803103002c4060301050620700017007103018810490560302203d02c11a8001010290f43c3d0761141804415280101550b00603250003046035000700403502510401c1a41e100159290340040e80d0390b00790000300c1c4003c40c610a0328000050301220400003000c02c2d82680c00102c5507240d542030700356200d942000003c22100c8800f40415640405042c1c080c98901e04040c1060031308803005018141c8040b01c1c280940700546081041c1341c000c03c02c0f00c403c41d01c0b0034003c40d95146d91f120300081c5803011005100c00300d410f180208810300d10000340d104e5403a450707502501075a1103141720000300a5480000101f007103050b10303000a07542c00074003c182c460685602c4980e5a0300e450220305040020005000945c0c03090040709010800c40042d0306d00649034191003099680320b0f12480d00b1505030042e265507003e107050100105200c0082c07030400d09806041e03080d8881d0700a600c0ca94406 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 951091636 1250 951090386 951090397
    0x20303040b073f0606020d0318020a030f0f150903120c1403060a030501020706150e011203050a1101090c09060603110306040b0a03020a0609050306070c1a04061104031511 75
    0x454814941002c08032031419000c00e03582c603c48804404010465043e032015030780759500c03140140c0c11040403500280c1d05401600b44039005481c03004128102c80c0d0000b0b803008400e01010b80b135404141c00074410071031081661120581c21081d243e100007041650100030304502107040780022000c540c009483c0e6603e0080356407480041d200c88030001030140c0843e405410007001954000c09004000020800c203200400701c4c5400348002044a9500881d0410880f81691084102d0120080108007045003590041c440b190305107081565600e4104c81220595010719041040e03501e050038003020850301120303103011242c14020a2151540e102825022181059002d0101800800000d08246041d40c812550300344000c1010300c4150b00d0f0340200346200090f40001001c80d10380c8070184503900d81000059444002071070400490031040d603450040390105020b07441e11080141c046020051640c0100e0020796402001a07240c40d501d003000b004280c10faa122456003072800c0440354040110b08110f58 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 951092886 1250 951091636 951091667
    0x102150c070f0804090204080c0312040f2306032409070c170f0f0409111c0b0f030105090c190f051e1c02011b0c05060d09080a020303040b07 62
    0xd09055007601c81c8003a012540b0030456090300100808202150b861006d40017030030380e680042c00001440c40c1814508402d0112114100303200f40300412040700d15805442c261402101000e00c144481c103402c08481d0101c0005940c0030780301000b04000c44040340324296400d0fa92005038520440c80c1828804902000c1e104000041c20400007940807840c400b202071121600c042900745000c10303640d490005a00f001c8032003400c02070000340401060100740103401d41c0f04401e4a110b490710f8040c0c010b5030b000c1c0183c6038851455a0b107415003060242ea552603001d0500c40007600074441460a0961191110441c0c0800c3c0e12440000c141d0f8611004103003811825102d0b072540c00240e00382090304000400741c01410040380100d000407025503075200c00c0840a1000f070315501c07481c00320000384000f41c044160340200e10070128400c148171020840c10481c50040701c606a90003584c5d240310316460342c040c1100101c05400c2c0e040c0001c00e12a00782d400001948214020405455240c0714170304202c1c0c0c2d002d0369100f510b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 951094136 1250 951092886 951092911
    0xe071805240d1a1315060803032d010923010e0601111c02030a030e1b010513030f080702040b090103050a02010f0c02130507020106050102070b1c02120c0306010215 72
    0x449400d000041d092150f004201c45500030719815201d602480040358402068507014140008102c440c00c20400b01c40c0b44400309002150403c1841550307800020001c1c01080207035032407103000c8004d507400c003001000810744a010541e1520403040103011628181c040c0c4050000c50b00105070a0703c2c03012410396501c8031480100d51518001190a600d10b03540d43d4a0714010000e1808100050383c1d02c0b0321581102e5006103407141c0345035101400300c41c07000c5441001908030140400c6140342041d1540c2c0c0d281000d007401503c41ca5004484044001c954200500e020f042500f028141b1043e1405415814802ca905110b00c40d4030b403041c031064280078070004040b5400b01c0e0f0410015030207040004603200c01858103d008042c581c0010341900120840d042d1020340d9507003032044241d42070041a000d40f00a000800034a41380c01c804046c0c6201d51801c09092401507000605510f84980442e6407103c454003003e41e060903c1c0d604600d403a0300075140c50307000d8030400903500c02e1003180d0100588a0f03042101007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 951095386 1250 951094136 951094201
    0x1020610050904020f28060201050a0e0607111011030613150b07020f09070819180305030a0e160f0e060105030a05040302210d1107020a0b0a030e071805 67
    0x34803051440740c15000d80d001c3c8005080d141940540310211900e0410001b00b01d60f0149420006400c485003e0001080c040c14040865054800040e681d6041074140c03500c1ca150209030f410160412030400800c0021508225034044801c070000080d500505045030502d0800c1c180030111007c48040d905107125801d02440c0070441ea001c0031000d4414540003609640142c0d01c0c2c2d4000a0100c10103c91410100c0d14550500404100c251200302440390700c510308120100c81070103c2001c800d11208003d0402c8000000646001055044203907074040b0141252902e03054000d0881240625008140c005024440001002002903003000e00458041c0c5403140b55803920882c200151000038000c1e81584034003211002548a0b0000d201414040700b54501c1d2140380100d010001d0710f16800343e1543c04c000c144040c001595a0b0139058040b11101e000d515500c0703034541300c290050b00e07c0a81c0345c191401082c800161b20403150300c092b01945607056003003242c0d5071200c4444410316802d0340c0700200801c01064 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 951096636 1250 951095386 951095389
    0xc010915092a0302130606030f0e1209010905030d2c010906030903020c03070f09111c020304170f13050907020c060307031518050c03151e030313050102061005090402 73
    0xc1500440e0b000d0b01c0100d115450340c0105001d10002900f444525590302c0d010441c0c182d15100741c01c01d480c120705040c000d0003100030070103685a2542c0c0500d8590703440045c203541a07a01469040303008200c05402c0d03130030316002c40d100600550b800c80054016240300c0152030301035416454070f02d0071603281611070b400c1d01400c0520850052003210b83c00c406510a0009030030056500704868401001085080100d0900740842d06066804070740c60480c040c102030001494030102c0f41c4000016030015000103890f80d445060290f283e804903818818490780000d0485d107034000040003001c20154400d419840a9620001d10400020440c6c5100050304030104a00151034040300950300200e06240111c3c15a82d0111648600744460784200d111064a40124902c42c00502600e540700118440c040d00b03614000f55041075484440031642e00c01d0340702c001c122282041c07565000100311800307001c9a480310400002c20801152074010035015105a00c0040e6084420340d50346002d56a002c0c0000e08180c44550 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 951097886 1250 951096636 951096683
    0x1005070309061b080c070f0603060e0f1320100921170a051b01360b070809010506090106050a140d020c0607030f0213140102010e030c01091509 63
    0x458a10f2066681140400d032810041c00365010301d2400b86c2156883c0c82d449407803071240c6601202c18182805e804002d1409624a6280e21960494550601d940d54821400a244103203a00416007a512a13504002850210341c6060380d400c01e45007006861006c1605890b00002c502c680c80102d00700c0000001c1c0d00d14680c00511034140b02c0d0200c0b40f0fa4858054110000c5e800000c40180040c038040b0b0850b06500f26416041040e140000c0204901000407002c030f0800c040d0300010b000213111150409280c18017001c0c0c0f500640d900f10310000894280602d00600d103841c20ba402c285150300b8540401c6541c0b900368090750403141c0c95202d2501d05891168282c40307045412407441c414100910506903448050700047c1a5007884070054521851310304000380441b2171845054001c0c91043c0b040240c1c03400d20304c1100d015640031144480312590601e0040303000d4199001c85084a01020901081c813000541042d00342030320449803540705102500250049922003100074229503901e030000e85030440702d003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 951099136 1250 951097886 951097907
    0xf0e01210f061a18130201050f0d090b01091d0c1908060103060e06070309050730060605151326011103070f1d040c030f0501090902100507030906 64
    0x50000d10386203000c589a140c1150801c40703e201d01150b03c80048a05450a01041d07908200c5100c044185428028440c80705a02d038030750300905004000601021035910340040e80e164405400c0d0a2060a99624007030514120a10400d0441401e001b145200000d1002180711000c1c015401040442c02080070003012a07020303151201030140d110700101e4140c01c2445240c5c0070f10b0054002058035511309120600d8920010207410805150141c080c0001d03001084400c1100d440d014501140034008021500e441400c0400030144070f2603103d032208100c016003111045940c00c0300c000360710140a540480701441010050024009607079070030b2080690f070745400d280d480d0740008001001000c034140c80742150b1164020115406001c000c00004645c007000ea540310403854a4135140002120308403a072205100e10455104036155140c0ca4a214440d41c402c0520465000c0248200c1d6500d103a070400500300e00e901a801b0b15800f5207505c0e00c481c094405c46840e2581540d6001707030f9030714002c0211400c3d142d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 951100386 1250 951099136 951099143
    0xd0c11031e130e0a0c020c0109120b0408120702100c0306140618100207140a05010503070e011404030b060a0b0c0a060f0207061d062508060a090212010f0e0121 70
    0x981a010900f42070340e01c40d1900c40c52500c1c000103980081d174000039140240140103241084101300050240c0703550740c058100110b0780104584056100c0b80303050845402101045031015901c0000c00803107950002d003100c551215040200403244541d1802c400381c0d03c03940501c0d80300c40c00c5040140080e043c0000100701d400c40e038a00001310a00d40d54002000b09400108010040c5d00291080c401030344210010341d90018200d07100c0d80564600b0001038014040200300318180400034108480c140d000d0034554a5a81039646410303a07035500c070300d000700003c0c0050318814001e081840d008a00ea0014000304c0320705c0c881440c000c4c0026000d5075565009011801480b000558003401104002540c034005d20495403810969241943c0d0300300d17145442c2072001040c99400c3c80ea40300b1300c034901c00c0c40b540c04000f900300305103070031002da544031008550b045586610140405200003882007120041110482c182d0f485034603842e408591b584100103100f2401e0244c90303110901c40440c28070001c005002400403501c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 951101636 1250 951100386 951100417
    0xd1709130e070326040f0906060e0f040e012406030501080f03070206220b0d0b0d0816082101050102121222050607021b0103020c0c240d0c11031e 64
    0x18031a04584e250704254403c5a40c104c62610a04c80ea070118060f95000d0a00361401440300c40c1008009103c2ca107040b62224002c581c1c44d1820f540480c400e4101e2140080752036042001011f06c84075a0404800c5e0344a8000000d01d04800031034122004504c0c00000341c5010015030410040e0307000c1102540c05010300c445201030044500c13106002406a02009215203541503440c2d404060100d42540d402d468410320855030b180c0c2d2040041c1c801c00680e04540e0744122031484001030391401a2103841081000e00300a45e2151498000400c002c0e80681602e03000e90170388036004541000da82c2c42d401a1803111447c00c1d1010002040307400c00e010051484000350194408a017126100c190808405988a10058001030340200d8480b1751000e050694030003c1c6070461400c00494103c41d02e0f1681030329004c0c82102c0b00034a0080358110040308840e41c120400c074a0365518a40d80000c002480b6107060140480d0500d0443c0281d81404400e8075000900681d0f1211180f0903040c5d482130361fa02008031020000e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 951102886 1250 951101636 951101693
    0x10e070627030614150a03150b04110714070e010e1b0705101d100e1612030f0507030503060904051c09140a051e0d1709130e0703 57
    0x810707076805100440c0107140028a0000030048080e400000504025030003a03950b904288a031034031034611007100e411010800c0008414204c41c0b000c1c24000503495807040c00c00b1441324075252400b008186140c4244024200c0c2150303014001c1c0c03071350658410300c103582c0f503039500400c003818000e100c0551042c0070301f031311151b0340903460103a25003901b104c84140c43e60b0303004a17624002100d16100d50301206070354928901c614000c002c1915654802030000220180c1c0754044c00120407002c01c0b01000c000006a140070905031110350000700d40740072400c01e03400900402000000c1038040e200320781550350555101461a90b6910911104031070240048420b84103416144850f0040801d104540244c40c0d51107201c6540b5050340000454010000244586803c0c682002241e0314200ca2510080000d03000600043d1030070001500440c107410082e05101082034620644007081005003070608085610011107165061288202c401c500403490b40c2e0b0340406010300224010019240d02040c1c0b040e800080328 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 951104136 1250 951102886 951102947
    0x50d02030604270c050f060a030f060911070302060a1a0904051e0f01050a180f0f020d080c15101e030503040e0612010b090c16060c0f11010e0706 64
    0x90040251400030720400300f211003002100301411009004c211540c40284d03086d0b00005000b0b100312004042815524440300c02c050203d600040020043e0034001c02c0316014070b02c5d10500c04e038014a405c03070042c06140001618142e41c0c4c411b0351010100003400c0036107542a03506000000501500c151030721703c9000440c051083d040003800b101c0c80540d0024004a6614982040c00e484025005a00c02403e0402c40e5a400d05e0b502c00c00c1c010030382c2010388c4d01d22010380c0d4146100502804c940180d0001180343c02d05050014001c000c1075000038840403243d0b00a05c9051301c2c8010303c015158131101c8242038000b00000001e003c4000302000000b10b096040300e0341e95030b956203503a0083e80540141c039404420080c0a1910b603c00d5064040e24800134001c1d0b82102002840c01d0100400c4040c840102241140720500d00a0750042c06a074041d101f040310348241034015001d924500c01c10b000081124a14148048040c0a25110300d0700100040c200b09040040036500c51400303c00101d2401c100fa0307c000e04a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 951105386 1250 951104136 951104171
    0x71208092b1e0e10110604060c091805040c05180408030a0b0904060e16030c0e0a0603050d020a14010c0e060d18030918020a08070309110a0f090b030607050d02030604 73
    0x191026101e8420f03203403400e02400a607041440c1e8100500264510b0760706028808118136a010b0340c00207000810f070940407001d44144000350004c1c080c10011800e1550b170480c89034800c80c003c81c01180d00303001c050303500c0d01081000002c5820300c00b504280302000c10000b800d107901850f04a6000344002c9010b01110307001c1803280404590139901940c0b81c41d044c6456007401d000021036407408401c00052079085031101c0d000b216040c46200460160040080c030408000da01100c05141e01009555150040c40e0700259a0308070802d058a1a0240b000d41c0010000144500d500c03044554458007a0060340d0003c0094941102c1500640d8545511801c94a80f440c1c4411480d440d12039140c1c10f40e840d0031300e2f924592070414060740f1040385204220000705640c0100500358855400c2c42c0100d00700f54103152020001c46481c3c4165000240320502088035000311126070305075035240e00c0c204010501074040541e141e41c01d50341040400d03070800c0030020240d1290020b503030100025001040e410130742c0c40300a00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 951106636 1250 951105386 951105437
    0x8190e04020f03180a080412030504090203010e06042a0e1f110c0a1208030a0e010e1e06070903080c212503020304120611071208092b 59
    0x104102c000040080c0c1084850490344200e001c80c00038444001280e45545040c482c03401503175014050074084104040c81402190040c006a4006546070750350b52018030100c0030241e42040c030660401d4040c0181824100c0240480040400703d190300107500002500c5908180b00c40076000204000254803005480841ca2240c5516645a68001441800031400c05001850300b0b440b400c0303005800c1254070342c0c110640c0302041e0085080b40d80ea48a15007420020a6a182c2c294082d500740882510007107800301d0400d0042080464800d08442c8800560b034691500315480704c040743c4200414404914083c02400101d07035040304a07071841403403504440e80c03000b242070018440d0300005130f11030341904402c0c000f4034084d98031440300354860304a68019451b4000c6004142c0d400d20061001c0003484465004041d40e0398941e801c5c1603454035282841440400f4800c2002c3c04a216100454400c810010798925000c094410b521f20104250800391854140c03840c5107410040051108038207070050014030301 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 951107886 1250 951106636 951106657
    0x25180b1801081204080a08090102012a0e060708030a09020111010f150e0402030c090603011808070c0b040f06052b06030b1005011409032b0206060d08190e0402 70
    0x51441d850301094519100c00068184200c1d10280410404000001400c01080303500c00c40040d240e41c10200100e004081340310b283c140c4d01c41000c2c0c1011200354207000405148032071381d03039a103410040407040c80882e1049690003001300300304200184607002240d2040240c288145010100040300c100f0b00381c05e5801c070006030161942d4550f10782080c940c0004503100101f5001c00400f80a140c641c00080d00e81c200c11043c0f50040c002200060786999080d4003000d0030708495100b0240c01070450404d990903401c8810101d500400c0b541c0003250350300dc20401d4a0440b86003004000c015800c0040032280d130b4108054064440040c0d94a00840c0201d81d00d00c801404428540043d080d480c0d81402c0c004100c000e020240700c00032244041c007290741e00014400e902c050109002e50b03240112804030703252001001b82d00b01c1d0013101c000c2010b10042100170525190f05150700301d0b00652140c0c01000300e0b8002c5000d004104000411068001d61544100d11408070142d08041426018031404201079038042000403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 951109136 1250 951107886 951107929
    0xe06040b100f170d090b03070f0302041737080c0a1a060a0905010b04050f06090307030b090607261b0409020d11090901120c05031005010825180b 64
    0x40100da0f1081000100e200c0307491600000b418a00740707051410b48000740c6810104100820002149406501190010401c6840f422000103034002020780f1040a10368025003201d00050362602c0000c281d6108402c4004c2d03964414009503156612581c660150706400110302038424103c011a0400e1740480c0f8413200c14403003541915200c02000440d516039044858180c0c40c01c801800741e0101402500d06071030313080d20b00218411319500040c0f854080c0440c426030501c41c664020080045484505000e454608200da01e40d0f1581e15080e9400c1f82b00d07030000c002c141c0c180e824074000610400d03081130300f16000c08001b0071103016408403402e1607441030300f240e0344258001540074901c0040340304111854070481c1007282050381d210001101ca43d018400c00341d0781254204800188440480c1d1100102802030842c4e14044100c2030700340190809206003a8640580e50315201041c0041e540c4030940101c4820186007a801d00c80004480c202d45440304085966454a0700c0080e200c2503555000704c14070400c41c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 951110386 1250 951109136 951109169
    0x203060f0103051c0f0e0301151508090d0c0f021305040c1a0310030809031501030c0f090911091302030a0503071716120e0d12030f0e06040b100f 64
    0x91031034601c01344002e8260782186000048425440407030380388441c0552801c924242004c0340002d001d021240e81142500640204c001401804500d032420801c5007520b4144480ea14548403a880e121440441d02c049000c03408030b4000504458000c09182d80300a29202000d1084128001114800c0300d048175120140c050500008081001c82c400d07009015034828514030f0140141c1010821030700c0000c19800001c030b010b54080d9400e00082d04100c02c0c0c20800451503070f4a0420600030b1450b031280c07100c00128a44042074140315401440b610603040060040c100d0b01181c05d00c40c2404000b0180300040709241000310040c0d800b40304603010720340074900440c2c43d0075040c104004d204024140031059030808100d01c002c0048520b030001c11881e000103c007807a80e02e41d864107840c2c40020315245a8132001c0281c0540400c80c1140040540018540d03003044280c0c52115a4000c42e07002d0030814006902c40c1c2c0000c1c0c0042c5040c18040ea00c512181d0448124503620401058500c0e030310741003901d060a400d142c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 951111636 1250 951110386 951110393
    0x6060a2c1302130e0c0717090f060301030f020d02040608030f031009061203050a0215090f1002030c0913021603050403031115010306020306010903140304031a06060301210203060f0103 81
    0x1c0100001c0981c104601e4048620790403400360b0800c3c416004d141d401480003079800040702082e5000c83d50040b4a5510080060495081c198841d802191190701070ba80041d443d42030620070b403030581c0e500c940744400d22045a001c01c05600341194080303074019181d80e00411801020b02c0503000182402035101d440e8100111050800126a00415121071070410100184d8030703907503002666036405040043e500e0780003100483c10000ca0500c80d40c4404588806d110b0740d080c0000d020000043c000096aa108888141c41e1f016807005413010b40c889103007840305440c0d030319020101c802d01d004a03040051400c080c040e02c0b800010080344d415008540e02040400601d86c2001d2000c410301c480c8005012800086030f000740c7d8409041c0405020140e001c000a00264010181c0e10701460300005100703040340c038207049180d503544940000c9407101c0c0b0740600035401030201f2b1140c80c040c0c80000c01050440e800c01420700e0024207000b00006104240c4807059004da1024000346019481c1108542d449604609 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 951112886 1250 951111636 951111649
    0x120706110d02060408030c040302150706150f06030209030321090618122a031918060315031a10080303091c0903060218030601060c050606060a2c 64
    0x40040390541c0101000d00000c0da40802c0a9500c941e2020f8003c0c2c481d220307118081181c0c0038903040203402c40300301ca400449000390040900700c03040c442c10301030141c180140e0171160300f13210501c0b0360061008050300034040d4500940150004c4000901140d06104000b0103203030f4000d2662101000e9411020280207081005002d000da0000c0b00c56801c0a034070800f600b499640c3d2000c0c005281501001040c5104020322031544142840800010310500c01c41e03503a401d50701c0703600076001c441802e83c102e22241034450044001c5040341c60131120803110189001c00c1940070302038401445c1c450344503161010002074065030500c1304200001c14050240d1900c0468240329400c00d4100300850752060040200c0f403040000c40a110702d0030000603c1c62150810001d440f24402600f0007410340303002143e2148020341f2400c0984501400b24112a02640e8554003036401c0c4414013800303015038010400041a50810600a046220031340c0b0308103170f80150800040c201c469050010213481c0c040c41c80d0b504040d24011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 951114136 1250 951112886 951112907
    0x1b0601090e0c0612070503100510030b030f010905070b030a020f0d020a02010c050f0d0902030f1b0a1721130b07020f0a140108060d02041b0810150804050a02120706 72
    0x3d5880320300c0c260300c03602e0f00c604950008010208002c80040042c8040b401606d004005100140c002d00d0340711721061010b00a01400300c0614000d1103a4008980540c80500a0400c07298000024000c00d9080814000345540001d000c1ca900769000c0110b081c0108201008010510b03080c140182c0390850007034002e0039200d20464200411070103212141c12001e604003292005140c2a1001501401c3c40c40400e080100c4503895400e640200300020a440d140b040034150710b500d045903520b4041d0f071103001c814012044005400003d03448031108000f8440c808824a089030010482030781490071207107101c09005130030382025003008004a20b0108504140900d010754620484809d18201d0401610032107000201060324100000d08010038032079282c5c1480c00178241d4002e001400170480340f03d039a200b200d480200c03000004100200140190526a9014040e1052415400c80c1200c0b0070008882520b0082d20940e40c601400ca68140169101c216a005014011010b000500e01c1e20701c0180c20480003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 951115386 1250 951114136 951114139
    0x6040e1c080f07080604090c0e0117070906030506160c1e051501060e130212040501200f040320030f010e010e0a02060306090408040b070507140f151b0601090e0c 71
    0x406014803143c01131200c6030b000105a800048503001403c10014041c0142c0c0600400019400082204401080381030407461a482c00c860345582c0d603121810440c0c000d4030010300b6a811900100702e400c81e062440081405207442c2c111800a00c94030740b004402c2915040c441c85881501590080003400d002048107402e6841038211690700d04040a840483e01444052058080580280000b00745905466020a4602c40b4100c4e80c5024501796008100c1aa00c0d90800a8091a0740031403101c8a0100d03281007001540342d81c142442c5545480a010f0010341c010500724036000703505116102042810a14101031001003031200d030554441c0d003100c168609103045904080f5101c805601ca4104507070b044281070700c602001d5603d900b000c1010b40241d400641c1503d800080745030600000051800507601001100d01c0c0904540041065015441c1050342e003001d4900405480d00d036410018182910098085190007651041d000c0e003004000d800a00c0e5480d610518070351048410401419610030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 951116636 1250 951115386 951115411
    0x40b030a030e150c0f010b010e0303070305040e0a09020904030c03142a0a170702100905030a030e1201090c1a0309030409090305040f1503111e0306040e1c08 69
    0x180e0745004140c01d4400c0b001900403d00342e0310b00074060084400b01d078900c02c100410780380f414a90140740c50280c10001d2440e4006803031040184070a10b07001c0119180d0301d5054484502c0c142c40c11203000e151540041104103019940e0f080c840150f150001058400e81c07080e581e07a030004d0014074016246022020740a07028085c1404001046411412031039004400500400310b990322601100b850101c00c00300091007201720307501e1030000d0f64548024219851080340d80131442c5282071004c4400d610f0320b100e20703030385513015600304d001082c010800405040000340045d50f1341d40d02c000f401802d540060004451003004000c00f00040405003c400301042010ba40c15840c60514000d804c3e56802680a80b409a88d5a002140304043c010030464004250030000b04111550303494560840004c11151400800d090514003405c136001d1808407200413055121802c804400b00024010540000702240c0c0c0050340c0d0b40f080320300c03500f04000f0304100030314400000c058901d002c00c008019000151880b001c840 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 951117886 1250 951116636 951116653
    0x204090f0506010b091e030c0303130806011509030f03021623090f160207080601090b030f0c0319080c100207022b17211005150a2f030702040b03 64
    0x595041245044011b510011502401d80700b0029080c80242c010b803951502c000103071000d0740fa8510b14001d086450000035181640e80e81c140701d070054030b6841040340000300000001e0000410090105400c140684121040c0c425031404404203600f440c0c202d2022229080403083e51414003501d403c500d4641036035903c00e00d0514034480450b80c003004c1d01d41c1419aa400c0f200c01980d52080200b54001c05c0d20300119009540c0d10b00103880100b41714000180240910007180300380041c001052500c1c0b240c040c00412075595000e540080e400c415100440350048200716a10500c8401c20850713845261000d40180c0d0f5003094810403600070804000030b03031950302010380000b0341c0c24240880300c203280d0441c52078400500c0c3c0280c19562841081c48002504080a80c25580260803892003880350000341e8219a42c1615101004019581035003122840039003001501031180c410468030601e20b0050022100914400c046141d420340c0705000c00c60250b1003c035462080d86400d001d000001d5005801500c80358 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 951119136 1250 951117886 951117889
    0x1207050d0b060d060c080703061403061918050106080d08040b0604051320010f11030306060906040302060d050411060c0c120304092409020406080403030908070204090f0506010b09 79
    0x640e4203902600d5120010001029526218000f1840c0b0758080c90070003400441000261003d0300a0701d850001078980300011907803d10b081c80c0342d400c4880c01401030880360340300310180500c0d1000d44903000c0215110702165110718071902c507600c40144280300100d03c46041610a0340703840d40c012001400c00004c1401d000c0494901c2d0703d16a003005060f00e01081c11f54a89040c0c01d100c5034020340c000c2949480648403644590f2803010404a20002d99900c1c0d00c280f2080c2080394044542000380c1c400d40c0040000c280c26140c45002016100ca0103441941001d54940010307840f41c02244109172940d0b2210b04110402080b19030030001000e04550160034a00d480c0101035441070203081071402400240d550401d04241001030b03400034481418140440c0c60303850001c503840402a40c001812a4441d5004038400e60306001365810f0b1441070b51000710956450710110040d156148042d60303602001c000680150f180d900400c43c20358022543c8001e40c00070340c83d0a901c1c00078160b2010305080e00510010070329 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 951120386 1250 951119136 951119149
    0x6090a15020315060c1506031b010305090c041d0120120a1113090b04021206100c170406120b01090519170105060a0e040201080402040903120911120705 67
    0x1494031000680725036030404845903661141d158076610640210f9141050782c80090303208182060010b03202215210302d0700b811380e0303200400d01c0c99031424900d6400c0e812a5204c0e5000c1d681c05580402251a45034400c0007003004c951500520903c00c00c0c20b09402800f174032090080001354003c02c4603014100c0c1c8038503c48807d03401403c0606c54401030741000b040001c0c0c201e0304482c440300055401d00b90b503080071140c500d8039169144100c0c1d40840c2000640000f5240c05e209a455901e402c0c014609203644503010052200da010300300c07074103001031514400041882007846600095014210b13564481c00c002c030282c144140f105035205040d040520705186664003c10034400c0751000e07100d034201460710360b440001d00101c2d50072200144c1f400701c16142c9042c1054021501a0301c0942d8590400d41d01c94000c1c0c83c2585046030068081091800480c005060641c007000b0b51900900e0f183d40381e610300300301c10415a08103090a8030021100150790f0441e2901c4103800c02543e00400081c0001440c003000b00c1d40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 951121636 1250 951120386 951120413
    0xc150108060112060e2509060501080609070f02030f040914250e0d021306031115030c0a090e180d11070302060d060e0a02040305010b0a05030c040506031608060906090a 74
    0x1000b511150102d0008a0400c1040070106c00094a40303500d00c1c0c502a00d0003e004540b26030780790035082450001d82035004205240c00303064040c0c1844460381c0e803240203507422a41900c03148214071080000744260400030000d040540070405c1d01003072081e41d1010f2041c144d00041c1000103081c1e4a0041203002c075240c8400d442c06d5444606084841e805080b000624a40e9120406500940710440386206c009659000c4019a4442d668460041c100301c0700b407010b002c0300303203004038210802000071881c0d1200c11703005440d13a04071070701c0c1803401c1584070700200c0d0807600d043d40d403c05220040035107503401039000d01c01c442c0c3c41c0e24541b0341800b00c034484480065849419200281c000d4000052075280480e12340c003e0701c054182c8000c1020b00f4100f800c1220004d40c01884140c23819440c2031061451880c2060b140d42c01c5800007401002d015045004004c000e000141002e681071050b40d1540c2e04020070085890010501c4c0d802600da0b070b00c1c1c030051050400100410042140c1c006004c00400102f002c04221b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 951122886 1250 951121636 951121643
    0x60609111801020c03250602030c06010e280209041103071b080c0124060e0f011206030215120f07080403080703060503030720150904020d110c150108060112 69
    0x10000160140140d08000f050400d00b9014066030415561000c09240d405106d03012203161200703001e9844800f243c03a402488151070060304004010010450750100c89a0884c460b100010401d079825564801c450300c07003da5031444240c004c40e0072101440e140c401c0c0d07600e0355800c4006529600c1c0c9400028540826504203142d80700c05098800c0c03d2002c004150707003c07504104000c009041086160620301c41600c1400ba80721301c203c88002c103841b4403604450f2030128002c1c00c0766a80340030b04801034525403e05c00c44101d600fa541c9800001503079806200700900311496150340e544031041004002000d030014400345000e070b1180107022402c0d078003604990f402134143c0781c00303900d546034260210054905a441039a040c440444d0000c1130000b922071030090005030740d9410003a58002001e03c0b000d000e444102c09400c14050000c00041d04040c1c004050050120600240402480c04503903019045113410200381c1c0d000405410403c000354400b1800340c00c03044001c04d40303503140c080d503001211b01c16071008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 951124136 1250 951122886 951122917
    0x30314101503090c1707080d140a031b0e040b060f12060616231501090b06130e060a0b041212030e060f15010c0203100c1704080706060911 61
    0x600e900c0b031282e48510741c03a980c0203403c488003980d100f0904003500c48001c4503400902821038005a00328002501c207403072500c6a00d42c1600560030700c0d40c8043d41c0d0401030500c020b140d03d5044c010300c05269581508510499600e545460102000601048900c4841510300030380d0108071148080c0134010941c0e8007128620740042486c0d942c540403070139901514110050800091f00c00000308052088818405543c00340c01989649400c4211940d0760400451845001c2c6140e0051081c25174580082e1040c060144c00d01d0b133010f81d0100d02402c08a06a404040741100301c1301030025628081c202000201103804c181d0782060300f0b15080c10507050f00c11200030194102142d90700c56450084e00001760058110007a0381e000d240c02c1e0a903c41a103404c40d4416451580d5030800340c810744c059598001c1c0550054000c10904801c46c084100070b20710078481c2014404100e40500c0c112024454241c0f2861098a050b911802245494402d0b80d0720343d00301340505814201000781e00960041a07421130303680d12218 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 951125386 1250 951124136 951124169
    0x15090d0e040c0c080307050a0e090609070e21060a0b03010b03190c05040e031c0c0f080a060e0405100e010c1403061503070906081008120a050d090f03031410 69
    0x380c4800c000003c0c0100b840c807002c0100000c10382c108014052003c06a00c5407452094001c0c10030271000300440b5008d5000d03082e4000f0541c11403060401d20000340b00034050303803240100c00c40b06c2e00f21018580032a21031a80407030100548601140070702c999010059000b44058035070000000c0c0c96005200f0141490501d4010702020700848126240060201030010810030780007070a8140c4960241c400c042081d51520308203010450a88900300e014103040d601d0700a040031196080712900000351800c100c0320384452020441c500d5a9240e5409544076000030400005000c560384c0c2500c442d0520440d01c0d92404203030155060304066604600000220b03190b560340c0c0e4260020f018070382e61518200310180040704101d03009801c103403a4015282d01c0e40303403114107641d8007140000900c200e004038880c2e034200340202c03980317a4000c0c030140501174010b051503414030360b02c1031000f0102c5842d0641640d0040d5000040307401e242e00743c4920320310840a03030300c1e0449503d07111440f1900000140310b6940040454450f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 951126636 1250 951125386 951125411
    0x81b1b16080c01121b08070905040c05031e0f0712090204050f010524040b070f050a0b0a20191103030906100e070e090915041211030a1e0c02030a0515090d0e04 70
    0x30024000c000c1c801c00c521018202cbc000c116402c11640040740002c40c61910b01d5035a0b010300380522525882c3c122094a50310000f0480f032a80306c07540540c40250302d03a10f0440041ea40e600031544180800040000158035280c100b0915090002003443c101040701300c1100740c2800c402c00c1b2400d40364400110b540d03c01e480d00d0050040c0b052403202034030390b000d0500b807001000520800107008800501050180d503881e10300c0d03c64001c951150b1203114000c102301c05603803002c645505c1c0c0e05803c1c2c64184015400001000d00303056500071200c282c140c0e080141001090f0500c801d518000e42240c01c04420503190030300000c1c0c0240c14080b2071034890341d644000203511071420442422400c18142000348103051519009070071020501c51000070411740f042d020070040c0d0001c1a15001b2080344e60b00310209003401e02012180d089441a1030802210300302d100c0158504100c001007503841000200304441d441c010352482c40002078100c00064005908181c1c8056010964100c16941101d00242c04001c008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 951127886 1250 951126636 951126647
    0x270206090109180c180501020c040f02121501080a05061c06020405060c03120606071509020303090d0f12021903030e0c180403081b1b16080c01121b0807 67
    0x1440340e144030a00f080c412003020000e0300103050131580750712140d8941c501528000380c1806140141401644041031070601c510f080c0e0803484848a0002d8011f103000c2c0fa8400800350b482003141c01c4001c00d1b906441e02d5607156400800c07075501c04038148040119007081c01c0000d030301d000800342841076040201c00000138004640d0440b001003900600c0e465a42003004883c94880d00b04240f541401c05400e40010040c0c10250b04480c0004d512500071820944004580801026605803c0e80c141c030041c03103d43c650ba20307500744220119001f160b55408400c10b514290b011b100900c0041c000711340050a0905a140940785803018166050401050103201003094a00e480701c1402501d0348030341310402d18400000f00707448a80c0911700a030740c0d5903031594a00746603101910000348a1a24008200701c545499903480c003036040e080784080143d4403841c002010049142a03281c02c55445604142800c6d00c5540c0c000c54806074201c80444140190144100858141384c401002e40050081e0a03000035541c1c1d2140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 951129136 1250 951127886 951127889
    0x20607080d0b120d03050a0e1c0c0c180c020f1b040902030d0c0b0c0304020612060f091006021b06040603090f0b0108101119120603050601120303270206090109 70
    0xf800c040383c030103400a8a41d0303940c9400300f540d00c04249040f000c0b0707245035500d0140180500d03004000703207a00c0c159a44080d034071181038020b84040100068401c2c0000d420205140020100042207228001e06101d64808440303005540f04103541c485440d480c0d8074840031424804510145010a20784601c11700824064509907070002d5043c0500390754154000c4d04a46034006203800342654000555504014041074401501c000c1d42c010030901c2140748038070300b40d145c9030303802003010b00207103008195200407400880381a101001400e0f400c64080c005a9810400f02094000101a210705458141c001c10b000380320300c0c002c4030100b545500d608070034400940000f00c8016800580003101d036940b2100303613480302a81480340116a06241070507051300328800c141e81c50381d4041c00c000440220a00c2e41540c40b00e40d820202c40655880c1d0341c001011403403c0c04020300802070016a005205030505e001411035881c08410303030201d241403282e805010308c03034030054044680c103071040d568a2040200581e001640da = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 951130386 1250 951129136 951129139
    0x42301020c060708010f06080a020724090605070903110f01090e070e0a060c02180612030d02071208132402180111030c0c0402030a0204080d0c150504020607080d0b 72
    0x164403000030900094140c070929075591010b80d9071b602c807a00315a620680f40700e5a800540d02030040f4009d62501d40c02449028880e030041091041003940d40352082180f46a0022003035682d84e20841480540c0c098554084032620b801070380c050860350382141c162096184903015200c61011601c0990081c180140540905259052a032819034001486104449840e60040c4c144440000303585020303030440508a54001d19a10350b0810b990b083c00c1e180d42000748026440301c0c0c0c020400003030060903c0140042180c070000542e035a201814410b6001c40e94000c54000c108444003005210a524200701c036945520013810100000407082401619400038039250343c0610016180c01261103e0700c5131080d41200380c0742e0710341803115005800d44030301501e01c0d803e01c01c1d00420a0582c042c5440e0b80255130116100500605080d11265098500f0381310740c4061001c2080e4546103420300c90390b01001c400301180414148541c1c640342d40420302901910304020665000440d245440c050b60b9000a100d001d030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 951131636 1250 951130386 951130391
    0x124180e0c040305071401140d0b131406030d1b03140d050603010f11040611120c0c0a150c121727010902030a0807021f0507060c02030909042301 64
    0x2825a5403001c203a01030f00c030031a81480342210010b01c070b103034400e4001c0400c10141c40c1c90300404000000045940d2042100041c415541c4040d140c5650300c0350b0b0004440302c81c40c0c1000524440d80c2207007160420b0080c141d14402d80c40700801e4a03601c0d503c031800680c4403500000340c150009080c0b4054400d0321240501800308000030581095280303090384418841c0300114001d010b032008142d403000480b0401c40d1841180c00c4c00700001e00c242c0b4042c000e00d13a030122441c011100710034046000c070001030f08074510040054000304914012450803d41000107400c441c04d00300440000d4140107001e80e0700101c2c00a000003115600e107051a030150410b0044ea00c501d69141c620361070048042c0195481c9000d088184003000144190806014826003034001e502400809805e2011f499981d00703904039550403640304940501119084c0c106500d1449406540d031190394407660236140c04410380d000c0796402821544203010604465540034a160341094003c05011680c0a00e80855840b041450348220704130b60 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 951132886 1250 951131636 951131641
    0x209070f1e121127030307050109060b0a0e0123010c020613230603060f0f1215010501140307030c091a090a080705100f1e0c0b0124180e 60
    0x30740200051581080305401003081c3e0410843c040500e00031401c124521240c11004560300280e80c1013074038507800c0d00030708a81c208051655024250f60200c1e100f2200c45455101c031042904040d204400900415850000c0700c0d8100884419560b1003031a2076168420301a46d00708140c0d000d40112a512900504030b20b82c0d50840b01e4038041e00d101e40f8410381110140400d005520485000035020400708010301c8185140c8541c400c00c00000c06d41c580c005d41c004003d0004030400c2e691041c020006c603907054082c104070802000090004407051344041d06101c8440300c4100340785005011039034088060708000816101d0450304607241c0c2d078a90455164400074900c003200300301c0300d00043d052505045805401180d280d60300541c65850700c0c450341e81c0184016a2a0035924042c21018002e0720651130003c0503101005100c2c940681040d24030341c040741500081e8000d0003141012a40503040085080c120000c0e000480012118004040003c100c50750750108e6541c1c14038103200c0300138140c9060044070390 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 951134136 1250 951132886 951132947
    0x80a200406030519061b050703120b0a06050f2a0c030a0803060405190203010f0504050606040302030c0915100906080906071e02010908030a05100905040803043206220209070f 77
    0x50b4000441034000c00c0400c240d107080400312f405031001810010741000c40f440d183c01415202c0750030802d05000a1102800b222a00384000749624580380c00082e84103200500d05e902d0310b0704003940003458034001c0c0c1100d040740000c11000411290003d40030341c0d001425a861098401400646181980340c0c24000400090340052441d640d2081c0e903400c41d010045615004200807061140e03110094044c1c000c840c07584401d250286e48203512103441c1d00011805103004000405d00c400c464000c0b00843c1c002c100c1806103650000c1442da00161810081201c1e00780840090142041c4030740128583e4086007101c9038561003074000c65220707503006c48584c0e06c82c20320805d103c014000c01c442da4007041d039074070320001016440c501440d4000c0390060b40a80c07860b22a6121000d0714a02509007a26214401c0118603d1060401d0450303410501440030700000c0c10f15403282d08041070300d50510200e841c01c0c411039801694545070040c0d0828024100a1801d40c1d11260a869640c070b0600b4644405800c021542e031700c1d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 951135386 1250 951134136 951134147
    0x40b0f07030c1223031b0f071718010c0f0602090609030303040c0e13030912060b131a0414010b0d09210f08070813050304080a200406030519061b 64
    0x121094160000f034241d80031101c003005c0c00100c0d0507000c0b4200f0308040300b2803400c4405c01003100c1052800100e00c2c2000175200c41405c1c003141280c4003004800015a0b00e4824200c0c1c1c46100400424030b400c6800c10200c0c2c8030020b1800d03540c08058017281c0d000039903c0b01390b581c0c141111303034205028054a8513442c00f400c22448d260458410b622110040c0720024039003019410072f07400381551503158916503a08040b5000d400503040b0b141200c0700c079505c1c0004034181e6210301802c41301100320340700414010a0314250070030801c58940380314007841c20304610a802504488940e81580c0c0c104000580ba00c1340942c9041c05044c0c04500917102241c1d114824400c10b0003600c4801c04442e4540b10040751540c0001c0031035284c00115100000108808013042c4640300c004080040c0c0c0b80a0310803a424243c44910281c00d017202e01004545d20700c444000302c0803048800c001e00c440c1500c1102d0400070a440c54450649a01101d6200ca00b034075004140501000f4040d07100745410104500014010101032001810 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 951136636 1250 951135386 951135407
    0x1d0a150b1e0f0a260f0601030b042f070206160b060105041a0904141003050c060309070e100e040b0f0f0103020f044805040b0f07030c12 60
    0x1c0000d459900c1c040e5110284200c60640c0700d0082a0307454030400c1d607001c48180800010180b0700c4800258407103d1a4804041c05000d0202480c42071018205400054225091b0880e298010b0303040c10b400c02180c049203040c441400e850603640c020203899154a0070510f20400c10020341c13140300851101d8034003002c0c50b112204c02d1b00c01c00180c0003540794040150381c580030794462001000808052a01a000d10340c01800c40b40070040d00100e40310006111403205000b0031980e00d03440c08240c580400c1402400c2081c082040c40a039880761440c200510100d031143c50300c0c010505548409000303d510030800d030415800600b040c5550074050308040c5460260324a00790f456544804c0014049440c005155807284c0c103d0340e0040a031460b40c54064280005440c80813501c080019806905000803000e154880d001c151041413410600241e0b030b581d0b500d84c0036a540034903013003010a000070302100d540401241c01c42da1704000182c0d01d410503481d0407500c6240005c0c00500311006014841c18042d008050440d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 951137886 1250 951136636 951136657
    0x19050304030203060f0f070c0501150305010b011b05030405040b12060109090c35010e160f061404030f112e020d08040b0601090f0e070201050c03011d0a150b 69
    0x1d0658980017010320a0708425a0440400103c40d404101040d000d07106080074a44518008901640151032010b4940084e600a65041c0d4440f0003020b000c0da03001180e2a00c45080c0000070808000c80d455040e0f0724000c40c0243c5008507a0349610700ca0aa4960389480360058040741140e46542e10703000250b014005480080301c110301c03070010205030030030f204510f200140030b22602d111000411000c00068503e01c9107181d856556580c8400b030000f2400d000007240070180085150650f403600284103a80c0415034080310420800c024101008012203040350202ea030460703031180c82c4910a003401400744800310042075005919450348032190394580103054000d603140a8604a001c072640050341c80b100c00910140010b500038000034001100020311507003221041c9490034003292a80d103032507100e018982104982c0c841090801c8086542405050750020f034100c01c0b14210752510080b07000eaa002e25811202c8039107054000b0b291549594000d500c07a18078443c00d560459074039a0006100d0b1300860b200c5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 951139136 1250 951137886 951137893
    0x301090b0a090b01020307060506010e180114030a020904030530040201090501110a080d0b100c0c0f031109090124051c08090607030c051e0d180603020c19050304030203 74
    0xb070380000342c80342d80b60000041c0c000d1403603c499070b03440a004040c001c003500d060064407810030080380c039008a911600c0d50320f0b14100c8065418614600d2542442c001c400e03200745e000000120068a40003405500240e160816649031000e010074803a9400743d00050900c01c0c1c1800040040b50027040c1c00c0c0c2030281d4000e803100800300d62148011a40440c0e8a075011202d0b030310101a04000400c51802003508410329080003030040284000114925808101000012032850f00903041c02516405000180284924040c80074555a5860443c0800c102040e1164100000181d440d070000e4000901000b1210b0145942c0c030240e004004030082c3d00e0050758000c2141c0300d841c1056000342c10940000c076400680c05400c181910701044801d501c404001c4041005804080c00041d40402500c0700100c82041d81c8070181004440d070707902e130904190400003080407142e01d060071074040540f404140c85240c5800741c2d07198121030f80b06180001104200070b0714015a058801802000b01c06802900d10840a5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 951140386 1250 951139136 951139139
    0x30c1c08070f15060e15040f060e0709140f0907020c030d0f02010606080f0606090a2112170c0a140c0d020c0114040e0a241403150109050603070b0301090b0a 69
    0x103c1c104c0350790b030107401ca1000b58800450700c0d810300038012507201c440007040890701c2880305928201f5500503501801001c009502800707580e58003e48c00c6005000a400c0b091034101352080064030f009201803481d0f0160f020070011a00442c03081c17018400c0c01d40c02070121000c503901030030020042e406d0350f00701c400154600800450254850500d0f14001e100c500024003190721401c04003c001d030f01500c0e0560384401a00c0c4001045d03103452441e100c6c0968480440300d40c0c0030030790800155003010700f0102c004024020a09000d08920412126080696890b541c0d44401a04000307a800c1c8660341510514194003141c8007080780d00009a400350401e55600b0341e0500c041e40760040d601c01c42a0111070400c020706000c14013180803910010b640c070003420720012a104a6141c1c2c9031113480101541c42e0030f40c030300c2410300b8045194256008001104242e00410380f82142004441c0341340410300441c250075899501103640ca0f46c0030810b00002d805000700f9980c1d256500d40d003400040078000801401070914810 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 951141636 1250 951140386 951140423
    0x703050105090106060905210d091406190c1707060902240304030f0215271b0f0604030206030f010f063f020c071a0702030c1c08070f 59
    0xa41c005c95045841340800c80d03081504100d0b01140007a0541c0140121846d2075017181c5e0204603c0c0f10624507501c81210301d6052018043c0c1582e805007855000e000100714403004440058041440c23900c687c904074100355a50f140c41c00300d0780c2e400300d0588842c002c04646030b810312000381d01c601d4080e072088610aa4070010100c2010340e042c0c02480c00000d01d601400000e011a000b0789501c1213101c59841940d05010444c0115a24200242ca0400e00c42240710781d41d030301206400d0284200716a45038014080700a10025a540c00b0305000700d02130003100c2d1590320501a840f0803041d28040c5500400b46c44c2c880c42c0c20380c81000518000d00c980420b84550300d0380058050f00507070204031052040c54241c03010500c6600c5201c40070006e80350b0307444440300080d401280040c2c40e10180c0803055614001e860028542109903543c2941030030314000c180c108108000042c2d60005821000b0f00b0282c035001c48030a04038003009882410058043c4c1396507000148007007004550800b04801c64458821004800103100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 951142886 1250 951141636 951141641
    0x609071e0b030103021009050d08040504050f0c0d020a030b101e0c02030a02011d0d14010c03060b090d0203031c091e032010060e0105010206061009050f0d08070507030501050901 78
    0x4622a00782070104018005410817002042a0035040d00f00307800a107a82d18045031100207038000940b000d02c00130a0a00c105d1a0900900c1e070400306d0505000c00d10304041c031112030b4910178154400c00f0143c0c00030f000410b07603001e0f03004034205260013408414241402900030b070210704d8010076000048265206000d10600079218074034007a4000c1c0040400c07540b25401500c01120b034008280e0781003600d00e00122280d07501c5888440c25441180c40d42508040343c202c1c5030a54207110911400d041c00c1c40c0c42400107960040a072032080c40226080c4c04490150b00200381944a409404c101b14040e5500440381d2501c05d4210802b5188220360260406a001450262000c10040003c000441007a40c1080044c02c41c6244109d001800301034030350b9882501e000c0c40c104c035016030054501c0c0c01a80010040f940c1c0600104d58000c005481862030203a149800500e050014000c1c58490310000458204030b845295025180070307448008141c0e030b0180703414010341d20221071008540b15820500050710110060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 951144136 1250 951142886 951142889
    0x7080f01060609030c050918101514030303060904060615050c0c06030403480c0b0c1f0b04020f0d05061e0d02060c0d0c0c06020706051206120609071e 66
    0xd4001740b441e051000700650700c0d4002d0000b00b9044c5c1d408480004034a07080c08035540404080c500000d40501042c140c45c0b40b21810703030000700c940c81307803d111441940b00030045036407041c001c66401c580c541d07503850850000d1840e078000301071903252200003540d25904040180f005020300802c40784d1107094242000400c1c442250010002103044103464554200341424180d42c40da0036541500070304048110380994071400508000d03080c14050791400703110442488001400304031442a00d0425400c0314581d0b1512409041c084038084021b240d1fa0016569204400080c1d009000f9550fa00d40d10313006042c00d0300042c0741500064900700106426180c90799010761007801203c00c062031890400b04000c61180703024416a002802003004810b1000107110000c0043c507152200366608075503060080c10418a80c010b4001c1d940141401c0c00455000029901d114402c10740c0c6040c0340d0349079404240720206401c5141c585200321801d0207103c0c080800e854098840400034440c80802000215020504d01d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 951145386 1250 951144136 951144143
    0x3050a17060d02040914030d020702041413020907170a0e060f010305100e0a1e030206011509052b03200735060f0615030403020d2007080f0106060903 66
    0xb00d160005040c030b500110f91a0317014032100c4040340d003512412403c41e80300c0340d41524480d0340000c42108620f0315114540001c0300000c8028500e20708a2a404180080e0400207031080c4021000102001d10980726031425200199001d401414a10141c0c03015126540302d8050038014940001c061000c200c1a86040b40d070070a00070105611000d0422004102e0700c0701d803100314001c154502012403805840e401d01c0c4078002590407400252401c1c020f04151041c0c01c803802640c0140b4081403043c0d480031704d010a617001100c1c00e0b0320000c3e01c08482000311030308401b451807078070440340c2d1311080c540c0003440c5013588429122032888246001203401d403605030f03501604441c07105110303d01050b884074101d014031320030710002ca03800b01542440e03040d443c0c00d030225110080c500d0b0704010060141424040091000010f080702030a6040c80d68002c0e486030308003c044420400e800042c070f03c001c0003543c00411420520000d84403403545075070b029034032041500e07400c185660a01382c002134560301c40c20181084942 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 951146636 1250 951145386 951145399
    0x240906070e0415120c0501091e0311010507060e0c04380307030507120c06050316030f1b030b150304080a05070c170c0f030c0310050c130303050a1706 66
    0x10076008000082140c000602e1681084020100d0142c4103030300344080190280007061040e528001c0010498240d1350800e01680181c0756440c03540c2c001140f131031006d40364040407900e50090000c004941078081c0c5000544054105001c0b80003920001c14072000148003550180440c406076400c0f20403e00c114004040c820860140c00043d000fa0032201c1014034000078161400c1550700e482e003d14120080d000302c40e0901e0900000e10400600807842d07801460103003080c40c00c1d4546031080710194070240e80b04905044d00d58030001c4240000340d10558031814448081e102e2041100ba0040060407001c0469004181442460b9800da0300340c003d891040e9400404245440c94000c003c98072074000c1c1c0412200740106600c0030501e4449240f0381041001950010a070140d20b4508010030345d0105124203002e81c10816468690b0f840200302c07105082c0002c6404035407921501c1800c42240b190003800b04c104103114402004065019000746003a14071030303031030315113821a61b041d031146002d05407200c661000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 951147886 1250 951146636 951146657
    0x3072106020c0a05030708040603050a0b06040b1620040f021815091e040c090303020c014b03020306011d060706060f0f0803030103052d24090607 64
    0x2485074000b4a0080306981c1034903400c0b94240e44562468111800c2280c02c428003140031b110060b41352042c242d1003d9506014460160b0341004114a807145000340c25403100c00003408031214060f0a20b20300890b52081d40040240350003002d00d055160108403041c0309600b40200402140141e0080d1002070f9000c0940c3e00300b040070314003000421910b108056074251018403c0d9041c41d5190143c918019403408202815000120204012612a042c2200c180050004107002083d1700040c8618006000e0914074544c3c151041c0170014a4070100320103040c42080107103900c044502c00c918008442c02c480c0c6211000302d00c0380c025003e901048414a00141c65400d0342c081c018481101c52a0b000d8000d006107180618a4132550103450b440e401a003610500712504100750003840a8050042810380065415941180d6443d515880c5401807600740d40c0d1040a66905806405401650601ca0380304440c200b082c08400644980c4010240e221b02050020000e6007499011139010f100d00c2142d0341c1c0f80b01c8070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 951149136 1250 951147886 951147893
    0x6060a12051f06050406081903110a02120309041503080f0a1b0b22080d050619080a02010e040204060c060f24150905010f030b0303071709030721 64
    0x20024503406a0711071168031100079030310504110440b001091080d010401c0e905107414003080c0c42d20b030303130000d0905d601c486c00b0394520102030314004240c203070b041c83c10143d07002c0207404e5240740000e03d0902a42c8080241c0c80c01303403a02d030004020000c0100585050240e04e566820a090100403403201078011030040040350b06c001d03504801449005c2190610389100c2040c00c1050420307400f001c80480d008450041803190165a029038059480d03480e03400310204000c2969220342501641c00315646090b2a10701044960342c81174454200c28050b10300d14002683d070345000703541c0c03140140d00c00d90124507a142c15070a981468003c540546011361541e9030040480e5030b0340c000a100c000c0740c0785006a41ca100b0009240940300c0c2402c44028220405942c1d60300789403041c004501c00e0601c060a00c000b80b44200440d0340c1100c05180e4403034050400181c003e403014007182c00c511550301e00401c200d02000300320614100044c06800070510507002c503a46a074541e02034941c0c020400842c861052442d00060000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 951150386 1250 951149136 951149159
    0x9060803040b0a0c060e060712110a0305060d053906040e0402010c0c0b0418020a090b1e03131e0c1a0c150609101508070203120702011d06060a 63
    0x203810901e403030b13490071081c1e441c1c1c00100c0302040840b000740c0d000b42d405e1040d032a902500c0020070f0341010300308000c0c910500c18412900e10500d0b01d4a0241929000007540300c1d50340207101d1408503001000e43e00540c01c103401c2e122990580182d60422020110714401518004121401d052039000c5c00709854181404511b508100009004a04000e1644400d20004110056044c0140b110a0800307894600f4000c0c0214405000d22a590149106015546031650300c400c1650450b2802c078003150752030014400e0811000409031003030300a80781c000140085007156440e9020f0103402804440c01e2040506450b00700300340c040e071002d030410800c181c0038421480140043e005112000558a00d498908207110f82002000c007201d2004070140d80800a20303080c440c003070584c003168060a082c80e584c201144c2151251008500c64100100b12002842c030728000c004855255589000c510500d107080f610007400b803d0b07103580100f0001c0f0400125110703040c0c0080d6036801b0740801070551500d1401c04209445 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 951151636 1250 951150386 951150397
    0xf010501021e150c070636080301050607030c1a010f09090b1501110a080d060e100b0f07240f1109060c0114072d0203090d0c080304080303010e0109060803040b 70
    0x700503c20016480021b01a00c900c5c240508180c440c10b80b08081c1040d8680014160700c0c1c8800c1310060801494001940581240e0564108840044c3ca0764040d00b8101c616540e56180205006210120403a0318030b0000b0005048406040c50002240d031542c0081c0d09980025000804014800c0007141d5010416103000b00f154206152a070031241030f003140d2603c1c11980c00d5003a036048000145c04201002140a4580a860340c06c58841c03007030500c10940c034040861b0b441144840f010108401c000300200c5d004480c500b030f8218070585221080c0413a10420f410599074110540d61404043c00003005180c0220107012032580d0b81e1508100c07002082c01240c1d888500701a000355aa154840610414203c00c0c9000305a55903406507600e806614903000304418940c1294840070f501c2c190550039071f001040ba140501c040e200c19045240612300790121030307202e1b000b0242a0102243c00319085200201543c122880007564001c10f0341e0358180e50003110b00318054a0226001000140400041c00c001440d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 951152886 1250 951151636 951151651
    0x70c15090201051e0d1d0a031d0907030e062208030c0f0a0206160c1509020d050111072a050127030804090c03112505060f010501021e15 60
    0x2890300b60700307000e842821802106882a1100041040c005006480c85124540d003a0710206d60402510024032941c3d81c410004000d041041c81011030780c1401a1a039181c0790407001820315000c13403c02c1c98000e00074081007000308441740f0551000035407107a8031005190743c02030760080f06003200c4026103441c002507000400340050b03110b0410210808034204001000c000500380d0161030315090882c03103000e8401d170801c2c1000804c00c100d040d80c00403d80310b00c2d03060010200d0803000a60300c031051021908048007200050100d51901b8407841d1a20689002081000e00c602c21000c181949200c0d240301d014807046964024051400040c4065400790300500038070482200101e610013801c101c0c0140e9410700e9001112000004581001103200c6405440d06601c03180c10248000c480d80703e00003015020701c030394845a15104809210031758211006008180b0341280035111507141c803640803d6040401e108a90061107084100c400003403c0d125002e0380446002c0c054045c00d16080380e01107041c41c0261000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 951154136 1250 951152886 951152897
    0x50603150d05060f1603021c0f1e02040f051906030908391c030c030207060921090b0d0515062805070f061a09010f03020405070c15090201 61
    0x1c404a2420007410348100c140c0a00742c1c11601d0000005000c511401c20031100741801409040e8408401888200c00e0700d84401e40010410381084140340901842080a0000486050180101940c2d600100180c5da20180c6540301556201c041c09090070181114000000110409000c00c503c03d40080c2c0180740a21030941c200100e0070100c40c0ca132110480516003180907a0000d02c0101480d402110903808204043d1155003015002d181220010342603040815607902900118a0b0180d8140c61490303030019000c1020808a107003520b201c5150401690020103111001c4000a100fa803c00060342c0da240a09414102018400405484050848600214420134400058503074102801000007620751038107000c40f180d015440001d09042c02d01040000401c091008181c2d050700032604c45a0052002500281c0031042c00000040341120682c031070102c100008032200440c01d4001920b000f00d07030400c01030315109401d8808400c00c520007046020656101c1a03c82d810b61300201c0c03164010b0400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 951155386 1250 951154136 951154159
    0xc02060904050c1b0607120939060c0c0e0c25080d2316111204081005060301150509040303061802130f08070e090102090a0b030f06040605060315 64
    0x3c41c0000403014181507182d10117810005126480b010640f91540049810080101c040e00d440c1d0402e4001c1c07501d0604912113150002101004101c11501002c031041500d86164031070394000e10403030a042050320244c001e0f20010076500501249580100d0b40310800c0f5162000869003000c40020441600c40c0c0c4282d0400c4100106d203128004103850005910b00141c81c0303400803203200d10480c14200758201800705404100c80300e408000d580d04169014285a141046d600e41d405151004a07000c0b00350582d400710b00092100b8000588031105921800213224556899051508032000034402c111030700c15884c01044607090400002d50410b000f441c2c0400c03040e07202d400e1507640485144c070788000c040d40003032040d000350001000350028088040c0e016045c0c91401e415036079500f8541c02480001c0c2c01080200b40642c81c258101c03008048050081c9601c1641c5404441c2c3c1900304680000100e800240000e90501e03103071080a0036640010301450441c1c070303501107842440780022055608104020003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 951156636 1250 951155386 951155407
    0xd080c0408160e1f1e0f080c1509300a14010e0c09060f011b030203190305090d0e0109120501063b130b04030f020c010c02060904050c 59
    0x3444a40811801050581a152074400b081420005010394a01807030081240d600610300756441d01141c492003d200e8000c2d0300842220580e401584c8402ca40d00008100001c900d000881c0714070030b44d00101d80c070017100000d41c26161890310ad12000b581e404940066903100e440301100b41c28115031070003d0700034100c01d071600044e803412411a00641e0380040c2200d41541c0c501d0709008928026903c035002e420007012a00205101240140100b841070000340e020500503407141e190703501941c41d420722801018819040281d01c80c3c2c00042d18a1241095840500903140a030203068041d5004200030400600361040444211039080d04640c10010658000500c03030040c1014a03242d80e0140000041d0507180003071390400e94102800c8645c2e0b8076821200d8080c41c41e0b48408080d0028019007640700c00e9030f01d540c1450002c101481d00100102c3d00d41b0188800d00d68045a1140450035580072103d0013210314005641080a1043c025440041013080d411709091540042d90000b80f03800e0040d090140100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 951157886 1250 951156636 951156643
    0x6210f020a110706020d0e3d0e040603030f11010b060c030424050706091707060b040e0304080d1d030723010801052b0b1303020c030f0d080c0408 64
    0x41c40c500000b00081100040410184040700082610340020404d80c000a1805460950704e00c960600c07036603840c0c110380c01840c004402940381d21140320300e081c02c00140d41d0195041c00b45c200b20100000d10350201c19001420b044c400d0100b501d0305030302e441600409007001210178580c4042e01614554031202440d0702625200c0142c11204c540380055a2603d0428111035078190781c084120300080b2060304d510760101e4008080b00e48294000d28041103507040c0b8201000d02c60010400c40c0301c1040b00003429000c1c008651b01c0342524400840702401801015004a90b4031701072405103aa40d900004684641103004909281c000401215604a00b101c5440001c0c02c0000c9548226208440c0352401400c117404200c69500251013428050a20b5051002054031501040540c0600d070f4410080480c1020b809000c1343c10203076200009400c1860929884800c82c10420b80460151080c040e85400514002c21a0071a42c00f0017401015501c0000600701c0315050040e111000786d0707030200702c042030103881030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 951159136 1250 951157886 951157897
    0x30405010b0a120302010e0c01271a090f032a190639110402120c0406090603020304020603130c0306050c1e090f0603180609010b03010b030706210f02 66
    0x242043c62410700141006406d40c3c00451030703100340f5000100030702c440740c2c1c1064010b654421110414240204001801c1101031555005035840303500078640a040b80d12400000c241f03010082d118400030301111800d155507001c114424400303102445600a9a1105128000b1300b0800010a80074030003112009000362481c290308061300190706c0c500220b10b52058034803d19280b0119542c1c600b01001c500307500340301c0854880d0004084404c10140700310740f5034864050351450711241c8400700300c80c100341c948001079074050f00c00d41010907260740000461600034401d9900c01e58000d440d462459690012821010042480c100e80c00310b40303d81c0101c086071003486043e10401c83c41d1401039588001e2040e01c41450740f8036112145031401040f00000d240c459040200401d28166045074a94883c003459140b24401c2d0060144e6034801c0c04204020488150001100100b043d0001c01c190042a420305031a2a400d00030800400c500c40084502144010b5103015021012100014045462200d4400b42da02c103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 951160386 1250 951159136 951159149
    0x108060f161710051906030e0309010e040b030304120b0106092103200109030e240f0306013e0106080c042f0d05130f0602030405010b0a 60
    0xa0400006810040109801c080d1468104040803514040107000506022802c02c00348501c80c0429408240004900044d2078000d06200c0b01c442442000c5031492210f208080000742009621141c0000220840302940d406235102422a0f5018083c4401b421f1800c54880c3c00d8402000000303034445c2c1c0d140c43e03c0303280d600c1080306036907035403621500820b0b038601070b08804d00002e00c060010303101c01d00e88103d0b034140d0b42e85824141c0240394000125540f24844204a04565080000304020585c0c01405804540d40c211002c1c0e07040700305944005044c0042005000080c1010003444a214103142c01459010380149460800d040c0c840e0145614202c04c075007040d00d203e800f04604040d01c00c010700d02c4400340340208000c200c501d1500b06c0c4155103151148c6824000e0383d0301d442140303161090040ac0100d080c01c4900d0325000a070401d540c241182d02040b10741e8605441c1c9804613810301d41401315000f0300354200c035206655440580f02d8400a500150084900d507603200080800d5490740505c18005104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 951161636 1250 951160386 951160393
    0xa06090c0e010f090b0604050603060103180b1603060801020304030f0c0602130f030b06010e03061501020a0605091501170607080c161113051303050f040e09100c020f1f060e0108 78
    0x94058071200b170f40d10800354240320b014140414003050310f900045c0c9510910928001c240501104980104070300048400303807098601a04208240b8110301c00c81e000a0500e0b6000c0207111380d2190098201d01098030700900140328052119406840707460b44d5100203000e401f006180c0a03049c0d12914060450f039000141c07d502c00030040081c02040402641e00500070b003004400d80858000281e11150011701d00071001054031a90702c2c00e039100300500e1a10300d6215108121a007040f103140e039a2031004940c004450f0f1038902c0080340c0340301260501055003031468000c00303458903050010740c1c0780040101300d0302c21040244416000390384941e25074204240621703051441c0003034010500c08002e441d0740300381c0802d40c00e11050240000151010503030a90b0140303000b81c4c07a000b10030f05d8a0f204d44221380c0010743d500d95043c14440301ba100030501c10902c0d01000800c001e0199a0071040c0c0e11807040e44140229604400020302c4000c0500f1095101400f040c0d0380000e40a40321940c11558030b200380c0101c8030a50 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 951162886 1250 951161636 951161639
    0x61110060f0e06100c021201110c1e0f060703050601120c0807021006030b06040c0203090a090e0d1d010e0f030f03030f0109050f0c090117010308030f180a06090c0e010f 74
    0x318400b12140c2088040c0d4402c2400c20803c04040c2100e4190709009010b140c140c0060392600344294003000f0b5004003c00303115074031480024000d03610340340100c1100801c400c40c583c0d070176402c200094010500030310300080c000507558000180d004200007030100303041c000c031002d28103103650491048401c00c5c0b0341c0c1d0f104c45007503041c01c1340000c2c50168120340c0f9071861441c2c00c105001080701c464006034010000c440100741145141c04c124118021b0529940c3c11041040c03020807009541e401400d0b809880404444517005a518100d804422600c0d00101c12141c1104c8000300e540b00d0341e0708000c1a48090481c01d0015056030100c0d1408a44e140c8441d859080841030080f1841080c100c9030040407422414005814402e074004055600035040d4060110001550090b99018411040b040da20030b0507403551543e500e041c00006548126086040c0000c51000100c5400410101e5102170300304c0c00c0140010304c1c40780d40b50380050800d0481500d00070840000084c090304d69605007406010408003c12005c1d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 951164136 1250 951162886 951162899
    0x4030f060509061b0d06030f0b070e04020f040905060102070b031e01121e0c09021803011b02070b09240c0f01020301030b0a0513020d030e1018061110060f 68
    0x442010782080c0994000f50240907007450b03944000702240b0742c0f2401e09030381c6500300514070b001060381e98001000c4c104da14003424140024040000c0c41800140c43d0304001c80035102c1000100d1254403460704001e4400c4c0030920040768075901850f40003a060040f141c1640d118030442e64160402c41c3c00c01c0c1d0a204283c840c48080742062803681c0101303810480c0c2e00c03000750742c2d80d500017480003601020856410400c40302d20031720006104200003401c8104046541d050140300103140c600002c50182c0c000e6090841104444c110300079900c0000441d46e01a003a0207040281e0100d036a40b0510a4540c400c4103900c2100b60a5800c00780300c200b456040b0030300756a61a80c010640d0500c0d08111040072240d00c184010404103081300c40592b4000e003803c0300061280e0702c612910701c640c0b0304403101940089400011104154009040341c88030761044411008100c0c00785402c64641c000345510b9210241c040a00b086901d000d1848040c0d0713207030f40c10140ca00d06074560030144111442980020b07030102d401074040105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 951165386 1250 951164136 951164141
    0x307090f0308121f0303030203390f0c1c091502030d0b0d0f0606050a05042007050a120c0c0f0b0a14092e02010204030b0412020a0804030f06 62
    0x5003455085210000e00e10740300d0003024060079801072002d0740e50500044140c004050440010300ca131264900700140c980c14010000e4000301c03801c40034030303140300c880c43e8240c0d4800409484003210a14070034490070f40009101016044940c801e83c22400520408541c507009211002050072544004801c80e05203030002000110141d12100d0b81410070708039003142640c0401190816401d1910200d54a400400440c14188030314101802d64540450800c0400030710790400801c07280119000302401d81c84804001c11624240d11842c00480001d4100c030b214111040a014200e0040c1c00703a9078042069200c00000105903088040000c08424100003000000d0340c1150160883d112007512042c00d004010302640b040a40b00005d0007510b80c6111000200001202c080500c06403210034000401e0100301d500300301c1c210f034407010b40a0540d030381c03400b0501c1442a5400c0300d800840105a070748680d251080b404564012140c1107004d10302c80c18001c94036101c010002144a0103e905030a88103003091003c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 951166636 1250 951165386 951165389
    0x213150f1d0a0e210403020901060f140408030a140909100602060c1206280909050c04050c03061306050a060e03060708040203100e10060b1b0c0d111c0602030709 71
    0xe80e140094a00740c3c3d41e40044e90540040744034024406000d002c110010f228055640000d5008007444004036845078481e400c04c00850960b10303850100109102c40f0106400759014144180d4414002c0030199072145075291050b04000900d545008445804503409060448144905034035802041011070350401a040d400041c0c000c116081a000d0403080c2d404c0000507103024803440742c3c0c8a100d40d40c040c1e115240140d010148883c0039202e0707910302c010340c06404185000d641c18014203414800508007805010300c59642541c15910350b585480800ca00c41032446a20741d90144e540e400070030703140c65801030b4002600f01030303e50700159818a8105031612000078251020041c81405220050310001010b600301d003210440416481c608102035407800c2c0d07a21500d00303c0c4906200e03001070070703240b80402441b0305100e614108519003060b4041130768031074420200d5500300c1000810b86e00810503d0038480e4840074001e10100f10407800d840324030459080d80505039105903000061041040d0040384500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 951167886 1250 951166636 951166651
    0x102100204152a051b09220302030f07240c080402060f07020406170f0d020a020d0809100801090c170408031506030c03040b0604090213150f1d 63
    0x149410b041500102001e200c104401c07043c00b0300420340418241c0c401031200103140c001030400c14065400d0415a07a0f03140d401d900001c0c007001c550664156402c0c11814144070f5104000000c04003046400c58815940c00d1100030780440c002401103002108950b0001c1151a00802c400012131a100030580d2004507040d01da0380e000d80c9082c0c00c108034150000300d415405601219125107800a1403a150700394030030080c00035803061070b218002c03035049034840350014608030800844041075980050145d13034102c81d110240c0507a10034007105005140881e40082514070500d030f00b60402000a010814418006c01080d01281c0c1280050020030103622038104510010707c0e20541100000f02c000c1d140c0030024002620464000002442c25a13603c0b074040004100038000507540e140006103001243c03c240d80c200c40c2c0c10b4032003011820525250052201c403940040600ca44148070002c00300081c0380b4200101c0c95100c40d0b00303001a01c100c408020340010100300c05c40d00032590a10104050304580102000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 951169136 1250 951167886 951167891
    0x10503060c041d0601030b18090c0d0f1e060507050711271305030a05120708061005031803160b0a050f130c052d0a03020105180409080703080105010210 67
    0x100250a400040703c41c2e032180c0c4002030314064071039000481c00b0740160003c668101807150710900700c81010703034070b100d10490703c440c01c0d910003c141c101000102c030082c0350b007d00b0182d03070700d0444130201c0c0103601d4082c0440c4100d44502c24489442d41d0302010b83e14202c40400201c1d03408246802400100e40000c01008011911140d5590051150845100000c0401c0800b08000c030006000c490116403a651003640200c202c03625403244001c003c0240d485400c80034a100560008030702c8240c02503501c1e50003100014500d030380002113414115015000141425002402c6101d281000b0781e0074402480481d120540c0c10340900c503142040c139400d22006e4800420b00c4d20780380410100c103a0a80303095400070b400715101c2c2001c3d4a00d00f000000d1140301c0d0011503110400d55840c02003143d10030042132010358a5440041511218020060701034410700c130181c04640208155828628000801d25a0700c400910008803c82161030701803154000c08030440200b049600148160760701040702c20103225010405 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 951170386 1250 951169136 951169139
    0x501030b09010603150c0306050604090c0908120a111c020303070f0e0a03030c05030d1104050a12030e010e0a030803010909140607090909060f050f060a12020105090d0302160e010503060c04 83
    0x10450400c45d50300b1044c03880d80ea07130000b05403000e00c2070b0000d000401c1e004214a80702c81d1546168402450b00a28500c04228140c400240e00710011403001c40202c0c84480c064100f03440c82074269040344250401c00d005000d02c80c0d140007041181844554842c455600135610307458041c07000b030f28000582c1d0350301003405050500841c966650745940c40c10b999141c94070081c11920b5103042803944c050000c1075001c1d81d00300703051385482d15002c0025008603141200c0c8004910b966085100c0c4e48a0980e1002d0001600c0046049855004020040c0072040c042c0c501840103590382c031940d10399002078010451881d200c205540500c88061222510014504054801821b000b04044c0a108091054182c025203942091080c800755038000015540c40210a01181c94840c80022403410f0803030f4030341d00ca00c501910114500b03124034003041c0055410307120586082042c0040144214040380700b01e00f10310070400d6025804000001500042071210400c004650428003014240701001b8084200b1441c06d200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 951171636 1250 951170386 951170393
    0x2150c06151c15091202030715021606110c0d0201020c01050f1e09010212070c02011e090308092e0806060715240b0a0e0603102105100501030b09010603 67
    0x4121002c56842840207103030002c60240c000190414400241a031546514840b08641e0080014443c040c49a181c10507640401c620a170128028410b000c0349040c0d6800605000a900d0391000a964000e00d048038142201c006850303180c40fa0000340307070005035008074032542480c00034010319030400010024141c05152075883c400d0312507140048003842040c03031004202100d00a41c101c424465045a2214192802c514082c0507800702400490005110100940c0001301031602c03448500146c4ea80c2c0d4a00360f00d140c689280f55000007070310b19404000513a070327640742122245a003114078000d042440c4034812100400380ca501401442079019050401183c2d00250720a24088a01800e680001070800d08181004000000c0010440c21106d81c1c00310104614042602034480d255003560f0f610b84420b4060140700340303400140d0380c4d145406080101440000d2183c1168543c20012102200601903035031a51131501080404401c1020780d11b6005000380580c01c1c55865005000348000d1202901d5940c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 951172886 1250 951171636 951171679
    0x121e0f050609061306050406060e09100b0a0c0507090603030e030d08040f0b180a060e0c041e0905120f03070305090c030a0605090705040204030b06012d050702150c0615 74
    0x52165111310381480214130001141da0220b009080c01030000c004403502c0c1e20f0040c00712001483c05a01c40c0403808000344000404220150076142c101960070306003480c8010660b1071a40201084800e4000c2c41000714000c081427240d41d000714080e60782c09840f25251800d150a00031413002c4d510030009074a0800c000704000449803218076502088051560f1f03030303080c85803801c808412103d0340c840c0146110030090040c541c024001704581101592588022a02004100c0f02000c6450040d0441c1c42180c0c08914120b03800b400d40c4c140900700707490019a00013001e00e0564400c040c0c00581403804418002d20590600c10258054400001022180c252000203a070302c100482d001440c20740c9540000d090408144110001444054000e544450b140c0c80c00c1c151401d4112001400611400c440c428640800124001203482c00558000700d0244030a0480d40c1c2c0c1c0c03141d1016a04030f074024403a1041541d43c0e000410b001114000500000d00380565101914640e01010030702c2151900b0320b00c1851041c20 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 951174136 1250 951172886 951172891
    0x1203070506070c0807140d030510030f12020106180c0906050403031209050309100509030c060702090106031802060d0c03060b0903033004120e0103110307030c121e0f050609 76
    0x103043c81c607012440b51500602c0c0c1c1c8500280109240424800019414400628400100c0e52510280600d0780c2e0512a16250840c900c0702820030554041c0440c0491035018010881c11704510002c02d40684911060311204851600d000e5503e5494140d001c403682d0000e082d00141c040b40c030f051443c0c2131840d01c008082c0107800c00901c3d0010740e142007007810400c0800444481c0900505a1109141e0f20704000e4170541003281c00d18000e0199a8030940b0b1440d068040b140c1c16035005003203003016428040124003c251035040c02814050b924505d0001d652000d02401d0405089100484c901190389401810f5400603481100b5401c0140305e00c0d43e5980d0b000c01a9080c10301c41c03468004080c00142500360400c4241080c2c60240f0858006010a1004a0a0b034420200d102c1d00c500415070324180044003201c0c40c3c44201e080310102440030503800e52107a040b07891010b40c80c2c074011004a071190846000c64001000d1082a030008001304e00d103412260099038a6030306a80001c1116141c450041003200400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 951175386 1250 951174136 951174151
    0x30209061c090203070f080105060406240c081b1e0706050c070909060608060903030903043c05040b010203070b01050904140616030f09020121020c100b1203070506 72
    0x910480780e45106282d4408402160024100c41c04143c1d680f01e040c1800340e280c0102d10941d403c000005405050074090b00d401c640052502101c6888101c089490081d1110101030403c06030100440c00b084480f401b90940313403090190791072039020514a4a242403c60b01c10407a000e0302c440d000c43e49880004c100107040301d03020700388140c2c3c1e4201c19003264184802d5400c0103031558030b001401c0041c4503a035480b00040d0354090044440310744540408039501d0008880c80340c0c80c0d0780304000500030040e01030690460303202821340030500001002d940804444103200f681d4024110031000704040d10300f90040080c0081c003800614a0300801d910703550f90a4605019450040340103402003000c200145000c460507046090943d503d1303082081c0e050344401525001d040019003481a020f10100092285203c40d9905866840c020380c4500d1104504c0540e11507886800c1e5030a00100c2e0040030b0078803030703004450203410b0300162000c01c010030440215601c102c07603803a560007400700c000064800034149421021 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 951176636 1250 951175386 951175417
    0x5070509210d140c0601031b1a0702060f04090c030e010515090408030601091502210306031b040f02161505010612180f050a02150a2106090e030703090603020906 71
    0x100c86088110703100300d1581300079520914000109200744411045561441580c2d07180442c0d60300c0360440e1003c3c0c12031a402172140c1080000e000186042001803500e14042c0403142e0030b00e40e031940204104d400a080480c007090319110f86120038042071041a511254100d03003958000304c0742011071a5940c1c01000105030440000225045038000d00e0f40000800081041007454072400300c1c003d407250140c3e40c003150006030b40c034907042e140160345060301d100b0080a0010a07009c0421002010129801b500351a08143d640251340c03050051030008003809140c1a81151515034146002081c0032442c0500700d2055181c000140b00140e88105024609031282c2004a04e200240ca600080304480c1c0c400106245c10714482c1780d0030080041110b11105008541d045082c1200491150741803056241200001e02401c0740c07100342c0464000b0418005014000000346103494000c00c00c00c0350001505030200c2d43c0b003c192401096480442240504001d160030340c103081c00840481e825003e06111100c5442 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 951177886 1250 951176636 951176657
    0x60507030c050c060a0f08070e0d0b060411040b040f0506160b0408090a092a050405060a0c050d3606050f1905030115020a3305070509210d 61
    0x20403c04907005400003444150344000305e02c40613054401c51300c400f030301140400d0002015140505203c40015001400c0861001c1c5941e842070010340c3d0081c0200d501c6a61000819000c428150161001e08003c0301115621801e081e40d01039010540d50015100ba201003100c000c4400091003130104d19036205421040a88861030a0780075030195501c69900080c607003e00040e0039855811040035589550030440785410b00800343c658803c00c00c007802c0040b801c200001c105a0034000c0080558000901d0051b070000031507a070340f81c1000980c0e46d01c200007410243c20540d41155010003950403000c2c40303c0702104950709401c840e440400303038401d1405000001c190161680d00e00c104031074203c0c49106e504441c0d408200405003082c2c0003030054641c100540d02034800c01c1400010713804262174018641c1c0520309455950790340c4800203d000700d025480e0506003000406a6401150300440050b180c941c0c03500c1c560401c0c485014000e29a0b400208840342d0007415884c00811a40524400c0d8036061600702d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 951179136 1250 951177886 951177893
    0xf07181104230f180103080a140c01050a1d061506120703060303020c01020307080d200d0c120203010b180a121b090c0801060e010e0405040b150604060507030c 70
    0x9019036804000e515040456004250ba04600600c0e80c0c50821204045a2442001408400c401c00c1c104049100e803840d005101203940500502020b2019282c00428184a5100c030720141d007120181c81216910382c401e01c100c10381c240c06080c5100704d003400000070b100d0031190350594804014000076180d240094801d03038035480300400c884141d501401802e0351410900f00060042900d40300070340060141048211141d072011088420395074200d039601c0c0c20300450fa203084000348882c01080320190340c600600f180e80103041c80500703009000048000b40440002c030018000200600000c05030a20400040c40410140d1040d140c00303200003000c80c0d90300f1400c080401c02c00180d94010f044501c80f44800c0350100400710b41041007044400d03d130b048003155138800384c0c1c090f14254608503021941100c0140701c500c6c0f00344600421020305251001400b015003011408440e0241c03400d554540e410b10030000310a401039000c0c10100026a14186005c0c41c0c04402481c501840d54018108682000d440e005e1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 951180386 1250 951179136 951179171
    0x1b0504111c0f090b040308060301050c040603110c060910110405011b060b130b12030a020601030b04050703060524010906080a020708040905070c050f01060b040e072f0f0718 76
    0x700d1241c00420800c10103060002c0e07102c804179011800158082c1c0001c200341818018a4014842111f10b5814a81001c0099028003520329403c1d034518814041442c0c2d01c1c1c000c000c511b0290030560060440d4080c6000001e00703407150b0340711202280400300300801c11664031001d005500800d140c581c04503510580750190141c50240c044a51000000340780701400d98484e03101184101c0c00329441c4030b44041c0f034044161203008052242d009a04a6401000420042807143d68014408d905880f0501e449540300000c694055907441e03170140c20084007504101d003900001c01840d200f4204001c0b46403500e40d000340900002030100d1030039030300403448104012084060350b01818804400f0f10051030080402030129160300025546403207040034450300c050341031007580300740d6007425042d81c5454141000c09001e0500a044c07030080000c01407081d18500f040c1051540904005600c101d0f60140f02070116140048102c0301101c0341e00220340c204040d00d25403584d4202c0c2107941c5800301d45540e0754001c03a002d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 951181636 1250 951180386 951180401
    0x108121c0f1e1404021008090f150403260105040c020c030a1208010b07080304063204121d0d0f120c05060726090111071b0504111c 58
    0x840c141402d2402550040c012400001295840700400901100d06203000080c082920003030b42080070301c60401d403454410560164408040001c4070240704a110025140050185424100072000014002010360003142e120500101c54040b442a0384030001e0282481418402c20b4030031507a900c9480c04190082c42035000700b62006058030402c510500744609003c042d15800c10029000000100e1804207810a5032000354208030301509565907a525030000b0031484040103503002500c1e403080a140c031055040d20707500b08221544165810030b450100000c4204905140a101281c1600305e84045505d001c1e2101f09022541030890442c0c5081071440b103080f040003e80148440603040101c15000750040c20f60030310a0f4120f0b04a9035503014200c846207100b110001c540d0803d4602c820308035245449c050380001400c000010a038107a920420321607400004110341d000c00140c280710000c003480c82200c0081c001034905200104010414a030b00e4441c11000b804419291004156500c0d0654044c22 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 951182886 1250 951181636 951181661
    0x1101020d17131b0f0f0b040e04080d0209060c0a17161104020c1603030f1e0809070b03090a020420090d080c070303200705130c02010b130905060108121c 67
    0x3d48540d19a010141d500c1c0080c001c0c10071001e40d44200256810030f2604850858480c0c0e04581002d031500d684250003584002540c0840036004d100c2140b0030f03680c0c5401040c58164900041c2200c00e0940f401c40d084031400851004213107024010121040c010311211166140c0c8401c030040d0301c07d00000000c000b8050304804203c40d108841d412058140700038400401d89009485101050b03950210866045c0300814045a103029074007540c4205a00801c03500d90400801c80640d1107441e22040125400d400460f408503641d070003240384e9405d5003064400c0c1900025000141a1528410480070020303100384100207000b284400c400106114030071013030760302c4215060252541540e47e400d00601115010ba05408030107900c00c0c1d001440013001038a4002c80d44041c14400700c64540381c0e00c8500401980e41c7d84805e55403108248041940c4522440345400c9000000040d08c0495003009843c19405030001d141c02d600034a019100940c4290a450051001e40030032414030b0075180c00d03200a0b051042085 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 951184136 1250 951182886 951182933
    0x1f05010e150a090e13050304050103020d1407050912070506040b09010c12090e0705090310020d2003010f0f2106060b07060e010b04200706020403020d1101020d1713 72
    0x480c0b8150384031020000710303003005086041c0f80d1240b10003a4442ea0324500014038a5104000400582d4000e0b009000e40040b42d0700002100c070311000c1541e181c0e000032140c0078009280090b03110300e5441c21b081107072480240c80b00100007440c20840031610600c81c901030100101c1d008110740300140e100700c001406d02a4410200403414800c0c16000e0004192402440c4980f04118000303040c403442401500c0c0401402401480c6005103109444000c7d40700290183d43c0545410340300e00e00007842c0c0c10145c0034084c401490350740d03503250461442c03030742c9880d402c00031850080200410440040c0e041000c101d000894085084800d1441d05c40010100e50380218010240441c1c01028400950702c02d140d03820003000284002078072403080004032660302008200481c420420b1300741d0700c0d01e0340002e03050342e40c812500145456280c0c0c00044040748068021502c4000e030420a105559050205681207003031030901c043c51440740b240d105000503000f4010044e41c1402900300090041c0c6a01d00001800c4d121103a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 951185386 1250 951184136 951184147
    0xa0f0602150a02090d1a0a05060f101107060c0501151a091305190b0f011b1b1205010f05070c08090a05040f230103032f0d0305040b1f05010e15 63
    0x46060b1106400181c80c0003980600041221f6a5401101e214000c004d0480d03042548232410071589119401101d420000328591410383e84c442000f005025046644400218224518000d400c1d02c1c181d15002080700441c00080004926000b07140449030110503e42d5122561040404c1c050b8458004102441c0e0621051003031800d00c1820b404250003104201b40862003001d0140400b2408400c402400241191a103041426482c0b4050704040d1240c8841108000388481c0e10300c21503080d400c80c40290050070055010440709200d02c03212400c00c0320703051000e85440c200182040700c07668000ba0248000080c54025030356105048009004001d05c10000c0150b4840344200501d40321454507102ca00c1c1c0e108d405108104c504886040381d07410340e5407800102203129a500784880c032900442a0500090040d001150140124025011199000070301444c00f800d09290a26002d03082100d040000460381c02c44403080c0c1c0c0f040c002d6410a0030b000c0c2004401c18042524142440d032245103a1001080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 951186636 1250 951185386 951185393
    0xb03030d02091809071505090307030c061119030c020112060f0906090209060a0c05150702030310061803120219080a0906020f0303060126070e0a0f0602150a02090d 72
    0x1d0002c8510648210040c42d02d00401c00c02c52401c1510003044507840a0402c0024810707007100b1241c401e06510308031381080814400720b0300e442c00315003003202c1680c0c07004000c1c010198054000b002e599001002040e02d80c03507040424608c104070100c058200a00c0170568025a400303841c44061200210100300151a52050520210f00f054010901001d003081400608440d05000b130b2480440c009001901e06074021038142c0c2c0381c0944c04402c45040c000c101020400702041e8807124400d00d1140c002d1942d03854041202005010140c1042087c081440210300b0a200100c5400b010340342d010500c0300c01d808240c070007a4541142d8030000342d240500d6114020800a000c00600940c0205480c4c58500c640c40c2c060aa0b02c901d032808034101c80b503005000007021581b140c0c0300c0b44452030b400042000341e4051008080c015040849201001c034080510b141118104890414003e16049054074080360500038000d4440b00456400441003040c4004200c060826504076004014010103919081c8054517 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 951187886 1250 951186636 951186641
    0xe010e0d1a01090c0302040518041a0a050601080a06081c050c070303091401020120030601212004060c060b28081207170304050f1b120a050601180b03030d 68
    0x40c0244072402c288401300c80500a0003a14180c9800a0100f10b0580ea441181c44030944000c2060398440511481100d010003c010304c0c1303001d0302d4919000305151130920b002406050b0003902000c02545081400c00c1691004500c00002d07424010481b80807060b200c00c00c48403401243c0c01500e06005204c000810140c21085070300468030070a422840c6002c10f00c006900301d5152000b1403040e500b0351110b10800c0c9468800965004105040c00c210580c0440101c1100850300c4011003e00d23550341a101103c00d001c02601c1c80ba00d540d03002e40514280c200b0500902008000b000100319540302d68115030b0076504d6002c524240000702d000b420700f03c202e03c2c00b90304114810340f18001d124028004912109808401150103064000d00003070303003084a60403240c10304d5200400655150007050f2031501806400c2c060907a41c28007068101d0314010745201008082e0540c406004110f40c0f04200900004101148540c1100c1441081202a400b0240c1c00401780c8ac2600c10b044c4d0600000920640c0e048069 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 951189136 1250 951187886 951187889
    0x30905190611120c070c0807060e09131101030e0a0b0f01030b01080703080901050f09150c0d020f1c0c060903022107020a140103020702210d020703030e010e0d1a01 72
    0x8034024440c0b540003a44402d803070320a901180d1190040600094500203620004120a600c42c1100042a0765500c131002d0502885400480000f6214035000c8076928201c90740c240c0115148252200120150f80e0709802c15901060560506403104203e800c015000c0c09880c100d542c00c0f2012204515010b9101d00721650240000c40740b041c0050004501400c00080f41d42c2aaa482a613403442c0041201c0107480c2c90f08881110000c181040142da061620340c001000850985481c8082d01c0345407040095040a5000c2e07054002c6520643c000d590014000843c03201c0c503c200a40485140c40c01030003198542c4034014040c1210342050402020187d0008540c84198215001d403009a08041140b814610a07158003039480400e440c3c06000141c01e01d14020072032a41410300510341145580810b44480e10050708202a0521080d070382c3c4080b074180290184000b551002d00300c250300f150750141254090650590400c01032071503040700c9403950861808d4481d080036a602c021103442c2e00030395124009 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 951190386 1250 951189136 951189143
    0x127030f14070e090a061d0f010f0b0d170a030e06090a020901050a0b121005120a170f0d0e1002031f090203012105030d050f0f0c0708041503090519 65
    0x95050010f82d08600c0070101e030280c900d02000c3c0c8280d0809885282c06485401e0070791306e003551054650051502c3c104070700305071548800008654100d121410404880750006414000c0c201d800240c0b000404102e41007042a22508a4980340d40100400328014800e0340d18406141c0320341401d00880c54800990402040e200b11210004ca0703886000348000b41c00d15108403051180144a4601e40d009544d5029038041f01891007130501a6842c1e002030800c0d20348a054408641082800d2014043e01ca4030842401054a48040c54050642d124190074070608100d600b40d10b50701d400e0081d860384240071100e220702400c80207549030f0405030f081d101e06850441861001440b00301c0e0003d1744802074000e5a048421040959117008504400012040a55803040310759001c10424100b002015208a5001e00145016000c00745040904440341000c0a045802445001e1250100245540d0100c07070517100c020b065090b031a1112301007075001d00701c0a08000c115008000d524100f800c803500d40076104500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 951191636 1250 951190386 951190393
    0x13090219080c06120c09190b0a14031005091504060f06020105060102010912030b150d1b0309080f0a120603050f010f140402010c03091802040911090127030f14 70
    0x400420041103104400e20985054401000116402d217800b0103040e032008041c08890f4003140350b808150340c805083d001441701b44000b09211400705d41c0880c0c115031071007a40031a180b450810381184001c05c241c80c800c3c1c038400c40c90b03d000103c003240b495102c00e0030701d10701800500c4041d44603000d801c0c214241c0e0086200542c43d00c00001c0e0301d9881405070881d0207800500b9040081580c40049000d0050741031100d401119240702e00c03050340d68000c000c10440300da80000241c88501140c07001d40c40014101c181003014204420000400c10010464008407000d407940c550380c01d410001070303524884080e0205078040c40d010001060010210301c2c11011002d450080100700742d140e402500f1120165190040171165a0004005500840541c405e0b18000e003003031038840d59944185082c040118984203845500403030b08000c003000701e011320b002c0c1e00c45060754075091030314000008003001501510945041c4071030a00821018201030740c1c2000e190007070b01c03800008aa50403c0b402c1030010500c211201e10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 951192886 1250 951191636 951191653
    0x2a0702040507020c090f0a09080d06050f01050a09140a080d08010305060109020f0d021803160e061012050403030b10090e010f050a03030309030e0907081806060f1309021908 76
    0x140b004c66010b4294100030080ca1a0780c482c107800300050280100300015a44e40d42440d640401c4e000702c041e12207251240c0010a1079403c1c00e050041c0c90300e0100301b9030305100e0248200382450703070841e059005464503d01002c00c1d001504001621646040e8824405409000100007000383c0c03210403541030f81e000d1000c51b4a2070b6a603055120032841031500180d0b0b00711040c410605070702c5280d0000d2026240894051940109480000e820300891060107100c110b003880c410003000d50001d00301075210b14115002061040d00c8c0350050000c2c0e0406095100f407964890005003058040e81c019183c42c14054504203c0108400c0042c04c10001030085030702041000740000f581010305203481c070961350054527640c805891923400703401400601e41c040f428404400c56080d125151040140d00c110300940e5180070740c1c1056500b80c2d540360b000c041c1c8000346030041c404212590701c80c50b205640319001070398070844400b82c030034070741c40101400c4000170340c045403442030543e4140381ca441d84001d94040d68159801903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 951194136 1250 951192886 951192901
    0xb0709060f0e131d060f0702120702191a04080c0a150503040c231c03022d0102191b1e0609170d0b040501030b0105092a07020405 57
    0x180110841e0000862a00280000d0300309000140c0254091607000b003220598140d8034059110740510400007a07200d030f0200300c01e0540701040c0782d400180c5c500280c8000c1e0002c080080081c42041800b034050241002c0440c0a8480901140000c12038410440a0712549560600d0507510510889149100d03072403440145240c20101001100d0005402c0020401502c0b010f82d12504000d2060702c1c150040140054920311102001c515000f8a86004002407624002c00a00181c80c550365040401100110300003c1d0700002d24a803018190a0a143c07076410350009a80390015081c0c1d400d40950010510b0100c0c50109202e0340034a03120b544803100000c0420000c2491000301500c050140ca91568043c201d1110300d00f00e41102ca402500c001c1602041c0e0384900542d1080d0548210002c2e000107502c078081c001501c00c5008803a000c40d0b052001e5455501c845800010601900e031055900c000410041050404c507003000c00807002811441409060340940c40b40c0040800707a01403070030200010280c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 951195386 1250 951194136 951194147
    0x1052209081b0c09150109080109050c100c2607020a03120e01081009051015020d12020f04050f0303120403050408060a0b06030a0b0a050d080403060f0203070804110f06070b070906 79
    0x1041010f0810300e603942c0d03102c017004139a4560b0400641441495100401c90783c0c02030240c0c2c01803500501c001c0c0141c3d60b85905104001c422805c6000c1000780482100d40060050032400f0000311120044813506540040c030034041d03100b001e400a50000d0301c400000100701000106545418042d2600078540107494015200208111030600d44040b003094103024022031580155004140203046200e603548030070a00d0380700302a4807502d0026900c4100d079811072a80c00b43c42c04044100144080d4100a140f00c508169409940507441c4269464032413644251004c1040d14440c981074244492142800d04000d84158414007800d4800d0040d8400a615459140141c1801010182c68585190b40300d40c01e502c000c265050849600c52104080041c4035500e144a019825004422550303999240d464824100e4404140c201243c40c01401084000b9400602e400ea0007504608240380b50300680d400101f400c1481c0c1540c0798005c20210742d0000303100c501203900344262207a403203103140d046d16a213060b01c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 951196636 1250 951195386 951195403
    0xb09121014090f0111041215091a011707030201080a110a0c03020f0d0c080c0106080d111b0d080c0a08040303051c0501080c130e06040501230f01052209081b 69
    0x30403c40810041240d00f5147d24003441090154484440311405098280251038000c8016a460401c4c0c40d007400f42841d2642c2e24600514031140300c0d1031050741800540341c5450030342c48081d05109038440003900300790903070b000000f00c12014a10380d41d42d0700c50510060301c2610202002d400501c00c82d80c60000714140054031440c0300001d130302c0701e84214115640d041b4155000c00301c00b50b40e9549603203000510100c00c006e0121201c40540700d1000118020303007550b2408020991348040710345594141002c1341c48090304101c0785034101d20480c0d5199803131001a0710700580e00100a040c82000a4000709140d4014090b160000995003003c085060410300742045e11020300401050f900f00c07450301c2032149000003083c0031001e002000401d030002d802000c03a050020869064071665102d00400002224070035103015145613072065050103080140301003a410405000303840c01040662000440094a801031050500240c02d003032040c04054a00002c0d42e4200801110351240070120300302851101245519 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 951197886 1250 951196636 951196661
    0x807150b090c03091005040c08150c04050904211d030a240b030a05060406060b0a0909090804051e0306011409040f17040923010b09121014090f01 64
    0x1405803203005900d8aa40e00c064442d402510072000304c0840100c942c01031b0340c4194000c5c800c01a409250100171410300c1452000703180011400c1e402c0141e0801440162403e995050f40c200100303507624039150b1040b0a003d0060081034040c0c0b1104054554424180b241200e42030103401a019500018940d54198001d8001c0c89001c1c602d016410b103002d0550391200c07081042c2c0000c28008868004a800c02019040584c2d0a800000410023440030074091a0024648500c01300d18281c40010018003000c002d0064000d0942c5900b0031100344420345081e14044e00c0e000b004031003e210b076003140d80d210f500082d69141c00381c02071800004049056a009124002d8090901d90343c036943c95945058814070044100c43d0340034440d42e04e100e5045500c000c0d20140075440e8ac00200300440a002c00d0400a410000c2400c030180940184801c000b00c005655400c0c1c2c00307403201c0e10801070b8100a98100242c4a500c0c005a5280400c0c0c05061106a969207024103c0d801c241c940107040ca154040c280c400001808 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 951199136 1250 951197886 951197899
    0x10f0501050a0f0c02011e0302031807030b0c0c030d0222170304031b15050304150b06070303021305060c10060b122a030a020a0f020706090b0c0307020d0807150b 71
    0x1902182d0191303203d040401c0c41451302d81c1e203030303884014007441e011748a00c0c0c0c8000099020041105003083d0382c4404d4219030160004120750f510355a2516200040148642c03403111003c51803420300b00b0300f00141d40c100c1c3c0307401d5025034a5000c00382c5d031031980c480301e41c444210703030315082500085401c6940c96080303200403890065403429095882c0e05050450703411500a01e0840c03244005410000c80b00d0038030030b91000f651025a070f8141400c1c00710b29400d4200c15016034500d003948501ca640d44050071100b010b641810056200c91041100c41009402940103503040340d000900340600c1d900100742c0441031480c05804202c0b071502c802c3d6203400350084002aa180c6e100354070104001d400b0481e8800c080f01811180c8a08588030048100c07070f50341054800448264011518404807900003a135092062a01d1008047e11071400600902c071605911850b1620480002e00e05c1504c0c20034400c82d06402c0e0040d000c102e18281526013403140c2c3e070041d5020f48420078004884801c42d01c0c0d0740100c2e9503106004050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 951200386 1250 951199136 951199157
    0x50414041e0623070c0c060e031002121e0601050d090204020c060f0a110301050901050d1b0f090c020c180a270b010b0a02070b0904290f010528200105010f0501050a 72
    0x5523842103c0220b0f83e0b07030602c034801c42c00b4102212400107182c0d194192105080608004022810711a15420401e40ba2840c4008101182c0d900034241c40d809860920085508410b600104000303208610116900d07000b4a41048000c5100e82d2015001d440300403803c1081c2d016500780100030b40003c4c061503a2240a000040080d450064081d803001801740b1400041c48038140414444189294800c1c008405144010070108586200700c2c0108d0078540054810a041e50740040c2004a5a080304824150307504041a009840390780412501d031703540403041140c00c0c00921f4013110a2441784045540d40314840000c180300c0b507000c050f80c030480d40a8005050b01c03410000b454031a81c2021190541146d40c07980556a040c990015031341c00480403680005200e0340c0764090180d5124280071141c1408020018521b031400310100c00b0200c01d40345a8483c0f404c54800004450004050382c42e101003145030481141c0d504010340c03080d81280c04032181c0c501500e40e035030011345e144e000d824840004030306c2c556071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 951201636 1250 951200386 951200399
    0x30c0212070218151f0f120b030d050d15060f0c0611041d010b13051306050909070f0602070501052209020c0c0a050414041e0623070c0c 60
    0x1401c0401c1c4010724000000c3da108a2000e1100c80486590300c0300f007029006000c83e8200884400c00a48498182c8240316819000207014041c07102641c8082041c511040c0d05400e006034400200c0c0b030801410345840140070140100140c201c2c4070000f0081c1d14091080010366080388101c0100c415680352034500d154420000c0d589030071040c10a407082130f19001c40c1030758040c0c210010406040c01c11f909015884c1c0c1c1440405460700c058200d418409400c0090301440c1e0007400b00641103c00c203ea00480804c84244248040c2c5805d0340061341080640c2c0500c0180700f00803270360704155910240111440c13591003408982d120840d21816002c10f8042180880c03001e803152407c001b01000002d001d5180790b840407171030126800350301d441d5815000075046c0f5005103002d0340d11345c0c024030080741d00340034038111385088894603500030304000c01603044280c4680b410400c1c070441d40480c680005080203180070380e527800c41c118081d409141421000c00d00c000380199018416000902c0d40103045c0c01e484a09016 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 951202886 1250 951201636 951201673
    0x15050409030c0b10050904030503010303110607021e030c03040902281403070c02130501061701141c0f0606030623070806031501080319020d05030730050115030c02 72
    0x41803022040000d1350046455190044400d00851081e60780b5a525851420001c240e50864110424250454804d110020381c0c00110ac5030b040025030118401020380c48040352640c800d200d002440c0c4e00000c00d0000d0216015400703460707c9113843c205c24440346000c0081069400c0c658020b000401d44910120107000f8403600910350020050500301c0c00b481d0340c0e40000f01e421020030003440041c4d84841c014088582e0004520240c07a8050105100c0d030f5050040242c60a400011081e0140003a1405042d584002941c21168282c1040c2c144090080302c0c14104040e250501090b02e16a0803d030b00c11084103114400200c1104010340c800c040c40e244c090045458800180c1402d0303040c803903036400a6400c903000402500825451006654921000032107449a0140c07035130700000d54006503002090b05070030200300c075480106131a14460320b5844040c2c504103a5462240c080708002c3c00408006102055801a07042e140020609401240307010422020360707079152140d000581010512184010681 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 951204136 1250 951202886 951202891
    0xc03060604030807060f0e0a0b04080705030405190609051c14121206041107120503070216060c050c040e03071509080c15010501050a0e06090a0506030a15050409030c0b 74
    0x504062030582d42e9201e0318000e8118007015143c19a0b2800b0803481414503100301902d40303400d44040c00484010b510780e4040c00d40700410190051400103110800c0003006c0c0115805800028150300001c840817454120444203030181c200030541c40c407000701d290300d040c880b42096082d03451580c02d11607801c3d07034808103079410520243d0058816448a0318a403895180640202e500e5081c040003d8a4601e0410040d1500a2010003480d071040125002046031048580c04004607400d00d107030382c0d48918808070f15006280741d840040340601c0c000818915407040b45407603514007500449415070710000400c02207032034511041079540d00c104001400203e00782070680c1408031000380001d0030325a580f0f80c020140e011084a0300980c02803084055004043c14065024040c00c1c82e1581c1014481c19000d0500e400c185d034070303a1088030301007505c00b065a1492004805490040d10b0325449080121141e0701800c0f48603070b4154003a49142d004100c0d410f113489800034040d09a60344080d0b0420700d894020410001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 951205386 1250 951204136 951204139
    0x30c05091f140a0302121b0909071707030e060a05060a051005070209011403060f09191112010f0c02030705070b0a12050106094704031a06180c030c0306 67
    0x800100040c080784101a00342000d9a032070150381c81c01030031030f0480030040040800400c0c1f296018124244c00d100c90588140da041030380e4015054444000079240c900d0382e4491031100c2c81c41c1c58100300509500d0780000c0020407101c411100c0e562100b50f40b440c04c0d90011142c55070440e05202e4100001d150401072182000380608007a480c152940d00411645c9101340c020080c0348800c05100855400d00f000b100790300800040045001c3e051214a40351169050901d40d41020b40c42c4d01c00c0403d002070350860414010005003c8510004034030385090203813030600b04803603c0500e0144000c000d80d002000b1680340651040103800031a080441c0e0344115001090074408019070600300c1c580019003403044030b01904058503004030980c0342c118580d0360207a0900c1c040c440320003004180444e06169184c4038521841c0039911002915240c646030b40076004513031001e800c50550240f08110518441d81f02400741c07009072009503284403045080003928100382c0c0c51143c0104104001807402c00920090364000c1030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 951206636 1250 951205386 951205397
    0xf061f090b070606080609030a0509090a0e01021602190e0a0c0513090e010f02071112010e010f09020906030706050f0702060412082206020705040b030c09100303030c05091f 76
    0x46440780085103401c802c1c1e04a441c00ea648409020b071400c2040110340c00401c51004515200c0142c400030020702030f03096454003607402000444c030114201e40240002c0c9a0f480c0007191a84410b80e980c04166000d048140e0288061030510406013604071074176001e68540c80e080ca0b010b921400003080007000411107640401c4020b1022040460b0500043c4004200b8103102280c200b208460990854660789002000c0510400c10800000c20200d802030b2861021079000c02c1d4105400c64440c05003080c1020302009500c0c16000e41c9204406500815034940290380b11003050391800141540c40c4c0b074a016a0b00403800c14060104000e031002c000300f10252000e0411410700b40d803408003007400c15070914111030382500801c411400051030100009090340042c1c0340c20741d6514010000e51103a4140c01500d0248d40c5811400b00951400c002ea0040420003504041032850402014130060350355000407000642000341d5a40580e2082c5c081d2082c0702e00040c03081c0400c60000c401c56200c001c410591005118 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 951207886 1250 951206636 951206639
    0x10512180703030c03020709060510080a330e06090610230d180b01050409080906280306030b160201090506071d090c070b3c0f061f09 59
    0x103405110041c015882522802000c2c20b8918001c0d0601d0800c0d04650502d41c0f070480f0401c11030b075410880311024070721802c00300c1c10303615a200c81790003134800d83c2c0261486440da0380c0009101b005400000c1c4d4940000010580143d40312021103050900645060703610080007400b10b040c82c41d05124501807070354182482c0910442500340c610101188184009190a01103241c0e168101980142e200910084c44803600c06c50807541e6500c00e402d818001d0500903543c0e000b5000030080c1200c2203881100c0000c0040d5100c00350305010915442441207a1807001c00038088010b03046000340108401e0303e0f404802c400d090ba403268510303e17003100074004401c01c640d2a840081d003c60414030640340038044031780c1c0d00104140202d000100c04071004003010301584040d420001d010300790100f65520a5400790882d131031922503d0800c041d174061030701c1408540841500b50031701a9240300a8046503140c2e0320081c41d00790b66269102c0d003042000c0b102142c1040c18107030b00001004a0314030603903120440303007803500109 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 951209136 1250 951207886 951207931
    0x20a15150e09010605090705090a17161401020d110a0f021503042001050c1b04060302150d2009011128050f01050601020709090614040308100e0105010512 68
    0x1005542d0104203075941d580a0155042c01c4809540c0180e00d403c01924020a00012402d1000c551180f2009040c114403039050507a018800300b032010003501640600b164580c0c00c81030644140100581c094420b07403428005503401000c010761210b0200000e0040e001190321307642481100034100726807261103042c6030942c204221b000303507010f0b5004007070811101d5044c0a40e48501940303a480789042c080c041c0403504210a002410048802c180d603103507104110410040380107020745400c020b6014151347c41607030042e2070100181c240d41e480d085050084034407548440702d00c0401d0740d80c6e185a0110803c0303400c209500644e0072000030710f1032804880003480c4c4088141a10030301d04c60300210350b01041c0c0d044014014100f010764507068200c00204041e04103000080e40da42218450081c1d800e071105094028800254450050201c00d104090f101e03103403520b0300a0256000f2035a0344002c040b03030a00825200404100329040e680103855062402c1402c05203a8000c00b0018441c8165203042124031029 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 951210386 1250 951209136 951209159
    0x2070c0e100803030903040302240712090906050127050405160e030c01170910050705030910090809130906091407060206090a06110c060103030f0f020a1515 69
    0x4060031030302600e050811100301450700000754801c81140d842402400041c0402104a6040700d81c1210351015007004c00c040c42030501030200c002496500081041c100303201e1204801070000d001681e4510700c09445900d00e0b011180d40740600350014196564070350501c00b045694500640000c81501d07502c0c0d42d00e000240984400311407042410390641403010b03849400c03840301d201c4104100d010781084401900024508034680301255042d40d050741c042840349200703100b220228442450140500e1a20348000381140d8025550140b81c0c2c410b5000700000c040f10f07849054402680001050b180002010802002003849009241c889968035040000580e05200742080c0d42d108512007d944844207200a08043e1141d00810a540040c802c010411401290080c00950b219a00003140a00d84020503028002e801e50b1418512642c0000300c241600030081d14011303c0c0f83c0d6120380030720001407400c9807140b00605000b02400424278a0740184246a0800f4581422201c444098183c2d00e8138103004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 951211636 1250 951210386 951210389
    0x7060c150b1f03060e010b0a1b0f0b100603290114040e07030e03031009111213050105090102120103390906091407030b04151e05030d020a1502070c 65
    0x103040305030703205121101d4150080703070018481780d03031384a003198500321015030503203d6094103008000c00d10098802d40544c42440c200215002030600d140d4058a2404a40b074080c1030300c1340072008407080f0740001c40754400e024000e0281d06c402e000301034406100c1c072100d03103420701901c040b41440211b03030040000b481c03260050002800f4000d1011028205550082c0447c2c00e400110f0314141c00810822080d0403255484a0446846060002e040c0c2002c00425a4601886441d0800100c04205224030240200258000640603000070480c40e1101c007215802c034030070203000d45080025800104041204d24110094000700000e0045003140d801030f40c9620062402000f20001c4485001400100800d1140380041c15400504016034500500c41449100740204200101621043c2181741a00d0356086400e11aa80e009111801030f143e4034001010701c0d106000400c0c62200f03220024043c0340020341e8003074000c026006007404000ba515990302d8018294494007100d6001c115540008821680035070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 951212886 1250 951211636 951211669
    0x70e031002180d050d121508010c020606040606020c010809120a1107050d020d1e0b0a0e010f1406060703030b0603070f0f02060606030c090f060a050c0d0207060c150b 73
    0x6030358400056440e08200c04022496014800b6803400f1000180000b6a110340c5401c82d0900511020703480102c0c001034116241c43c09283c030420940004c0350700054008014004450b001d6429540d556421701c07040f20348a205070070041e40030034540c0c0102c0d4040d011181d042400102035a401340034110884001d40e002a254800040300a0010740d00c03100309009540c00f0300b404585c00b114450017600054850800c000c00030305441040605900d8601c20007074540b002d60751058003880d240c60003000c03c00040040744a03100b2154240100420211072501c5410040d169941242d0326985900081c040e0f6600040422410301d6903804070008180d480c100a14814007090341c41000044580400034886512440c54030f042d507101000740a41640c600b01503e034040104e84210341c8401c42d00700060017100c00607a009406c10400078001c44050380c400c004001307186401007101e840180100040340e44107203d21a0400141603941d00350700040460290741001c221800f80803178041d0f582c00c00140007100d20150003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 951214136 1250 951212886 951212891
    0x11060c0f0601151806090b03061915030e121204080d060b190819020c01061e0801050105100e090402041b0c110402040302060f0304080403080705030d0f050405030909070e0310 77
    0x101d1588218541840c1074242444c14080b0314180b0050b0514907140281801ca660100c0054901d4480e0300c2c1100441d528803039540500703540c69501d42504c814145031000084c0c00d006d81141188000078000304400d048a07040c51402440c000065481d40c009441110301d0f00e810400c1ea0809410f40c00380c0400382082424007503980715a41c107803140900d40110071030701340f0403c070040000880101c03107142804c425038403015942c3c480c02903a050042040d030b08002c00e83e112a64801d5804a02503c10009a48e410300007044503907210b070200301080340140000e40c0090300c580184944d508203488440e8019101510100f00f04810f500018502c501c0c0818400016115501d14024000250700c200c8146c1800e6608514040c11500840d070f541c8600d56030364511080000c0840e04102e0480308503002160000011a03d80415290498680c0d0100d0325100841d401c20810701000802c40c4207050241d81d01600641c0307443d841400380303d000400140f210040c0100c08400031035a4509001010101c078928100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 951215386 1250 951214136 951214169
    0x230303060301051e16030f0c030e011103040203071712030412020d030b061b030c24060415090b040e0303100e090a051f0204030503120105040c0c11060c0f0601 70
    0xd1600b11400249561021a031300616100c60903440c084054020b9007001950402c2180c07450705030050400603441c1058a40740428249003941c2c1350384580100c0d401100280701c0c981341034400428901054401a40c550408801040703410315108400c1000518001551050580451202c0131038208807400d8030f011314549405c1402640c18800e0041a0350740703013010031411200e503001c210b060048000c20300d0340720703c600601c0d6441c050400980f0400c0c0d0b002411614505084040c40c203104004400c000841c2c06858040303a071629082c00380c0c840240032881d00c2002149404100c8028240c5500a41c0d0441d0395030355420050740050000710b02ca0420400c403282440d01e012020400b8142c02420f414042d00491250b100003100031810000e40590010342500600c070002c2e0b00b00c002d1240e58002440c61000003280214264090f941c2030403113030100d03420042c1d00c211b0941035039800344c0e23000001c042c1140c40c980c03c20f1501c0c1c10405024480c06403411a0071880100040038a0700e807080c1c00c804103000d0303100031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 951216636 1250 951215386 951215389
    0x6030201031803020303070c0206040906030c0e0702010c120f09021e0f0d05060403110f030d090b01050108070212030c16050102040f1d01030618050a03110d030905030306090423030306 81
    0x1d07000c4114140e00a044500b0071520025181c0c0000340a520800c200c1804100555407104166005401003540800c0a03580ea4509845200f50b644170300e4071217100c040c000907c1036006101c1c0318507103141c80c1c03942d0140f1034013900988028008903c1030010250f8031460200540c40e80c9051503c4001840068811190004d041280c441026038509101380c64020240300010f8011545607002a0b06091080c2c0b01d40c000c1001c1030501d112406a69421310000c07405185a02468010b00c8071503000f60703040009a600e90004446c0403104403030303941c00360b840071000e040113082c210000c1d43d00030404c403025030511054645004144006c000d00b5600c9a4003c0f8040c00b155401c444038170000c000025004960082c40010800300801c1480064003440e41c07a80d1109030012441c52080c00c207503010081c2d035500e032132038a009000402560b108030030900c200708540d201c5a0203441800c00c0c1d26041f4008608566032401000500e800003002114168608841d0348104912400001e40c200001e0f40515180d00d007800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 951217886 1250 951216636 951216641
    0x61d0f01061e0e06030a0b0a02340f211e181202150f070c051009090e1e07080c061903020a020f0601060914151210030c090603020103 59
    0xc108840c2185200102070002100100b21400c07600110140641076076030a00013803d1500c000e401800c03480880b0100006226660300408007190b14a000880803507005424040883c0c138141d0b1040c0d208250440040410384020722918054422600c0182401380001d00034200d415096031040880c0720640c02803c0340c000b900200c050002c05290414400101c50f101610a501c60711907200c190340c416010f5410364a03884401d0101e00b1a051002d9a00c00c0c120000f43c0d036903480040c00365910140c10001080d54130f08841c08a5240215680d102642420031454000808003110a099140729000d0b54800c03000b0221179400041542c44060004c1502d0241e009003070441c0031b80b45a111341c0040094010401030500e05148902e0b882c680141c40f58940705041e45032003808a44114113100719800002d180f90302400c2d031025030700c5141c60b460303000d01520140000d20b03150501d07180002400340180008400741c0310f0400e40c85074007840d4111141d5031780d480d02d9100c1c6085420085804c1c0d1244010f00c15540c150 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 951219136 1250 951217886 951217889
    0x150b0417010b01090519030206070f0b06040c050d0c0e03060a0c02071a040909080915250b0703050606040b1206041803090b1c0617010c050a020c0904061d0f0106 71
    0xa0009112010350040004c0440006010345442402d10064550030050789000c801c01a580c0a44616519610b909103040310700132408088840100c07400000700c1504007401a0804ca000c81e89442c1d05024a00f208030025090020018080052011841c1c405035010008075000d028511000280d064100380c00a051603247c1c0c0145a00c48406041c03060110724040445d0b0450b46d0300c050000d61850310340740c61200f82c8240e140c00c550021100c1041e0596401c0c036001845040c44049414150700020602d04584444084010b400721b800c00002802c0c10340250402c80e401000101454500380d2200c05620341070308040c2102c1d18001e4503000700300060804d13210702c6240f05142d40e41c0580c6407542e40d07002008640140540300d5140f10200e001d40324415000c201424003207040300b0911040e51582d00181c40c0864903d0702280960a110444042074050800c0316801402d41e409410001c0707803001405128480a8411612280e07580c0e8040403061380300700c5403400d00c0d1800e800f84c41c0782601802c00a09403100ca = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 951220386 1250 951219136 951219179
    0xb010806070909150503030712030e120708030603070e040309150c05060a0f020405041103060f012d140c010c0e1905011103070516181107020402030a150b04 69
    0x14a081c4030030150019066011907100e500d0100780c01d060780708200d81031220399004540600c00410040d081141c0350b011001e007100c0594013082080600700045e1b549005070a0302d05510b0b003042050601080613031004550204000d0700700c0c5e2029542d00c040340400c8004550540000300d8812003403003040c0001e480d01c0e185135283e00d84560700400076201c1c0e44e1150000740945441f2952001c0b01108909190143d40042c1070044c0304004010300010100d2041e407089a05912800303004048912a42c02003582c512a103c02100b901c0b000e81c1c1d0354401d250540d03512502031040c081c10040d03404580b500c880c001c0c141c6901900010541d4481c0c42e002610390840c00702134030721520581e15820a03420300300010f40d0840d40309217000910f580c0145d160604600c205070011f44103000c0c503203c6c104120700c0400c46c03800b00d0f40c92021000c280c0c2c141041c0e8000300c0301d4110f5802c0401c10b003000400090318081d0003850b040120322100052b8015254040701c0842c0700e9030700501018001203803c100095010109070100c000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 951221636 1250 951220386 951220393
    0x160f0c120c06030b010807030b0d0b090307050705060408070e0405010f09081803060601081303050c0a12080901110904091a0106110c010207080d0825020105252f010501120b0108 78
    0x4913002806181000340f08600b0199541c030010300c29503c1410009299822802c810054281040071940341e600128080d00d1a1262090004a900b085011034088611450180c041c00d810201000c0622001070002d54096413110204a80d440c058130400a82922540c039056549902d000342079800280c10310b81511903040380c001c00c615640c200c4003d0368003035000b40042d0301c11039039803600b42c41d50b002d010081341c280d00c2951168000c010b4807031203044d0140c840303495060460360798821050030795602c40810710400740140071074040c5d81441d03041060107034841c440b2000b00b2545441c141c034141c030099004000280d00c41101e07600c4550240181c0d0396022003132001d0aa82e60030458040c2e41e0b403002c000e4041c20001c0c210001070181e94003054452211802c41a0751040c00030141d8000d020302401d5400e20700101c100c0c10644000c0b420185928524019034544140640f144441900720b213a032540e9080d54241d01444101d0b0400b820302c581c0b806403000124140040b60641403c07480c402d01600000364651 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 951222886 1250 951221636 951221651
    0x41a0c12010b0703090e0601090305030304111206010b04260109050607080a020702060304020f06090d060b031203010608060d0606050a08070e060a0b030c0703050409050c071a0c160f0c120c0603 85
    0x941c00856101a98078004c20000c085e07c8480040b02c8040b4a6840649240800702c1400208a0190342030010390008a580c144004031140040c0d45070b220a2003824620601000b080207000104420400245005644400d500c44101c12170703070948800c10012034154022000304145150042082034000405510031402d0940c80c1e030100356688400381c0b01922900304811248401da4504044802044010340088550022850880c01420a00072154420700500942c81d00c1584c0311810b07a4100c6840b559a018030b51143c409010b801b007907500c1c0c1581d26a885600200c0e01340c0311001030900071b01c988c4004081440c41d114580c0e21300f050207400d2612500c01d11504101e440b280c0c00a030fa030042c01f501041a07481a25181c141c415210356030010060764101002c1050b03040e1204041c010940c0a8440300a40e00301c0021b036105604021900781a51030700030b02602102d04244284124960b10400110b4100456504ea4079038004450788010004030100d9003403010420302003c401c00400083c1070611040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 951224136 1250 951222886 951222893
    0x12060507050a1403061318051b011d01090b04141f080103020919181505161101060911040510030204080601030816060e0d020f06100303030203041a0c12010b07 70
    0x18481200c003900c3d039002101049182d69140076510b030104144908101504145000c40802c081e909819a802c0c007036202000c414001546074551072003016540c031585081c0c5814034032070f0400c0c40107100e4108041d109000c2035001c041d50081000d442c0a4441d24402c1684108110341d1504e004540c40360400d003a50409015600003000074150707a81214403500d1581c5881040210401118480114a013030031000c5c0b2140c0040440c4424017170207a08802c03040d01c50225034205844c400d0f22100c04589224852410007485903200509a0700c1580005c2031060f038a0703104130140ca10000000281000019040180d07160013030455040c8601750600b90b0030145403180b0700c2c4d11030340c0c1480040c250410008507036940340b00c400980206960300000030424001804505a42c882c40a40c46501600c42c1c020242c0e01d910300011030f1407044c44090060a000c9040d950102c2c040e400252044428466000301c1040000242c0724440c4a070310800c1c070b0b4503110b0f02e468043c8030744880d040c8d201003481d03a010041103010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 951225386 1250 951224136 951224147
    0x1b0f01090f06030e0307080a080403030605040510060320070b09070806011401030f02090916110c031b0a0e01083a0c02190e060910060518030c090112060507050a 71
    0x1200c401d400c0000d1354104060349903040d403054000091126000081c58000c0540001003070b8040c2c0d001c4d540401c01d4949071028402140c80a441c8010b103c84104400c2109512079080f294800801080203800c000c020300c140c6c103030758000c3e050071112005203208010781200d0800440e002803c500004001652405018410fa02c1c2006d23202c44c10141c46400203084111680c04845202ca406045070125162007c1c111420100300e890041c0024590750f11140e4419002074400c55440c0010003030300681d18646038002620048940042d040018820005182c015194400b0300801d0030130043d0980f01d8810001c019a18240300e03840c000c0700000c0c514510205e1540520309201001824282e01c1030120340006408651031100f000054890100082040800340d68014012071007514200740c2034079510315846080300e1300e01841001420a11000c0200c041c8030900d0081c0c1e00005c2c040d038140c220b0520120b601c002098100013100400c202184040014500c2200d9201906152507410400607140c000c18 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 951226636 1250 951225386 951225389
    0x1e1409070c060e161403011a13052203021e010615050304020312180a05040603240608070909050f0114060607030905060711010f080714030c0c1b0f01090f 68
    0x7030140e0310070380010310390010082c02241d03162007907540303109955805c0c160740c151404081150203542068400c0e5080480640b01c1c008402c07008040c4206408c0f680312100003410700410300c640207020524030181c0048801e01a43c0c2d820302945c0034018090340b010240505440c402d000c0741150385080401c22003500c040a00700303900d03000c074a0219501c0d02c5500009140898282c882c07000341e2800a0410329004a40c4aea4184030207095401440e6103640703d081108640c011b2002038100e10314200428410400d451070400c0030b4140304000030f1103a440d83c503c1441d0a60303581201030303440ea4130f291003000d000080081446450386d440080c8a600c81e014800000804060041c602400c80410244101402009005c0c0a448050030141d00c56800342007170102208407404042c0401c042e04121860503224140041c0b0510054450841d080350840040940340c0c001007803c1d803d114240009100c50000b88424a0010500c20000103446810ba08002c0c9203a201c002e00750501c5210f181c200a804070711300d040300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 951227886 1250 951226636 951226643
    0x2a030807020d031205010e01050f0625031202160201080a09030f030c05071a0601140a020a0f030c290603070503100b04090b070314100b1902071e1409070c 68
    0x14000b00a07150039a505a000e00c40e022a0b1410300c0c0002c10001144079241d812258101c4103140e4014580040c85454400d0350210020346203140ea1003401506018580c1340c0803446840c040510384142c803456800c9800c01361103590400c010b451141c00313669203c43d40c250085901c100800c0b040204e40d501904505d404d0301101e0505031615514010940224140d070f0007181c01c61150700c401c02151540e074541003011103196001c42d03e5054014040075640c000c2d038112901940040c1050b540d96202c0304401c00c1e0b185401c908100c03c3c500310800089107a40c4842e01200c458949030200c1e184100901d1071200000d01c03850091717200d41e0703041109981c000742c0c06a1207404e0940009100344540b0104019215000e00500311620410a02644030f0381648101c03042c00400801076120b440781015401900114402c0c10811141807101c80300b81188444d82e0500c0d0310340742c01203882c016070b501d0802c55130060401106024034801c0303c00b040500500450144001e000b00c03890380c11480c20312805802c90b9100c12016 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 951229136 1250 951227886 951227899
    0x9011416020d03091208091801050307140a0b0c060a1413030c02040212040b090105012903071709010605132a03090f06090218040209071b020d2a03080702 68
    0x8200f0705000c0d84540000e030039000c41da050381041d1400d081c84941d0007443c0150148240e8548401c40042880744141a600028040d1a070246012010030707101d10702c0615641c1c0540440400903117a040480242500301c00b00c0d000d0000340c41c01501e220f040302c1020305010500a140c030100501c0d07003000d5843e0700c2d066605080c184506c082c1e500109009009501c554118510804240b005018444820350700c1001124000d100c240e803100b1170300f580d12000007004c203d2007607460f62a4048001000286510502d0340c03418004000c45402d805400074010795012140f42d54a010a1049061555003aa0000c1034444244031484290740c20902c0f466038001246210441e08282c2c103c00791298018005444e0448810f449500c000d04080008100d4100102d1040690b0302440f641c0ca11a030000510840c0c008060240300e41d901082a03407440034043c01c0c000030000fa905000e005a803514407e0b04110702039051440d2800c1e051114031070079010400c106480c844100d601f080001c1d0260300710340d0200da040e03408 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 951230386 1250 951229136 951229159
    0x23011104060f110d05030f090a0f0602030901090c0f05040f1b0c0201090305060f06100219110f090a02071e150902040906022b020c2802060307050901141602 69
    0x1c64004043d08a455103e006546a0044c030740d5111000d140124007002c0c00d81040d4846401c11959400b860750000e228944451040b40414010340c05550312103003203000414550003680e03c0c0302c2c140e040340d0004003440940403c00e02582c01d1030b00c2000a0070140d8101000105c40c4010f04001854880200c0010048405000011644107540281c01154004c08035013940c203203070f01c0100032070000300c81c0c013800340240880c1070355028400204d941c40b00d000c0c0520f508242606846042c000002c0b105040c1d001864046112856112000070034802c5030031000c0140c07612000d261030184124002d054844400e500c1401e40d0100300c40c1c4a149002201001c000200510240f01060150010040c00307802c00d840895448446150f602c84812820f903110101190710100783e90400c1240105205e10710f103603025044400c0007400c080b03149001805c4400340440e0300441603000a100e94001c8520100040000c2080595560070180405140c0d480783e4900d424138440403980c03001d180800a001e0b02c40c5408100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 951231636 1250 951230386 951230417
    0x80f010525021506010311031801200a03050a0e070b07120c0c0b031909050309012a06050c0c0d12050714180a1a0406080a092612042301110406 63
    0x100d11f412039078045d0340d201d1420f02c04516041280e043c06c1030103942403c26900080d0404180603040504050409040126100c0210020072004020030200707540c0314018500150b0410007000100b46044c801039440e80c0d9440c21126180440803440203122108205030300042c540c14010302654142c41c05c4948964030301c510b1010484400b00d908007a0b07850851060300384a40031000788008002a00e03500c4001400302c00d00038649140070b01d90360006000c818807100107009030300b0241c1c00c8040600d0b114102401c045105e42440da00c50a01c20205160140784c2080b1181805190350002c1507081c180e0000d6805403600380ba912901305c640003080c00003035844843d690384010000290400140c080180c0c6981c22807541c0c030754098003400c0c0c0071444c50000254004624010034070a10f6001081c00e000741d4800d15007460341541106c94801c0140d06101b00003070304d80c200c071900e44514040c1000b1140001c80400440c0110410483c1c1030160f41071403841c44201c00a9000c0310121041468511688100c034071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 951232886 1250 951231636 951231641
    0x3010b161b0312020f0c01030e03040b030f1008011b05210901060f0803030c0406110a14010606080c09100806010203040b0f0408060c0a0f030b0604080f0105250215060103 75
    0x100205400100314190141c1c0482008000580b8032803d04100c5040a501069a0300d44003901240c103960701c610004580c951003078200000300b09404044034141601c0c0d0748016216041152443e0800d440c200030040280c1452a1007802860500b00801003411451110b01c0140740240300c010612500140c80061410144200c1400025015104806082001400d40680128803d0010502c071695000c1041180402202d0088100ea100c00d4941071070f0010640341d1010100000b00745002d1401080080780d1030040f0b28450780014400006c2250030110050107010006d03000f000001c0091204e0754842d02c2d6440e0001000c0468204904103944290040703140d4400c9030000d00084401246000050b140a070140041e1641c01041c2c403c40e41d2940301a09990240f9904100050040d600d4030a040b4000d500c00003080c1805803000785010b8941020510b003c03121485c903141c0f40c0d034038010024418425188105480c001c21602d11000e071000100941c0c2c0d4100c1c00c04800b514420703c01148140c2c0c001e9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 951234136 1250 951232886 951232927
    0xf080c10053a021801260a050a0212042a060512180a0807050d050705030d050903090a06021c030b06092206121704061b0c030503130303091a03010b 65
    0x40b20075503a5448480140da00c4212030314596020640449040304221818041e40d02042c1390201c81c03107000c1da6400e044070081d00b0301410061001d0703801c0051014041c00d0351582803040d4065086001c111208803550803d89001e1003210340c2c42e00d00c051042c032580c0c2c0e004d411101039007450f14a5400648900021180c49ca0940b4030608052150040c40803c010340c000181c014540150b09452000e03507900016501383c440c01d400100075420410081d21045116031107142c101000c0f8044900b800f81010211300c0c2d0098542100025a2000c0340305841c54503540e01d01c0404882d43c0c0740a000244100020a0441c050065400d2040865000180b4400860711404210102e001d00602005560b805031841c8101011070649004a45423070071485145010101e904442050f03442942c0144110140640f81c4400c20b4110361248605100002245041020701091058244014212484d45c64042c25100455202860070079001000d0070401e446030040d1390442c0c2c071030001241d030384603092004407000058 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 951235386 1250 951234136 951234247
    0x601051c2403020a0509070e0904050a1208090d090807051302210906010b0c0d0c0221010c0306050f06160c120b01150813110105040f080c1005 63
    0x100001c240301c41c0544090300c11a8002d4421122954950060190144084601101051898003001047d003841107000764850300400a841c08840d180d500c040907100c03280710b0170001602c524240f15030114248013410300690309052580e070705071420540540700c118034840c0501c207210b148101071542c845601203a4011000d041c5c40038144107800d001040c01e02007940c0703155a500c01c180c00801c0f1010010300302e400c920f01030380042a144101b417104403105e20308544101d0300066030314007240c2105d02f07840d951240040c1d03201c004950340300d44103002030803a100341d40f09600c2102d80308180003107525510100c1c3d425031100f26400b11114140c1c2820580348803640d0008140d0011800e4100034400802142410303240003022222460300782000443e0f1103541590045402907000b19850300003504208120700c82501810100c0c00d1a030b070355444010442c6a03900225950b0019803003081545080f200c1c001d900d1006003030140c1088860214072014001c0329004151250031000d44140d820400c0d50641c00c44441c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 951236636 1250 951235386 951235421
    0x7050904180c060507321b031b06071202010e030711010314010e0601030c140c01060e3412290616020402070f02190f0603050601051c 59
    0x500380041a0070204078003501e201d1214400410340794400c2c4100d580301a0080300014070051402a107030b00b4604e40398100e40c2c641c2409050804d11180501c110740300c00c0c1e103a40b1011000d102d1103042c5400c201d0507800301207034910000c40382030036981d40b403064401e9280c0210703d003524410380f03210507401005210040d402c1c521010414804000500b010012800b01c01c4c0d0303043c00045020f401c40215075400303024800b00c0b814207000042c8194440c1d404203007801c02515280801028210308034000d58003400300628565140c80042c844103902d18081c0380c010000980820414800243d2070020203815444084844e00c1c0c001500180d61003800c0350030034605100800c012102d00a00d500000e01003032040640d165131100108030712841e14105450f6030980b000002804a110303642040000d5204802c119041032540a1082c05a00c0703000c4a4410b6403a00c01c0030400e42802d020343e151441038154408810541000d00f00049039a0040c10b4480b41c489640d0320310a80c10380100140c01a11210b14407014169 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 951237886 1250 951236636 951236651
    0x901030b04050d0c0c050913020a150e120307031413062f1c030f11091f0f080903070b07020105010518150d0213020c0105040209060f010c080307050904 67
    0x168800229001d94882d40031501000c46a1a06507948000094054200c1e03c1100c000c00040c1800302e12107500440e0a000c000098500c1d40c0001d905207081e401410700704404080e220607164008100c0080c00d1030496003541c5c481081102e89035a0710031814000c007080010b29854416500c1c13001514007030304101040700d8415882e854000c21741c0381d0504070035040701c021103801e4007401c1c400c90f03242c0300e20300030321014064098800341001c400b14110755485003019a142055a40600c80b4461082d08090303140109603100138540401045294400d903414080b1040d110030a070315600702810511608150414400d29030390461003e01394040c1d00c0000d40034800303c0c002c1007c0b09d9410f502140c16910210b4201c0b080a51521903c610392204a40c8080c407804001001d0440e880c0c540483d04495100404000090202c1d08244090303070010007000301c9682d1940180b10841c80c10b4018141c4c802000e0f12060146118240002c18090400c2806000d614000003c80c80c5188544101d03040e00c10090010301125 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 951239136 1250 951237886 951237893
    0x70510020c01020a08060f010207061b0c0f031127040206190e1c111203040f030614060d0b1311330405060a050d0209040f051504110a030207020f090103 67
    0xd502c15410800045c0c96080010000d1a04404100900c0010b80c01854000e052007419245290381800360909240d82c0c1c4002400140c00079801710213040d02d85000c000042ca10300c0e24410b04075a11950600c140c410b10a9401020200341c0041303440300c409025506552668000b2640901c10080b020b2910350502c01c5104c03e440c0c120007001c20311101910a450300300440401c2440003400351038010a08035140380d285040e440c04912200607a6294819245066501c0d10b40d610b031902507520849030345850700305240000c0c2c805941662301c404162100a151103c581d82c8001c448402491480000f103058012010b10414035484042d801c00608500c0001000b442c030800c2d400c01840079007884414001c07044668038118001d40f41214406010380f42451801101540d281e08103440c04841c582d800d10100081d940c60380191181c60303140c0751000030b0b9800e122154032111071084d601c00d40220f003000030150035200d5640c1242c0003007080c1d141c0162591410f100040d480803501c40c20316405601c1d04008000e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 951240386 1250 951239136 951239141
    0x40e06040507050105090307031713260a12120e030a05070506090a032312010b0d0c09140409020a03060e1f1104060f020316150c0e1302070510020c01 66
    0x3030340507408540c4401d659900444082c400c0092864068021180410010720a800707100000d500b8400c03040e007002e44440803040c0f1112a58400380003001507540d10141c00c0305050114400c000507501400e100c11454070b840c030038442d03143c1011081080400700080b4070b01841e4040b8110f0200c0406490303484042d40350041c116007104000360703541d0240c4004510980720000b0382c9960b081d855220072820514040500440d15030011102c450140100901d1040d1414000a01d01800c0140d8085860742075000445080b204190315801c1400031b8190188000907400a03460303a0302808a8003c50080c20034408078441c414071340d100400113030420141550744040841c1400b0420003000190044031410a1843e040d00c20443c000c44d000d540270442030080038840d1020801074403c5004072031501100141828a0300141c20342913481c820242602007a401c0e03203005a403070315200340c90843c8010070042d0000d10003c0810b54580b9503640d0000c0e02d80700300001805102c11b42c5200ca0310854940c2c06214900d0f01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 951241636 1250 951240386 951240391
    0x31911070b040806060603130c0f17160e0a090f0507090e1c080703141314010b062a030a032f0315011e1148040e06 51
    0x1a1405140d4010800e409860152011100a5002040e150712040b0901285a201810325501240e4401604022840c1202c1ea2402800c40c8040e0350801c40c90076445024100e401c50004403150440d07a0103212a80b01d200c1204199028808440070301c2e250114450003c03c40c640004040c004040c00c00c01c2884000318071a0101d91806030b0034400036a61602568580d108444030b04003032894801d000151900c15901c10760b00c01490700340001c5070b0300300c0d80702c0c21482d00d011500110442d0002141008008800148403030016541009220180b071035000926280500010315681c250705a5040f05c4418003460a208880741e042d0036039540d18548840213026180700b40c00704012a10b810b04807105002110304050001001461250840c3c5402e40b00c0c0300c8140039481e9440c10441c1440c02818200e06000c5c0043c04100903458107000b44501c0c0f000281045041008503c20350041c00005003049a002400c0c0482c44c2d0749005109481d0b58880d00c0e40781550000c00c55a0400e24000200f158682d00045160 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 951242886 1250 951241636 951241667
    0x21906060e0903120424022b020a143001060207080309010504030305070606081b01030f110a11190c080115050f22052e030f140319 58
    0x407016520011000d50b03910940100704030085072100001e000c109200c0582207064046601d140496040c4500201a0307080b40510700d6a52401145205490012000c0046940e039002010750410070f2a0030083c008807104000c41180ca040042c900b0078000c8410114201c40e070014010420280c07a400e054960715000f40100c3c00948a88407000c81d4641c03000050351080b200580d01c032840d043c00c55808680542241008881035525103c0100c1e1002c400d201c0302c8640d00000d800c240e403a01041d800181074490b0000a0742c001468011030480c00c094050480d1240c00c0541011f808401c003241d0102c0c605055903550784c0598035442250020008058004030464000d01c000340601c4400140400000742c803841559400180041c810215041004045070a0740400c0384d05101c03401b02400c0182554012103402ca840c403076006120414000703a10340e0754440060300300c412400d94150766803c0c2d080044004050804460701c0480c250b582020000c490296184200032070490150b02c0707018207110314060119 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 951244136 1250 951242886 951242909
    0x305070b09040e0f280b0612010f0e010f0b09091002070c09050c090103060603020c0d1107030f0807170f09010e121c0801090b011b05010b1206091b090f0702190606 72
    0x40742d45c0b80610240704810341d000203007100551586030030082c4240c1d250171000420f5403290003603280c102944c402c5801402800700003040d0b8002c0c40b00201d08407004844220310661580c01400101c900c00501405640e00000c001030b41c500c480d041840c105201c82c4e1001c0f280324204400c1101300d0029a0103820504402e0724140440d5484050a0381640210f95a08100354031011a040c1034034803d0b40820b50307800c8550255280641c40741c032160291010400c05460f48000010f00600b0015940c0b141e14a00c070713070141e045060010088100100380702e0352110340c4c1009207140c01d42c2026510382c0c40c0d62402c1500c0c10109e83d481901420303403501c1c1101c800a020b003c12070341000020407800314081d2980c006016550071014070301c1c000ea1318070780000005069400d03650341c000580e0f0f15102e03e803d400c1a0319135007009040e94034044910600c0c0c0000e0319180d042c03071000b4100d4003025440380001c40342c0042c486140350740300d5a03401c0422490901d0351103c000750070809d0b0140c0310a0214942c480030580340c41a008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 951245386 1250 951244136 951244183
    0x30414090c0c1c0315140906120d1d0105162a060e030127030c06020f030709030c09090b06131b0f0810081e1f061e0305070b09040e0f 59
    0x14500c017006520039507000f00b412141d0180b652030711205c034a51250303004000d112084c1507415030501d80410162400d0104d04c542241d20072000141c080d40301801c1003464214a000341d002845ca02d9080007000051550102020b80b881104101c2100c0300115881c080038110b15549610050144052803000c0c1e0003035190000415404600e1980392140c8030000e00c40c1d0240b80101d94044031100e0101c00142c590b16401e006119151182c00003e6000e01940c0c0e446030f082c03600718244008800c429600104055182928220005040c5a40e6036806402240c040182e01c08205803500501141c41955070302c0705194550002050700550034164060b16603550841b20f80d01d210341d415509184e80039021043c0e001a078804c0741000d009181d01c1c034842c000740c2600c400084c028030b11218980305030743c403041c20b41e20340d08240000d69040002e4190b85201d0f5020b0529a403664a60035143c0000e402181604038000074040ba00d0340742d6400450f00c8001c410129031601c80715140712600c4000c50503610581c600e21585 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 951246636 1250 951245386 951245411
    0x11701060f0521060718080f0601120807020a06030615024b0a03110102090a050f04201207020d0504090b0f03031b060108030414090c0c1c03 62
    0x680000c0c1c60300000c1000c1c0745401c120030440c10005420070055000101081241d8280081c01214043c1a140c1c440b2080c1c0050314090145030303d59a00240141d0f84610320000809030005040b5046131604001c80c0b03e20741650400c07072003d100d040c10103504040240d400148659040d448181115010700102d0140001034804036101c004103050354041d98000c100c1070000200c1000030100000030f44500724082c02e032645050414014901c028401c43d08031310140c2061640000016406445d41d000841c64100d1240015841900900509004001c001c130602030648a07030303210291401c52003590361554907000555010070b038400350300300d02ca070b0030400e02090106000190a00d800e003900d845982c102403d02c8400c000500070740c201c487d4001c5541a01c0041074606000401030b40b07601c51180c882084440c2d010340d14104040c0d10000b4954070411003080b856000c00030310505002d0840704403400381c8071007000d1646c6008100040c503d43c098070500100d0100c0101282c240d240d8142c03428485400c103443c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 951247886 1250 951246636 951246641
    0xb03040c0b03181c0801380a1e08040b0411030a14070506070215030c04030b040b16080108151003050f060f0c04210f0b101404050103050d0c0f1a011701 67
    0x100c03600c005c9030800005006150203900d040c6e0301851024442015100d01700e150581c2d40012100c114142c8000240d06a400f0740d0020304810700441c001c40640071026040e00040000c2e40042000c0e054512000c040b0742000305482d0100c0800000904481d17400e81e980c1850741d41c03181d04a8030844e0172300c00ca220009040c100340041d1070304950010b000d41100c03021062099890380c0028070a51207001d04101c084009040049458062400b40b50f045c80c65140060301c075140221201c4464050141d8070004112030040050240400b41c018003072209607072900f02e121a0003401c00d401c010500d00400320000248500010310745e1045e912682c0c2c40c412a00c1c1c00e402801c80707119074098060928909403600708820241401d401d42e00e48250000c0c0801055515161900700342541c03505050f2031400020071018040200008691400700c500700030551543d52030581c4c4070900d0007840c00f40626582c0c400107214a9110f10b03129285c000c840d42804c08054000c1b4104d0a00c24000d2403807203900003200d0b022880052 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 951249136 1250 951247886 951247933
    0x10801080607091205011103040b1e1b13180e06010f030f032f1f050f010302010809030d02070302011e020711041d030c07030201270b03040c0b0318 65
    0x19202c103c0c4650134419400508485400203483e0303592119443c84074640c10000540c0700c0c90040c80c82620904022a03141c1d003100701444229094000842481041c40710b5070008550001d040305103598500c0d69104468190216901084a0000d07038031918455640c01d40001c140003542c4001e5910302d070b032a04840c5090390194040600220035103140540000d01400500f07400c150501c0c594a0328032000c54004038103500c4035030604100d400c0550034800782400d03042c0842c0700e5507014a0a000d246020301050500b40e00500c0064104240d00001c0365240505008440640d09882010b41d5506035606000c0d01900c1048554005810621650384108610b03100359000c10350311200c202128002402040060100c03d5680400203428050b054040356081004260002c20180603200203491400013510540d9209a00c803103030000c600d00710001c500d03c85111400d480030001415201d49890800c4449041e082e0407500d505070000080c80000300050600d01c40800121007100d40c2da41c8803114100010718030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 951250386 1250 951249136 951249151
    0x60902011e020d140405120d12180f030c050a050c0306071e0305061c030c06200412050c06030423120901031a0301020403081b0127060b0411090108010806 68
    0x18802e02444a02c00c1158425842030114014202a00c0f003002411b4803030184030229403640010040385165420207403240642d41c18000810184c0cac0903451301c4400b0740d41240000c0118503100c010f081014043c2c201e912080b42c000c4201c4081d0403040c81d1072544c0e151241121480f07407040710300040915110300445070030808414100800c141e100d503000c0e400340002401070740c0d014141c0c8102401240d6179102e0881c8041c00780c0e8909034800464200382040710145004003d016104480546442c1c2c541021079007254200d03000e8802c49036003403c1950a105680100030b501c820004140018030039068400e00307031003210301d50008251042640199940c41401c0341080e021b0f03c28414a1030540c0241e114500b48004404180c22070103654000908980c002e8108444070540811010100d540c200c1d00c0c0201030344804001c00105c000d14890210030003160340940b1a0400d000036450402450b90030642c54650050018001c51100e10801c1142d03400c5074581d1400500954000103144070001152400b5641 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 951251636 1250 951250386 951250393
    0x804050f061603090212060a021e04080304031410090812150319020f0607081e0c07050f19030b01150c02090705160c0e041703070206150301060909060902011e02 71
    0x101282c054015104c1c440c03003a41d02c519510282d0765060014441a8490b90020100595892001030411030966286203140d8001c1c006100c24070941034004200c0d01940d401400307900c1c050300300740f50a13464091904130b520110313410b1403121420040340384003034241410605c40039241669140c01c1b05146555030003c059065200314201c01a10503980d481001d841d00107000074804449000129200d0380c81090201c4110300c00083c282410348030020704076108e00c0120030702460041360703006c43e40d80d071400c80c007410b403045d4807072025014590b845d842c1c0c1203440e40a400300d0181c4140d5a0402701c090860903c101e40b903d100502019030b030240315085210707000354002e044480d943c5420004a84a400103000c01341c0341c0c141c0c2020f02002c00e544008200042c00350b5000001d45281c503240a4054030105100c0d2480b01c0c0f0709109018904d030f000704450b40d100d210084007887c4001d9040000340508a41d5201c142c030f4626141c0c480c010701c25503800140c00b044c000e03214541c060301780b40d40b0451004a100600c100580 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 951252886 1250 951251636 951251671
    0x3060528050f060903011a0a0512060714091309060b06070f0b041e141516030507090909052506020a060e16260c0607020118080d0804050f06 62
    0x142031214001d0039440981810b0034242080042407c56035041c0182c240d415100038642c100b0b1412580102c00b510040e140c0454107480700c840c2c0b071f80c0d82c407001e040102400103240c103480310746200405540030014005c007040c2000348803501c804014100808265115420101c05800f941002d000312440964010030038400c10280e0380705c0855846001d8812162101090104006028518002c0509500070541d1040041699280fa80741c550140c1c541030590203040200030401c01016424403414215040c0498542d850000071655070f003542e0004400d052030710b500e5100340500080c16000181241400090664048614018441091080c60016880040b950380014180d4020806807a0303420200c4644404840b4035030f41c1c41a030ba4010400265404108a55031940c1b98048480c1d010400003504082a61501117a450302c03907090041d040c058911021740e9000414030080004000c200700742d44015440490040c41c840080e1406d84d03051045610074015103002040040c00b442e5210720050040c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 951254136 1250 951252886 951252889
    0x50108190206131208360f0102100609020c120702091b070803130b0609161107030b0c1c0605060409180c06020607230f030c190306052805 61
    0x681c044440f41c04196041d400000302c10080350326a81c1d1042c440c521054803501c5502c0355403c0e0443d41801b100b101c08098500c0d040c1c0350001c103c1c6130303c4004140e949103140d07002000182e00d03040c441221103007014a0210005483c5903554060944034802c202a558240c00c01c1030030103003a00410380c02a500401e2000401c10100000c030148600012222545083c5042c0d03454514441d001141c04010165206801d44204000315510a0703010001302c03509680c0e0705200403100d0038071105448038070178803003035242059042100300000c2005642c0008030307004c0c80c40c200a160304550400c26001c110b140c1c3c2d091601500020901510702582e0020b00460308162030050100013030880c103604241c03640300142c500000b007a0b25040380e00252205400610460030407580041984548a02601b1180d43c03503032042c2071440442046075580f24140e11095103d803510101444c19110742003a0b40901602600201841a0941c01c9003040300c4040703074111840058103114400300d4444004604c90043c5500c41030045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 951255386 1250 951254136 951254149
    0x60a02090111070806040317040b041e08070501140609040b1f0509042301020a020601171905060f181c030f09081b010b0102030d051f06120501081902 66
    0x30001407500c603407018020280d40c0d0400019030499141c54000b04d081105144c0c206400300040082e0400d40c481c1480c068a9540760040040c000401000d081000740e44204d00c4844410300454215003150b03501c1090f4036001d4024200c8804101da4010b07800c0009116182c818035181c03040750850070741100c5a1b0784071564890304484a00c00f01540e2180f03840440ca54036040388081c442c3c2e100340c0719810340081c1c40400318040401012049016030040051b0800c1d5036000c5942411228442800c44007810100b81a604143e501d261445401c2c1200c0c8041040c0500096810300030302803545c120071903445409412800f00c0b000400d403000e980c880540c1c41802010141880c096015501c0c0018448015100c0d12041d03881d00a415908044007140f0040c3c0c42200c404050648190480200049007a00300047d4403030007208400010182c0e0388000a44401404112010008807400c24810071501d4640c06002d01e0031045c881191a1300d864004070740c1c01000a5040300ea18503a0751714007080391256007000700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 951256636 1250 951255386 951255397
    0x22030b010501030e06150604090903031401050303041a03040c090504210c0c030305090d0501020a0908010b06090d03050c1207080a0305070906021903020c0d120210050106080633090a120203060a02 86
    0x8000d039042000027107010359442a0b402c138a100b9980498407030b0320700c40c0c51507002e40180c100c50701c40d4004000c20821142c1c0c4e501040440303000d451185403260f41d40d00701310001080300d5000ba030b10a403c2100b000b0803c40038042c08100380700e05a05030410800007000455002120040003000856140018000300e401103010f0948050700414010300c1e8010340d0f0b20503003a45c1019401030007140341c401d41840403607420701070790745101819144c00f8100202600054903000711004050240a0b002854055560080c400d2400c2c0f503401b603004590b034030903518100c4010f5004015210000e031420001c10341403441000c0b40d20071903025a006000c8802c42895070406040001d4084055110b04400c40010f626030310030043c1179038060304002201c14a05407000e03040c09a14035804c4a052304d000700600c242604403104541103a001c0d6034036407075904115441a0389507803003240c000c410b04040f00c00b298ac00407407000915511905559800d83d0729911000740b9000d10316000000e506410450000b501022141d002e001e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 951257886 1250 951256636 951256639
    0x30b150d09061d0706210b37090b0307031401090c0f0e0906010b030a0f0207060f06030213090f0f050a020909010c080708011809030522030b010501030e0615 69
    0x785888103698010481c0e415070540190500120540b40035441c060210000030a104e06044a001d18000317402c465144044c419040f43c565030340812021a114610152400390318034001c40301200d0034401c0c8000c0403c41103507000900300c06a1010a1060b00b90003560f03d07003031025004101090659580c078542c094000301c440142e6688511680c04200101c414400803c3c01078074494000742400380d401c0b20910000c4c40310909511640041182c0a02c40b42200c1d442910300c0c90001d10b10285a0004010b481060340151856042c61540c0910729095070000c03088900c2142c0765094118032000100540e1545140500520502499103021400c50419201c04901c0303101038820200070750f030000b51000001d07540c4c400603a54640090410b01e0300b02c0545908400d490601c000290b142001044c5d04024204040c0400358a03030081c0c00401d0b0244003a41e0712035501026010391860000404032240b5034510040c0d0308006033100008580d40207204401508038800e010700081c2d514603211038619142100030741d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 951258992 1106 951257886 951257891
    0x906042706060f080a06090f1e060501090b0c150103050f0c1f11100e33040f030c020621280f1503050604030f030b150d 53
    0x90620420b04c1c603100000c0d581d244401e0b0301410035075020020007400e00008441180c495080901007401041400c0c00300e03045408658241c51407442440d000c02c800d58000c0c04920800b100401ca01406030088400c0c1c454580700c0c5103804042640240d8a54008040c001d5582030140008211400221150003811a841c20300b003d0480388955108184121501030002e51601482415002d10184408010b00040340500c0c80d2240000440151040c440348844541c410702d6944901590803e02406603e982d1190380d07000c00884060402d0b814440100039500c0180d032410001d15400300640351041c4118400031a8803409440900100d8003400e120054012104c000c0c6450301d1408203032203002c100b00e4180c142410081c98006c941024108000c480401407100000d030040c002c03482552448804407003520100c00701e91403607020799800014840000030000852000e03103900d14050200 = true := by decide +kernel

theorem cover : BRFrame.Cov 951079136 951258992 := by
  have h0 := BRFrame.cov_init 951079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 951079136 ≤ n) (h2 : n < 951258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
