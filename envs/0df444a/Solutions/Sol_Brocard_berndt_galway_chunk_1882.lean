-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1882
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:01:23.459088+00:00
-- url     : https://prove2.me/submissions/e6f73cc9-2fd8-4c9e-8f54-89ea69e94dd2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 338309352 ≤ n < 338489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 338310602 1250 338309352 338309357
    0x912111b01050c3405030c0a1412030c06060a0e040503040b1c18060b04020c03121e0405010903091203050a0e040b03010f14062d1804031e090513090611042301 70
    0x171180c50b100003119488d030360080c2080a042039440b14410f44581d41d802c01d105084a00380e98442e06806030a1755621011100c0c00d00c034042c41a000540702009841050007290410003a510341420500c0c8042c03a80c1c424044112900110300308184c0c4485e242c810072044440150480d03907070b001035040c4001030724a03010109105903c10407858543c5500041115650080721910000702d0360350310701c0340e407039a07042d00e000541e6044000f0400042200640c0614071140c1b180d00e900c4440e80d00c403501c2004202c031006000340400e80802c21590303101c0c00341119081054006002050500350795003c00e00751207403424024403164a8516600000e2200c0020359440081528030b80102a81c1e401c078407840020203101c0807400b404c0510401c1294455098140d03190000325500c030a1414549001020151452403a03102c00c00c402e90328032001442038021004423040140b01c03403140850400310400030300106404460044e61545194403a80c4e1001c080d00040480301e080300c00706189435161030040076880e0707990fa04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 338311852 1250 338310602 338310613
    0x1104090308040b10380406180b03010f170a240f02070c030b04020a0f0b120901020a08010e0712020f04140117011e0e0f1b030c0301060806060702040912111b01050c340503 75
    0x42801c452001004030b40cde842c4481c0d214444004100c60401e0010200078121442404407102c1540b0348103103080d40f200d090ba00c02c20031202c40e0b81c5814201d0044100003031012214000c2000418a0340c3d4103190000d0005041d110301c90703510100507007641101e41c0142c07410b400c0482e00b45e4014005042a0b41d001c42141e00a61601065134002000c1c080140075110696501c4000302d100c0c40c0c4191903000c045a5004030455943d8004030605440703801510506152303062841c0d25071059446000204985452040000100d900307040a24a2864000002d0484140c58000012b0300c540304241d03890194000812602150400b80100c02c01c0030b11116094030039500410502185214180c112070440b80c10780383c0b903e400c2e1690700c0000d4241c410944084d42c840d08108818042c403004440d281f000c140c03581c0312030500001c060121034644c00c41140d02d1102c0ca007402800310065016200812640c03017600c0030740311051080340c030184151144407881000403044141c500c0c1203c60100d03919028200450042c01b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 338313102 1250 338311852 338311859
    0xe0102220504110c10020307051e07020f0f090f07031103161709030405060f0702040c030b0f03010e0307080d1503050708060c03130f1104090308040b10380406180b0301 74
    0x5a4034000445c5540000c3d90000004207254816010f4403501403040d000900307d00d28011a0301d46a41261000b40c1c070030180d2507118100361404240300c1040d004003070520030700d955662807003c614a2008101d00c0070f01d81c441840204c49421a4003c600c1015400f0050404c541a4400201820190b83d01354003002c0c03413003041c01042d00700081628100c0390304481c801e03034891101c0e0091180340502ca000940103400c0424000080d0b4268001d01c0282605481207000b80c80031808250036100d080041d03c0146e041044200c1c0800c210800070040c01c0090386c03000c00c441c4002d01c4a2043c40d01e080d4419142030300305035428403854006021b5260000790320060a800c0d810141d4100d44010b80c400e84c000d0142d203000101d5000c1215880388440d60440c010000c00140b42d030f03410003400c5003a00b198105e4200c812039001401e030340e00f090108400d40e041003c0300c00301302c41c4003070001190400c003a11140c80320103c00400e01c0c030b01c51100010400360805544581440d048017003101c803400740035085025001350034401130 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 338314352 1250 338313102 338313127
    0x10213080604030801031e06060b03090c15180d020a030f140307022b050105070507020a05040c0c0f060204091b0f0806010f32070b010614030a0e010222050411 70
    0x890551f42c125141300d100c0f030304541070861032400585000301501d00b00000041c0b9a06590043c1d44503419010607900e00340007450811541615051300b61812a0b81400122546c1c0d201101c105202c01001d80714030002c41d8075400040710908540c0c82214400d000e6201b120070821080c0e88805014003180007142031011b0b59002800003102440503c42078000e00c5a00e41d00048070040310350700716070000c00070011030400e80720089c00c1d41e000201c00da02980d81c035040060301c4d013040e2061030f450070040e03a900c6d00104619514040c0c01421540140c5906400380004141c60006204400820080388000f1240d02c0e41c824020f401e50b90102010410300c00300104000c0680d1304032180ba100b100d824078140d10929aa40e04c3c0d4003030300f140e0350101045031951400024144068100600c1041d001d690b900322640e0b6503032001c56105050340f14032598020f0510214460410b207401c0904a4000f450015003070009481c0041007103441c802c0d002d8101d404040003044103041512607a0050260301e45100e18140006050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 338315602 1250 338314352 338314367
    0x7031b0f060506040213170c0d05031206061e030a05061f12020403062301080f030436090b130b1f05030f15070516030c060b0a0801021308060403 64
    0x140071aa16800010344940d40c581c1113a00a0700c0c9080783d88440c40e00c81c9160560b22018a0400806100c0c01081e65010302e40b034a507022603160b2042c011403404d690460b207030380703100c001078801600b1034814020010008240c8401c4900641124203843d103924248a0fa0015903001030682ca02802500d11042420080c000007007151504508100880f40c0e09007800600900c00d640c40600402c0c5032070740040c041c02a044842c103201c10510600790250340c03144509621605e40c03680c5840503603c100000c21400b1006c540b0b405400d009a00c061522045001001c4400d66200e218904402e5031030b00203104100180e41da0b0741d000304020000e52100d0031507644262680c540075002c0030500b8449180380720300d1443d04001c000034010150039100300a00c411a06961498035500c1241c0a200e00000903070820301c00d00c06d4850007261341c5005185c0b00d4071520309807209012030206a0303c43e52100c01c3d1401a45440240800805020000603952041c1081c0d034401d5127441d4000d00758980140d024070010030b901001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 338316852 1250 338315602 338315633
    0x19111006180b062104062304110d2a0f0b1b01020c0a14010b040c0503070c0501060806190b0303030c30040b09010b011107060e210307031b 61
    0x90004030142c14000244181c041c4041c1da441e40b49491000c0055088801c20883c000d0744600000d00c04103080100c0d24800511a00c0c2d001c00541100c0c0001d004900a18102882031340e01a001d459203000315100d07840d0581503045408118506441207588040d50352603c0e0000703203503c103c08520503041c25041038081c8198000711013a482e010f0040038010600b98100c1311402d070007604481e10f0708045e24109403c100081c654028951808a017080c40341428003c070003800c00169540c6107075545681c41517400c400c00701800e50302503594840200e0f01d10420440340e4000d8010900600300074440110510a89071540c441030302035081030080c007030b02081704400e0314441908020f2018041ca00c2c03200408000424608203850401c40c0002c0c00305012200d140c03a03028103243c07002800b20340c0707120b001518003550700302001e02d441d03100d0030003002400d10130b1400c01552a00180665404103241d0034603495040441c3c41c8152a81001032a1b204058000300b40d031415240c0c0714250004035865489142c00d258080e40d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 338318102 1250 338316852 338316899
    0x1e0e07120501060906090c08010801020403020a1206090605010b09100908120702060c06071e020f15090c0307031a070912120309080705011a040b0609040c0519111006 73
    0x140300408121081d040074000d040c003100204409a500c2c1a030344058034288040101145005001191540040c021141074a13000350080e1100351805010a0622044400580b400da940c1c2071441c000403018081c10380203041e2640d1568031600c9a000b0400300180b0044410b0501003180c008200341007000c40c3c0c401e01044501e007160f031108064001324070f040c402d00f2070a00181c095803007003000d00364019903c0501c0900700703101141c2544900100341c0e5030f41c1040000b04659813080c40b038041100040c0310035a51026162040d20041e09290001c00d1801645400c1241d4084500440c1001c0451740700c009035004040e131829228091900100d030301a031107844005804059100b0420005034001d800151040c1e5200c0d01407540c42215050103802050408954600203018031085040c0346014014000a080b004000c1460404140f00300001004500b416a00b8420709002da00800d4854012200c00d00b103540c0c44407039503800c05000305818106081914814030749400701c02e100c0b00300007a10040d070290144 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 338319352 1250 338318102 338318129
    0x60601020309090f04031e020d020c04142403030a0302030609090d0f050307050405090717060a0f4b050105160308060a03050d03140a0e0a020105030a0216061e0e07 72
    0x1410100c030760b4031101c0c80d1f00404c0400c43c14462030640d0b000820460810040e8203482c05c03084401c04110903910400250007001c0301c81004120140c40200d8085400c50303043c001101444058004a030540c2c001103078140100340c2c040200803142c1400c2c0c0714540e01012540152210030b0303004e54050b2401010080346010008040005080785004500f240e0107010000d1040741c117407802c0350000b04801240c2c081e000c0310060803008500d5031b080c8080644c05507815042c48425040c205900c0c071200c43c9c0e6010081382c508200b0303100f2078050000303170340e0502400480e441c4504942903030152200c0d40d14482ea00403410400c0400000c00581a0344102104140c1d25203010303030305a196140051401841d680020b00107001d000b11120880b505035100c00340e0609400e841240e65600d46030860f0803982600030340612500014000c2c401903105900955112208000050070f0008000294400086e500b00807a122079030f40f1009845021000f80790b900f02403120034280501034400c0c0e049034031060244030ba078010301c014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 338320602 1250 338319352 338319361
    0x30301150302041a190e0a17031c0b10021906180b070f0f050906071103030f12041104051501110f0111040e132021070503060601020309090f 62
    0x2d4040b20b004190314040e014100c1403850289080d075000c0c91920181d081c1218016102e0780c040d200d800b80d81d81c4020070f8407005921b408190350503040e40784500346441c0410004088802c00005042d0f002c001c0300c6a000407010f0307645007405284040050b90701e040d944103c18207521488203409803041d49920450120755502c64041034032613040c02c182e000307106440d40c80400c802668001405a041d2140b6594a9070500c0030600c00d071000c1c0b2031121030700d401c103404000c80b402082c5001102c3c03581d0304c00501168a00202d46440901c283c1265910232681030744076040c0b1080c0507045d20800170703900c4200c1d0b04200c282010500032003400b14000c0054188541441110f03480c400c14030148441c0210b0380024444005090148c80c855846030080e006c2c8002d1003c0030415400603c030b0386c03094840c0e001608a00ca010080d188403503c80c1e481c00140d6010584104640000c07814031780c1280b44414140c01010061308003c2054141000101501d0441d0300612481d05187c0c0ca010700d807500082d0440010003591907 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 338321852 1250 338320602 338320607
    0x4021e0a0f022a0a12050a05160807092c010c02010c0e09060f040f0915060602030f0d050a1d010516110c090a0207020a060c14010504080a050306030c0a0b0702120703030203030115 79
    0x4071390300040c100172201130807038107101020401070340480c410019203105021f40e18880300740310500c0c01480c807641d0011a0a2000e03a007e036001204200204c070f000080002a85801d0900e8000381d16601040d94440c080500f070130360240100c40f1a9182400c029580381c0c5e401000c82c4041d0f500a107914030940403142a140c0300d172216482690f100c810340f401481144045e00b01104402c0440b00604921741ca48580010385034408400d03262024038041e02103180c04500180e00003e4800036005420a44e03035845c0b81003e60070a0440b680c090801d81001007201d2034001601031070002209109414055840c20b1708d0444100492331800ca040211401c00d06034a070028444000c0c0103002c0000e41008602602040054000e002900603d1248040c0082104d11902140c01e940c1c09503001081180c06101000c82c1c980100061584400d02078100c0c0c4051144100103291045958000d1390084400190340d000e40c01d00a01079040a40c40d280142803042c81d69800a43d00d1005129818905030701c001804c06031407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 338323102 1250 338321852 338321869
    0x207241134081c110307200d020a0b0c010623090106050a050a03090f020a0f06033e04030f060203060f01020c030c0f04021e0a0f022a 59
    0x15560301241c00d032122181580c10803100e081911040041481c00d030540c1080d18644020560700000042d080c0400c0407000a41d0b1016442d80c0700303080c04030580001100441c108054008140a0016002404120200e244010100704000350040030f00d08070050240c2c07a14071100080303440800f0b0f015038071440307a80868010141ca0b0050210030703081402e04c2245044050f440b043c45601215469000d03680c400040d5400d10402840300082031080c041d600d4507602035480a4007250240c80100c2a288855000070030314481900000114100c0745810b104090f418071481c0458034502d05400411410418460401c0c089003c1c04d1041c1e03001c060b039100c1200d1820b41520b000310340c0010501991380e010314007800a90011030b00107015900744604500558400100b01014607070141c0039240e14000311003070040d0b000244081580082d0200494079140e02440c01c14002c9030014090b840e21401d00d110000c180003090f0800c80b00310340c000d00101c2c040300300b50604940488860701c00064101d403044040748444 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 338324352 1250 338323102 338323127
    0x60406050f06100503090106170c0f0d0c0504091419060e030403020108190603021507020f011b030804030e030f150109020a09140a1211130c0e0f041b0909050106020724 74
    0x60030fa9400d81e680d0349c9001803008100b040498003141c1001c00c00091090a01d803025000d06034100c1c1940800c418102a407145607030600036611243c29526005da81d40c90050889091421881200313060000d001c0d151051031030080f5524095031603c0d24580000340040b5000d400301e07980030225010305015005580c400c07401107501030800c8001820b400c080134016001050140e00454117541808002c0d8440e501c035010740c2e0b6245041d07009a80054400b12607800c1c00a00c12000c0c0400c0d2030414020f59003c002802800558134020860300320000c3d4030850b000010b078011298a0300500c55a03a2064000040000b40d442452494001841000001d001c0c03509561205030030040c40c0e1440e100380142000203020340b201c00e8442d20760404c410a020000c03170b144d0907070b180001094001100410714249141c0109860028030124440d8032001c08881c3c4c005442507410b000c601020ba00700104841c0740201c6004040d5800941401407030884c031a0300c06640104400c005c0b610040ba07240c00c043c028180218407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 338325602 1250 338324352 338324369
    0x8040b2a09030109050604120906080601050d0504050114010909022805090c07080403030504091503080f0a14040602010c0807020f0c0609240903100908040605030c1209060406050f06100503090106 86
    0xd804e02d0305002c80070301482030050000824800d27021445034011165140140d80695441d07240c000c040c3d201d40000c08000e00201c0b07c039501c40e180e00c46011110200340707000c2c00e10030000041450091041041e141000249112820f400d4483c1c07400c00302c44125140200c540c00e50340f0310650303038030805101c80c80d00c00e0701001400c080c40030030b000c010b01d0760040191040d0303100108100035030006010700500300d41c07180c40000c03c5480100712541c19148441e0150940c42610b041c00035182c0e110540850701501710f40c000c0030050303554160303440d105076204c07800d180c0021844c005000c6a400c0007041c0307a22915a8000f440c01034030005045560b0303441c1c0d800b00c03d090700c14445500e01c2d804052400050715500017110030344a032140d684441c05541d1a481505c8401e980302010f9850246081003d03183c0b900014074044040d8002d011420100d40e00d076080038881e6182c0030217010baa1809281120451308058083d4140426520400030b082e00e5146950800710750701d0409030340702d954204c94607014000c150054140c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 338326852 1250 338325602 338325613
    0x5130b0408041a070201090e06030703080903160e07090501080411040902010507080c15010b0a09050d030306030c080303221e0c09090809090c0a05040b0c0703060c08040b2a0903010905 81
    0x29a0fa0003002e0030140307100b41d88921000303540301c8560050f04416a50194190404001080080e400a004051000001d82554042140700054842c01d0507540d110654440d4808200b008095000c1150340180c003003400d05940c14141603c07100080902c403e900c0d4011395a843c81c08040d680260b05903130059600c00d04180da10003c401c40c40f6115070b1100180040d240c518400414a01652415954002415a18001058900020441413602000060301410350380d440200109084442681c054141040290341d01d0070300054002c0491b0f0307160070010111749410100070010b8078104451000000707090341c190756181b00f800d0560701c00c3d05680c0424282440c0214030420804080042c0100800845030400c040c2d481d5050034141c1e220341c000c00400136000304001d22020080c10013410b02c0901000071103ea1980300d95a02040319420001140880c9102d0204010041d0100d002c4d81d21450045441e030b050f50350224540e15400407905540b240040118000c00350351000d5100c420019001412180d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 338328102 1250 338326852 338326889
    0x9050103050f0d08060310050613060308040623071b08060a0c03051609210503030c18150d0b031c0302090307150801060c0503090307060e011205130b040804 69
    0x60790b0302040b11542c1d005001c1c401d184240c5600801c101c0d84a228050060644034601240c1d1000501c0001c01d040c0c2c0c03060421400b25507512180c4180005544a801c000d9a580d040c018080c3c003c00b41410b16085850341c070189403501c1c1d8a0344081d580413603404109000c140c00300da141186142d140343c00c5141180b107040c04006624101d5041030403001c1140c1c40401c442d48616500c2050484206a2a400b00e41001390801c804c08000718140b0601000c40b138111a2211583d481d542150700980d284c00580d00082890703030703160381515003003104450308442415103c10800c800403e1401101c01c042101d9130f41c0c60001c030765034505205c0c072030030000b842001045102441001500a42002e403800e40203101c3c0b460041018016503043c0208081c143c1c03180081c5a01c0d049080b9000c81d94080e0403150ba00050202c8107031501c0410400025000684820590102e03140004081800c81d030481000b840c105018495a00200002c0e1000140c01084010b07595031103042042d15441107038807400e59540c0742e12840 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 338329352 1250 338328102 338328113
    0x90105041818060204180b03071a0c071d0601080907060518031204030b0f010b0909040c051e0907091419080d050306040c0905130b22050103050f01020a1e050409050103 74
    0x1002038a605410300c2c00042c0d4600c0386c02e4120780e01d03d4030340380d01948010707414000b02404c0080003071a01c24510300e446c80d0016810555040012a900c0f80032101541140d0310400e468044031541c0c8000203180800c00c5107400008075613682003c2c403803e8107100000075887d885c50000c10040e03010f1500502151030020007031408024542c0315100a03210b118038180420700d881950800750b8105d404144400d814010420304010781003501900485101d200700c580003e150701d541210115103c01c1892203500e56110b0424081d04010050490007000080142804031031820024104c45d1682030320340300c0005010901c0d000c04107810b90820545031040c42e68074107056a01000440c81641c0c1654103101e0b2035880b007400d4484c150140181540450800d03000c1855041c564442c1c111008018070804004414011140000c51500490f4051503142e80051050040400c08840f1a01c402c000841c60301700350103c010300304250100d5030070040d4100800c203159588030b802590084c10011400300b000396074a00d000b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 338330602 1250 338329352 338329357
    0x31404080f06060f010c0201051e04030b0411010305070503060d14010e010e0f0115180e01140705090a150c020909120409140f0415090c150c0b0c0901050418180602 72
    0x384298000308504c4404e5110f00282074a00341d068440d1420440f136003031394503a40f18079105540386d542001d000000c0803840c1d0b4411903010380e005034184003400040d94001000d9941c020b0081091100c1041481400d494010810102d15008200d03404403000050820b4007410030b402c4155620360030303c000640316200200b040500c810700340008201400131100c0c02d2220b800140705001161034150390b00c0e200c88920f508802030b200c08850001030300e03243c1c1c2c076280000311a0590340c420000d00c0109a0386454209024200c0182c121160031010f0030303100400007081210070010090240303c9402c042020254100500c0160003407000d40203888640700c0094900800045100c00c800340410004a048810120020f90007260000304111600d002c1c462904003030551807a084854942081c0000b034a03024007a0710340c40144141c0e907000c190681a050040300c0300701c00380140000340820001405140c0c4c0240c11102114016548000a480800c12070f6008100341000f500784074841c840c1c13900410219500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 338331852 1250 338330602 338330611
    0xc110709090215040e1017030904050406290114030c03070c03020f010e030d0c050a0e102f0705220b0a0b0a030e07090204030816080418060807050f0904031404080f06 73
    0x460080f2a40c41240302c0c00d100342203400b686140c200b0809c2c023105080c150091341d4058080c0c94041044249000080c81d01d000c080200404106d080c80480786640e80040c0500e00550017803101400d60804c202084440d02c00a1b00340404d10817480d691104050003032201c40b01c1c031034001008011903100c901c4070a89135440000000329452908c04c0c0030340300c10700400a0310300d00542507440d6003405640b9014400016101a64041448000001075242900c241c042e0140301502030354240a0703165009055181c02c00b82e0304020700c682040e80071341259503501c4600c16100015100d0104644800302d0104942c61100c0d00900c0188200081030040581c041c2c10030b0300421000c0046400daa0fa40e0b03a01d0710202c0c06a408001e01e550300401c800b5003400d0000030818a000d002c0c602d0340d40380030780c0d0308040464600a0715140504548a84c0c04002c48002845070b2070080905807031580b03407202880d00044401ca4010001400c1c00380c41c2c00b0b20104280c0000550340075002040c21510000d008a101b00c0e5922000c85 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 338333102 1250 338331852 338331871
    0x1a0d060203090d1b020f0a17070320031203060a090e01021b0d02070314070909030c05070b07030905041a03060702010b0418020901030816020d030c05010c110709090215040e 76
    0x4580701014481c00740d4500e440e15004c0840d51000c900ea00704060121050001584448207080104031002d0980741000301c02c0070100100899071451070140d800c001450000740b2004140454441103031030210781098090040010181c3d41d40d117681c00550034140c00e40103000d4103880c10b81c0c200032840c8158010f200d01103202c144c41d0100b078407841e10a56241408440d820061304091130030030000d44002101c00d048071200082d221a2615089003c0441d8a0660243c0009880c4c14001040c818144205405402200e80340c07031500700141c401510001083c490319020380e9507612a07407080840760b08070f40c0c40328070002c05803412030600c008000d000e008401c0d003071480342c2e1400d0046d80304c03400640c2130076001c03907030280120074280c0c030b5900e0b2440241c00008411242e03a5070b08076000d00603a501d030300e070800716846038a0303e001544090600d5821030b0303040440b0300e0501000305da1030303032145900080c28001c4034008400810030040603c08aa407040030b00a03410024076020402040e8a13160400440c0318200c1036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 338334352 1250 338333102 338333113
    0x616110609030d09060603020d0b07090602010b0a0b0705010e060c0306030106090b0d02060703020f030c0d0807020c010903060506040f06030c03020315130b0414030d0605040507021605041a0d06020309 88
    0x410255444039019108409a07501c10005884450300384d402c01140603000d02070001d2215566004911021294401141c2d880e0100041000c40c540002002018001c03078030003040721031419008a40000100d00440174008000300d14901042400d40007030142241e850281c1d03566007070100412031140c009070386041c400d500b000302c0420600311300c0c840c42550500c000c1041c040e6000d03d8080c015141d019190a500318003800386004030320041040140050720000000b40301d1200d0505004180c0d260241070b600864000c1141d0015a0303901000a0069076005000040c154441500140040200c0c960400310300d810000008280000e40004000b201d0090702502d400111100c0307078422503402207501c0924465120520004514044402903009101d9040710b00b0b40301d181808180703581c02140150031101d4a0744001d100508160281d1034101e84140010401c441140f100e110b4400e81034040c40d4040c40d582e1603180d410216100d24010f122901500150b203042a600f402c20182d031048a9061051052 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 338335602 1250 338334352 338334377
    0x3008091b01020a020607080f0c0d030b0907200118030224040f0b0a06050409060b100e0102030f130510022404080301090902040b04050907031103010525110616 70
    0x840001000240c0c0503400340c01002803c4d8200601500070701e506940f1140d05000401100e14058001c0c1042c1280c03400070b146c000340c10300e0b009003650b2800d511340380a00c3c410740900800d941c000d9009803a40320340c0c0140c8490140c00c00000350040c0b41c180c8014060702c0440000000b45500402c10407188892161144d850000300101c0764005441034070014040000b195020340800e54108030355401c1001e045010420603030742c80005054810348030f000d844c00e03692828950110314121901d16488040e6003000352002c1c01100010b9203e0054254004d0302c40e00000b07900414400860080c0007a04000300000f1311440b803800020360b503c0b0b255802d01c9040070400900110a040c0c4150148103e5000403100d18581c240f00d0785e030000d0203001900303c0e0401d441e001c0d1034032280c0e25030081c1845440c2e15402001c40e00d10b1810802e00995440c0308290082e4900000d0003003040069018910090a007041c4030f800c00b400000841d90f0004910100905001c0c034410700c00c00612a04058140f1076035581d907055002c3c003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 338336852 1250 338335602 338335633
    0xd022b0201030e0d1b1b180e0105010602060c090d0c0605031602010605061b03070614190b130e07080102031905150f1905060403062a080103300809 65
    0x3910626400482c900b42e030201c42220103108158041c5d88a400705035004102e811980c00c0c1001180c00080c0400724690f1045240f00441c03050070341501c8a01d0090005501d40040a9210940944a09800c520008140d00951074000c20140143e0303004d85010809030369404010007a41003900d5a00b82d2100b20a0070107481c80c0f05002d06001e4a100a10032840c2103c008100b500804101d054100380d8001480302c4d002088151044070b80d02880c41080b0301240c9044d041c0841c0c1441c50b02c24078900d0138940907649506031181c854427108030380b007110009080301496000030701e815041d62010f800b560000041000d00545480b1641001c0118007050116827901c0000ea90030100100701c00d60841b20003040950740b45441400114203c02d2032000046a588900109505a205401c00d40c2c4103600d8400650001c1428044030710600004505869030400030300004105250600c4040c01650300d1003180031841c02001d0104180350354401ca01d14001d501c5000190040303804441d00c0e15a070081c01c40e038030700462 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 338338102 1250 338336852 338336863
    0x2070606061706010507150f0b090703020f03010905060301020c0d020706170601120b0a0510090305060711070608040204110c01090b100602120f090306040803010905010518060d022b0201030e 84
    0x208044981201583c410700111072a0700440720668185d0528495405a03d50074424071172040c180d0580400c1c0318294106010049030064aa0003c0510401c010b0312031807010070681c0d065911204000c034040d03d0310000030340a1300a2101902050081e1061140a62340015410044a1003030b1101c074022201c0082c0702c9040d0400f120a00d01040f1003a03031284491400c0c0e80041c2c80520000d004841e80b6454401091117010b144600e4000300d4111641402444010000260700c0041841c001c54501d210340c4080342c445040307101354414450101c004c01c046558a410000c802c080a03040340742c03a9422246c1d02c9020708181e07181a05c4952000e0003007880801004031200c00d035526a0004d1001d01140b00350400300e40c0c0140d002c009629030602007007044c0d9030140b104501450182c1c0c180340e129410b02c0d143c041213a0060744554404c2d540311010402c12000403400b5039200f14111a110030791036040c00451400d82160700d0f43c101003440d891100e02544922003804194a000382d804108141302110000d5884 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 338339352 1250 338338102 338338127
    0x9020301060815010c14012901090e07120207121d030d2607050307090f06020c060a0318292202270a0c05030403080a05090a020607060207060606 64
    0x81d0000c0c000650454040141d020f5220040c9000310f18242e46484052601030304c4400e280469445040301500c5221250484009030000e514000d10350030341ca0006455030030640300e80340c5040d11202c0002e514500820140d00c3c1016210000d40d41c034081031a200490034107840200d40401e040c00f0000100910340c120344d018030704003d0010500c0201141d03007650441050713889a400303901ca800c40d5407100b07803440c01c03814040c8486850321a00c1c2d042216000e04842d01e0f5402c4107000c030010b408100f204580c0090808520316041d52019a52154203500f10050102a0030003e00c03030540f20b500400300300709480fa803181001c0e041c408942c041400d080329231078110180e602034100c1541c400096601c5000c0162a10303001d100900d034485402c3c13281144415840c258840c500c00c20382036801c10880703480900958070740040c90714045145180c96030700a0320907000a0202746e103881c1ea400015030041d4080040b1a08607400401d881c0d2101d10310318180c00a54001c0f0021901641455800034400c3d025260b1031910 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 338340602 1250 338339352 338339357
    0xa03050c120c0d02040801090b10080313090b0a091a010e0109050a0b09060909040b1005060a1d01261e09120313120509150415200102040e0906010902030106 69
    0x540c0340c00b8800b03000b60b0010901c852289608020014060b1002d1045c100140e02c036490a1450b03150407501004100c4d030682c04000140c10400200310801c5600e4103041c16102a0b4100040091144002c00d00780191074200c044220314142d281300c0c0f202500b4035142107500090380c0f144080c407804c000460f100d0010b84541a00300c6031201c01032082c00c0001c80540140703007000e0005401c10141030000341c071080043e10286e66000554060124002c07048040b031024081c00c1c1c6105140c05281c02e8010905050010402d8102d8000040d840c03d6a108581311114000240c004490380c0707402124190b0090001d0300d50b00e5103040341c42c1041c1450002ca6001034880c00b2004040c20307a01c0440c8404083d1a8401000d9109401003103035040000382800d48410010079055459a44071100413082c48643d6220014034a00204140010040b002c50241e0010503003940c0c0c9440c50b0900c01d29204c1800b5031600324504103595002040108206284486061048005a044800710390782c03080c40c04201e210a00a0000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 338341852 1250 338340602 338340637
    0x30204091e0b040b0114090a0914030307270f060c1424090604230a050d11070f05060a080421081806060306040204240306020a03050c 59
    0x1526066101200309406841551800510424060344040c161482110180402001e11060000a100003405442c51006113295441c1510020704055001482a403681d40c49041030000c10046105090041c0c00700310840ba00c034180420301500c5400a81c00b548120364005806125082000d84148100c03500ca0300d8010300c0b01d05041c07048902d481138a10550384a065900c0d1810b80c40f104000c6140e107494400c1102008080038400c1440d9814040c1c1030f07480c1c0d980108140170201c1c010b110b10031000c40202a9200340701c040081c24138180112420302400b11300600c41c01c2c07035909401c41000380b4151038013070030b40e0400750702d07020101c20a1103d406010380042044c0540700f2814000c51540740c10601821010070041d4840100025141e4040c81c06800900e120060003401202d4142c02811044400090700300c528004000c0f075a0b03a800103002074829922440b00010a040c07600c156507504891074840e030021070b183e080c49030107540a0a421000203207008005643d102612050350725546501c05643d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 338343102 1250 338341852 338341859
    0x9040c020309041a1e03121306120504020a231e0a050603040302120a121a0112020c030915071403040302090a110313060f091a1305030a180513090b090c0604 69
    0x185d040700c82074403074040c411303040b8110902c100a0701800c05003480043c800f0041d0708103000140044000e05881030342d5410a000d000050792210106d0042d40c0313340c000342003000c1154400c6100510749101d90351b0030000354003103c40340680c0c0c0500088100c406aa943c220720b0743d03450600000b44000c84002c0c0040c1c000411216085c80c4480c0281441c04051504044c0c2040d585031040c11076200c3c140b84042d42e222011118625604a103c000e100b000b000300460519507403170340c856100d1244040f42807240c40e64504100f61100f4141c04c3c1c035401500501840400111582e50315a02e40c024082640300b00420320019042c0030b41030140802000c01c2058550640d2603040011f000c1d40d10030041281c80d551182c01c1089d204095118440000703018000480850320081e15041d106200500380300d0041e00d003103241c10003249001044408010883c501070700420000e402e0800f2081064000300e5010715004468217000d8565000070800324065140d1018a4641c40801c503510381103880326036003000c401e001c1003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 338344352 1250 338343102 338343139
    0x50c011e030e03090a060e0f03030a0c02011815050c0c092401110609030702040f050f01030b040c09051603050709030b06102007031401060b07060506010509040c020309041a 76
    0x50b5102c68002003100c4c01c0c04105000240b07107101c0c0390030000001d04500b1010899190070000341c00300c11001e4010394940010090b0081982e207010102034140524450640503003014403d4080003055117031220603c68042c620018180e0381703c01000c0b5414440c0030000c001920302618080d00855100c40c940c2d4100c104c8403860825120760140e5107042c442c2140c521090418240030182c40b0b40307031039006180c0d07410140c41000201c40e8003450b040ca80901d001d040141c04040000181d0559070052054a482c2da0341d86010300782407039103400040e81c060520f000e22140d500a400340e005580841d0b2001d0007d662801b4089407411035521010302107940000225503a0705000450300510b4041c0c3c900841410f0b171070302d1044904104244031841581c050302041003032001c6100c00043c0292004000e201c03041c6000025005402540e0b00035040310303500c8010940b1030313016074120303844584007500a11130b01c0702000010317480e90841b00d03031030307024a0038103070310006000c0991580b03200c0c030000802980c2418003c8218 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 338345602 1250 338344352 338344361
    0xa12020412141005090f240105010305040f060c0207030b0a022b0209030a0c060207080f060a02090a1e0801050106020a0b040b060d020a090903030b0603130f0c17060103050c011e03 79
    0x46980e9400f402200d421442e0140c01501e1161010304e0050040ca11020301e40b61a00c042007900100d40000d0f401d46403803501c280c40e841c504541003480c01003a90384035400d204510140002000313020f103241010000c10190081202000c072401401c004078a50707a141c902c00c00380d100d120b015095016440c46e8205050b06040f02142c03408405680040c02c01524202007444d140b2106400d030381c040601310040180d0755040090801515244c4068504403440c008401d030b5403080601183c00d0030350040b841c080c1076103c0210400041031a00c055074400140c04203c9100d241d03042c05090620350802e00040355942c000280300d9802c0e503010000d06240d5803592541001d040000e003029a22001d5030a0070343c007695a03890404003030b105180d00010b1582051802400300d0b0321102045000d10414020000036409071120389200d5600040328205101d283d180c192035804135900440c40c2150a070741c40c860100300020385281a68412400c44808018141c015a1803441c0c07004082c3c01c10b8450b0704a0716506100350071 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 338346852 1250 338345602 338345633
    0x303211806050c0405040e031e0a02061503011e0b0301061406040506090a0902070b0a18020f0402070c0801020f0c160302060f0a0203120c0304260a031512080a12020412 74
    0xa03950a003170316000001c080d42c0c88840c84910701e40c40407030000018900f0054030040710035400e503440e14020049001a40b00e0358020100303211f030200b421084020751429008680024000082402d156155586000050086480c11400703903107055000f1500080000080d00c5541d80103205606181c607050802c5110307030080480b280c100340e8409000070760b401e140c0042c12003244252034400f100c5c907022070308104548822400c485500004581c07a005a1107850000204803015580136035107000500300424203811b01c0d0702c50029036200249543c450040d81c1e002d8203591307101c0c50641d0a4008440c3c5182c0c40c60142d400b001e03506c403c0800802148400e04802040034207003a005913820035204240c0c10401c50703000c0f02d01c440d8104000007000100068031244444052540c4004248401a0705100d00a8003521240703109250752000380001c64000e82010000410004490352411102451b203040c8580010601c800402d05000380c0e5400141c150090345d0a90b90310a8850100291503103501003c4880d504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 338348102 1250 338346852 338346871
    0x90b10061d010314040b010e13120c020d0b07050901030f050c25060c0c1101170705090109080a150b010507031205151807020d021b09100f030321180605 67
    0x4804e281040d079007003c0f45200302c0c056002582150301d00a2400c101c00c60090010314004010004e02000a0720b2000385190070b00140352a034401c1006202060507101065000b90001075814100300e0707040e40c800c004048441013079806001c00c9240d1080842a550140c40484401c0d8080c800c0919a0700380301010411980e144050941e20782c000d0f02c40000702c84400d945000000e0603942c2140030711000c80b1026511980078a400100026029480141600040c2c0b03a02c5c10458001049041c0703170710619804000d0000e0384c09480090300f9500e04a02c50103088035000c200142400404011580113101780c1c0d00e01074158444100c4000310400d42c00003420010b00c0c20204070342d1803180312001e40301c00c1c010407034000380424100c289091200740686480c02210100085510210808d42d001040140340021254266510b1140e507d415442c4007002200e034204082c0300645203400424598001701e01c44224030b20740704811005e10140c003d1400e5031030924602224070301281c02040002e405d036100319032051101 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 338349352 1250 338348102 338348111
    0x31707020312010b0d0605010905010f11011e09060b010305040506041203020409020d1d0601050f0f03032b0507021c0807090b0c010e06010e25020f060a090b10061d0103 74
    0x814030b00151081e00a264590404500042010000d04c03070100a041c00342020050750385000002812140c4801040040000701031002034500d03c250004210010700d001079201412400b40350310010f02c8125802d5030b0b036030704048440040794024450703640183d4115018100642e80d80e21250b202c044200c14007000c043d800c00c000120911107101900ba1100d0020020640b01e0385840c2d110660700140781603d10540182004000030b80d515181212250b0301520300620b002e504400017801c5000f40e410041c401884010030915a100e81c1280030a5091402400c200742e445d1208200e80d141d0603105c0008815051307000010b500c6004a05a6a00026915004000315120b02c5502c40707980155061140ca40c0d110038107055015000e00605001d00b410306142c1010345840311030783c0c42c0c8000e442201d1007041002c03111480914801e0008140d4200400111500ba0426907140c030010302944000b07503040c007450008502c0000400e88200c04540d52a940c100790145030201203199498210f90745810306544 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 338350602 1250 338349352 338349367
    0x1b060c0c2f010513150e1206090d0309140d0c020a060f0c020405060f0a080609010e0102090303160f290601020102070309030210120f0e0f0f060a18050a050a1704030317070203 77
    0xb800c0c0c001c00e4039170b442c0c0c3c4160f00c0c84003580a10840120300314403000290082ea04110000000246d160401d01c3d051801003112015420b00d000383c41030184406059003d80e40d2900d54885e00200100e004610903200d046400303654510403503103185261400000500740d0100c1030090714082d0007150b04002c004041040c0d07a0400c07000500e002d00950310001413500107004110300c2d81020304c0750f8140124580005e500d480d030303541d0000743c5a110301da1158004c00100503070b40081c002407003460210290720449034242070603040002d100000d4440107001c100075803940017035901d51040c0207813034006a00d41c581c078201900b15403c100070b90152080250800581c0c10f50718040d81359038002d0321410340d20713440001a4a08449292414501c603185120016800008a40c00ea0000000c56542c000c101840c00100d034003100300342441405126001400e140b190f0689481031281c0400c40390300d6281b184070b49110302e40e80601c45030304500840c40040c002c1002c64003503041c4034002c00c184580c0500c0600c16240340041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 338351852 1250 338350602 338350619
    0x30203180316060b0406121b0509090f010614090402090405010e1501080f070303050d0b0f0411122202092d07080604020301030b071b060c0c2f010513 66
    0x881c900c510181c8070b2408294007488070610400424490955050050f103090596020b2940e046c4407006140d41c0384955810359148140204e04041c040080100a203410142c1c2c44c503035510300411154070346510f000387c0000c510251003403c07411640058203002481d07546808112006800900996a035501c81408900e0002d007400f4400362004540301d03600ca594104102d40780390001104e503e008a610017001800031940000c2a200d04124501006c1403010403680415500021061801c0d0001d003400c14440441034060040c4c419080d0800460407103568444107a92083e60b14246401c400e420b62a1881c09810104d4036030341d120440d01c0f0301c0f81c404580c0b010000c42c0141c103c0020814140e03040305209045038020705050300544111406e60555040d5200d0498151010b1b015605205c0210000e0030704c0d9035800652044150440c0080009080854010b084441c2c545002c070b8080d40f0003560305010000000b20345c41ca00e5904035128002042107001940e480d40895440100d91040d00800206c108 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 338353102 1250 338351852 338351857
    0x30f1104060c060b0d020609061605190b0603061b070606030206030f01060f080412110c030d02010501090b01030e100b06070507350a080f040f08011505030a0b070302031803 76
    0x1c40d690311a0b80320061414020201d5540c400c91902c521240b5241102503521070303003502c254403030455503e83e5680211103c000d01c2c080d0703640000c0c2030340aa8030f0301c030f000402254502082d1740c0c09191003072210b644079003c040d1140c502711012601c0b0001244dc2000c507003860350143c01a0b52007503000040d0503032240c0000300560800c50303080b480d60110000503c81c5950250046281e019581480d8650b41070550300d0490f420900d00320b4074100000040f81c40c00c1d12808000c031400401025065a41002c00240001d01800003401007622050030421800c0381035102c2e200c2c6161580d00b180140100620000510b0044c1c05032540d06980f0100c280910404283c0a00103a0000c1c94021461801d8001a0b80c003918401c0b240844d850052100002616055402080708044140c0c803641e4980c0d901480c03600000385001d41c2c4c200400b0102d0075a400308003000d055000080b000040816201d100b80d40e03804040e52842410f500030401120701c4003041e0b1250003900516001210300c01d80109902c0c00714070007850754 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 338354352 1250 338353102 338353109
    0x1090f021b030c070602030f091003090803040b090606030a0503030a0b19090203040c0509130609051c020105010e0c0408070b030402240901110105130209040809120303071106010e07030f1104 84
    0x42d0030000d00e07a10288010030405004003814005107042040502482e1424041c2075002c50092a0b0b100c5d034024054420740c019612a079020b021030391a0304080c01c140540f5a811120000075104010202d4030610300041c0c2c000c182e5602800031403859450038070110180210700340140d08003801e000f2018240510800800c0500400f500040e00ca2419041910399542690f004074044c000d03030818401d0036800c078100040e5160b04020041008212031800600e0180106a01d0b6481445003032203205c0140d0640000341200c40c120198280354440c445540d40c60300c240d100b1151654402c40c8100100b20344640950782c0a1300051401c043c4040101203c00c5a41418400f60b1420034005400c103450360300001c0740344400e04808000c1110b0300d001c40ca0004000d164100103807040c4a440009001c100003d41100c41202000d0240e070300d082554000180d60741c0080d903103440881d00c038805084035a440024024101c1c1c17800101d000d9282c032403602c217074010103c440020311156120301c00c81515005807001072008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 338355602 1250 338354352 338354407
    0x11a0909241522120b0f01140a0b070201090f1814070215041106070b01090c020706140f090d06060e1f030b040f17041806081222060e010809010c0801090f02 69
    0x300c0c58220036645140320140c2001924490b850170404235034580d84d02000584d182c0c000c595541d28094001a00c54415603403003610b02c410201c10104526007002c010302c64280e1201d400380b000784104000c1c210107410459a400041e0f00070500140f5a003580c01205410030b0148218011382d040207400b02d0702507070180c442540c48104003801000700a05a00c030380d5108000910150505905105000b065846100c0d0f812110800104110181184150031250341e00f80081640c02040d04504d000b5000d4100340c458041d00e1140d180000d0300c02e0f80c803410000c40c480e00440c1c00c603640c2800d550b50102d0106000d0f005903010f0f0b001d40b0014002400780f110b40580324009880e4181c07107528155030700c20218495014050309a0410208000d40c80d0300161400a03003400c04034260710340d402031550400003c0115092401800e081d040003400701e4020300c40c404042003ea82d0340e003c5030352310343e00f09080c0c918041c403080010311541d0040107000c02c02d40c00401c6043c203000000d85000c40d841d5000125244140860350b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 338356852 1250 338355602 338355623
    0x3050f010912080609070f0e120601030204050c0403050604150b0301180b0703151703090a0f060e0901080c09090309030a0305042903011a090924152212 67
    0x42c05010505007180e518149006640340c0340c82d401141c04070310054a81020300a0490300000c106024042020a0b5000074040007214850f55113403a03640c44083c0b000764062071526001c1103c050001c82190240e94100c4000c00c17454440359182035240d04101200100e40c0e6803843c4040c00e565080c01092440c2c03040d240c05055031412820300d03443c41540a81104141840c0141070407194084482c0c0e1400c032004181c40e407424103d400e0007942103118040001d68064031340680880c031402032529250a0343c0641d82d4242c5d50903a03400c10300c1426942805104503a511401001c039040c64a0303260140e200d05c405055034100880340e00802d140c4004080100c000c02d8012400b4071000381d095006805500d00d51502d07103401e41540f03941001510040c007601c42048a001c42603d11101154100d500801c0c018141d40030343d1802250342c07103c0403850300b150900c40d00e1042e150342c020b01c0d1141c1c2100c4000403440c4443d00c3c02c4602c10f2982805035044006c00c803100c1c1440300014074040f06443e04001786004056201 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 338358102 1250 338356852 338356871
    0x9061b080d0f09060c021c110c040e031201060914190e090706020c04090b07080a0e030d0911090c0d0906150815011e151b060b0a0501020109260403050f01 68
    0x4e0961303807044010021984040c1495800300444054811122603e0178000549a1008070050801d02c22810040c1c1141c2441c114503854070001000300158130a5404026981c0d8846204641061091040c03804010418520a0131441d01d07855520188040f9840000d003da07840300f1580a0301411a0020384a0300903010802801e80c06014203401f1030001c40701002412065501c03001e904402810071010406d064000502058055000e6a10198540100c9840e200003025030700c00350544a4045980c003805513807514103806e102440e103001d02c1c0e0a0181c50306002d108e60342c040040c40d0700082a513241e6203032250f10030303500071600302000604400c2002d4a03111145640f00003e06034182c0c4040611280350050703603540100420314800390340a800342041010b0301c200c011130f1032455030b610040740d00401c8000b0303404001c495805500c43e0003080d600c04204e9980c500040e422141701c1134000d01b49582807480d02c10403130310401c0717400300c111644c003607035414182c582d00c40030b1070005d0507508400142e544996a8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 338359352 1250 338358102 338358113
    0xc05120409060906050a03060b011803060525020607030203060d0602030f0a060506040b0a030902010905180103020a08150402060705011407210209010e0112060803130e010609061b080d0f09 83
    0x24400303041003003010b103c80c4c0d203800c0104540104a100192405944500807900c2d680314000d400c8490703e60785c00c50440701d512410f00318000c140039615035000c400038841c22069003185040d80c62102c001034010381410303604d9203016406584010705c1310340d0020285402000050340d034805140a0025060800243e11b07204170480222851038205238880e0350180402c0141204803002c54485c0001c2d8500460b14104610068401c4940c5030002944400c201c805040c103624041c80301412640216040c8001c1c55890b044651191441c1000554052240001030098181b035002042c13003e1081000040c44450f0420710350344404240d4040c8000b54041f0040c5042c18103d500b48032480001e01c0b000c506d00500c840002c1d00d61810280c1d040d051112054400401144580c07210f070080018005aa541e0441d0030801c450707a0410f0300401c03a02c250f00c44000714099125203444001c0e40e0054491248400e400d10105110000820040301c00c1041003100e01142c0060303004000c0081c044001c007081e429102c1c41c0c003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 338360602 1250 338359352 338359361
    0x140906060d110a091a1503010308070807060f0516051e030c04091503110901120209041b1d150622080304060504170d05030a090203010905060c1e0403020d080a0c05120409 75
    0x1d051090444001c030011b801007070411070f41166807020306d5659800389482d1200aa008066026000a25090b2007480551441c0c021500c03854900043c2e054400c1499800d0300c0600a00b5a03194261000003030060381d03000020015604000445040c41c2032580e01d086a209442c1110708130a005100300303c0c20002c00c980c10080d5200c491084441005640c10300ca40d1780c01d00000103001912907080c100200301880701c884070800810800129412a05480d038022400d110341c00c441300d01003400c250000400404025050f040351520003007140303107003142041c0d0311280c2200c1806c4640e01450104400500d14000308000c1c801801903072519500c6526000e445090303000b0441281e01e0a030030681d032102d03c2d2507200f0100da5009070101000104000507001080c011300440384010b05610480c028481520300c0f1070f01804841c822230100c881c5040030543c000d4020700907032000070f41040d074050000d40010b8590005d000d0a0005103090f0000c004182c0780c40380f0b0700042d20504044420005018814070406020303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 338361852 1250 338360602 338360651
    0x5100903020a140706081302010c020901080d1701030503040b0f0d2f09031e12030f1602071206020a0c29060f0303070b07020a0b01090c0201140906060d110a09 70
    0xa0620b917860b1040142c43c013007004190a03804014115400704581c041c3d01e0b101000f54004c1c108a81542c1c64a4000f940c58180000d101f001c01c9003528601c03010441800c00ba8180c0307600201035800c141c50715000e040950000181d104d07031408284040e01c503000051181e16410f07041e40f0711a8142035409040f051070040c001415948016007040744103001e1700e00180300840901070408010030140e40803010b40c18802e0704c252b80c12300303101c1c00020310050710100150680142d18000d5421011540c0480036079840d403d510407a01c400c030f5404c03026400726125a026103080c0d0414103010040300500d50b00c034904c0c41112040b2006070b44030380c01c0c035086910f522440d8940c0a041a2002c44040030f090000a0340e82c02086c0e402020106070100103034040d44280311007582d140c0d05c65404005540c60303115041c081c0c16403000c9030005628005034643d103200b8082c0c45601449211303025010907240c2d1800e000484600000036644403440040084003501c0d41c601d07440c000c010f1b10324000360100310f04441610b14505201d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 338363102 1250 338361852 338361893
    0x6080c040e0f04080408010c09050307080c0117061504080a051515041a0306010b0c01050c0310180b0907050d05090a212a03180308031305100903020a 66
    0xc1402941115044980c00c003980c410260b40070341e500d2070a90000c0c07140383c002c00515420310740300f850401e40024040301592403c03070654440e01d4441504583e52880c000669000881a01c1c11800f460200706c1540d41100300500314055601550500c070f01c140d0312a0344141c0b1580d000c0c1c029501840b40610486552a20042040c00c160030b14450b415101c0c136205c0d1103144200e5031400507004480110240612020001c0e003030b12065070359210101e0860700440d00134001035081200180e440c03140f103021a03210301404644007900c942050002d18085820030600040d590b6500400d41455a84000c000d05c00c10260b40c2e0f25a03681005464401036800c041d10000440d032000c00c0780000565805030380c00c807042c009803c045c0998800d03c07040715009400058140c00700d803100c0d900101740501c0702660076218001d840303070080c245001c0c0c1010140220381c40040c0c16000c0500c042000d062494450301c1c4201d0207141110351103040c0c21410011599400400c4002d41d01c4405403004120001c074034091910303042c9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 338364352 1250 338363102 338363107
    0x709020a0e2404060e030a050717060a05132d080c0714090601030e1203091b01050a1d0d080d06210b0105010c0c03050114010e10061706150a0906080c 66
    0x50202c071490740101e0040005102c3c0a0141c04560385041255160194000044800e9580e5648071420101c464002102c00350141c1000038080120a000c4c2c5400f6040e22031a01e12580e07001d843c0c0c00304182015040100940d9082d009042c1c1940005002028500524030650380d00c091012007403400020b503101c00c12901000c6003191b420303642c4032520b503408003013800d002c18035006d0f40d01c0903030410010809580ca0000048107002a1900c0015a003050294100400e0040780e0400d0040d00c89008031036004000031030080702551034095100c3c01110030200540b0041000308260742e45640c41d0007040c030b071403100361742d903042040b8080070211040c4c1c3e081c8030f020400302c1c046510384404d000840140910340c18403007050202c004106220707013070100454109008002255603680c003402606802e02c07a5000641420000c01d1001441003820401c441045c0c5842101000750010501d250200410303071540201400344030035408540d034000340316048031640c51403402c50420b80094024000609482e001a005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 338365602 1250 338364352 338364409
    0x615030a030c060f020408030412021305090a03141303200a0302091b1e031006180e0604060906080a290c0d0f18020307150e010807020709020a0e 64
    0xb19400e803070b040c0c12010206558616005403c041c0c85142e000d20590701c0000f070300064106407404040300c03031482100c00840240c2d40785000003d446041c0c41c6981c00c0d400c07018403200002d0140d0300c000028400614000d05002c1544061004002e080d0702c10340d00d42c0d003244000c004658000c025848004000c071a0b0f1100c09040d600800c0714504028101441100c902c100050a40007120a485c2c455444840d05144002d0031a501130642e0025164031252006550010400c507000c0c071180c51480c07000c107240780750300e510385480241e588101901d03481d0000d566113800b180c0181140030f0100a01110303001004520700500d40a9110b0b4030b8504441140702401c107040000c07812a100c0b940d0880501803e003500d4402d00920351008191005917612451300c0c1c41c072b626040722452142011600d00031003d543e0101c0e910301000c44d0072100d010002c00000c0760f00138004c4141d1700400703c080d0810024411280030717640f02d003041e02c2280e02003c11000442c2d10030b201032040340342214403090464044020b120003c0c00303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 338366852 1250 338365602 338365607
    0x1318050601170d110703050d0504031a06030607030b0a050d0303090b0a020a05040303050906130f0f1707031202070f0902030a0e0a171c050a0203090d0207060c0201080c0705030a020615030a03 84
    0x210f018101c010400c3c218541103d11500700300c448003464102e010ba0316603030400100502071703521074407086959500c110f40d4681b90035080740d6441e102d40c0000c1c0140c01681e42d280e5044004080c0352802d2640080b91140110301d03912030640d180ea115100f40c4000403030110b40d04208100000042001d0030007801001100303552a440820f48040b254107051a544078003525002032058003464080e050b030508980b1000a2004031240d041080f00c0f0402c8101581c9900c50740d1024003180d6100c2c446905910030f490070400288080032043c4030310444d2040d901c546031a0808042e04401652000c003d080d0040240046248180725001d0703002c68150040110b0042d6030b40d4031500800d00d0a00003032406c1c0114007a04100c001c0c00034140c0420350002d0400403842c00b03295810080d00140c507000484c0c480c042d8611034150000400c0b4003500c14a4442d24040c01c19640112a0543c00924940c4100828041d60300080c80c104007400259080e034001d071200307150040201d0501888440014840d502c0784d03140001094 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 338368102 1250 338366852 338366863
    0x606031a1f03061104080609010c03050709061e032c1203060108041104110c0303190204030b13050114070807020c04020a0e040207050a0f0b01090e1605010e131805060117 75
    0x1da10820114448413079449910341402103a000c1c080900400c410415400c1c410352014202c45982d45003000262501d1608880c600d00a02605000c50720106295204421100c06405445a05d10303002c50003050906100e2040405c030441820180d400700c00242c2c41903020300403511000d11030805581145024800203180c1c00b0082d001910103143c503c5204500c0d21140c100411040d1201101071341d400c408800e05549920403600d8442510b0050f8041d2022120750086030205c2380c20043c02c41d080c1c1c49107103c43c265404e2590003200c03159600c00c0c400c02c500c10740c0040d19101e51003903101c07004c0070301d45144040e091844500c1414403c1d44100f0011303080c941c01c000e4944007003d068900603200d1400d441c040b03140420b504000b030000c00560000c00d00300400e0060340c0741a141c2e2a0424031802000309140e5540720341d0303006c8002e110ba15a0300f09100a510a030020301071020010801d40341e415007081200304550034801400c1ca0010030f89003aa040c0482040080c0c01000500071002d40700801c0150282c844 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 338369352 1250 338368102 338368109
    0x10501080606010e210f160e060105070308070c171b060c04090e0c04050901020301051002190201080a0f0603030305010510050c070311011e020622110f0d0606031a1f 73
    0x80d1940742c11030040d21040000845c0c0418004100e13480e9a00820b8801e9a03038413030b40c62107890511009400310ba4004481003150180c84103840b03135401c2c20310503941a110f240c8020040c0041003440855503011516041e80200c050b00f0040c00d19a5401130031b28032110684650004400c90b5000d5010320101803100412241114211040050795640a4413450304140e0700300d04081e8001d040a0034080407070300660065040704c20894498810712050201642c88214044a4108440c00900383c00c001d035001d64007895000c1881c800015081c0c81200b0354804403000c0b50403e80020b5a500018099810000322024291825042c420706040000c18025980e4a41d400003d202d140035141864950740203078614042110032042054904a5102c030095482c0d03030813101d281d0126040400d51218101c00c502c80328010350840d07019140c4010301d84c2804251952042d8150300f040c0700c0008040802d003a8440c20000d14800c0c00305a20400d0941f0410112060140071003102e00388200d40e01e604401500d618500703c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 338370602 1250 338369352 338369359
    0x2010c080903030d020309030c0106051203030109181b06021b0d060b03030f040305010915062301050c0f010b0f0301020a05040909150513030206010b13052b080c010501080606010e 79
    0x120010703840868250300600c090320300054004000d003d190b05c0080080c04001c80440d008106280d42c8900b04200c62141c3c0d036480096400800050000b903c040d0800d03040090013128038005072007503a4030000c4802088007400d07240990300e1010b11425505005070145941c02c0745599580341d00207030009035040d80c025002400c3c55034500c3c02e412552006d1040e41c13071151000001c40d440395601c1c05c5c45400713010f049408803020005038903000c0c250512072207000c05583e8001ca8a20f9164000d003b046100080701205505018080c000411f003040100a8141d81034610300001c03400010a01c14411089030035030150341b10b41d0062000f00003079503105050314215203180c88045042e1041d0b04003103d030100450314000149084c4010442000d6415980f40132030b61103542160341c01c2e0380e034845208e02406144800c4007440d444030001c001d1840d00c081d0321894007146003554920382642900d0f000100c414908c0441e200c402c04140b80d20500300c2841080d00502c50200501183c0c034081c8c0c0000d01c684500c001c590710 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 338371852 1250 338370602 338370607
    0x5040501051e0f070614100e15090c0a090906060507020607030c080f031504050702071e080d0906021b010f0815100e04061205030f220902070b06040902010c08 70
    0x2c4103011640c112200b00c0a112819600c0c000c0c2c01c03040f01c080d8041d1100761180c905215030402d09650002d400751080001d002d88600040c145001d00602503806040703059428401115014240d4a04182d1401500708020103981c901c02074802600301c001941c807044500d407400342c04100a0f1b42040441e03420590494100d940da03105441c041c2c445c1107112602401c0200e0200e2407040788400c07180214000c2032030710001c40a407240c48081000340e5004680e80b60042c2c000302001c003d0850021110303900b600c8003c1c814861305445120342460028484001000511002c0c0c0800060340c050200b00e40711650623403d00301c200d00c1708001a281090f54000c071000c00503443c002449001504001c4005140020a220400c00203244018001980820481d21031454140005001140c2e10300c00c5001c150b20501a5050050315a416481a0010802c54207074601c0d030958114070341403100081e03001c2c1c070b001c5d000181c85002d41c1c1002c4881d4440184060300841c030700014480941c0c0c01421000740180d0180e16240e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 338373102 1250 338371852 338371867
    0x8070305130b07030f080f09100c0c060e06060906030a0b0705030c0706020c21120610020a050604030809060f190b0f0d030e5e0e06070f0504050105 65
    0x880c511900da114081142c400314a46040542c06441c40440542c140e44a0859407101703000d0100030070b005d640440309076000000c2803102d140c16800031840c140341824000144c0b540c2c0d4550030166040ba9118034a0b9402175410007a90303242c104482c40d00b00100764020000d40710540c1d505070800c0409040141444004800241400603000403507568542c0000190340f10107501420f0b0b07035120201541e482c046d41641c4116003d0743d080200751241040940c21404030785e1910f005200d008038000510108600402e04c200000c6035040065070b024520035071701c04509160154955081040140900c000d1001d03450038070960110100c4512044190010006440043d000000e8400c8030b4130401550049100c41c0120241900400d51070079001c0c00359001010700d000401198140f4841a80b915502c0060303800000c841d41c250040030810403900000c203042450484041440c0d4030b074005484009540310304958640c16000d020254202c141400c1c906060882c0b21406400e5010714021113040120100c0d020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 338374352 1250 338373102 338373127
    0x2010209030607320a1101020a140f070b010e0103030305060d1110030608060c07030306140919090507091b02011104061214070c020a0e0f0a1806140109061208070305 73
    0x10800d070382d5034101e80c1001c00101554014150801d07121345001c41c40440c61031490580c18022903034050040c1ea90824009802b101500740ba40101c94000220001070141d94000340c040700c03003a8040e1980312410b091030741c5075280050a8490082120307000341c2d0000300d1400010700441080254000455a034003640566400c12070003040a60f0003115a44240400d010419140c44028100f81f40640d07001c1c8045511210318500300d02c0c9040600380c10400d040c0000b03d40c09011002d018a800713454501080010007070712014a480040c7d001139088540d1900c0912180744c248811000703600c0075000a03c800c40c07080146034240d000301d00c142e0060182200c1c01030301203141c55100e82e00c8044a200450041c0c20f01c0500105400e64000049000310f00d4060302081c12a82c00407103034450304049504003141d9a03043d80010241c050f0188509040c0800080140000c050380540520143c10b80c0340d645407907161a0070441550547e5116030b4102104850344804904610102c800445d01802c1c07490b525502c00111 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 338375602 1250 338374352 338374397
    0xf03020109051b060f03130515010f17060a020c070909080904050f060306061201020403020a0f05151806090a0506071104050c0a050d020a09120c080c041b03110417030d060602010209030607 83
    0x1003050240002c101c80c2449278041c041d0581c0c6d2100c04070b03071006840d600e20304a0b5180f80004078030320307034058800030350248000d0300186140207401d401d80d80c1e40b903510211340050380c01c2ea810441c0c0440740030032008a41c2c02c0074894142e0019401d41d0307460140c20210040303511141c0140c02540035081060075100e9040094046074015035028182100c1156100c003140c41417003150041d0345c0b04288c01c0c03030750340c3c0c40115020a8695101480c2040c01e038031104c4400300600755006078607540d0403440e4184001065aa280c016209450082c1d56124071038000b142003008480c40100b410050110a120710544c3c0c0c1d9000c0c0c2a075011700001503006030359901c0e141d01614151041d9100c040700d640000c85c45002c000f002c1622404540605084443c000c944004000c241c030544800d1740c501c03280480040b00d110744280c2100c1c04180d000e40c0300c24035240d01c403010305403440c000840e08001581b000902003d103511620542004009504c003c43c2850314140029495100203410f280411100492079480d941c4482070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 338376852 1250 338375602 338375641
    0x10219020919150b0408010506240705071a03070e090907060c020316061d040902060d05270d0e09070c021002030904051015020f1e0102070f03020109051b060f03 71
    0x41418055580d00013245160f441405810010350070300d008250582071010300a951495150400403c0c0641c004060b10700d6003103c0c07002d440c0d502c02d4503000110040c1007181c030010003505141190760b83c505405d020302000d072203100903801807124a04110b86c1800128600c0141e0b452803505d41400030322400004e01d040742442624980c8180c1502c0051840e0300b15103020740185445a000d021081c1743c400b00411510403d10203900b011040011580070549540720b41da0003203a00200c80003200c04015050300c110b604c030f24141c501d03501010912003280d030040e0341c00d110143d00725422180ea14014034000c000442120000340600e0754508503407102030007481a24440000580104000e00c0c2800c0382d0300103901c5912580902026900000340500d03c081202e03210724845000030a481e0b008058030619003203800d412802039544c24004500099003d020101141c0e010b580003190042441c02e0441c20140c84040305220381070000e50503205078440300165840b5000f610062520b03035030f550b5100c985050a40c0c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 338378102 1250 338376852 338376881
    0x605010b030118020a080f04060e010504081b0714012d0305011d280b121027030c080d09050106060e04020c19030513060e010219020919 60
    0x40010480c00242005103048401d8205000311440c3d802200400300e100b02041440001d007100300046440202d06441900684a501c0002d0a030103004200d900311807040d04c04403840040010b05a401401854241d940007d40001510781c003490540c070f100f0126030741c0c92000d051140f004031000c0308690b10340c010780300500111020301c1840d50b0600b000700181024001c0720000e003001140c040c090049404228402c94440b07940d03814428100400790380250700209039a000c0c1e0f8031000440c1040d1201d54a404402a442c8024805484541444410b43e902020b120740180d440c5114580c1d0286c1c001032040e40301d078250500f0103454910b42400c0211740f192041356000c95050807414420000150300000480300c2c180c2d0b80780180052102000141d1007800200300f0785900c03c030007602259002c0720b0f155040b00d1107814580d180c00494100008584510f601034000320f680c14000118558062000b0341a82ca8200350000468640303a0010320f2895001c2c10691100c8040310703110b039816403241e11203007002c40001c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 338379352 1250 338378102 338378111
    0x9210715020a030216030f0b09030d0c0206090606090f011215020708090301050105010315030b0c0403060507020f121204110301060b040803090102010b04020c070b07080f07030e1c050304120f06 85
    0xc0d00003941d2581c01e41c1048006214840c22651009180c1d90322031300307595002d01c3c00380d4803e00d20348400802180140070b4a545002c200329035030b410b032414401c910108290b500503000601d420903010f41403200003010741e4082c030240001c100180d00c5010001341507484071700c0140d500000030309010400c203041040b480c090601c001035510034000d084000c1c05019070120001c0c0b101c0d0380ca5100450603128855040c0080340140c40741030001580c240038055002040e0448035091a07600e45880c41511001e48209001d40c10a8020391001a0b043c0300d04221025003011075460448003100c00f6021050091025020b002c249120a81994081d04180000c000c0c209010b13455039294100151a58011104140950720346103008429003070034000d0b201c0005484000d4a103541ca400d9035800c280d407100c10101c68003182000766104007980e41010386642406541c8140c0060080414404114010b1031442d04400300b1000a00024000004407801d5415440c04004000114900000c00c00140f001c02410142007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 338380602 1250 338379352 338379389
    0x60711071d06210304060f050708181002061605180d0302010c030e0601050a05040203190504080403031427010c1505160f09030609020f030a03030b010e0105092107 72
    0x36400001d0280b4003c030b4164010000e5220b0201109840c001c01c04100e4109100c00c0042c54000d1404450f461101d04002d0310f0003801b076482009650145000c1b0000c400c0700041045c1608001e02003216845ca18001800c103400e10b0054a0800620442c1c0f8000700403000544101078130131110907000108000d0a00c2078920307041e01d4080e01a040c10b041e1400000d00e45011401003410002e0118102c2d84041c0456038480d0030f180500000c3e501c020090a210171800c1c10001c410062841114840d50040403116269819842c000b006043c0a91000500200602020307880c2085001d4140903429902da00c03d0f0413842c0c2c200180c5d0003110408000d0309000d82d081003da804000d6400092192011881210f240c00c0092070659426801e0100d00703000030004035040c030005e11140d0143c8107060008001c0312007200e10b400040c0c50b060074400d044000a031680b0030451596000b59000c06500f41c00d007045070902c42164041140c0c2c0c41010007880010700002e0341100c44030824481c244c080d020303207070300350050004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 338381852 1250 338380602 338380649
    0x1203120b0f030a0605160c150203090f0f0a12030207031b020a180b0f060a120c2313050105030603031c1103040c0f0e040b0105040b2d09160206071107 66
    0x201d0345071000307210700311005841c0c500c1880700c7c0483c154000000f440d80650887c40d5402904028050a00e034400e0345516802d200081226104200c043d00c000c09040308185810003c1c0f98510000809050043c04282c002a420614407402c400382d000340c207004480240009046004143e200e45910f814000b90014022607940000c490725009581680f051040744052280504ca44056000040c419800d842220600398015a9103034120f0702d0062121008031800c100c4205c492503400007444070009221402540310120800101401d0130041c0c1540380c50350110b0384070320805140315070702001d00004040d86440c0303900182010a11000550b1645020300d446c41140a182c042c12001000c244070006807941318501c2240318903032014980e000c50b407a040030b00c03018066010843e030344151740501b60b01c480304c039885448034840303154500003001900f46001d01000e030710054850200c100c3ca0200b03041010b1b800060503500a41d040c40c0ca8120b094030342e10805e080001c0d64100c950790300c2600d25214420507 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 338383102 1250 338381852 338381861
    0x1002070f0b040905240112110a0c110a05031002090105040e090a0515062409090405010614040917090607290901090515090a06020c0a0303061203120b0f030a06 70
    0x10f00c941410021a258042040d1103000070141c0703d805120000c10380f003415403149950101303209002e0004100b2080f0300d400005e4130b800440820000a85036405a01404928100784030301200503a0503201a500b0000460380316101d10810145168000416200076407042e803c4500a05040310302034001e040040e082c64640b40031400650700780c41034000c040628041d00b01d1050107100300911009280b00300616024415180c0d13811a13103c03c00611042c0441d84900c2443e42c419440750000040f9503062000340850109131201d40d9002d1482c007801d4800054805520450740030304e04281d40d450741a0413002540d14880c4c1d1000905001320f00259001503502c42c003039500d00031030310b680c40303081d5686a048481c00c0b240c2000c8003801d40c2d84a06c3d042d0f0307165800c03031601c1074104680d08150703080700e249921081d06980c01100780c402d00b54010b0113400b05041d454401c030009042c51010800361041251002030802c90800b4851415550743e021040c1035030b9803441c0082d0400c0d005011346002e02280c0c1032010081 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 338384352 1250 338383102 338383109
    0x40807050d0f210204030b0907030308150d060203090304050310050f0f0c0904090206090d0b0402030c100807110c100c0303050a0b011202030408041707031703151002070f0b04 77
    0x184114440d140c0907a0003158000c00041003980e454550545011500504812410024400c26420007011000c1383d40c900030f0612407040300c070040810600e54a0000c000050051003130921180c82c004640840d40c1d400d07000001103400c101c01503100c2c4c07203611000d030031b6124951050340d0611810043e00d0b500c5407282c000700c2c452a00030b210780c1d640b6580e151000202030001c5038400c030045420060100f05203403036400794690320f0002e000c080c240901c03000450080c21b81e01001f80e91a40051082100318507080120088003034054954280881c030340035019000d150b01800007802d212010a03901c9241c8010070010380c00440c000c10401d420204214054001d803980142500001c7c10000082ea0100b0307580100048458103940d0a076030a0340c10845840290000b4104981d400001c00001030152806102a6000010880900300c102c0c594070b001d03c403405000380d0401d80b0f0300d01401004206807205c403000440c9401524000c000003009801203041400c142c000030740350040040041640050b41010300301b0b4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 338385602 1250 338384352 338384363
    0x90d020c0301060303052d1803010b0f01020613030c08030c0a0e042d02130f0611010b0906120f0f01290609010c0f061b080109140f100b03040807 64
    0x440000300a0500b6030702c1030f000240110f201082010313840e001c42941c00760340780214071070071003003610f4000d09060592040b607011030a401c40706003000d00c40c6020311600714210800c48420a034038100c2800030351500300051100b0842865400c149041c14043c040c2e0035012640900c505070f503881c00c08001010358000d490030500060103140264031500b407900c01c4040c2074500c1c80d04128a104010015000c070700040c9800c0180c25001d02103a841100348401d40b002400121002c40100c0b0705044000306180d4030101d2981c400e0381000e20070383d11a1a4032142981001c400c0d00d01c11104807500300101d1901800d82150800c521440004011414042d4040d034440c00101c140700d003146586200c6c0380b41d85e00a074035605134000d208004c4800950302a48900138418410080c2100c461210f80b02d400031249106440700385914010311101c40d4590003c030300707030240107481010032440482181c0d031072004000800c030041914180010980110112a903400140302c0305030b0081d500c1c07405150101154112280c1100d5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 338386852 1250 338385602 338385613
    0xa031e06180b07081b0a050c07080102040306110403080a050702042a0206060114090603130f050a1b030503070b190914060a0c1d01030902090a0b0901080d0f08090114090d02 76
    0x90740d0b10606044e40a585910f11803003030a0030001e02403100c2c0d88066810014010108007000c6103060a00a0380d0040c0816400140c940d8598102501039840c0840c0b8108400001c110034000124100f00780c405145041c9007541c0c50b8081440400e008141150708003688a10400d03650750b81040c22213207192101c0c1c150b4256880750b100c0a00656042071400d54504c14000d0910411185080100165a1105070911030301c2d00140744c0d807901c100004080d0ba0513034554001c001030009110740d004601d143c440343c05c14044c46082c41e68641c3c2d602c90050040c000c0c00a0490404900140400010140e0010b00e10204008200c3e0030301e001540b903c40c9081c140703058010880058800c0000384074845140342c071071300d991038001215650425001c8540304124180f5903141e082d0720241c1c441c074006601c140c0c903d200004803500810b081041186050303000c02d60982c0014000118190302c116070181d440c400d41054205038403144030701e9024028003e00c400100b01040100450b5180004140c0c0b002d1849409454 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 338388102 1250 338386852 338386861
    0x11713020112180209060a0f03050304060e0102030a0903060b0a0503032d180135060414060102100b040e0f250806010b0705010f06091d0c0a031e06180b 67
    0x750340d00400750600f0840c00785072950150401d12240c5500480080100f4440e07038a42d11084801c41031604140c034250f102040501c55290440c0183c652403800b40003c41c00c003d40594028081000b40c003004004a444403442c4e0a2520360b804114080c000050589440b800400750801186500000000311443c11907030b030310b010f41c224008a0740040391010401e5200001540156240200701ca40c806110b40705e901c1358420107190a0149000d8429840e4014aa08060f0104001d9545845050105050320814400a40e8000980ea1680c03c20300d40046103400907500050b008204100528400d8040c0ca50300800c041408542e5039010554642425805020204a0100c142e41c500900c08c10380d000034014400310038003901600380b0a11420001c617020b00860109c01c00e90f180c0d40d01070003805480b1702d940740315042808048003000100714000c2100c61407100001d03204a10621000e05112201c0f2001c020300b01c10394200840050700b20501f4000c94014890900045280c00c0c02a00d05034203400125 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 338389352 1250 338388102 338388137
    0x70b09041d0303070c0212070303080402010905011d150903030c060a0e03031504050c0d0c110106060f0503150411040b030a0c09030305070213060503191101030c0512060117130201 79
    0x41068450420041d429662840c80917900e003c0700038020380e4400c10485c41c0c03e0f01298108650006503210f540c1d40b400504251001502600440e00301c503050105441307600709411900400798110304011203c0d4030540c1692071800c881c0e48a0007801e9034060000107034900c08980d0001c0c1c0c0f60301461000f07104000d08200804074540300d02041e01d080e400100c0f00c0b4001190303458a81c020a07000390310b1500c614a4064480f4034002101d60036540da00104070002442411203100b07124407001411581007540c482440d03148020681d1100503e6040d00031001d18540056483d19400109401c000101095a503511140102140d400c21511081500e04114a05041b00c0c4140203d50071641d1540795030781800c03510350800602e011841e03199a1000ea807940b000496541c200b0a0310101d03280000b0114500350241021a05089024410340c107150900542007400ca5000048034401e140c6604503891584480e030040754400c058105100030102c12005000c01d8124080700202c82a1007621b56113060000038210b0b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 338390602 1250 338389352 338389391
    0xc030a180504140c0a0e0d060903080903130b03100801050f0a20040302090a0908030112050610030507060f050c070311030f150c0a110a05070e1015030e0f070b0904 72
    0x2c110350350700c56102080400b5081d102170102c40c10030b410191044c13011a07000c01c150b030119100030791b40750b41c03121001c01c207064004a440307400c000d0303401c0514a0007030300107c0000c140000b440303440c0400d41d0020010b41c200c0d240c10003034005070140c40c000b031000d070500000703492500324280c58070654680b520001041c2c3c200c003595001c06519039104070b14217041c6941c00b0072880000040c0340c140c0c0300761511248000201550b000703501030016002ca0300c400605508049141240051800a65030080c0c9420b202203100084c0d1502100c41618100780180c1e103000c000c840c00d02079100c151440344200c903804010042542000c031a034000c250121400c030300c0d07044e482982e10300701c50348203001c202407410200e00b12000d0b80700240b030148003d0170603600211040c4440c9240c500140c0c0c1c1501c05401000091100084d61540290005401a40440650304141d10f500b013154006400e942455920344400c900d4420030700c0310040d19510b00d8227403800b580da0385403450100e501c1420780501c52843e01e00d0504000900480 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 338391852 1250 338390602 338390621
    0x4082407120c0c02132412020f0a03060c0c1716030f17011706090615090a180b0106020d09060c0602130e16030b0f010f0f050c030a180504 61
    0x72503010300c0e031020700e2250003048445200d408103c2d820b00d09a002d603ca040600340d5400350464000792002c103900741c150425140d8100362410101e91703c002c00420300c020148050722601200c03400403003d032410000b0070003919036000030122406c1a40014803150818410f1003220f01901c1c19031001880b0305034048a6106840e10b2080480c0381c04000c00119104038007102c55070a0750308100d15100c45030003001520140992184c02e0000c968048514403003401d020541e0040304c00d6008080714148400c001385405405001c05005009400018450442540064118002440d0000201a03450400c00303c191424041c401c0503100c1d0104480f43c0a202d0b9100c88101d40040e541e04502a035140d90b00e02c007035404403480391488406404042800441c200c207040c001c4040c0d15450411b001d0001c0c0140545042140003840303008500c280d140c0c80d9030008a40f120494031450030340c010010320715041d81d40b80100703a0003007628403012844001140e0040081564a00030010150181d035903030f410041556071500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 338393102 1250 338391852 338391857
    0x201020423030d0f030e120d0c051312150608060405071401020c13020f030108030a02010c0305040305040b0d060e09070e060603010510050d02091801140d0b07050703021204082407 79
    0x100d90f0300e0642c1c03080f2400c41c203040e020f01d004100002d0042c03210f03140012150a400e400324000030140f440a07040d200700f492980060410b1030038050a640042c440002c281300702040240724241400422280582040c0c416075000b00420031141c031075403900da88210444088419100e0b0820100b0300068018240744080c90590041c94001c0818041c00030f890006241a9030a079028807042c0380540d90100610b010300b5695000b1904c1e4010301800900f956a00c03000082030508d40018040445d501108440644000507802c030341d6030a80e8402c410080caa15406003e800c282e12041c4042d41102099610071501740003980740f200d441c0c00f030400046110a02c10b855001ca010b101c021011030081c2c01a11000c00014401401d0000c1080070a140c0c0382088104481a5036030401800325030f1420500304603038801078030070b82c195520b01ea1391180100700c0038108800340701c0081005420188204204601d101074906815101d541d02d0105503500c0c500051481d01c0140c0b00d003400c044030351100c02c130140b0903029507 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 338394352 1250 338393102 338393113
    0xf1c0203071b05121b071502060a02030f040204090f0203071e0506190c020d1403030708090118020105030c1309060e0105030a151e0c0f0801080f0304051c050607020102042303 77
    0x180c01299581d80b10800c585444d1810074417041140f481805404020306208240000741102c4400c0282403203401480001705030310600c01d021030f05c0d42149905501c01c0e81528009030100107070502d844005040038000354188035605002c603003000300720052104100450698114039840750204a0540100c0300e000740324003040003000403110300c141318861001d030001d0418883d03131116407140310726240490103850b65540004103011800754400b02d0030350b0159100000700010030000e61710841c052460400641000004000301b181044003804030b917945158010241410382d0342c0c00416025000703611520107044804c3c0e00000309820041040140141c1c800c032841d9103000056540802880c1d40051112084000250b0000c1d00305944030300080024a80c5400c0103000c900300d0000d05400c016082409250000e84036204145000001d4905a84c0d0444802441460240c07001020054204020700144070300401c1c841c0003034042d030051013524035041106182d1032500310306901d102c2d032000c1001c1d0180d02c013 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 338395602 1250 338394352 338394373
    0x11404080a0f0f0203060a021201050d0210030e030c0d09090b0609060322080f0c010608070f0b0904150f0f060c0206040329270703080f0f1c0203071b05 67
    0x3940504402500c034620310f00b04801d1903000f0a02e80340084904030907080e40000e0100b5031094070078044e030041408030341d0500c86085c194086998280400690b0080c99107545424a04880c02c0c000d0f550708a030400304480c0c2c1d1000c1c01600401016642c4540002a890400e141c0c0703507130034100c0850f0308107000a040305155860300a50080700400118000141d403115202000001e58075100400078183c90500e15510740350146099030859640b0360140d0715580c442c0e0800c104c8840c01a00507000c5540c40c0c6511a100d000340408240900800b10241801440c503042c08943c1c482d002640c50207131801480c28000007030320380c00292032100951a0196000c1e005000c00c00026004c00700d860490301c80d04850070401e1300071061081180000f501c1c0ca003e00480064a8061221a4014401c24103848401881854a151549029407041c000400109000007c0a0040c4c065501c204e8081807440e0b44944060745003545100300940064444030005500d03801c0001030340341041001524150040080c0004251 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 338396852 1250 338395602 338395613
    0xb010f0e130602070503040e01091a090c1809071808010203010f210b04050f010e011802040c0c050d0306051302130603020a030f02040305030309010e0f1c2705011404080a 75
    0x103800111582c40c0c08200c00000140180007403c020009000100c90550420950078140ca8941c1c0203501d903a0915200280c59960300c5007040e03000020307075000310790765444515400f03904120307418180d0f0804040c80a010440781d0010750401394032903041c1113000b225160880c6900b42d20003072144440114034841e050110040d51100c0d10400500f4044c82184070312103a4800c1031204003140d0a64041c0c01400602c06002030238011046210341410007000070600076003440c0d02010b86000b000e800303956550f00019255019085131011a0b8000044031803400c0340e0040200034007400e01030540511f2a655141a02204600a50b511021000200e50106043c40d8040f00250003540c00481050780380c3e00c0762955003c151008001560181e8082c59903881d00d503405609696041c01d03922420751000140c0c1340d003010040b07034410b41d122070b2401c1c0c9283c2103a00542111001080e10041c242c9844030100f0800e2450191f4000007110820780b10307025107814190707492806005a10489800307070440104003000a0307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 338398102 1250 338396852 338396881
    0x30a05030c04091a12160b0c030c0a060b030705060403210203160c08070b03271e0a0201020d05191101090614010905060a030201090e0702280b010f0e 66
    0x520074030014103207903881100f1000d4960320840601c680c18008a401d0860801c0d50b0b8605000120100614280684c8507a51250111a206603146010003055400c1540001e008558031078403440d0441d0002130003070900c5001003440319216403191040c1c240003d06800c0000640c2d04413038000c048840282810000307815101100100c036001c40c002003005801100f180c1d9011108607010701c00d051101070030030689914124442e0000d10720302c10b0900130407900c00d840c803880e50700180f01c0311010702c2c02d10003034801545440c60042701c202844140100300301901400007510441c42c0d00036400c0341c5034980320480c1a1128843c41001c1200c003801d076486004114018007c03508060608c034000208041c03d500c0d118102c0d501c03c001000341e203a041004010314100b84c001d441d001001160b40030714040c510350010700855002c0c8103100d8100648800100280d0081c40701c00c000e095017044424a01306400020b4240c1541a1422070712107104070008aa001d022f0310340e140549207003400044003a1030700c4000c81d5940703 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 338399352 1250 338398102 338398111
    0x150c0a0305060118180e0c2107030218090c040c0e010c0201020c060a0e090901150614070c080c1302030609071422050406080109020a090f20090a080708030a0503 71
    0x4103005008420800d007131000c600040c405180d07080b440004108031101907804240c409000c60b844403114041da80e48070440c942c54150516120904070040480440c10601c40783d0010b54082030b00c51440d2200741e02001000d00c114080025912202200810441101d205072030001c0001d5122114440741d5004a01c00125180140101c4030700b5000280051801d5215442600c0082d403002e1100c519800e0451041c3c0e0800e8407007000348004c10400b08040c1047e001440360301c00301b000c10005c00c100002c1280484810380d8100070040c29850721100810781d200c003003402e21406890007808d40c102a6040b84250b90085d10024203076012521000303000c44401d41950100c9140301310801a90003031304c0d40700f1140c1020502e210940703c52980b8100402c000c840290703000090310317410b110a6100603036030016064190b1b002030400161a481002c200001402e030600c1c64801c940c50103a01402440744a805050083c00c102c40c410540c03030b100d80601d61252010f100d110041c4e4024031080300d22501590186500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 338400602 1250 338399352 338399357
    0x19021504090509030703020705120307231b090604062303010e07030302010506030610150c15020d02270102030301090504020103140c1c060503120c0c03120309150c0a03050601 77
    0x20907031104640c1040328410380d0700791a240e20004d207000403d901030003802e0080c203080300e03061043c0400700e69050305c921803070b2001403219041c441d4080c1000001018507a040b44118101c0f4814034050b01c0e02e2180f10403101c2c806104140304030005d1310740d2a00b4010181a2a603091980d48080d04031500d880003010211940d036455500c0d030344070102c00300080203104000d42c001ea0000c01c0a0420106050a007a00540800720448442409110038030031411140090240f03454808101d40050400c4549145040480030907640001844081440b494000c2c1c10b182002411962072154418000c40c1d001c015401c40c540580c0007480100206119544010340c468010304000c5405000c480561b808144122040744141001249100102c0d42c01e007080035110110032000c00500d8284400230780da41900c3d0404640c094030001c1c1c1b0301254141440317900500c520140484160028550300440c0582040390200200d20421041c4d0300c0d03440001040b140205c0458402c81c0c43c002011904401400c002040b6034107 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 338401852 1250 338400602 338400607
    0x207020607240f0216021210020f0c070b18091503030f040306180c1205010f0c0201050601270515090d080901180e010504091a07021b03190215 63
    0x1081d00c18000c1c19600400c64a69200094040341c81c40c00c0340c5285039215490f520500c080541c00848621420220343c04440c8418040b8000850618141c0c00f412a00d00a900109032008620384140242108d1210001a0b80160361541e01c1c1c2c81c3d0302e0003102442e0348c00c00e002d040f403008a400c00780109500200192940e08072003e5801c080313451170b030000810b02029500001e080040c016640324951841d40c1d5483c00c1c4035035440070789402500c0c0f9454000c000d030381100d40c1d00c0c2c4000c00c902584140c0b1010b181c420181304111030144042e000384001c40f4500c0c0441c0703114800ca0071011100d442005000d800f019084a580e080c401842040307258446400c0ca03001007008241da03690340d8481105181481024020307502c5010100050000c0032101e14941021000303942408418043c03058035066800a03203000851031900d092421200e511280003100c0c0c02e1002c3c00740300e15181e01051201c011505400e18003000c82941c4241581c901000c5ca0070300072034002c1c925a83c0145007480759000b451201c0b150060 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 338403102 1250 338401852 338401867
    0x609290a0203070c030809010e04021602060a12050411090609040b0115090810090c080a030503340c050d17060f0406090606050408010e011811030a081c0506040e0c010302070206 78
    0x72201e40c02c90b0016036950b00c0104401c401c2e582e109d01d005003811816503081d13007450040300d404034074400c145500030310618000c202590118802d4181003241140314006200c0d5003030604110f1001d207905003c1c50b0190361348400007091130424003440c901460b0700c40c4883c00542e203480003850b10761305420402010001665000070b00008108004400010030117400034421226140400c41e83c4002da11a407540e401890062000c42d4000064940c042001035240d0300881200042c80c4010040310b50440514200308a1824401d61040c00d40c07030460711800071100610504503095586041036a003c12900504100058480c208510131181d48030010384041079054550104070142ca40f1070300b100c2c0004802041c00c0000c3d1a0034000c0c01001c07600d482c02000000412368801da41440e01100c0030300031007030100d2030000301d8400b00900c42681b07401000701c0351150b10070010103c810851600e219021801e00c1d000c40c1c1c20389801c2c81111242d00080005003017a020480065010350403449060b64403443c24400306 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 338404352 1250 338403102 338403113
    0x20a0f0c11040204170f07050307090b06040e070f080708130201120e060901090c050f060f0714011d0d0201110415030f0504210c0f02040906090f0c0609290a020307 72
    0x10300103011100e403042e5015200c007660900d841081003a808080e4011f181c1080140c901140b404162019010081142c0d034031940410a40d110395880310055591070020403c10950101c074034403141480765518280c3d40c6030079a0403240003000f80c0c2ca641c001c84001405400541c043d0798100c006801c420340c0800c1e10000302d00d501d03060000468140946075101d80300f4004000000c1c21100c0640803c59485888403e628040f070f140340582008000300540000c3c03110144542c1030420020f1060172002442101d901c0c403d400f0254514014420091107080f0280000d513006005106500907412a614102850700302e0500c03884000031495414199512800440700d03509004031440385000e28442c81c0c1c00050200c0c40c6130780c81c1a0040100c00c100c85299a0030005066480303070060302d078048401184241441c240040201500800105402d8116042c0c0d0f0401095101c064105e0355a030701c58034442079844640080b0000070440d10442c403400b1f43c50216403440e100700030340300c1d0880b0307441100d061103682d0750341 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 338405602 1250 338404352 338404357
    0x60301090e0a0f391e030501050a021e0702220f050103081207081603230a060f090b0612071e02010906150602031603051c021206010201020a0f0c110402 67
    0x51310305215410030340b42100d152542811000741100041c0a00600e810003058411803140260090342c20320b6080304502d00360b60700e074420145170080000c2010b820003e02d4070300290700808082c0315480c00341c901c460085c0309890680ba40907801800c840ba54019200c1e030420182c0c2e090400300e42440d650721001c0c0b41c5007080d200300c5018500c62504240e0350b1509107580309040314003e0481c01001401001c110070300718200c1c1c4c1d01404200908000c60801105480099600114024400700d090f0410404c450340306c0700d4010808031200c40c044410045d8843e21402c0c00d80e020b080c004da8025108000076144414404545035100302245040303448003c016012009400c294400c1d240140e4482c0b400005202080c45103503003116007181d0074482d181c64000e0194881c024600312426003e8616408014540104c08940320ba84000402100c1550f030007032800001e41010305081c1c0b100d006040012280d5005201315040c020aa4940250078070501c0c40c1210111444c840c00c80309481104000301903610365002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 338406852 1250 338405602 338405633
    0x6090303060f0e0a0b03010b01140c100c0804020109080d050a0e0604080609030d1a100c0303060f0611070e060f090406090203011503020118030b01090c020f0f0a05060a0b060301090e0a 81
    0xb43d0b0100d061022030741c1c0656004511440c8a80d141c4100021160703044a4140d047e070f14007061003a164050022800e044c629000e00e400a41828400d01b41c955540c04039606104500c00d0300c0da0490716880c0c4512555441580f130140012443c20003030780f0044c0b800b802c40910300b0200200f42500d0240c441c1c000c0c07420600240c4401c4015400800c0391000c1108034001c404a000305d2034140080d07a400132000400c1900007541001c1409004041c0c03409061183e0000c6001d080d11007131a10b121662800024200c01d00e09596190601410713201160702045030503a14054000140b0110701c054001040000c07040c0090400c6802d26600c0d01c1c5240161020301aa00c10882640d00034949146113000141c42c20301074000c0b810304004c030b0074802e00c00035000798545415a4018040082d609407115416450301824010041e46031180d01b8060f42d9220700010aa28020b104500b52606900ca5441507025507248880c800da1280d81840144500092a440303e88844401c80443d65100d00507118030300441004d41 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 338408102 1250 338406852 338406869
    0x311041203091d0601050904051e0c04170708060a020f04030b0f0105270a05070905061c11030412030207020406091b02010e0309010806091503070b0306130902030a06090303060f 78
    0x100700c031451251100d4403841c003c920350704880c80d207000000c11a1280c1011144100d55520100d44180344070203481e10000e600c800c1740320b081e04202e112a0400e8010344501840c052074440c015400507001f00d640c40c11500040c2c0204517503120786480318081d4000e8544240d800d0010b02c00000408c4080b9041401030300c130b001c15501903504100510641081519102d800d00000c0c08043c9030442c400312600d94083c05503600015075031501581222401d029520041d4050000f29189101c9a9070b4104003450714500f038410049140903200d04e4400b40000c0760080c00c045464510240c1d0b45001350001c1c40300510040000400a40300c2c890502164030301b250006110949072210120b0303540901c101c0700601d00317242c015410030310403400090014000034403140c00b6400c00700c00310700c00e40b01500090001410090035680240e0b100ca8030b06d01d17070350011200d852140550a000c09400400b138400d143c803094000e4007500281406032200005401d44000031401c00d503440c6400500c8100506800000c1c08958 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 338409352 1250 338408102 338408117
    0xc030c0d170301091a040e19051606022a0a0605072f03060a060f0b07081908090c010e130506010c06020a020f10020f070f11040f060305190809010311041203 69
    0x111741c5045543e1404405034000d0b0b18018081240340c0340001c401240340702c041c0a101e10a007061800500b040a8003248181c1070000701c201052151300492060b20941a15108094407400d002c18400c40750100f174920b071b0300081d07060001d00c1102e100301e004154490107440450213030110b40080c0c00c0c0020802042004145001c108990703546801c0c0846034100312014000d000325401c0000b41000040d0501c1403001441e8001184070800000300145c40d13003806440010941141c1d0301c800601001000c86800e030f032074002d00e400d2602c00d6000704101855600c01a040ea0196100740d20030000500c0701510503814400c282d0030a90018000780020160b00d03569030f000d4090f010b88201b05510b00f91008091034032090052007145d00c40f213680800e80310040c0e080a00c20741410329905102040c480d46505082d0080c0c1000010b100c4110660420002c581c440d0045403825a0319040609503141100001407060001300001c410940c844c0d005400010a20b888251600c1d0b81c90000300f40b10003e9400c200c001c5100d2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 338410602 1250 338409352 338409371
    0x308041e0809031b0303030604020a0915030204081c08130303200c10110f0f040e040606060f02030c0607180f1d1f031704050d0302010e0c030c030c0d17030109 70
    0xc0c13040d0488102d407118460b10400304180045c1d00c030700000380682d00560380400d60f05480c81c490003100005010406180e1070b501c101e02402401796005011340c14131480780c5c1c015421200c00c08514011064201da4607a00940ca516144c0040c04c03008040c1502003546803c03160140096403090f1100e000f21499203541e42d807152003406e50034940500b8818881e40d00c0c013403442315006010000c075907511740e815030100e0707980c04002300795407090050b40c0048003510040b00410003086026448541a50b030310352a0140301600b1030b1400ca0740c0e0301c00d800000100d0381103403001c101c402c0e00410300421a40845901d0a4100d0345174001000104040d500c5504a880d80304103604490084501d41c64211402000e4900d29412075818100c2481480c44000c00001441e000049059056416240544002401881e07038001c2d0341002030203031079503540402d1a8041c0d0303046580945400140b854004070064007030300c84114000200420022040f00c00c0d02e0f110807010700c65144c481080d0045007e8a82c818000600768203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 338411852 1250 338410602 338410609
    0x160507141e16030302060a0e0723030c040c1d03120705030702190302010c14100c050711120a061107060c09080c06130b09010e360c0301030308041e0809 67
    0x500075040c2d441e122462000f4400300f41e000c22001d83c007901c0030383c001c0340300c1030092440c910340b001c26809031030042084206030303e50100505200d01200c03002c40485400c4200d480801c0125581213500f0b00104a9034581c190f103506815400181c80c0710003d00340c41e036810b2284025615680081c0045545420000349881180303010300030348081506015a030300f034040c10340e400a0188400c0c0d41000e06150b01030380141203880b4041022a040d600300200600140c1100345000d8810b8105200403a440d506001d58100d0a0030070b90061102d41c102d000041582c0183d40e16040024682004450810341c010410034021450f14007a204c072001180e42d40c00c6141d442c0042c114280710007843c404c3c1c4618010024001100d42441d1104192070420740400d641314000d5006031444848000816001144050902caa4038400800c045922441400003515111001e1034030100c2c00040790303d40c1c0808000d10050001c28442e80806910512419000e141003103550380c24102c010b1107100454501030002034802c80c030706 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 338413102 1250 338411852 338411863
    0x18070c020910050d020607060e0703060609051b0a03020c0307020604080a0b0a090206030a0507020a02040609150501180e100810050412050712110a06020408061806160507141e 77
    0x1031260403480c002e0341c1050005042d80d012200c000c1d104400115910b030034400203500090800c11281e0483e02e801c0e40c0d0785081005010b0314480c2031482071511001814081e09005a950907001840d000382c80c2000202d0141c2c02900b10402b05071803888144000c0005071940e0340203001a2103403000500c64a80325141c40b19550400401da00b5106040443d20340043c0c551006607074000650680c081003a5880a000300d142000c09207010f5071280c140900000e01402a504c4160341a0080900c016140d0700c420041d501c00d44621040c00c0302c0035001100301710102180d400c29421144981a01e403100d6955031059140c15250b40303040c030701a81c0c0c80c810301042058002d6007801082e818103200c0c1c240002519282c6050f191309031500b00340321024100340700c0c11206125281225920810454a8948844803244e41d41800c80702034921040d00b0a14a201c16000204a071117420503c03800312006444402c04c0741c164100040c00c407850a11080500a504c02c1030003034414030a5071544c201d03042040321040c01e1402 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 338414352 1250 338413102 338413111
    0x1e070501021e070804030b04060b06070308040c290f04081b040c031109090405010209041a0a09051918080c0d0816090303030209030c0a080304091a01080103060b18070c0209 76
    0x1e02c000c000303240001d5858000d0760101d81d044024241c01d50b84a0600c00d01a200400d6a59442080002d042c4201600700d0000da0145001d90040c2408a403074011044030a10031065006400d64002c00d15440c101286000b030010158001209003820b81c2d400007640340800e14070144550b046556101007080c2058458820041e5051405101070714404000107480e10894415034051140b080000b02408000d404030b615a580c09003007001400c00d40c0c44500f11100701541d1b140d02c0740c1d07201c060028410083d0b000b0300e80100d44400c00c02c4868000444a0b4004040d80c5885400100c030b10881c800110300c01c8006440401556005044499500000184000401040d050741d0314418900f079034a0b503a02078102410380398941001683d404888002070310700081c4445440c1c0c400030040300412501d00c044060001c03a00c001400340043c0b5070030008550413141205683d400a08850010008600b40350045220140c01034410500c03c8280c0700d030342d00101400c481c1c04d80801da843c05140110304055880d80d501 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 338415602 1250 338414352 338414407
    0x10806240f04090521040807050603370c0815100206061c0c0305031209010b0f210706030b030d18031b0b0d09151a061e07050102 57
    0x1020034036000849540800c00740300e00480c0e880d40e00d801002800c015030f0350300b1a6210300906030b09101c10b803191150303031040c00303180b00c075000380c07100042c0301e0a108040e24045c6001c00c003140c46a00410b0120118404000781141c0503030f00140039500514418407407600e404900380e0f2408803600c1c02d00d0307014500c41c100300b00c2d29000e0006c00120081d800d40c00700b84550407040495290340000000c1d00100b10235840c1c580003400c140c1200d0400000c0240c00401803882c2c401c03002c00004203648150401e422520104044c94121040c1c0c10082c084d8036044884520382480500040c005080d0100b8641c40c0c4111500b000f0086991030311341281c5440e007001000d500210a00e4000121a480c0c0721410071150300b03100081c450703400340040b0306440c28240c5165001d841c08132652a12000c29610320f00c0640440c00d800e0b1404111601c41501f002034a0040b400c408800c5500e92020305101e1081c03149940c00089804c1c0c800314003903902c00c454080c0b90002d02c1c200d40141c1c0050b031038036451400f001c0c40410500c80c9900 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 338416852 1250 338415602 338415661
    0xa140307030603060b01110a062c0106080105010608040503070215221701020f040b16020d030e0a05060c0307030e0a081504060c2f010b1c0b060306070c15090209010806 74
    0x1403024005231000c0115440100410f004a1808490030001c00b50003031120703040c80210040085000550181c422204144003e20880e680e502c4183c5540b0001d640142098104111000c05828078000040806103000b40c203524120703040c402c0803040900d13085a2486006d0b15502001404018801c0442c1590100000c40c9408640095000c070340c070461090316480703000413542080d4403006045000803a0740140460003440c040d850f0040c100039020241622600741ca101c04601804c1142c2617a600310061001140351490304c1e2001c0c0c03418040c3c00d50190b0300c580c0c0c0000100c0c0610082c00008610420722502c1d5003141404e2405c0e1007524501c1e1850b8081141c002100034464901034400e04800114125000d1210000074400d0b024285034808244c200e250340010014800452006090391401251011420788a0710105600da48041c7c440500042c0c00460742c10100704041c19980c85c00c100c1f40d0340018002e001354045101c8c080241d11400d0240c00150412449030a810740c800d4114905c000d0504 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 338418102 1250 338416852 338416877
    0x504090f0c062c0f030109050f2b0806040f0c0509010314040f020607260301140909031c060302040c05220b0d1e05090115050618060a140307030603060b01 68
    0x10090489103400d040070184660800c0e5542e1681e1101620313080c2d0107402401140387d141881c550307800c90349c00b00740e00c42e01ca840182000d58a00c281072048940100000c0b5503c1043c0010071184584046c0c155607115a942100c50711003240d034412940d4003107098880b141c89a16181c005011601d00c0b210f05040500e250080000080120507400305d041d40c1111016111281410240190582103d40da106654a04100101840740c100a14100c865505805190180074014801000300075100c07180923034410300047c100c0d00c140d10034000c45070f110300d000002c0c2c1d00c0d071746d400003015aa000600d07c40803990006220f002c400d4100e03c0130249400040780c140d84980b51051040c503512540c1c0e070f205a103a07a100da6118010100e02509103103504001c409102c50b080050740c2500030301550404400800950f0400141d90501c9010360700c94080b82c01503804031505040a0110710303440326515804000ca003001c3d00d800e20300c0b41006580a585156000140035003140303010f00840b18049901c43c1482071090710031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 338419352 1250 338418102 338418137
    0xf0f060504141b0f0c06040309211a0705130902040609050d0b0105010f0903051506040c1119110d060504060501050f030c04150b0409020c060601031e050601090504090f0c06 76
    0x101d0106030a102442d5403130107070900e032101c0d60080b00b80100090180c00180428190b00418040540d0200c181050018103c0028600d503660a00c0c80207066030f131803c1201152907030410840d41d005406081061074540b504880c0305406920b40c00100c00c09a01160030322069901c5410100a010140c400880440b00d035140d5030080b840503c55141003048040401c0741c403d115074000c800560348001104c01c03c0746000300300e20f00c0d92801c440c0305000c0d03403130910348804d0765200c0d810b1440340c8901c11010380350444000c1c03561024401201c0040c1e40c44c00170450b0030080d03a149c00146481b154080c0c0310000d40c1e424646000d200740c0781d041e40a41e202e41d4aa41d10442c19030740200b940d0140040403180000c81e1007804060750b4804555a10070001c0d802c3c0860000f410340300b140c004154a05000c42541c403c0d41c2d400d40103404503082e4980381c82e1b60860315400a10f02c0f0195a11090300180c050401f003c9041d583d030300180a41d0120f040031a1801c241c489142c0420802c13801a9000d0002d6042c84d4260001c0110740 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 338420602 1250 338419352 338419381
    0x10e010801061809020607080c01090303050a0510030318030b0f0a0c02070311090a060503060901090201030f110403150213030c0311010e310207080c12090109090f0f0f06050414 78
    0x80c2604941d5410800046655401c07c03620000e03813110049840e12070049510f8001c0580b56001c3e03001ca403c110001c0d03100381551162511030840da0400c1100503040da10200c0c0c0c41004840c5041000311000004000300d0b004a014502c00c02540d22012164507110250b0300a0791a008014070541d07200c50380c1400054074004c803600001d0800d807802c110070381e41c0a40110240149922040c0c06016800034041444019000680900d00030380301030000c0707904003402100f1600d1603e40e1300c8441800340f1092000551802100c11f40c00b82003030026042c51003100c40c034410702c2c4481e0301c01c68107141081300c100b017002002d0a070056042c00c2401d100345150810008030700c1c3c1c081c9100d00030140c82d0450b5100c2d140d0100c420b04c43d08070704481c08021520b6001c54541fa260aa00290481607035100e044490003107100100120703120f40c14180e41d24503145160034400000707000140c00000c00b040e15100c00c1c0600c5880ca110b0680c0c0102d0441c2c000c00c100d4541014002180c40140e0170003044031500c400c204044502001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 338421852 1250 338420602 338420639
    0x60a091e03022a0409031d060702092205070f05011202160224040306020702030c0307080307110f0303030901050415020a090b07110a030c03063e1c05010e01080106 72
    0x540401e905120281e2003149183c410b19801407910740c6a4050683c00160b024038001d80802c40382d045a03410301000340724011410000d500c50034000005126041c054a01c0b41480400c03440c03400c10010340d075036650a03c076442d00030b040c02c4000500204807560388209094411220382100f18074202501342d05207038040340440c0c0680218058024100c12008800a071880303c0718848910340c5481d26485e0442c083d42c05800180d10900c14641180040c0ca00440d00d8000c030342090000f0b40c6020300a075104da0091a200122a6002404852184454400703000441c8241940f01c000180c500e00707840c2000244400a440c0c505061040c0201030050f5006541030094901201c0c1064403401189801481c02c0b0805012581003c4003260000401c1a6030084c0800d881c400e00c0103228815104100f25500e9805130306030341e10180c2c8001c000e8000104104011501c0040d40d0006180030780d00e0b00c0225803c0307601d083d06400103641d880104140406000d42d240980709003002408103d14091041100362100d89 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 338423102 1250 338421852 338421883
    0x3040b0c07021c0201210e0c190603050a18121206050105040b18030307080a020c1008241e0102150601020a03080c040909120216030c0b0c010e060a091e0302 69
    0x194240c3c1568000d104001d05d000d4038280c076072105064651004050300f159480740e2043d214032075014800340307884a41464015005032803c0300300c80c5880f004038042c050142c400d44407203540d41e00211106003001410310a00b40103d018401c002c1c1203a500410300d00701420307524045460843c00b400399aa020040b078040719100e07200140c80302c40061440303072075074000c002d80c40d03051000250444c01c000b03040c03001d86041610380d000d843e00c1116000902079015082c8010030002440e143c0010340b207001c15003842246002c00000840d5103035800005c0382c040071203002c564030700340440c9101c5d540e1981c0c1080700584414502c1c5a602c854244040042d5031752146141c010203001080d030018401441074810389006113003008040c0600e0841e42000c00c0301080400008005001d1900c1252982044400c20b81c1200c0d400b95806041e03500d00340c4414001e80000300d00c00301c25500c0d04803200e0709032001c0080e20700a026000000603480c159152540e00e61721a031006100f8041005000400701e50003203a007003c01e68009 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 338424352 1250 338423102 338423149
    0x60d060608060411100807020d030c11010c11101b0f0c05030d02030f011e05041a04020309030c07080d050d0b010908060703050624041e0b0a0503040b0c0702 69
    0x618000018108640100e00240300380c10401c8180f1400c0b0090510980050ba00e5070a012a481411910581c04503410030150707018011140d02c0611942c8480c1e41c0c0b42d028640751105410340c0061a081d40c0350a40c014000488a510301502c19200348103034402415548001c0028028401200d2086440c1c190300e40180401c400b080c11446005420003401164040d0599940e0046000305800a405c01e803a043c0e41002d08400208080808086118049040340600e01141d8900340411001d070009030104076a41085400d030a400780c80d00c1c0091030054030780f070001d9515000a021904e290811580c80b0100d03036407140f1910b0a640f034100b012100030705201d4030003149040a401c0142e50300c002a030301501d003a128510420007030315415400140921070846482c25000c403245c081406100c1610f183d21120030042004028000452240744004c19400145020040c0d031104501c2007030704108070000108400004002c02c100d18000a81e600541c001c1c1c035607042c41060f40115051217031403051641d0741042d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 338425602 1250 338424352 338424379
    0x70f030218040f0905120c0d0804030c0b0c04050415030b0f040201051206040902060309100c0e0102151f06050a0306060c171e0307090315050f13150501140f04050f06 73
    0x103134100c81c0605030802c084a9460a0504602c6a182e1008074007885900455901140442c860b030031060040782c143c0d40d94440c91a0b141c86040da4594080c2402411020401001802e5190b85c000d0b010181c202500503c0c22602d035050900d039108005110501849a5000b0000140c0e002401e442600d8085000c41c0c1240e594803021400030030a400c0e01070361200d070100802443d0390001600c421031a580e0741b0b083c0301402003202c0545054a0507544d890140e00640c0d400d016044100c100e5583c4503101100941580b031500c4808401d2002c00d0b0401c0000541c001041c01956030113001d000000c081514041078080c411381c548901001600708150101c01d0001100001c02d480340f0710740c8240048800755a40c0d207083c0008042d20300981c2e80300803100f4150429000038903500c5842818803c04071116071400c40d607034282022550b8050710204a0702030848500403044401280304a5018040306501c0c84a2a0860410000211000c6003094400c0341844104192000106d13411070300305400307a0b0000380311400f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 338426852 1250 338425602 338425631
    0x90618100501092309030d0c09210311070303020a0303090203150c1809040b01060807230418021918050306090303010e06010906093605070f03021804 66
    0xd0a003503040e5400d080500100c0c1a80d41c80e4000c2d14500500480c0050314010b204990083c2c1c2021604e22401e5042804040c0c00c41e0300c29002080d003420546000c1040c1522001001440c0c415400050f1034802c01042900c10550031041180b46041004014507809103981d400039a00c2a80361402820180c0701c50209085450030400b491000c03d008070614043d1801009990460b0440e40000c2e5980c0f00c0e04410102c03904101c04420b01894002000c1c46143e0700300754050302d42c030310003628007410800c0078038023610282c440403188960504081c1a4039512460170600304070700b0481c0302c8940116481000240c488049060140780201414101103206599146460000c28190340c071490700b5003d2001042041c00d0040003c50503a48000c4036890b0503215400111007000301d03030107180c001c1034504405000e030741a84514075003241507195140541c20455450f5440010205c42495202602c68051124180d003011140848110501e421418022a210410b16a64801d411a401142d0f2032000e82071010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 338428102 1250 338426852 338426863
    0x1030c1802040902160501110405010518210105040c0f0821130602030408100e0601090504020f040207050109121e0c06060b2205030c01080408031008070f0501110303090618 76
    0x400f406007151100702e40051080b0440101d64211065480e000950440189110581e01941e82c103030f540e5400c0088280b08011b0302e8007495840d075440440f0110300b044a26245c507003024401049000407829050a240c91180a40540c12451079182040000d110104e800142d4070003550381c4210b0b10041000b0405108603e1090b0700300d0780c6101307002c0b0b1004140160000010300c100c0c0c0c0702600b22000200b00011000446503400107260081d0060001080280c2140d00556080380c001494101010360074070001d0101d91000d8812206a5158000032040c0b0125031079041640c030b01400c000407410004046501510b5094400030b0074040d51292013010300000364400c2e0041c00d05103108584c0c2d0350310b02c2a00c074500803500620030105001c030f0802040c1e0341004030382520f14a40603107070030308152120755940031183c20041c4500448580f800c40080c00b41c1c000c110320002480c014454050850500d40010060307462607004424035401007051100c003000004850740e110141302040c0d000c4042c404bc0060401c2d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 338429352 1250 338428102 338428109
    0x1207080702091302130903140f0a0807031e0b010809060402012307020307141c080f07031107060503340804030c1202100f0c091809050a0f050106060801030c180204 72
    0x6520141c04181c10345c065011034912406511403802c80282410150b08901c03884406400510702848001c02e202d00a5480030f422845900700420200a550100c11181e280b84a805403490348a01104515580103c0101c0c0c01c2042103020381151704c0c140d00041c0801d142c000100c0d481c040500540190441c903031056030308044c0d004060702e10103940c139900d41826000320340440740700c0d001c1e010406042c82c00620101055581c0140c00382c0c141000a186940c50303801c0301000f0f500f4050340c800d00000c40042030100170003400d0242c42e03c0703840e42004e02c00c0f148440c02c0c1404c08141d8000d2104038000c4014001d00c031702c119203070f5490080b415540d10319080342c5541003800018401601d43108180c45003a0086101c0c4d0f02162131040410101140c2160070050300d0300800b09401054114600340030101d07916184401d000340784400424089882e69405241c84160702c4203941ca10448810601040b20a000b1a00107010034544000c1c0c550461702d6040010300d0380d05c124440784c1480c0e00c0100044031150140e8009 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 338430602 1250 338429352 338429359
    0x5091807091d0603071d010b090a090207060c033819030501060302010216140d020f060d0504060b0a030b0a020c011803020d080702030412020f0604091107051207080702091302 77
    0x380b80058215460a043c0c42492003409040030100e00400c200141d21090080c80304049540c1e441d0041c400e541d03a20070310660350040c10554001c41c00c01c0320344c0002d00c5d4651180500041a0a44c800c000342220170801181c0b00042c61040b103e81c40030101c018001a500e81d9807100e4140320100f00004031042c90440300303101285040d10001050007010750100086074000c2e000c0c0c900d80b80c0408207441d0000064054034048003100f8149030039600308042d01c038460300d00c0a8881c40300d1400796400240d20f508900801070081307440c0d00820041140c540a0160780c818156901d94055045549211410f03000606002c0f8160f40403541100d180402d411500300309010b43c4c07801c03a00c11241d040007912594030b1280e0101082400c00400e590a10010403a0308803071581c408480c034159140c1c02c1040c00305100c180d85500210a0001141301d0381d8500c140e050450403039115079991009454110305110381040c1d1490340e140184072540c085640034040700e03c51541114098410340d038100e04400c0e0303241001e41c060740 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 338431852 1250 338430602 338430629
    0x30b040c150c0308070c03020f01290a06080402100c1e0221070b0702030a0507080303070909020a09090b0d120e0118050f010302030403020715050403120509180709 72
    0xa2018000410040c1e41a44802040e956007200701901c200d000e07403000034000381d49a00010b402610441d481502548644155040240c0481c00a801e41c3c2c003450032145910841441e8003126031907a01e0b05251a94103030307180c5075002e00e000d03c007402c00310009202034081c1295000ca4803d2900c00ca0750030414a9220704460314021040d1003503041d00b40b1340d4104a0040d10002c0c0802c2681011180409140704188014001ca505180c40340741a600f02c03010484e003601c10350b11079000150041c40450040c22041d8003c680f81d207403115000b00300e002d141d40b00880c071520401c4410f50380d660110b06001683c1d0214004601000180c002c103a407800c8440c0060000c0301001d02c8072401591100c01000c440c9400d0341d03007003031940e01010800e00000c1103200741d41d44000c1003e0b00312001d500903000b440e402030081c015030b45084d43d200711150301d0442e4082031a0000713038005024800c106500c06104010b44461900908010401001c1a2009100c601c0c001914910b0400156040d1061003882c000e000706100386074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 338433102 1250 338431852 338431861
    0x9031606140708060d02040e0a0b150a051210021b03030f0103031206061b080403020d05030d0f0614010e03070503101b05030c0f0d0b060301030b0403110309010509060d0204030b 78
    0x244a00072100e80c0c6511207901140c2c00500c01d910190041400601d40b4289010381d070b080000604001c044158a030080c42444c10100d4a8014020300c44c100c14030001c0244401401041a05866500107904c50601200309600e0640f0001c1d4206140710401001170795403a44101d403a001051069845400b44800400c21464100300801d030b5040f00e100741c40d4602503064044141d01654514042e04000441441700348007002102c0384080c0895014070022440c00d81c07aa004140d080d1203440098402d5031001410b101c0c612624400e824000800c09003c01101c0d0a000f4091205801511380a041003807a20042d1003030380e01031010302e000b40701c000c08990507041c295581202070035110001075900301035005400243c4d402401140d125490700e903291407504c4071400a980e071a0300b00300300b80c0e94441c2d9208141086600c1c3c001c0154061801001925107510b01480e004140e10b828050101c1250828400041d03ea600f100568600040459226031078010a550650007801aa480036002005000a01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 338434352 1250 338433102 338433113
    0xa02010b030d1103070b0a091b0e1e040b06180a15050301020f0406080c090a1815210503090307031a10030b0a0e0102071407052106010608090316 64
    0x218540318003030302565200d940e0001e056404482900258103550410400d0200080d81950041c2c0d2102e654034000580080070340b2119500303104d408600381141c41883c414001c0c0140744500c17507840900300810b07007100b10181e0b60000c441480074000034a0540b07400049a61680c40d40c0a900c15441100e00c40441842c002d21040d000d003080b03c00c034460082e4650740120319810180221000d090300f083c0c803a440d0134645401100e039442c000b41a108109000d008000700c55031500146c1c402001a0b045950030100007141080131a003100501d1640d1200e44901003003c01c032141c0c1c2201d44400f10121203000c1504031704045044d482040607250341401110343c003108108440001e6074024a01d110344030700d02d503626405007101d2000c0c0d002c080c02c0c08802d000003601107000c5400012040402c100098205055030b030703032801020300f0010101401d0f00424420310460515540711782c41f142d40703000c42500242c48090300c0c5840d170106008400800c04400009036400b003003001224004840386403071505d102241d0510 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 338435602 1250 338434352 338434361
    0xb03011419050906060d0c0306050705090f041515030213030f0c060f0804110604090f0b0f04090209060d02010314180c0402030103021f120e030c060109020c030414030309060a0201 79
    0x440540310506041c100741c0c1482889403912888041d40140b14585880c81045444020301c901246c0707201c0f84110100001e04140140c6c0e01860090b1500c80d1200354140412560702c00001c462405246044501c92284500c541c0385c200b1100350001000710042551300482c0644a841c001c10000054140300004112031290601030850003410502601074544d0000c840c001c10701c0348080001034000005c07402141903080321825903880104014680381e580c0c1419000d903041c0940011445940700360401460404502824524008a4003041601c255a0008440074006806a8090003001541c0c0d8110390081c0e01c4061810101d03410340540e881e100c3c0c00080010407801000c10309008a2404400c2e90815000703681c182c941c014100c02d043d0010030724007102c20328000445001c00000902c030460440c1076205000884d10600c0146541c0d911820800d80307003210690045480500c10401c0841c1030502100703941c26a101000c440360440c0ba0500001d1841c09418100781c0c0c131a400040142d80303140c05500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 338436852 1250 338435602 338435611
    0x4170a06050a0501080a17190c0302280f050a021f020706020a0f150f020f07110a14150c013608031801090c08070f230909010b030114 59
    0x1d004560320081480c0c00d0329805e00c6091000d17400820014000751030038141e10907203101110f55504110708190180b4900b10560041c2010503003e81c100001d15a0600407195211222070b051200708080e03c6210001864046000d016801da15202c001040020b0148040c0c2c90b8000300380c00002c1e01c9020750412907001000c0050054810401c1c0011a00e0000ca0f43c1102ca030740181c40f44083c800d00380c40313074034161501e100414801581c401380004807103203501c058030b04201c0e02d10761507403202c5003841e10100d1900200350203171241c42d600c1c1d0100406600c0340d40b039650000d826621f0406a880c3c00f001c00c28140102c0400210b00d5007400c041d401c284240500c00c0801012040c0601c001da000b801c01c6d00040451203c01034542d1b10300f080003400c05c0b20001e854038280740114000040e0500c0d85c1d00c8140d03d260640e00f00c0300d000c2d045414100a16840c4945080151206060b070150000d852400c04160b500c0810105019180c614009150b07071000390710450038000d000d4000d02c001000c10003a0301c51114100e5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 338438102 1250 338436852 338436863
    0x804140a03062c06100501030f09020909070f06020102090a0909030c0f0b10060c0209060603061206040c1d091f06120537060b0f15121b07120504170a 66
    0x11059600000012110300070300b8004e0100e1760a9043c000118050800c500c46a0f210395100c2d0400c10042e100c0c806e1041c4965080c0c00649122400c0000c3c580241900e0b13800032045a0041c80054819034401108101322101581c00250300b855074581501c0da01c4101c07402902c0c54148650282c244501080b40511841924070703050030050311864191441e108014002e9001a02e0b00c0000d101800c04000031600840000c1c01031414908182a03d49408070840c0e0403240c919001108000c0b9000c28400c91a038070800304180000c0d494855900c0d503407a00060242650000a00621082401245c1c004c0001e40003020350803001809604003542c0d10303621005045920740f80c528113000c01150000c2081100c00101845801041058840c800600503080c10310703500c1205102401c549a40e8500900700782c4080b0940591a03614803544440300703610040031032404081402134074042e0500f4070210341c419079002c0c03103194071440c0400c42140c00380203580024500100244c151000140001400202d02e031090 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 338439352 1250 338438102 338438171
    0x10c02010c08040506070c05160b0d061a0706051015051c0b0112020705010609090c060e06040b07060e0a17070b1003020303030408181008011409040804140a0306 71
    0x3200110b030740000c01c80f030180440d0005070110320b043d841403d00d490300398050001c0341e0000d101040200003048241c0c0c0a110000c40c0003840285c2d0b04c5950040000800c1401280c41102003611f140385035510980100605884d9610300141d0f000585072024805800254040394010351602800381543d07215400342514091001200707281100e650140c28140d400c182d5074214003000108910007c3d41004404880954071204017040c245014842c4200040c090154803582c0303880e140018000d030034520f030142d002d103000b0401070080c41000421030303090507030240001071b24a85003100f15040c0903c030b200091802208004062010f031110024000b042d0250707541c80c03601d40720604080055111484000c3d00b6800a000181c08101a1405003804285103004000c100054000183c5d85d03044d0107102c103020070061300041c00640f655500024030654141c910746254200f039254601d02c0e00607842000156050302d0700d03c8203661180303880e42004507030241c424411880c40940c20030a0040ca980c4444200000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 338440602 1250 338439352 338439371
    0x17011b051236010b040f09261206030a050a0b090f0601080c090c13030b1501020f060f10030f08030906090a03171302090405010f0b0103060e011202010903080309010c0201 75
    0xd07a005403082e44000d82500307203034800490342810445440c0306911950f0301c440001140c0c0302e600807002c56a90202001591641628003070b0700b180c0840e5800311258001c1504140760f41c00d01e00488140102d02c81c41e100180c1e031840b000a142000c113000040c601d0280d18032620401501407038035070268030002c050b03801d0b1071b44032007200341d80c0c0c02d09105a4510341e020135a010042d08180d05602c0e08501d44543d02c40c5050200c0c203a01c0c085e80719942c000c0305d40120300000c10404820440c406514448244050700d10505515465035854401400c9113510f0a206400f10301c40d804e4068100c07005540c0001e402c04031081e90304107887c40b07402c01c03126807070140668400a10396100c0801c50520113a0705486141030303c42d5180381d400c07108000602c0036901d860889106000b40c0d0700d80040740d2145104000120b20f090446072650180c1d01440a0340e414541010b0040c4101c01d8100b4083e8113641140d0203400e00708400d400101c1e441d100d00d40c07002d4050348001050000c0341c203040d0000c980c0401c040d0000d108047c1d2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 338441852 1250 338440602 338440621
    0x21e0c060c070611161110020601093b060601090e060f01030204080d020307050f03090307030305030a09081b120f04050d02030a020a0e0708010503030a1704060b06040602030703031805060117011b0512 88
    0x106007c0c0c150068000170014010b2881541c411051050301c000445600c04070004009869040440343c2804200000c00c0004402d90800070150f20440c2842c1000c40640b90030998000c0303031809400701c0e00c20b084a246001299209906880007040280111480302644a001a45035408002c0c15034190150703041c0b500d400107002040b650410300140007030008511350340f4111003640010700703100010f81c0c9420007900030030640303005003500343c014044820487c02000d00144c6481075540075001040014071054002604083c1607070101c68003540c0c030246038106803000078180107000310001c0d4071204020003c2029001c4040c003a10813612501c403000c86903200c01c10151b8034054444a0f5000a681300f50383e070030820300503121130b402521543d0007058201300d440005013542c1180d00104010717032011075840c0505505010300c0504a8246029000d00030090710b4090301c5d140140a520420680740310b1905582000754021121a0340b2003070702152000d14480001d00550180c0802c0c5035008402d00030481700c04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 338443102 1250 338441852 338441869
    0x90c0a020307200307030305030702010c08040c14010c02130203040203152a0d060b1e040e010501031104080106030807060b091302151c021e0c060c0706111611 70
    0x82a800a5040118560781c0301d10f15865030466410500071594548500c1c0c60070010000a18807a031a46134a0b850110300007802c6650b81c0f0748107800c000c024014000482d607511045025604040400180c0300c01840041c3e8220040403c001c0d04152188154446070313a0301c1e030155000f02d100714281d80c00300c030364104910300c00300701a5440f9642c01d03030f00503d04c001c2151300d0b07840d0791820340401e0149080084500340107045512982c00b81c840040002a0251408601001046040c0e80700301b801d8205400d0001c9040311440502440703040c55540e0015003050040c2500f80e500500c0114000e02240f500e81c9408100e54101c2d0703904403500703401d24000c0f580f540b40c007084440c0309071a14103040d01d6018994003004054406480000110801044201010100050344420007000001c1c0540d0310313085e201c0c8260714104402c0c1320100240050140b00040345020480743c0d0002c0c5584a01c580b10382080c01c00e2002040344404d0400c005100080c0a151a0141159101c09174002d00781d0884001400382409900c2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 338444352 1250 338443102 338443117
    0x11181005071a1803031003020901050316090203130f0f02010305060d05101d0a0501091406011a0f13031101030f0b0609040509211201150804021210050114090c 70
    0x201c1c030310942d90009091404865500000080c1e445801980c401115800c40e0b209442010540305a54400d10075400d0a0200310700515080e4001e00a00c20103484001640b2002d004402481c7d0f000000316440b004841c00300c0103800c1d048001d5040c402224540300e80e800801000c100c0c0405c0c00c09000800070314050b10001700558201c4003414a11813541e8103000140000c424103059140f80300070509118000300a460300300c6201c1d03800080c0e083c61074100140558100031000a03e6031081006006e400c0002481d0011888030740d01040e1a062100340b085894041d51407840301180c0c44202c00024401d0301516513040103401e80301040007000e040c4408080d504100c800b0b179003185040182400740d04103680041d60014804068811208169081c0c84440541000b0100540c90101c1d400c8180b40003600424010708206c1d00080004d90400780c0a0032013000180040d1180c8154ac0d800b101140b01449101c000c8800068104001e68503030504202402075840440d0080c8401000200415110320403950780 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 338445602 1250 338444352 338444363
    0x10f03092904030306050f150703020a060e0102040303080a050403050a0c1401020a0f030506032a12010203041211070503120c15012907020303070609170d1a01081b0d1118100507 78
    0x5460410808e190325501528045046100300111180403c01510841280c405810000741e515891401c0c0204224000744c24084104e1401c801d00c400207070090216611292941002900a401b40c2010300745000f034039464002c2540002082070020313602402040082e201c5407001c0101e40c681e00181951800181d51030014490b8440b04461011003800c2510903280c0001d010180d030001030401e41e402d90300103039402c5400e680081c140e4800344d0317003001c08014008943c000801c0c46030f1401001a40d14112100700400d4810001460030560031305010410440540d044404840c1d40d44051f0310208203109415801074183d410b0b045040c4101c203400b2605c07800d80060080d0304100c0c44e9200c44000b0400420100c80510307500d20051607020300034010700318584100700c0004040345292408070a84d00352400c100c0c1000074200c00c00c090044c15036015140c40049180703150f111300204401c200207102144c400c0d0250280460f030001110412036400c2c0c009041601e04244454100100707980501401800822 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 338446852 1250 338445602 338445619
    0x3060903051b0a0203060c0903070305010614030c06070c060309020d02030109050c150c0715031b02150a14130c1706010503010e07050a181401030f0c050a05010f03092904030306050f 80
    0x10090018054003021000030180d4001c582d2f0ba650301800c440141c0e003c03100c450803000c0000e0191805124030016014152840d901c3c00f80c050780d6000b940312550007800700f403540d108201c0d4250746036440a044081e90181c0204204001c60402650318070244211a1044101c142039040760f030002c4080e03480300b1002c03000402c042428815036031001e0503040c8e440c0040582e00c80314000461ba02c5a051800e8040e0350b000b8140080c0310005600395240020500e0190b2403c040c1002c0503803800301c000c2680010b8900b6160841c020701d183c20000401c603a44448400b00c040c5c0701c0303100c111802184550403607000700c00810211040c05103d5860b1841031190640c031901c040020042d89050200528010004483c0000c2c100780c0c125600703c100750281c105076494900b0743c0080080280c1061404041c01041301c280d020b1501d400d000800301840ba045d9a001c05841d90050f0080100c0c0300e103805011007440e48800040e01051003115112201220181e00290819100203160300740b80c808001c2d040c0f0301030100078 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 338448102 1250 338446852 338446861
    0x221030a03050615070312050915060108040311030a1d09041e03020a080d0c02011d0d030b03100f09050d03090c0603020f13080c01021218100903060903051b0a020306 73
    0x1402000010800b81c0c1280c149a11183e5403100b13600141200d9119807680020034501d240342d10100c440051002e07925902840e2007142400c0c3c1d59544540c400c1c024030300490300c1ea031a460b08a07074401c40422981154840031a580c130300c0360340050b18641c104442e124400000c0e1405410003c0084042e0382c083c0044586400080d10a000c1c09500100340343020340119180c03042c4075034a9002039403090f091005090303504c081000b005582030185c02d10290000c0c0d0029000079180418680b210a41e5801409140e66000500d0103070314180304180e1844403051040003c0403443c1c40702c901514a407002101c00380108420001c000d80a44a0309503c0750b00490700010309814128190020340c001540098070341c000340204059000030400450107090f0072800303800b064800000180c50700d003082104494041003404004d2114000c2c00c1400c8101c5400c8034101d4006d005140c0076180340b2100e4101600d51820007401d0000c0c184c01c00011f095400028544422140e01c0306400c0c0c0c0c4804c140a402503041c0c0200c1c0204 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 338449352 1250 338448102 338448107
    0x3050d0f030b0f06160b0901090b010b03240102010b0a230303040308030f0a0207020306160f050424092105100b030307030f0306050a060207030b0115091a0d11070221030a 75
    0xb803d0030280091120400c40c41500c074400a00710450300841c03269158400d9804006843d052b96005001c004c00c50782c218142440100b086000610390400091a845000405c6038405d4200440b14440900030320021a140c80a0003464006014500e440384840b0034040a036060020032030341141c2d00801003600b10b0310b8540c11492501c0b0043e1007544c03000d03000e0010030b000d0b030383c00e02c516401114a05100241c00558070030140c100c0084d50503010600c042404100b003014103040403a0340d0a018101407804c10300c80c1501c2030310782d0404c5030070500000e02e6800c1001d91109001d48107101c564059000c0320320030058284a2000e940c186201c0c05d4040c0c00c20720000d070000c0d024070360300c04408040d03040201d040d40d201c0001c61200c6801e544100010f91205004005011040c00c40d6409095041030f100b40c111001c01c000b81400c0e495100791100c0c0700c4c1d0302c000d09890088400c02d40c0c1c076030b41e030091040c401d964178012404001e410070403050f40b181d810160044184072a49015000829036840a14245140e0031011f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 338450602 1250 338449352 338449357
    0x1b050307080705070b070c140105011a0d060801060803070c0b031e130b0720120f1b010203010312110c0f10030207021c0c0b030c0f0c010902040603050d0f030b0f06 72
    0xb2401803050a210b440000303080100c00a2248155030349072003a0000074200b0450490178400d2459840e4034040060107240b0f074001150b1004401d0b170b4016507840b08070000640040000f0740c04402254070b003810115001c20088010041e8034011800902c41540340c04407d141c601c026501305080c84a1041505045a00d140f180d80d8011f010800450480c581504d40d9148140c00701c80c0d2a000401c0940588644074000005c440880c214400070440c00c50604514001c030710800e00e9803504d801c4007251101c04000c64440c0001f601c0c00300e40017503440c0d50f980c0c9441085800d0003c5401c3c0825070518a005503503c0c00580c440b9507c0380246003016a4055000f4055070307040226001c0c0030541c0800004002da00c8020880200d1400410300700c10400da01c1c10080d10401c01e5412000000108005003da001c3d030720f1066402c040c081c00140303643c80080c42d029034010891064000c0d002401e0050010601401003840e010035040744c2c407000f0918903a940218122020140e800f0b500509444003e603050410311302 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 338451852 1250 338450602 338450611
    0x30201080f100909080c010f0c140f07030809030c12131502070308160f0804030b010b040e061c121205161e020c120c01031103060112110d020a121b05030708 69
    0x485e180741200086100d420f665600280a0140d615111407800450780000310a6800c10340414542c02e0140d882d0400409100b1020050104240070001c140c0648050080320003600b4a0801c440d112070410842002c1074000f001e550b030002c05110b1001800c1d9461070071988024000364041d0407940e0170350b90b41d46201d0b000036080010300d21030700c124800007912110881c2c0350342e03001d0240c20341c072289103140103850030714160840d21500c40e05100c20040382c8031042285401c003034201d0b45200f0540e000391440800200b016400b4083c0b000c481480c0141940050104014000110083c80aa81d4800c20580441388000c40100000c0d004014800d01341042c42d403100046060344142c61012040e0000541a5048081c0b4107146030050250400300350b0b010302c01c2e004440e10884101e401d501d450400642700d6144610a11032294a40c0b50b207841c035800e03035400c40320803125481301191a142039481c010300c171410001c035400c0264500740c1610a4002c0510040385400d00070356940f49590b4604030200c444640191 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 338453102 1250 338451852 338451863
    0x306070804031119021203160303050c0906180a050102280c09020f0a020709050103030804020f0301060510021e0a170a020102040b16060c031e021605030c010501030201080f100909 79
    0x1441d840f1040302480030881690709903400000251080c01005003d0200c692045c80b954020031003c4442d000741c10040c004281c040c20006440d40c1c1d220b401100e06e22441d42c01680c08800025800c110b4101c0c0e50818101c06019031b1032a003000d454400581ea96040c0a41d00c02c4807400382d6135207401c88909000c00070481c500c11041182c0030307030381c5000c820242d812031189400c60140224501c0d4a0a604200a900410514000380425491918040c20541015001038010103a0344c1110102d61001d40080c0010480034000051034144200c0003912443c880e103822010380c0d4072541c0c15010450000b6400380e880e4021380000021004505101100c1d0b01c01d02c200e1040d55024480091030f080080081c1401d4446041100c52a81940c58801e0450f01040300d0502418582203d401c0c116201a03a815440010910010ba5512524041609409000f80e005041d440002804000400107401c403030b041724402c4c1c840042c41c0c0c030340c014811400c0780d0440e103d4101400d40b00d010001c51407a50001c290503401340 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 338454352 1250 338453102 338453117
    0xa020706020910021f0b010503040326070e030f0a1a0402030f150a0b1e0402030601121e270f02010e092502120906030a1508010614010806030607080403 67
    0x41e003c1a902e421a00034900540c0107a409042d5943e03005501034411294858200021032042c1c0c0080c0050201410180c2044816500940050340703d100000b8081411056260146013032040180ba048800c00c1c0c180c042d01503450140044a80021030a41d034560001c2c05011845148802035144400103100740c0c2d00d441022022005400300b0711140c03c00c102201c40d900c4080c60151204001e4402e6215041d000c0d43c0f101c1d121000c20f04001d0820589110201d0700540d0305d031200b000480c0c0114804121000c031070302d0541c40041c4040f01000441056500060500c25000450402c0081d10901c2203214030001504d420480051680083c0000107481410600b403840b0f28807000c104441c3c400c440f560b6401194602d80050b0062480c2c0351464205644020a03603c0512100302d8018014141140d0003100084003090100c1d500d40c0021601c00c03020301003900c0c0035a440440901074441403042032592810150444400d52007a40784c00c2c403031800a03000b0306040d180e050f0200d505040040041c0c0810005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 338455602 1250 338454352 338454367
    0x20c0703030e0f030a1704051f030c080906040213110f0c0d0f0c0807031205070e0406050f030703170706021917040c1502160f080601090917070c0f03060501170c06030a02070602 78
    0x2014281c0b0302c0c4401d680727020040e858081e0805002c4824a03000700041c450700400304200c03404005200390348150b065821680701c00f005c00314a409000b006200154010011842d030303960750000b00260600340c3c17500003195420807500d03400707a9800624540c0180040d0b0b4203103140011550800080190502c00d21303140c44a41c00b14140c420440d07005a50150005d010400e84c0316183c03500340120f101800c821520358a2818108000954810261000410b0140d803000c0030107900c400c01e8160f54001c0d410550540da110584840c018038031080b01c21900120f280c11000020348660320901303d104590150340d40381d03003d040c0040411240f041c00203520452080c0740c08181c0c0c602c01c12501034010000400c89000340c600f4103030218100201600800403041ca085800c0d0040740b10b1a400b4090410442080ca9441c006800c1c080040c54840c1c100307140b040c441c0741c000420094140d00c814100c4511100200700000d000214549499800f1226540440c003400072401d101419801803030418458000189820b29 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 338456852 1250 338455602 338455609
    0x70f0c05100809160506160c0b0f19080601021506030102070f0b060103060509101a120f1005010c0507032004090501050405010c17130213020c0703030e0f030a170405 73
    0x414501d0300e000103041009021500e041000056001480c490094210604150100d02140611038007800c001116440600501c00c0c1884020013910b8480100c2d41d40c5c900d585a4000c0d26400070104405d50380b110500d24422502c910001c03401403005a010f01808100c11608100038400a044207515560030050000005c101b00c12280c000351007448402101c4ca170120000d0101c5a060344842d002d00032910800103a8004c0c981460182d61103003110301241228010307403407614001c2d10410340203d85c4007400d008240f081c0300200351143e400b6895005801c0c0e25540119000d85156500414a030f00c00c00040c40010b15840040050508141250302d4101440d80014195481844251901e0359a0014441800b07428090a801c1c000541040c03064282c403c0c903200700504008003000b0f20000503120798001c640d5501c0c00d10500714000c68007551100b4128203c17030b44444480c44118041101280329074400d0030300d2000c7e06454400107001d002481c3e19901c62005c1c069842a10080382c0ca010000030a0341d55 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 338458102 1250 338456852 338456869
    0x31e0507030606031a15030901200c010c0504231224100b04150507020a060809061f120203030c01050c120f01050d02010c0201020c10020d1e05070f0c05 67
    0x300c5580101d42d10b450003401a0031690920803035215900c0032141d43d1801d032505940420340000d180c840661301d940300d005140c014144143c3c1c10144185410072141000c0f0b02c01c002d841515550310007008000c02501c000e644501c030398031803c415943e91181002c103100980042400c1000003602e4030489000d8009824240308040c0740c02101c0524802d4003903078600740000901e50004150301800007080c145814030341103000e00c0c801c101b0320a910090041006100e04292528a0b6000e004140031588a9102401142c41107400741018824440000c0c8a0245000035041c1c15560080403540c01d402c02c500700c9012003c007081680c03d80320030400d5004002e002d2060700d1055644000c00794440351280c9a07000c0c20b540240c54000200d1460740144040e54550245030445607090914614000c510303c0145c2c00c00c20400035503640000140b8410015a40103d078030035120080b60742d104460004440451800344440207403000180c1d05000d403100041e449040007000f44c2c010505002c811395504009100d02 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 338459352 1250 338458102 338458111
    0x207020f09090d201c090b040f06030b09070504090b0f0303040905070f050702100e040e0d0905100216031e0605070e010908012009130f020304050607020f0a03031e05 73
    0x307500038400da100103580810040d40b402e03040e00701c1c4800000c060320220398441203144ea4407201c0070050707510a981401041b1010090200b4201c458541d545e40004611881070751154602007400c082240340755103403044900344036441c00c5d21031b01d0400d03040c8144640100601010749410a4004070304510b140d40c1040070340700524180c5000301d8140b4020310000c20349025810380c0028040d0178000c410040e5500c42e84031024000d03c1c58007020491850b030000d4090081c0528070380c254000c0d40c40f20401154007001d035500f41d0340c2c2500e44122108071008105d82e10741d8203030070000c51214203034820b1000074030050300c4594440400c4000200702444e61a554221281a504200070664000680c180da58001074402c00504c800c1c802007000380c010400428000b145401100c2c1c200000080c404250780d118130a05694201340701c010020200c282007298020343c425502031720701d4460180044c10041c400109103030560f151801525540005507000d070302a21100703061010f2a100e40e901041442014445c19226 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 338460602 1250 338459352 338459371
    0x14041103010b03121801020609031207120f0605100c05070e0a090b1510080108030d0f02040801140f0a0c02100905072705070509010c17191d0f0d060207020f09 70
    0x31100170140c4d10140100b105686030664000804002c0251404030560301c0307094001c0c103e01d035995594242104c400006003206a0f0a6141c149102c0d440907113a482501a03501c260b8003041021008882a581e2900c1c65000906c07a600c1420148040000b1b092016041031107aa0041113511701503a42290301041290355aa41e408a40c2201d1101e1405020f1030b191160346040585040d4100041c032a280d101d2142804e0300903031100d1015004224ad98119001449654001c01003450720310b02c400d42508003650303015003c086000100305548902e00c9010001c407201d0b001402881101c0c0c4800b00902605401030320540a1107a0020305c40c2e1010f9111041c1502480d02d45a00d2481c0014520884401404507000c00c0f0b01809880e0069800451241c2c0c501e40000f40004415444120f4010368810400c8104010704013901c15441680c0020080414462444a010a01030307260184200c50440084040c4c1c003101c060740110110ba45607000f05201360000e862451b0010350800821001001620390466 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 338461852 1250 338460602 338460607
    0x30309010513081b07090f0c03050903040605030415060909080406021b10050906040f1e0e07120e0a060501270b060a051b0619060914041103010b0312 66
    0x891420a100c1d00354020103584100b4203014403521098402e01442000f400e902c0c6409500c1014440104600d0340102440401030010504294600c005428a6980c0c0b80200303041001113940d07000040240c9042c0e03200c507034885065544a03160f604240003d206042c0415a5501002c07603031940c540550004280a40860380d034440c0341140c000d140400f442c3c50b114035038024500361016556601c1110107448054a40b80d91107803e41400181940309a0b8020250440081c200048400751100da140003003030882280a030b81e1350784022400801d40100c6641d00000c01120308490704220700e038460740c0301d94660011a0042c0040e9030320981100c41c280c118480010072405100c4c07032400410b05000341000c841d203007446507450801c00308080c0d00984060005000700421481d41c1d6842d071384c0110007400d080104a643c00c0c10031360115005151041c0d81880c81030304040e0045a0003070503008100c0081100003000c40c8036905c0d502c401400e2124910b5259140d5211070400b4403980c1c7c00c210420000c0306020310241e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 338463102 1250 338461852 338461861
    0x1c03081b2709091c0509060d0c09050a080d030f11030a0504020f061606180c03080703300e12130503010501121e03030b060c0604050f1f09020d0c03050303 68
    0x1041c414140c00380c00e200b001d1000401030034103c0401c004a01c910889503600403507064100960300c0f805580c10b419006a00071465020000c011b4000c11070401413600c82108030750301c03182072107110201805028516804120400111407207a404400c03140c01210300081e14000d1901d01181540c03069451504481c0c03118140815490209010040f414003107901510340801d103410fa000390706c03d99102030b03c640c1d900c0c500c1c40c0c05102a1000c2c0c654199006a001000986038074000c03115070000078041d00040c0d142030a1649901c62110f0500c05080c400f009075540744041145a0003a2585a6504901e801819900480d5140c0c1c0c1010b0a041d488031100e03014050300f480c007854212a0142d01c01640040e11030645c4011a0300256052410584510070894150003410158003516203800e800390000e900081c940107546001c259980600d12400a503091101c406044580c2c644420a840d0100303002d4a079407040300302c0142d10440d550b030f00c05484200c951815844d5a0780c904455031081c1c920390800400c10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 338464352 1250 338463102 338463157
    0x2071212020d051801080421050c0d0903030c0213060b0a0210150302150313020d0b151005030703021c2d06060c02060d1b02030a0306051c03081b 64
    0x42c60340e12243d140403410010019507044040d07000704070490500014801040c00d000e240640ca28407100c242000d134904810420008105034404121007440b40070380c0318070701e80d524820303402101200c0d050390347c40201410719001c01031064414151441101d82c0d034a8001007a4241d240500803003241c0c0c2c0c0207070a213102004003643c10b642c4881c04c11511010f40c03580500040e82d030480c4103200c1711203c262840d02c0366544120502c1003210100060b41c0b00c400c003410b4008218000c40c4049c03040400103114080b203913841d4148003081c02c1b0300300b0b0040490002c0c4000b40d09140710754040d2034005489403a001003000180e005000b1a0351424021a040c8040140a21004014411003d181803041400c00c01c540c500b0300000c00d1a002c0e045c000b031150030005038844804286400c402036a880710421104112014640130756258004040800441d041c503000007840d103010003481c102d021401001d402c003000140d40495008034010000784950500003108104082620040c040155000c84078150480441401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 338465602 1250 338464352 338464363
    0x603060c14030c180a0f0b0403021c11010516020901030c0e0c0f0d0f020706021c0b01031109060c0106081515120c010f02030f0d06050a1a03160207121202 68
    0x6500303480041040c01020000c0808591300603034141020031044d1000c000288035030b9590f038001ca501c07400c4404040740e038050040082088074400c541c40108204100c000031103000041001522003aa4038065420fa175019000600100c101000c18904603a10390740003400d0030600f03030000c0d03c5d01c8042007814098418403981d6160840f0b41d22800707908200c40364400030b24078482c0d0340116040e9038072158508a420140c0d015076600960080701591074101c0a10a0b10403403040e840740208060500340b152009501900c507001c00c0c2080301200303500d0200702130240041607110340240f0517250342e43c0d080000c030144103014042c20303400010b0f80d035581c40c01c000e0b1291485a0085080c40e22580d00d401081182c000700103269070704c4031070a007016120407081d01c50981c118041c442500306801c2c8001030002c0544075541c0f04c2d00a50b201220710043c0641c40e10035860034095846500ca000440401c08286440e14000070510009a284101c50740540c8560085500031031031b1000b2528070104611140d4001d030103000c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 338466852 1250 338465602 338465627
    0x619030b0402040806010e0c040326120a0903022e05061c0302151006050403120e03071e0b07030503060d060207060906050103061407020718021b060f15180c07060603060c 75
    0x504900b27290031a140d081442c207800103d02003004000c40e0448a0b034481000750b88040d135251000c0003007850034010b100040c0101507412401070107403245040305c0012401070070340302c143002a03280c1010f11600c00e80d04000300b101a050355805410ba1406401008000444c5100a4400c7e07004c2c0c45110200aa4550f001501515950405d150310b40306020b040d6001e01a03800700d81d00f000500c0003000d40c0d044103485640446041e81e030140a0098040b5640720707842d50350001880c2081428400540e43c5112560034000c40100a0015408001258942c07034990760a0300928040c1d10018a07001003680d5a0301100c4030310a0031641c8030b44a100404c284035091099503184000301d5280d0a4901d0a068029200d420b2401020007603505680700c0c8018118590666203c28441121152408245030f02607070703581011214602e020b0540701c0007801000312070400500c1998007805000c10002c031014140500400181034890540e010f12002000ca00346000c5e00c030055010b0800090805403462000709840031054 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 338468102 1250 338466852 338466871
    0x60203040e01090b01020a020402090d0506040302070501020d030506100e01020708062508071e17010b070c05060a1e0e18040203060105120c101701030c05100e0619030b0402040806010e 81
    0x100229005e98000c00c8480e41c01da4100c2d00181d880b80424005408001000d40181c0b052040351704100070560000341030801d030b510903022107501101108040301901d204948c505d0b04101c1c03404031584028098040081c10902c1401034030130749503d07402024600041201e47c0b41c00c800400041c1000305a0004070f0303224504452070944076a140c50403014101200e070401c46000030210503020b040407846100004059294000c245440396941c0e901c40769a5000b001090300d00050042000403d4500442201d0440d411070300c0300d00060019411808005a06500c50300900c2522143c8000300e0391012042c0000d0312010802c030100341040d005140ca07000c016042a80110a2036a84400404002601983e505e2048404ca4081c0581d4801211900780300c030b00c1c07081100e01392000031007004401504c4105a52041d25a030150540c6040112103a001d921842c07030300b16004100052002c031080c140c0070340803040b605000c50030302d00745000300b0100c0c1e205900c00310003a0800c00050040241c0e801e04980c103d041700 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 338469352 1250 338468102 338468111
    0xa0506040e060904170c0c0f0405102d230a0f03060e0c0306040807110a03020901142103040509100e0c1c05010303030911010c030e060c010603020406060203040e0109 73
    0x1090541d400000d00750758840c0c1c090800040420810110925002d041d00d11403a4032280c00760300403581c40a40428a910844052521440c241054441d5030b10640e403030a000c010082c078041040d0101140803820b2041560429081034038209020920402420261030b980501c6914850251209105022040c03091003003940400c400858070140f041942e0b0401030000b41c03182107130762040c9400d032501004c681500aa204100901c044903000d400c0f01c0d8040c03a6403081c0c02c0220020040c41c6072141c00020740c400345400050001d0043c03000a6000c1230806004007000700e00d1058040406488120021a07540c0000343c1800241054520300b6000741d00d00d030b0543d82580c2404200c0c21040001031641e001008041845086245000c0c001151056244410411561241001009007102c2301003a00e141c62800240b5941c0d521900504400a030903507513141c0e4010800c010801280c1c130034000d80f00301d5902c0c0c1c0c0021015035640d04c42d25000713180c507400455441d4031f445480001c8a070140c5c40ba1098030300c1c1c0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 338470602 1250 338469352 338469359
    0x190c020c03071a040f09150f0b03310b0106030e06040c050603041502030a0c09060e0a06111e0d020d0c0b07030c1b0b0603010b0303091c0302011b030b0a050604 70
    0x1c0c2c00d4040c0d4125841403c4580da6404800c1d007203001d282e22075101c3d625401000603414000707500c406008804080b80700c4440b9152001003c0206170341c0f040f9002e4076020400920860328841c03480d1b1103032840c0c84000c50b1076200c0d004140f03034902c41d10005446000c131000040040c10340602c1180c100c03203e048050040c6160503200d0803003800b0944a0140a0000000020108000100c1c801e072900568102152039080c88646803004282d03040101c00441c5a890010074a54000c460741415480c004018044c80307414507808a9005d07144400c03009442c0f144000c0d81806441030b00310903c540506400500420b500d5880c000c0c0b524100300c408106010003100e80c90040b43d54072982c10341c008900e0038041600340881f00f00300c1d02031488000884c2001d000703030a010f00700011014605c1c05120124024041840640308154517440744910340d981c00700c404030b0300030f01c3c104441c0070111066011b130000040d0140625846030046914010f00b07400240d441c0028045890101c080300050034066a400d0b041ca401d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 338471852 1250 338470602 338470609
    0x60108060a120b04050102090303031003050606062d090d0308100608090303010e07090b0703020102031e06031b04231e010303080a0504330e01020313080d0f05190c020c 74
    0x44000c4081c000446040001381800000d404442e6130300000740440342da80c036041e614405220b81c14001200d4601540011030a030746002c2098a26044586840d290f40e111400413021328002e0554420440c410288030707281c00c03555407000d40760001c1d0003501c52403024600480728030703000300160300800c0a0104200a1260110b4008103490540705003100c0da42141d101c00314151000e1a0700c0d480707080d000f803000442800b0594107401550241d0203105c100340e680d034600074003101c00c003000f03e4585030540e12100ba00b400c604541800d080382d002018000243c4150f050a411001c040510f5002c0040103a4909200248505060181b04001c078002240c03101c1d411503600030310140018160200341c0792900040340c1441400e401d121180c42c0c4c002000b0309044c802004994110b203003e074020341030901d00515112121418000c803886002c420311411442800350b5200001340d086681c04100017507450402c40c1c0c16140034411140903410300303035400c1b4129111118000988103010701c0881150000200740038242c9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 338473102 1250 338471852 338471879
    0x9031407060c12020c130c08071110020d1e090209091207140309030d02010509010b0d0f030305130b04030e0f030a03020705060f0d020d090507060c121b080c06060108060a 75
    0x540c040b003400200d41e000b0004030f1405c4030300000705d41e1021034050140d0100d24241d200001511050b242c00c2002e030340d41e003001d4420302100380c2d02c520690402030740407413892141d070700400103c01c440074001103000744003800d004a00c40c0d00f0b100038505030b0381c5c15080c0c042d8a0321090459000510b040140210740240003c40c8941c05040d03001020f1402c03180c2c014001a4091061b80c1c00c1100240c2241d46c01c25198500038003030300341035555900700e5190414664650a2054043d2041d541100001c4601e1045690880003040000c01424400d600c904074003002072001d02030117014502035640c02141550f408100054920b6420030184a0340c00b0360f034049c000076008206941103d0040340c1e90340e01d50744900803a07030301c510541e16007101c0c403440040d14110410303155115101c200d0064041b18030f000c0d2070714000d59801c4400d030b10192654400121031043c06118a003240003910282c3d40045a0f81003d90300c2c1095a085840034400075000801001200e5a100140355404001143c00e400001d103001c3c109810b00d0b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 338474352 1250 338473102 338473127
    0x4030302010e1902190801090b04020405010803070b2a0a05120106051801081504020c061503010e1b04091e0201080609070f0509030a051510083d0204060903140706 72
    0x1416074010500d802210007217014020b2008070000d015080b10780c58041c000050450701244201e02e407030700110b80f009000007911039555010060080035211041000001c1c4034071946241e14600d54400b450111900c080541a02c0885031501e81d00c13110703039802c2c071070b10220140c0210080240a028440614804084c143d080c00001e003003a008030b440710418041d5020301c1001030781e0018000104409088400030303030f032803298001d40c030382d2445c900d0751b04109407d0b83c011000c2038000340c1c010300b070012504c138034a4580b00000400800020b0a001a565001202c10a030504a08001d03050404642956000680f141e401103084500044e1441c0118020344842402c042e00d000f000000306d407035151900c0170040c11021f0340c0c200d000c550401a45540010908004440ca4181141d118400140b00c500001d807545150303503040c52180d44048500b44440c0040b903000e9000c40b03d45a05a002e56056880784002c1020b440075940f41180103085040014004640584811007540b15031000c0000b1580032101c0c41c0c7c003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 338475602 1250 338474352 338474359
    0x3031b0305090609040f020f040303111204170705031204140d0c060c0204020f03090f0d0201060f050909240a0605010903020913020d0501050114040c02010b010f08100f0b04030302010e1902 83
    0x40c0c0c00c1c6013021400030101d1b010503600117440000c5460030550800c0207041264481d5542503850a90300c050360380c035042c080c0ca414141500078042482000342210030711140d55402406c0303a5246035980f000034500b00d00506611900000054240b04224800001580d080700c251600d24000c07845980c2c9c2429240144103034420095004095421980c2d079804031031000c420001c2907078507410080c9280d601c460b0010600f29481c480c0001d0303242100d00601810f421030304001554680c1234076240a010035004018a001c1e254042d040345203040c1081000031040c2d141103403042600604d00210503000b2038000740c2240c0d0602000000c10801a540c0c2400190b00c55641007a0310303414044c070310100320788804e04800102a94204000815840355180301c040115070200d03024404c00351102c20690032584010075807400591550080c02c0040e00802d103047d040340c120b403540c60065980305d890480240c03a0b500b160b103070314500060810600d40d09006180c200034420703014100400d84415140e49454200400a01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 338476852 1250 338475602 338475607
    0x2060106120e0319020d0815090c0f030a06080606010903111201110c0309010905040606050a0c02010e0a082b020a17070c030b09010509030306030d180b040b0403031b03050906 77
    0xe40750240d003140000b0301e5120b040700d459a112030b490700c414402043d080401449220b425400143c030075581d943c0903001500000180800700c0c401d003c3c0349000208400001e8508114a4402030300460041d03200382c1422400240b203d080c01c2e2214240f182c080c00140c10032990500500115840c0140c0000328041160411300113400120b200d809483c0c015201c2d0490b070b6012684000d8042d003c4002d01e200f5100b44d80d50030125803640104130807980d050040400140e41840203800e19400713400c58140840c014101541d0302603403000003a0054070306410003210b0382c0103042030940c81340b61014010800c80d040040001c1480c0380540c001d41d01d00b03100d2005005482c10801c1e921101c040c5908951203150010f030745019184d144c2c00c0100410006403146840366192030300140c080227011054034002c000060203440030040903031088800d4108036500900d0031754840e00c0000e021010400400040c011000416291440d6041c0a08052815030400740d118001c1ca00c030100082e03000c812a07004042c00c855140c2c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 338478102 1250 338476852 338476877
    0x1030e031210090501060809240a020d09020901090c0e030703110d06020c0607081e0705160c0e0a050402030f01230c0d0609020903010e010b06030a09052503021203090102060106 78
    0x240e01c001c583c40805407a26082c0081880d9512800251207075425000b03c4107540032844000c0301c515070340000d1055030000382002c5070071442260020404441c2959001c181050f0345c2d000100515800e84c0003441a070f0303450040040440d0841d83c03407224170800320054040c0d24a15181c0040ca102c0d8501030380e1041c1c900280341001c100e1280d040c1c907459040707070003240c40b80e00d07000102500c24402a00c1d683c02510141c01030311544000d06101c00e1007842036917141e5080a460f10550035449410b54001c40d0103011480020a40084008540c0e101d9045000c000c245801e05005040c14031030141800746090341040440340407081800440e6070300e20000341392003081e90760f08030384010140225841c05824504001000506a0168000c1d0547c0c60044008000310020145c406081702e03111007025030400402c3c00000d5004007030764019000c941c0150240c489070000d1126400340520a510961004181c0590600c250309282c24500f403405407110040d46052070722070010f540c409051003583c040050100d20039 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 338479352 1250 338478102 338478121
    0xc030b090622020a0206060924040c120908041d0f0c0d0f0e060907060509030712030e0a030803100b03010605070b04170a031d0606010903080708090603041b0501030e0312 75
    0x182d0803040602c004540701c1c440780c0002503c030002070382c5884c4550300c1013012480c40c4c81140b03805401d28440824240c0020f02d16424032000e09005d800300340c00e02001c096039032150501030080614542c455002d65640e282040661080d000340f51036408034940c40001000040300180f8412504005040f06054030b1369200c202c400b01400380b60100554450608006900e110b5000901e18000c6542000343c554903511404100c426002d1b03001c2455155020400030012059003402e6890b0040c002d20304802e10804100219003520072980c000c444e5800004104034034500c10b90101c0c4080e0240000d83da166524041d401019400750780742c058882e15040000c1010400c402c0005d60b030480c24600255150250108090018121600c2c450000d40c6004580f0201c900c001c80c1280c813400c03058403207081c2e881c2144c9681d6042d07040382c0c40880b01d44004010b000b550307907551005544558400c4100d096104c200c203000c0741d14081143d21140c1450b0501080d2800380e0408000e441d901e410900d070390200355640d02c800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 338480602 1250 338479352 338479399
    0x608010b0901090525030e010b010e031f0212010605130905070c14010e0706020a050705090106090b0c0f030304060c030b0a05150a12020f030108070e0f1501111f0c030b0906 76
    0xa070780d601744030044001225805030801541da02500000300140b40060005607181ca18035031000741e058100c0100074001d08400d501180301c917541010010f0500d80d00c0c2c1d07484511804280c200c3c201142011999000008060f001480646000c074418042c0d41001000580b141c0a81d860040c43e40c1c1c0d05880c1e180c1e56440940c4890080511034040340e0040d0307034901010303441e820999410f8031076000f4200c0100301414041c01c2c3c241210601d81d038045c14213242103d01002d43e0442e0024250901a0001869000004001035400380d40030710000503c80c1c2c031160018046494070792500340a406840e104001d6a83c034032006071203860307000840c03641d9043d4014044440341041400a16201d00c081142188c66008074043c5060701c15660031100d0f0b07103440307140303800b1903043c2155015909103e9030009000c40f2000c9601d03140c0502d040c100340d681d4aa80c01103081c1800007010010714202d840c40303420343d0542894028200144000e00341000a128044045128810b0041c4258000d104180320340007118655401e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 338481852 1250 338480602 338480641
    0x60f060904050411151c09050312010308030a0c210b0613120b13051b0d1509120c03020304030b06010507021c0c0b161403041206060503010608010b09010905 69
    0x1000980f426203058030f40c0c030104404503802500500d90000075480010103e400c0000200c40300b4001c000035040880c00b03005101c1046555000900401c2c0c00080c0c1907100c1400f07548074840858483c580708500b0f50491384424040c42c1005500b90b844645003c0310a4003c00c200300d03100010807500a0100400c20b01e00c94503000f00c1140c81c0f51440040d11031a841c9a0000350741c4191512821031301c4a0b000d80082c080314a50140030380e0842c414100042c2c8241c8080070750340c80d010707001070302140c40e81c0c0380c040280380645204212151281c02c81002c100070904441c800d8500c5040c003542140b020345000f50b403401540001040c51446c0c0010510603805101902c080503070060081003a65200d0071010a2200b440104907028242d8040200301d40c0081c0f010346000b03032440141d80c0d2441c62140c43c0d8591400900796406c056010400010550b00103015154000a010300300100d803c86c6014207041c21140c0f25030091a41ea45000014001a03452203a4281142c0708070201103660707210300342e50040725440d413003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 338483102 1250 338481852 338481859
    0x171509071e1e08100b030910060320042d110301060f0906080f0c0a09090c020106140a06090612111b1905030334021606050c06060f0609 60
    0x80d0360301121075000c401d60040701d402480c2c40c0c0142141e054103581003881626031441c440c0c0960814890100c1010156900049003006c41c0c2c80348940888141c112801c6d41c00c1a00c00180c512044400d0207000c800c18004100241c400b00f0421a000c94103002000488070258000340803440b105500c48000e8203c0000e1070301055460b541c95030b42d0750380038000d441ca40c28554049009001d0008040e4090403186110f90703134000400c7c1d06547c8840200302103078421041c64050140c0e0741000701d120f9800d03120301111441c098000055480c244800c100c82c00c02c0130b61300c4500c603040c1d10000303004403036104dc11a012214141000301e9541190303c01e4901400c4c000296604900021511810f0820280340080c4100c50a46c00d031040c0c1c0c008a10607581a440345c0c6005003040d4400c00120f820140070b0003098010306410880d61800340500e17003241c0c1c04210070350318000040e40044480301181c0cae44035031000001c0400e0300b0a1481c11204c440d9440c1c461000070f08113031180b403400710241ca080e107034907040740c030501c9005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 338484352 1250 338483102 338483147
    0x302070306060f38070807240b090402060909130b190e01020901090b0c0c0a030b0f0906040c0311060705150a0608071a030601030908071217150907 65
    0x10341d902e0810403968400e0a58000001c00380d10030344c4245010030044840f400d6216440240b044283c0c8019500402e801c554000d002c012201c042001342e811803d2018003040312181d10600103a510003505d41002216110300c201209000041c0d4903042140d0b403041c4181c42100d0030350f448a6035604d0040350b0b600082d151406600400c040b6502014243e50007800443c0d0801800088804480c00c0740261440d80b0f0120701403120500200c0c1c02c0b00003800c04400b0420880d0b00c0b0007842c40200b074964130b05030300442c0c85400450034050401d8035540035a80c0f05030030304014001880c203602c603800404014800a0a41c0380000f10350942c544071311007100d84158000048a00d030003054100c0c45400314040700c140c48000d2401c040828066000300b00c00c0100d0302c6070510100741c6488003a500c50242c1c809441c187c145540c0d840b480d8001000480502078140c0964101d0046400038200178004403130701d081e40306c242c20b09a070401c1103100130714600113105001640d550b45680e55403c004d03a160241c100e800c0e0985c1c1d482e03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 338485602 1250 338484352 338484359
    0x16020f030f0c01020114062d1509030705010203071505041121010c020d02030d050a0b12071404020415030c02010e16080c0a03110d05010b06031014120d0c030207030606 74
    0xc2c000030b411100303038002c201c62561003095494102066820a0380184004800c601d92032041ca05900415507586c09a0078203050240061240554900e03004240000421514a54a001d2214400500f003c1c0081c0d850b00c842c1340d4a8580030f04080486001c00c0c3d0762080418140249031a0071005884007816901c0da456a0842e24150200a00c00240c01982004991000c0901c041006150740c0401d8008608045007a8001e8014100c01000140e14a564075200032956403940380c03110b400c00460010700459400c06c100e0b2086404044c3c1040d0181d40104030030030600e800b01c80d0580d0041020315001031902041e000c00c90143c070110303814a0640c81104501c01e5840040b40740c0030300700e800305001c4403111800102488065001031001600d0300503407820200c49030038204200d0705180d11490002550350b80600004c2c0f19a0401e840d4145100c104060510070018400c480b42050b20080301d000c0400241c1c4811140e44100c000320744410854103c1415003018000c02c440c034055540040280304241e00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 338486852 1250 338485602 338485633
    0x42306040e010e07030c021e1513030f02030c030403030c020d14010c09050f030604020f03030c03030405060745120f23210403080d150f050616020f03 66
    0x1028043c20141c0384080011a9282e402172169104244a0781c0160403070420000ca482303180031008034500e95034003030502c84140340101140010f00c60400420140107040c42400d000742038640000c1c104095600420402d5421500001503508491303240c81c00b000c2742c0450384003103864005010401800341114441c4001802419000303140440442e9441c014aa50b5800400010405400d030503500f5400035008a000350800c8082c00c00f0320800a0201c916140080490341d2441c2d01c111415100c40d0450800c1c030440c03d078800c601c0000c4031002c0342d4001c0120a48400c0301502c040d2250300d00229046045000401012441440020441d02c00c09000140390340c20726024406210030129204803160f4100c02801d00c3c1c99100d01c11500003a0000d00021990000440b08901c1000c0c903417801c1ca03030900c80000065a004000c08820014440108048003640c031500340307400541d0000440380354000b40510180c0c40750303800d50304407400e000c0c0e00300700d50102c3c0c0c00401c02d100b03183c0300180c2c0c26000340794107416440c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 338488102 1250 338486852 338486879
    0x8210903010f140907030c03020f06221a210603120c07030c0b030c040b030417030103060b0f0619050d06080a0c06090f180b1f091d0c04230604 63
    0x7030401101200559804c080309840341403074007004008841c0324805001605100030000720203080504164038040c82d05980920804808041f000da82881d00003c0c0700d51032180e903018070841461500141416020028007203a95803c190009852404100040c0250303010051000c0307242c038008002d0f64850a4000d019200c40e0700f07002c15181100700e08000101d108000044900c151010301e9010b041c5402c000d0480348551025000356210400c2e4010312083c400040b0066000314420200041c0d191084020322240c0307110352049510904c400c0c013600c1d65560340c9041c1c242c141c400034684030341e48022050646000b0300c4240c201032050321421001804116050001b40d0070340b0016115804900c0d500c0d555005802241e0003869100240c1d100303100d800c94102d8011101c0b8040007010395800b005c14201c070040707040402815000285075006e007048030013101c1c04506010721300c104148001d8070300720280d195580f01d14420803116016800c402c0d03c609410021103290b11100a104554560751401900c0c26003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 338489208 1106 338488102 338488121
    0xd031115160f0e01020c0d1a09010507110a051908160506060f0f10080403020a0c0915080d0e0402090301060306050c0a030605010908210903010f 64
    0x50009111280c07150340407004203429074150000007809808030304454028090000140b45240e41d012885210003001a40d84044610b81490244448506107034502c0f075041010f014040355403419007009005004a075140301c520704400d80e00607282c29016900070101c1d03000c0c0c001907000042030171000c0100c42c040c030351440c00d00b000300002c0340b807100319520226410740110003017100230321300041591170240064030155940303c0d1800101d9042c4020611b0300051120080c0001c0400d071080260024059000c02a000a6a950b42816020300385d503480b203100703105010340e000c01e014100040741004010b850b99200203541209050000075400560f810b5019500c428020022030894000e00f4040c00030080070943e200c4040800908484440e00801c1c100000508200030b5a040004e000410945168100c9222400c41d07000c00250711a079410b0a400d5424001001040d02c5035520441d001c = true := by decide +kernel

theorem cover : BRFrame.Cov 338309352 338489208 := by
  have h0 := BRFrame.cov_init 338309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 338309352 ≤ n) (h2 : n < 338489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
