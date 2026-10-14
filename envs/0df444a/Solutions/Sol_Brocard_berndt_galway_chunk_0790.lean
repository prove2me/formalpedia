-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0790
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:48:44.828123+00:00
-- url     : https://prove2.me/submissions/9a74424c-d2e4-48e9-8dbb-921b547806b6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 141906474 ≤ n < 142086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 141907724 1250 141906474 141906487
    0xc0f06070f110a0e01051c050a1a0a05060f280504020304080409050708130b130605070f030b0d0209040f02040e030c0d03110315010f0908030c0a1a0c07030503040206040306020f 78
    0x3d01d154004043d10820162442540c10440800c9800340c0d101c03000d1240c00c4c03681c2600c0003004010050706c0c5140e076010803442280c191141242c4181403081e6000a2203a00784000100541003007480d900390043c0c020803055280030010240d2040c03131203000071042034408480020455440d40d00085014a1080050701e0350307039140c22400130860b80050854000c01c29880309000c03805d002c8682881c0b48941040070851182c48034560b1841561f01c1c4280140014188400c029080e0307004054131202c5541c0707440905c10000710b201003212400d94507a00950120407417011034041943c4110790400e4078405070000800d2505509180e295130007214500902d6404100604005d503494040c00310805030100000e811410041c0c490505c03250500007440c10000410840040284034140c00c030000c01d000c90a682e5604c40c15237000d500e42c00944403d540d20401140c0b800c90b102242c11000f840751b40007080d11030500c2080d5600726035035403002c2d000b07903400b4070280004404103809100402480c1103007031000c0d40c5e544 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 141908974 1250 141907724 141907729
    0x17040c1e090c0f091e0e0403050304060501150903110d08040806091203010f15020c0604080a1b030c050907020f01050f0a15050901090e070e040309180605030c0f06070f11 75
    0x24030038820700d0304000070f9190758806150090b076140d054424103e084034444610003100603420b03605e0b50000390341c3d041841c207000501d50458000c500640c09010248501e03a01c0b580350710750024100d6070b0000002c070340820800c081900d500c0808042c01e8010a541608102a16203ca450b04550440c000c1c5410500a2000b4404c0c204a240e80c43d48440071a030741590f241089440a0115a06c00e0001c0d00040744040e2050078030901140050341c10003007500d606c0d1503d4034849903655400500c1150600800e8112812402000820ba402c899000314040340d814185024004e03491006421607056110303042030030314805401e026036442380000848059039840c041c01c414060703455801e1490000c1c64510424012a101c0092517411344250b82d40100d00e01a40f5064217142210950090712524120000c3c4010503034404244411140040740c08003104421580800444d0150b2081c2d90349540054801c641d28188441460b0750f02d807000702030504001e041c0c0c41d6210920751100c0c0c1218460a1800d5082c501d2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 141910224 1250 141908974 141908981
    0x17030a080108010b210309090c03071b152301060f030b010302120426070c031406151c0506091e03130e0a0603021806010206150117040c1e09 62
    0x502c1250000d00c02e2410b09404103410025083c65a4814803403c001c060541004100316041c002d0702802500c0a03260658000300b043d08103072401c00c001000550540c5202000c070440b03500c0260405000c03e00c0f44480c10384800107240c00781040700742641040702d41030b8150451290a0003402251145103400000d20002412500b960201c24141441070298070039104181c110b0b143d006502806000140c16100c209440140c1c00a000443c00040003030440104241d1803010000c40344284c44403840c0110884216480340d004880e1a10094803001444480e4540b901c000d00c00c0c1c0c1c00880c0030103941d01d410f03100c4c0303418000308913030b422215030081d04822900341c81d21081c00d040130036103c089c504100c0402004840d022282c4281d210171041400824000c240c0b5034042c1004550050442c1048150310401c0542071504403003130360150083e500042c0c401d40200010481e4100c05039150748203400c0c202c0010448440240007610881c08000010071510181114804240b06100c00c0075905464a03107504240c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 141911474 1250 141910224 141910229
    0x60501031107030807030c2a02100305010b030f040305070b090f070e09100902040e030301031a0a0507050a0c0c170307020a150e060d02070602040306091b030302030a050a030617030a0801 82
    0x7402010465040840d40c4031580a03000000d501d408107180c8416981158500243c1c581c1901c4000c20185400f24036820f01c9490041d140700744c4038044603000c1c1c601c2c1070f0b04603203003440303544800c00c0f0400c00110154558858603a00070301c242805400c104da40d440b80c5074000c100f2030b0300d039200d0780c4854001d03c1d000030200418001001544012000f03841d0001c440d0f03803078074a454010307907250f91600201d2086540c0c41e0004074a035014141100d84079a92800e05440b13400d1101c019001850000c030100324a204d480c080d051040d416070315118948549000d044a1b442c80021003550010303803a035030115180104a441d990313078000160003141c8802041c0100001a00c00303920014103d0310200d4113207459900800d0040d040902101c10507100c0403004508006403255800040141d0300c0040e020080007030940c440390096008600c80c0341d41410794004045a5642d600010300564414000300722a1031280c002802194281e240114070b09640d1000c0001803000c03c04601c0a5410203d283d18408d0340c48002c1380e00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 141912724 1250 141911474 141911501
    0xd0504112e020a0b0f01060816020712140604030f17060904020603040314040905010f0918020f04110d240b0403020105070309170a03020c03070e0a0506030a080c0106050103 76
    0x581400c0208000d0351910710070311110900301c01d5903a40850342c0c003e10101d03404540108019929140092100003400400d00418004c1040000030502c0010014181c01c460103c03030300100459401c000a00b6800308a05e00301f200c039040355914000c4016070501800d409a44252528004280004400f52a0400c0d8021510079081103074200035150380c41c0d011203604190182d40480c2d0300d840310b081c115659600301880030710200001400049902260303006a0403640074516101c80540c0fa04901c8099441e04580ca0340c81e915130113001009441c108690889461008100051000f0030058018150704480500b0046964030741141c0e01d000e01242e0b110000721512000c41c4170550621040c541240a0303804040d04014012590a007054007401038030024101d40b005207144008030700f00140c0c0c0c9441e9440d080300180141000700d40c1c2800c001586405698000d14a0040340d23545255280081c40000e1941e64144140711544001c41d44e94001001c40b440501e002250840c20000054151403d40c0071505 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 141913974 1250 141912724 141912739
    0xc1e0c060f2324030303010b030901090203060403020a0b010e011410110123010e0402010c03050703051201170106060e032802060f0403050c0f0607030f0306051003060608100b0703180b0d050411 85
    0xf000d640e010080302c0c1982c03202c8038429160f40368404007070300408140070002d4061052000344420715030005135084220f4425000c858840e80c03145426402c0840178410180c00c2c805a40c1c1e07013105440c01410b1505035007014a07110042158248440d425541d61920f14054480030341c4502d030756203d91440c0344d13025001b000f1004145c2d00b8076031300007460070040700800340410a000c81c1520406108000720b0f003403c80d0500302810b0700d50316190400c103603210440c400d40480d840e01c1c400080c02c5004a030340e04240342000340508007002c40380414040320811800e072074180706584c0390740c0b82c01a03644030007030701021b10151b04654446040d40382c914030340008600094451410035003208000d035030790030464680650614004401c245060019009000d0039000320b50310085103c3c41e8005941e00d64081001c60307503140d6500156071901c024102040c14580103c4400c0030b000c02002000c80c0c0103960728541441d1100c03030701030741550f1072003e8a6260020604000699200c0c800c0c0f1007070104481410035020021034820 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 141915224 1250 141913974 141914041
    0x901150305090f19080d050403090602010b0a141002030c0d0309140109050622050d05030604060e0f0601030203040c170106050405070e010e0f031f0c1e0c060f23 71
    0x2d81c2c0c4c400d45080c112120709022400c00400280e00103840307815110031814032244c189460098890b140b01d0090000540c80c050310300e40d0310724007080c00e80100c51100c0640d00400925006001c0c2d220090b280260a51200f00030040c802003040000210682c81503500243c00350151809000400100e064402683e0400c0b40003c0828400703d5901d030000e200c62186030200c07000218441007100342d0074024000d802018411251203410500951141c20102c0381000450b40b10700500c1381e0200107441c400700007240c580c0041d02030f50184c0d0055030014052050303030650a6130b6100f00003074000315804620b0130784d442c2d41c030420072820140500ca8102c0110300b00300c4040c1040358002071441ea1741e00c121502c20030340120311580c10344043c030044800c045461362501c0304001c0f54102c0d9018180800910000544401001044140d000c0c22001c8410407130303550f4445120a5210b5801500001300045415540c03a50b0514200c040d89000d07000d030300b81b20301060b4528548801c040b0400100b0702c0300c0c3c07000703142e01c00c850 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 141916474 1250 141915224 141915253
    0x30108030f0d06030b04030215011d0f040201051911010c1b030c060626060c03040203060f0901150305060f100f0905042612060d0b1501020c090115030509 68
    0xd8801d41403408541c141c55410808065001d080c0355440035104d03e005101707000034540e01096440d04242c20051610460340d0f0f070780300e80240c3c000d03600d8500b8400800402003000807c0312100e8070f070401e00501d8000c3c100741048664118a4032001c140c580480c44155100f00306210a014034140a2401d08211072040a204584071070450800402000c101411020000f004143e61001c0040c1c550700c000b120040140e19078041c038413141a10341070303440c0c411400050000c1480c501103910403640070340903280540711500300000062001d0a1901207548684101c60034034280c031101c60066000d07000400310350401c4800c02c0c5010401900721044414854001c0c405002c000741e6600465000b00070014107540e850074211200d5035204040711044105400c10078546a10002030076600040c4000e101054032a1410018024a4980300410b10801100006ca401040c0c9202180e111130600583d00d5501107a070004c0c0421400748c204000b0702d01504002c1c025241d044c441ca5a011038504014200e01003030000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 141917724 1250 141916474 141916477
    0x204150813030c021c06060b09120a02060406260c190309081905040906140112050105011b020102010b040e010608010c0903050a0b06060d0e0703061a0a09021602030303100302120303010803 83
    0x2c010f0300a0034117494550703141103181383c8002d10b80c0e082075081010302d880b1284200140c1c00680c600e4440c040d00241e000a030b22000c07880e40c086650080800e454640b4040094940381c12120244845902a80c02541410b2035060194407607911031181940d40c2401210700f6206024000550040501d040c42440015100130304441010204031001040314000f020211801d2141e034200c000d00c1414a180000d40b101603c1c541540d4940c240c0f44c0800c1c4410300406c00c41211000d10405001441010030ac1c408240014094481940103100208a501801d0046015100c40710341c0c6414aa54540d410080c6403030a01c00e071100403c141c0351001c6102d00e03680380c4a0307482480c0000501241c244401048240c0e8544080f01c42c02d001100c028071110104c07404407900c481c19444240c1d15281000f2a0460195403003c01c110301010080c02c65040f1030608070220000e40000700142d000c44070300c2140401680c1d00300051489444e2031800144070310300314814003000c00c4c400014101594010300046c01200008070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 141918974 1250 141917724 141917747
    0x7020a0305090a050301181211031602041103070e10021f150305070915090b1f05160501020903010c0c1a04030909050c0c0d020f1b0d06020415081303 66
    0x50210b403500c44440c0001c000e1101580070562540ca0f04042c180c0400e020b03850660483d0140c2480e0000b0034640f24140c5e203009551380c02c500c1c60740080000744900300440300d400c1100781c006040021042c81440ea0351a0b10340c01994003a01040388080b0000541c40c0800c4500e5050000e032004c1c201107000c1e03102e921010103048116401458481081d0a103001070303002070000442c0c1180c222002103a0340c4510304001d0240c2c1c0b180550308180c4c200c000c20510040c1c0030741d000c514809000c0031800b200b040601c3c60280214540c0d1030070402e040241c0c445004040007045115070140b4001130f40c5400c1c0404041c211031100c1034103010312080e444901c0100348100701c4543c07411070407040002310369128a022101608560007940707809240074140718600306954040c01c581d802a10440c0c04d40c20300311a0607699445403021403c0c8550042c0d801001800440722844c502801c09000c0c0300b030940340c6981d5a8240e0b08181c00c004440402003c0358450998443d41058100c08210b40d40500c01210783c1b8003c04070420341 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 141920224 1250 141918974 141918977
    0x80c060a05090d0b0423070b040308030a0b030f0718050f1306090b1003050f0c06040b0f0c010603030201020c12030402030a0305030603151614030f0a050603100903031d01020307020a03 81
    0x3242402d15a21014030b040e48065000c030b1001290324092400c0412200302c00c1d0600c221494103003001110f0000018603c007902c981000032803d1030728542d40e5100c5940f0082900e900c594507100c0758070706038400300b282c0c0c0c0e8800100805000318078100001803000350310348440d120501e400c006c24001e000c1c81e00b180046d0008a084c043c0b0046812900b041009800000801001e0403050f4040040401803840090142d920400a079900720902880f4903964410302d200c401e0380003d04201c20402d513401e50008000c2440040b00750b40c10046030148a5084403884e1348290b016075000604540d00480901503c00c01c600801c40f8a030030b5040070740121369100380c05040102440000000b04070150b41c01c0040340315a541c1000365590500d408031903010018425060740c0007050861a0480d09881c03c0b20582c0c0c4140d0420180c02d150382d503401c0d65080a0072028082c0740d01402340c0e20440c014080c01d405001e840901a440124185941d560450100c402d41e080c0040c40b030f40306106012400d41c0c00b060804009405 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 141921474 1250 141920224 141920227
    0x304050112021e0a1106040303150501050c1b04140a02030709051e06162004062309040201091d0609010902160201140c07180b09040c0e04030512070216080c060a05 72
    0xc5a10941e00c10011814286207131003500104805c0641c146c10501c5e5500904040303d00c4ac3d5558001900c4a000f002c201d100e0940040c440324903c489907140915080c500200049004c1c14145101d0f080d10070142c1c1e6118104d6000800c000c58107401c03c0315480100000c0d201a19030744011050b110b600e03040c01010901c6020001000c94600200c2451022195080812029082070142c180480d406001c075106010300d00307200000420041c49060320000c040183c2840703201c0c08900c0100181e0f0100104201c1c14802865004070f082601031141e5850513922000c02d00d59420f01c0b01c10000d003407505a125140071401000109060b480c401c0301d220b040741e828203140c49074030008850b5107158028280c20813054420420001020107180b00c960396082e05006081280022100034010380000c11180a400045400070401c040e03100c04090301e501c40d000f4030b400e9062604000181c00028015a40ea10043e8482c0032541440034010404100415460b0024040c10001d0000300d003c9000d034040711000e0200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 141922724 1250 141921474 141921487
    0x50f06091917040510022113090504050307061e0515150d0603150b01030b0d0c03020105160c03030806031c0f0c060b0a03030203130f050a09050901020702030f0304050112021e 77
    0x51a07400d440191400820803c100200c118000351f884110803445c0e150481d82481d2449028900c000f100e01c245141c60501100d9400c02e81480c014000c0070380201c50300d01c01040190b01052082c400e206080703c1c3c40d0b0400e400a10b4103110502a110b01503d440c108540300100080c01351b03905d4802541d41d84121040c5612806444010b0000302402d0784058100959801c46200c1d4a1856000c00d5070600262005c10640c0f06410903c468111140b50040c80e0100d041d80500266004e900908042c034401e0916198045035a130307500768048034030340c01100825034070418800140707400c0c0703c003c0310070140c516106840342c2c0700803008021428104040d014084582c0080c810f0001e1a0003806951101520a10700c0590b00d1400954951000e2900a84182d2001010401154a003000c100300c1d100201001035080c28164524014440580751803900d41d4200074810050320184090411340300c00e24091500d031442d240000d8206254080007004813881007082840d0105001800e00c082070a80020b181c9815 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 141923974 1250 141922724 141922763
    0xe06010f030e150916050d0b040519050706090e060117070225080106050d0b010902090a09050a06030209070216030803040305120c040603060e130201031a0d050f060919 74
    0x11000d40c1c2c22081e401031501e0b0382d81c9141003c28180c0140d000c1d44c01c60720410542c50450840302c2580c0262988090030380039180205416a40450700310703000e0070903148110071142c004075501c008500102c07840c1d04500e10401005030400700890083c406466414003924180000038804d6000e46961500300740468042000d46108000e070700c680380190491601070074426400ca5120f54214030909506600701580415a42030250b1856500d40e0300c0303c51240240d081035a000c0194004800058000c1940c80380000c05804501519000381c91004000410b241140103101c0350b05e000400c04415548410b00380140004a241507004607030300980000c1c0c40752150310342202d1900ca0f4201c20703540c68611030103005d804450100180101d407100c0e1001c000d05039071818185581d136001c88100030302d9920981d41c41c0243d4025003041c43d110100315940e00210315400002009090000303025503540d401300840003409a010081ea580064a001c000c0160170403240b007540741c800512038001e050084c80c40d0f207824041d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 141925224 1250 141923974 141923981
    0x5090609040302100e1c0f020307260417070504050108030f030c070204050906090d0309080a0f090308210606030c16050307050105191b08010510050408070b0c0d090e06010f03 77
    0x41303a44050600020401440c0705031344010010045044030a40e4002c2220f02e400303401111a94941030b00030714104242c0e6111030060003284000401c0e808070301c4841c1c0040c000d1003801003014044070800201101c09403904a441c240305a04894007440c44c01c00140b208800000c26151118546010030b80e03266100c481c268094045e070706000350030504020034440c0c0a98040703003040c03003801c00000321102680705000c214243c401000c07001c2e0641b0303000c0054400b51840381a07041e96101490030241d4a103a517030742d14030200d5030104000500c5138500e038214111081051540039001081100c0082c11401c181c01c81401e90702c40d5444051207600d140c0268010842c0c00d20a9400c525000002001546405010240b0b590351224900054510f01141203000342920008a82400419603c6401a80c2800c0a2000300d401c407248c44400e11a0030310000503000c504001c400701920070f41e040c0d1600c4008040403207103000040c249600070301c00801800d11043c1405040c10390312100c01d10b4003000d0b050002d80700780d008 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 141926474 1250 141925224 141925243
    0xa0c180b040204141c0803150f0a03080307030609060b04260706020303010302090901050f0114060f0c0304050a1a07031b1a0610020c010e190b0307020a0210080105090609040302 78
    0x101d400450005104001c040b00d84035002c40c03c0d9080001e0390080c0391040502040030000400850040c80820000380d500c58025407400009003225910601610001d0780c442c009600407030b0745c80030000400401a51501030790000b4500b0034014001c850030050454914052030140d20035000c8c20501c04800d00310f040c0004409040c6040c240c40401e034031608000d4881d402400240d000300460000704100d05014403c403842400d0340400002c160742462400d44698442e6400c0c02d0380481c00748039003512000100001c20b411400790b001582e41d280f40405101a60a41e94003502c51910006c171000f00005018040b140c203281e040c41c06a440c110040c50200a62503a00d0018101d02c00b241604007030780d1a47c0409070300480007110095400d440b000d40899072640481103060014421f030481034014100f811640c0c0c541440d07100d0580c846500d8007e490350301d41045810600583c03140e401007055040c02649610038000ba880c15524940c10700b00803034000c0901130000c074040c0c4a80c50000c0e082c18800d0000c4c8a9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 141927724 1250 141926474 141926479
    0x103060c0207031e120903080306090c1902010b0f0d1a07050d091a0603060c040b09060702180a20070f06060905010603060302040e0606010e010c1115030106110a0c180b 74
    0x2240d91101408803104c0b50b4154210303040c803181c90b00c10700707480c1c0600284801c90f50f111080300d00d1503035020203000b01c030000505141e820500500920309080d00c0387c0c5801ca0010526400000c4070600c400c00c2114000900745000d00032040e140e40b01c0c000c03480c1070400619460403c03540d00c940d0b4491082c1100c0610903580c50380c254a1505d5000c4013002401c8680f608500d80c05150020b05803030b0320b409c00d45c48010644006028034010031040006004038000742c201c506c2c0c0240395500b881000d402103008682d041c1d01901d83c203408101044281d141c2c80c89104020210300002124800c3c0174902d1110340d109c0c200c0080c0454901080e40010440e1503004003010b000d50f01014040365035541009805003004e40000c911603401d1643c02c9151070400608988a07a03016900e540100803407200550341410044010b0391540d17041d807018071040d10b4407000800c20b510b04013410703950b0350316100d0000c04603203c410304e00c18103402c0076204401148800b941d00d400d41d0b00610850118602c04900c081c010100f891440d038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 141928974 1250 141927724 141927743
    0x1504050c040609020d15080319030b0603010e2707030b0a1d0c10030902090a02090612091c0c030801150e030613050c010503240109051306090b0a0e0103060c020703 72
    0x15100300340d0b4010b0580c803074000c85d00b030040c210078000c0990480998000c0380c165900c01c2c007140d00b01503031005440c0403031611400c0016142146401088456009810446080b240340f02031010781096807208140030615240c4a407280b6980f950003170740710002403101910440584010480c100c0700c0d03a0000f890b026008490800750f030380d0010850380f40e045506403640303d6200260300e11280740c002d00030710100741e600802d00d076041ea4030038600e61b00a4109040041d0000c07418005580620f8045510318024031a401c020024138032201030f18030748170161101000411050070041400203030003228440c151440103103204100d44101804485007116924100e905100d0103003800000305001c0a0051060f011b0029a00c0e92802e42005548e18401a03441610304e80c41d0400c103000c10700e2251601c40c03c0010500d0440c078029643c600140c1d08294901c81503040c540d0320301003000a0882481403e400f10740544403250743c5864107440009c0c2c00c0c4144000f0b084140ca03016040307a003074824132408002d59070044850 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 141930224 1250 141928974 141928979
    0xb040e0a0e060a051006051c020c030f0c01150504061214010b040c050c0601150801090c0e040603060209090901330b0415020708030f07061e0609141302031504050c0406 74
    0xd00030b02400e070717003900c68003d46804c0810410f01c1503003194010700c00c4617040f180e5522012110402540803039032001142c0020302c201d000c2c0c0d1002800404100c100c82c1c002040307090780b21100007004c1c07181d58000c600c1949082d1040144d500c602c00d0541d0b4507a004140c44c035555840625050140010300e0805501c9403600f0b42e00440719030004007900c440044042294000d0782c1b5503104e600c40c164a050b60340042910400104407a004503001406100c00702e180c0000c100300220b003c20182c5040780c00c2103801d55004148c1d04030a08115465907401403004000380b0014a89100d0398907403083c180e664160810301559410003041002c25000000c0443c1c41c0110b81c2e85640d03840e812560192003032828014000c01c01c0c00120340000000f520038240101d15001c3c503015065407907500400725951440c4d200502e5160500c9040128483d80000b8841703481d000c01c43c82080d60044080d2310f00148036000d5040ca503481c010150300c0c006020f510f54400c101d407403c011344840c101036203030000409290354454101301c1c01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 141931474 1250 141930224 141930241
    0xe040504020a080319030b040204062a15020a03180305030106030e0c090a0902210c040207060e060406060501030b010512040b0711030706062c040605060d170301030302060705040b040e0a0e06 84
    0x141d019040c984d601f0401c05064004001c1a40309034460703c070004100d003a00e03460940194550f020301c2e000c0882102a841510b0b6600c02c810440d8454019803168007081c8101416011300034041441c0d0440c12084031340324980c0e0302600d5800180116030030555a2100b100080f00100110121010300402207852464100030004c05491a50000ca010340742140882003401812007111005184090107086042998014000250270042083d035125489508442160006200280c0510b015050101c1c0340d030b0520001505403000f0075800c5042010070850070810360b40309594503400680c010501020768a6002007240c184441c401c8001c1240030000b014410413800ea40110110f41703001c9040c0b000c0c0c3c1c440c51000c80344660f6402196060320750000009000490a5108035801100200005c86481031512100b01e0302c150070858911002e030003c018420f00d40c04110051307200e800c6181151a142c1032142180c428041c6101e0f08030440001d81c0480c0028855030403072040e010410044403481e00e490fa00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 141932724 1250 141931474 141931507
    0x310030503120117060106050a05131d060325051c02090c03015a06020303040c050f0a0902071e0f0201030605040c0207050118080a0305040e090a030e040504020a0803 73
    0xe41130070100401400c009042c001c21a60f040f586152078084c2480c03010b004c1070710780d42c1c4110301c0000c40010078140824286004207040c00c5501925150000600d0020181480e01800d801d5215a46443c000e00d0341035210f0428421066440999500381c414180d040341248100e051030000b98000c0a4004012030032256801840c12284100b00500341c200e40c10717451800c100d00f0030220450030a0610859031807054041c076101d0849a00c0014031500c003900c0040341c809010160800c00068000000f4030051040a48845010340302c121040c446036084003000800d104a644201c02405401181510a12000310744902441007c406241d6002620b454040441050044101d010906e40b07800814642068440c28181c014250018146103003010300540d070700078098002c10591a148a8007065114060017484c0c8090700c40c1e200c040d100c50420b0120b1800040c0200a001503034400c0e40d0100109034800d01d0384094000c03c2e1000107450f1a0303800030070b040703085582009000c0c1c4030004010104011200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 141933974 1250 141932724 141932729
    0x2d1214010b031f14061b010c050703110601060e0909030c0102040b070201080a060513020c030403150504030212120a0507020a0203011b0f0318021203120403020c1002011b0503100305031201 83
    0xa10400900f882c00043d11589009024407040c00094406481ca9800d1a0f07004084084042c945400369118a51001d425110700c0d24503c000100c0110307501d001c1640144091410803502c0010701050360422900401c030180550302c240c0b09090b44004a01001420701c01c07616140007040c025551152694100040da91000d035040380020350400001ea040307040c9200d1401900d40040c10710044018a5080ea80a500041d00d0350825000400000002800700300c0d81c41d9110200c6903011600b0310345400c001c0e051414010034481c503944100081c400100342d01010701e41c0040b51050010f01d03038641c0f030003c074600012460004d402d50328205c0440d07283c03423000c18031401100d00c550b500e207030585444804500782c401c00c0000440300d03c035450074400140782001b1400e11414400c4d04890a107004444044a6014251400c1c1d0158024541610b1142085d000e4040107102c6800284080100c690786060214403220036203080001c08400300d509030841d0040e100096410100700c03602d9071078110300c41d2005242032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 141935224 1250 141933974 141933991
    0x15050c070209070201050f1b0c070e010302150304030e04150513050103050105010b07020d110f06030406050f15030d030e0f030d060f06030605060406031104030b0103060c2d1214010b03 81
    0x110004041ca4414000c4c544299442043c4180a4440e8100c26a001c2c41002140e408e001c0240803180030400100300b4503005012422540c5503c5d4510300600a4016031004411a040010010000807e40000708002820000e0b10006498014005080320302800ea401003130b4480076500040ca05000c0e55007020b81a6402000208126641c80d500c01285100d4110000d402c150404098000b2860740000f001c0c5014000e0000032007034241c00c0c001681da500c125001c65540d65035034140901d00038405122640b20703003031100c00b6988514007000a555048501c9c1c24008154543c40c6d5803054800510490a0201d42841241e4030b6544840d003000140c140c0380030301704800c0c0c80c1510018030b451082c05914221070002d00000d107003508003101107000d08040300c0c410302c42c440100310000004401940041c000c50142000082c10b44103214001c040c0a0746012101040716040002481c1c01c1d0b0301c131484051007116091001108a1200c240780140c0610301807202d084646000006650105500462060011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 141936474 1250 141935224 141935239
    0x209090a12091503020d1103040c080d090e0606090d081c140f0403050313081209061e130302010e010212060909061b0306060c0106060203040501121406040915050c0702 74
    0x30240446011a20380f09514294042912180d9910700070390042000600e00c100210300c18120307400d07120041d441a60111a0740044d1041001444000c0c0300b60001c00680e4a088081715203030002c3e04402c0007018084510600340095051502e6485156000c007207039000c120070740c490070540d8502c1a034088c452850005142807907011001c07000400f600d98443d01b50782444e58425112920116110381004100c100031180010000000c02d900c44003900d10913035080542d04092a107680b499042040c040d00030304004007100c8960f00d400810b0000c5591000441200401d0801d186c1000c901500c2d140340c280c1000d5100203203c080900840a80c948030702e0702500d260708281c035690b510698655088500e1582000c003030030764005880b6180011500060001c02c400c0c240030201c9030390340c2140c1140d07002c0300140c0c2c070008081019580005185122040c440010440060350226103204440010030700d80c843d03540c5064520070419030140c5440480f054401c10080c42c68010620030443c2d0082105910440c131 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 141937724 1250 141936474 141936503
    0x301022a0d02010b1809120f0a030c08060a030303150e04060e12070b010e0c0d0c0306050f0a0315020d02070c0f0801050c03011d06060c0d08190203010621090209090a 73
    0x14080c0b00c0044401178140150604c490509031180d6401410801705801200114020702c504e40000d080c031158840b0089542d8540c2c0c0c00003408840910401e0400d2040308010051181d0713600000f54100c80d00340c180803420a542658011404016801c40010210110b00380b0081c00b00e10342c843c401ca40f850508591522414032240052402a590700400b4449210014031003103802081d0150001e400c0c2802d103003010204c82c0b0320130584800350403000019a803080104000c2c58080142c090261301034480840150450701c5410f042c010207110301215540001d4007820071103141c1c0c120b5500e80c0d0410005070700c4a441d4420800b640006110f1000b5941c20b00012500da000c600084074102c0c0d5201d1260075101c40801c1b42d0031150480207140b207501101c00e104401c010401403201d080c00040b5a60ba0402c146004884600038460001c0a611281e00c1072006200c5203030031000e1610450798140b900f07010307041b0b0014240b01403e90b60100a400c101d00c0c070140704000c000020010300246c4503050386107203440d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 141938974 1250 141937724 141937727
    0x40203061507170f0705281e0203031c0c031e0b0409080c0a0b1807051e03010f020a170f010506090303090d0807030207150203180301022a0d 62
    0xc0c0d5005074000a507080208000381490001e01d981442030074000250f040803c48081d058016030f11884240c00c000800708104441888028103560851010321065854076140740105424450300515181d0400c0403441961403000300f5443c083d5004080301d58a007455035520762046603513000c40502e1030a02d0380505005000e070160504100c0d594820a201d48024520000502000e0300a280c12958491007031012401310b800a00034011100c0040c508110207140c402d111600c01069a428420601c941080a1602055a0044520032a402c00c0c0c90280c42000341521f00d05807400c66890340c41c0941c0d650100d00b0320b40103405011015281c0b400e803481216010b4126203400c030740400b002e4581c0c80041c04186000c8000e441e90442c05412281840423032004100c1c0404443e4090302c1e00500420004101681008120060104000d50842495026034060340d680160400c2c0d4000718001d0101c40302c40c0e01d0950694a080f134505038034505c031450045682c43c480c404550500708a01517001c1952006 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 141940224 1250 141938974 141938977
    0x7020d020a02010c02180114010e010509060d0e070803210604090201090603020a090803070f060507090609121401140105150703080f0402030a0b0403030e07050a051804081b0106050f0402 82
    0x8140680207481c0c020442e500450b0b414604240482c0c2c80403020085461050320b6440341c80c0a4980043d0f200c034503000c140009446041c25882d40c90400000300302c2c0403401c2c0c5485d03041d00c0c49030807803440105041101040d0241016200d400844140c4004201d0ba1607031b505020400740d12920241350503030351b510342e002804280c035045500179000c95001d070740c1040b80384e00c00c0d8010446202076290124035a602c5611490442d8810101540d5069104010a06106e254071072140c0000f03a034104824003a291400c05001514980700b2840b000300c079510b0f810140a8080346188188000c80000c0041d42003c102d0521511002e0040c203004260304445c2d06008008002211803a0340c240e00c445409a441c1c543c840e00c10040104101d806000e0080410001a40030000c1c4e405180b10707480101e84060320701466440c0980c2030344014441c0c0c222580811440e104c0245071a03100030031020301c0910b9a181d003001c0c0c90520456140780d10040e40000100440c3c541035001c030703081c1d5004580301010300c04032b441044280e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 141941474 1250 141940224 141940243
    0xf06050a26030705030c0a06112803020f040f050405330103090c0e0405070609181a10020303040b0619060c0201020c03061504050c04060905061312061b0903080f070201090512150702 80
    0xc244103040151221042b1141202c9001403d20300540340050b0f4026101003074205a000b085500e407080b400340080c1c609401002e038442c1e01100244407416901c0004c07034103401309280e4400d44190350303001101c03a640310380c100211390707500b003400110700c0c55548558000b41c0c0310803201603601e401403040200b00c15208070040400c0344c4840700240704405151280c0b1004201707a03503001014499641100740703d6100c416405121480980103980c6a1416081c0000403000080605114140000d807004e0401c40703400303818040c0d60300d601c0c001210403a20320050b85403a2044040c50b6051007081c3c100709014662920042c102001a50240690b031943e0071080d4907805035000d070101240c4400c0303090001c1d0620784050024481c00c2c07401c0c010034a99640c0710103403a10302074006542664680021401c008803005840442d00798134640f080c16a855503c8829441c0036016042c51840c0c80000c120003503a22071440360024220040034018a43c80607032016548407450149030401ea056a00001c409a00200d440010f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 141942724 1250 141941474 141941497
    0x711010b0603061009080109060b0a09110f0703050c01050f0114010e0906120a06110702040e0303070804060b12030c06100518040f06020c0307060f06050a26030705030c0a0611 77
    0x21615502c0c01c1225044d2090451010000f002400080d558801d009a000103401101e00094200c010320600216408139088281410f04010382d18041850404c04c8a0038044c43c03510094031440da031302d405c03500c1d88541142003000358241000d114150010030340d407504880301d403a0401e422039950710040d03800b20285201603500c064803000050481c2400b0300d40e200c080403014262103c4800641e51541168aa502c51503110f880110302c0ca811801c1c507100311803072109030720011411403800c04001815582d00034002011541c8540680010707031a03c5080281020402099a8940441148032030f0380303081c101c94507410f20400703e600040c0c608091107070042007a410b0620101075aa80d03100ca40201c480720300100c600d9a400c01085559180910140990b280308950120b5900b0400422406480b4641c000310b10515002c20300304808000c0070070b00d00b0300420f022072a50051100129082c111b004004018000d400002900b074004040812554107451003520100300316900442000040d00503e0308900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 141943974 1250 141942724 141942727
    0x1206090905160915050d030c0b090a0203372102100f09050a060203130c0b0a02060108070f03020411040803040308073302090f0a06050a0305090a0819260711010b06 72
    0x544c0c02d1000d03000d1145030123401c0c5844140420396401c091420101d83d1104d080d00041003035001c500d01400b060b00b02004840c00c05c084551403107580f00c6200d1441c1c4100d00540c0f15001518100141c4102e103032980c0000b01507100d4070240143c13000e925040c500c89082900da01c1d11075101c0e00e80807144924007200f03030020001c0001d00c1840d03503094000d62014100f0781884c88050791a500290f0358a03901e001501c06510044d40340d501e21a8082c0c94a44180c100300881d810040d030034801036224162000459070129030216010080740f9800300c0358843c41d000010f09000028008c414401c2c030b0002803507107621800114821030001a0608004604190110f08648844100100003040ca03009000d07402c5000f80389074480d001030400245040701c16403142d00070500100b158440140c061054550054100024107000e10640e502c030704207803242816a81c3d018a5801041000c03603c9200307181e07040b03032031401140b00c603c14443c8001a01201194408000342c00301c0c02039200c011060058074100880603203142d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 141945224 1250 141943974 141943979
    0xa02070812040303090501060f090e0106080d051e03180d020a0c03080304060b0d062301030f0b1b03070215130308040212010209060304080406020c060301060801061206090905160915 80
    0x40000660142c025010181c4402c10076000c540288681070050a5400741d64032642e01d4141102d055441407a030070031040c0d140660820000d400441d054444181510f01142e40d8102904a8102c0c9109812800b030300c18000301c00c0103002600c2c02c14008407404004c080758040d8403160401c903600c009120000b040c5100b83c81c0100001f0307640f100596081445440c011440130030b0040031507102c070300e003a109880030f0761145c0c4c6c0e070260402c0440103910b5910034007003206003560454495261012404000801404050002032203414006454141c02826018000e0f501e0a0240e4000d5a400b201c100c0b1124101c610400714000d11851000303500e00c11f034540c80301d06107039a5640800c100102141d40c101e119540070010303450300741d4034200218406c6100d205040e461b11b04281000303150105549866005160400c0140305090300040024112407413882d2060316805c440d880b540c0604040d6100d03010301c0741403440480800c9004981008001d40148110306461395500f461810b441b003960004216020044d001d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 141946474 1250 141945224 141945247
    0x1706040c0b0306010c0203010f0911031209101e1e0306050906010f0e0301291804060216080706090b0a0605010906030b190807030b01080a080a0f1e0f080a020708 71
    0x2e160711040c141080440b403292500030900b903440d4114007180c44c0d035540c1c2e010020403d415601901b9484140c004102c24002c0c08440004c91181068884c402e03c3d0b0982038081d500e1241d032a00c1030103a09403507038452001c10b4180c064111040014142100c82540c50090f04e018445d11900c01111401004c0c2205919200019107198001440310b50401100c8030150610344c500740a4200c2c1008200b00b80400f04541c0112600d2403104824614407034245400380b1041840d03840442034109800140060342d42c0c0360308a4284245403402d2009044000200390102400040d62009414600550004032256100000b100c100d0341d440c0201408110725070000d118480c800ea0082204c0d85000d8480e408c00d030741072801d0790f0703a840729a0301885003580101010310810502c1840c00d8018902400280b00c44c0c2c039a82d43d00b0fa441d024103006501001007580b10101110722071074984072281c40c240102710502464240c0203122030309841d040c0b03012440c4000071440340450392089801e06508041c095040003250300c0c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 141947724 1250 141946474 141946477
    0x12150607030e0603090a080406020d021203013002040615030c030615050d140a020405030d0507031205060d060e01020c150f011a0c070806060a0b090a0603050c0706151706040c0b 78
    0x1054170244209000b0f0303800500e80c0ca00800203001950020308510000d594000e150200218160003540c00501c0104180600028140034038108009500c00181c002d0603485101001d8810195210b820030b2030016110003034028603c0300100c55a000d00450000c06016402d94842c1c9c45003800303116403182604411072042000c1c095599012002142003000d03180b10404152056840707140031035002900b003002c0e15040003c030005080728106242131136102e0b20013502545a4402c0d816840d334a5400049035a6114217880c04c41c02d038009130400440b0400b01c40f02d130007504140d54904983c0318119650514540c80d81e1800d202d0354030699074120076801c1544c1071101c0c7e00c1d845105014880280420600302c0c0d414061000a4103900d8018241490408100500484650b110360000e0f501002a0038803034950003421010340b001410042041c0d107554203100c4c4903114082e401760449103410208504003120088402c200c6000c00006a801c0b0031050100351a14002e40b00240158242c1604002000c0c9000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 141948974 1250 141947724 141947731
    0x14060f03010b0d050610061b021c0219180b0d060f0b0612070815010f0305041704030c030606050312040312140705010b01020d0f0c02041a040212150607030e0603 71
    0x340080342c242e480c080480c0300e0040e490310031640c0da00043c00b00310422001a102c00c2c001d0034203103460300c1c589114600380f0b4450390481801900603400b41c503951014601c2c0d014040045540548841010032034507040700c0180303019000741c0e01821542c5d03562000111690080310352103540240f5030f02c1c16075881c1c2d85030401400f4540380c0726010754036076000071050784d86e0340c01174850350150298204030f500d403110b00202807a0005114101c660404040300c903080c4d9008108d210b0400085c2000165034450b41820265151922030741c85049000250100400240110460841c4d10074041448001e40740d00415454803004007848640040510040000c00d8a80704001c402c6401420007891140460040c1d1526074000c600c255801d03915404209440c1d40d041181d0b07a180b41c000d15205614100d500f800401e0000080006841181c545200044200307480c1c020030005000180215030f500100c001e0712149000454184601450039100c2d42c5040c14207000715890b0310392540d1403103203424004040202a80025 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 141950224 1250 141948974 141948979
    0x90b0318060103050609062212030f0c020a0506010504060e041b050303031320061b03130608160806030a0210030b0904060605101103030c0903030d060609061214060f 73
    0x10240c0080e03040050203181d02071030060700074000d03525010101c02e151101c080c1400100241040360103d410561101013034846501ca09040c2c028812024200d0251005141e04046503280240000e02c5503000101034844030b2013402992426a03849003000121170302441400b000741d00c1000068006120040089040c000c1c40c0b0a4112058070368010905d50f8200f240e003d501080700ca4103250074070550301104001e81214482c401c00d02210800492001e005480d410005100501c00101c94030784248196031118042040c42e015160b83c0c1c0c40024010107082d80d01100500d44840d0641500d0710885d0064400d800280c02811000010390a210782608484030364010103940d0740000b005582c1d01008075026902901c00410031500705000c01c09180805007510042c0a0321030b800007040c14011064940c42101c105030192140354160101742144958849044007600d00071012030b80756000306050007907c10543d00d01d010303d404a001c4c14211340d110b10941d103000030076100003030851508284108401401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 141951474 1250 141950224 141950251
    0x50f0109060b090a03260f041409041505070207240305090601081207080403021f02060c090120070b0712030c030c080a1d0a050a14010b09010b09030a0804141003020406090b03 77
    0xb1b4004e084250089a8901601640024108900d0707401c42c1102c5403880b070403551082141026070f90103801e81202c41104c03091a89507400101284d00900a05000300b2401e14031050366042c00c60092104c2c4155a11040404c2c644404100e00f54400100306040c1c6000400409862145000900413604440c200300d031040410040031005803611040c0d0b05620041c8900d10700c3c0503e2400c401307400c2040091401e07454080c20701070074680e40e92040b584107102a080c01e42c890309440c9400c4003820050260860590048002134030000c00040104d114501800c0c0c0ea0100240b0700410011800c3c0d0316444900c20010341c00c1d04c0030030012001780d4402c1c0f0703072070180c07458000e4a1265080c945052500008003562240c012058840600050811080e0b0704a5480d0080003400c2d9041c00140c0110b00600501a0003c00840c40403a0340c2c80400031880010340090b542a121607540c1844410707003007420100350140010240d80c04825001b4001c0e44c090343d45c1516480c5555081c01441032554000618000c504210f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 141952724 1250 141951474 141951533
    0x8010923101d0d020105070c02120111160302010e0606100503060a05130603170301050315090109080d0603030e04140105010c02150a030507080c040506040302010c02040f050f0109060b090a03 84
    0x40352041c1d036040301e40601140e0580c216000b9803030800406100348800e41e4108070420032501d07445184a03825a6040f582c8202e20520f8800e0742d801004056180307612010002031011380e0b0030025200040552180d0b0090020108500781030352901000e40383c0359040100828210490350060307010b154010710142600d25103e6803100010301507101a0031401501383e03034100920901083c0f000250f060006070042c030340365501d00b03804280c0c4e40700e03110780d00304001e0000740104030420401e40007095880c0d00703c3e51458840e48028034100081c00c4500c000c5001c01c0b501501691141400e000706000400d010b00264050380c64000107545104484a04a80c0262402d520358240b0404801a2038400001c4d500014a80b900000141014070050224414564148410031565803500c045074140d81c0e0a1a004000090318800b05025001d000130312030140c2d06000c204202e54a007140e10038101c41804405012041c3e032586841003d100700020715400490100e001e2021541c20301400b0b4060001172070031209140d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 141953974 1250 141952724 141952753
    0x5090405070c050706051905030411190e010b0a09060806010c02100c02030a20011103030606070305120708060114040e010515040807122603040b0606160b0a0608010923 74
    0x40301740c201700c011413000b1460071005c42254031500900c040904000d880e506140d01d071f05031521204540d803846026204081100b9a20500c600300c0203001182e54411956110090b890481c1c11005038040003074512000010b1451081c100c0b04d004903810b03114603411220f507400340301c0c0004d80c0301c01702c50a0012411501c00180c40800007524101c4c01201840440209003040108030031650149d40d0400500c102e050b4a04040881101c1e04607004a6209668020524090707460b80200b0000010b003060941c20800d015030041c4116208007801d80c0c5d6042c0e10340c643c0610407a18040c034058016030743c40000042c855402c0c0703440314a241c0341c450780c0c4141c2019500d66049240802c6504801a40c2080c1c9901000b0030a4840d05c07489140c50a4030207015203440414030f1843c0b4000104050090a504404140c070340d2900000c03544404040c083e0800840040d08054003061400d480611400346803650015502070103209501c0d45e00e910030161000c0f0b0a00c201c50440811540c1c01c554014010000c0d41803064 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 141955224 1250 141953974 141953983
    0x608070e281a07050c010804030207060e1302071406010b0414041d0106030c080709020703120510050a08070e0a1802090a02042310020f03030a0f060905010902030402030d0f05090405070c05 83
    0x14601c01c2c88035642c5407001d00d0014107100850a44905002800d004d000c002600401d40d141560120700c5d09a017030081032000100058a60f9030100c0307089200241580a01856504084840d1010421101070f07036a0381180c12190310503841580808000180100788a1501e030b003080c600c1c003e44a081c4a5044138200110f82120506da00c1200c448031104000c0103420f0007400950024101c0c44421030510314552406000b86081140903807031140d81c0c40c00680d9000e4184031080241c90090701c40c5414039280d020203279030382a00e0701030211010700310750024186050a006005da2045042d1200e9079440480e4280189528040c20318041c1d2a000d2001240300d072043d10316460b4062505c102890381d880507209019001d40925048001c64115444480d10f001307001081307a400c95a10040000c1501c003500301d8000901464000840382c5d4200707400003078030b56995005140210b0088040e113144050f020380c250307850700c2000d81d0180465414000e80b41d59107815840290b110905042c40c850102040e0358980c1070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 141956474 1250 141955224 141955259
    0x602030d24120b13020108270d0807020106080f030702010c02060c0102030705180303120c031320100906080a09060e1c090501020c010206010e0709120c0608070e28 72
    0x31500b00442c00041c402d0b2043c4031a0000d00419607641030072116000203156080c01442c5000910240505c4400d18000b050303440a444101001d603072803402c038540b00405680301a200000150f0034171801060706440400c0b09000b1b4800710005510300013180d80195189602ca01003a6030100090051400308002800114071407003840d80d072217544035181380e0300961080800641c14000c0c1e100b444564040b060040400750080e1031041d40329240c1c0e039042c0c101c4003101000100180311446407882c1001180740350035010250300c0100c4428000141042044445050701c0c4900800a50302e040802c00d4580e065200310b0b900d40c01141d01240855440850703e00c0e000f2408072200d030541c6151020281d46601c59038400c094442403010307154420080c80001e50301c44041c0108504c070a00b010111701e40e01c1c0907116a6008008e284058601222682444004407003035126400104110400080382d0500c03030409101003c0008040343d0105030111300d003d0706640d200310350f004042c040703001c04503104080100c400c15 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 141957724 1250 141956474 141956489
    0xa0501020702130905030318100903030516030504080f0706140405060a0f0605030c0f0a050a12031119060209010309020910090b03071a0a020109240e070602030d24 72
    0x20344060610500c40c5a50b400261150f000c0d10b05110880000c9020003101d400001d0340c40c0e03a100c0318940c1c141c0c4504110500003001c05961410100a00f050b41603004144645140242000e003460340c50b0081d01524400c48006044007803c00c1005d454014100151010b6805000002444502c102440a8541090f207050756180d200384204481e040310342c041c44089488403541400b0092421000c46d40c0c0d0039094211501c0341d0b1048a60340790a45403095214010240140711000140e680c481500d00790714a20b5050300007034200921105500c3c00001c2c0480c0c10764180c50011a08850780e29131400075040b5101d901c1c10142c68000318000f40c0d88007000340d8011100700840b41a51860301500408603001800c0080c040d8126110410414106024001c0b11480201c940340e0b542ca4a544228011700303030000c000b00290007940d664609883c1c5030f03110002840505904000d0300800d2a01d0a81d202c50a114540050b4401c101441c0717181c45640002e420000200b042208030704034206030007207011b1550403802c0d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 141958974 1250 141957724 141957727
    0x11070f0504290409080d0c0f0f02030307020703030c02011e030b1306050d0212120403060230010501032c010905010c05040303090b07170c060405060106020d0203040915080a050102 79
    0x600d1410b0311840c07a003041045403001d5040341c900035803071458145284451241e50ba5000314800e00c031049040b2010881e0b080402c2100f402017020141280c0c100d2114003000030900e00203070000e240000103c1c3d00a0786940c00404006240d540c045402e8211344508a042001c44a0190007451601e2034034100b00203d51804540d0100351400e220681d0001850207900354103041003000b941d161541e145462680594200303617403d036004080d40c13038850740d64425402d04200290000134004d040e40605a80d09141e4912807008425414113004000c101c0c59021841100100421a039806039000c03078040c900c48510034441c2400c4c04468480108035107070004042e519200c000b0100002071051560449050401c6410141551001819140d15005603a94286e001a42e01c003804003003508503442201214020703968030444043e29456103c03d880441d1544994400424035034004210ba000c54840c0d0fa00444c106843d00601502502400c16160450680014042418001440515140c0c0d01903000036 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 141960224 1250 141958974 141958979
    0x13030e030a1104090203030417010204051801080607030c11300f18010309230610120825230601240e06030a06080f0a0206040e0711070f 60
    0x2510044640005510a03041602450009012905665001071040c0c50000f001a22403021900e54410754205640301100c4444102005030150014029203000755600340340160390200e55003400e0b00a00ad040410b400c80d10002c1c1c0000c0c46503105e80a045107510b1314001c0705c80300d007510600300b03014582c10740c0d41000400001201080c900c0f0a002503505240c600610300060151140707000d00130945e521080031407400b41a107035a03100390800003c1c0c54008441c00070618100071402d00f800b241e9510440d280c05040300041e00000075802440884d5201d00c0c40e1098140c2d01e1342d90745015030012035000026144042840c80000581c010a412684900340742c444103100f0922a503803c84070305c280d050300e580c8580c0c010322100e60140650401a080c1c0603245140c801c042006880d2046140103c4c3d8110001100704160324445410440481e00b2110a944c0c0304a00c41e04c0864498001d002c0107908a14200401c101c000c100009050b803009842c074211a0110a041825050101c168042166120341040c103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 141961474 1250 141960224 141960227
    0x130b010815100503060601080702071806060e03060f011701140702030909012c0403051c06091808030c070507080307060506040c0c05071e170d140301030b0f04031202031303 76
    0x14035030004030040d00b04002a2602c0e001035503038040101000c1c10030098174040f0344618001c109401c040c00300d074061340381005000030490b801080b040c840e8a0010740d00203105402c9040c04107610b40280200d42c40204603a08002038680d0003111501c442820b590b913030036a0b03940c010043c161a80a81078a9002c5c642e500c0c00601000100e00040c2c0110040380e4580c80d2400100030b0004860b051030780400058600d69550742015640b60142d80c05548400c000b50142d88200201903100c078041e01c081050401c804010390030540c4081c03a03500030040c07491204102295510f15050041c18215101d00220344081f91218402c07425034000b8001180d10540315005c2c011246000d018101100000e8a403c045180103030301c900d81d075000d55224040111044800341c0c43e20340e116041120181229248a0708600481c0041590360001c0186100001d003441034600031110820013107034100da4021080d0540c5840303640010b003807020050030480c18421101305c00e42c0b00213014000742d40700302c2420b85020319419a6050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 141962724 1250 141961474 141961513
    0x708010f060510090e0606070516030203060c04060509120102040513050405011802031c020c0d0f06060b030403210209180702060a0e070e090304030204111b071508130b0108 76
    0x2c544540360714240c40d185658800c901c4003c54001c417001c540796803035000c08104207214003030019010340600344030107809203140085441100d01c281e08a5410b661140a00241030041e0702403440014000c0040320030918102a04014200b51907000501d0030343c0e2600000d1050100324103006203691038000304020303c1400c0c82000c428a1142a044000c240507500003510b4003481c007490003c111829407920002442040041c1c0011005020328011890a05245540001c5002c044038080c1c14403501243d51901c10b01600c0c02070f030b8035448989145890203585040110003188411105509001c18039055940400b0256074940c0c080d444442030414190081c200034000702040041410400e4007055000f001170a0022505115884002a00c509020340c1c01c41c4115480a54024100580b012400d0ba00744001c0054580d2500e01a091401c92040d03207032141403a1040c008000c03901c4404000490184543c10360000d0301d04420342c0e01e100d041d034400400c0d440a801c11680d0354450111070513120f56080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 141963974 1250 141962724 141962729
    0x6070e0109050f0108041a13060f06030803040803070513030f0b0601030b0a151e020303010618081f23061302040513020702060f03070c020942030708010f06 69
    0x40d001d079400e401c0c040820003181c503c0702070604001016001a0a00c0211008420a0ba046891494031428600c100300311003d0f41100644800b4a04016440910301e140720b0f0404580e400401c1908598558803900070581005010200340482000b598503040e0318070071004081c41c0b01d50710031030305c10016082c400b00d44240181b0107814580303000c206998568411079031100310b90515160004450460000b1a6041101c014841c8020305561409107030580100c0554103940c150703928401c038015106042c2e00354a0146c89181c200d50842042441800180200004503200c0310f6408200308114101e0000e400010b50410003556803408184190303898407195100d036120740d01030150700301807d00300015500d500702607803000300030383c005542c60454482030103a911a0303d85d00421a203078500000c0143c000c8610400480c07058552200040c03410100856240c0e010054510b1100d055952401d00c0800e60019030340044010705001c1c81c5695a0360070030224020300821000818a00740c0303032040c881518642d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 141965224 1250 141963974 141963977
    0x50c160f03030528020904060b03010f08240a0c2105100f06021203060102071706010f06030c0203180102120d0e191e150f020c06070810030f060e010e06070e01 70
    0x5045108600d80c4804400c10907640744c00c005076204000c100142c018a240d41c00003001071000700002440c000340e0722456040790050415a075080000028201e444030b640c01d00d201c0300791080c0340880c0c5500c0640e0301030154080300d4240742465284003550389400ca0840920718010507152400c00c43c4041b80020305800800110310b400c14541c0c00c255001e52541000d442d0b040c00048048005145603200f000383c0401020ba02d4410904031002c05a804c1d01d6003424080c0c0380300c1c00c181120000341584030b80715006841200c2d5001e18240140045010790b8411410300c1130b411481980e0360407010007080c038020540030141c40700000f9000c9005151a040c06a00c914101c40d044914201c80f0114205404040c0580c00021151050030820f02c0d1070200881e0205000103103d18ac81c078505142103103030340149003d00019080350000c0c0e8401404403070b801822a038080e21041c002d4820000641d542c2e0200781000e20070100440c038100c80c0700740c3d0360840340c918105400344e612036010f00800542204c050415a28207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 141966474 1250 141965224 141965251
    0x5030901020f0708030708070c0f08151501080604051302100509030c03070303140307020f010f020301050f1e0d020f03060405010b01121a0913050a0501020904061d0406050c160f030305 81
    0x10413003a15228081c1c0000504000000511102080400203420b40503045580700c595020780c50710a05543d0f0707001c15820b00d540c480040c0106000090300202100c468a050359500e00c2981c550342408017920015080782a0869040281c0b00180d58031003403c0309024090796200d031548004000c06141404030300302036000b500001c0041c40806ea1120030b25001030005030404d80d032a205c64004a14200c142c40409211794600f16900d441c4030141c0c0c000b54100d03842155070000c03001c2c0c044100070702c040341c211140182010020300f941d1039060038440ca0201500080c06060b000700440c005c81e0a05404550484982e503540040090301d44c0c000184150040000d44108080c440004640001055401055201d000c4240006a00c0c031764804001d04400e602130244d40800b440351815a02079042650790ba4419030a1401c040754001041301c000034a440010380c041e1540d140e6417183c3d002040050103103441d09400f0010391100b40d43ca200344410042c0f24030800c03180382c05103090050456102600c014801020b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 141967724 1250 141966474 141966479
    0x150c100603150c09030f031806030c0e090903090607080a02011d0a0f08042c06040209130908070209010803040305100605030c220c030e0705060304020d030c020f0d05030901020f07 79
    0x104141e103148110a0b10301c0008410403003203001d4a40c0c19250b800145035500c40e8035680201340d841030001c9001c85050131080e940b1511414180c0944088415a100081800003450a145004140c80390845400001c4e80c2c501140718001ca1420b601051060301c41c5400080c02401055091003040340501c50541c080306141c004001d4a40c440d213260030080d0640141c02015401e12020000f190300030603c2101801c80c070000c0c01240200447c540d41c0800c094804200020120304141c021100398846c0100700c5110320941c4c2041400404c400a015107042e00140034a40041c4c403095103e9018200d002d0003075440301d2941c901a8a0094521641561581081002c2055403800038400203201e50403214040e070716552002c400f40034041c9000d1621420f08056907000c1090b09684061a070454a8090b200059118401c1c000248000d99009411031001c0e04c0c40d6002c00e20940301c66800d81d1000f4601585241e113540052814880207405940c181c00004415210750b8040084110800250707010301550751 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 141968974 1250 141967724 141967733
    0x30605030616080a0203091525181e0306060f0e0a02090a1503090b01060c020906120c0d08040b0f0d0506090f01090b010c050105070806010f0305090c011d150c100603 73
    0x6015100704c00442d004804a98408418840a403001e40c41400c2c66140b80750112500b0303000110613002c100e40d04e855901e04c4034a548138800c580790042580300601c800c14a003c04e0b201025048071070820901c0c0e0700000c04400a0043e004682c018103d0000c1c039020741d400c007110328000180151a8160f014810080000a502d560703131300808580d00880b01110040005c2d4083d00900400b040042100c0b4400d00081b5a240c2c000c5ea0704800c0b1802645c0d40d14680d036a031414840340c000025036031402c3d40e100f4520f4011910700f00c15105041e521030f140c1517040541d030740c0da0310040d90814122101c0400700414008580c5401e4800c01d94001c030200c030590140c1c1047400007030402d0201801008012603d40c01802e1460340182020b41d072941d8400001c000038500b48400520041083d91114001a00300403128007561003030080a019420020141075002c40d0303400191a08100c00d100600e000241104402c00d40e941c120010050712518048290f40310000c070442414080e4022441d05258508802480801c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 141970224 1250 141968974 141968987
    0x1a04030906030608210702040e01020a09050114041e0b03071d01020d08040206220311041d0714040e011503030e01020f0601050409110904050307110405040f0312110406030605030616 80
    0x45c4405140c00000070a550091942413003400d40c069005400c06010105d41c040540c002d2050043e90381e034400381c25480320700444250020f03c0200c0c1c0041c00500052040354000006e0000a4000301140140c241c3d5410010550750401c0f0707031a001040352500e03511a044d08121171604900801d1018001106141d50060302040d00035102030300a04000c90001d42e032034691403021485412462558401c00c0c6c0e20700e45601004400e00b0344900450400401d00c1c0b5504c05d282814001c80000300203003d00a042c0314003805c40fa04404002a4400e0b00c90685c821060000cbc4100c600496401d074403d100c4a0543c01d0142005401c080524110341c05024a0701c0c0e0360b400071070035506441003206c01040c45405410802c44280d20606680e40c801101d070f0a02040041c00802484130710f1003000c501ca2107a445008220841d00f003110098411381340c0302580300010b88180000c9200200b11440041d142043c2c16000c4040e8016800c00d0b00800e40d20a000c1c4050301e010805141c0c08010300e40703002414001c0c0000140b54 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 141971474 1250 141970224 141970243
    0x10e01170a11010e0607110f060405090a1e020d0b0307060203030c16080405040c0203030114030102040612020a03060f18050c03130f26030406050a0501030206160f1a04030906030608 80
    0x5080d941038035940e01e80c0715030001c44d075081c0c000308001c4e01d0303104a0400c2c00800000e08022445950304030301d264942d0074800c3c251421164010002006540c440808502a0103a03030841401c8401d5051300d4003003044c2c148082c0021501d03146001503c1c803034440c1814a40030050f0012001d55006104002c02e50780c3c040c080340e045c00300403a80700d0f510808500e0a400c0c640901d4101d9580103040c610041c2d00d0507400005141210321a203440c1003010012000e2600700c9c0728030f010f00e100081245c0200a1503603d1600141540c25080c500010240c3c0c0e41e00f004802403407e03030403400e0107851382d415070028120903000d015004150724945034074508007a5848040090403d4005121142440920080c0200d18083c0545841442e802d00f80d145100040b01c80194007c5400f10380c0d841c60200810039036210341c07250350705907a80940098a0301000007419900020360580407200400007003400700015140d41d019440894002c12920070380c1c10146005800c0b144250440c1c0c1c1054500710081106050002c3d14141 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 141972724 1250 141971474 141971483
    0xf1a0c09100509060409050603060c07050304090c18170f16030b190c02010f061203020601050909100204120c08060f0604092d02100e01090302060901050c1203010e01170a 75
    0x101d500c860041651a8003a2150142c0d0100010a0000d005001c64103c180700c1d000c100c06413151383e51080c0c21290a80580100039003641e2061105101c4000c1d01e5020199403442c1c1e08248511045008006100c12043d030810301c10f00c1c05051459040407070400a452400d0b0310740001c0e11000300100540409100603102c06425000f41802082500299903000c9070708014450041c0542107907600c0c0079001e082c0200908807401d1034442d000030042c0c407c07a4103155084e455070107800b099180c10f0820454030340141c0110304500840120050312101840204001c041c84140491f02211500b400d0701034826590058165401149c2001440c1c0b00070722145500c500110303030028818013181000c03981c000e44d00c0c4c0c0301c9000aa1100028420b0494030801800c00741c42120f401010801e0600203c0310309000c1c0c0f8100f40882c1c2c2c2440180010311b020b0001d48500c54041c0b40046c00d011a455002d403500200d0200700d00c20890010052005005061100d4090300b0030300c1c00e40281c2d10141008581e00c0140388000740 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 141973974 1250 141972724 141972739
    0x1c090321030e030c0f10110a080901020c0109060605090604050618090a0b010315050109110d0906150605070b06060403120c0201020c0306190e070501230d05040f1a0c09 74
    0x28041c041e41c0508a00c4401a04998944c052004916984e010481a1016038407401001282080e001d00800c1d22005248550f00d00b05260820251550306018184000954003413001d4065041e0900c600500c140c010f18011803514a07000c2840010304014156034011403c020400c88681c036219482d91031940220959520743da80c900c1100d0a0004c4424000c0801881d81c0c000421300080e41c0f102d0b045004049010812a41e0f02c804c0e610403a0500000c2e43c202040030701c03c410040b20700c0d82c00024404e0007103e0200f03550030540b090500c2141c6a40000020500c042040fa080c0a8284400c90f400f840c203035000703031a050030341d26104006112000ea00b0f00304010101e903101164801c0c017120700d1a01014040720b24505181d003010145640c010020189a45041780c04200180001180c00449106845241c500080130b070034240301e4001c2030a680b40d404001c11400e0b6543e2460301c100ea124a003e0341402c1d04200b403e00d02080095407851441065003840400d000c2e0261030b020849000074003c84034135 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 141975224 1250 141973974 141974033
    0x1502091516021908100506040f0905060711150916080703020604050d060209030d11010e060402090a0c110307050c0109061d120a02040e01090c0b0c06010b0904060510021c0903 77
    0x381100ca10f16041248036004000681c0c69001550b08224068102190140915a2441c214034100e5460040151540c1d11060208011601460440a41240c10005d495400c02c100c84181601c00c070640302c001c43d65201021901c004105408620301034a0030b0400f40004a20710f230002201405580501403144941e19411803c0000c20350446104220180650303002c02030031000a8030303102e9902c03d00c2d600c40d402c098541100403c04910144900d500415141b2241c0340c0d0504a001460110140800c0c8002c003103886400040410280000790f1141c401044014018000140310304c0c2c95522680a000f1704081c030100302441c00941b480001000d0366004500c0b048083c1c1c0a15001840401941080c940510440300d81c8042d0403812803907009006408001c1d6a48020703981901c2226024210740e04150700611010400b50000c0200e200c0080c800301e111074582c80002c8100c40d001d0b1501c03000d640000035410005e4407001c42c843d6214024104000513034a552101c155024410072100c08101d582c0080 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 141976474 1250 141975224 141975259
    0x3040515010806090d08190504030306031b0302010503010902030907120503030a060609080a020f0f040914010b032404020f1c170a0909021c021603111b09090a150209151602 76
    0x25940c28003208071048c00079080505001c4c008002d0740c04160381010b6610341c14900303182580c8011040340d81c107a5859185a10304284200250006400a50780b80500790000074841220b030b40c0c030446507001e6000f945c0c0c3d82c01c001e10590121000c80d4001e0040c022550410010101c2c0490006061034041d6130b807481610070768000429116041c440d00317a00c00c2c0b90000ba00e05000009100604c072a1400000300117200c1d00e40c041513605d40442100c09407486d0001a074035401095080380b540c01c00d00c060210f1102e80085000510b040c4400e04504070721001c443d4220040c481c0d6420000b0483c0000748406291070700d8010010304612490040c001307119000905002142001c28142d07130030118a082c11501c600078000d500d424044180000e0300000d0101c00ca20740a901c0c013003196100c4403000600307070240320b10034014010f01c200c008002003c140580c4003844085101c1030642d2600444040300181d42e040120200174a4002c41101651588414001d414419040d5103c02c1e0001d0340445a001070403089248 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 141977724 1250 141976474 141976501
    0x4060f0905090414210d110309070612020904020a03050703051509131b060201020910020105100311061b061e0c1b0709020403120e04090c0b030601031103040515010806090d08 77
    0x2100d0702d200c91001c481610048104002c1e203045003520400b480540c20011f00c000703090101f680c1d42a02c582164508004060240d2640c50741b0090701603003d4281101d0740c001078202e0f005465018046034940e410400500e80c50f200705a400100700310015501040070b0045a41840c0041000b900440c6c160312880c28400e80702d18030407644150540360020b450b103070740c0001c0c042d421250382e09001e52080000c0002483c0180a554840c07050640008100307891500d98008170b05412022079003101c0700304001170f040c151443c051036401c042c01c4001c00044c2061a010449840e00040e20100041120180107000c0c4a0303c0850b80b0001240d0868601c019601c00c6c400d00309107460f4805d064140c03000400004100401041d03060400054a410414400840900058543c4050014030610304400188206025000699003081040c5000107400d500100b0000c803076813041d10b0a6420f0b920813001c1d079001038503583c582409081408050644c0b4242401c0303142e561b822140d984070500002c81d001400c5c0108816 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 141978974 1250 141977724 141977743
    0x2040f1814041b0e010f0515120403030b06040b131503111206150316171315060506070b010f090c090608070c0c06111002090105090d06090c080304060f0905090414 72
    0x4816084d996501c1c00b00801c442014031444c0d020795100048088100156000e1f21b2903683c60501218040c2c0d219038045009056940072039600407021b02c000300300258943e003d41071000c041c0b46d41303552442c103201c89841e0200746622100200750801600b00b100d0700304001507c680c0051145005995142e8900190301040001ca0b503c4200c0c80100800841c08004da44150b000d451b2900c07000c84a861203030003c80820300c211055110040300000f10000541c03050003c001e0506844c4000a06036200c6001452a03400150140c64544040c00140504c4009454000007040c403500108440918480042c03c554000d102d100203200c0403800040d401070140c000342d40c41c0c9600174101d100c03160700c94330701801e10f41c20a022444a845802e40c0c0b460581c210f031003200e11048050315000d0a003101c560800502c131400043c102c8100740c941201030005111310f101d40001d0001030000e151290b043c07000082030701c141000c1050400c980d04d130007004140c850101040c3c01c1504800c012003074a07080d0180d00e14159594 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 141980224 1250 141978974 141978989
    0xd0c0c09050408071109010f0b0309011d070906090203062805040903030e06060109030305030a180501090f02090708060a210f06150906032a080102040f1814041b 71
    0x1d02040100440d500c003d04440d8410318109562403c50002c1c04100402401343c880c09000044003440541899406180e04c0802c0200114071002410f409002c0d40e600103900d40c3c405c2c0d000d4a010302c8480741c1c40c000d803000b503d0342000460551808030300050124098a00321002c03010b01d0a0400030845100f07010502405c8064001d1000510a2500034020300c03540c2e00d8070f082401080046007640d031041801c0c1d01103941665900b800d60b15413940c000c0c010704c0c0c0100a840800c0210001000040080c002e94519501441e4595941c6c4c3c1d443c0140020b000004090504000348502007080365614040100f040d52000101c541d41e1071060050f81c28240080a000351000403910600c07001c0100345e820500c02c0408005d00032100759030700c4600d00c0230789085000003000703d0321300c09940c2c560328001000c50001d00600810140c0c2140e80e1000316003264071a800455021004000034058414402030491040b41d040d07904110025009040da200f42802505c01400100300121041120b10f0454607080032340640d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 141981474 1250 141980224 141980231
    0xd030c05070b01140f09130201030f0605030f1e07080304030b060604180c090503010e0c1513080706030606050a080f0a020c0706020c030c010f020a11040f05010909050f010b030d0c0c09 81
    0x403030103130b884c0c1c4850b44650540315080e61003201c002801c051000d14010400900c644160700790f242e0054003d49110424604201d55800e0f00281c00e40d01001003109062403180078100318240c151900400348101100d408191f40040c0c0100030b04c02c000003c4408803034005800b60056240c01d1b00003a06407049034015503d0011120f0340e234807900200c1d031081c0107004090300c911040a036524149403d8554060710449a504103a48071101401c00c603814010000e505807800346410001d82510f10b4041e025000b0450581c042e02c400e101d05038151207220003174101d6040070350030080710308402045100000c000c00011000d28000ca10000030b00d4055802580b100c1c030982c2c1c00c50b900c5030300007903940607441c469a11910a1032141c0388954011000c107400440703503901500381d50032a0740700d08030942c00290045400c03a13a10507c0030143c40c15881000c0c0a090444800306007001075007041361801c21b070902d007188242d241103904d480383d40e400a0104008001401c1c100045211800c00811604040d8010124a401c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 141982724 1250 141981474 141981479
    0x8062d0114030d02010b0a03020613080102030c070507060905090103110102010b060d020d0f0204030c0e070c12030c080f0124050405190314030a0503010b0f0c011e060e06030d030c05070b01 83
    0x4214940341c00c0301015001c0703c0304030380303185022401e81e285082566040f0400642c14805418040024428020810441c03982d096444140740e089900446550200003004110201000824050307000100745d03910340b5404003070500001030841030f810f200080c2489001c4180c00b800364000e40001d100c40d4030051649441e69100c0c0f1280c0047c1d40104203e2900f5440c005a07640010824400c4e10241c4e900400d02d28122810700201d9039690300007400100620100030810000115207200d00042214590340103d1000521381d000b603c070110252051541076200c90045c00940c00c030181040410140341d214501541400c98241d8141c411908091f80000003c13842103501480845000122407240385888031100c2c45001940c4c40c0d00480b100b00d40020070800040040c20031a10140180400d5030b001140380c480f06840450860340d5050282c00720260481e80b00040c9512442080020081c01040f890580b4043c00000d86402c91400006d090540c0d0740c0064035030510806c01c0d02c480a51258800c00c041d40c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 141983974 1250 141982724 141982739
    0x515010320090a2a180501051e07020a09050a091101050705060703050c0c0105040521041a0f0c0f06070e011805060a090e0a0e0c0f01050d052d040b1008062d01 70
    0x307801401d01401010b41150020340b65103c0c0084441c5060310350903860844100e0000389e5400ea01c5400140c0e80b00c0040d2502040302c00403032040364060030300400009010019881c09001480c0c2d40c0d003030f85040c05418441000072035004944a81d2100a9160006e199654000d841405001c0c01c8a040702640c41c0500b0042005800100c0c1d0088500d1411444942c0c0040c41602c00300d440342c3d00a003621400c40300e07031441041403841d001d0804581e00307600c41400d141e01d0320101850328a410328000c540341e1040042c011000d420a140303c014440031720308400d00c4010020307010790f0502a489107901a0300001748680501c0e01c46c0d034040000c1c0070003c46141641c2480140000503004c0d5007018421401000280d4110b45030894850740d200d00182c40c0c4078201a40032191500900008080c1d040c00302591400b4000c0070b982444440e010075510019036010b04160608040c00d09000b0320009201d0300d8904240902c00000038203591084001c45030541d01400c103101c0310710301203103503500b00046d2000a0021a062 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 141985224 1250 141983974 141983987
    0x1707031b2904051e030706020906090622060306080a02010c150e0a051204150c020301090b1e06032b0c0b04030e03060703050c0313030207030515010320090a2a 70
    0x2903006508139541c09041811891011040d004100341c243e204208001c000b4034aa00500070302c0c5401400c5509005030740010130000e510000b04001c15140e0503032602d8030407082d0201480507003514170b002c01c01c2d1420100080d503540400400a41070000751100402086400c0030544e001d1006280280071940040c1482503a070040c03200222002e0290021070023208000c00251411541203a40c1c10901d020308407415074100f6041c800030390309075498050900104801550103400360b44201b6444c07400d806c1a090345550900080d0030544079402035012160b030079a25004142017401640c2c42000c0602155005480e0080120070003401c0c00c407942d00300018942c009980c900c4014058040e100c0c0e907550008100e0031650111131100b400041440805da1828010171b0081c44030b032107401120942601c948601b40b402c1d544918980e15070440344010300401a140d010b0519041c18030340400c80c08484035000a501d080000c0c01c01030440c2d56400c0400203500717210031f107030901410003811072200d0b1031030780b4000d040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 141986474 1250 141985224 141985231
    0x803010e0702030c1b120a0b0702070f0b090405061f020102070605070302031e0705130b0306010f020f030703080a06090c11060709050a0909080903030a0207031707031b29 75
    0x300c0040c00001d030400c1d00100c21585103410090180201a00ca4543c0707030944480f22005035049003101d41d21a81080d410400025802c3c01014102460b02d01b1020007450702e07070160010600702606040c100245041c0000ba28407038001114081499503d06001c9501041d01e0000300130890040d04041804c0b41d010340c014140b15014180c144407666901005500341e10081d19142c6a11071a0100382440c600a5050340da044000e6103443d03440c10343c0f5038481540058803500001a1020b00006101c0c540d0703005103824044100c0380c0068510492001c1d0707a29124003820f50050240700a80c1e00054aa042d141c5c008400b41c00b04d00c0c030402481d810014000c203104010002c0c51100e00c00c040218a0700f0f400703840c504084440c0249585407190800705040090995100704640240c024072401c1529a4280080d00c1c5000c100d90040106600e1402c018501a81121403a1032000007000810f011030b50220450700d0301c54031079210080841503480e1049181d848613080c99881001c9946c0c50310600440c0000314003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 141987724 1250 141986474 141986489
    0x110a0b040203060606090906010309080d0212090c010207030c1211060d0c030b1e01030f090203060f070909020909010306090c0f1403010609110a0c03090503070b0c010c21021e07080301 81
    0x40e40e9213506000b028802c4c50803180c0d10100721400544150f02c01e4105506403885110078509103d0201030490680e044411081c1514105d00d00b04800800c0400c04000c082d04244020306229146803210500c840d520302a010400c1c114644010034041d819403003480d101000b40040707550310a12840c40c0f00801900141000180c28903c0350100f81c5059141e841040d4048a0068001c03162400190004c00500800700c20194640704e031140541d03000e11410748600c807001090200c80c50001002040000f058000d1860380e4230500807070300700d5184c503401caa06483c1d0020b00098091894101189001819404000801140e55010a500010020001c000c200c1a0000d00525440d00003136000d0324010883d19003c45818490082520700c40e10410b81c01c03d000381841c0030030545440100b414042540c0180410170000640000540c00c2481034601119a501c0d01392180050101036000c005007000b4503450054021454401d11000204032584001003c40c0b001c0d40c070443ca150502180c1c109200d502d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 141988974 1250 141987724 141987733
    0x10050f030d1b031205040503030402010813170f0d050a0605040b0306060d0219030c08010914010e101d011803031103010f0302090c0906130305070611030712110a0b040203 75
    0x15aa81400a01850011110344a800720b00c21100c00d0310320301242020094042080010f6954280002d0f403203058051801080076668071715250001424071040901a892200208402d0030301081c201030108200e000081002a03035507181e0700c10035000b40948a84171030b00f14603000901c401e64280340e100d02c0c2220f0042d64140810114041010b84541040324016088850120134000503d01808220441004046c200b0306440e1aa168510910070507040710889a56072160b00090000c54182000512200301c001c0c001c01999504254640b00c50352003102030940c4580464183d2109082c0341c0d000d401805008005919245940340600c845004054020038a0a5003600d540f070200021070341030340c0c41c001501191528507404d10010140080000843c000c060004090641c1c42400410b41c40000d060301410450840c01e096003000e429a001d02c0a100c064200340030456004415613042c1c80c0c01811540d040c1c3c010004c07d071000000d18001e000c441c02507410700d02c200010b8a80c4940124001d40488 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 141990224 1250 141988974 141988999
    0x3123b010903170c0a0b04031211072a080f1501090b0a0b1c0606030b150a1d030c18071209080403021002012d180b04020d0f02091005 59
    0x548010721103000c00307000070001a002100490061006040c1d08061074201d405c152203e84490035000701c00c4d502240090b000d03030030322040d00e6514000c1840c0312030714050403407401d04640d8410000301c00e812003003c5681030114401000341440c40071078000785800d0f41980c072203500140c6065154221030100004541c114030003c1025107013845880350a40c405030158900d907040c2900711440b50440151404460400410329901d12214028000145425180812000e085030100000000402c0b00d02c442c2600901c00306c03d40c964404200031181415070480944800d607071020074180009145e050b0b4010342c1c540e191041201c0054803452051a01d5624162880f02014000c000d469800c50050031303203c000d01041c009854404480b60713601550340000141101803401c0c041a02c4500d4109031510740072000e08c2c1c401c500881c05002c42d99041002e8480b960082a40d5002075958040d00c043d00400e2288019000c101410840024681d0024601000303441c12140840c00071361a801134a004001e01d1401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 141991474 1250 141990224 141990227
    0xc0304081c08040b04060e070f05040e151b04120318080601030804090507051303030320070b0a1d01020f0d2a05161a010302090c040b0403123b01 64
    0x2001c4240039520000291140c1e21141d40c0c0d000050801e4403120b03682e200164500d03104105020040896211009100340380900700001c03659121b501c8104c0d1b0b00140d05c0440c904241c0140f4589c40308841003200e0f1401816440307002d01e40216004441d0103014109080241900141b070804170052403425080616115104c5a80b116020b2000401e15801072009102149a541003103521208614010f0300301019001d1600036410250300c00c2c0c2c0829070312070a0510355403400e0a0040da01c0924a540b030324200d940c0e941d049024030300170b0034003c0140da24ad003884008031014201c91402c01460000795150300312145002200da00003c41c0c400f050385409410921400300c01c018800c80030004000d03180d400488941541c995004540c0c40b00003003014140000001c100c040249440d00c22210007030255819031051282d44680905070340210a0184010401c060410044801b96036000b003102100c03010050b001d1743c0c89080d11018100040c041d40c080c2c0e4515221a80c02e41c42d034800014a20050b8054100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 141992724 1250 141991474 141991513
    0x207030209150a080f0619090203190507080d0905120304030c03210c050c0112110d060f0b040510050a0909020c060a0b100e121005090601060201061e0e100b0c030408 73
    0x4980e001b42c000100048003015020025686882c42c03200c04100c0600945c0068244031030181c46c000c3d010040b502c0c69040c070404000e5038001d00f5041e0000c0c500c03851200c40240070604c61384141442400d00d00b2000521240a10940307000b194410051010300c1d80340d2400d4112006404030350794907007007010403806a13584200d0030440016088405003139031070384680044034154501d842401305140c54290042c1e019148000801e152841c00d0b10001d50f0604101203524840c00c1035000c503000c45c2047c032081c005a543c102d41070745103c4050914581e074200500c001e59556040390f1000280910208410036408404604680f003041c0507502006140e017040c040008030b6a100014200040c0d41e420251101d0400c2c0303207103c408081c280200c42c0ca85440101d81c40985108880000700390b082103004010380e503024080c48010300aa0081c2d100e4005116030040301400c080d2150203441402c410101c0e00155072680701c0c801401c103015000e07070b880c17216050300c90f0b50703501601c11603101d8070402ca901c1d40f58a04040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 141993974 1250 141992724 141992743
    0x30803010504020310080f010209180609010506071b060306170a11040b010c0b04050d081503030307030c030915150e01080606060306030f010c031e200a0207030209150a08 75
    0x5006411a420001408001d40004058212024140d20042204c03d07080140c0c0d450340040400142e0b03280d83d184244030781100040d9202640c425880b045c02065901c0c0c507501410b59406071086a2103800608003c5000c010817034000d5401d0306401e4002c10569416003143c82601e0402c90300010440032600c180303644800ba080e002d002091420384074601d0b440c0640101104100500d415107040581e900c4512040005880460302c5601100e01f09052940004009503c20005088032410300440804a600c0b48801841e02d010035642d1050710b10101d00a07480a00442d40041a154214007440340a500810591411803002030140340c1c0000c10030007694143d81a211004003510642e01c401042c8002608007515043d4540038484200b0a070321400d00c106042c500456402090079156a0500441040901c0c0f006034001d04160300380708448100b030b0741e07010361081c60310040d07942d809601002c80c10000a6003009501030b00c00010300800038040c40910340e440e00119081034880b81c3e2103c61a90342c50160 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 141995224 1250 141993974 141993983
    0x3060e100e160302010509040e030d1a03031908061c0308010e010801150b0a2c0a06030507050a0c1b0602010e010e0a051005040f02040e0d080a0209011b08040914090c0105030103 78
    0xb03034420300c015407040015258a1a014201007501142e4111180c116009074003085121aa1500e40d90340c9800c034840c0c3d0741d20305102900a5460400300c980e60058004005031b01c00140929040442d405403a00c02024034030303a03c4c1000c5115540703042e2900405a0704207100d2214070300c0780d0724000b02c1d9003a410300ca01822003410156010b8a14074241803800507030007141200f0b00307020030821304211800c103110400c81c080107008800400c50748400300f04010120143c12480c1054a000100300c07850750031800b1141c40204e0b506041070282c1c142c0c07070961988032018075000d4a240700f08600003805a015040044100003d00c024803400d000201010380e182d10b000c2c4054656800f41400a42800c0e407036111542290099110403513643c60f42d00490191440340070b200406a000d011700e0159240d202c030000d504000801020b52401c100100001d0012103660340070010814480c1200301001415400c8400030003801c00c041c48503418800901660000458444429020341c8500501c6036200e034080700e060380d910 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 141996474 1250 141995224 141995263
    0x2c0108150a060f06170c0301031a04020f030f030408010e030307080f09030403020a0311130605030309101209050a0b010e0c030a180c0e01090b04020f0909090703060e100e 75
    0x41085044a040014000710751950340d0b400c020980b42d20401e808400b60040b900c40340704440c40480000700460300200728450a800c00e000500010345407007242c0e150040c119076124941c0d22540000303000302c0d002c03588850b8940710721007442d400c0000100241040b0b0700040001c01c24081001e130501d842e888100c80120000300d030a0000b480341d0b004c0c6404107400200040c104d07402e06450f6030109188a09a4000346e80b4600c1090030601c183c5000494000601010340050107441e1030302001c25524003e915416209020300302403042035520401d0300c2c8400b50a40c640a010030442810640d442d0009281c0550740d04610070b0000c01c10706090304c500c0c2d005507604001c052860f6070b0190300100500303001d80f08005c24008103590002050901174440b010f0a0350280e01003c81d49081c409808a40c10b0840850059006008484e0f02c900e800d0123980e07001b0341c203a0b925030540c1e6981c1380040c2002003c0d040100046d1504501c401c582c81c3c00501250641d11060040060310021400b65070f42d0300340700c244006c0b0f4491 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 141997724 1250 141996474 141996493
    0x612040201081305071d09011e0506010c06090b0105010f110d0305040c150809060901110301030204020901140c010507020c0a140d021f030e070501090b040b030c04030605012c0108 79
    0x452800ba903400741d10b480c0c003520b10403081c0c0e85050030b04000c1d40c810010046480c61811000041c00c48098010305400b0003002485c41c4000c070400d0503501d182920001d01d56a20005403d640601610f03800280e0040d410441503030382e40f411480f444400c1c01498000350b0100c3e07014044034014076040180c0310404004210803400c107a401c03009004000c00071601d4136000e01002035004040b10110803581c9650b2500c001c240b42c045102864201d000742905d2130ba0b0b041070a0b40c0c50004a900841e815a901910302581c0e6001220040c3c074864048c106c0c002c15408000340032055040194800d0340150410f81c20340380c03c0190300c8200401c81c55140907403c051402440f61603050700e041404d9945040c40600901a484d002c2e0140d5000d0400c5d540c0e40402003920f40d0b503514011300c000e1118078003030f28003405c10010107800d150102090b40110300030310040c8900000419a251004c4050782c00a50740034000344115a1a03400e40404030743c0c000b001c04600d00c800d01c0d00d41401242c080d041416a080d00008000034075 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 141998974 1250 141997724 141997727
    0x601050316090c050d090308061e1509041b2319030903030e0303090d02070b030708220b010308040e060a0612021804090b04031e0c080c010f05010e01140612040201 72
    0x1411100702050002c00c100c60005d042007070107201010b6000340c95030f40840c42c2140038080040d03810304045074500b84245608801c0d940340d003a48170f419010a80b039252030700516000f02f0000c0c854040c04800041d13614515260443d4821030843e003100c0c200b05503d02e03050001f145903449024030049901014200141014200d109034070162101e402460049464a84090340c141944c2c000c1c1c803000f2240d08440301c0c8035020386e0104400c2c401440c0f10600300f89140b80020000304404400b0302280c0d465040440c00d014100b040300d0410804a41200301300304656501d1800742e00c140d206200d0b41181807042e07030020710383d45002110a01281c1c0b0701e0b20707500d0051041c1c0e10084000d62010f0004c1201e402c1c00910b5000a40784d92043c080040d12a1040410703c4c1060b080160030340000d101401c4202c50149510021a5031001a0340c01c980c1c0e000c00426218ad407085041405860548155240d0350b151500000700820b03516141c03812a0310050b40e200c0b06102103014090381e8810545078000c10310140000c64010f5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 142000224 1250 141998974 141998981
    0x1d03131509030510240f0603060e060a0512100204091e020a02060609060103140406020901031404030f080a0e032208010905030f070f0804030602130e01180e01020c0d050c060105031609 81
    0x20b00d543c50304c540040d0400f0164172025545900071399580e54404100340920758040c800c0201070065490302e0602032600c07a000413a1100580110ba000f5960140d0f0350207010410801c204208003062000d6454546490512005042079a07031084040220030340340c1b210070784074801c4a184004036805070041d90342c3d8800740144600040c001604150b41c401021035020901d484080c042e500c20100542d41c0d500400006090300e1200620052a00d18a4148400280c00800e005000d5411707041c000c801d543e1f504025001404100d201c49682e0000254403040c0b244511000c2e0014800b6002c00c41049481e400b00c182216680d103c010102e600c20809040401343c0b18000d4545030f80308001c240c002c00607540d14041e982d000350340101e030300795000b0505240d03550130a15094058040301403207100c250304d0a00c003906d8020341d030404500c4640d035070003c3c1c00c82010290100c078405403400040f940c000400000c010410350201e0840700d02070044c58000b03d40c42c540400c03081d03041d40c42d6450703090219040c8003400004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 142001474 1250 142000224 142000241
    0x2010206070e1201090804031b0f0306050403020c0d05010c08091b010c02060702040c0207060305090a0206070b090703020415050103200715090b0a020c0c040e101d03131509030510 79
    0x2c024000100b0041100074055074182d507206c0e000b490703200ea1551405440c01d4451002c099801000c0074814004c0b449a01207400881303420100114080e221030400341d0400e605114040d40100a8030390500030300a0540012520400950340c0120313640c0c40b01042c13601d4100c8030b10400d031030310707554400399030558071811410b881c0741d00040c030303542c038105c80bd80c005400c90302c5a41c00500580c0122a04100264251294681c4044038a0141000100e1a40051210300c00c1d0704000382350000460128903030345070410045015541c0a4010084200b0788004541d401100c1d10400d40064280304280302c24082e219601c04400200901c950304041072582d4102c410628180d0041c06140c0d20030044004c00c40018000340180001d24006943e14040050310381482a00d1160a010303500704650448015400034400202000030400000c022100f03229030340c8010101c101c9103017a0301c004242e0b14080d07075000e9030030001c641208000001500745440300751038400251001425036040303102403039005501c0307802c81941e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 142002724 1250 142001474 142001479
    0x50a031a03070602070e010603020a090e15090c030a0c02010204080601030212031c0218030c090f060402090d050606010e0108040308010e0c04090c030b010212090a0308071103030307020c0405010e0402010206070e 93
    0x111940d042000c0391074400700f94810f0005a01c555000c102c810090701e0090f000d04600d2405515062240c000a40860198030520340304100c80700c0001c0c041c1090f032003c156481c0c8010b00e8850103061030f852104050300207640c05440d0358600300c0005031042c01403080394102c401c0c8102030011a0f00e15020040e00305000182c85080380802c110f20201c9454034150260902e038021401a11101807021041120290040207402a80010100303100b903a150038050b50701581030002840d2560302c05010401a02442c8601c0e90003900d000e003c4001c1007008180c4620079002a82c42c002c4111301d0704011688110250740141c0480c80020044c8002580791044d103502079030800c4000d00c0c207551819450700b15559072581d100020351700c2c0b140342d500d980c0c180444506120400011400c00b850000012510344a0b44002018054001943d030100001506541d882c003500a003980d031a41f421002c081c0d1030f070b0480314030280718038a00000411140712001c1c40c0c50069070180c1c001e101d103985202d001d03101c0382501c40c026503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 142003974 1250 142002724 142002761
    0x110f030102090a030b1603060605090d02130207030509130b0d110109030b0903070b09010b0102070b1c0c1805040204031a040c0b0a050403030201051005100f0c0f12110d050a03 77
    0x38240d207410400e0002144a481c1c600e011b864000340e01d06601058101c4201013504010040024660100545200c40c0040b04d64580441c00c2d4400184040001c1a0b10f200d810700100f44c1a040c190080060101500c00392a40b43d05000300941c40011119030706011680070101d5044a408a507040603070050000c03045c189a102662a52117484080404448054003a800098120b040054500b030190300010204002d000c030340c0f20580081c1d11013806000b6403103ca0360110f4020140b1506c80c0c002030104001100c1004041450140105080342d4154600034501001c00c000420341401c1c8221421a03811030035651824021044001c01c52002900070344101e0381d6284d011482d040014008c18007030f401a244c00e0780d51455403130081e003503890003030445600750b0344e42100704581c0c1c40f81d4451000480b032500c4c0c4101d0790a045d607010b50309a00200d6001d01542c01500b503040401c0130483e202e030034600d0117469855002021052650760b0308900640032001420034001170b54414000c0c1c00c00e50541d000c1c02c039487c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 142005224 1250 142003974 142003987
    0x3070f061202091e0f01110706050a020319020303010f0e041101110c0a1403010e01050103050a0b1905070e0f0616020910090905010501090b01050a0f20030a0306060e0a03110f030102 80
    0x9484c840030050000703203000a5407400c8a140f6041c05401a9a002030810502141c02c01498984410191244109000000500c07844503442401240e11404c000c2141d00708500c40314500135941d4000340130720003400c1580d260119140800c400098480d650242c1d494072101c4c0764000442d140030b14901f00c04440d02c60f00c4400030349941c40318081c001801500b6030003030000688104041c02d60f69005c00743d20a90b45010014008100c0c0842c0055031140c00c818000c910741c840038654895410401c820710b02c060f1812043c4048681d000701c4803010200304991280d80051240c2c10000b1a110b12900b0b262034030f081002d60801410130038002984981c9408103048415610b0030b180059803d0010100c0382655190010f012501d420b104040d410f1a083c6407260400010030070141100c90070784000d03000d100c0c0c0c01c00c039901c440801c0100040b040700d0403400d61b030b100c012101c405409840c10307014810101c0c5801a1004150a00040c8881100c1e003061a42c0c820094210511280070398262581d90155000c1024 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 142006474 1250 142005224 142005229
    0x3020702061615150605040b070305070b1006031a06031302030304260607030203010e04060e0718020a0807140703080406180c06020606010311070b13050d1d03070f06120209 76
    0x2d86a04034010240652540c3c285102e04003281c180d10003038100001c1c40d00e4148003d80d07000066406440650794840d41d070701c031141410b45084c05000e1000301005071050820000c400184070324411125079131014003001c10b100424134800c08482840607000b000134400164a0075a1f0b10703040d042c11f0f0003e01581e203060740b0f44091070742e40884480e0865544403240050007954500b082000e600c00c0300381c941181154101010f070540380202400240c4420340704d0b01130082104040c84250000c084086211030f1150788804444003940101c0611400b1500d43c1001a00ea58007544000504050b4804c0d4945403144550f03080e5500c200142080e00d02564a00c540042109004800d4440f00c4c01050029059894000c2c000c0c41c02000400b000d04043c10034041c0500d01c100070b4103562071654014a0782070039695008105040030400000034204e80f184c4484812815080b003104076421440304540c0c0001c0010300c0030306554a05c4c900c511010250464002c00096116425030f1f050f0003040348002d864035510400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 142007724 1250 142006474 142006507
    0x918100306150501200604080319020a0e031c0e040e1204080106051512010314150c0306040e03031b0313081210090509060601050c01021317060112120302070206 71
    0xb6004500b0459800b40003d603001544010080c1ca0410441c030300020308254240c940c036024100a12408004c800325052418121500e030070505412011911644c45281c020030154000d031071240070340a0780d035800c0c90300f1000e81100303d01c050301600e0700c0381401464802d0100a1105500803000c40c09480c54000069823400000d000821803030b00003140542c20141081a82e818001c500025044104440b00300c6000304000141141d80244148114506451080d42040540c4510a0203035240004000006c407a030000385005030402e8404110340d414000d0060740e648000da50040030200f51021341c10900b0711450082d6405502c07140d01100c460f0541da0743c0241c0e6002500c0400e90b0002510800000000384403110b0028250b0200910403400c0143e407a43d21008013030000c604010f0005500c101c880d01c250101c5154891240c090502c00396580c0750005050746181080c0a1800750f1000083d52800240081d00300c243c00c4039404004064641c001e40c000d5101080803038100c0c02c20700c41c056034001c07880c0703 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 142008974 1250 142007724 142007741
    0x70905010e010608070813061e0212040b01171906091205040e06040c0e0405061c0c050f04020f040e04020d02040501150f02030a05040b030604020702060c0304080f01020918100306 79
    0xc214506035051000c0130304600303c010320400402c00c002c0d04002140400b10161514035400810011b070a003c02d00400340410307891035950019030700014a2514602c0b0303800e50284150b0280004900507620380300c012415a01004401c021503214204516441c854640c0000e00684108400519031307410307640d03580c0b0640300001584c010540214042000c506804045580100101c1c1c003080007502022003d0001941c5500181c01a80c0e607134000340e5152107400560880648040070f2118800300c5191423801c40d503190080030302403951461003808034180740c000d84400e000d0200040341085d060006004c1251001041030340d016120301c07900c0c03000d600c884c81420301801020785c0c11000401c98502c0074003415814030700d020440d0300801181442c164440152400d40d140ea0b40d02554036256040014082e001309100039610050004207140441d0b80040101f0845230045c098403245807860108174201d0040310318081d0410001070314055402c16480b02107603c522010511b00480c0d07102e407035000c05c40d5440d9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 142010224 1250 142008974 142008989
    0x812160f0f030f1403130302010b0909030a1202070803130c0504050c0a0f080c0a1b02060c0a0201020d05040e04030c0201050c010507020c0f09010807060c05031603030f06050409051e07090501 84
    0x10071410305140c0d200f961094285041d0601c0144c200d0012001c2c3d10307910004200d017400301300050100c800c06200703400c070380b1400c000280f001246050442166440e0741c4001c45101c085443c500d078824007034400b8026a0319058103d01d085046644200d401e8400d144039540480300203103462404103a50b134440c8559400b40400303140d400e898014090020b081241c20202100600c0148820021402070040c00c8a1008a6a1410382c03e11a5142c06c810704110340b20b60029400313280801c0081800f200000c2d000b0110303000340e0854032840c081d9481a030b1b20344120702902c021080d203000024082401885404603640c418500689082c03008a0301c1800c583d01951490010380040c12808480d241003900107210420441e2924010752421503410b0b0341e4040c5108600510107400e010101780701060042d035214000d10303010916040a21f14000303000380008407220a16500e01500803c5604261180c1500c1c1e030390103001002e221a01510313500401e419103a03088841d109030782340070503842002d01401d0700030f0151 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 142011474 1250 142010224 142010243
    0x131e0b010302040501062c0a080307050303090d09030c0515070204021b100c0c060c1103030406050106120b09040f060b1005090f0f03070b03060d0c08060709060206010812160f 77
    0x1144100004c3d60010791001c401c0000210758000c2440700407410304100c01c01d0a500c480243c0c4140d000c01c0d0305501130fa0245a107400041044030901c100880110711a500d1007003912024041084152803140b00e0f0301000c1c1c0f008100460900c450700f00b0309200c40c45a1030f17641d51642009140d80c0040c0a0360b219a00840b40c0050404120203610010030110b403c052202909200b0040d03100401840c1e070461079006440c9a80b58841ca074140c50103810300f00c00011000c01a207a03289842e0801d08040d040a03c1128001100c000700c2e02c880004170321511920900040094802d52196241c100a900c3c0c1501d003525155601c80141c4026a5400316500f00c002058444548442c1a030040126000300d000700f0f01d000d01e6a41d440300c401c641e4082242016600c03140001600d030b803911004a141030780f00ca40018070a0f0100000030074014800188144600403960710f542000d80c42e544c08a80702d51083c4201c182c1603103e50109000300e50711002404501a48054544a140720740d00c540020618485d01501c8a460 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 142012724 1250 142011474 142011479
    0x3050709230f1e060d0b03160f050f06040b0903070f15020114090a08030901150905180d0801050409021318031e0c021002100e06071214131e0b01 64
    0x10309096001d142c560841d18003014211003905060003604a031600740c80b90703c0000d1911403a040035445006041400340031149406400620b50f0200c1d6410700079042c580c1410500002c191506009292420f4005861301341402c2c42c05c00751080c182c100045a95140c02071007004036800c1031401e0110000c003960000088000c164610190840d61651200c01048100d41c00300540c902d400200c0d542d12943c0550035a41c2d942c0d078019090f00500310340380b0820b003505000c0b20001e00480d445e08114043c1040c003013000d1000e02710f1403489582d584041d01a20120302d10400401c554035007039001c1514103001070704e850300702c01503211000304482e01c0e500001400ca44000710501031691000507503442103603410868601580080b409002884101002031103200101000d148840c0309000d442c0d000c1311403013400c0c4507076004a4000e80d04c4200403614000000c2c1007071001c0c0c141c012140151491101c1075040c0b034440e80c584c0d641003030190008040564403044046031000204003059000d0320704034080c0002c0d120030750 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 142013974 1250 142012724 142012729
    0x7080c0402160f030305150607020a0611070b2d030f040b090a06020d1508070609051c081207030b0a0608010510030207080f030103020f0402040e19060b0408100e19030305070923 78
    0x8000311400d024280a01c00274005071114207411055640c20b0620079500c040c07a40342070b45803481a4000804501010404039004510740f20b40098030905101744c80c1c072580342d5088240c82c9000880d1004401c0448070049030110745252506c80e080720f144415030b01059001d0321642d040e0382c04510408a1590303a846424086828010200f02829484018000031840c0400052001d1068002c083c40380b0380e146800c02700c0d10f900d480700b070b10175507400340c40b00ba240c480310480c03000000d80441e03468010906094980e0410b1802c0e60b04030b800c6e500306032140c000c036034244400d00203a000340300188018990f08010003408038000394003070042c0310840d9101c59505c0d0b05610512005102d50000c0e9409a40148820301c0169500303800d8561000980d4043e0b10180401c16994015180680c03155000d0719000a01040c50207022079980b5100602d143c00384052241541c510355100c014045003500004404901000070740710390046604040246820040c00d9180d041d161012183c0c1c0fa210700c0e010a240030801c0320750 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 142015224 1250 142013974 142014001
    0x8150912070308040303020310090603030507050d0e0a090b030f010230040804060507020120010b21070e0a0b0405010b0a020d020d0206150a0e0a02130807080c0402160f030305 77
    0x8004021664286078242e076010342180301c081c1000b0141500400042c100c0c41c02d4000d014002c100e00141444290766904018040368000c0ea8150303035500695010705c00e00d500607440b45a001c1005001c00d9185480c200411000701482e000309541400740302d40e0b003011500240041e0501c02c1d1200e807804604418205903c0d01c0d01c508018014118a4040410001c26010000e0f5011a031080c20825559940741c40104c07142c1904515035103100e003921713801c0e034a619015413049503c410156004600c0c410218244d40303250070840c1020200380d0000c0018000c02c2c0702251080d4000b006400045242030007a80054140e4100342c005000342e400100360381c094540d040103003100080003800a440d0024103420020745400009001c1030b00100014540c015a84a8980f454020442c16001c4111820090302420281d0301c450354500b0100c0543c800420071a20109462003140c101d04018000b00320300c0414400a500490718003415000409400e0010418140c450b15205109640008440c9006040e402c2c58 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 142016474 1250 142015224 142015243
    0x30503090d0302031b031b0f0a1101051201061d040207120e0a030b0406021e0702030a170c010204090204060e06030106210b031c03180c05040504210203090301060b07081b07081509 79
    0x10b40c0101d405200142003c20501d1134103401458089105101c6001691f0b24070540d181080c0e01c026503c0005001c0c1c0d48520804d01c0040c1d40d416006500700c409047080243c0c0251400904262101da080f000401c1c001c442502c620700024201495555603a140d036030805004990507610250001039260302c0313100345201c0c00c0315910b400c007000341407140303540219590707821451005110124052030140c805d043e19003500c440070280c0e0001d5585549030400500a500903214880104000b4140b507540e91805c641982e05841c86e80c1c3d150b4a504000c000c2051601106e10102c2e0807155803440e0000850f2000e11484084001c0b0003500f030000c900740d810043c100ca6410003034010b25071050f43c520340080e2548510340d00701e500803240840d1944490414a004449103c80164540610242d8041c2d40340c010018100c0f02008038000c0100903a9020b40200608c030319034004118000400c07110390301d54281900100c8000707251040b200c40c2521803c1192600c41108040d080d021100400c0198944081003801c42 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 142017724 1250 142016474 142016527
    0x901090608040f0609060e0a05160e16230a0503060f040b031002030907050909061902160f0c091811030123040614040c090b040501030503090d0302031b03 68
    0x400e8541038a0303100000031090310044c8215101c0e5480c0003400a80d41003050190381c81d03c00d4a0709500507141c4603548206031094003121501080001809049910180744180c000450804504a198604a410903001e0640442d20012200114569003e43c1d000c0c10030b0348050b0301d89a03903c1c28010200a5103d02c001e1049200d541400c0c45040c0a48022400047c00c11f4a4040580ca0303440c1c403002141403c1e459006035411101c0d140801058034800a1010b01465220000b2400054180850410391007407820414082c40200a0140050001c1e5529006240104680c00040d502e9101c05026122500c1c550710610901c0e81c60042440018401240c1c01c1c0e80c214000c114043c41c00c90181c1d11421120703c14000712400300c00060501645401c0b1741e00f4102c2c1081c5400c010325080c6000c4891429038011000c0551074001a110581080e05c582c9042c1c85e0000000e6040c540d040c2c041111000c1800710480460000340003120410300f0422108800d1b03100040034603160381c0d1192500010115401000c40c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 142018974 1250 142017724 142017737
    0x71203020d0b030f0709020a050408060c070308090a030e0f03030d0e060a0b01031a01030b0d0f030f17100e07020102041707050301110406050f070f0b0405100c050405010519210209010906 82
    0x4d9448000600604a551803600940c94428264041d10a40529400140140100030400ca4240403083c02030203203500c2612030041b542c4a6155541c5e9880e90304000801150448000101501d454199103e501c00014122441c240e440d820f20070580e004515440255804034003030210460b2103000d00400400286003c002140e0050f01c5404a0317000e4000b0035040c5650b070391410340c040e00c44000f140d0000e03820400344e9000301c1503894010448110340580d0350018550f41052155460b242c40e82a018210306071442d00b0b410b08100a8110082e0094215030075590f0806c000514076101100d02c550581801d0b0203821102c0c40c0105150035100d0800c2c1907641c4240406c401e002168010b0207440706005107503042c03901e400d118a8003188483c41040064400d00c074100810081140006400708000542102405a4400c00c1002d0741c040c01103004040c045a0140000c00c02d0510fa80800c40d20452940b0340740250040740300002801d9144000e1103500b0580004004e2841e507049111900184010315242 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 142020224 1250 142018974 142018993
    0x403021002180d0201090f0f09050606040b0703030c021e0f10020c070b070302190803161e0e0a1d040606050307030c050919020417120909130305071203020d0b03 71
    0x80b14001d00039941441680f5103031a01d803d6901c0358030640080c00100c601e0040c081c1e111541078100b90501c1c4a801c4040d81008000340c0c082c05c0c203406031011501070344403c2e804c01c95247d80c01e80107400041190000c42c071855290700307406260708409c00f800302030395000303024805100f50143e41030190003213084000c07a004000d080354515000482d81c00721290010116100c041504d8100d08105100901d03007000e00d1001c45038000c0c481d6200c01103000384038080141c850b03d03030f081d00e0540d0741d90340c040c900d114402c1e40c3c0c2d011901024002c40201c0b88081000703003c001c410352203150401c1030341c41c80c43c5501d01205c040b104010070040540304100160104800074001c40385180c0c0d4a00070090a40a01c40c0a4114940130441d00b003c801e00d41c2c400c0d0240b5910964640d521110382701e040408640c250005481120440d110850b084011100c82e00d801514000555a846030400450342100300c007101004820400030f0042008012081140310180da00941c1c0c1e4a040354400742a200700390501c80c070a07002036401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 142021474 1250 142020224 142020247
    0x61302010c23010c030507030f090201050913090f0501020910140d0f0209120c1c0b0a02030601140f0910050a0801140102011d01060e01230108060d05010e01050403021002 75
    0x4450074180e011000000042c07072202101d2101c070140280710040c2d0f0a00480412154040d0031662103040c59035401c0083c0802d500c0124203540c10084040d02050040050b4402c50030009000c00c6003000c4c6c52070101c0c2044550303503550540a144201901e0340e075400705c0c05248610b0000e07980076403e207941c90400d6038070360a10101c80e541d115510f694500d139030f550b544003da0000d03941c054900c2e8200003040c0140c45c503500e14403280c55030390550f040b51003581c00c10610420701e54400b20715104c443d0055421502603640b404040000d620140410741403000e032000c0700001800038001801070001e032290280c0ca0b03900710000d02c0b0340300088808031814420180300344c2c2d00c80c0707500019050444000e0304030000410741e0080140c0c010241210841280301c0300030100a429070054010b4002c0f16040c003089820baaa03115911004070300b000c1609070380d130701c0601c040c02041c0d172140000300d4104400a100c1c0c1154007003030f03584508503040c010b904405a5100e004010516405001041e80e503400c0b08011340c40e003040d0006 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 142022724 1250 142021474 142021487
    0xf03030e0d1103010c082a0306062104030302041d0103110d020f060f070506060102010902010207060f0201061d0702060703150e1009020309030310060507020f22110c06130201 77
    0x14480c01881000300d0301003070141e11002c6003644800078000f046010504076004242150440e0260a810701d50018592950381e41c2018000c100c00e0340f003142c1e045448a004110490b0320041401004500c01d244180005100202544c0180d00c04d407001641c541c505240b050040014041040400c40d103040108042038400c5003044007458201e8940000d0340c0b0a00c0000d4100d5007101500c0c0d0003010109207803410040e048000c0c21700074007403411191706076a0030004a00740c92180c1002801030300061010011240a034841d031520f1042400040341185d125942d045882c661500c0300e00b44c5031203900c14007448580520080b90070a04500d02800358844e5001c45045040c202d10441e05c0e082c070b16000003840d5020540509002d00b1402e03800755035170b080803107401b5038a4000362980d07140d41c1d40c1e00b00006421402082240d5010741e019104059400c500780c10000301542000031042d0704d0f44030741d207565014040c5200312944440301d0402c0a4030742d4030001c0000e140040003820400c0003d40b0a80c3d990240c1e801c0701 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 142023974 1250 142022724 142022747
    0x140f0a0804060c0813141c120b0a08030702010c0302010b0603040c18110f07020301060b031005150a14090d0215040614032a0c150105010806061201061d03070b0403020a0f0303 77
    0x1020126030b02c4c1540d07015498021b0108201d101c0e81141406034420a0707000c41100745901c508d42c0d040c0a002000b00401a400700f981c41502150740c4200050001540034120800041d400780c00006107025036000400c0450b0f101301d034100c0d00901071450074480c1401080380c0d40740660030540100112100400c01c1e440700e04c105442c0c02c070104408a10502156000d4011602800413500c4160b100d0a080000303103400309460259921407500d0b00f548545a2040e00706603a9010030382e544140130f01c01200c003041000e91110100541008000d107403c00036888004907d034000e0380d81c4900650b04da1070302900410f8401c071000400c4803c002003051114100c00852a195105411308030f40001d00005040400359108440e0381c5846030040b031080d03189151091004034100d035001c0c0c941c03000907503c0c1303020084144644044501c1d06c2c1841e000604c680c6100c1c066503515503100890300f10200032241d00091808050741d1240c2035804002400b03000b141480c0f9202c00c000c00b00b810f1814230050556030042c040c1103116 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 142025224 1250 142023974 142023983
    0x5010e060906042f030609010e160c02040902060318070501030903050904020310030c08030408010606030509030a0c050f1b100207060c060c051c050402010e03060601020d140f0a0804060c0813 84
    0xc2d500714540b01c0101212049044c080355030b80c80c82c13148140562446800403903950344511886400002e000c403088120900c9051000300f191101180540c080c2c404c0751400c3c000345c0c0c000742d58140f6400181c46e504002c60041100d5400c14142e19070304804285011051742010b41054140702d440701c0001e07003040940716401002c44001d81c0f81d50341c444040c1d03009001b07907002400400c00a00c0000d0001c0300880280141c800e20402031007a50703116170040d01074400945441c5a194405c0041640c10303841076000111991003442079501c1c0c1e050540030035181c842c2c4240320514022400c52013464074900900f0580b2000c030240094049685428005091902224400741c5810b88035071542e5922817050049500c020a502c607a100480c0c003541805004210442d0124049000c010190361103180004441d07124441c164020b05611144000c01c030b0f410071401e80606001607080c0107883d0b12a00b08405498252450b948a610781d01d081e04010b411784882141c1c110038041d0100c01d0264294141c0340121009400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 142026474 1250 142025224 142025231
    0x307051b1c03050c1608130e0103030903060c0c02060f04091d07060f020307050d030b010e0a151112190f05070302030307110f011b0e09090307030c030203070605100905010e06090604 80
    0x601c03201c0c942c00c3c0710380c54411500617421943d0340200296a40548000c49007014040b40c15a1aa40c50602255003800050f02064000204000180b45074202c88111986403800c612110119400300e0a2504125624040c001d000b090501c041c0c50b19101d250015030040031b4905803800c7ca03203041030700c0307003224050704d070401c0060603e0a0000d0300800c101c5981c1c0340d00c2812503d60054081000700148000b080141c0040c03100154100c092801c20f071400150744582d100b00c02c0e0403001c403806072005058203100484500680060b95485140f0801404ca540c0c181e40415000c5035440d43c00400d031055146070038060102c01d020040100703a0000c2600c1d404003041c1041805201d030661618600f1000d111050721641c20070507a0a410b00d078803505d14140815a445154218000344108205080b00700c41c2207242c3da2040c40704101080c418a0840c00260203801506c0c98070150740c8940d4166001191580c0c00307000c1210082119900e940f08250041c06100308100e45030803e071002444070759001c1d00c41c91041d40c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 142027724 1250 142026474 142026481
    0x2a050a0c091b0905060f0703021e010f0c03051501080a0f180b07050c1009030908010f0f0b03150411011103040303170705030f0f070207090c080603010e0601030201090303120f020307051b1c0305 85
    0x8102c0c1d44081e2b00400000501c0f0089544098040c0402c40e400901c514200a1000e860500a0065501950450703991452407100d040044071000c000070042200140c8031024654440400e01c0f49407841f120b800c96080c020286800c0c0000810406001da500b0050204131980f00031202003203544440003140004941560203080441e9110656003012196500c0c180c100c40445000c8d601c03018070b480f205481403160186407401c140e100d00e4400c01040e80408003800240c00160010038045a0840504089011a6820b020300e4a035030020b800c1200410b00001ea21910b640040701d44907405107042ca0420319519000055071000304001e4040c280b0a8010f4000c213200900a0100201600607a01c2c03c0103500c980e041e00503c8480c3c181ea03541e0103035190030380a800207000410103d06a0390103031980c030605842d50f0340846e10925040e6008002540e250b04400c10b540c0301d4002540a91b01c1d95480580f1403c0711020703050309403c05025500307958000113400d14070452607801000030156504001560350b8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 142028974 1250 142027724 142027727
    0xb0405070308031e0708091506061306051c020f09060901030b3007031106030a110406120b090610030c05070b04050303040308072a050a0c091b0905060f0703 69
    0x11100e070402040000d010040180c0b441074119072048043d06010b00c2d11068440da0415101c1070001e6840104a4200501e50580b040007050020341201015120b18500102c0348083c0384800c24a80202000500002d07181504141d900481001c8007031204046151020003240c40340c1c284a480c0d0724a006d404c01150300c0d49640c0c040d510844e0f8656024001c080c15003d10f844002500401003002c48400039202c8246200c403c0000d203950960364030110b40440800e040c1c041000d0350704010b00c02210592140512841d08032600c01800080106858084420701024030600aa91403521500d001c0d0405400700662030b514500000d0b4103500500300010b00c0e50401c4800c030b4041c4201c00e40038240e0b45d1001d090000b0000d00100440c800c500940d22001d203034031224400c5132000c44070055560305080000c40d440051490700c0340d0900051040086a40d44c801070382c0c850b14112401d0384034841440d62000c0c0010b0301c1e1100c2c2d400c445a14007078685400c9143c184030026005009114003141e620101092240030075 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 142030224 1250 142028974 142028983
    0x6090501020d0501080309035802060609060f1509010903020307030803040308060a080c011b060c0306060e01030204050a090e010b13151211040f11070c1508130b0405 73
    0x40c0311180c81400291703112602c80781d40e50b10038166240a803003103c1004100009100c81c0e480c0307040e40400b621400c000040a1412410303a46090b0103071448040c0080100421643c0351aa9030301c0c0c0c150080c03d464609041008100000146020b01548105052119036a142850001c0c0740da0081c80d100d490b071a107940101e613002e2050b0002034061107000340c0030062011100c0952b2050b40320303a8441b20306aa4400501802004a201d45625a03105036041e8041c0d40c01050060f28004410126030351131481921024207407000d0140400100350348503020300c000d542c0644c1c4032661907000e0a05610381498030021451162542c4100340c0d00503a503641c12074034082e013904100c1400344014104404084801c40c554001c210110324006c40c00d0031820f000031002d5600501d00c8007a034100c0e2418a90903e04400c0c40007600042d14903000c007550345c401da007800e104140041c02031940030300e6913002400e0408002c4e10300e01c849181c443e824401c201c02005401801e4a804032034a42d40100d0b031130100e80344d0f481c009180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 142031474 1250 142030224 142030237
    0xb0c040f0b070c050a080604080c1006150207050603091f020405150d051b070308040c0312090914090706140405030634050d021608070f0302070608090a0609050102 72
    0x3003201600005000c409640107080e156029821418040e9680c00400181003154030503219107402240010300803030b08041c0030707000c41c2c403140050b596a451401441002c646441d08040030240c0300800806600d0340c104103c0000d40010340d070091450500416441e510450003920350468400a081180e03541e20381d4050b07800402c0003801c9800d800d440320040e000c0c16044414a824094506000101c8000040303401c81852044040d005142450f1034404640c00c2c0d034010001c0e2022810b100340080010328100621580c0c10b010b60341d5941d9030781490301050541c2c18003005100e40d820381d081031000340c00d1701192040c101e414038100340070000c2801c80000b44600443d84804c1e418098101045424460b9100a11040451074a201d416246a00302c02ca840d8088009090003e402442100040c0410394014402a551000d0444580b8101da91300f005503440b2078012030714074004a49083c105601007010700003800280c01c00c11000d1510541940c5c1da43d98400001c0c2c5110f4a0b8014041072000a5044428 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 142032724 1250 142031474 142031489
    0x9050303060f21010e0609011b0f17070207080c014407080601110105070212030a0603170a030b0102070e040b040602040b0d06050102070803091c06060512071d01080303040b0c04 78
    0x3c4040d280001907000b421041c50f0b0700914080c078000140e41ca01c2c107216070700e07120744200d00d10454095000c0e070072101d0b26501440d010900003016142c07141443c0b5956541d202c0c040660007044030324100308459080c04180081da9040c440420100b411108a011000c15461410b0b2526003101015884035444041e41007425101501c4000074044c803981c0c050709140c1f20755000e03280c100000b41c401a405003260707001c45450006801500b0008030b42c01d136610055410507844d0102155568494548803071001007401040e400380720004182c2c2e03100e40c060140c0c80c480d200034005402c50528100c0740c03400c0108010300c010040c140c254000b9080140719070503a0084c04071400c0035a203602c3c0d8050700c1e000030040b600400c0e025208800d8005070003503001040b655251009031101d9610022000c44065040780b15508403a103070b0702c84d0000300e017544440341c03080c81002040b00140b20451801650809005125510101383d00e07040006110004000007140d03040703907100c1490410740d40c2c1c0f2000c0d68102d0165801100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 142033974 1250 142032724 142032769
    0xb0906040b0d0b0a0507020607050414090403030f0e0601030b061c060207080d0e0a05120906042102040c0503040605060307061e020f06071205100f0501080a06030b0a02030412020109050303060f 85
    0x1d070b00c0403540e003c280f207881b05400319a22038a801c0c809a40e130b170003244540784080d0584010b52880e42070000701681c206101e4200454040c0014071030b034055940b5030010f00c60950003200108240702000c0309c0c05400200a075a0340540c0c044941000380b01c03c503100000350010f030300081c440040003514400c0714070044c0c00201c20070403590480071550b25050129002d031072920816420b070f070303400486030200c602428000300010719181c54500904600c4001d01c07070102074446072280400158446008142080045980e10f944e00d14051500d40d0849002a01650090780721800c203000c04c0381c103d4071162204d40910001840300c0a146d0301203103003071820704d800d14141c0200418441440e8011078806041c56032080b040c801541c821066211494580c450f20034080b601910401995000d408841c0d00000a00400f098642d00c030b8070341c018034080a130361418009a001041209000e603039034442c4920740071413000340b184c05c0307064495a640c2c0c0806004030384074034030030b4052083d20b540351203980300381c04101c07013004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 142035224 1250 142033974 142033981
    0xf0f0f0618150a030e0c010f0c05071e180501030b01120f0c08010e070801090c062102180a050315040213060909050a03020607020303010f06081308070b04020f040b0906040b0d0b 78
    0x3402d42c2c000b518070201180c1024030b036100351400405c00d480f03482010783d42c11070b50f46400003049400c1d03020070700e003a2070a028000003c40c101d020007104000603c110170403038041a1400650720400e074803d140d404010b81c038000050000425000c1001e045410715030990280210a040084a800d001d0b04020200d892061002074041011340100b03501d0f450a2081d152196580c4011030b090f54880c000090526500b00d50600c0240c0c0120711020000c1c807040c002c0340004032085044002c0b68080c803204d0f1030300003550140050525010310707003401501058010b0280c1d2080300e440c1005100b400390000f441812003101145400c1003a600c881d005080c0d551046c070440b401c0342001d0780c440b09206403d13030060040500040d5050b000204407412101034a403180819464030108854900c0b02906401d40504405200c03c0032852400c00740003058010000c2d0b2200742030a10401c00f60781c8401c00c51900540c00e100300800b02e0755070b203200315034403000680300400d240500f000000e0380034120100041c4851440c40a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 142036474 1250 142035224 142035259
    0x40804090203130b0606090303070605070201180b04120e030c150903010c090f1a030c2505030d0e01050c04030308090a140a0c09020f04121506060203090f0f0f0618 72
    0x3c1600c59009002003016130320384206000041c030541565941590040080500081040c2e0290740c4c0050342e07100025030f006e00d0300741c2c1554400060105441010b000f400740000d1040b00d544103105040c1e03c0c1000c403400d1101001080d258400d90700002c1c41411004544118680c1400c200c5102d408020020002c20442c9074018280c0080f5001300e03040a007206502203810261000c0c101021544529034908640c1c0764038441d0010790169800042d070402a0200c17030070000210030780b5400d06120340b014540340c10500306680121155007400000e103a0410090014800c1d01e00d044170300340c2c0e41603e040f0003180e41d01d105203850840c145400806a14607440c051501420100303001d20883e201da4100c1400b50303921004682a0b0044c4000c0000d800000c0004222844240c1c140b1007849110b8084403031200d118911440444200f0b81c0010050380000401c0740d41403922800b440384c500c00490f24583c0324030208000c1408409121105070044000140010320b4864096108052090050851410309040d009 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 142037724 1250 142036474 142036501
    0xf0809010e031909080d0503010e0c090907030f0c02070506091e0616290a09230c01020708032107050c010f0f05010905092a09010314060c030c030f040804090203 71
    0x2c030310700140300c401000c17400300d6010518180a00040c0d0399141141d0805242c0804030034003504104002100f00070120080d1240a0201e11407110343d1000a0360455512440069410b41d01c3c1c00000c54014041c18021596084203543c13401e01d09542020400f000945840c91081940c00c80551041c008101d09254482d103050a4032902d100b810710801115945003090058a4044d1041099007107041c009007140f9002e9101d807070740d00e00070000b0101400107085808680500c03110f51048035040796181442d23a5804010240040404000962170705403001c141e40e40c4a03a0b007140805100084602007004a0310a000f51441591524002c00c900050840031100400700c0300d5600c40e4080c1002d0000800031a00e01c03030917110716040d0001d001007291900c1041d000b071403050b0704403820580c0000000703481d840b01c070441d41c0650f02c00d00d011a041d1280c00100361900d600107040100140c410420007240407401000d50303401190f100301485007a212441c107074589004a030441000588084101318940c0e04151 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 142038974 1250 142037724 142037767
    0x10030501110a021207030e0d03110f0a0503270a120c06030516180b1c060b190804020d020d060c0306050402130501080402310c0201020301060f0809010e03 68
    0x402000000780c811010246800340035a03400160704406803820031014004010500d0364444d281c04d25030344108800203804150840401e80002e0340b0410316421001007000814503600320207000300f400d004155242c07981ea2182070304014003c00e5100421a2b010000711000d000311100030043d12003280c4669001e071000027501401d58825540c0c00d8006611402442254020045030320321110b075601502054030464814070348611960f031090f000180001d500005007403006503600c0b410f010b101031100584160b503902c0d0000c440242d400c01c46c802241c003022020381024007144c1000340035941c032800080e0282040c200c002e900803a888104600700322050317000310301030742a03a202004019192410310041b1b0046048886148610110510043d8002d00503d0350040c401010204c1703404400240ca10290240611603009240030707000440000014000d07090a4035191000b1410342d032403d0301c010140589034103d102841044004603a43d41820f4108403200b10300382c01103ea569610307105054981c40ca60 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 142040224 1250 142038974 142038983
    0x1060f080f060d0f0c05091305071d04170c010c111b091504090203030a03061802070c06050a020f070f05101103030606030603071d1504020a080103060f090501051003 73
    0x1400a800c5040d01440c5074003900016102c1c22903210f02d80d650314400003030a00142c4841003440c0000807580c2c0c6070806540f04030030856201c030f03100b04c5c1880c12a1508030315400c00c1110805a601000d00510701d41c01c0158010340085041c00c0e11106034114031980e10034010f01d4880c55003050186940baa07040b000d040c1600040900716184900ea0700130010b00e1300280c1d0f01c030769030065500001c282800701002c1201070300c171002403000a4050140d800070780b45902002c0041c1c0403c0d1540000c00041040e05225030032020040e50640c908042d5646000391481e203806840c041c001e021809982040c400c0010004081061045840170b0303403258424080e070841c9200d0a4854071b506000d8040032403003062215034480312a0002d40c119120b2408201650300010000c0703070036101703002000560102c01d0582c13403007071542d02e1498040350920350680c3c40040105007000d80610300422a64081d00d41c014245411260400700001c0c00c17528a0f40b50740b018100c0d240c0040c01a41c201010300000e018440e0a210072207104 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 142041474 1250 142040224 142040237
    0x60204030c170a060e01110301180b0105280504320409050c0d030509031507030c0e030a11040f1109120106121203020d020d0506120105270a0b01060f 66
    0x1a18040d0b0b101c440c18455101082c0c0145041000041d0749422040c41d0b041d00c40d0002c281c65101d990301d1540360700b099110f80e85040d2042d4800f14104a6441015070041e42860880d15040b00010780081888100210200b10000f01450b04112032154080e94003401b609104460802030000d0760440ca0b42d04c62456614074800720700b1881203441c05116880529600c0001f4182001800c01040101c483c405020740a00004000c4002c2540e0180045405404002962031841c14030700c01c001c0c1100c54503c0c1c1c50080c422043e082850741c4e038001400d01e00040d40443e083c010841c104000c14050190140304080d540d0404451402140f91100500183d01064800c0c1e00c1c2c41c00e02c2e40e0741c44c2c01c1e41e0700d40c81f42c1ca003500c44550309140410400c00351404203045900380940782140c000280812070340003441084809903180144080c40c903210004600e0b4400000c0240f20307904210211400004207889080c0485841a00360340301414144400010142c10042102d032560751000c2c06030031860000d51000c0050f42 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 142042724 1250 142041474 142041479
    0x80d06090c09050409081603050307020f0606090c0d0b15090102010f060312140708120601080a0917090a03021305040c0b070f030c020d0609080a022b1407050a060204030c 75
    0x3541c4940c0c60102081c0e074034001d00600d008148002000d40b49000d1320301c402e040103e0708498541c1c18089081c0d52003940c7d21641c0e4070300504002d050039503160403903c06030010400e026043d0768030031050f500700c000c001403030355112403100780100108581c1c800d4980041100c4c41c0402039042d800c024004040382030300240710b040c1180c04818200d40e06400700030480b00440e449020001d204110340f004421090403a180307452030a81314500c1642019280010606010082104550b804205181c2040d02c500e024071a5008070b0b502c25101581c0d400c00c0031000b00000c11420065515864007100440e00a091058003c0ca01e06009002c0c000886040d288002442c00004880308800e04580e0807540040348144400515502207498071031640060741d0002100290380041665407140900c0b8910440c1007035559081054041d00345052004500417800710780804180f03101041c036025800069520340307250748521801c011a400c2c0620040a040c603c01c460b0094108180e60b0700400540c1c2c043d84801070980d5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 142043974 1250 142042724 142042739
    0x4090212030a0e030601150c030504090f0b040f05090c010e0a09020c030d0b0d0b0610050f0c07060e01030e070314011d0c031209030c01110102190302031006090803030c070c090504080d06 82
    0x4801e101d240b907047c824010300000d040c8a180d81c180c07914843c0c070f4003c0c6055507800045060741c4144455440c02c030707900e01c4444030a01d490b20801209419255003030007a8a000340c0c038281c0f54050240c440d8140110b046000d4510380da102480c1d80640140c0b001151115150104190703030b504003070114600306140560030000c0d41741010100840c254404d60492895440005200a07001d080601c0000d20105000ca00000c0e0b02c20009022214074400c010320140d85801e100070800081410010306251405500b2001140c0204648003074035000200012a00311154200c1c2c01020f0103406900000ba02401c4120b070302c03130003041581c44250120119020035036a2078200d034040c400c00140306e9161340300c0302c07400000703502580000804c051150001030a0008800b000314085110303115100c0044e6000041242c001c441d891071401604040c5483e908160420b1304655803444040d0600b1408100407842c00f041022508681007d805541ca051040381840d00e040b241c50b40042c10304500a40c280600445d012 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 142045224 1250 142043974 142043983
    0x150807030506010b0c0307080a02010f05010e010b07030302091504120c270c121803090e0411130b03010c0806040e06091c03020d05070806031b01081504090212030a0e03 74
    0xc941000252129920380b0007010269400080710300c0c03180c0010711243d008a04070300b000c1c02c20020540c00202e03210400b00380da54119541604011685130104c5c0041c0a980305c000b007641c47c603951500700140e031125070341c002a88840c0780d2105078610200004004c2082020044490001c40c82544e094107025224030354000060682000b040c080d8a40b2404d940364921590080e00b88180d01c0d0804800c100449140e81c400d1351a204a03c1c240725015400302c004050780910302d0b00090401c4c410548081c10a5618003501c0c00c401290144070310b2900702c45810314003030b0340c1c04100300440c024001c001c1c0360f2281c2030240200a080b104140728625000301300e02d41090105210f8820920b40e000f5240a02d5180070704015803540116000404d079003480a145c0c044454400d060256005440d450000c0c43e00718105031038822554540c41507440c4e09400c603942c0303980080e00b00d50003010b41c0a100442c0c0245001041c02030881502c040c0d4080c00710031100d040300001100400c01040155990114070700d0f40010715070768 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 142046474 1250 142045224 142045229
    0xc020105160212010f0e0d05040509061512010e010513020702010206071101060f080606040b1e040203040f080d050708010f0e04081e040f080d0c020d0b070e0d0501150807 75
    0x410300030414603410101501c40141c0c0a84010074105568910380400c0c3d007104d4a00040c0090a9039070403000c40c100d00e00f0048100e0004540c61700301e2420741804041440e412019103a0383c007400e11003034412140341510b0143c0d41c0f40c5400070b2524032503682d0740741198034080003845003e0103404060f101c818a1301550003122845034068004180903180c40c5021180042560b1647e02c055686840c0410441044200580103005e0b050007001c050070300504005c02c60b141c000c00103118034031402e00f04620800d10710118507820f00841e00185c6a0b51a41880000f110f20035200400d05000003450000361119644098041c0c10030341c2d03403401c0c20b0f0b0f21503910201c00d8000b030188015103280c420010b0300140803000200030190082c0079550803074052899004403034129400001030289030940a0001c06010800907004010519040441040c1070700400d011411700e1001a006003a903100003004180140018603d010014081082e09a06801c000e402002c400d0903000c15030b5034400000908006c0002c07030000307 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 142047724 1250 142046474 142046477
    0x402040b030609040212030a021b011e140403061b0e0f0a0504020306040914211c0f060f121a06300a030309110405070e040e19060e06070c0201 63
    0x7468554008100d800180100120707032001c104113540254003028406800f00d640c25800030045040f801e03600a49148541800604209940000c1d424440c4003100002e04c10001e81840d080c0810703d17901c1d400840c801e0381c00140100d4140358a00200300c100000e044c0d4448896039800030181310b4002004000520b5003c01e65011031415030a100b14542607005641000008200260611035643c50414034038100c10060000c3d00f10f82800001140107404640c1500005207150f80b510383e10381c8450000c0d244d0040d4003140d4955512400a038940c07107600a001400b82092000b000c0366403004000e010444c17001c01182d100b8842c0306c0032440c03504102202405030380010544000c0560301101018a107482004028000c0e0002ca40d038902c000062011120361802640c020407030301c1850900001001100450600032440d00c0c0401a000d503001042100a8608460110343c0320785011304075207000d0801850303207903950410a40ea010004c0d07550040c00341041d8101603c010b03a40d4450142d80c0260594806030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 142048974 1250 142047724 142047727
    0xf05040b03100e13080427050c0903190b041515080f0c0604120b2205150f04030c020103020c01020408011a03190c09050601140c01060f0b091305090a140c0f0402040b 73
    0x202c90016207840f50310311810b080d20310401000000901040c0c4070149c039402d030480800900c49001d801d0900401d6901c0c212800c45010a410b00d688858031014000c1c80074140344600741214080d40d40726008003ca00344218000d16502c0d03101d2880301c0d140c10740003031580f40920900d0030741d00c0c103404d00d0826203048a4411951515101d02c1e45c88080701c2c1e4400030011203030ba001d04d04004c0e0800350307080c100c000624003410051220340c41d40703802018121400317801c02d10040212001c0200096004005110581d420301e000741c2c40f800c4c828000e81c0a802150084c5c0003d500744801402241088440032400e094210111a5003007000505101440003944001d031000c1c807450020700c18004d20742c00c5aa007000040c50100301350508150a09904d800031404080349944a0004014114220b0260780161201d515a00d02c3c01611400003014108081c2c81124110703150000540c00e64002d000180845070040c101e00e10112000c0ba81a440c1c050844405200300c1c000780800c40e503403c00c1e2090760203440d480381015 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 142050224 1250 142048974 142048979
    0x6090f061f0905040611070c051e062205120a05070b0a0912020a050405040609020f03060c090409170403050f0f0604031d030a0c08030a030b04090803070f05040b03100e130804 77
    0x700c02400f40100245c4e40a0380303507a0b45400310600f10f0000c1640b940a8564140d402e41400100301c0c0088a004032802c00504100c009880c0740c0d143e00449181c0100a904440f8441c100000350561028503440541d0100304482454101c0102080398006035114405590320140c5401c000041401501a120000f4240c1c1d00148075002c415003d64046600040c801c0a207a55038800280594000b214203c2c2c0103600e6080903811814140303008a05800308501070105803600e41d0310300c49240144528588215140c0ea0083d0a0101100701010700c0c0d14200f611a588507142d062907a901c0d50600c204c10003d1240100442c0426004941c3c10300030380e81551103e6500d010000c000280182458800d41e0500444624000080507903245038014118400919250fa0703040e14090700700d804002e81c0354000c500340075800000480150803240d0083c4142410b031300e4200301220454542c05240c1000580503070000903c0741d0003284140364003c403070400c94a1141503a1f10070307580e1198080e07084020041d40080c0400d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 142051474 1250 142050224 142050239
    0xc0c0d080406020c01051305010b240d0e0714121501150e03070311040e06040206040b030405031209100e031207140d020d06050f180406050601050c06090f061f 70
    0x800e8100c2d00614000d42001c2194000c0b50031a10f055a070a40900c0b03000044404024080c01407c441c0e10048480c0c0002c0314071402103620744d00d000c450004103d00001070344005031050341c0c00303800d04041c0700003102c4480d03486640492004283c140058410001e1480c00d1041c414009030180f8004014600320001e6460094203c40000703141503c03109002c6404020f00b1030351401c000c1d1800031409031f00e04d40034034942c590900044811b16455800160082e00800002d81c690314100d50480d252010380382e071799a940e42000c80c1980200d180035420a001e810030b1088004c0006040060072907040c0b420001c1010103aa0150703a442a0341c00084e40d02004000200494002c007843c003550324160701c4851900d0340840b900c0d41286d10699242c40c900396585170500035803c000c1003900d41404203940c81e042c004440c1d2141512038034010300042c1401d440d200000c89a03480342090311046810003040758802c3c101f44c1c000381e480d00e1041114015511458000402240d110544006042030123000b020b04181414030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 142052724 1250 142051474 142051487
    0x1404030f0507060f1b090617130503040302060d060f120f0b0603120d1e050106021203100f091a0f370f0612060f050105030415110d050c0c0d 62
    0x101610380c140d46051141360450a80101e1005521580d004201c0c0000e00710003401030405a04030390100414040702550a030182d01031160401200400580418440d280c0a0325600c50340c1c100a400c2030010502c1c090047e11a002982612501e00071441815125a4032107030610000074098025190600c9400100b0707466020b89401001c050f013600e000703031421300d13029131550300c01d54080c1c0c074255032083c400406c81d000c44025400c0c40721f103803030030b0049503d0100002e5503000c481c0c0c3c08010803440000812241188e000701d40004100b424450011a6980c0c1d5400004100350400309040c0b6416004510756440c2c15506802d04d80b200400c0801c040c0e03a0740f880b00541d500121680f80c0d41d0300c1110300390314444501c41010002440c041040f00400c50510310010806488000340007401810710b10b091040029000c0c0350340654a0030700c0c110743c50f6592401c0404d00601d1069201ca00940f511400441c1408003800a00d00d040c0804410b1040d600e9681d150202ca204070309403040250085851080503d2007601e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 142053974 1250 142052724 142052737
    0x501030e0703050f0f060610050901081801060b09030d08040314090a05092e060207031203020d0c020303060a1208030604020703020f030c0a0b070c111306030510050103061404030f05 80
    0x1ca4184589995030341e480c124040c1d80e40c5900d075010402400103007808103c0b1942c46001503d603082d20b0584100040c046001d4200341d103050044480000d03400c0c8902c002038089901c2c0340300003070140d40e40d40d100f00101c60b4058031310980280140010a1035460140e2002806294555500850980301c01e00d004030a400001c1d10720790210030742d48d002450303030b45960700305000381c5040f1514003800610941e0142e01020b0b090176691058840300702042010b8011540b08102ca40219210303c0c4444c1e1000200d0091048900e8003c50502d00607401001650001c051403080d0401e50f02ca100300c80d01d520032804540e0004030007d00c81d00c0c1c1000044c000d403d06401a0504034800e00407a50030101c1521603070b00b9904114007699030b5a010901100c00c0c40300803207007542c201c1c40d14104201c0b0004180c444200007060296898043c0a01e05140107000c13555a100c07400440d004030a417158000c8515112000d4642031006603009400c00049000088001da0412301840d0301d03440b0000101c02e040c0c41500c5071b41050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 142055224 1250 142053974 142054001
    0x115111609110c0703060b030624060304030c050a030c0501050114060706021e0c010f050a02190f0207080106030606050906030c100e0d0c0305060609180c0f040608030f040f0909020a050103 83
    0x5120b0001d2203c0c0410030704010714441c40c2d000c6911183c081c01c0c0343ca400c0d002040c416400c840c90340064038030000c4611912010030280c800755640d0f03945041c1641c8a200d542001840781c42076030002070074076a0008010a58a11600080c0704a03683c42c10f4016107074502401341c03907201f0010000030000900c0e650050000301c40618032017050000062503080b031a085491000000d9440d010302c1100c2c1c454601c600f03a400820002c00318100006807034107101020880c01408188a03101440482040c000c010520003440c048009108082c2c60f49460b5000c0d08241c40f405029106e00c10205840d883c0100b1030a039812409008400340c16014403080701c00400580401303030808105c50849010804042c001c40140d8040c03c02051141007000c14090199401415660491501c1e6240c14a140f008140010100000c80d0f003034510111050000c0c00070051076101840f288000100020101010005441240da60000a40c4c485550310100d409540a100700254003c010a1302445558001d0f4412180d01104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 142056474 1250 142055224 142055227
    0x1b24010803120a0e0a08210106050702040b180702100e070308030415020706090b01150c020312070201021009030c0201020d090b04062015060a12050601171005011511160911 76
    0x1420b4104d420902403071130a542d00000007a610b400901035076500d000c0080b022000090303642c50a8030007051070040c07500080c0300719103d4280c9242580c3e0600740e128a1486001c240c0c04078142054040c1d960000000c01200d03560501c109110314031800300c1d07040f0880c0c2d084803d0303502e1a540c0740d84c0da05203041ca01c038500c4481a401d201c0b038004548513109490b4454481c529481165042101f40d00ca849008011501003103050340a0100584001c902e58406990062081e500c0e00304a10040c0d0420039030410b044692460020312006065000241180a41c002c0c0c00750380c06101d008400301c8034041c04d03000304610000204010400706214007907000301200c00c40c40700304401c81001180c0341000c03100b049500c009001ca006000c038070300c0c0482c400c03002400310944800c0380c413103d5510291200c030144240e280c426030076000d03615001024040c082c144074a4140400c965a11003940c08030061401c101c0c200000c00c107480500031401d002500580451411980840c40c0b03142c651000f000d41a00c1000c034000300e40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 142057724 1250 142056474 142056491
    0x901020a0b0106020304030308160f0e0f060c010b04110a1d0d120e0a06020706020a08030406090210020d020c06041211010908010e0102180108010e1b1b24010803120a 73
    0x1c0390840c0c1d01a1116601860744e4900d141001000200c005c4c04c040b0942840c1e41201d04081d0f00000303d81a40c2c0124200801d03407407a40d500140c01d181e40b0407150740d0019000a0144e401140c10341c02003a1481044804200f07800042074840e07494001d00b402d9a01040109820403002090700d030b000e005424000b00809100620390386c855440c11134044142c00417408414241c0c3c1d041c5800c940034005014144028450646031010003540d0b42041200900b540c83c2c0080420103001c0715070420103031107801604085449004c2c440003940c40d00341e101c00c0360043c00390006240c82071400380b045030111900c200e901144880380d92524907813107000503042810310041c541e0011720314100703004001808046200040e00d60f1210004580e103504c1d1445c0e594100a81c503c0140010903241c506140c00803c3c0d18495144440030540d100340500c50028201700c1e03e2354010500b10700354070004005507265034254920740321a0890485038181242805807600d070f90010721640910948044025a02c0710300741c400452a042d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 142058974 1250 142057724 142057733
    0x20702041802010906050913050c0405030304030507030c050904020a0512010f0513020f151c0908070c0612090816080d060b0406020d05040509060103020f070c0902030901180210050901020a 83
    0x2990401020350a580d032189590556130010007000041140f41010303450301c50201c0c002074000902284602d145aa2840801c40c40c1319401c0681e000b420029040300d50341e030340b00c5c14601d98400d00351104441488900b030010403613017030400000703001d298043d00045115003802c0c1000f030810301802c0c80450640d80c899945804030501d00031540580344d4445c00d019000024010b20529400303602100d400340c2541c42c10500b16202600868a0150140e0060310b16010740d0f0740c1440280c4020000944080e001144034824810381000f200304071103050f05c0366510f4040b070380813840a40304146000b80400d2014403140010001856126506a101d40e000d64a0400c030300c0308440c121411500403c0d48002c000c50103011030784d01008100c58440e0142801030810b4644000503403080c80080903603041580125954400301450700031790343c10344e0344111007040b000d40b01c140720002508212001c100e07035802c0100e410840d420801c08000801c4d00a01100d140d080c5070002641c1700d9000e152828114810b00c8501404038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 142060224 1250 142058974 142058981
    0x2070b01260307050604020f0d0609060204170f0606060904020c10050114090906040f0303090b07081605040515071b0b090102010b040b091b091003060e07030c0903080d02070204 78
    0x2401c01c410502401c11010350031041040c128038503110650310030003150010840c005296a801a4103d5040da1202003805c0072490031225034900400301070a00304031808101c0140c02030420b4501c00c9081c0e41c1240710383c15065540d075002c00b21010700e80d040306000c905c00382403210040080000103000903190044105500385071034007428954185990700c10042c0b1802e000c14001b60004842150240b5050034034441075a21040040c0000f070040030f4140007102050300035000161034603000f241c40100382c43d1060024003030400c1100c48401e00d65044010341d64080c05203040d2000d40d00081e00c104c120500004da83e180c1d0743d02120701074030389018800740038640d200b691290f4005080c602c488240c84209120004e42950540c03111030740b045007054806a03007503c5043c00268405070030350205003c80810031031107a40780b1400500076004902c1000204209030503130081002c99002d110304262a5460031000c82c11142030880031400980c01110400c045007400014082404800e2001882c10300c8540c0010200c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 142061474 1250 142060224 142060229
    0x40f030302010e07060c050304060e0d08040603090b0a1505040207050304050303030103080d0f0203060d02102f060f010803030408130506031905060301090816030908030c06190c050906030a02070b01 87
    0x1070391240c0d00760040c80414090013008107243e0801341c000b06031a82d039a548078081d5000d508100603031000b091500359071303a03040b40c1d145a0f0048146179a944d22124000c01519034182d095410b5082c038030119050811038030820346d0003000101000c851034102810040654800401558688028040400c150740e050000314000c500c41e51205640303603170200b0f603c402d4440490b00c46003010320502c100312240e110911041407640d0704491701c3c00040a09a0309550b1380100c06160003160704411019520f40b60100003003c404c4c1e01080407100785035509240c242c13240109004c1e840c0ca80d002031012070006681c08020f050f95107003038070075008150f442e40081040c81d00102c504c0c070001e60740000e1001580199200c0d25411103401d074003e200544954588842c503100310b0006145c001c880d02d01c0f01060510416240000d0003a102c2a02c1e40e441c010300c1826954a070a8801103510320307501030302440c00b02591080001c0300701d940e22150f0030106558104030b09500000c3c5408080740c2c0030000180042e00d0721002601 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 142062724 1250 142061474 142061477
    0x507020a08010c02120f04141c03050c0f0606030d0f360e15120a0206030910050610170705160f0606060309170c030c060403030605010e0a0302060a0e06040f0303 71
    0x501c0c3c40c400b04000d26002c0d400c811490012801c01c900589080c45004030740580d186020000c1c2051240408610a20341d90741c803490388050804c0e480010940d1140c01800d00760000000c548041d14044000d0b0340b1070805880c0103625a020300c01c0030451600400e0142910f10079403c207555002403201c0c03901000307190440101c0340c2540c0100074001042c10301824001400c0c00b00c02d2403000c0c0c80e19401c08000e0201c465480d03480f5108071040300c1004a81001100321031940a090302e0707100d040404400340d460510100c10309c0300a01300700006030f403807c010a8981d20803a066950b10400d40c603900e0710388031003440035081c00100141080307600d42c0d07440d00440310b200061040a400106148a041031800c988a54211500301030170880d03d00b000c82e2410410011081241044603584c6142a04c1e652840c4140c0700e80d070055001d01c400300300a15405a000004a8001f030700d0701c01c001c1d50307110100028603480f408000e512980a00900d04218070a42c10360740805000340030185010f40f22046070345110348640c030890 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 142063974 1250 142062724 142062731
    0x3070501090c0b0f0d0504060e190c08030a0c060b0a03060905060a0f061401030e160e09010b03010902010c060c02011d0f1e1e010207020409110103050609071209030507020a0801 78
    0x30104201c58000800030b201040300c050904e040301001540304c0c440c3d40e5621001c10b80700e8003c101440403540c4000711619050040b9600100340c6041c4140c00f4071080401d80d60080000b0000500e45000310807510411003e507601944040c940d1b403200010000c002c6030b0b9400005000001c00051700074410540e083d40120001c0c00e143c40c000c902d110031340b0b18001c1119425810b00030700b0400a5040d2100108881c0242004101904d0042c4102d107094100c0c40f040208892504001807a181c2d28861a8000c1029400900881803141d007071600f66418040000d00140083e0b80403004a54a68040070380c034000c0c4d00c00402d9464200c0ca81d03056141064040f014160082c803030900c8450f20070030603020403087d42600c0c819154010101c180e154140d840941d6945114240f69600040c803e60464000d1a40100100818842c03402d15031030031041241140c0c0030070310b004085481450401942c5218454569078121049101a10350014100c060300440070301100b8418400142da4a80b2050046c005050000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 142065224 1250 142063974 142063991
    0x9121110080109050702010b010e060c16060504030311071214160b030601120506090a0903050d050907141c02120709020d021e07051515031504020906010311070f060e03070501 77
    0x490803564085d10702c109580c5030001640e07059030040030171120800101e4229842d212020441400d01201c60380900e001701035003c0104000350080c015000f9203009954480c480300340c0c9014182c1d20b1410340140203400211103500700014108801c3e810740b1170300c000c056843e1325603500311522403c00c0e00d0300301103850340c804002c004940d41d20007001d80390500820414000c0b81811404901580c10141005821a0f1106440820302d402030003101c0680c101007204008628081d8841c40c0c9030195401401d02c0a440010158140c1c41c00640c464102c1e2840315600c00514038960801c8981e501148030048a4040c94400058145c2180b010301400c0058090240e61900300540e00c1d45500101040c144012405100040100d400058468000413000b042c68800d0345a03404103001801034440055810b1048104104445003c0220103004034804c3d07030b140403941c56100054091b40c02038202c0d032030034031000e00007c000302d199140750061285c040e4a00107250b00005000b40d08540c40034600303880a0b03441d000003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 142066474 1250 142065224 142065239
    0x6041109160504210b07080f0703020a050d1509020d0605310504031e030c0206090d0c0602070822060e03011a01030519021c06050a06091211100801 65
    0x1850351200e1800c0800c072148403416005000341c06140a400c0018401c8801040c540407242c00c1e0280460f0001d81c000402d00c1d02c1c4134000e20b25107003160358101445c200c50124004600a00a440800c140c40d00d4541c1845202c140740002000c0d569034210b403075601800e00040500d15880180581d859140c0d01140302402d01090000d0032416101144404101c03c0000001403800c590040c0800c0c811500882d542d10f89040868005913086c0c40ca401c2261980d5a0394041c42e0181d006046500083c0c080c1c0b00d16a860811594890124002c0c00000c268100c0034000020b5407903005000042c4204086c50401d5400ca001841c02242e404048410f00d0307040105106e482d80090030117030b840d84120024004ca00010384d100445402030350100e81410f40302c1c000300d02d80c0401c503441c01400b108116030440d00d4a5060035000b400802503420080340d5803401c030b000701f41404c00f440b8400550358580c44144174180707404c01c84041000300c10420780d40c0c0d002c07180c01d104a035076880800700854100e5580d01005c5504141a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 142067724 1250 142066474 142066489
    0x2403141f0e060102030906070c080303070503040219050a0603020715050106055206140703060e0105030715140a09030309171e281704080c0609010e03060411 69
    0x120721031903110020400c0c02c1e0390000c01c550041500b0b030307030301074595109142c41e1020860640000702c050202204000807154017001651103036000b15940d0b00366509000310304040c0b0344140580c1742c2002e50480140000d41c020f400404040340b0921203c090f180c0c004e010320040318003c0c0c014a0004200180b02d00c12010b0304010954110310609805c50451008000d84081e211001c0414142e81450045119425549540250002c1d0040402d202d003490170328842e9408901102c00c0ea02103403400320045000c2d80f284014605076140a8020000725041848022241014020260070084c65400c40c80452030040701038600041c041c3c940318010380c11442c016103500541d07000700c448814000c5000403442c2d070001384400d1017130303606c402841c0c203281c0c4d03000c0c0904104480301e4040742000b9079202014801184180403400600039800020704982d81c0c4144071681c0308620510140d0f61100314400300526004006107007954050504241d00b0030030801290500324101c80540d90080c0001030003280f420420b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 142068974 1250 142067724 142067729
    0xc0a0e100807140f130f0617070b0d02070c18020d050601110a0201112104030c05030609071a09090405010e010515010507031b06060b030106020d05042403141f 70
    0x40c080329410003c0001a039601104410b210340325524204c021919806901102070040c983e090100000c03e20594010702454420400300e441485540020850003041840c280c40075020200e2410034083c1074000a5005400e003a0380c06014084006169040c8003415199030130f801d0409a25604122550821581e000300201d051080c82003603c070003500d010403034000d01e641c242441c45540b108044560b00d0181d0f20800d802030422503880b000c0f8040b1802024000700c0340b1030b1140842c025140e406268407504195000c000d2039000f102c00313010051b0442c00caa06454084c800395402c0242040000e040c4030301c10341d4140d5a0b650b5503801c102208000b800b61503070104440800000b0290360744c0000b040303881503a41c042c0801031010016880c040301d42d450300d030725160002418854151241d610720400c0d40207115000c054406d02e031039081600d0060050350200c070001a001c08070680c15031a8140c1269580214808043d40d90480c0c4025038021003410b40144020180408010050900217801c0a20b0f034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 142070224 1250 142068974 142068989
    0xa12050a0b06040b0d1113050f15190c020904030f021c0906050a020307080a0e130513060f021209160519091805010e010b04060509040c03080c0c0a0e10 67
    0x5161041d03961159000c4030126500c00e0880c2d40e6419440e00040020101c1c8417128184150010f0350703280c016640c400080556004075035581d04c0245410404c91400b00403042505440b0041c8241110405444482801d184043c03d01285404940e80000d815200031038044021600700806144010fa0400455400b01540314007020290000d04003d8001c10307140c82140c040250005507034001310310074010303206042e03484882507895035007040b00540001c281c5a0010b01075894080f079030720001000c0c007409009079030340c2d0045686000c541c0c840c0c1c00642403545400c1c2c80280c003082580c548440c0a8425481040c1010141c018169a80c59007400c0d0380c00d13588041c0c400e4904405103182510f11b02002030440380c0c0e0384800980140340760f0000b80e0103132001c04007800d29442d28007585003000c81900080a544402c039420411542c5603c00c00c10000020350b005810410780300c8c4203000184418006240c03d042820481d41b03485d06510004414004981020080c001e000052020301d003a401146c6010701241e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 142071474 1250 142070224 142070231
    0x70b010e0a0e060402090703060b0c030a02060705070809040b0d140106080706020f1507020c06070b01080607050c0616050c07091a030d0f0509040609240902090d0f170a12050a 77
    0x2d2510a0f0307072044080c01c040d00c00d02031a80401d000d00c0c000d501c848010544054040d403030780c050010481d1250846d00150002d4041d03a000a00003d1150003210901540131284a04000750482030000034040c9040711604824640355220126840100c03d504204071030f800030813610b05040106040c03402d268003510640d8440c0e03149188486010500703188aa900310250b1a07281d03600a001ca01c0c11a4280c49141c01c200002440d606008003021181e043c1d031140c0c4104c0e505a118000308603464401c0d6031611200342c0084000c500c42c201041440429541b143ca85a424110001e840c2c40c00c00c0905e1341301d01e018540d00e102511601c1c07403014118089220031000b82401d004106409071020380f22610510030030800280756445981c80b980001d0240960b40e0041000c4e461445a82c1d0341510306410700b900c030041000f4001101d2a0324000c803a001440a009840007081560b40c5480c8040001c0b411540301d07817481900e0f40e0811510300075000c0c0d00d00c1c5580340180c0c5203841c60090100e49010303019001c40c504 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 142072724 1250 142071474 142071491
    0x30b0a12030e04061a0c0a020612040b060d030504140a0302100207030b0a0203040c05270703060503210901110709050f1e091c050705070b0d060902040e0408090a0803070b010e0a 78
    0x85c81e440b0610501d4110b0021540d4090ba182424188811580000e510010201d035030084081841c14a0303209038810540034055844000401a04001d00c801c0240001c00801060115a030307500354115841c039014081c440c800ba00c9500140484152070205801a80515400c1090165035044c881d0041c98111086155003865210b82540741b54500600b4020034402403d101942c1308942c15540108001c41c26940900301140020050127075441114840d00c5028244401c0b03000341c07400900400140142c1c18900b4651000545d842d15502441d02c209000e422000646c260715801a240311b10101d01c4015040e1070304540b00302420201c403411010b000a501700304a954840010345102c0c083c0d04204460020588100c111014030542e1001403060183d8907002400414020180c0130700c00705c46030184034864440700214128045c51041410512200c004600480c03080c500400b40380340054002030b94036849109841c43c0d54499941141c1112606004014001c0001c8c06190819842c0320180030040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 142073974 1250 142072724 142072739
    0x81006050609030d0c05190807060e0105060f040b0109030b1806010b0c06070c02040902130c08090f0c1005190804030e0f031e1609020306030105071716030b0a12030e0406 75
    0x4070508034005120001c00485d06001c420480c4c10347c1a402001c041080800510f00800b840d0440c0408030340d0182050304000004006001d054441c4401402c0c200c01e6a045004000180c8000d140d5217040c00032049000c008141e190044911484850a903001061542c01601c3c0c901101603000c011360500c02d01c503d00c0c0e83d40b4041121170f0810f0940c54410350084140c00041d0007004e12110080d03000c031241c000c6085c41d901030b4000c80704051f020344840070b080da20034054544403008000c00788544d800118a0b00c400d45801c08040c5e907400d9151600500303106520f04542060111111004040b403810000c20042562054202400910548280c1e00d4082c1c0d0b0004070755a40b00c0c0d2034215140300351104691400201c20412580c011700d030f1020452546581e469901d00a51007500c05078000c1d400c200c002041680500d030b401d240616a13404429003560340e8000300380130003444103c0c81c0c1019181c612094035541c80903030103030241c010301451400f60350705480d024058160344401c0c036002d142408010000f14 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 142075224 1250 142073974 142073983
    0x80402010203040b0a02030d0f051618180b04090b18070b04260303010f090605040509030405010c0c15110f01050702060606070c050a0306140703020304080304020f0d0c08100605060903 81
    0x104c0c4c0079012943c44141094059096004070005c080030705142540142001101c2d422450198401d45148842011080c1d0111001005090b0070301101007810410070400039160b00c01c0303000e000c032040c0018000744090000340c1907401103241601c402d140f110a114415483d5884040701c840200020000645032101d141c59a0282c0e00c140c510004c4441c01110101108a100c01803451852094940c3c0350f85a10305a80152010b000e1104e20354584640814582070a01c41d4901403082c2e0f00084d420107150100460350740c01c040d0801c580d058481040042c1a000038242c00c49007004686600510b05100202e440c90b00c48440a82d40c1248e04080030300c1000d82e00864030315044182a540b01d995003120341002c01014038168400c0e6045058004c000040c840a584418141c01000d80070414689a02000b00d041e80816a009800040d0820101d001031900c0f5504070790010b800360000180030140c0d01c603020402c040358052000c070740001c0c0341e4200c0400c141c843c00e8040d020448030681801041004240d54 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 142076474 1250 142075224 142075229
    0x1212090d170402210d02100f0b0a050f0112020c0a020103111603051317030703020c030708030313060f09110a05030708060a020a0314070905030c0a050d0b0402150a0908070608040201020304 83
    0x50751500001e00a18910b16600d00d40304040d0200702e81d01c5c881c400c0030080d078510100d541c01c0301d1540381c89051007029a0324001e82e500020300070070f80c010f0141018100403240640d241031078148462100e1080010409001030b00502e200180580b12012490002605460350171070002e101d2281000074044400196030703007501c26a0940f03070540e2a0382200c2d000100b200c01603002045400c4603031100814141c800401424290700c40d50035074413141c507000700b8150341c0c110900640322140c00620009506001d20042050072130300400300481e00005041200341180d03242030040e100c016030380b0f07006002402e10741800c0005000680080c04004e280514294440c8009882c0080c680d800040165482d84070b90400a1960b241d0b820500d014101668007511044461042d14000e0184003060b609a00d07000a100049400140c03128803446000c3c0d40e541e914540061040340d02192420715140d8414002001d03084410081d194071000034104a0241c2c505107683e40520100f002c440708020040c1da011054404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 142077724 1250 142076474 142076479
    0x22d0a0c0b09010e0f100c020103020d0204080a1104090b01060c050a02060a03020d0b090108070e0a090b0106021006060212031816090e01060801091e051c0504140405071409031212090d170402 84
    0x2007c56248012006480740c08180300010b070011a011032581d001149807120644110f030310032550511201400240c1d6070011000c0c142c0d06c0c03a100100803039130061a00000c0c00b44943c0030344040c2403007039000034a150003d07104000041d030301141c070807000010b0384a01040030f0700072106011503614025003e0b64445090083d035400c450b603280481c50710301e029007001b40e03410360100c06010950303180c0c0d8000750b07642d052002c5118000e0030540e0000b0030320b0020410b8031160343c0700d920541c51036441420001c031450a50340419140e00c54039074000817940301540060054510500042219200c0094050945495411030031081c0d2609010303c0000e034180040c1cbd103d814450303c3d8901071101c641452400c2135400080d0360101035a000290070300301c5e40310b0000c0060354131080e101c450340e10f0b08800344001c441d03084580101042c2045002164529500050098440001d0880301c043e003001548a14030340041c00380100624860061001c0c10200b4400400100b61714036142144003680c0b40100710541c406003000c0d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 142078974 1250 142077724 142077737
    0xa061d15070e010504080106120b131e0203030d060905091b0a1205070e0a020304030f030c08010302060315060c03130e041106180d0b0403080106022d0a0c0b09010e0f10 74
    0x41543e406041510020070340b0b0380c020040c03669913001040c0c0d20309002d0300460f0701c5164580060401c1e461030b400e045109400405040c545641085100c0c184618901c1c242c0c0d0500c020f0107040e0410401c2d0251a0141a6410b40801d643c140703401062b160039212a0070070301254050018024544859113100100c4170700c0004070708416032904209051401e83d0b0062220403141c00c1c10440007500799001103001da8860f40e540304445814401c203d04442000c1c140c807001802c818010005482d001c006190400418526004184c00850000b05a5070081b200140c05030400304400e0110303c07142034030790010f1800c3c2c0c00c88507061a0556410f99680720314200f55100d180007094417010148a80008100e180d00501020f4048056080001c0a00c030111401c60000b5011000810f03030600c00b10715039500c621807164105000c500185029a40d181d01d00c002100b40c0705a0340840d02050316841404010190807500307a03601c1c0c184c040010080fa0f003482a0501624000360501440c0d00c800c501c1a8450070700b45001e2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 142080224 1250 142078974 142078997
    0xc02030f031506030403270509040f0602090307060804060e0601150c110d030507050706050a020d030218180906160c060e0703060501140f030f06010312020a050a061d1507 75
    0x480082a0408030b494206102208103c20142c11910144086030814002c880e200e4034400c00b911002018028240c000c4504e601080005000110740b001e01d6100c0e60003d41009801c101082c6010804d034000070020301392200b80000d001d82845240c40302d40c40c000180c046581490b103d82140c140c0d080aa9041203040c2288106200810a0068048030300608401d4417080034100200b094100c0c0390140c3c1d1301c1c000c40c4800501c4900070000c840f000c030314580180c980003514410640094200b8030b540c066065203200303185030583c1c48110001441c41411990340780d0741000c041c3c00d0b2034031b8001002410703080907003950721307420303503040b00045071100d03804480811b05520f101d021a00b0260302e6400101054200800821a90003d00103139503440c109407940d407007405041c1c04150b83e400948400c84100e070170240040c80400d241002d051601c044600440d40c2c1c0310070300c3d40c1d114500302e4468415110f00b0b641341c900c600203002d80d90301020032004032402000212a010f4496244100140c90354081c0030400858 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 142081474 1250 142080224 142080241
    0xc060304080c01150302010f080106080106031805010606081006031503121b062708040b0a020708030a020312010e0601080c0a0309020d0b0a140903120a11070c05130c02030f03 77
    0x40b42c5290307a10100a014021064001c03140700e50b41800224003049190380c614801794441d40d041c1d030403208240d42d8480264a062800c4d00100200314082819442061013000414002d002d04001010301c0d81ea940004e1800602003038400c203081e040001094100101d108003074407285c2d101c0040e00d8100301d800e014103441100c00d91301809110040a80300206a8244091244c241e10103407904d400c044808594a200100f0b802820404030001440300e5810311083c0080843e680203041c1c1012103004503800030341c0343e241e901e246800c05064030006a10009103071280110320700505004002c10b00c00d5030150b00b054000680005001170000074490008901800000e10a420220109402a015000180f0310381014240e04804a45107070303032241403944541c44048680e02030303445881c203840650304240600002513101078000e4400b0303100c5900c89040109291a50000300032552041422058052914090090120005e008004203620380b0405510181e00802201c880f201404541a5240e440840 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 142082724 1250 142081474 142081477
    0x30503060d06090c06021b0105030c090307050604030803100b030603060a0c0e0604061205090d0c0f0201090308030a0e0c0f030c0d020a080f060a0e120901050a030905030a021e0a0201020c06030408 86
    0x30b06690300b422001018000d080e41d141003030b80d0842c0d0070303038080000101182d00c2c00c280600303440d8002281000018080080c0c00041c2600c840d006054a10403503441c000610290840d400c10380d0844400011b000000b00c51203160030061161032002e900754a0140006a01c1e1000200507404480d102e80000c48030612a40000e910040000d20036500d998503a1001041c00e4460813040d000c043c54034021901c43c1c400050b01d00c2c0c01d00d160ba525860214021741d070780e003a8041008405c0341440000700d0003200203415200a50b00c1103035417400000320701d840c40c00e45d0b43c603005d10000c801e03014ac03000114655180e10b000c554007608020035a0605d1507a851031010032110061507000e100d49005008600b581c0c0da101107044e0b40100c1980d0004e210481c2c1040c040340c0c071903101c2c0060310302110080012440365406000544206100c90400141d44003a6440300d504551003007091400681100a1145a140528034500070301d404000c001c000700002d03940081e50b500c46c1508124426003010001404010340d0b0300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 142083974 1250 142082724 142082749
    0xc1606060503031605070512120c10090807051b0a0b071505070c1a0f0a0e100e0309040c08040f08070212010903020c0108060904030e010809070905042a06080403050306 74
    0x301100d0343c50340150340132020003020000c1100e143c003c45000180603e0461801e84040c1c1c0d62070090b02070030314540700541003680901c2540d120ba0240341f05288a0200c03600c5008a09402000555520341c15407811b141403040c0ca0640d1480e00b40d698002c01035a032100c0110405480ea80364960380d4032025030406001e008428051138403240c0c140000c00404c0c5030700c0f03007040003038074400c0c0080700f6400f81c00000f40400ca1400c6030071000100c80c11000580540031a04210004034907801070b64103015240c2c1043d0291003450300540001c0d0710003d000102070a181c460240030280500d80a00a42019940c2d200309917001c036000783c0820b1010030120103541e100b407a61889501240020040c00e001e910380a5140c0b1445610603000c2a8040001034172414404a014802da07070540d00e02115440d0440155a03003040a0a00d50340c030b02c598640412050ac05104981c051030007031304010400148090700d50f082c102c0115040e000011001000c100058205e6a0b2076000769040c20190784070f90b5460007081c181c203140c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 142085224 1250 142083974 142083979
    0x120f010203010b090405010501050c0a06050a0e03031e06040204080703080f121e0f07020606010f050910031b180e060f040204030317070809070605090a080319030c02060c16060605 79
    0x100020b102d004000080001c0c0130140d500b0f100310ba9030345005507100c0c00f401800603110b0701700d1700340640018441d600951340080200b00c001455001c0c02c03501031860b00300b19228040300304801000314000040f181d02640c408002c4030b055280c41e04000540d9141d4001c5d1000428040012a076406604421401d42d0401c0e842d003100c1c013000e8030300540140198600418403d41d1003049502055240c054000e000388100f184d40c00410094440c00f00449800d40300508400070070005001040c0709607101c9040904141d50f03580c004c11011001d0760b03108800001c5c7d40d464400e11503031302c1070407031004103040141c4202d40340414103103095038400c004241d081c002200100e60207803001401104154219081200d08243c3e0782003242c0035a01c140096407803107400d603510f07540380c5c0c003082d410040700340720703100810304d60b1000340100429a83d01c1080750710f10b03041840078401d644082c3c40c0c0d9220295052117000a0402180b00038001410301c941ca01c88244188640b010304860028104010702c02a07400000003844003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 142086330 1106 142085224 142085227
    0x21506030c0d021012050705040509010e040c0e09070807091b14030a0209190e070f020a0b0c0d090b150109090b0f09250906030e030c0c120f0102 64
    0x803402d0040170004030f02e0146500b59882e014680c020240750320345c60f81f40d605040030800d249505802c001d104501110402c808900a00000b41c203c1d1011b0110100680380c0031000c80c104509030304801998400c0c43c01c0000c5280d4140d110134407291408540d0400c001070351800f1517030581c1425020340c2104045c0045650580c40d03034000c00e00803800514441d13078540c03981610442a0b15036840001d000d80c1400c100600c480e01700c00288280403551021b000f40401d1941c3e03076042418007804030a00e200700441c5448442d240c40d884034007c5500404e0f001080c1c9040b091031003d45111001f514001107042100180d00000c500609545500040405410446602c1031007150b10005002c154508e0b02c6a00f01214070101480f2029500300326034801950508055001e000d64299030040000b0703038010440c1c01d1400102069801e2414011900340c6805803030707204500e00d44140342100c10100d510 = true := by decide +kernel

theorem cover : BRFrame.Cov 141906474 142086330 := by
  have h0 := BRFrame.cov_init 141906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 141906474 ≤ n) (h2 : n < 142086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
