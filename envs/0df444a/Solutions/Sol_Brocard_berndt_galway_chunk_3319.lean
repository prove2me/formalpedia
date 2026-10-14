-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3319
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:19:04.421982+00:00
-- url     : https://prove2.me/submissions/556c19b6-8617-4c9a-a1f7-0af7e9512514

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 596762589 ≤ n < 596942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 596763839 1250 596762589 596762591
    0x16170301080a020f030a140313080d09180923010b0909190f151407030b030d0c0309050a0303020d02161a1b1e0f06061318050d050702040509011e 64
    0x90945030105c1c2c50f120311803100a00101c08100795802d00d01d80040079004440015400f00140d59551803172540342d403c0c01030540c000420003402800300c00c03a500c1036000140725000002681d4011601c03807800d15070316140f072083c48404402349101000402d0003070301c0c04a101140c140c0350038206035034074a681c0c050030070b1804404081088c0c0802848158110449a56081800e81c00b0401c802a10301005158118607015081040404a40c0c024800d02c2003000d6480d0180c001c01c91150107030300a031101e681100f0f0440410010070b90210f007988440c0080c1005511980040207101c28081020341800068842c01c1c00407541c48800300036004d000c041140a00350042d085a03a14508030226001000d55560310006a12540207480841c40d1020081c07001d1840790030603110300b4004035542d1a00c400701550f00b071740e000510441b0305a05551690003101c03c0c03035510050f8041000b40303684141c242050700008401140001c1120803c0d03082038003403203034040800002000a9000d2840f1200e8118075155200401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 596765089 1250 596763839 596763859
    0xa030b031f05091507020102070317040b072001060e16110a060c0c06020a02071701060e160c050f061f0815040201110109080301090c030c020d050d090816170301080a02 74
    0x100360921400b0700800000780421388503d170940f40603020398020318080740010000800700f0f040305483d0f560076000d194000c408491645076500f04480d0203d51040b250301c94068140a44aa01001d1007a90014240c1e04101c402c207242298003680b0300400035030b101c001d100060300c0c03c441009000c103840e02c0305688000002a0300c0580f40e800c4886c06546000100310910019504070f403942c000912074200c0750001d0076284140080300f01c4500381d4a0a1203504c00c3c07414040089000d1000b207000c80000c0341d041c0c1c5040b503928100d80c0c8420b46441600030008909400020900200030000e02c8480a9030001d402468291072625000741c0d920100314034403d40d110071041c08503045a20030420800c0c8580410000e00c0b161249003040324284c0e0082c4901c500461800c9601103000f8000c0c041c07100550801c1d00a1300c00c1c90714018094419901c20b807600043d1585d0f848540c400101741e40041c001e940c0c4019030900d030004c02450b0054081d0008030324549454002d100402084000240101080f94181d80710511 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 596766339 1250 596765089 596765101
    0xa02031c020a0606031b061407060e030d1b180f05010e0f030601090b0405060910060c0f0c120213050f01051c020307030f020910120f05210a030b031f05 67
    0x42080d0b901009000e2400c00c0300000502c4100f1003030104100c0c10001c20008541d40e03100559400038902109081905c0c2403003003402141c00c550149600c11025000d4030f1502c01351044481c115100038030030416140d007000340c8280b61030b44a203c044030003d103204403003039082c10f1410744040000a840b40d28104400000d20001d6130703d6a600554003084c0113130880c1c80c1541c44c3d0125202030b20f1340c03d0f1028007840c602800a00c4a18041411034004c041860a42a105040c09401c5441d0603030301c2c4007176451024070052240011045038072880103040030703d0380c000c070240c5601c100301500c040c1025001820b0f04000a0140011500c1c540a0444104a82c42d020b0b075040c030320207241079840c61440a50305006426001041c048101e0200107504d2003111410b220395507000012100c1c00b030900448045440720321807100002c0300c03034165600b558095011261584000c100c2e110a1444594811540705008614030862a4143c05415006281280130b0403550090300f48410340550442d564100d125101e101040ca = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 596767589 1250 596766339 596766343
    0x304210e0a0803032d060904030212040e150102150106050a0c0204140403030b030f0606010e01050d0e102306040f0207050d0903150b0310050403030605120105180a02031c02 76
    0x18500c0003801032040703141e4a00303155440f50021904918000201c4e241c075040905250402c120384002c1d111011456180d1800303102541c01c0060045095103e01411801d82102c118040d0005121189403008185040d5140300c400750184c416442c159800342c400c00e20005080307840c25055402903e080c5445d194254812940040d0300f0002a401a240504121041e0426200648641d0007a141070200e1f0951500380360b5141d84103401e642c2a50403c1020981e5588118509184010149841e50070b1007685490507040312503001c0350094980c891070402c00c11503510b0090700b16240182c0081005101c0c0c0708403456001c4802001584542e56490444102ca81c00303606030344640780c1200480e0b0211103010300140c1900d04030b0005881400a034546c0c40034890a90164550703182010b006007118414190240e0060003001e0003c40a254603550049950b4a4841085a404c890100003103128100348038103008111010150107015008000c145000d6140010030392294480200404850040c01e40e00b24 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 596768839 1250 596767589 596767607
    0x20a08070e060d0c02010f060605070213020d09060e0a032a0213020c07060801031109060f040b180c1b0106050102070512011404080a020d0806130207080d110304050f03030421 77
    0x8a0004c1c50305075541c84aa50560084c44c15a0507000304002080e140c81c0c06a0b41d50040400007588901090914461a481e0760058110103180c0d900c0443c40c01040d0399014283d5603800182c41d1694080c1d078040f424940c0c8051307a140c04020314013900e50707441701c00c641d2182c4000071100060b028452420307404e0001003d1b0360480d0a01461082560813581c0c6410004118500071301c8283c0e0076000041550071a468249101402060000d00101124000a0502015001e0311285aa11140e0104488031f8048542000381c8140d407050781c0641da88442070b0703944100c0e581d00b00c0322641d00d030b150038800d0000740d03000a00002941c2e001c88241a00206175010309004d022218202c0f508e00c0c00180900040140d1500584803c068580a40742c5509210300708a80c40e4500701c8115600004c07050440600c4001c0b540180581c81c0261a0035140110f810880410f46402001d0384440200000403c801e001080c060302680041303250241d071440c20035031124420b61540c040c4086424056040903072085005120035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 596770089 1250 596768839 596768857
    0x708070206120709060f0f080a022701030f0603020f0925020d140a080a0f020c0303010e10231e18040302060709080a0b040f020d0506040510020a08070e06 68
    0x200350b0350b603016044201603102c10707680304020604c503a1000ca007090107194418002d5600c0e985460b00e00340d000d10115810716024019400c00ca41c03c02a00c5040c40c8680080704400007000c080a079204504000103040340d88032802c1c0c00da442d1174181c00f40010307507807010350021545085410358542c1c0c0710050b00c2140c1200701300602e90454051000810400c2d00454000d00141c0c4948480c0c240c08400000e5503030502c10a1030100016118400164400510780d1000d410310050b0b49005060444581c102c2c1d01d56442a0401203140300e000b401c2101e050000c0404402900001c8078150f04411001403801c07540d80043c007180d02c0340d00b540440c081c40585142c0c02d0303481107800409005990300c800040fa00980d000307a07403c0d001801501d000945103405000071000700d03034201d00245070529181d25000d4803180090421a941801c41140c0b00c0540d890180b0008140d0140010b05514102490b0192402140328850380010f4018018440e084c0d4002d554154801c5040c240644000038000c0020294810813120b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 596771339 1250 596770089 596770099
    0x7061104032a05010215100b040b030108010609090308041412030109090201030b031204032306010f0e160503010302040510090509030702090c040f260d050d050f0606040b07080702 79
    0x91102403541c000142c0b0080d0031142421000c036861042c0c0300d00d18010103015134051203000c008040d1814441e030740a12490019014280c13500d1560003031764020350040070103039404001807015020038881c40300107041c00c1d0010007884445a034040c00d02c1000600140640e203400d03030440440c1c0c42c14440d04030003841030b0f981c00d40d60350703101c42e040d20090040c03c1003640003925020011406050002c0d1400d4548400c28101d030415146a0702c0d000c08214418004000302c0070261401c40c40d0318204101c9028105044c1e0361035003241480a50302c100f0f0382c000c201e40d0864112803580d142e400e8000c01141c0c10b40307030181c5c0c011030103555071105583d070305911f540b055842d245441304125a001c0c010001d806000e20882d100e64030344c0c6998071804003902a6000b00c0c0c42c83d101941003002408034120408075400c07072213800f104e00c1156201c201801c00b441119540042900001d21942012040c071641d5444143c40c0c9010410f400c00d400860910b008601600740036841c00070f5500244100e46041e00c02095000740 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 596772589 1250 596771339 596771347
    0x70e0108071e0e10240914040209090106050a110d080726040b06030706080f07110703050604060f051303232206020601080f032b0c02060726010b070611 67
    0x21283c00c2d5034085110344014000c2e01400a14001400510020b131845c00d541c1c0c142620303013822025918004602e2600e40c2c400e0b4200b0000c0143d4940c0c04865000303014a840c0c031500d443c00700078081c0100b0660350b03030000643c008450492170990818600e90304a01e1910b001d035410301c40706140d400100204016a4040700c890420403003001802c1c00094032454055050341d81841d900d04c0185c907910415104450030148040004020074452117842c90b80c5100902290400303592900c9940c01c0040503601076401c20b441d4019103c1a042900a042d0080001c4d01c074410101021f440080415500d08440b022603540d0400f2206c810681320709544148207080340a070f100000e00a40c5032108049442034401502071880001041000440c0c2080c1c4000d01e0740155161501041ca44401c581c001e01d8640140b810281d6a20142d0700355105010344141180c006002c141070007030002d0601e5000003000c42203841208405481d1416903100300d030445151042c596100d45203482d101c40030b450f40b5071114440c104081 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 596773839 1250 596772589 596772601
    0xf050316140f1306030e2e0b0d0302010b010f11100905031c0b0a0503031312022407050115080a03121107030c030e091303080603011d070305070e0108071e0e 69
    0x10f8074810031502a40c4040041580200455480302c0f91150140c1540f038040c4544100851800380704a025150a000001c580c080000040c0190321001c8095005030744d00c0c00601c245581211859804c0c85642c18044564040102440d0303841c0a64a01001c1050320707506401d040007001c000399202c10304058900c1ea6107048a116003070040151b642c100e840303a070714118005040e08000c002c0324a040c2d241f0300403101c218200070201d4074110002204076004403040c444415499290300d81142505000140240e548080341001425079017249541d0a0600c4519410003040c0b800040720031803158581840700100c80003a060600a0038035249441522134006183c80405a00007000940544642c40e10041c030410b0f4070900501207011a07407007942c80700c80e07540030021074011169543c0c81400100046141d07001014113000018406009180c560300c034900a00411905010450290900a49001880d85083e0301d660b95981644165010b0304840240c030510344601c42c950724064164260704040e142840 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 596775089 1250 596773839 596773867
    0x507030c21080a0506031213050612010302030d140a0f090519170715080c07020409050309010e030c0603061002030d110d0f0b130b0420040302010f050316140f 70
    0x4415a400189102d03001a0708404035100d41c0d0701070341001d03000340004d41000a80c00101c1c0d00c464001139400780314030000181c40d0784050080c1034542d050b4000811552451061629029085400d40180b00b1518824980c00d070268040e641c2d10081494242e9030024070100079607511085402c4190002c0062194980312801551413204840351640501c2c0c4c80380007001c44079141d1566010f84120100580382e40b00480d071203820200d421900030442d052070020194009007c40e003010700b04035955040805d900e1356540c1c014400228080f400d03000b038006251103c1c0090418400140b400c0d106a48000700c2400d4a8402c1060f118002c40441040040a02a180c0030311325030042426040c2d55818904d844001d01d403d801074590300e40003d41146160b820451401c000341c0039810200d03411640c0d642511048420b64100c9025041d26040003566071821800014043d0024980c83d00900c10b0410900002601000403208000c1842c80d01e010301344040c20042103d8800e00d4a0360840c10008190140b2800070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 596776339 1250 596775089 596775143
    0x30e01031d0a050f0c01080702030415050c0a0606140102070b03060613030f08040f05060c030a0305220b06030709090213020702060d02071a0619260307080418060b04060507030c 78
    0x44c0b0080700c070b41c03107250300045420300c10403681500160003d100801642d101d411441640703070f030103081490034000b031544018600111004155440350b140c02041100c18500a04134030152000e00c00303811040c0c1821400001840083c0c00a4092140000d80008040303041c2d00a00145a001c1030300325003401a4244ad104c107400a001d40381000c0074180c00000c4d2440c4c0507003100e01c1109050040d50070009a410300b60300802d0010652440c9403000300410300750042c00021820058418500d50145007001d5080c5481c040054000540c828581003110002d40e4983d04950701a0366074607809680c40b003031f0744081200c50107029030075062640003140500402a0512069401900c4007501c0340140e560082000595845840121403440007186d05101c0032400028800000c100115264960784980030a01d04d5980300340002c3e6204003022038248204c0000d0301181e002d02d00b1410b0240b00443c100380300424030340300d248140700521800040000c201401080314180007a000f90640c0c110004070783c110045080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 596777589 1250 596776339 596776363
    0x18020c0a0b0118060518040507051302120109020f070807030e0a090e01050901090209060f01020c0904080c070801021e03061c08091503011202010f02030d020a0e1309030e01031d0a05 80
    0x481c00f0b0a44400800030f105010448034010701820b0014041350b0010407402002e4030a590314014418045002d031034400d0312000003520358000607650300140711268586003040e000000d5990040040400500c00001a40c00d0507800c10250f986e22180351400b0b49100c00314111642e0000c06114000a08824a40c01001c801c412040240420354070900c4040c201c40c044807000790700000450201e406801c0c02880b03d10509810700403610300346213200002e402c00c541203c0480344141c0009030014614014005600100b00c0c240080d0f04044114080c010440907211030200f02d0032010001501541d40e2492840314102c1403418a0a201c15900303040030707154809040f10b03000b4075210b0301c045000c095036811a4100c5503035810f9031181c501650700441d0b0b00c41551550204500c001d1011000840c601d03c01006115a103407079441d1342c40002028410740350f1515240d00da29914081c14080466007082102004604c240390001c1e01601490034080b0001c0c0c02547c050b298455505000e041100000700004244 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 596778839 1250 596777589 596777609
    0x102d0801060c0c030b270109031412040b0a020919060e12060606070f02030607021f0c050313020109080703200607020a060c33060e010f18020c0a0b01 66
    0x40e03220101912a01c0c0060300081c88601c4099040001c18606003046810490350490701c3c8001c0074946d81c04000091020224661340d541d0070464080540000001c3d1090514940c074904141c06004052204140100003130040c00e0001d0000755130b0441c641c11035100100080004550b01400da50a104d4881103000d07450103e00f00e6021601640340c030202e18940100c22070005c180655440f400d01403035800204040f100c900c00f0201c40b0b00166000e202440c42540542c0c01817481d5100c0c00d080050340b0590145251949144c5088103058503801012294000b8450071010007041c02840103c54024231584044918081c2450100400500510303001803030b8252000080040c0221042000c0d070b22440354020350000a044c001c01280340500c4100392294010828000c40455000d80e0184c03201513101c01000301101c05461001200f0184207080c080c111a03061800c4645c14036060034444e030b003207004440c44210740e20656480212160125500b28404005030341413641180380084644400313000320346041c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 596780089 1250 596778839 596778841
    0x210c090f10050a05060904020d0921021c08070e0a0801051515090604030b0a110d050f070f02060606092403010527072618010b180105102d08 62
    0xa0f10b01140f003042540d6000703141e02c2c9031412600800000354800901082c0040d1075100c0980072075000d8050380c2c0e5800c481c401035603110000b40e4000f030810144580b004202240c0009182c000c5074072142c825400125414081504890780d400101200c005030b01c0005298207010401081040c01c40310000110340943e402940300d803c54005a0240c022060040d0308110305120401c0491000c034030f61a00401c0c00032000404003042d01090441c0d5200751300c031651a5480c4c1c001d000e000e042030b2a610742d01048515284420100007030000b1348900d0040c007801d2007914046120203039a81c070000e1a00c00d420691101d036449882481c1184c0307003a0030904c01d261040720500207010130200c1c810144040c0b17032040321840c022580d9861094822210401100b400e0320b6104c3d080f02d000b4241e80044501403e5445c07060200020340c0100d160a58084a8403a4011030280c0b4220b00d04048041c15941550320440f80007854403100d150403200c049041c51402d40380c5c000c03e01d03051002088084c116142c9101550b410f191 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 596781339 1250 596780089 596780099
    0x10b090c2101240c171c05060d0809040209042309031e070804030b0a06050a051002101802030616021018030c0507050a090f0614210c090f10 62
    0x103100d400744150310070070074403201ea0444140c0b00c460000203000309041541071507000b17440f0b411000b00d0003030340035500000006403c11142e00e00c0c500e00c80381024249081c844c915021011072640101504014001400420302510b02da807103030151110010301820401980440c003041441040100034100051144030003c0f40140c00c000c0125000800b103044101840c000140c2c206105502056040d41d207040c0512021000030700d04260140242d01d01000441c005060504028219009901a0784200000d0300c11603c6150080380c80d10040d000b4520009200c1a00c101c030301460382c10000300942c540500300c1007042c1045402414100210705500700d950381c80d000718011041707500ca400d1084d403900000703030280c0004e4410007030151760a00c12000d54035025071310f5001c40c0d18944903801280c852a240c0b60000e0f40030180b40300701c1006040c010002d01c00340c0f41a4012807024a42d16024004808003042e100a40080030801d03c0103004000d0408142072424890841e50b4590684240c0c02814101c0c1001030703 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 596782589 1250 596781339 596781397
    0x5060a050714070b040c0513020a0801080120070c080706020303070e06070b060906040905030d020a14071a04060908031e0f071b030318050d080a18060c02010b090c 72
    0x1140c2c8120b200e0707450510030352a4601d20a4005004684104001c40c0104d2251100c1d020b0030346150320104090f071036403145030028040d440143c1008506a04d015040d841011014040100032420100300c1503940445003000c030240125900494101d1080c02c1000a0055001004602c00ca00c0382c1d98019144050008110b1544218180501805102c8002c51003a203800000301d90840e800600008806c03030580d41c5e0500b141c03c0b900400038503036030108200ea4101d402026102031024080105172810201d680c3c0c00b50940001c0e0452048080404009001c0204551084c0c2c200c07500030004035164a0030740c560f8a03451000341c08001a603c02e10011030130b02c001915036035002d140c458a4804034411507500440c04040038550603001c2581b00d264108071079420041c1c040c41c4078000e01c040e288060b20041c016020200c094500a034141c5440301c0d640003c12000510060b0381d03804a004510680060701c12400740c140d803035031540d104800d0710034090f02c2c881c1c4400500c041103007240104200510030b0b102ea0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 596783839 1250 596782589 596782607
    0xf110909130f0b070c0c0f0f0902040f170a061b141309020f0d06030f0209250c020d02060a0309110f010507060e1608030a1e050d0b0105041205060a0507 67
    0x380b8462000c203880002803000a0069405101883c05058140803500d41d2506c078000c03a4040d1800c1080d810003403182c40360100c0117102601c1000b00a40c500b17442c2100b200360613070880c4258000c0440590380f001602d8800d000300c1c84601d400400034402010341e802c2c4c0d802e4840c500000b28020820400403000e90314030315419a448680510b080003003440c50042020040d6005158401c1040410800003c80103018461f20b40a5400b030140504141894810701660102c00341840124013040300015004101e00b80048500107101c0ca130010400c1d07010720200781e81102e5024000c0d030103000400e564425a91641c0000c3c40d40b8054041480c259402d403092103141c0c198510480c3c0080c2041003000c001c00c40d41c0d0050344a0460f000200d03450342c52102c0e01902d1030380b02d0750462410b42d000000c5510245501c01105a210035000440502000b5910f00140241c820000c01e410025140c0000394800da020380305a60051044000c00d142d25841c1f032401640f140402c0b04e0165505203400c1c0426100384c841c00000d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 596785089 1250 596783839 596783843
    0x140714040e0a1b050a0807030506090303090601031106042126120603120c1c0201230414030a031d031e0d0603021c02030d020f030417010f11090913 65
    0x16045400340e6850320180d0f540002501640100b80880026041e110b0030aa24002d03e2032070041c1c003070b035030940c070f08075003000005445c4204961050080c80301440001c24000e04581e40121402a142070b02c601088860040c0c0d401104140f20405408100106241980c0b4040b4481c0031000e0f10351200c4510008911100041c600b8000c0080c080c1040740c8014058140c0c00c2032005040354075a2420400c81342641c0e01c48038100203545c00c0200040c0607030a14001d582141551130009000084640c5071110a06024001495140f1101008101840b500d0682e10b000c00c412403080c0c1c0ea032582c892202901801c4c1c0e00694000225001189001440c07000c4240c1d10178200b00c503894041c40f030800b015241030350840c903900048541e0350680000165100b55200b200d144070482c142c0c409002c640109800c120f03440101c3d9055400944504072101e10220455040c0c6a00380140c00c260359184003040d0050003c090015022490078149a0194102c0f40203007412503c00ca80803811541c88144188020451105c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 596786339 1250 596785089 596785093
    0x60204152304050103020d0605040f1512020d03140702040617070602010e06010522050415050106080402030606100e031f180c05010f051215040c0212070f020d140714040e 75
    0x501840d131094001f044000c20703d00703001c20b17450384400020b0304944c00303214242046982c46451070b0b01103009500e210020011001c0c1c0c5c1c10f092a1980103c3d142200a1900a04100c1704446030706064007951301362031556030003810420005440e1103000392900d5520100c203006205143e80040c0b204d00c14000d4616014094025085036480d04052010b01454a08041003014014400c11103143c1584156403045000d45207001c0440c41425540303040314010780001041002c01070410015031070000d0b00f180c2150341034903555181013004004462101c00c001d000c43d03043c0a0080340c10421281c5880d4512143d01c0b0140030010403c1d112440049004a40c200800002d0369030b500700210343c0250340d101400080f034207180d0700c0d00f20341c42004010500200c45031000c0e0300c2c0180c41140a03003451300c10b025240c0d8481c0000c285030900c80b800848140a0008010142e00a400d807400840d15a405500d030f034160f111864401c40f0540300941510340c54a8091145e2914000c0b028410f070745864010a400f200708040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 596787589 1250 596786339 596786347
    0x30e041b120b0f030a0f060e0f0c0a050105160f17040b03040b0907030c09051510030f050a052403030c01090312050f040b071d0a06030209010207140609060a0c0602041523 75
    0x86e0f5154085032240083c0c0325640e4802544a4046060024691000e03180b40940441c0b80088200840c003034454018904002c0d0500031282c0e0f140c00e6000300f101154001c0841e1203070752524030f0b20b03c24078903040f18850510714002c10000b905254210145004a21544100b8038940d24a8000c56669015105c054800d81c40358008020000280d40310366044401d02c0040030380581000f0108902843c0d1000520000341d580300c0c5c030146041035110341508000d80310713014811030500343e004403004040c1000c28001036002806080a5a50070001c0b0f404910408000313024401132810050040030b0501c40c1c0300d46641c104000103040d580081c0c03c1c0c922503680004c0c1c281560305d0f40d0b0022030380d000741202151103568800e490340f00140d84102c2c4200080040c0e940141ea14100300c0002810980c503540710328040340304040e45410659031403050b22800c1d4000e48030941c4411442400311070721901c5280180803075100080110386d88213445d02c01d802e10002a01d40741c6820604d201c4030442d2030034805030904100020701c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 596788839 1250 596787589 596787593
    0xc1524011214010f05130c0f050a0201020c010507111b1305131506090606020303150108091609020d0614030d110703080315010906050c0307030e041b120b0f030a 71
    0x80d188001d032081c0c99800062080500080740a850801e03045400c03101d60608040000f40b501c01603506030842e800c8410310484001600140050010b0304407041030100100d40c000c40b0318030075410b4039900c0740d61030000c2c02142440280606043c0b56186070b803170140940500ca20b414440e041e4040d1030443d014100340b058035170045c2560001c090281c0795002c40c1583c40c8100d0080b03002074814214403c031420002440394944080d5104980c0d4a9003c0010354005004014a410514403c141c4426080c2000c84260f6500d4484505001e01c0e01d045500800784c105000c90415034075405030038420a002410080140c13203203129004441c03910002e99043d4000110004c00621511060f141000c0720310803a00d0301e03a00da503141030b055001101c41403a10040c01e5941a01c1d580c6c4003c0c4003009284074140715141540c00025203842e841034034006401d011840002d540c0e6901c40d580900e484a440103000d030001014904010328009480c82d1604c0e5180c01c00141e99941e00c0c11001d09000d060000300203080e0b4814030717 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 596790089 1250 596788839 596788847
    0x70b010b0d06031505061921080903030307020304090b010801120f020f0d210c0215130302150a02010b0901180519022b050106052d0c152401 62
    0x262008a200c20b8641c1c400000040c0d201d0038074001c01001c9140483c107458104c00307105410b188240d4455034030754008000c000b00020120b450070305002c80703c0c0700c0c29510418141441e052040101082d054400002002211607000c40500241c901d441000e1000010b000c004603480c1000380250003901c2400f0507001c1c002120b0301c4500012500c00744c1511041c1d13040c5030015070003802c40c120945092542904449885841e103000421862050421148000154002c680d10313030490b0b40e800c00244000980c0e480c1140500700410002c1d98010824203403482040d800e41826040840700c4130140d8280311594075140382100c156070580303440390f00d02c402425842c0200b4000e85005030085840000b5007910f00d080c086640010b18a0101810110010356510f000840548054403604148546400300501860341e02004a5003102c940364403480380b03c20844100c01c0455100340d034040412074005061040207002094010309983d0020b08055103035595510303070303400c13041e80f1000c140502d0110703000e62000d42c01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 596791339 1250 596790089 596790097
    0x3060b0a200f01050a02040e0606071718130f050f090c010e01120905071a0304030906030b210c01110a0506010306180b0a1e1a01050f1215010201060605070b010b 71
    0x251408071804102c0e1010610300b158400d54a00d00a0360f000507042c801d90b28240c40a98100c41c095401514050007034903264030740034144d80b108032072480000d4064564481c003a0700000f0741400802c4409812052641e01c0c00900440041c40c032400e0418000403034140c20041e40c54070904194002c1c00c0100200d100454076003901040e145d0621800300070700c0c04102d285100d1001c3c103512a07802040700301c0c1492104240052030580848103800308004020001c1d81c010710020803605241008928683d00c000080e042451411041c202ca00c00c2c102c080861a000040f2000119000e880d100780141c80030480d10f072514001180070300250720000042000076495131282010304d1400b80c1c1150b09620f036980d80e0395880c00c26a480d807244c41d15050f1031001d6583c0195140c40d40b810401081050002080c0781c1440c038094404403605000b004900040300b40c0c000c40c2100d40440c01c0c900d441107030b4a00f09440d00300c2c0d642a044c48900542c604030012907040e001d00c040320902c58024002040d660b01c1c0c4100000d00b688 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 596792589 1250 596791339 596791397
    0x7150504140615131d0c0102060921031803120123010c141f0203041502090f1311122d0a05040507030f08070b0a051003080304050106051f03060b0a 65
    0x80c1c0c480c501309561040036080d8000060a00c0a089451346c21070009140c00310103808020103030407400f040d41d10b041c00c180c0b045507108000070380940c40c7d0340c0d0540100c00000c1c0300072280034140000540c20210584034829141a82c10111504501d140c1c196040240007411b0000180072480903040d96001c00c81c2c1d80702148900d034090089842c802103076413448103200c203400c80444103940c0100502c0108031340180011052079014404504004204000803084038107038143c140551980c080c200350006c03291b04070860881d81d00340215510052150109100780d821204443d540044514602030360301001700100e0081904006a0719644400e03020500600015204807000d2007010380000000740c9004d0750500150060540903240c005900f05062a0480209120031032440c00c0c04002c01d000f640302206083d03e8206141548954440c6001401042c25820042c0d01801260103222818600e0f80e00708850061039506001d00c0d542c80079024030900580c690703003020a10340b10f081e481d00c06044c10301d4000700c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 596793839 1250 596792589 596792591
    0x1501020a020d050c06270d021305060102010914070509011d0103170c07030c1806030b0703020d2a1d0f011b0c170d080c03011a0715050414061513 64
    0x48456400240d00d0790110309000100503040b500c11906c0d08401c1c40c0304078010001d40345608002074940c001041c0072102c001092486941d4404550183d1007548990407007a800400704c5145500404200d0340c81d501445401c0c440c10080380041002e900008412803458440400030318940d00356034405d00460010001c00440e080c050081c060000810081c52000311301468065150790700b000540039038600720004440b14dc9040c00c82c200b002405403030350180d001d00f223490016110f011140c2600d002c1c045495115840c0c00030039a4144220182c6001507a0211154661184a50305414600740050601c0314495100d8058071101c1e40c2035020303004d0406003078148445071a80403220b41e0b07400700400c00c1d50080740c120940d4025070343c0406070400c20301100c01d007203050078079143c94002542c1c0c00c6403105000c0c034a00d0f00c0d0180780d500b0104900200740c0d2520782d400742c4044000b044100d0858000d000c100d42c180c2c0c0041115450315009074010460702d00803041d15204500018201c001d0104901181c0b14980100f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 596795089 1250 596793839 596793853
    0x3020a050313030204050c0a09090c03020408070914061207060c061d060f130c0b0a0e03060109090c0b09010807030b130603050a020301060b040b180d0f14061501020a020d05 76
    0x184040c40100000e400b4a00c107000c0807425030040c482102d4000b028120b0078581007080600103a08985508122440c1440102c0e1804004a04a0280c0200d0384001075a01c14154081446403440e0003a005d22005001400f800c1c1e0f807688104000130a0541b110b01407500303c0350050001e50300ca840ca40e01c00901483d004104c07801504000b80310390500ca541e00c00260051418486107034001e554454010b403003007481c001e0380c00c2180c843c40180c01c2e00e807180641030311002560814450083d03d51008000e0020140c50403580d5444001001c1c00380c41100300d40080b042903020034003980b0346090b145c40c080c060303440c000b05544040c070a500401c0c043c1441d0358405209075421000082c680544c0002d18891009068500568418107003581c0240d000000d40c10b0781444207024a02d01c038402c3c1c58002c0300c5c21300307481100000d1001090b44c81d69000800f03001500b02000d56414400c000b04a56080700d0f600b0115191659040b0003096015140c2c0b41031030042c0c000c920510003520340203a0342e0029500071400d803405 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 596796339 1250 596795089 596795093
    0xd020102090607060b0f0a0305300417120301150e15070f0312020c030d0f0c021c0504090c050307020c040606021f0b030f0105060108010608040c030201030218030604150608150a050403020a 83
    0x4d43c0015074001c84055107c0c0007000c1115040c4000e84081d090040900d1802254481064ac5640164007555003e082c0101e02c1c440800c0042216500c1070300d41c4e16640b956940c58001440940010a10140102d40000d055041e2820002e405490178040200264108079055aa40c43d18400c0390b80b040d0104030700340b0042926001c0320f20050504520200c02160782c1c03807080071003800741c2e10603001d0740d1982c91400601401c180d8000c10741c0d89800c030343c02e0015001e00e0038480081d105070155130000c6114914000c1d0401c4400d41003801180102d000c0d4084800d004c0d00101080300740c540c54055400160040c031340c0c0c17022a801aa9503160540c07040c0c01c010840c0d1001d580424a40841c15940d00d00681d1514144103a40d40c0013203d40717000d00a036103020700e01d03031a03c2e80380c5184011003480001d04060380050034201924418107500c42e101d81c01801e451550600303007010305c0207801000360885450316100c0c000a03004000102c030250040c4482e064642c1e80d441d00500c0004001c01003007a000e6026407406800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 596797589 1250 596796339 596796349
    0x140a05070602010c03140105030601031e0b070314180c19031403071a01060e090c0403061410151d030a05060403050d060b041409070228050d020102090607060b0f 71
    0x40601069800004c0d000c001c08030003400d484a800007041250300c414014000f0340c0b4007061940c1541d40010001800358034804000e20000359032807015000000d01c1040c8103003a60316412602d5414060b0903e41425110f024143c6150040751551502076845510f034582d482c14030385040b00000b0385d00d0130441c160650300e848a940d4481d008030a1110750708001409402c01c004141620005006407444610039810301030090f0190303002c0c40600e07124662a0f00054031500c5100203e40145600820510120040303448860026409503080099210300900108070201000145590501c071a95a4001411a9503100010035001d136603264044c05004054008a03408101e141d004503c6a0703903450b82c0da869580c1d040d00725440c0e40c01249039900100700800040f00180380301101c3c0380f800c480721115a00c80020603481c20001105e025282034500761104144c1084c950900300d40c50040081d00c40c9008909001c81c206c0c410303a98910341c08401484079102040540d8800b096441002d440d400301340c0c180c040003403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 596798839 1250 596797589 596797603
    0xc19021009030917011401090b0a0b210a02032703040e0c0301060e0316051210062309060108010b0309010e030f07021c080f0c070302040c17010602030f07140a05 71
    0x5408a450f9500801440f00c020a08a40111000d03008104c4d542c0500103a0524050602c03c0d5007019031a5401c0010a541d140001c0000b08868117125544401c00d02c1b214480c200d1080099a180b202400080c40c0a003003402141d2149005109040c5220000c4440300c80341c0c8150031010b02d03a0b1006000201b00d04002091b1280140300703034900c00342c03a0b626156000b0241c0b101d501c3e20034060b4000741d82c4040c944d903100c1810f6050715030031944911190301c02c43c3c0c1189070948031310b040020f1505264002581076058084007000c1e40000390455002036440051003907054050f00d40d54006071154004000320a1300c0e001440e0010105400401c01c6a22034424518641113100d02000e100c400060790b104514000e44410315501074503005c1c44083c070143e203403c4518054401c1c044090b030740c00180c0161503032051000101540e0300500400007100c080d01e000b401c0854040c24000300041500011821b0782c0004190740800c40a428201c1c50851180e49500c80110501c031403015510850305160000b81c0b00703112074 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 596800089 1250 596798839 596798843
    0x2010905031204020325050409030c0b1006030605040b0a0603020a050d0e030a0306140d12020a080d020409050c1204060b010c0b0a0c0201050a0c0c0b04051f02031e0c19021009 77
    0xd02010b0030903004142c200002c10108032200da03018144001b150f800d8441d03100071250300711400521068181400d64a80c0c04c0c2030f070001e2000116400f0800d02c1101c0b00c400400344e0b0030545c1c0400800c0e448400380300849940f442c0b903950080fa000810081c80d8483e8005140c001c0c2640381ca1418083c11540e90016034541b18110515508007040000c2c04643c5445840002c0c24a02c0d0020202501030020841020030306001600300d4501c1c54040d520103000700807071141071f40d21809080e6034408000d0f25500940044c001d84400905180205481c01c440d401910166141c0170b0000c0196200d595800c001485458061030600c83c40c000079030b000ca014200b800d0700c40d0b012500041103000c8090802404c5544c010440c0070348901c1c1c021056052a4010800d07618142d010380061901d8036642425480d00c14000c51b424a40410542110f440c1a0b0b2130b0040c40c050980314a40300d44071420b4226445030b4402c11245001c2020061000320b103202d503d140380701e448142600540d0300c44c4041d4180141078810500381 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 596801339 1250 596800089 596800117
    0x41e0305060606030103110d05030417010204092f0c15270d051c020d090807050c03011a040f1d0a110a030201090e0a0e030a0305070807091a0a0201090503 68
    0x10014000c0520005a1044084074a03c3c50343d81103650308111411a035001601903c1085a10404c00008000300c9000e02070b14140405520b030380041d518080e601c5402402a41c906101301000002039608032443d102548904540c02c0c210070000702c000c2c2c2d40000015020511400c000c40007220a0602c84d04e01490b1404081510b148403806210700900b58600c054907568007060301c1104055020007940d4100301003040c0540748210000e03403c0c0103806000c0c1007180e514648000d500800036490014014188244195404042c0e002c0c101800c803503000b8140c402c3c801090803120100e10b407992010410740400c0100088007100ca41041c208503080e50046001039004120f4042804108014950344003011103801c6442c07800c50f0f000810a558612030412082c0360b40300461040c4100d504628152200348048079115219060000c01034901901c440000c900440d012540c641d103d0b210943c20b1b500003e61130620115201c0c2800640c2d4232200010045540c1c900d41e90001507801d0001b80342035910402 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 596802589 1250 596801339 596801399
    0xf07120902220e06010302060f0c2803080709210218070809012a0807090e0408070b010b09030a020108060301020f0f0a0806120a03030518060a0c09080106050f0d0804 73
    0x401e01086495550f5600840e82c400001040107071b9420080b2081451080656a00c41b0064000c2a2500c1c00802003101070200500c0e0805840000103008408140603540d000e007152980c3c0025120040c0f107000345d83c2001e20400c80151215101c1c8003458240381f000d40001074864082c2d0300c3c4200c80d1815614140018510824040029024084d0b41c1d05140c4619115201c460403854600c0c1480c24103d24005010b005400240f4503404ac102c0e420080a0030417515216181515140c006507214080071183c0d01c00100001c0780d40d40702c0e0401d440050074060002c01864070030703400541703500700c0003851103606640030414030308554000c05c0070742405041c41172403588500d823100001e408013100900305401010160460700e00c80c41c000510f02c0c0c4203600b5003000100c0b0f407940b590101c0380c40076400c6c8000c9a0b1040038148051145140c3c00f44512404558807101c01d103858485036400e890f650f10509902a038140d45c00b4201d86040d14000041921400800c0d151541e107200e00008000b020b000000c04001980d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 596803839 1250 596802589 596802649
    0x30703200a08010e060a4403030402090c0904020a05041a091302251a07020c10180906032607080f090414160905090f07120902 56
    0x10403640030a010100159040c1000c04000030401e00051060301c201d0200100030a00b0341c0c450300030301000f40503034840c1700050362002c040206800b5100783c2d0b402044101540002c0190748542c201e40200005400514a1a100c2d0703000c005000d50060003482d0b81d039508100e10100d5596900c02081e450a90382c6030aa26949809918554182c05c048020103014080064072030603961613140070000c01002400580350f4201e4240c200e403d100c0b0001d0404012a180340c0c1100744840c14035840381c10820720b003080c40d140d034544104a1f110303145104541c1d08008218854410940114510112044810490740d2240da45a10740e406480c02c03030f070098503d03460703c1c0300102c00740c0c0d004103800b0b01d03c1c04404085403800340d00780c2c1d0b00805807160060300c622038680802c500c0b5103952250840000b03281c44101140e52810300403c1c54000216615960001c076207406000a450708120349060b200c0c00101003100e2840c0d546480913110044c010442c0c03002d465564100100582d50030140e03410380050155000754400c058 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 596805089 1250 596803839 596803871
    0x1b0d02100f06051f031b050309100c050306011b1e0b13080f03091006080705012601050f150d0213120f0210030902060304051b060307171b030703 64
    0x40d007220300c1c00c9062080901898440b10308403e84412408118110201010f8040f00101203480c101c0541000300308a82003040d0303100c8044c6000d00c0d521420359411b41051764840c81214078101100c008100c00788000b603401e43c00703111451024146c0d801002403500ca55920340d6400400014007542441049004c40c0a010319903500d6940304124003056144403016484600c081d000325001080c1c0f200c0c00100040c1a00024040c024800041110611500e905c8202da541c0301d1a4502881d80042e001c0c903030f010728104556488000c5010040040c12581c1d0a160a12195401300c5000302d400151901c140340c015002d400061480c0302c490345005031184c3e141c501594071017800c0d50007001d000b07001c110300b240800c0c04460013000303442e412644005c02c040140c0003580946407480c40650301080200030001801800b181803d54414214a81004420345104100e4580010f603012000601d00b202051800c540c882d82241d003101d4500307001c41001210692004140d4000c4554200094031010207602c10714003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 596806339 1250 596805089 596805101
    0x90e0106050d08090d1e030c140307021302070201110f0c031b011d0316080a06050c070507030b130605040f030905060f2d03040804230f04021b0d0210 66
    0x42200c402010040540b00d82c0601c0c003840d8501c0b0311a69042202c003041022291040e000b40144508030111118682006003901c410082300b42ca408400000c0803d41183c080211456075034007c0031200b08040b50002c040c000e402200003203040c001000d0703900310304000802464001c0d440103001411108013100a041c1004403a44407854480c040e071500481c0b0384c1e0008200c8181c0d0010092041e103600e40b00300002d150100003d42c15055010940003c100307042e001c14000c809131302542090140c0c1d2a4814010034901ca04c6a01910a41000030103000041d205003040d80c02400c04841c2a0481e0030a417290000c40d01c0c20350b4200e801900801000b02010f402c520307120300800c001c50f552410700e1480b1410441d2441021030b40a0f10280746002c82541d91600032048415407504011240c0300d203401c3c90588200d5110b8007800c90442520003003400c0344030040b0681e04000c0c0010301010f403010142d40a000294202244ca0464201942690700300001c0822414164140e01c0c6e0051201d4400c14a2113411245 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 596807589 1250 596806339 596806349
    0x20717130f0e0c0924040b1b03091f030f06090504030f030510120212060106020303061207050604150e15030610020118080307051e030412031a01180f090e0106 70
    0x880c2c010050541c01c441c0c10b440c504501529524001c1e010081c04202c04481080046881c840c04100880c074114400050841c281c02c2d46070a12603c402103403600d540380111107400740d02c007a90381ca01080e08001c001da00d0740f0803105401d010032a151903244107029511241c2042813540c2c2d8410800007450383c08040840901d06900b4204082d007003480c85800c1100c000e00a111100812520510464580580e500e2aa003080b0058928958403140003d440c0d03402542e05522807004100001a101c0c80454980300b01d4200425646c0b40a04e0035884000400e00d4032201000c0c000502e4005195465803081c0e841120f525513407680ea28a091010410381c5100c08039104210381c503050780741c2d0100c00e02694480c541a000003074151640d5403c00708849604c9103000c0200d00d404c2501c0f0851303814410502540c0501d1241c1940038410851402c100c0403111100303244148044165261141035005070140400f039005015000e0310651180b00711100700718554000035040b4ae48404c42c08603404280b1a00740a04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 596808839 1250 596807589 596807609
    0x602030a030b24031b0c0615060f040e0c0405030a050c0907030614060c0c0a06020708060c0712110304050a03030c02040609020405060418140411010914030d03020717130f 75
    0x16480c41c0490004100c5100700c6049100000082215040030300311604007103080780784456a071100c3c0c00c0040e45a007030650301c142341d280d014211001a450440141c0d0b0141c001c03245d0403400d051901c03c801ca2007220140800713100050400010400e610309220a807640f0f8018401070190701c26550511104d07030300041c8160109441c192040c008030340342d03403031540040404030f841c03540f540c0e0002d00c06400d06201800f4146e10860303020b000110540c000c1603c004507088542a030780c01c0e98401034074001511902e4070041c89000c81d010780d01000c03806480451008241c01c000c4034285030311400807132901800d68006801250501d4040821850036000d15000b07001403507001c1d810980741c0808104503000c1da01505401d00b0015450700e800400c29400303142d155011040740b07041410039091031494400390b45100e900140c880e0b080442e80398800220072140c004003400a00c1c907140f050030210002d420508040315807041704124280194071800103082c0d81244401040341070781c90700c0c02e4940301417506c2d4041c14480c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 596810089 1250 596808839 596808859
    0x916080c0406051b03211006050f0904051305030c03040e0603071202010f031e02071401051b0a02010905070f0f0603140a0504020d06050a05190b030d0f180602030a030b 74
    0x55507001d070503070b1162801204c941c045080c1c4519402d0460042c90041000e0260401084c3c5288048448507030048842c005540c10440d03c401046480d8850007034012003034581000ba1580c18201548120340c482c10002c0c810352121550b0392440d003181c2c00600001443d900100302407000c06107400d2000d801450490080444034546000d005504401034030107070600c0303100804c20ba0f819020350440da910122000c8001601001085200002d410840701542c0130041b00e12403101d45030701442014050825810a07242c0005815584400e9511210f0003800b19500c44852800003141000000040c1801d8000340c404242842d02031040091258040d6003018103000407071250000003240d03190003440608012a10380e03078500200e0101d004a9900030200342ca0001003060601c0c03503034400c9000d0343d00201148044110008140191101400348c90361507045000b030094003501941c04c4410300001c50400d00040407840e40d20040500c080e901c0040540c00001e81d00c01004d500d8030070301e03044403400c40d52001c003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 596811339 1250 596810089 596810099
    0x503070e0f07050310030503161a06031c05090603042307030305160c050d110901120b0a0507030e16030309150806040c2a020f0301020a020d0c0c03020916080c04 71
    0x703860018201005000002002c20241d112080c060005160800112aa1001c020b4290240c0011018007078030b90185910503000307459481603c49005640c01001000324407500030b41402c001042004900510004104040c8152140c201452003203001d01066049410410040314481e00c05e00c403030b0001070304101014000650041d0a03120b18099035104840c1c01e00361480c00003203503406a042030b81d1000251f0100808c000f40901403a036140010348850000b41d036034903810050380001000c003c004080e000000340300c1e1041540003030f0344504a0b150210307072130511240090400c002100980034101e401c400500505402001a00003000d5071110003d6054200354014074800d009002e41d0f2142e0785440030400010700c81c840d100d9000b040c4005e03810510809420a8051104100c0124081d4984450b0908035203818805d50326001c8160700034042c1c441c000f40d01103607000c3c03514001712074103049440d01201503103640840d18030070215400f9925101700c90803009020408000c2481c01c0c1d60104100c2404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 596812589 1250 596811339 596811361
    0x201050403050a080c090904210509030706050f0d050c070605060306071b02030a08040603090309080d1407150c0c05010f0905030d09150e070f090c0c1220070503070e 73
    0x32020b60145002070703042d25451178400240c401c02d90640d81c000c801e5010f120038040c0c0d40f07850503002e86400c810280306403000b01007607a860103021603031981508100420400c00340110000e202d0056200c00c0c0d1880c0c8112444d1641c02c807101980c0b603289600001c9075410400c00d81c0d204481c4c001e40110002c1c00ba929003d10000c140700303040305042c4152124510300b0000c40d00d040100300c03403455100e548944c449844400c010001c0241c1e140580025421200006203040017055034180c12440d6650315010640c00150741d407050340320010446008004000b1400d05060340c1c03041403402c017800d03501c03281d07142d0980c1840c60030f4038201c02182d40c1c010716081c0203000180c00081141ca04502d00340000c21f0180082c10f050590140e00c86503020006d060100b108d84010700400c0207012341d009095100031407a2610b142d603007210140040c140224601800000110b0a81020803001d40030501e081e9030b25412410010440c4240e00b030301c81c6025405a401407003107180511820001d4015544541101d140c50ba41d050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 596813839 1250 596812589 596812597
    0x2010e0114070f0509100e0f03011a0a06090f05011b05060c030f0c0922060e0f04020a06080115032a032f0f0304020a031e0632060a1e03020f01020105040305 69
    0x2d0602481c8081400103444000d42d085202230004c1c020046109200c40040302d07540000800c600c40c42e480c07100450141d000d210000d00baa070440200c01c0995007008010b40701200828540030340c441c2000fa080c00010010000303240f040c031600310b1864403410500060410600b0107052803c0c45201804070312015281d007460021201c80c841110010f00d003907480310350014000d83c3c0010542e000380d0ba08000c41040044034043c007031071080d0b0f424841203680e10001c850101c801c1c0282d0104090042154140d944281c01c861030750400b0031605040c40c888501811076040c580225500030a03281c82140340003040180c1c4101c03410300d80612410907050a449600c0b01d40c41840d490002130b41004c4049402d40d20303803a06000207142c0c42004424502551141c1401403209207000f00c07545c604048500d0300c1240000c50284407040400e0310b44d540c0c5a990080d203c600b0303000801d07140c2c0002e003c0c03100190003c001e41701040f0004441c03018801c85030643c014888441c85005040703042d6810402444002070f4460200c0e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 596815089 1250 596813839 596813869
    0x106050409030f0f140403060605030f0715050904110a1112031e0a020c240106020c06030c030702100501091e0207020609090709030203010c0327080d0c02010e0114070f0509 76
    0x300d8659132502d01036404c1c0d914440821a680c002003008006c01010340d002405a9004400301d80800b11014203069032840c4e40e020700c00c6080c12070180d0301d100b98094400360080520007007010031120b40100b07804006410010302c1c20000784426289060011041c44490210411142e0652942c6010083c0149260034071400082942c4080000350107081d0660540381040024019218503400c11141d010100704000c8045d030031401310390b00000d18107000107051102000083c01c09801c40e43d1302e940c2d40c1b009410040004065014000010003192514410503000e086540300000b81d81d000505148100707681c00003140001d510403c12071025a4030842a1000b00d60112900b04c020355903111704440c4036079035503c000d42660814540000300c80e019045501898840b640c8080401c2030700d8400301ca118020b940242c070010003003203240b00250303942d0230250041c2201c0c000841e0b4080f1013410710b401c503030362103803451003203128941406880c60340144440742548480c6440c0d41482c814400145e01403005200d6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 596816339 1250 596815089 596815097
    0x20906030f0c13090c1511030307020705040b01050904060308190216030204020715020d0b090a050403080c22080d0207050a030809061804151a070302280213020406020106050409030f 80
    0x3d08005a800c02080d0941c0013600640ca143e840b001d1750001c1ea08000401e0201e0b099100c00900b621001042d01e20a600329401401040d20b07040c1404001d1204c07040c0d850411100704031200540e1107901940c8011881040d9843e076442c1805103d400c0c059031010034600315002032503411281412101d44c80c3c10f603601200c00582e03070202e519200c140400ca4500c0c1d166094008169100140b0b1a0f030b008641e40b11064a09000603607950b04803d0450b41c08942c01004514800d011510030210200a0400010502c44400b03103902c00d885024000780c0554064a050743c05422a078000c65410f0241305c0003000c0540d51b24002a0030340e500c50f103c1d402440405030003000045a004c100c0d03070040d41002c2103070101802c1044041c8050200000b5403600780500b124030564040110345036004041115507841c1c06a000c2c0440d0703025920b0380001000009102240000c120300004003581d1081e2072039002c0d40190720016500c44c9840c40c060b0a440d0380c1d600a0303100398038141c400c0003c01d4102032030312281002032074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 596817589 1250 596816339 596816359
    0xc05071a09010e0601060f0e010509030d18050310090c06030e070911041a071a060f0d05100e03210f0c03061f05120c09060403031202160609020906030f0c 68
    0x725900404034004654081c0c4a104000900704d034002d000c0348100c00d416a03a5041d410303c40350041d511442259505501350744001c10b180030541c031441c102001c3e405846500884c095031400028a083c1c0032a444508183da2801e41c0c0b0b08006204c0720080c003c003540c1c102031050215a240343d64541d051403080d00d84842c0c075050b1000b44040340600311806001c030307222810712000001c424455a90007141041383d40c80f01035540c00e04606a4248030300e2080390014140b81070031000109010a014034900100c6aa100c1c1890001c0102da150141504c0101610002d41c0c481d0408200c003805000000711600302c0c1100d1400340440f140121103555808844581c0c481d5a1b525071401185442250040c180782d00c454181c00b10500f03550000003498424041260305405890b024400c1c40140f16500030542d004600300010400a402607030448400f0070140401402c003c0d607803e1174030341d0314440d01003100c0c95030b922940d000031494082c1c2c0d01f5801a6040d0004c2002e103400c0d50810345e658002020081c410f0307070425 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 596818839 1250 596817589 596817601
    0xf0112060b0d0809040515090106050d061208270303090402210405030301080c1e151204080d060602011a0f030c06040b0a020d140706090f0602030709090c05071a 71
    0x60440000c49901820007001c2101e83c0c1091442e5070000f42909200340e0414010624100380040d00019102c002041c00c2c1441e441c120040e00c069000c0780c4115501070315410000f68554214a41e18400b0f401101100c2c2e45503142030384010b00305544000011418501e08951400340c4001062f03640162041c0d800691f0340e0a42d5840004420904020a9100d681345041004024001c0040c0d0304884080c0200c03003e001c40c65040040c0410707078007004c0a003501547d200d4401441c0098a2445890070561924a0080001c1000e20000e00031a0142c130b20240008500900020b5882070100410152008001101050868100029981081780c0c401c10400041c81c41d151341c20320031840b04002c0102540c2c0c2d229660080f2101a400c62080b020140c0a11400c001d04140a005204450602c001002e443c144050382c0b0140141510745050f240000c40760210310000d0401d100541c090701403921801040d03441c3c6490401600d80200140c010450140240070000e40214a50126980700f10403021182c0e54003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 596820089 1250 596818839 596818841
    0x70806040f080405030f0f010f14040b0a110f21130b040201120218030c0d0b012d0602030309061f0911070219081504120315171f050f011206 62
    0x4d4000c941d050161015610411800103030500d09854244002c0c0142d0f1403c8101d6011506c42c02c10b1900c9001320007000400107a00c0d1004142d0018500c10001810816603408600541045140a0f41d07000d00181e81805225402803a00a90b500140710b0800c62502c0d2204500c00da0a00714000d04a421081c0031404680c02042e402e200400301c2c003421503e400703100c0c1e2055803036400408c2d038070b019000d0190b21140c541018140a50140d070820710300003840c0d10f013160004415402444240b44d49500d0340d130122011408403c580c00402055004503140d0400c855154149480a480c0701640708c60390300300311100c4851900d0982110104400040d07a046501c41d00d0307050707201d1900c000707520010381210540c031602d00c002c0440513204c0384da084410144a80b2400f107070100e010366014112100c06820380d01d00d1f0f03100c1d4224001d10328110384c1002040c0d64400b10503204140003411081a5003000c08500310741e62814891078058980380c241404242848001300b06841e0060003000c40034503100341010140704036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 596821339 1250 596820089 596820097
    0x1005040f060e0a0b1305010510050307032315040902030c0d05010603080d0501150c03022a03070e18240606071b03030e0f03070b0a0c050f0102070c08070806040f08 72
    0x800706003020700b0303d00420188002c1c580440742500c0380c3d1104130f01c0085d82d03415120b494140c5d04054034116104807c02001d0310300e81c0008060108058039030300720b51250f510b0321041c11080c0c030001a07856198242200c03000c0654890001103070280d40b919400c1405a41c0014015404850961300c02c040c24545062443c090020f07500050143c2200147c002c0c1608999800641210414075121040c07404c10b40044400105810b03020780103030300c041052921210b24045c0c4c19600540500340d181054010b501181c01d0000382e03805654800c0032102040f0000e800030815010009086001c4c106600c00e45010780e500301c00a0003404144444103001600c651180e004884c8410340140d94113805a6113a45103010000c4140011400154440c40c42d0046040100c41140c840c08001c01030700b02d540c100141c0310125009841001c0030484c8013821200450303024408198041000c4001590301d5485041003100a20907a000c10b810303510450741080107100100b41c140d0000d60100e180050301045007440d880d1801 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 596822589 1250 596821339 596821349
    0x30e010c0e09180f0706110703080d020d2405100f0203030c0306030106030f051b0103050c0d0b0f0a0f080c0a0602071701200d0608010608030406121401080d090e1005040f06 76
    0x100d1000380c1615200001140c204a846e10b40d1510501a445607120741c40e2403c030311004043e50401e0005201d51245034000d49444000d441c40000c40b042d010136002004203034003603120320014181005118600b0f00106c424110315103400c000d0076061004100030760f01c0c400242085040200800403583d6583d0070b4214000442c2c1040e0802700342e150340d09140c1d45030688003013500c00400440c80140c103a075009008562213006a50100c13814201c0d4414042c02500d0301c40344455110200c01e0380d140311507841c101c050002d40050030340b80203000d040000c0d00e458050b68840d140d2098a910500700a8079600294000c01d0f0b0351402616000c1c131152440017400350903000000c0702e21841541d40f89031918100c8000d000d120700404001c1c00f416544880c1142201c01070b0198400302d030410441441524061406801d00104013440010003020402040400601c20f0300700440d03540182c1c3e0704c6080e50b940111321102230305c0e940141010500f8101003400d800c0c801c62103018011a11b40d44450701d8410300f5441000240 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 596823839 1250 596822589 596822593
    0xe0d0210020d02010501061e1214090705040605030105060d0f050718021206040902010207090b010e030303071116121e050105011806120809120f03041401030e010c0e0918 75
    0x1a40e1a20107500d07080c2e50010070300103618040c000210503115038131a08114800c88600c6180000b080c204984000a5000407040103444501d40c81402e040300c1001031180741600068080c840c1890100800e0391302030f9103c1c52180e8140418041070b507980c21081d40c050b40d404600c00e4000b203034500c1e00c03d003460499807010b030521900c034801405044489e0000c051060041c003000c0000c0e41e40c4001c0100719901a000a07005a0000c1c41c00c0c01100b82a600c2550880390505113460305084c02c000080c5154030444a000020b52941d1101c00001c10410000c2c0d00e840044142181140c00c2c0000504c07684407500001e4140390100d46401c00b6206101300144840d900031001344155070311990030166030080703441e40d801e20918103600022040d00c080e40d050403064cc400f48e40ba1074107285800b0426282050307202c6020324042c1800031180c1c51401c000400080c41d485a2a440302c0d000304001508840103540b0080c80c0780d040811200c03a25a1004034085044000c641c00010f81c1c490002ca581c00c000c00100c400024 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 596825089 1250 596823839 596823859
    0x60d082b231e070c14010516020a200d080705012408060c0d09051b03060a092004020c150f130506040f0c15050c06070f0912061103070815011d010e0d02 67
    0x15000c1034110b1407040c10b003031440300f984079540f070700492b40d80203040405001d0350454441c3c6e00e20001c0405ca07041401d4402081540000f9950700d4070030091b800f201e0200c0716030390340340541c1d00041c0d510003401c000343d609404103494461800e2800b07911007400504243c900700340082c42004085031035000c01d00f010b03007185c00c444003445080d2100c0302d40c0c0c1052043d40e01c43d01c00c2c0340028086150034041c01005560000e51560030b600740030303070b00529200010f101c664499024003d13600803a000308082e07180100d62500884c030034100046400100d00010b00300e011405c05415a900c00706500080c41600303e6403050954016407101e041c61419800300390400c188009110070343c1c0004541c04009000d015245c007080d00c005031120701081d109001c0b181408404103404a400b0003010b06107003032540c0054020314000c1188513a000c4030081d40c2c1e104881c8140070802040c248100c041c0400c007509042e0000382003080c510002d070710900c0d403107040c004020360402c42d0b143c661005076102c1000319813586a01030402a11 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 596826339 1250 596825089 596825123
    0x902091f0203072306180d0309021309050319050f03010e040c03120908160305060f180106090222063c080f0a05060d082b231e070c 58
    0x3c01300d07004901011a00c078100c04110b008180856800c9480168402802106ca00260960281039846026030b4004100c6801071070710785043c0284070380140300d0005995540d10080d15110801d501c0d4641c0420404180101243c0e101454100ea056540c880000b408960311460243e4a00710796400050004104444a400300c0750002500c00a640c150b0080c0ea21105440b644440e1084591102505075489240030a090b6217005039240d80144000c050609060603000649007551900d0b88441241c5030b000440c0c2c0a4005010611008511194842c00f801403034910002c091841e190310004016000071410f01e0088507148070f40c0c1e51b0700400e01d01e4200481c03182c800544a240f0449406841e100030b200003a80c681240e00c5821711074080201580d408084548070580302e82c00071702041240c51440d001e00752403012600342c45c14003104424404a4030f07410440c2000d9210355110301180000c01c01100b0300c00c03010100c84c180015800c003481810684d56031600f088400c01e080c0803014100110803051007074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 596827589 1250 596826339 596826383
    0x70f03021011240105040606050c031204020d08210901051e09031309060603060812070b0c0408011803110c030712030504120c15080402030a2006041d010902091f020307 74
    0x4c100c50003100c1c00c02c10075070340b24015510741c4903940c450b2400750420007807084030443c0a42e01c1c3e078119001904100f801c048541d07550032642e2000200d11810340c200c00403c1d45c207046500e1051340c0704224070000c1c40141404000c044a00381c0303582d00c04501408510004618900030002d6841407d80b400b20740c0911070baa850184000c1149004040003c0c1c20440c01041310040000c0040200765001d1143e8901056a1a03d0b04003400203042e40420b410108000030300000d0901801611034859005000181400d00c1c0c0505013000000e0090039607002408c03103070030720382d000300f21a822211101410308075003419107000c03502c91003141c120309012000d0700018001d00c150f03940c54005840014030cc0f01d00da510340e5038044d540400121002589070384945402000940301004030219803102c1c90130201d40080410010f0416042074010550010486a880b01ca12644000150041c0318040c02185440c11381d5010484450300070328100c0480101400c10130b070581c400c1044484158020301d0003100d5407000b50380720f1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 596828839 1250 596827589 596827591
    0x90406030b0f091219030603020a03050c03010b040c0e06031801020c1c0203040e06010507170a021501050a080a0201140f180f01080708060d050c13060602070f0302101124 75
    0xd141d01c900b1600040c280b02000503210100400102c80da400c0175842e42d40d4030306040403c5c4040c1c082580311000040161130b41c0c40e020028510850103410440701c06c205160850b400310001d184290705091450840a401030101c50034034200340c50700e503580c1d522000c0d400c0710310b0101c1443d000d2079031000810700c090620204408850213260000d041e510b4140c403c003281e0f41e021702e018002c560310740500822410340c026001004894443c01c04100c400c8000c10110000341c008003011400342c1c120300400c0c1e085101e11403089024040450b002d80125047c0034002d6a260f58412009040c441e4050803600d80b04640e00941d19181061141c107a030301d0740030380d40a10003080da240341c1d180501c5212100d0301c140d60141200c98450070660399048000d90780c3c68104001100200d600780e0702400344450122090322110040401801c94420200da150700d082c3c0003d03d80400c43c4c1c844900c41d0f80c01c0301c0520042e9581500e01c8030151191801c2003442001c45030703281c2040000d108004a03022551043d610b8071500c50640c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 596830089 1250 596828839 596828851
    0x2f0f0112091e0201080a05040b0a02070302010f060806180106030b06041104090e1e0607020d0e0f0402040b090906100c12111e0f21030714120a050a0b090a090206090406030b 76
    0xa45c0c0d1911001c03005000d680d000d0f280107004841d841c000035a165090b0b409051254000e10010031190381b44402c040c12100203421000f65900500704100345012610074400030b070066140200070341851501c690000900241c98184115280c0e103010b0700c9403031814241c070040d1401040c00c021802c030000c140d540c1c0d00003074124005d011003607491071211000d011403030300c1c170540b4290050b01030030f02002000c4030003420004200380c0c0b00c1942c800da6151511a4030207070018000f5020080d0756950700b03000700007249000074840c0b03204400310300300c0400301e80e8040300509180341e0082c0030000210f503442056503100c8588103010000e2290b400860b0710240c910400e06d2955044900b80c601c5c00c104151520703120010710030941c815021940c2108900e43c114802990b2022141c0307030801907040c89107410758403507201c001000d007190795210510090b00e1251181c9078120304015000c01c07071465a0004555003603c0204410642079640314088199104c00003110807081005104000a0b41c032441c250710600300c1a510317 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 596831339 1250 596830089 596830097
    0x61b02042301150c02010e151e03061c0c060c1110020c040501050406080a03050c12071b060815060d1e09030311070302250902072f0f0112091e0201 65
    0x2440101c500611341c0c120b946406a48140040301c101c4240088109942c220503120364082000c02c00030062101052075928441210641c0e0781041802c0083d04034001202070710001c28043ca0000047c0504030b07441c00c03601a400c0c580500106801c0902e0620f6115400071341244032164010005079021480680106048404000780e07603d51007408121031a134000c2000d04ea01c80c90204d00428091405001c1e1324145000320b85500480314000c1d965604900e004035091004080154803400f003130314407540500741a2505143d9480c181b4000110342d0000340640d40200c00008000c1c4000c01103400800900c101108805d1400510b620f1050090003040c41c2030700028036003011012585464811180560340681c000e008120742c03c1d01035058414244c6800d4000b00d000e40c2e000425441c40d002a02c5640e001e2603040c02c804074204102d030740110160000c080c0c441403002d44c1b01c4a684d1a50302e2344d85036000a2808020302400003a100000b42107562000c0d024448810b60f4149259200b03e0081001e03100b039071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 596832589 1250 596831339 596831369
    0x5041103061810090e3d0b0a0311010c0b0f1506041a03060109030b070315171e12031602011107081e070b10150504061b02042301 57
    0x8000e41440d0b009803510454a40d4038041044081c40726000424803441c0007041c0e401600002c00a42d400340501d190500b416449109242c4180b0400d01d2005400d8035039050900c08000c070540003601c103a115000007451411072024100159201d447d00c60075196010045010031300304078268140c0002c0c00c0703c0f00c801c4804400440d00071420068103031130854012900489a5084014000d2804d0b00005c04c9030741002802103000000c40e402c0d00409000d56826100024010480c0414122200e102d070841325440e4006c4900c3c074200000002e1006444107a9070b09030100c40780c15894a414501140703625182d0f0a07000c02401a0b140244056090a170001c0e002080384120400d045c100714010035034007422440061100c00040e40c078004d2627100ac502e40c0c14825141040d40e0780c400745401e9003628541411403804000f40449480c15a1100020001e42001d50605e45440d400600e80c4140a002510307040144c0c20900454940e40c1040c00311001c01500c400f51400116058039001009105811020310222 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 596833839 1250 596832589 596832619
    0xc0105090a120903020102060a050612070605070302100b1311090a030320060f01030627030305070f1806030209040b040c020d0201060f030f120c08030106170a050907060f090504110306 81
    0x14240f80112581a0003822156070780000d1040100710042500303400c40e440c5039880260700c030144105005031405403500c98540c107403810004d01e0301216400c080e1303c240c5030030051012a516600c2490500007141700c0464203c01c0180b030511a4050341c507031141c1200e482c4c0d03408000c2507001061981c2100c070440300c0317400c1c800302945a10f0f81c6c0e500681d141050310032940014000301d010380d00440d5070070341c02141c8240d500611105c201c0c0044910401900000e907590140321038542c0c080100348500c3c2c06807802040041d03680c002c10300031030349910a503800e05900040009681c8c07641d401004403040020410403255581d2107001c0e488003000303405040154642440882d8007105542004140c0341c0040525198041c1f694440e41e540b4010046002804124031803e00042d45007001140a000b090b5595400c07601444440b10340300e41d016091b003420740d05210400425003c0050188200c1d4114540340110005224003620025010740100350000d04003d52000c400070110000c60040800365815050394242e9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 596835089 1250 596833839 596833847
    0x20a180f0204060804030c170d02040810060b0a1805030f010608060702060c0405010516020d05070602070b03250513030b06120a030e0103021c0612061107030c0305030c0c0105090a12 80
    0x16010f041c0c0400c09100c046004203209000d002440792041c9801d5a94449101c00c4c00d034030342c1010203150302060300001e080c82800d2090010910030240301c00c045c0075503820041518200e004055080041116024410508080c107071b280030010400a03054401c9110360003d4140649050300480640380709900c08104443d1000810601c903081c0b60030304a040a04000044031694400c44224080200c41c80403140581ea5414800d00d40920a00043c65294503245010f400d04019521810744484203004010310484650340300d42c0d102ca4003180c4030590003e049402d44640c00b070134800700b0611510034008004c114150400900800b0200e9012000180d031800160341c486c040a402400505c007003290b1152540650003030441020780c80e0484030f43c60010200601160207036400100440004501e08082c4002880380c02000e01500700d04078a80307445500c0143c002c4829500007810041c0000005080070002c500b520702420604000f13204600b003000c50345a50788165801518001150400c441e081401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 596836339 1250 596835089 596835097
    0x515030a0b040209041401151a070c180908070302030406022119120e03030604270803060d0f031107080d2c03070308040609090207030e0f030109020a180f02 69
    0x4400d540c0070040e6280d90901039801c0d00076204641c900b2a20305040e0141c0c0084c00380c0d44400410103070a4400e07030b1504c1d8030801215104648541c0703039a400c010000101d4800545202a10300c820014040313070750310f02c1c0e03e20010407460304050802d545c01304141082541c04002441141c0d05075007142c0c0202041c50800000018040880007030701c2c01000340d5046c405171408ac004088a140c20804c401402c1c010a44081d034400ca00385181c10b4000008010b481c1c82c20340715040c11031303e849800c00400f02850015100b031007a69000a041040c0100002d62140e480070700c0440300640c009411702e1402180d01d805060b9000410351003229000303d020124100ca400104809030f400345682d0804601083c0c0100002c1a404500284406045e0402c11002d40c03000c0112800851249848954988c54080d00074030341e4101780c028448840c0100041004203902c020301e105031510031189003043c487c103400001c0c010011842e000750004030103500082c1a4035040c4610484144421082c80b034151100030740d204030301c5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 596837589 1250 596836339 596836343
    0x4090e032b150605120a0e030f1b06070f05030c090a0b0301032a05100207032a061103091c0c0602030901030c02030c0d051c050910110705100b1507060515030a 70
    0x201403000800f200c82c2d018445406c01b140312800106007035600c101508650003005012000c0c02c0014200124002190142c40420720010142a04d410038046c010308a03c0382c0c1307542c40100100403010602030080e03101110744000008001c01c001d65600c54003031070150001d1100391400c0f0400103482030b20703420f044007004e00d20744000380c140905414903040040c00c4044180502c2144682c03100800008d01004803c0043c1204006400060035039a011030408003158000d6010001961a43c1010143c008240c4131080d904490b24203041500008507040d9014040001d440045085000545d6940200080c400b14400380c0e8280302038501d03068240d03500d115450039114198080818820303e9441070001e0302c1035000b40380b03944111030f089010001c02d440c020b9602c030286805c1450b17008400c54142c46050960b030200b07210740342007076051380302c1c41e40f05c03070070324070003441850703c038030718240545c0d1080010300ca114001010301d45c450005003820030050004461100a8041d120040501482c00003182242c0617 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 596838839 1250 596837589 596837597
    0x50d030c022407053708181906020115050333090615040614010305071206030813050f09130201020a0c030f0308010e090304090e032b1506 61
    0x350640d03090200403403450101940032620030122980c00d0000c0c90003041018000c0c801048100e4082c807100079420305600e801e20075416080e032a8180e60181541d140c0030203400066980e10303030409140c520a51129001e15552011100740c1c46400402041d04502c141c0301c0300e45c001c0092141d5940c4481d28000c07140980341c0c0c9a4000000440c2c49040311803130341241000071303c0280410100c81c2c8250070600054506030050380146d01001401c0503608111800c0c0d4404072400d1040900d00110014404624003080f0f04160300c4100040ca058051844491034603c0700c41e0421045940e4146940640c01c901c9140e10104042c0c840000d0601d0089200c0b880404020030005442d00c2d80d01a0091990615000b281580181e289240c0440c0035609480000e40c041c4036500140f07078441c607000b442080142c1010f9041540310050101240c800425201942c01c01c902c001070300d01d541b04008c0c0c614000c0711105001c0402d9140300c070120b1020a541d824024a0006007800f003540210512110703106a070007118005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 596840089 1250 596838839 596838857
    0x6050c060612120306040f090f030e010e0a03030e01020f0d030209090a0606080601080a060e160809070602250b0a0302130801020306090c030a140c03100503070b040b0c1504050a020406050d03 84
    0x1c071003100000c45d040b0340001c1c00090310740d5800d5040d9041d203040303e00640e40170040e4803042d4185900300400c8815024246803612021300c492001501d102da95000180c00c12440b01084040ca900070410740000061400c02c441c0c243e104404000c002c0d62016400c18014640a00400c0088485000e10340540e002c0f030700c0304482c683c0c810b001180d043c40010030300460540c82d954009101e5100c80d581c103004014044803100c28801181c0040c00d440b0004d000c82032682e0009400b00716090340414140300052420712480141c0360640e101c00c1d4800c03103a4025200291002030840441505903008000843c1840c007030391026641c0700c42d050f00700e000854016401c4902e010000b411400b460000b0f5500c2501000001045048041d01030340504084540c00d1614000009203e05016002030701002094100c005007415418842104014007961240034a000808500c200f0040c0090280a030141c03240d020580341c0c3d2800f410519034820149600360701403440c2c15400700d12030030028881a541e68142e2540082 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 596841339 1250 596840089 596840113
    0x60a1404021c0b0f1903062004090f11190807030f020310030b070f0e010e060f0a02071a130e06030a021c061104062c030d0903020301360c0f06050c060612 68
    0x19166140d08e440c03224002c1c1e0440010600900060405005210400207070318401c60208001c0351034500788011207901c10311607855040c1c007200c0c03640418403280c0780403000d9444080c025006040000281d078115400441000b1540408525440c2242e000e030721203030520307110660183e13034806042401100103071403a441000c1a5016201c0e0716201040900400d242000340340b9008400e070420183e0000581013240108007507e14004280c24060304520090b10b44140030082d03c29119032481841410703803117000000c070160384c02c0c001c154801e41c0203400c0f081d2010138155201c61a60011604481580ca800b901004060a00d41581c3c265031440d11120902c0d5201400340b844070301510710f1400c19511016910740349407000c1c41050707801051600e8007512503065104150a4075003a6402e403840d06401001c20101150080d04944c28152420142e41348030801e0a1500d00051103810403c2c220365010400511940d00c800101005d0307a884080c1d41940d1031320010400c41813001020b000c003d601850390700c52 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 596842589 1250 596841339 596841341
    0x7030903050415020309041b0e0f0d0503030405062e1e03050709092d02190803030c03040b0f1b13120606180203060a1404021c0b0f190306 61
    0x42024001d080c15820940d035101d028031045400303805800160004294519242040c1c00341e0980d150510340c80e07282100304040010144102640c3c031920070081c2606031002511091444040540c10506484c2d03a0720f01403c10940e0b41a06843c034a5110f0180c51082e980004080d103203100d990580e21451902c81c1c94441030690b484400740b0a80c0c0d00450b0ba800c00800075904000722002400c940501003a2580d00381071242440c0444090700d0301d003214660004450708060949205010303811078020341c030400420780484401425410588403440000f040c400e4404040014511591040c60103075090390700c1140c640c06400c41034400080c0114462420029400c40e00040c0a2070901c07804021030842d554a003190080c04510b2054807110f84e190350900c01054110701021030901040b1045d031442c240440424408060752007110850a6911078070800da6036283c044500c1540c100340e81100695500e582180140103003030100303100c3c24214014408a0400d04401c040c851601c030f0319007108a166440c3c0314 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 596843839 1250 596842589 596842601
    0x90c0904060f051510170117030c010905031b0f0a120509030a08091f09060e011e08010f120305160c0e09060915240a0b07080c0c10080703 61
    0x8035001e807503482c580103018507482190f00c10765620310722a040c82c406a0900c040c80700844055810001a142c2070b00390030204810007030454080348100403e1030140070103c0c0c01c40c000d040118110354206138902d41480000400b034508148150003592200a01600d0995107070400ba06651441d0004040003012850043d6a02c141d4803080c140240342501c0140001e040c6810303038404903a9024045141c4003e420104d080d880410000750641c1803204901d0380240c10455280f142a04000d01006950700c581d02c0348032540c1405104100900e020382e03410401410307401090051954121000c18001600705000840d52511038154a41d02e00d850786a00840b01c003010491000e9640704502e00c4001000035a02400300d01c2030700e001002c1e110a0521502850408551070740d001c044000642c20300c0038000030000c0000d4184800507518140302c6c0c0030404200c2418050307110051014011030002c00b0700c039454004164044024041d1100d000280c0c0800c8510b403201642240000ca81000140585000350300003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 596845089 1250 596843839 596843843
    0x170906070c0618320a1d0f0906150102030706020a0c031419080406060f080f06100510030218040c02010f050604020406051606060312110d080c18060408100219030203090c0904 77
    0x3440042d01c19601180c02e02d80f41790f02c006800c1c0e0340e00f01006e10141c800260380e500311640c8946030020342401030140f039a525005d003000a044184540e40d80a03070b8020070456480c503501c240c040d500c91045800180003218001019404184031481d6046414070320f400721560000c510202e0f40c0d1000040d8822a28990010021281181d54040c003282101c80c0104c100001c0004500601050100699007414a040504502c41e40182d29a003400305540e007203500401400c2c0342ca40140c440c40650f401c2c10041007680c148035001803810140410340c55040d001210105400003062000b1b80b204000d0004900c00c03441500700045040c8050204220603041d480c1301e09002d0f1030085042502c80e02d6034040d014000c20040042070003800601c1100c407060021030320a61450401c1800b40c07604580c1070000d03205240c2e00c4001c480c0c02002c80d4203551348010503500034003c90811214001004650f1800a521242d51110307110640416690b45510a000b20307031040f0b03a202d02408580c44003500784141d06c4005801 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 596846339 1250 596845089 596845169
    0x1030204050a0e04030909090302060f0c090a140102010608030f0706020702010c0c0b040e070f0c1511030c0406092c060f0d05060106031d0604170906070c0618 70
    0x40540c2c8004064020700b00e0b4011000080c1043d00d005046442c40e50301c200b544a00749a544004a41c0225103035501808140810b0800d40d580c0c618208a481004001a804203401201080c2c4208003403604000e0344081c2c0003042102d86030207059680b070040c11050320240b031040081c0c0d800070f0f9880e0040d001c943e1040c1410304203404a070380c07642401c52240c2c020310304440004c40c0801002c0880c5400540100301d07810700c019072040c1e4500003001010280390140080c104000180503e000940c40b049812010300c01d8580c90382440841941b59500901c1408006249040c010a680349171085541c03103200c3c48290a221070b090141054041017004003840d03404010b49000175410744804d01c8101c2210720500290210790706000000d400c0324014114680b030701c010001c401211010016030719402c030f600702103072040210550641c13104510900c180703150800400702c1c0072810484007801301416500c05484000907036140060f12510f0021031301c28400c299080d0a0003400000c1040c00440c1c0c0580c045003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 596847589 1250 596846339 596846347
    0x1110c0d0515010b0319090b15030c0a090f051f0e0c13030f210903060e100c0810050612010b0d0e0319080f0c071e020409110306072a02010302 63
    0x40c4990403000d03804104c944400000b000a001e0303240d081e000340c6195149040240ca451911800c005c0c840040003c16807803c8a00442c21035902000b003484950b00c020700e901a40c585071044000904000744405c03403040e0415020a0601c024100307a40c0182c610644e802460f58030f03244266120010260a29601d10001c010075090b40b800d540300000503502070041c800e035200207490501042d007596000517481c1c1c440344034040b14141d4000420f100f1039400c00d201080003105030040606181d06a5001c06045140201403040160000078941c4240d443c000282c0e981546d0344203000c00b602c01d03440a90500e1a40f20014000b44100c1d40181541481c0e01d04009010107400032540e00e07592010001c00d0001800d990764000c0c20790b01c101601d6000310b08050320f120b94103040410310310500894030018050751400c907040391007c800c86200020140c000300203001070050340c2070500f00540003a00d9940a030091100042c01c150007190428801d420800b0301a403102c10100e110b02c00d511008008a04242d0200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 596848839 1250 596847589 596847613
    0x80901140d09080c1c0504060509150301061e03020702031222030c18020c1209062101141215060d02030a200315070804060b10020709050601110c0d05 66
    0xc42120b0031144680703002039440c54041340d95072520b0003a019880c24184d181c5c0c1c1c001075403503021041e070f001c5940a0800c00c1c0c8480e03d00d00040e4440c2e040400c8503260398404800010840d078880c218010512044920b0010444145d200320240d02c01c0b50303000303501a403092841c05040703141a0005e241c41c005c4040c6120a031007413296031000030302080e0700035500501350280900054400080142c41080710001c118581650202c21a0f10b880a0000e0b2103003d10010400344002d448040407151480e40c2155019040c02040d0142411000c0a0117290070352021070f201450103042140ea0a507002d61050010245584464660303055003000904090704000c00c800480d0050310208040d5443c40c1c450101980c0c401e0a000c4080100e180031181a40300c0d030301034a0340395203a5100400040d04601d0074a84000181d0365800c260000d81007101d03103a500030a414914115095022520909841c083d02c42481292180c2d0011194540c42c00314080c1690003160105d2041c0ca04606011002c47c410010b5400c145603113 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 596850089 1250 596848839 596848841
    0x60106051b15040605011e09020d0e0706051e03070509090a020f0a090e090a030c3e0405240409060b030f061008010504240603080c0102090109080604080901140d 71
    0x30940e940d40c04018030503c420040740340541405080d4080050b90140f9103080012001e04680c85104502c69000800482c1100c0903007000e00301c0120003084a000750307912040140560301100307000038201c200c3c403480c10400090030f08582c05024151741e041d08001d03044040055030000036005400485d42084a4220f482d00c42010b04000358803030f110701c2800c034034100400040c820020030700d000300e806c3320b115100042c3d00074085100c03050304501d6025502500f0540d4140c00074030144d50100b140c0e003034803e500010704818244c03105120295801c0c01951034481c40e00569241d10b000d09502e5104030780204081e410242d021000e124010784000c60396400d88000b003070400a0302d281c4c1000c207401ca14200080382031364411000c0208001c00080140e4901078842c00103104920100948488803040d009001500940040020f190054011035544071002c107060700079070068204078007143c0c1e00180007512500100c0c400307108a800501351460440c464004494042071904c0800170202c080c8292208603200d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 596851339 1250 596850089 596850103
    0x2060c0a050d03150f2103020a0b0a050103051b0a06051e0301081e162615010f17070603091401020a020604022827150504060f08060106051b 62
    0x1548000a2040c40e107940c42c0210011030b0443c4101c008502810000220034406c036000e40721228084210103403440c507049040174080c2e4400f410081c00d010038030280e4003403a80030341d049a100b2022103c1d07204c04055a5000f1394440c0403c9036100a402c1d0080002a0059005281ca012000050040f0802c07440480081d80c01c00e8110b14400c0d40301841088070030200b030040c072214480d400c2c010100700980d0701c84405a250725000d2030611002e15030744255000400d82091180b04644401d40e0a00b9242030144162040700744190050090303042000a4000d064a5425561091030409401c2d01402c0c600298040c010000c011074424026400c00301d00a03100f07101821030590154050310303660a02d401002007070425402c1c504c0d02041860100d50b0a03012400f01e4404541300c1417081c0740f400e588050715240302c6407040840104241400200d5029090b540120340648408403010807140e51903445100004986010350901744d0b0040b001030181d24000c40142800781440c20b0400701720300c4031041c21801c0c202 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 596852589 1250 596851339 596851363
    0x160311070f02040c08150f0103140a0c020111040b07061107080d0603110114090904081306093b041112010221070c1113090b01170601050603010302060c0a05 69
    0x100c80400d10701103180034020340c10102c406141c0031440742810f4420024258000110380d00c0340212400c800c0300359000c0d030090408520784e0a03a44045150001c2107a02034500540c035030005500e4005d80b0032140d507048003038506580030700c180c6509100e42980d585009109040160b00c1c000301c144180740024000d04002d2040f810f0103400890902d2a40c40c1107400311141301d4103541030006052005188900740000d0302c1c0d0a20084804a60036280c0341402c003e2480389509046d02e0000c40032020903404c0d0400d010700219812403040c00c401d41c241100843c074031101e00c0700344880240600e05006440300d0302c1c90400d400c10701400610135003031010300c00122400f1240c19401480d94001c60145241a02c01e500c40301c50f403080610b08941c2d0300c1e28640c01810000c1d405c0004080d0910080040c0442d10340d50008461140585410002007040e8240a49006001d00c00c041c01804817240c1550701d04d1000c40c500c1c0c104c5d00041e1900d400d60f42103a08110040d00700245280383d500c07880c6941004200d0802c05121780030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 596853839 1250 596852589 596852603
    0x60e060d1821080114091506030109021209030702010e10170103060501151e03090c0f030506010e10080607081914070e0d020325030c0602030a110a050616031107 71
    0x910703404400e00101c0c940740060240f00e494001002200d200740d1820841c40001c41e100d403100c1d540c05c030041d03407100c0c0d200c1805904a04c000c4000329020700a580103244620040c01c02d150165149010940e0721f1203400c0000f40081c1c0300c0c0003540910b0508201c01010510141000f01c000c0c2c0b482510700600c190268415554552240010001c240005035010311a210b68540a590319001c03280c096008844509044105503660040c84184403003900000082c10780c038505e02c07003003594070b0402e03d07130700c00080c020030100413003000118031494150400350040317480703a44c017420181e0f131248425984414010405102c00c85080369110107110f092040003200d0b000300f0600d0700c0d0b60405000060102508010450050f2000c0c401100960341c0021240c031510f10320f02505844002000c0c070001c44c400b042c2d0004011028996001c07030310319000320140110140e20380ea141c0c02141c203114280e0b50345581240207000c54011b600440c518a400402c1400a6551814003043c0364101581c104142c0d80181003d0350b102d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 596855089 1250 596853839 596853863
    0x20304080417060f1803040819030801050d0c12140a0605040b07030c02190807020a0f2909151605070e1b04090f090215090306010609060e060d18 64
    0x5001078805107039450394100010801c13440c194540012880004c0c1009420200c08542c080d00e04500f00f049402900050040c0c4401a860307030120304415000240c2100420f100000100c0c1c6030902a00d0f0260140e04805004145890540c8030101380c9c0d844241654180b0a04a0701c2022030010400201000d2241e01e0020351454541891071400c0c0300641800708050030b0504007258542d002824002d40c40070321804001d02e00541c035000c1c25034840c0c40c1000390424644080090074041110207402100e0032882e80c502405c1000d190790780c1081000465410780d50044c0510016402c090b0070031281580c04148042c0341076452040d00c9041406a10100d07a41e9000050034808201000045d039004500c038a00c0d002002c480748000d160134002e900903070220395515441d401c0912200d4010700c0c44650054000001030301d1041649005074003007a091030103440b5400c00050b6181c0b0801840040350b0700c0307607200c0f1422540c0908000b0250b200310581401c064841a143c1d05416281c0501c0c04024800d074609848 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 596856339 1250 596855089 596855099
    0x20a0c12050f03090609120f0111030907050f090406050717010b0403021504050a0b030a06150801150c0c14040204081902130501060909050405010e101512020a03080c0a060203040804 80
    0x151884081d480c01c0d0359041841502c130b9940741c000c1503506210045401402149615801d2481d044801d010200d082d82000d05680c03104c0e10780d00c0218010083c06045d6550540c4500a10803050f080380d01c1c07142c0003458240040d01184856101d5904103510b450301c01e09070706c0c440b5440e18a18034280c000260402000804008501e080999180c64441102140381801e1510300000d071460300c98840c01344008000000540b4115880c1d02c19401382441a01400024142e01801807034070409000e02c80c4a151112001c00c00d56019142c0e0000c01c603401213220a185007014904203900101003442d5801c61b03001d00c400306200034140300c00d4080b9070041c025104041413030300400030142808040500b6172854407005002880d07221400d0303429a00d800e640455240c0322454114010002c150108016001e455541003210324150002144954807105486040c1d48400c0d40b401e140796032450080d8014000789040002942c0340000d4044096201c094800100c82d540f1404145d900484003151421000282401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 596857589 1250 596856339 596856343
    0xf021303060b0f010c0506040210020a0602030f18010e060c160f060b04050c04030804030236071112090d171209060106090b07030c02221d120a03020a020a0c1205 71
    0x20b00f800d1800b40460f0140351109611090003501c06401020a50b18a540560081001d0b40c1c03200e5210740115030384d14090b0310204480f902601d5410480c4c080d426842c0c0500414041c0c00312101c0b0705800340007161150f0344020516400b4485402c3c503900a40c10720008945940040481d543c06980c000c9000c0780300c00f08000444d10700030301c060412002440b050011551800644090f2507058070015015038000c04e4948004070f01204c8a440d001c801c0c404001040054945640511801c1d00c504000040d0034044540300c0490f200e062800703810922903485140381c50400c040f0250b002d5500711141c601c612075100340a82c4080840f461081d004024401019402c010081c010049403170080c210b94207005104800e40703d0014003070308001c0900608002e5544074600f84d07034020740103880c0c6a0030a100364003c0e4050821150001380f03405214945c40041407012441c025105003406005181111120b800c1d07000f90000701c040c1046110704441d41e070010742d40c0c0e03078488090000d554030f594000b9070078503042c0c1c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 596858839 1250 596857589 596857609
    0x91a04090605030a030c030e040209040203010803120603010203070e1c1e1203060e011211130b01030f141b0909071706030d21140705040503060f07080106030f021303060b 75
    0x1d010398813074030943c800b1a5112009070000c070703410301c0d00b038800382c02003000500a401190351643d446803001000180c1414000003c080030f00190004030707896a112070400d1708034001120440041441078840c071441d86010115a8441704a4012480011440e42c941c0000d1041e480581a031402020404a01f8003045000c01c5d003c0c050b1a281c14070405041407003a132050302041c440d90f80d440b81e40120b0f840c1084030007108082c2220024054610380d01c41141140041e01c4c000071524046441d010058a02c86000d0086607900c1c5912094088141c5641c8070080881031062903c42d2120814840c078111fa5441c07218035400b900e46641c80740200c080f50448024401005026140b00b540f1200d405900d02e504801017900d08940c04a8004440a6941c00720000d4400c02c00483c80700c0d0502d8080104068001c4041e00c15501d0079412a05656a002402240c0381c40035940750000c20309400040142a100c2d401c010f000d01e281ca903000d802c250980303045100c079074040d810445100791620f981c010345090143d103070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 596860089 1250 596858839 596858849
    0xe070314030a0e0103110702090901020a1206080303360307150b0f10140301170105091906020a09050d03031406030c0d021c080d0b010f05030c0a0f091a040906 70
    0x20350720b00340c103014020384401030b05070b40310741030544503100a030181c400681524982034014142e40124901048103070300035805140c5c54004100d4601e015801c85240e03126400c00d40b003179240110300d151981c4902004aa1a02583e101d02d2040c4007440031126004040780c03840c0340191401141c4400c0c0780d29010320b0300d000200400e001a89000301080940d900d02d10322540c214016600786408542c40d0400712005103042c031007406880d00c004000641000540b00013240b080344440204513a80360031507400e44410118004400104209041d1004104158010214007410703003030009023582d8a01c00f0601da90110a000e60219945107203003000d03120311400d11640b0001c11005822002d944a00003811810b0300c1e2006406a8614000e100c980d000340390303200040300c2e00400d16540b1480c41a02043c0540043c0c54841c0c001044100001801c502580949010398440d00c0c2560816080324801c0702d00c600c0c2000b00b00100031440500245000d01141c1101c6058180030300d1075a6241480302d01426100ca81e442 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 596861339 1250 596860089 596860093
    0x1c050d0302091003230a0e030c060105150403080d0b03240a0515060a1805040207151103040c030b0709091508071a0f03090a1b091406090a0c02010e010e070314 70
    0x640b0340040d071081904100c0b054145e150300d01030300c0f0400450300070001007900408512002a403d80c1c980c2001400904071282210b80000103100b14a140c0c41a000700d12000340304d01c0060055040c07030b070b4450300000790b5403501400702e64807114a00054202c1001c0d8400034907516010000380015102d1314090907900c1481c0b4901044050600c01c0440c0003032245010200c1001060a1441608004050b00100826004105548a007000d0605200503403443e0081008540f0746020301e622449800f0a5910881e00180340d000054a0b607103926149000080c40542003040004010801481d144621844101502405403056041c40f0a041c9407030f045030007007820a880e60154090100100046450310100403058031b0300c98640c60301d070300d260490143c1c004107120480030581041060401d00d400884401c0041807020101064070030000e0001a10703030300e4122203400001030708802c0c02d0f00304041448041c400014607030b00c9001c00b03500711001604007039600c2c1c101800810078820a14503015041c203030400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 596862589 1250 596861339 596861351
    0x715030b04020d0903200c0402070218040b010e01061106010b4504090b0a1d0f0a030e01031e0b010e090a0902091602211902070608090c09061c050d0302091003 70
    0x1800e80d8a81d134007010103200d189c002500038215202c0260f0703581c4801c604407001c080745c1001d2806550802d801d004403140180c1d84000044e903031b8440c01b00f010801d48041c025145030790a0005031a0150300081240806902042244180080b00c2402c44000748000c03004c0302802400f800c20365112400c480b81d461059050027a8180855100c6d420b458101c604c48000203038146411b4803010031000310045105403800b40036807811807050007044c1810100d1007903130b480e2a008482030041d0102e5034640f00300c0c0c0c080c2104281c241016401c580c0600d1056505050000c06003040320b000580f6071104a628540175a11800c054045091075500303150884040d010082c58142ea10100a5407000210710f1a400340e140800e0340a5031288050445403400181d5428000c1d64201000c01b03541d0b2001840b440c0005140d03007000800742c1e103000c40c04603141da1380101035003800d071a2181080100602e078500d465601c440c0503080d1000403005c03c18030001141c0c0744c4000d41c0300e424000402203d6404114000f041c90b080c10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 596863839 1250 596862589 596862647
    0x6031803161104020406050f09040b06030a021c050f18011b090305070801091e111002010b03070e1e060301240305073f050304060207081e0715030b04020d0903 70
    0x7d01034030749108030800520340b1000240c00040117482c50225582d000308001080c014640041c3e001400e981001a140b04140b9411500c42422600c084840360046650007000c962622011030311500f4103240b0600101d00700502c28101441090403103965408901c400c00c040081000a1043d11b000300b00c808000c0002480e5a1600381e00d41d0640c0c10a014a040c03003460100070044281ca2a94965001410300210b6007610503019000700041d0012501ca84101c05c80042c07182030f0298160700c1080c130402c0600c149482d0b17410360102c1714406040f0a600d9500c0303111094915101d40d460b48040d000d8440c804801071b16505109081c1a01c6030409201400c03610030921344140c081c00c2400800f03042c0160710440a6003410b0b40c1d8001c0700144401005070000180004149900080c03800a94007058207941000c401082a074050004206429280d50003000040003000c0a044145140c150300d0b00b400300e1000c01440004007268884160644081e80d50301d49101803540c0012607207100c01c0c20074070f0120800261 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 596865089 1250 596863839 596863847
    0x204050a0303181806030b06030609100e15040309030c09050408070f0501090c080601051e0a060f110703031d03010c080c22030821040b0606031803161104020406 71
    0x980070203414024102e6041e0f00400c20b00d030f06400240030300741c00c10082c007a54448113006080c0070300c410389050104d1804200030b4940864598000d813640401031007281e141d40305040290104103a2603029029800c8603844041c0c0e111640792103144240d40318442141980782c80344200e030858209034003151416042000041811040f19a0340f41c000f851455103d44914029001d03010f080001000203e6038540018842c0740050024140e40d800c44047c914441e14503030b440e51204546003003d9011000140c2006518001c5020301c0c01e540040c98401c0656480e4425503103040a5a0301c104c0c0001c411441c00d90400390390400d40f0705210350890091001381c0c015540149000300103043c1c49100c0200051908a100d0010f15414255054410710341000e95030b818481d491350400e06030000402681007807400c9002280d0b072071512461740a219100d5036201c903400e00030580c000425041022101c1c1c0a41800074900f00098003e42e000088400f200d01c0c0c0c036107011200008040c0c0350f01c0c003440c01403005020b10f81d08 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 596866339 1250 596865089 596865109
    0x1b01240e0c04050d140105280207030504080d1206060c0b0711011b03060503070509100b0304050c0d120906030c051818071d06070f0b090109021002030d050a020405 72
    0x608014036a40e51154000300c1414451903201030f50103c000e5410400300700c2003005450102aa0500801c5242d0320b00c101c4608010340400502c030303040c41103400011841c0c01c0e0340c0900399440c000d00d441400c098481085900d084040705c0070201250178100c91640000d46806107c001d810a4034280380e034413156644144c5500320161000c0103000311011074a000d204251b00800343d0b00c6002c030030040303c80b0720020040c0c0100031030b029141c00380c010f1000202d601d04241d0110760040034400469508e141c684091003240d5000500119664041c0640d486801d40d20601088030b02070080c240b0b01c58801000f800170300710040c02e90161043c03504084400494503001070540301813580c00005076100074558000680840f44801018652580035020700003580e0384010003c00200d20300c0c0e04503000aa02703000b01310585c00760180044c02c3d4003595200d04000b4800300360582d00a403010002007040001d59001640513514610b0040050340302150902c03a0b003403140a803d40100c0507910441c901030400c0082105584 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 596867589 1250 596866339 596866349
    0xc09060e06010507140316060b0301111b030409140612010515011407060501090510080a0203071a070209070e011701032a0816090f290d05031b0124 65
    0xc001c55440103200074171400b11101c00040060701d90f01d11040b035103a40501c60000c41981c3c00391400506d10b4807414140700340340c082081d20020b641003040c5080400d101110351802190140001d001c0001e21141074090120040d00880392a0f903240380c49014080d03102a220307080a09c6030304000900c1103960b10507003a00001c09082c80c120707001d042450b40100c00c034401d124000f8691841d007000041c6040b0030350b11442c0220803030601110b1490341c0e2207190382d4450403000d0195040d08420000c020300091012224010384051a032a828000342c4d2b0001218031030200e618034003017a20741e00b003079200c0d6912400031000754800f001c0c4e01c0f04550442c0c8034031425425035481c1080180c5000da80c00c00d003004000c3c0307034401850914125015034100080070188503000c0c0c810040726900f844015075180c2d10134000e0038a03d04c202c000000c00c0c4071a44808804a004900031140c121101c1189540411020b200074160512558402cbc201a024805c0c01800c50718444841c60010004d001c0f070114011a000c3c070700040b90 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 596868839 1250 596867589 596867597
    0x9010b01080c0310030803130201030b01020a123006031e0c1403031c06140607051b040e0a1a0108030406080c030702070906080a030f0306060c1e020301090f0c09060e0601 75
    0x1d0b6800b080301015511366000949140804000c000084a1681c900401c0c41e00c01e0360107102c0f8681e0f0200690341e9441120b0000d0504080b030309500e200c00e1150500000580600c40c0c240850059003128840041c40380280c2d8245544420090050200b8800c241602004100c0c0407c1c0b4a400b646405030000054001d00002e001c4500004e03c20b0755080064802802c90321103007003c180c0050100100420031842040741c2e4050070b1618414a14103c0103a4680b03a4004003d030426a080e0300e88080b07181c500c40c0081c0c0e4003d580d4031074010349a408104480a10748140d0f0703c844034484c0d10049050002c4160711000d0036500800c01407280d44e61141c0e01d513401c440a4012a81c40380c0b600c100580c1000e10355042210a44d1405c08001043d940005402c41070328026115901d07801d50072417003281500c2c22406020089491034905a00040d200c0040e2081d144043c82c80d0240301055900003829549040b40c1034a40c0c0c81c41d855a80f00344144612428002d058601017000006e140c03440c1d01207411001006103040c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 596870089 1250 596868839 596868841
    0x11031609050408090916031808071136010b0403050a1502040e0a020918360706090303120903090e2a03090c010212030a1e0e0106030b09010b01080c03 66
    0x4510401544c1d1200001002c1c0d8805150840c201c000740d40d0481180c1b00002d08107452842c41c00d40c80c80c400c000854102613604d00d01070041d16584101c460460415802c50003640403842c05021010500000110007014982c2400c8210b1019a524806820110850004100c1000080c00001e2000c807000c3c4d11602549040c0d010200800c024000c0380c0c0b014010800c00c0d0304000e00c958035580200307140101103881c0307100c00d41b0203500b003100d5210448002c441ca010000c4841d00c41071051400d02c2400c0800f216601013018501e41203410031850307600c903201003141120184201900f0216050302c81507104002c204115039620000c09207201842440310400311000441c040110084400603040703040224500403e840d00c0418001d82c1c03080701d8401d1a030050742c180c10507039031000c604c103150703844d61031955411625500602c100907d249444000360143d07085001540b2031007806481e8120b00b2820000429a00d941040c440c0e2400003044a02142d26005c441d010720b82c0c106540075044100c1c4007030300da01c07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 596871339 1250 596870089 596870093
    0x3020f0d092904030f0b060411120c030924010303020c060c0622060e060609011a07020618090106020607020d110616030b190503070602030415050c0c0d060207110316090504 76
    0x80d210315000902010103007200c04046c0441124003a0180409035810401050300c1d00160b0010301999220200c002044004035180c45200701c055038000c40d103001a10344400ba41140c41c1c0004130031028101c0880402001003040c0b41d014003c154102e0070980d9100e01d00310328441c20549403100100340105400b420584d016020006075040082c20b58480d40410400c02d4048070560780d90340403241e8a1142044e0800492850080c01c0c1101e88030541d5100c20b404d21105508002c600d0700f045d94046000c84000d80c1c40178aa566420303200303000b410720350058903103400c1c03844d03000b070030001441c124001344030032090384803501c2000161455020200440780042200c94100403405401860384480c0d101c0d01c40e401842c2d411000d0050902240c1049080701c1c1e00d19a512001d9031240030703034481c003c5541009095641e6282c000c4005000814001081e5440b0075003801c0020901844188140e9105501007101410070003c0c0c5070980c42c51701d00700d004141e01d1040030380d10010032140b4010303c0e02040d01e407030100d02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 596872589 1250 596871339 596871419
    0xb0f04080412060e0105070207050a0303050d0f060e07020c011e080603070e07110c0906030601030b040c030b01091b030b1309060b120d08160c020907120903020f0d09 73
    0x800b03440c1104a54045041d1810001c010344045504c11885518020214601c0381c00021020f00b101c901800354594603103540c41c1600d6a42104507072a260948501013110541d03c50302c81c90014084105032140241003610000385003998252074507052102d00d4812602080312415088905107061a1800c6035a60360000b1904001d44c5601000112001a09005100f90440d2140140000d1002160703406d00100040011601042d00d249815811503801030001c140c20700c400907480341c0502c410160060ba2a69400314403c0c1c26800381c002c16a42d070000c5c001e089881d014100004a09203824011445030b0800680072110030300304100e0b4180e03114000700800c00c1a400c58004068001c044210250038880b105860b00081d100c041300045216000480e403540415102d481c01c82c0c50f0fa9442100441c40e030a03c091854050080801e210038101e00039200312041c011201103a102c1d601504520041400861a000c2c140d11000140220501c2c01d00802007203103501c03a0604182005c01c4501048110562 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 596873839 1250 596872589 596872597
    0x3080306011b030306050f09010f0e102304050c070201080105120a0507120b0106050301080705010327030e0301050106020a0f08090f060a02011415010e040506131e11070b0f0408 78
    0x14000d2060b4241c010103060301a40204102d45081d200f0000e101c0400b81000b01064090090307000314010f618080c000040d4280615900990807060422070580310508080101450040003412201c1040452210b08141c040c0c25004010001c1c154100345090740040c054540502407103000341094102408908010040303a4240d64003d021b80b8006a1640841c0910050b12402a50780d045c501c0300000741c203803013a412281221030000c0036001d440d0a01d40114054500c107400700c10f1441c4003840b0304200c8590b0312114a8414072a88416000c503d03d08203144c29603405038070030402d54000d8540c100101e1044c2c86522900c0c0c2d0300030f120750307512902d110000b400c40e0000c2034801c0d004280814030141b11038055200341c200c2d11030503020400703540d50701e980c40350752070462071540e4002184141c0310141414560449600900020400c500c0121100e000300121501c036510421030aa03d00da5902d00ba800c0c91003458a400f16503c4440e1420b11551540c65040310042c0c10b000c3c410300c8040c0001e041c05041c0c4261 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 596875089 1250 596873839 596873867
    0x30a0b040303150608060301140402011e1713200a09110412030203070303061512051b1303060e0313030206070501090501050a0e0d020d0207230310020a02060703020906040308030601 80
    0xf04400c0e644440000b0300000045a807140290310703109a1048110400c41c450340725075416502c0b0b94007850711105014044140d4821a8180010282c00350111203565000c2c03840356811002111010120741002c0700701d02c42d1600410381ca2900380f0707036540b00ca451302c000100903100301000101e0605280400705c0c503944030303562015940b43c800810b103800b05a03003c0010440c0c24000d5805208072519580752000d5189460310000c0412030f41100c81050100360b8000d181c1c0810a004480d400d01c40c02c03054101c480d4809210b0401e1444010828030411003140700300e51442040100450a010003200c64050b40b081d1400b0191003007002144000412509421400d04554440c00a100d541001350f40ba03c080d0030641d610480c00d003d507080d40e81c0014400070320344045c0001c0380d00a100c024038010810118029081401000018202285640b5101007094409240c01d0010043e620b001c1814020b0034140017400c1d00d02054010840d40e0800d0351540c0c2643c3c19a50441d100d41d550740c4513a801a80c0b4200c020b002c0e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 596876339 1250 596875089 596875121
    0x1710060b0409150914010329040201080402010c050106060906020f0606240403060c030f06150c1101030e030304081908100b090103020706050f01050f0f010516020f120d1d030a0b040303 81
    0x11145d43c161020307241ca070480340b240c0800c0e241e03811100745d40c0c240407820b450000c4c040101600000c01541c403844100c0c1c0c0050060405609d0b441140d00d8141c02c0d58202c3d0019000b10b100b02000b00801035041142c0903030b4102e805c024183e1802c0c800009000c824540300c0448660707401c540c00084200d01c4000310340040d54807207410480002c00350307000341c094040b0204020314a0316120000820074035245000040f6000740ea10313165408075954a00c2c694440b42000c0504040d9224a20f03014201c00304002c5000b103001d0000c141d00c030400104404c085520010601c0104000e071024065541e1001c0b007104281c41c10b0350503854483d90a200124000c0c040c1a0016200500b85010b010400c000380803128180c60b029070750405003d032030340c051080d0110009292800604100310280e0401c6441c05004912403000b031110416446450004400b2000159441c1c00398210a100c0c2030f100d9040b0049004c1c480351080340c2648640040d00003615100283d0b40507064025000002d010503100350f1080d9005000421 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 596877589 1250 596876339 596876351
    0x2c0a110619021b06030919060b2205090c01020307060c020c0d03180b130905060d02090c03010905010e0103080f13051c030207170a1203020d0203011710060b04091509 73
    0x2503540411003040f1025406141405010742010700407079100d2242c900c000c09003460181c50106d4a2024900705582455460942031490794a50b483e0007101c03902d11852003135405104014034215000034126600301d50000003c0d42c0b6698001c02582c1000341c000030001051010300c00d040c0c1c101900090031a130306c42d1441c4449002c054202c012004258051070003281c013540c940a18400314400c6030b548501c906201e100400c20300305150009684003101601d04984841c841e0302250302041d05903005111450044018461311900e44151030042965102001d090351550303c482e0101e1203222042100100000350514a5a0070901c80c8c030000e0001410500d15200d20079003c06681031041402c0b030050144c19800134aa03031641d51142d0b882ca0b03010028044c01070b00340c0d64144104074610485000c0c1038003840754007030700c11039803014600038508024440d81e400e074a042c0160604c121000c426000301d01d000001d11207150200c064505403550b5000028048400400e446107501e0160711810189050031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 596878839 1250 596877589 596877637
    0xe041514070815010503240405040303020304140c090c31082e2c0c0108130b0f061816080601090303051c090b09012c0a1106 55
    0x303003018403a5501c0e5440b903406483d00300c0c1404000140802060000da8140041244680118141803a400902c03548080031003000e400300d800c0d100d04690590220381d0120420040c0300006520703d14a0036404041c12084e8007480c00165518406003445051100104261449420740404030b01c85c2682c41c4c042480c1690040b4612110781c815006180380742c01002c8940c0300924000000c0900c000041c0340c0c0ca07840ca440c50210800074420055001043c01824940b0710310001c407100031407580c110301405001410107601c00900508006080d502320a0346c0c3ca40520702050180c03480d10740003041c180e1030400c542c40b0100010282000c00307038a0090110410140070f800308045084140d05e00d04d9440d10401a41e48200548029445c2d20018000c5813040001d0469040035014200041c1c410070b01c0010070f0201501c03007420321507081395042816955040802ca0508412a0000c4003120451719488421604c10b1941e40701d902c031010080610721100381c601d0309139550100f900ea1411480d00000811400c40b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 596880089 1250 596878839 596878871
    0xa0e010c0f090303120f1d1612020409031407060204030201090e0f060415051203040e1f030303020313061d070b040b0d1e0e160e040b06060a020a021c0c0510090e0415 73
    0x41d01607d90b110301005041c400c1201d030702c0c0000b00c413170074418006004003507002d002c041c0000741411400c100c2c0f07101070510100d0080010340101c0f03005127001078482c1d00350f200240215001c0e800c81d601104502003008550800a4051a84210161404600d0800d48004041c1d403010316089590f10402000000b9400130000001e081212180c89002074140c03100e01c0035424280c0000301082640e809003200b8400300e0301903002583c0260340500348110140058413201c1c11100c0c0041170024000a02401000c2010100300d2903001e0a10511031514003850880300009a1141a491784c5040d40c86280d10000700d858211945070861000700240001c03c0b080403059210016401c19600b070b002420360105242c01c0c1c08248c144260360091120055403512000c00ca540d41007040000b007144614000c400040c0c9911400040001d4070340100c0710030081d80d10b00018645625000381d8064108000300e810000d034015405000c4802c001440400d07a1102d09008505250b0404110341c40c0e030800c01181c0c40c80b501 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 596881339 1250 596880089 596880131
    0x306241205010605070c0f0b07120c1704080d09080c100302120c0901080106110a03030e0a0f03020c1507080f0304030c170301030218070c080d0e060a0e010c0f090303120f 75
    0x8694440071090b43c540001910547c4940200c000d00f1a0502c403000021302840125544400c150410b40c1101003680c1e0350300381c81e101c190f40642150401040800441c0720410848080b05c0030790034092480c80c01c1c200d10554a00d80702810500c0303415042550308841d8040d074101d8040400000c0110f64038504030728a00c00d2940250300c0c45000030120310002070018800e07110301083d031400b440603006241d49610110060a0454000003140c09084d100400141d81000c4242d41588241c01410020480508100014402190143d000d41d41009484002903802c001c451015202000c550b07180c3d121401c0450300440224401001c2810584003208140d03000000755040728400c50700e9200c0e01c55240300051205070291142d9000c0340e1504800e200052040014118903241c412000031a20359109c2c80615050b42501c80c3d100722036951003450f00800e028042c01070482d40d13500304080040c0c05200d0040958102c2d1001904204c038088400c428156950081c9401d070340081010b01008905212052103040e03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 596882589 1250 596881339 596881343
    0x101206080703050d0c03080103060b010302041203030f0c1106010b130503030c0c2713081314030705060a050d0207230610080d0c110f0a120b07030624120501060507 72
    0xc6004030300300001e03205c0e030300c0300940640c507075105202646136595141c060074808034000e05240e0207003c0820322a08ac08031403136030280030350740120b03042031840f810038101e401401c800b40c10441b920710070741c802ea180000d2160446e0940c40000e591070400810b031290742c07011900031540c1408000750881040340000780c0455041c9044941c02040140c01e1040f5041740348240460042c840c800340025a1503484a01c40d0b050a0301440c8218a0101302d64040c000940c0c40d600281010090048032a05c50b0400300b084c030015010940d1480e162160040014103907000700314420500540000e007180810551071481c0f51036140c440701130a5901072108000d519104121005660200c200000040d540c0b0002003001c841c40d000e84521204c64001c0c0c6950a03a6144503611a800c5600101c0b074400700c1d1100091400107240040c4000800c1a55140403441c03504050301c12000c040c28128203000c40c40a4a0388040e41804c48402d62020091045041e19070381122600c030f00d00d140c0ba2000000302e140c2c018004280480c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 596883839 1250 596882589 596882593
    0x603041202070f0f0501030207020f040f0c02070902030c03040f050f01020f03090d1409101b0501020301061e0f08091c031a03070b0706051e15090a0b010e10120608070305 75
    0x20f515050001c981e110341c0c2c8105007a80e05141d50801865001b1b80c002c049180c0050003c0c0c1008040034045416105400c01d0640c0190b43c0d000810741c21641030011101a00d81100c040d441e5080400001c200782c00302074000b8208010007500f80040001c1046030045602181e00259280c004801c00762003250400c60700c84029000e040c0111450500c180000007181101c048020f0900205800f03010f550440c800c80b00c000e01101d100010f805076014000c2008035842a00050b96035070604100070028200d0640003614015007106068030035070010558800601986850320444d51440c80b087e1801e01d642c42d006d0349008070200380170b04440d07044c0c0000301e81140c2250070301c290b0201c00b42070555400355441000100f03101407041c7d1000510030340006030040c1404120b0850460070745940706044809540c1d0541d00c02c050a008200c9040a868260740880c44001c00c1142c50703140b41c0080e20300e0700e03001d2106c0e10491058100740e82e0076004044400d4250b0780c002c010400103071944a240d40d02c00541c00180c403d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 596885089 1250 596883839 596883853
    0x8120315030312010612060503070803030901060e1e04032006090c030a0b010b0f040e070201020426100c031805070317030910090302070504091a01080714130b0603041202 75
    0xe420300000701c402c030030208030044100e031707291913000c8502c181d92041101d01142c0b030f9240040d60342d9041100d400500450030195540b07092810700300d801c50304141c0c00000312440c484104140707198079004000c41101500c00100740c59503140f804490000c2c4030004c02c005961308428050240c07200003007052040e00722504880b20750461000b05681c0300700d00714008021030150001030000d10b4140c0f0141c0fa15a240d080018101901c2d41d1942640310340071128400144c2d4007141c20030040080b0301812411403810750071b03984c500d5031200c0a644c4880e18601c4110255071101c501eaa68284241e110400030241c042d62000310708a60300d401c1c0e403112a24030042d5850301c40c2130000d2900c400d1440484e4060f030401402031003001207135814580900340c001e0081d42540074080c40041c2d80e80700c42c028040348511480442c03c0c0c0e8281c1a0303810f1408001a040321895510020042c42843d8820440c0c5045101c00c0f00c0424080d48035210b100d01611032104500e40000002c03040c0000c1155501c508214046250265560 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 596886339 1250 596885089 596885131
    0x1107110a0602010b030a0f050a0c03080d0f090c150c05070605090306090106151115072606060418060b0a050702031506030607030e030d05040819020a0b0c0a0207081203 74
    0x90b01c1300d040365294141c000140d0103001842c080300c050182c903c50030903070710210312545400b5000c2290350320075038920400240a80e8070f10038a20890014000c020810040c0c6403268880701140d01541c01988225154400020503041c0030304c1002e03400581c0041142c1c5591340f1100c00400710f0300f0000071280248582004990303510018090700d0196042d070b445440c0e400390307103520894440d0780c085a00030301402040820000510544103540c8224142c0e111080900e001c0d05140440d5880c12a6518501c500e0702c0c01e010881d5110002c8504442070b2001c0506004043c1024a00034289913000c5040003800203030a10007150004041c0641a000b101940c004108940200310f008404841c3d899168000000041c1c20340c0c001c0e4403a16040d00098103c0f82072000c92580c1c0000c8030b000380c03030903a00c1141c081050321400d4003e60040740d0300e8100c0c0c0f018100850f101d43e0341400000c000b8000c4d40107840b021401c104010720030411f40006103030440c2260f083c084110f4091200c3e600c10f80b244409084c000c610480 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 596887589 1250 596886339 596886341
    0x10309150c0320092e020714060309070504050a0f1415100824030a11030607210e0c0d081e04060c1b120602030f06040b0303040e06041107110a060201 66
    0x148411803d41000c0c42d0415000800190070b00302400c0d1118500d0449001c00104407250a80c1c0712a42550000c1003050b040680e0000100030030000944951400c001f00202810b000c5508001c4540640e00407030f15459a072000406441a001c100311407614000d80c0141070340d5034828060103016529002e1500d00d4040040c000320401c2c00701c411000c61001c002043c02c0d254507220140d8008070f604074401c0106040d800081c207201092000756a265401441501d00c0e103411b04ca03242d00b1000707500f0895801040780c0d50045050380300501885c0c06a94583c4160741301c00040c803294095010041c040b00e281895494031031201d8014440c0c5c03c650103032061206c0b4208203084100c03421380302c1c55200c2c4121112140d40d030f0140368004642d08180d02c62a0003000030b10803c0c1c028044c00301c9110311005078487c074110b0344941400200401d803070b100f1070501501419644021088505a550400910445a90f0381020602a00400c6488801e01c07000113422010b126000c440400400070403100f01c007086548613001c80c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 596888839 1250 596887589 596887631
    0x71a04030e27010611280206030c1b030408071205070f06020f0d080105060d0b040905010203182116051903031b09050a170f0a0b040201020706080906010306020306010309150c03 78
    0xe185940b00310486d0b00030012000400360903c00451780b4015401e80d6902040c44ea0300b06403044041d144001c034021120a0019005001c0c0c00e81150086041c149044210b503504d80117407092a8010303440e08856818404140150000b600079080740707010940e581e10700250b9400c2d0040b100306c11400307145039603078102d4483c1003018103c0704005d041a040c0b22a006103440140070f80201148d005030f8800d500380010341c003070010710700c9003041d1b041c0561b561001d10002420100210610030f00384030080844080680700005882007a141881031410149982c9481c51030322020b1360014080003041081c0d0001c0550540049407403403440811003048012440050768642d02a02905501040009060000c103007020504030501340c0403000c588807a521034098500304224880242c0d00c2c070340b00a0810066580420001000700400e20305030f01c03140b60000b040c0391555410300005004640000106405a10030b40201e040c158214070710340108010550b03480002d128084500c00440d04000c2003222a05861000d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 596890089 1250 596888839 596888867
    0x160602030a050f09120105280b09070311160f0c0e15010e04060b0f09031504030c0b0411060307020a0c0506070305041e170a0611071a04030e270106 65
    0x1c1d0500450341e0b00c1401139040108810340040c640042c0800e941400d006050051f0f0101c000141c401c145202480d00c50090902003508480c00d1200060b00381e2501249070b54005520310f4000703000d031100b203080f004034403801034202040883e13218090103204012010403c000c0c031881070101c3c116603845808002040c1160404111003550704540d0a40d400344a1108402c42c0007440000c003261203074175285850b0400001e00c0c24280010030704088600f4208107100b644407a4030000720080c03801c0d944c000c3c08200d0321880101126114408201001941140070709059401002c2e1034507841c0c60340000359903a002c4042034803401c00c0034900080d42c2c01c1001c211100c058040d91503510f024204800342a10201c000c0200080c0019038800140608a601403041c0c8588104050600f0300b40606100b0300b038a01c80d1210440070302c0104900c0000858204540030040d003540d44801c120390341d606003a10001c00c6586920340004079441029028500d407100031214041c02e20003c44a40d0300c5010460f4800505a20 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 596891339 1250 596890089 596890097
    0x607020d0314071e050f1201050301061e120203071208030610081b07110303030106020304091b080412030f0f020406030e030c060403141e090117090601060e0409060608160602030a 79
    0x1c4c0d5007070580b480c1020081040c0c6030900d68a000c2011596030415401040b5107121118170300c0050025140a0045400074403c40e030704c0000c4400c1070501000700b00c84501c280d0294940307001803041103440500a180052800000c20b07800c50701141040500d99000b143e00c1e611800307080d0740b00503282c1d001d201401d0149001440070044d91603d01310540c81030380941c2c000e41ea0104904103440d80350f90100021070180c4500c0d03014549551420401d5025a01344800184e0600c40701c203010404e1660007154140e1084d0801c50080842000340029002441e01000140c0f00c0d6040180300800000160014812201295010007060940c500e141d5101d00816142c020103403c41c00c089030200341300b124403504441929a05500d030090101140442e4034581080c01d1036104041840c60f000d6030402d140101c40c083c1c000d0501d501e0701e800c000c61030711480140611402d00c044400800001c5c0c4540d40704010260340302d0010800680c483d8021540c4200e50f0a01481d91000f00001255841c80031007a90008039407911 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 596892589 1250 596891339 596891357
    0x40b0a0308031801090606080309031501080c04020906090a030c18020c0a030507051501090504030818100e03041a03060f03030f070f21110105010f050913060e0607020d031407 77
    0xd002021008544403c00196484900180218070148140c0c0700500400c001140e503102003905040c02c02c1011303108102c0c05000c240c01000942800f00b0340c454024170844006035a0000c500004956004140503180c10000020300807080200250760300003503403014048900c130583c2c10003c51007640703d0713030110307081541040c03040100003401100034141c0c4520034019114190988009071110707035800d03403201d069143c440d0305000c01e00d500801200c0d002a08550500d2684040d080d507540c1d40e404844d404851180da0b1100f902401c1d00501c02e4602400982480082074000203000702201c1d041030b07a040b440748100c2c9442c1074803407a00000706c0e9140c0200040c01403c2c40c8154440d618000d15550064441c0f009514180800400d078a200da60302c00166281c101008210026103821100c0581220071004002d034018030181c0d5a0701c51644c2d000e996001c040f07a10640c24600711000e050701c850018201c1c400d10050280c03264021400d844664070342da03004c2060000403010002e8480f401d981120200704442c0b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 596893839 1250 596892589 596892601
    0x90902030406020415081005010903020d1403042610090b010e04060b10030f060b0c120d2a02060a020708070f0219140906030604210c20040b0a030803 66
    0x500919030050242c84010f04299541183e00b0b06401c20105103000909a81c04010488215545c601b01820b03080c60010403041c2560b011900413900c04a01400d03012520000700445442001124003604e0171049031081c94a10001c0400c804100c95107400d000e004d1800c020300304801e50b00c100440c85804c81412005039180050002c03420601a0055413001c0d160360b00c0030940d8a580f40c070300303a1808290781c1c0001d01e190348490075000c03106039400900342a00100000007200301c0010b0b844d1502504460308907601c00045c0c1004c8014201001900c00a8030201c250a042004620320403021210540030f440d003680d18003003003100302e1041080042500c0c0080c88504042115007030910345403880074001c1c1d20801c20031304070401d5800b8640d010501c900c0d803c682224990400c000c00c140c1080080d40185a80e0030a13550300540e04800740c071b80c5594020040800e07110305104a03003002115400040c11981d0645030180c41400d2048400f0701130150341080d07094811070400c255200c0849400411941c15a1244 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 596895089 1250 596893839 596893841
    0x180906160201091b090e0c0312090d0215040608090604020105160218090313060804021e0d0b0c130b07030c170c0f01050a050c0c070b130e0f040618030909 68
    0x1405603141190759034448000000c4e4591840e81070f581280c01610045442d03c0e8421044e180415001c11280c1c002c00c2e0b411040d0344000900b160f03038001d00344605031a1780700500440c0c013500b0240c001950006640903034280b11008a0000e20a03240f00c0d68034181d5690380c41303004598070042590020b002031001c12002070484489206c1402d942d00c014008046400300c1071000d503c0000c203440403003807a000041c0652401d0141e440040c0181024100031015142a8002601c00e035110103440d0300c41c05640b84042000d5664031403072038030360354400303000001070a21464601084d040b4800c052903001c0c00180101c0d01005400a0303504483d419640c06108242c160b40381880d0568103d01c0c0304540c0b005011540c0c440b542845103617400109178000107060703c1c120110400343e45010703001000d00a81000399110050011460500f0340d5809082241da900b02d140c03001600141d25404698000c42440a000c40709103070015085c0241d00904007402180c880104501203140100e0008020900c1c21408000000c42 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 596896339 1250 596895089 596895121
    0x501090602031e04051c03110325020d05120705160b040303060b0403050a230712230715020c130905121819090516030509060c030c0d0b04060b0405180906 68
    0x6c0d030301d00800c0d19085003850a0403900203a85001003a2a030805201c4460040503c00594000d01e1005011440c00501d002c0d1152103488400310546c0b509600081151b40a00100c0e0b0440d0707884010025403d4150825550410003034078200c002a0416900144095404069034292034000c40030704280b42203945c5020749407103100c940c011990f01c8180c041e0b2500d481444104020101b2903215914240b8038038080460080c1c80118120024003c84c40c6400e1010000701c400542d41103013400702008000450507441c141104008660004025108404ca2201a08010700c2203111b44122981f0f095951894942405803140c101c2c107000030001800c0340c0749081c01042201032285032050110584841404054500885d610981d480f444031801d07000c075a040c0702e0158482d03c01d00142c4643d003000c1c11030304514131014203049900840410400405400380c3e00c06510307004028010000a607581c0c2c40914560001d01c03500b4414100c869600706c050f000c060256104401b01c401804180c1e03540c0c41040c240b118 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 596897589 1250 596896339 596896393
    0x81b0f0d0506030f0d02011e05090304030312090b0114041b0f1b0f0507050109060e09010e192d0e251d10060215061c0501090602031e0405 61
    0x1300d0901c810540300790901c48844d890030789500104c0c0d071002201c41d00b22184284000d1514841c5007104010164002205850603a41d241c03900c22100c134901e002c0030000d803030700030fa015003890000c00001030008600c060030b0750508001e40f0103004000801d1440c80402d902e08410074013141c01c43d202c082e80075108500b645030407070101c0c90cc8032502d02282c451010303a051424003110280e1103000e041c002d96030803044260062000d0703c1c1c4a43c80c0020540824402541032117402c820051030004540500051601d1400d01c6048520412003140c6881100e40d55880d00c041ca1001400c1d818000160040c003401000b9100c0d03403d01c018242c11042c80940304040401c3c10b81c541840a41144c0800e418000c4645c0802081002c581c0ca149803e0460015810708070583c0700c1410f56220041700f6500c0001515840c0d0300c80e008844011030004100c100c0c1c3c514020401c0010100d5280114900401520303502031801491010000e1018011040441407840010341b4090f200d40d1061000f541e4004141b083c10106071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 596898839 1250 596897589 596897593
    0x5031b0903070801091218180b01090b0712030b0f0d17070b04060905150108100b0604080a1a011509181401060203030f09010b06180d0c06081b0f0d050603 68
    0x1650303281c81c80c2c05c6568090b011104c80e054850340c4240c06500002c503c02c1180c80e0b011000c0014508060412101d030004e00030789005441d0521719040780e0007440303000000c08a10003007a03035035440f0349030920284070503002c1e900100e40b9087c070340c81c02800c0c05100e200c1c3c483d40141500d1404d200507210103d94604035001c4078480c51040003440006240c80304070380d0180344641d0010800c2290340c0381c0303941803502e90180d843d19041c00c040100200c89000400500a9200141c00a00c21207a40c002c280705204d42d4201081a1088070480c8003004030f00e00e001301f8048404000c4100b00d90b00ca0011069894101d003800c00040d0203c4828072400b00c0340300305100e041c44048000110f8842080402c002c0000907400f40c0b0260304040108100220301420041d80888910009c00c10b0011a0000415501401740f00080402074445988490307254403080508e100c2d007040d41203030700c2941c171a0024001c03101118135040c0002c3c80d02c45424480702210a550040100380c102074241030440800000800d001001b280e418 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 596900089 1250 596898839 596898853
    0x3020c070501050c241b0304080304110a0b18010e03010b18070e041802031009021f05070b0f04233a1805030c10110709051303080705031b0903 63
    0xc5403442075180b000c2e10040174010282e24000b40311118401c0c2103004a41211410030401c4000383c010402c60360300660142c1030f4011a012900450000c0c0095004540c4000001071a10055951881004c880718802d03030720303074450980c210700381400e075190701040b19008a001711a02c22100000c00c4140d512a6891811011252002c000903040d40c140c078501130322031001c010384001036050a200c5800c5c044043c1c3e00034058807000741c0c003040c24200c0300d000b00c80d81c00c50700090741c8080307510640c115000300d0703000242c0e440307a400d1400c00070295980030b0b6011a841100c109144102046034014090010107860151108040e11404051902e95000c12400c800703201400240d030707040950a580300344002c1c0e556544000c0ba20182c0c28020f030304054110074881e03401401003101c40d59034520242c03c00c80c0340707161420002e500e28840f5454040351703070400281c2c103080c0000c2150035a0f5a075400300d41c2d0344c002cad5955019070f00e41d03190030b0b1041c3c4000ea9070480020714280890700c2100942d0001d003401e0b00b0141c226260 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 596901339 1250 596900089 596900113
    0x315120b1515070c09050f040f0201110c0a09060503160b0f03060d120905010305090111030a180b090c010206160c02150c07060302092e030e0a08030103060f0c03020c070501050c 78
    0x10b5a07102210464544034060801d0003460b070644115a8007039000c209656003801c1031744448131813000b0303c40001d04015800c2d0b204041030394244600300b2100c00203054000754540314103c0d40c001e804140145806489081c100340c65912801071030b40d084860a030541032504c101010f62050700e0744020500c0f500b0040145000000038100c44403003100580c10b0380c45403455800c001c0018280d5002900040c45a8145030880e0f4401c0c0d88801141d0b000007043c6000a03070010a01d200f034020010805010301258446802c120505102054028441c1c009900b40c0b07043c1c1d034a149069014041c0c0c1c7d24510000382806600b003005042005c0004420b02d0741401481c2091441d0302d15034503042c6681c100000003500420a900103040c07501800540720700840302d4007040c0c800000020200d5000b61400c3d420981c58090014440da000d0110780503468002c900756650f0b60712414481e02600000d40307400781c07a916044500040c10b10904c2510f01d46403140000d855214a000d00454071608088141140c0d03014006440301 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 596902589 1250 596901339 596901379
    0x9040f031b080903010b1f1d090702030406080a020a090611010603080c0a170f03061e03011109030f0a03090605070c05030703030306050a080304120602030a1b0315120b15 75
    0x18281e8410301a0603030f00c20108043c5400d55001c031006a0240140d1100c861000309501641c0f0100c98052074051300032018100702d805980309035110940c01201c02000d010303405070301000420079201c8a881d5046180ca40c00540d01c100c0c41040c401500080d00e180c41440748520640301c40341c259447c0360001c1040b0b6101c0d1683c4049034011a0b00410744d5005c009580e041000c005080c0111411100d076aa08041425540b5074040c800142254480c03800c070180c0d4101c4a880d0a403440d07030b015000c3d000304609000f0801c0ca45c0c055010400d50b80c881c1c41001c20b04007911500003000025a03506548060030103144c46002d9949070040c2404a40707035203885802184030340341003018000840c0130350307004034078545860140007440034150130039072003500100303c14400f0381150f0700030f1142c1c0703903001100681d40d0b6a0100083c000b4805031030108403d0081c01885181c60b0380c1500581e03c0101402c0240b2205039942c1250709844018040050645103000001050b024600c1d030001460381000e0020304413207001c100c03044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 596903839 1250 596902589 596902637
    0x702040912091508240d0b04050102030609180703080f0d09110a080303070206011203141b06070302071e050a08030c1305010c150c02030d0e03030103150b09040f03 72
    0x100000c040000420201001800100545000742840d800b5824071750b0102c446200e2071001401d043c0c180158001140d00c95918000800d90822810f10305800c0a2811a01035842070b200e49102c0c024520121700900c90141100540c2c3c1c16070301c01000b55528603920035045070004481800d0210040c0700101d0103206a00030360740094400c51a4100710007481c0c00300b1113004441d822402c40d5500601c208401243c0001320716056a8140b510103100712914a0704643c02800310306031100f00e060100381d071001000e201000d956441605000d540950307842800440480c02480342c058034907206403040d640103901c200c800c112510301a8040e5401922039844500c1c0a034000e95084210340d4000070160322424140705681c0203840246070111511206880ba1960b4401c12024611030030356800c0c1c07111180b8001c00c00c40b1140004c108040c0403080041c818941c4a80007484140c80f004030f414040041041248104405000d00421400294449845640104016130380440512081d42c441410800e1014246 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 596905089 1250 596903839 596903873
    0x9030a0f2109090e0c090c09131d0106060f0210050c04092c012c010f05090a0506060303090d120314040b0402010f02060c030a0c05090d030c0c060c0c03060207020409 73
    0x420307029103443c3c0848200c5003050701c410b01c1c135008060300010700da4074241165081a0807280340307601d948803040041d007031517a1000c01d0340303100d07152010400304600c0da445000b4041c1000d200800c2040c1d81c2e0350080e948007001207516001a0421880950044c00a6006540050038a98501d041c0340e244c40a0404035803070b080b04000e2920001005405603032410030890303080c1e43c100340240f040310001e40d07c4007040302c4200600303d5101d5400b601c081e4070200c00d41c004103801000e94410b120b9414498601c6450362120041518039010380d1000400900f800021170301340b448098888140741c030f01c94542d8021010042580e808040e110101c650110041840c0c0c00d018902999042d4034a0500d4800500040a2a0301c2c1c2c2c4190b400c10300c10070901c00759150a03a9440b503062000030840c14041002182c5900c10303c441140d1084000c3c07003410500d0b40c0800c075100498851a048600b00c0c0c3c9826065030361890141e0000c18104c00c42d00184000f844a4000d0401148040d00100c0c00e00d01c00e80e51030915008640135 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 596906339 1250 596905089 596905097
    0x1e2711060c160902040302010e0405041e080307020106080309060306100504030b0403030f1b1d011716081b091c230c060703090e07020c0306190c0509030a0f21 70
    0x1d50140e4060b04100c000038018001c0452400f4075590028100c06c13413654840c3c0c1f0880d030780d000080910031500e045081011101c00f01407011440e5142c103010f10b42050310f000c401507180c000042040140007003224500b0f1001084942507540c0c000170050404601550482040018440040007030902c1d40701da0700840c407940f80400c4020310200e01c03002320f0f88511404840c0813514522004034541040c580d1110036000c2c02214941e0280c8030041e103581c2c4041c420310503050307035040030004008429482c01c91045c40554443c540c41e2140d0b51030039200440d80d20003130311f9003404101e0046a45851040c021080c3c64100f819002c1c0a039036203903103031440b54101e840d403d4001005002c0681c94018442c600035000220b80840c100009620010a803400328015a0365080120004c680c001c5c0c000c1011b1041040000c04540f40c41c6803040f00303909a200a90701d104841e42c02d1494000049010b0000c1c0c0708600e03400b6000303041001a84e110301220002070760090302d4100414404042080c40c98402000c0c034a22071715 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 596907589 1250 596906339 596906353
    0x11042c071505030417090f0111010e0706020f011b0816200f07060503070c2303070c060f02120d1e060807030201020c0639101e2711060c 60
    0xd14000c80c01d0f0f4100c0115550a08000758040b659401f850006030b20028a0020762441d0103060300b900404032501800740c18411464002080380d40066482c0242c82114000e002d4450181480d01c1c8640c50b032442c110124080d40f0009540c8025000c55480a40071f44ca8032030106502d0092841c183d003c0e104034040c107a0000400c0c0d00c2103403000c002c8080204a6440d020b4958074012800800a40c1d180000a01d000505040168003904400c00d10f00384986202c01c0d00da82c1c5220346807030980010140700301e4021851009280a1040c004103442d240100c0003090f86242c00d100001100c01090000c20400d05401e03104001c01180e070040c031170400902906001000010b0460001a2070030100300c0e0b55a01c42c40040200a480c205030a480741640d6660b501440c2c1440140c060903182600d082911000920075200403070b01d600950340041d03900b18607210340c0300c100c1c11644c0082000d503055284561603c11a10f9000140018a420f80c03c40b0980110b20004820070503100207032003580810300c3d006407a84021 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 596908839 1250 596907589 596907593
    0x5060d061505190914060703030212070e0a0b07030f0c05161e0504111b2509050702061006081b0c0708060105010f0906030c031d0a11042c0715050304 66
    0xa0b0201e410b01e1040c04c28556041c0303041d096a14080c450400300d4003510000c01c441007014000d4055610094522020081901d031130f26004010002c503500140c0b14159074040007442840302c2c03088424540d0036589022880100c04030a945001c1c2012044540d8030440c1e02280c0e240d1030040c00c1201800a00002100038920f14074101414060350f084584180e1401c05031074080c0d03290300203c580080c14075803000000c4c03114943c950f003080300041c40080b450301800c90010202080c200d032a001d60f0380c20389003004592144c01003240d98180495290440610001042c084c031070044444660040c1201d034a076a00c0403485551160580020b2075079102503101001c14401801c0901615014050a18015103600c401017030062143d80b0601c685428142d65140c80500140320360000c4000201c5002204010b0140c503198507624000c40c00c00741c40c1c1c0e074000304800700c80c1d24107406041401c03a5102031003da40d800c038416811142d00103406101c2d041c894a280095001c0080d8000f8010400d10388074245c032440c0078 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 596910089 1250 596908839 596908867
    0x912080f13121208070908031b070e1603051018050a060b0703110d020309030709020c1608030a03110c100f09020d0b0f011212031508030409090c1a0405060d061505 72
    0xd0017907000c5c8a24000c06004030b19000055546009a180c07401903051550780c0001e040200980014507001802c00400c524203501a15280800100c1d980801240d51400d52043d4514840e0207684d035100004009408146555088a5000300b005280060388036611649030585510442d000c0b0003180c04503200d6804460140585000a2414005145040c0540d00000e4543c00c2600465101c0da41c04201c14800e52400c000342201540300340c4100b102503468008070b0b5601d8120702030110029050400b0500c055802d1030540e201d501b1098000c1903841c0c07c1003800d20207001c00e03030120b8007115a605902c1300542e035000b1842c44150f00650a01d00d00e400d001c14050302c0035105801c01d80c0c00d403e0345c00200001410319880c6148000300d030301c0e0007d14412071a00c1802c01c80e0b03003548034024501c80405e010507425001d80c08581101e01caa0190024140c0d600c032400701c5403c40b40300100005134140410030103400c00c4030050180c000c00340310000d44151507030911000d074009425608000b52021800b82c5a40381d070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 596911339 1250 596910089 596910091
    0x120f03011517181b0609090403020705030304090e010c09150e011205010b030106080a090308010312110109030f0e1903060903050408030c0a11010e0a05100c05010509030306010912080f13121208 85
    0xa040781e40c41c00284a20100344144106c0070628069190320b00010306240c8240031110107070000030281c9560f9590741c01000c2c0a889001140c986d1940707010860a440c6020740c40003000c41d40c8020205041c001402c400307440b80036003826507030b040c013075030140307503003142d9441e1080502919020090311307101c1d4100003004268107002059026154544442200441d4002c90741d43d0450b0307400f843d000418080d81c84115140c00c9030050380741056080941030020075811484400050030240c2d500000aa04d4004215515880d504640b4080e40401818008103200b0340115072024041d00300b051420b40c0d913050329841c0d43d004900b00700990b004204444c007040469890011007a00034680750701c0b0601203000003a08421180b00d00f42c4181e03010307100f00310081c1c0141205400c20350080000c0185180c9050071070b803254400c491860004620000c045940c94440c0e61a03003050750450280c5090000c0713043ca44010b5400390900c0341403440342e41030000c1c40012848558210a02c1000e0900001c4070103103002e065140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 596912589 1250 596911339 596911363
    0x80c011b051206060c10050108060903090a0e0a0b060a08010303030f2d0b0d1b05010c080f09030312070c11060301080c061c051008120f0301151718 65
    0x55409030a010056000c015181260201040703041c5644031400040c0b1244229040c4800740c0c010070460400e480c4655019904072405001036500703680d0f484c0350140d160700c00c6d642c0705c50344414854018055006800d050b1540802c03402e07400103405a003400002c986400c000e081000140246006008256050217036440c450038450b0b0078030003012182214110350301070404a802d048050b01e069109031b501900000001c60000c0c2041d1404140ca04024121240b01258003803403c1d111100000c140d40319000021085800c10031690820340360b10039240080e48400c002c0c40d418841482401052804001c0c4075002c4c0b86103449410406400385080c1c01c00c10707210b00318284110710520040080070000318841c80b80c19012140c4c19600c00e07502c0d0306168048207801030154140c0c98201080300c41d4100c420044141ca0880c412038980c0170300e4034035070005482551440c0c605a2001d200410500d81d0060301010000c20030b003494030300398800b201202c40300c40c030072920346c40c00700f00349440003018250601010710649 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 596913839 1250 596912589 596912621
    0x23030c070905060d0605060103110c011d0a08072307061d0d120c0f1202060717060a061103190504060f030b10050f07050706020d0f0c0209040b070e0904080c01 70
    0xc9080f000198032000000d102503c21a00d03240050426840703603000a0340b0800c18204240c83d40c0b2405060f0f80240f0b180f0b561001800c59065016620322030018908010729404852145480070940d10349003000400c82c0032242003002d0511110b0100c009000e0300016020303d68600c035002400260410350302d0000440076010315800103044000c03c0010440d5400c405c140c0c100a41d51a04c3c51600004041180c04094aa40386440b003031707154a640070810302d02405040e40c2e4440341c150310038507859405500391200b60740440003100c01c0100600810f030580340a0108410f80b81000180c0d07509070300d00140040507900154000500f40a0207400c44e45503015400e00e440d041001507c4140480c81001144905030280b0202140480c4003101c41d004071504150b101d41511a0999180400707541e9445000801c004038003c0406075016503c221035507019982c0080c07a43c02c0640301c580703c19041d611701501600411928076017200f015100c503107035140214401d101c0c49a488120030000d60854001e40c0200d0001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 596915089 1250 596913839 596913841
    0x9050d2604080306220905060601170406050415050405010603020a15050d0f0e070303171510120f0608030d05070201060602030717040f030f02040f02040b1623030c070905 75
    0x5800040d4120360700c2039000c0e10350b980d20b4590b50002941030500c440700c1401016240281c54803c0300c60f80008103090301c180e0494545440b1a00192600314009850b4080c5522030400100030420b19005281c0150050400c5064550002011800e842c3c0c1100c040e03405a44078a4108114142180410010020b502400041c803000703040c01030640c4903000443c54840e03101c2559400003402d0794008036401e0f0b0000c1c104c0383c0c49a92842d01a0400a007002c0300d211000515000501225501d1888036020314020f00c0c5030a0566149020382d21000d002e04c0052203551755460b603108145d0319200d64170162201600542c1c0f1850090042c02c103903034004080f0b00442e41070000410420f6000405d071021190b0003010503045088002c007041440c000c0750300517026024800d070b000040c0a042e031040d07043d0038000d0b0b40c04d10100407410511020ba205900ca0040064030802c00c020403a81804003d008291142d185420703010510f811400d0300280b00d40c803c41e016000080c0e140a008030800c007034030080189603410710003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 596916339 1250 596915089 596915147
    0x5040b160c020f1c12180b040e04060e03030108070e09070509060d06110a0f020c1503010501030b301c02060103020402030c0d1a1305101208040909050d 67
    0x10310800048000e008102100002455643d1a030842c13150700300074240c00034000e030b00303050001180102038010000b05219680150103000010341c828180c0c0c50003040c40f49003d103007031031405421030024402d5036003543c2d070f04007a51400380600003140241200c000400e003150400e400781c000b88102406d148116440b0303080420003a121004a90b0340030386c08940c0c40300c000b851418900041c084131400e00f002440c000582e8a0781c00c1d009100303423051050703541c00c403400305046400340104228004080b001e00481800100250341c03003034200490421019081840484005981c062920140e06188040094290169546030801c2229800c0703103040010510009800300350194840c403040c00068001c2c1c1e0000001100801c0520880d1101c01d0401c6041042e055030303841c0315402174100a40c1031703c2009000c042c1c518403501409001d02800c1c0620001e14264a072850202202d05054012540b40409100000302c0c07612902c213100d1000d018001520440205003002007042805880040c0400c1c02e4000e2040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 596917589 1250 596916339 596916347
    0x806030601060c0512030106170a0c20010906090b040b0f040804120c03290703060f050f12030d1a18060f040615020f0c010813080f12090105040b16 65
    0x70440341e00c0d0402240001d0a414128245003e601e0329403e42c1c0070000c00019815400181d2843c404078140548000d5210341d0128003d64100034103403c0002c1020103040200c800c41d0380c0004c1055514030002540040b540c1d2900f0507075094400584031011044108414001b83c4818139a0050380351b840e02d004c91600796250701e014011030081700310014030a0175400030010004030b210003a54100317200c0941241054000081e080a5007001d502500c41c40010031a214042d010700700a80b07042144080f4080d00304011b1010303060100f203900d64007003d070301d48010303002e070090005042c00c1059480c0821400104046006a080300c0200240510500000302003010b890f40045900284202c54020035001c1d8030700020041d11542c0c01c45002101100584254242c0001e8102d07010404042603850b40000d0000564a05500b190040c0960085100106c00108040010059031121400007400c0294040748600d40d54801c40d0441103e0b991740d010310040c445003807455079010360604401d000c8100c111400034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 596918839 1250 596917589 596917591
    0xb0910020f0d0806150301090b0111031911030415021b031203010605160203010509030c16030c060f180f1e2111130903180e27010c0e030d08060306 65
    0x190070091070b03401003044c0b6500c03500190011100546440e45079619450000c006020781c00b80140485c1c0d004694102c0f034803004c01a80e01500400140f40f60007002c61034103403214a004448011075010801c40400c8851030b0035403414084d891640181004000040203004040796003801e24881e03481051040304914000040f241551168503100340c0f5910307501074140c00160700050007903040d400e101c10405c1d4005d001014080034044082203030031034202c400b24201c84c02c100e408043c1400080d014180480d502400404103860080e20700a001d03000c043e404850f003410203070403a6032840049a01007207041c0400c170161044800791100707511040d01d07003440e0130001e4401c5070201c1c1014481c001450705008580720034500023100a4a00010794002c1320303101c0001d1180e250114041031005043e0541d8041c1040c1c4c2e403050b50320b808010801501d9071000c40d580d80418200d44d042d2440101c440c81c01000c1c081c00781c02440b8034251103010f003075003407501054106030b602d840c58403c0009200420a40fa41d0002c0c940d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 596920089 1250 596918839 596918863
    0x8060f0c0d020a0507050a0506070e0d02030703030c0c09140615031006120b040f02030103050607050c12161b060305010504020f0f030c090a0f050a050904050c090711070b0910020f 79
    0x60f5a540200300942d000d000e00c050282c801c0c0280390b4490180000895407901c6680b065a521a50101507410414505078550000c0d40507030101e241440080d0049451031202405600325402c1180c1c0d40c2519400d072500031450b0f6003072f4403524041c0001d81c203014000081c03100d24040f0660552600500942d0316182c00e101c0c1004012134100b0756104941d6076408600307005405801800610f444501039400ba60082c80102c030070707200344000540381d6407046055a0072540d0aa0190103043e00d44184a4026000841400c3c203480940c07204000003244506000c120743c44510b004044140303001e20290403100c05900c150300880c01000080c004195217001c482107042440d0302141c07240c0b00c4000300b030618000c8013111a005004882c0210300c80409680c6501115002c0360700700d161507158410301034004c4040e60024135950012128460b20f113860340007150300c00d0391403502d110b04039610300016103841c140342d00400e83c82c01d000901d6155400d0501d48101c66030035038001007076101c1303004140303070303980c0074405c1076 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 596921339 1250 596920089 596920091
    0x12020f060a0e06040b060120071503050601081b040e04030210050a060b16060b0a0b04030c0f180c020a080310061106010303051c090f080405030615030309040c0215090708060f0c0d 79
    0x81c001c1ea0003400c8c21010b1a80780499200607200008003582e42d809207003d0607445111004d034003071140c0c0c440d029091207046c041e520b40030141c860880800006451003510446a001444045400706080c807041d8822402a40100307140300000610320200d0308007401940e0f0706c2d4100305041c04941d0b000070803140f02c02d6484e15150386a1005041200041c048103014a0f8804180c00b00000c410b54480701402c10ba9000301e42c0c0010180d0342e501a10076850451285070804030307444402049200541c2d110f00d001d41030f58016100a100250b0350600b641e03100716110807220600302800d000b0345070311007650201418000010440e13541103031400703091400b40c1001603074015610240243d680c4074541000e400c0c59031011080204540b00e140503001a003181c01030600038030401000409003810040181c01c1c03420042d01451500c024102070202038060045900294410b24007507450080a0f6280ca902c55000342026108240c01c0c110041e09041e4050f1000c00102c5181040c0110714540204480c0130000400c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 596922589 1250 596921339 596921341
    0x702090a050103110d140607020f060a0c020a030302091f0909061a12061207090203010311010c2303071713050d0b0112020f1305061302041a0d0912020f060a0e06040b 73
    0x68800030186410b03007241c03003d001f11000d210303856800082d240c50108462007a102c0700d0780c03041c0700d04003100c00b00d20a003801680400324590202c1d000307a00610342281e02500380c02d9010405140781d00c801d00500700041c009031802104000703034800e520840740582168000500c9982078841c081d0298003030402501169001040032442c1a44c46007400c0014500f404182e4050f00ea5500c0601e000703400c2440250b0f202e1901c001d0001d0b075903110340c1903100101d5000b201c981c509407450110880c500c1d892811642c0c030b840100100701c0170420847c0001c43e460003852481d41d85140c140300c0c01100c0030300d03544028019441050244001030104101e107046d62403208500403280e0315400003030b0214100500103030300618501d0303c80300503800f02d4008601c04e120541d118600f124204003070300101e208620500840c80384020101c02e400f000b040c000c0010302e49843e40400c1241ca142c035103030f4888401030790040143e071000139100308d1104140b1001d540112501401c110340d010940d01c6a0311000000d100511400c0703050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 596923839 1250 596922589 596922593
    0x4030816020d0303020a0e010e010c1b050607151802010519020a0f0b04030906020c031b06090a0609080c060306090a0207170414090c03011a0a09050409080702090a050103110d 77
    0x180c200016074000701582080c52842c1000380c02075004420b40b8000920740c4001c400f5a5000d42141f15021a060307540141565064440c10b101c041556068000d255501c500001c03540c1e100805020311310300a80000c102912410408812299148011081c21500c4c441e0395000d84c0c1c010080e50075801d8203450742140e141420300100e0410711281401031030020482c4c19401804100703c0203d01c5a0321030745403641e0305030729403500baa0b0740c1c01c1c2e0f4912160f04d98000d000c5c1d070100e110040074201840801824030740c1400c1c6218005843d0003000c2d00208001000c0c0401080004010010042c0e40c00050b61005d2860902402090f08440d0060544003c2031300018000e040004030508908030a0500d0203c3c0e031110b40321025074107010881045c0b07034030544a5801107906a000002180d04079003802859040d40c00e000c1c03012010a402080c200700500c0b240d9280010140c0b01c1d03015284e4440e01c81c01500340e84400904c1041602c140180a2150361881c210051000a49901035198001c008440c10b0040b21058 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 596925089 1250 596923839 596923867
    0x12606130b0d06090b0a06080c04200d020a182105030d060e01060e060f03151c05010506100309030c11040f0e010509010507050705072106051317070503040308 70
    0x14011550450b040c101c81c0e0050040d240e0111544510600c0064069203540d44550203407406c6014241c4a80c1011030340070418030700780c0c0c4a0b129004404400714595040c2c2c2c005151030750807900e4841c60f41e54002803149640d5030320802c0312050050508000c8003050411000c01c401c00b4001c070101407500c2d10a4240ca00b801410030954405001d40a0140300081e112280c120066600384a000d000c03c0381d40350408218509070301a5030611807000042401c41c0c0d140c2e60101e1030003002c81c02154004d210b0441c0042500d042d48908060b140c001d800115560500c2014000001408010442014580b605807400a07612203035204515401c0980824900c42c20300002e4004c10407140d11018052070301103800c00b20300040d0003151040c8820402002196074582c4c099507e407198160052080c1c01c002000d00c49042200c0d140000812f04006c3c10758004400c0c0d0718041213440c00e445401128001040c524200598a90f980d1241200c00248074148542030769165681d00803400000c1180c170000c9590703402c01c1a1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 596926339 1250 596925089 596925101
    0x50406081b0a0e011b08031506041d012112030515121605190b030c120a090203070510140c03070516091b0e01030b01020c12030901260613 61
    0x407405025514442c000c1c024091141107040c190128180c410442d505542e641c141e6a05d883d0070484503031071036443c04158010011b055140b0b9512580500c004190814404031441c01d0f142d0102622146504086200c10500e0960f03194060a0303407070b1400030001030704072a04480c0c9070b0014100450a5104d8101c03c0c824280101d09281d0402c1032200440c4411400082c2110051010020b07444d9458807942445655002ca05110b8880c1c280c0c20f000700300c1d0321740310303c01194048030001943d0b00300324030403c10126901007039903034200880e101c141c441c06600d014070028000b860100c428050740f00e1100c8025102070110805100910b0021900d40d0b070240040c01243c80e91a805010380303114014a40c51004004a00e0107402e00d00ca00d4910360501c0070b640722140d541851a00e40360840400d501c007004401a00741d54141604500039440106180d449906c0c2c80200011000c028646401e0450001868041028696a0140205007a0741181800500381c0e58000ca82034a4012404102c1c1d0420405090 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 596927589 1250 596926339 596926381
    0x70812270d260c1605151e120423010b010206150102030c0d1e0c031e030e070b09040b0a0f030b060a0b030703050403090b07111e060315010306120305040608 69
    0x3d8414506480403c0400464422600d140c0d20f090301ca000b449007000c00d8200310720701c0240400c00032446440d01d801801d00300c0003101455142080c0c1c080843d03a0720505507401c0f16881d04203021504511060300c000035690040d20020010b240c603010000790741d100007a03d114986c49000031480c0c01a4424402c86038081002c070101d440301451040700a00c44031a43d88100d10700e4031005040104648100039418229415a443c3c1c40e41003105083d981480b1200600101459900e640d0b488141905000b4030004013210358007581c6400f182410310054404106610340704110030030b828040340300c02c0d800003c203a941150071034036165038120100340340007219045074000b50400301c100100d850b8140c0026120b030f40b0940d81c110754581d940f10006614010303010001d10400b2000340364005400d0280903a02e0386200003903042800399101000c600240d0080e60044014480e0705584801542c06d401104010600300307001840980c01c1e502d0040480c091030042d03008000181d0007040242c5102d05044030054 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 596928839 1250 596927589 596927663
    0x30709020309030a1106012301210903081305030f030402060702030a0f1b1d0907050a060c20030d030f142a0f04030311070812270d 58
    0x30812072403580e41d0b500090002e0000485c0640d80340480200852007030f0407140410f0400d102c500a180310040c0a031840c0c501d4078104010040091140802210582c1540d1340002002030803c03403904004040c00002010320004c1c456450740c2c1800510004100d407011403a45840903202d44540c40080d155205104000e0341c18400c6081c400b040c40f41d801c0c07504100900c41c105075182c0a044a040c49084030061107018078082d003000d06d803448542c50041d40c1d640481d41500ba560029101c50029041c40150b4201400103111110103100308544841000303214080c52001c00b0641d4034070030004c0e40c1d400d40e8904410816480712080703000150316070845002d0000c1c020000c200d43c540452601c035581c4840c108030010030b00305c0159000c544c40314030407600c035071954030603051800781140c0b003c4c1c1c0d015101c103a250708148100140054111070500291800081c850012a601d60440a1840c2038142c110000700c4404400452420b485d5120b031603d10507242e01441a5240c000c7c40c0207100e0400e80003140d260b84107 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 596930089 1250 596928839 596928841
    0x3181c0f1202060a0911010809100c030c090f03080901270e06031b0109141302130302130b0904140307060908090a1406090625060207021e0904020f0307090203 70
    0x1200c1c00044050140c01c641c211101c5a4801150700e00340d407440800a00045600a09075046500c1041d0007503002c0d04000031144071901140c1610110751900100d200000c0c1e440e41180b104075070280040b001070003145032040c0c940381192100e483c54452014020306101d906030705240c02c500d030700e01c1090b006580e8003290b960107940c51900c33100d0044115012031003801040210070309401001381040e08960706070b403100801030a01800b850802d13003000c0707902c1d400300032111726a80d101c2c564002000e4900c400035510598601d103106000d22406000c00040c10300e03090100380742e8184c0720008055070168110280e0300e500725010380100d01710f1188080140c81281004801414041e0380c41c0102180d15041d1201100140d86610b0060281000c00b030701c03a07020034104400e041618190b400307070a0f6000d1543e401440d0b441d08090504041031a800700325142c1d50085040c000350718191100c001d0081d80308c806402e07070001000c00075800d01001000207105891071861688140c03020003801000e00300d002021992 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 596931339 1250 596930089 596930093
    0x11042303100e070608070305040c03020405132901060c11060706020405190501110f030304060b0a15080a0f0509030d3206040b0f0d0602030402042d0e03181c0f 70
    0x110f80d00ca000c1c030703004101e0340c1c40840e02d02442803180c2c9218903004606c01c1031042c219400c0001030000038009000410034a1510f4010071740722808030482443c01d100b9004038080795403009075056016400801408080e200c40c00102c0c00040096501c58004c65952795100b100c0d1174004001d004036006550000d6459071030b882810f40307444443c015104262104003160002890850365002205c108540a40041c400720b0300250741034200c05032041d03000340501c100d81d40303c0e000240c4c07915103290214005003400d400d20001100510668004443c607000a204504c0c10b00520342c3e40344100b40b45144c03810742e81d50001c0c0c1010405010301005500550110f0118007802070006105d600554038140301c0c0e868080382c2c41007841d002d0701c1c0a81075400030b894204400496222140250001030083ea080340d100c42031110b5082e41d0141c0c8140d0342c1c0d130341c0742050040c131002c4601c041241c0b0192074450b01d90b84108281114140c414084503040030040300c80c2c40842c022000034901420070420010104ca01141050b81 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 596932589 1250 596931339 596931343
    0xc0312090201020a062d020a1b06021204080d0c050412080a030603080418110c060f132301150f15050408010e07180c050306120c03100f11042303100e 66
    0x4503801d01c0c84400302c103a50444806c02c034861058240d01203041e4010f0502d00364918174688440c180105001428454182c4c01301c004114101d50889000da00000d2a900441c0c0900c0b613003141e0a128a0843d003000c2c00c1c100c42c0e0320104950b06020300b8000d80400e041c01e00c64031036005040655403144103103441d940d50342903403000400b85604000c145400d0903d0754030204c00d604103554000000c00014040717900c66107415140c440b405403000d0460100d42618002280d220010004414984841c1d51154200b06156030300f10f800104040900403078156040005070b800b0802442500c011840c2002107005124041d91a44250360148049500b01104401520030106090040300c16032402059428440545801100d84012011001c070b17606001156031800c002c0c020b003170718a40352000c540011400c2e0700001d18007c120107454144589801d2460040c4004d0b000c2c007210380705851006c80c201400e211034400e2a11460f503082c0c89954010500c01e034540e030100840e08410f881c4000400142a059011035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 596933839 1250 596932589 596932631
    0x3010c021c2a050f0102040303080709050904020f040203060616080d0e1219050c100605040f0e060604240801150b0c0c04052805160c0312090201020a06 67
    0x10001c48007007a024400c0c1c50040c00d00e0244900c400900030100e00b1060842c4811280848040c0c0305031080d20f4070070780c0030361003440204003450217130721043d0031480c1c000350003011801140c01990145541e04107010050f104c02000340e0105104880140e100c0e41c803400440c1d428080d13000d0410070388050070b04070010b000c4650300070203440c03504d40720610511034a60340c00c0f50740300100c02e003071102c1c1082000400c4c4115420580034203140c50600d09513150022840f800c900d8424a440303d00c0c0110f41e1030404000c41d14181c402d00020300410801840a0000352900369101c040c001c0029004584420241d100c14011501c8031812440c00d0300d0180c991074948a1160080120000200d05441d42c02070214901311004159004030050030300130304951020400b0310024100c040c103e0100300004401003a004801d010700b000c01403164600c0029103240100c0e10ba00460046101c4d10140090000d014001c44e50100312030302c00f440c2e1f40d000461529186e100403450305402c0f64010b41054600343c114481c030795003c1c00360 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 596935089 1250 596933839 596933863
    0x301050606120f0612011103160206090607050702030a0b0c0c0c0109120b06060723100501180e010e030406030b04060b03070c23060a05180f060106031e02040f0f0603020f0a0309020f03010c02 84
    0x8801c00c01010400b07038bc6d40c40081c1c46c24041980000e0010f5000343c41100140001803000d41503460314041680c90403c290304c2500d480e04051400300e01c0b00200d0070104090459500300b46040c4890602c0d240010f02a001034541c0078108241000004e80d244d1501c004580303403240c3c002001ca01d03011800a18100c0814902d24501c4940a0303180e0036081a009030040c18180d641c03146154034030414040c2818020000d4200f456101c0d500d55007819440030050011300000e02490300c000c82c01c007910740100030807601c20303400c2104440380500610411035805240c1191982c1d00c80e014800c482c41d641d1000000d5500e4885d9498284071b204c003000252190703600010f004500c0074030510307034094048203069220078100e810404280c3c040401040214400d400918009070400306074034035041025403a40c00c0c0e0f072082e00a0820889008420803412446c1e1710000002c0406113403c60922100f0102c8410920544510008054a03240c645e002e540d112800c8601c0600b00400070042e020200c0350103500c3c0d00ea00210 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 596936339 1250 596935089 596935111
    0xc030304050705190b120603190b0a11030c0d2a1218031e030603021c0c06090605040312142706090a1203050c0d0e0301050606120f0612011103 63
    0x107040554090100f600050705d8440824500704010341035000c004400040000d507051041240c000700398011491205a0140108500c402d14503280400c8000e950603002c104200090400c10490b510350101c0035034680d145c0803100818800303000002c0301c0c0407035150303444110400c0905031980329064000c007e2160110042d42c06025031000e0902001698402c1407000d0007007400b21000c00c5182d04810031050803043c1c00d08000603500e40360f8003c105048140949841401529081711060003207040b08200181100c0c54485843c50401000401c140650f210051003119a103408810407030085061442c1400ea20440d140c481020034409080402c00f40c90509042c078010f5200c4529041060484a10750006030123140f806160594484045100590540801109014142110b42c0c1800f0065003418940e441c4021401a0801c041c02c641000d04058403428080207001500020500103580c0040c140100d00303016901c12005c241900c011444070f0795a035281105900c007408280f006540500d0744801 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 596937589 1250 596936339 596936359
    0xe1006060e0f06121906060201090c12021c030e1c0629060d0603080a020a0605060319141e281e05251811030105060c01020c030304050705 61
    0x91000510030b490b01650010020800701081c141c20340142a0802492004000201a41d40321801107034565000200103075140c6082070140030040c504407000e4200e0780000d1400d2003090740040d40048002c000c640d035100000c1e1701803040c5401540d61104402001d0200c041c40c0420300700200f21080081340803100d032458a84100c03000040c554408d8818090a5101083c61a4203420006241c000100b4210119100d20000c030004103041c000c6c0c00002034a0300140000440742c07070840709480f0000c0030580207070b01100c60810140703d9580c18010180e001203e4001c450098240d050400164040000ca03401c1640d08040c03a03848001440040c0004035190550501070390642d4401c0c88003044405400e000108032614a4010b699904414003807080b011500903080303200040c3c40c402d0525006020103840c804040010708080e56004a200041c0c00e01040340050f120949030241c007041c0070f00c82c0200c0c004901d10050000035811100360516180c1102c1c0c403860f0a01c0c1c07199680703800340541750060208003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 596938839 1250 596937589 596937617
    0x150903060f0723030a111303060b1807140d2003090106081c030513150506010f1b03030e10020304050c03010e1c0309030c020913060509160b0d0e100606 67
    0x42d00c101c1070750f04640191443d5482c1c0c080d032040a464541621889010204407100c424100b0040540085101e0400452030382010401c0040903082101d41a2001c06001d00b04501150b204616144040443c0a40d54a401d401e030754920003844112603000402d0700b510713020601c0c500341d280a9841214a8002807045d940caa10803581c1b0340d10903e045103c620381c003002007d643c502a0700007a43c010180c07070030031000c18210380307580ca41ca48212a030218030642d11307402d1140e6940e22445001c00089070381803403c4018603c0f407024941d104680d00240806a4810032014200c0092015400fa411140c109646130306241c00c0641d00c0711030b0401d02d10310a40c602a80c00308008030100f517154920140d86c4002c4442260007209070302401d80610102c080004490201005039a001c54082c050070043c0080c1c10b01c0f00761450318900b2a100170340400c0041c1c3c80402c100c01085008110f103010b5032003010180391914600c00c140c1010f0f110810041419000c2c7d004441081c0c041d0754003a8084807515929004058035003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 596940089 1250 596938839 596938877
    0x60906030c010e1014030103030c03091203080a0f020c01090b0603010c0f0503160903140d0305010e0603030901110a0f030c050c2706130213061202030114150903060f07 74
    0x1c280403030b000c5844241c010341245007100341050346146070700f00398600458101214a580d03000b43c0085010a889130900000c2c1a440025900035002c228440c904121103500c02030f2050782d00070440e201042d100d09151511907007a07010740341d420307031014000e0060f46007916024010800c2194028000e40c40c110070354002c81d11a4091004d44445900d400b0b2071500d030a0106407a5282c1d00900300c00b48459540f0000c0003501007c01e0f8001c0342d00307040182c00d0f501280b9600800303441044e400b88241000e00d50501c203282e0390100840349007200c02d082200903400d84041c103a09180c40700b0009000b1422040303004040c9504070000001c0b0501c5142650692601001006490781018002c01080f44001c5542d230400b0129685440e00800b0080001000b40d00746114ac200344da03c000440d5104e40000c5200b04100c94109007041c0989a00007001e40c215030418a41c0f10042818089091140e01c2d036a1590006540900c01c94001c800d002c0d080e544207140c4104072150341c0030166112400100c44004903c441007038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 596941339 1250 596940089 596940103
    0xf060a14061503060d06140a020a0e01020601050109060c0c120f050d18030308040f0501050109020903010b18040b060a030f061407030e0a0209370e07030c06030f06090207050606090603 81
    0x5070b002c0d81181c4840f0305101360545040d004880d07180d030b1040c500881054161080e846a20204c00c05070384c480c40694000d00c00034004483e541554003180051200d81c1e04807041c01c098824501e440c1e0444e0700d441c01d08424452465104070342c0c03184010404014001c51180e81000c080c05501181c01020342004122842c11001c60f01800d030300407004083c00003e11894131141c00a000743c1c05c506250380750392519402c5410a030b1160070125400900d2030303914242070007900c040b0003044481e010840c00b0b622000510721b030001c000611480c60040010795903910350702d03240050760300428080302c1c0388410b02c1d0420003018940c1d9075024813884100020a210300c0b82c0945180d503044140505952403255003801801c00c00034056101c076080019007501d8044408046098461018403030446e1481d0300702c0c600c2d04442c0075105240158100d00010300c0810040f040748000c0390240e2400042c0c41c00d21000c00c1000308072582041201600004a8800707010300024158082c0c8400c031101100c1d519254101039031454 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 596942446 1107 596941339 596941369
    0x1008060102060112030c0b0c07080d0b0114070807020d1104022206020102070302071502071203022104050f040f020408060106051c020423030f060a1406 67
    0x6034100070b024010710390080c014043c101e450700e0051141c000541c001c0e02c030000000102c2c05185101c070460f003489401824243c0c0301d9110140d44000352a01c40585070015803151400030702d100900c000c6524035a401410b00e0701c1c0c040d0030f50900982c1c4418100544120f00800c0c0c28861a443c0c500007081020303030400310000003504015201002408641101045a02c14045980041e40001d03401c030596003414a007484569880400301d19000c40d94114040c1e2940031610f0104058001805403110304203500c1c620f040008400410805000d2442000c0c1d012481c1442040c0504090340200c0c03200120940141c681520b030320050b4981142a40100700054000501c036031820514480c02100b01002075007503180500d020782c2e5075000c0020701e03003c805540140a40712460769041003110b0261021a042c2c0717665182034411440101a500682d0301c05000400018400d4a0115010390f00c4034 = true := by decide +kernel

theorem cover : BRFrame.Cov 596762589 596942446 := by
  have h0 := BRFrame.cov_init 596762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 596762589 ≤ n) (h2 : n < 596942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
