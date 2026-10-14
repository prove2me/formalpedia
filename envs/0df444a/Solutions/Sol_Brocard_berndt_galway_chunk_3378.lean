-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3378
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:29:43.442314+00:00
-- url     : https://prove2.me/submissions/3ecda0fa-a363-4d94-9e2f-ceb97511480b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 607374100 ≤ n < 607553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 607375350 1250 607374100 607374149
    0x2115090105010f261018020703091703130306060f17070501030c1428050702090705180a180507020a050c240c01050910020f070b1305030706020d1401 66
    0x45290a103810381c1d20100340242244c12a4002c0307603c10341988001904010140c034040351081d0182801d00110310744001c0b03480003052140c450080349645010100c46aa40b44010801c8900c442c02801801d0000d075128917040c40501a81d1103010b2002c485441c0204619182c0c1001e2401c084810700246211842c240065000e000c3c0702c0c135000103109215440c0703070228011000500c4142c1084c0d807282030840405000c590150102d03c1220308103c4d0500c0302030300503101c14880a41101c003604110381c507641c162038408081584107103426001504680c0008902e4a005135611228448036428019030384e0703003041285c2d680700d901d03806070056102d1000e007200350402c124100d4055405410103041c2e5a04102165180e070711503107488045030740d81c8041000c0020140000714001c3c2c500312056250400030040242c1034001c0d80e001408480a02c8080f4060071458101005400c0d031002c143c81c0c90780341c0c5051080094011801180340d5504000140046000c100340c0c160503201c03c001c0921261308400f0905 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 607376600 1250 607375350 607375367
    0x80c0103060b18030304080313050a0b0f1b010b03010612060506060c03070f060f1d1204061713020301050f0426030a0506040b0a08031308011503080a052115090105010f 74
    0x2544c0500042001080d5910140010074554149910b01d810383c0d440d020521811000c240e103c011740380024030003688415645c5084859804064841015070b031003501c402030040c182a07410360b0f410341c604a00002d616400a00300c01289010710810030060f42d070130701442140d1040c2117001c0c4242c2c104011680008110309100a00c00d809103000155212465241303008840b000c40810030040400a40c070210349000700001001c0302022004107062a10701880079111040e03038002d401c01850a00000b485140050145d0300d4507c0e0002c0c000c5c0050b003004110140c1ca19800c0da800d603034000d40b04160320340003007010714000c02c1c01180c090f42d545159200015440140030103000581d109072101c044c211141d440a03192006040b40102440d40c0e072506030460524180703903600071011641850b104403484011181d002e02243c5d0810205031b0366810607801100c5d94880c0741c0d60307074516220740900150b03220111000c0522072103054200748910209503080000e141401d00c01c4c1c50005000981c010321980c46061072 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 607377850 1250 607376600 607376647
    0x1812060f09030e060a12090804080d021c0f12050c03270309041e090b07031505090402010c020114040f18090c170c0619021501121709030115080c0103060b 68
    0x1b990500c0d0103103203c4040e144d0000d07050f113160102080038007100c407050103500d400f4191400101142c00a5121081e250808807010109000300f4000c2ea00325540039256000011041800412141c41c2204070080140c1040c0d480c54840b104444980c807400708540f41d02d0f60341c20f0741e010040d400d00980204100c043d00b41803e0740c8203504462054806010345500400040c40d01c24100003103640391400c8001c0031681e07102800300350780d092010204102e448006001e80c0240d020305e4801200075590006803034040d1003400703484400304006000144445045800303c29590203940c900c05080e04418213109981c000c101c0a0580282000108004103844488040502000d020b481040c010301c1c0c002402034004084061602c8101e0308000851a810301a80d01068003a200c84903aa50400d40c0901c0d8895624030014071800c401301d419110b0004c410295855220020001e010f4001c074101c80884041487c800d1040c2c038800d0b8203120325250300038001d400036980854039460074085030407c829402510281d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 607379100 1250 607377850 607377857
    0x10f0e190c030b1030090803010e010302100c150b1314060a05040c02060a0b060904060303050903070e090316060e010203071107092a1812060f09030e060a 68
    0xc03450680d02141c064450062025180014444410030900202d0b226206030340041000a883d1030032200d4075040082501c80c0d442103444a2000d41000c0b80d001400200809000590080000243c03400d0050395281030728829642181010b24171b28060b02d10402180c2e00500000680c40309040441c0994080c0513041c07801090300c00718078070942c40107080fa5900c00304010144803040170003000d810814800b000806040d141040401607880d002503ca5001800e000702858540701c14003101e81e64142601c1e9050002001008503d45c0ea2602030211340c40300400d140240968900002c41d40100188288119036401c00740d403070248800269030500c0900da10072100b096484c402c81e24034281c00d00c040c5100301121780b1188018030014110070701d002d40360350010705031a0825130300114000c0e41d1130a80240c1000506004040d0242860541314114440341a607584040c41c0c1001440b407240410030170015016660411003580300508400545031040b0024003c0340100361a2070302814900d00504030075002c1d14 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 607380350 1250 607379100 607379131
    0x9050306040f200910060915090b0f040b030112050615090106120905070e01030c090603150e10050406050a060e0105090402090718090c1e0c0b1305030c0d020105090303010f0e 77
    0x40c002224400c0176120700d00da05402c850240085604224003c000d000c2c200307a9058410350f200802081c3c0c0c0207a00900f004060b010800008030700c030000c199406407003c2188030392250b84808240030140d409003c25142403240c003020402500340c16900b41040d10b00604410360aa082440c291107051212031515851075030340480030085182800312402415800700b12403019407450400d940811074070b80120084500c0e1007800c1000541d140f1108040403254200840c003415000e01781800c001c04032207140c0d130322803c0104102c02c210385d0f50f00c107900c2520300b900100611a1108403410088009001e51a000540030f00428054940b1240496201080e454124814405014011100c14095001c803000b9a00c0c1c0c000000226001044461a08800c40703215005803980e00c0f0003003071201000000351045451310040750400420f2100c884d41c0356008411259219002d101d420381c0e0b03458050701c1c0d400552030b040106825180100440e4101c4200188007021300f4142021201040300c0070345942445118207 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 607381600 1250 607380350 607380413
    0x507030b060d020a03050105042108130309090c03150b070b1f0f03050706080a05190f0b1e040b0102010509060412092408090c0d29040503030709050306040f 69
    0x99034090065841b50002242a0030240b6014500d00c24418003588082d081c00e500f03040c11940201019481008500040002d4905050a031101c80c19500000e51603410500c4501003541c040d000703414803086003584503440c16911822201c503402420402424080c1c0f10707021942ca00404044a0140c040280c1c0142c001aa0b44c5040007414069134422146031b00002000c001c403d8100c50115403100105e1814803ea01d0074448901c2c0182480103000301341c17036441c912141d6151244d40a8a080d85024184d031180f65500003d1070300c5103d210346450701c501c0c03d102080a0783e51040c010a8002d80c2d80200038005603e499035801e495000d01d1080324100024014002803a040300303180001101e01ea02144005607007800802040c40000030b2a1103d164000489401d00d0349031840d4081d5a150021480e092444c540d00402d0150110043d22112480e030b04002d0209000012000710f01810b150f44591269070394400501da291441100c02602c0380243d406c0450104541c1e060b801e04000f8a00da60341080e9485 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 607382850 1250 607381600 607381609
    0xa05120a18030c110607111020030912010603240b0402070f06051b04052101020f0913060b09090901090b0702070815060604090e0a0609080a08010e040507030b060d02 73
    0x582805600094403150500240000021880ca0005045d107200703282001e070b42c03680414410006040b1380120382d0044144000ca105003103001c2a00c811281c5240720600c0c44060603030b07075002840b0840c8958030303406941111480511480301101d40c4046402450940721103811084905400c12031005502c030482851142c4e40c602c028140e0521441003c155240c3d01d0400300100c9000422450030244a0020021001510b5094400b2610100c50b14500c103015500d080944c1c0c17814005001d5290300200d124000d86002d40098070800c80d09648003503d40b81003594500581c0c0e080e20640320041030400440159003000d0036403a0b4050201000451010b00903030301c011600d401101c8013001038201c1380092161100600c4082e160032500c40352140300d4188000000c036980710b5481340019140e5121403c2200344401c3c410350803000d030043c40401982d0214200608680e00400880d0002901c2d030700081030100385540070070301517500080140502030035903a60305040745c409400a54004c030a01c40c404d0040c0e48 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 607384100 1250 607382850 607382891
    0x30803070203130905060d1101020106030221120f0a03021305030d080f070201020f0f03090a0507030f0c0608070e120c0406230619030b060912150109020a05120a 71
    0x8940c0159540c030000d00e95407103840140d030013a03a003441c103080a016490751a0710051640582240b24a500010300200503401481650300080d0412815101c411141001c2c0741d01230003a1346088d044d60301c22420420081c40c1880350b150703180a003500502091301403034401d6029100c850400f01c070045050392148002841c01c00302e0008040010880c40401185d40206c0c400d40780c0201050000754141005207141840701d00400e00311500301c00c004000034044110070429034000076000303015109501d4481c28070690400300c00b142030321803039110500024224403034168644118030b6079503002c41c00c6584100300540c407850080b1420081c86100e603030404650b07452103048001c000c00c015010340f0b000c20b100703844000402c068295109000a1006941120f54000c0c9119030841914001814104900009055019050415404c40e41c006001e40503035100080b1701c48a034842c010800400c0ea80d500716002a8451082140d00040c005d1100e07041c007400c4148040e070403d00c0d028005c2100101148903d01c07146c2c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 607385350 1250 607384100 607384111
    0x3060a1a09040c050a05040303050c10112203020d08031503030f04050a0506390607260105100e01020307050109080301031e120e010513080f1231030803 67
    0x540e0840c0d0b4641885071242c02c0c0d0080c10200e040080c0e5031000b4009020307030703c070290500800103030445018000340102850106011007c1014038031f40820880b207038011100114194419004088031803080c0304203041281c1d8010302c030b10804100c0340c2d581aa160000f40c090442c1c0040100440601d0f58288007070501c51b503212044c0c03512580361034100700c5200040e0b40020301410082103070414008000d020711080c9503444038000b03120b0b010302600e044580e900191600050080764107104d056903124050b00f0407d060000c0f0f000e80c0c1480d40c058840d031100c082c460258000d1188010428050103815040c0744400c05005607401c0400c0c948580f401d40b400004111040c40000005200f08014048819003164421804084104159491580601e64281d18200b0300c1083c080d8198207a215204942079146a082c02280391603488070f80580d10040e410340301c0d40c1400b4004081240500e000c0a42d109400011074003550300c01c000360111140e05141c1001c400032600c84070080041750b1510015406030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 607386600 1250 607385350 607385399
    0x20120d0b090c0c01060f051f09030c0e182b022805061012240e1005070e1e0105040803041d070f2717030426060c03060a 53
    0x100f0412004a0864800d41c011440c0e040440a00f03001366101d41486082881c6448610540080c0e540c00c19911000749500041260745405404141d5030384110000380036512000303807070011961010701d168442e0000c2814000348290075011000ca1350400001c3c8080d9a202d0056951981c1c03240c2d1000e03642c0c1c9945c8010403403855408041000c1100800c0000d81c0400f04100d00300165003020441c2c100d07105140302c041d01215034451420b4003424210102030340d0310400701c401c11642e01c414080648a50414101e005501e16102c00030780d0581c01401030100d07a02e40101143c900003480907034130f0078000890207201e040203028080480d810004000401c013034200180c0b0743d40c3d40c0140342580844500010490800c010311454502c941c2a000280729800640c0c2e07085407941c43d60006a0143c800b0460303842903440c0185c940079149906c10100003001070721180004100a50140c0c000b6401d44c0304000d0520015500c5000040c0d881450300024542040004110410044c0d0300c075245003000701c2540010a52 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 607387850 1250 607386600 607386607
    0x41401271e0905070906030218151201090614010f09020d06090e030c0606060405060a110a08041403120708030105011b151d010c09050d050102040b031003020120120d0b090c 76
    0x43c4070082192000400300320310140a400e08507070100f0042070641e402c041d0b89001000c00700f07000e82450280ea8140c49409003c0314a2415010b82c1c0c6406044038400548850345442400c2c411a0b40c1d140c0d259050395004014500c4036860304008500035404003940c1c540e1156070701404200c81c2e00301e02031144100507400c000d40c1c4413402c0345892410410041c0c00740d88516001c11080156403100c01c1613550200f21410203060842000001071305040301c0050051841c01d00042c080b41814444040a1130580107030125400d2050446405503903121f4940042c100c05418001081258882d204400d1792044020b00c0c0c0140a13074550360382110030420714010620702e03121a888809204403a04019a10080700020300191000c2c45001d04030201da8003519000c4d0002c484540d00344802501150002c10840c01596580d1611503041550340d1411f0000f2070000e034509500308818041c0c4200d001441c14501d016207a02c030782c031700c007401c1d043d50100440c960745a0700d070808209aa038401c0c00c0c540c0300b0901c011002d980c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 607389100 1250 607387850 607387853
    0x516050a0c050910050d0807021906200a020f0d02150418050903211b03040501051b07030909020a1403092b1b08130b0405041401271e09 60
    0x1218001001c40907480c101c9401001260b8130b4200005800303070400c1440d48c1d80c00040c00854a01c840143e00207088150058000503481e40c400040c9030551900034840001c2c25401d9003040d2109030340352000e03521440405044402d450302c0701e440381c04103100810a11220169201685ca640c00c19400028404100d01d007a00000ca00350241642c4280da00f40078602e0700b507455400c181240d06201411104a040c80b001801840448a603a132506200010391034032271420f031400707502900013160045002c006007045100c050103c00705031032003190305071169894907042c21000380003900185002c0c0b0410400c4001d802d902e401ca44003c50190000e1406805885001d561030208140c41d580341100324461945114030301e40e4404000c0307a8141e640903044440c00d089043c9180344c0c0c000c0b0f03c882c848200c8020320000d00f503414200104100d0360151001c0c041c16000c135020000c811400d00c203c14a2002c80a4004a100c85025082000842d1840006102007030f42611700c1c81ca01e008070101c0b44c420307560440d020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 607390350 1250 607389100 607389109
    0x10030615020a120c031d0328020f060307050409021804140405010507080112140f1c021c1b02031c020a030905030c030705010807020114040b010612050f01060516050a0c05 75
    0x40c15085081c80c85003800315590080403291b600300d0414028580c00d200344210340d024810044403010341c1c1c0b841024000340c0c0710001c07203130480801d04905c140c0fa00c2d01d601009003071403015684108081e8903054145440c2c2144032010358001159050074252540105103e03955901c14003d00c10092444440700d49810700d00282142d002510400511003414010030440c66259215059158003152480c18550701e07100380c0d0700d001d01481c2e414030307a0300510701c0716090041100d861200f040565402c440b07040b804146942032102d40f10680e01c0c005004400c0031003a5a10f100c5000d022a072000d01210920761004018800e020441c4007107400580040d071002c0f040c103a001a030140034081c03c402078041510303260f0010b0754903c028401e442c103000180d000100c0890003948601c0342a4407104115001380f60502e800203110200b400380700c0209292800203804aa042d02c5410320546554000ca0f445909268054465070808842030b503089a10346614000a51b003403008010307040c859450f05841900308404c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 607391600 1250 607390350 607390373
    0x9100c1e151a04090510020d02070512090102030a080606190f0906110a02010818030304030306060809010516180f090903110303090705010c0609020907080609011401050910030615020a 81
    0x750030190905484280d400c90000520074400411500064034080600d07109092000201095003074503c003040316142807060390024a519803081c030607560102024044204d003070041c1007801e40142d1081c8a90b0301654042c80c0c006400400003400e40f400c04000060350203203207007500416000100344100010002ea00000301c000a4403c905140350300c0d50500750f105030781c1c040542001c0d0400140c640402c81d00114001c0c8100e0240c0b0a00035650b0b2480c0509019000c0d2203d0302c00d01000400d9500014001801842401d01030980d415200c5200110000c0c00c030341c094030160400801d8a40d0300700c0051410101a900802410800c40210381d050050402801e0040510840b0540d5041002040380e0000049441c405030340c000d0070046c10000240c00c00030700600c80410001c0d00441c9400501440daa0001540e91003004126080b0045a8842440714840140000402cbc0800c5003400314000c18079295a03001c0100b106480c001403051b03618843d00a0f910340006040000d40c1000b07070b050b4180102440394 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 607392850 1250 607391600 607391633
    0xe010e1e0a050a150603020a030b040209060d02060712020f070305071806030c18110304050a060f020f04050913021021110a1809021b010510060509100c1e 68
    0x1d4451401d2a49565403901c0828100816180d800441c0000921082c0d00900107503401030700c03c038941920b130700d4110703412042914240c0c03140220000140981c0340402076504101d60103000682003080039500c064140e82c10142c50025805a011000d40050341008080b000358000c50041c002c2c0751901191180301a03003030036111140c07414028244045800347e2141030031109021202c9a40110300c1c0c0d00c0500a000449211020410010038401070010004d0025000c0e4010341040020041d075007421012031280300361413290f803141440100194649224072a0f40028030051500b4040d105900007050048105034440104600f004401d0014a0440d40d202910904c01410056000500c507400e959001c1c1c2c800c08000c20210304200442c112810304244010b0160701c0c401c0d502d5400004c0230040030310b02e4415840f080d44c80e180009205104200460f411524991940c510300503c000501c002050b000c1c01100611450f8001d5030002402d44203550303220151205e20441c4011319280692001070007081 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 607394100 1250 607392850 607392853
    0x91a04020109030212030d060314011a09071202090a0806180304050a0b090415180e010203010f03110a080a060203190b01020d12061208190f0504050609040e010e1e 72
    0x10000140d8010802c041035a0301203545020400b0b00c4d1754080d00e10b01c50780d0b00c00400c5a0070300000004000e4050450318060808000903c02c5124412105c0c0d4070400d448501c2d6841010280420200c40c09903072400c07a1102908805450003014201041304407a0540c0049000e62081c1d0802201442200342c80c1c4038480c507072010310b14082c03402002580b04841802039485d4101d000460f04501e0b540c42d400f4450f4100c3c070002c00c01d60381d0383e1101c41e09030303403036030b042d9000203c030705101c00440450700610840b03041c0c2c1d007905000c43c400c0d41181c403001c0180260200070354000002e0000480c410340200003500340c05100d0b100140e40c900c2d1045281c4e080e115143c02003507403203051044100c12680c02186d600003025584c58200c940f0000d032082c10000d40003c1d4042c80c840000c8200810600015200034044413134510721107a40c1440c200000c951501c128030081c0c000490510041c03080d840c12000420001c107000700042810101c4104150031074003003881c110321580c0b0030030700c880044e000744c4041945288040b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 607395350 1250 607394100 607394153
    0x702030c01091d060d0f0c031b06091a09061c1a0d1202190c030c0f05031b01020a0602030109091a060d060203040215030f0a1107030e0111010b040f09 66
    0x31026603100050b58048420000c0c0b030400241d04d911002d07900e10340c00c0d4104501460001c002d003800c400001450106603152109421143c01d4550315504050071660603545e48140e180c50b04003440701000d26280c880200715810002c81d030051762184050030200c0300528845004490080202080b2210200c140081d00c4450420410940d244410300e45507541001c0564007034803d44c1403c90138510320705245054140d075a9480800d02000010b40d10070340e445031342789886407034031480c0c02030004016204607507042e405030342803017050041c94208507034468040c0102c0d00d03948220340c0d4682c1079070000d0300000c03103859035102c5000600c45501d59000440088181e08449420f20303902140b200040070328007800c4a83c00001140031900c0b140e00300c03d201c0e042d04610f99100d0031b14a043d00301c00700094400340c000d83d0900303240610000342d000444506640c140c80e400e8002a1140040d03900310480b00308098195654038a102194455001c1c080d520071805a0005141c0e407980780500c151440703440c0340340c15911282e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 607396600 1250 607395350 607395359
    0x318080d0b0d0501230a050f070c0510020a110d0c02010509060f04030c0306021903050f061e090103110a080a080d0902120d080412020c130f0b03030f0702030c0109 72
    0x40444046048955011070601e0040c408502c5040030200018695840c3c01c0c5a00001ca13480f8440c5007170901a008180708a488904040080c0e480070340300740c1f000340356034130203d00100d001350b0030201424840c0c001d8400204c20901300c0c104a800481218021520541c08110380d00414060705954174900c0c20a030f1241d03111500020031a01030340d5501c81c01127500003035000d01c0100e01d0090714000d60f4402d0f8000800c41d1240b41c0301010750042e03400100c0e600305041c90080018081d005992050001d80100c200742c0d07031143e0402c525280e6210350700706c0c03a944c55607041c111500ea440d0080e010314051020740c425240c2d50024803c60b91402e42c0708000e05d40200c000d134400122031000312a401d030780901012a850700a400011017280000350900301ca403140c08810740d405500076492600c05d5016411075182890021005c1e62244d401ca040154013424071100b412003442d031640500c0041082681c000748640c225000310b441d6501011000c102140003241010851900304070006440c4020300e410a01503180 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 607397850 1250 607396600 607396613
    0xc0807120f210c020703080301030804030b010807080d08060a0915051203040f03020d0515041a0105090105060304021002011803080103140f0a08090f2d040b010e0d080d02040609060318 81
    0x88120311030140d80f58000c1000c2c1500c00c0003650081c0d038100030b200390349507903902e04102c480c3c0c401d10048544140c040b0000800c09408601503086410202c058404c50720b0405081301c5180c001042c0c82d42c000c3c0c080e900401c0080c210b2055a400f03c511031203140000d8180f0003000700e81040182220419801008140f01d034045000c00d140460781e060360341e0881440c070392400d01c0c00c0a20300005500ea440007c401c100038455440e1680d00f03124900e8000010700d90302e071000d0002c024400d0003140e4210f8001c001240060910314510504411941700000380b070a01c0d0950b03228201040c80050300003a40100060080c003907000d11070244031540b2001407007414800c41c4c010703032550480d500c00340c2080760114a06440c0e468510110400f00001031101c000d8100b45071041210901002103140c031540e0b04101008203061500c681c612841c0141c41c1d010038000b44900700203000d04402030807a0310240038405d0b40009549400070344003030a52034860445090805000038101d50f0b03038135a251540c0d424040044003040c1c9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 607399100 1250 607397850 607397897
    0x20304060e1209011704140d0801090605030d0804290901020703030e060f180309090a14060306010e0a1104051017130b0c09010509151309150b0a0c0807120f 69
    0xc5403407620170560b41c0d03170030a06049809612410014002c02c46120b88240d440040f0707a05030343c5891010810941c550741810f0344d030341005841001151900c800310b004a451219880c43c8182d800103181810510460507410901003a900050f19039004070300001015010300645030403000740350041c241480c007548680c00078400030b04100075000c0b011960500e441c40500440340c9090014020003c40d040c544440c000502090b04a48243c45680000c68002c1c5000304400d0b0480307a18001120b040d888014001e4011b2001c951520b4a004d020407002449840d8010950109185610394200716a581e072031030328100340c009080c1c2c2c404103800d0350a4400183d00c022540e40200da64548503494899801c016100361088141055106524050349100c0e050184002c08a03031401d4060100b0042c0c0d11a4404166841c0d81c0410070819810001401514500c4001c2c1046440034a07000840010a03120107903560b10035072098030518012816040c1d501c0e00543e0702d004c440d0051600c00050f0540040443c120413 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 607400350 1250 607399100 607399127
    0x90f1210090c090608030405010f030b030606010516150e0715080c03060109050d1b0915120309120b0a061d16090f061d040e030d150306020304060e120901 68
    0x5554403405030074000c0e80420b0401038150348808100c050340701d541e95941d03500540b040e9800103044140b001285c92090060036401380000d80140b1041d2500710041d03406400194110621388903030700e0f01c40c0200f8005007505c2d011800c040000506000c1c840d48150821701c294000468890318002c03640040c9d64040700641e442000d1209003a120b45811b00102c0c1d022140b0750106a01911200100041c0700c1c064803007428900d108080080200c0d03440081609440202202488501003440d0410044000c82d107080301c5240300c0d1070402d280c96220807004254628050017540d407119160200066800c035840744070003400203010000b101c94002456801000d100405851107070131043c24900820303004440f15009046007219010f003d607103884006281ca000b001c4448048003a640d5103000900340380c80f03280038103105100a0342c507080c2c2504d40c801c051b1044400d02c010412009600101140d003e1014501441c030404d00410716118003816240340c81080c6401e880f4070350702002070340000d0f030704480100e0075207 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 607401600 1250 607400350 607400383
    0x110319060b0d0b07020c10020c01200f010908120c070c05040c0306090203191103040308010b1b0d11100506100e150a0c0b090a05060a05090c0d08090f12 67
    0x120341c00740840c00722012010000c003040e072200300b4040600d40110f440000518107135a60000c14080c05030880ea1420000442804611a4440054441084021151000b200e00c0894402c010200c1501d070071104009070a0b03400034400308003440e0300e6034100200d907004540c0400300c40c01d003601900ea1580d091001d12500c2c1c41660f6641300b03949514001c2d0032640092022400441d00c81c0380002182422040d400300110f806803904001d1941da00c2c240040c0c03030142e501607079103180c640c4c00d080c5003029a501254010320983d100761011240001c040003251a030030a40d43d28451140000080c0f140b0342846107110880c0b2504040802c52552291401902c00380da1928112041105140210769040ba0151000300c1c20311000030081d2025801481034062a40b2903e1042c0c00740c2e542520142c0c82e46407203100200150801d9011a21500c1d0b076401080c0c1080d40072003a10701c06002c54000410305180c40c8412140301501181407621860000a1040404c1f42038407099000e070340f0105055202c0705890b4841c12034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 607402850 1250 607401600 607401611
    0x1050303030c18090a020903010f09082508042c061302090d080c060403140c0d0c1a0a050f06040204290405030f060405010c0c02090f0c0c01061211031906 68
    0x10841c045200c6110f040015140080a003000103140c80170f944040c09460003582443e416840d5518203200c1c00503e039800011140c200b000340443c1550803624804a0104a001c0158000210310080300400042031480c0e1a0596085400f00000145d45c181000415075041c0104100c16078849442c58501c1d40f00035000103a071050010005003000c803c00d400134042c1100802c0c1882000c400007106030042c1c1c040d0701c958003a4074021000340018030a02c1c251013155004030007400c18a500800e481c01c1c0c081d1149e03005600c40f1120340400d400b00181268126a5507485006101410520050742e94115005580562034682064100781c01d00800001c0342200500e14090703010315400300000e8602030180202601c0c80e41c41c010940550f40d003410b803000d039415441c00425002d2540100e000b801071603405081900907a484a800c1c0d655100001c0c203610314080e042241003c400702c28454407000d010001c0b408050501d59061540d1480c100c250141d010f98460004410b4869000781900900f0398070003804a030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 607404100 1250 607402850 607402867
    0x10b01120507080609040c0801060b1c0606170915090606100f0534054c090206032805040809060d1e020406120c09052115040b070801050303030c 64
    0x84c5c94929230140a0b1703946003841c0802c180e54550001c082c60000c2c1070b0440410b0080b40c0401c42218003600c68000403c2580e910803180515050b40340d54007004400940d04010600c014044100e4011100b425842d0480b0080103840c3c43d00160755403c0901524015800f00c1002e00c02415612031042e0b1404281c0a04c10a03141e5140710500e10009c00d481c200503510802914940035580d0828014140c0302804107602242600c00360540107840744100e1002003000714501c045401c03060a10366046039900d511940c00c0005612594001e50041d40f580f40301c3d40b0100c8030441c5640c900c502000c146802c460401c0188404156203109490701a013088030141d82e20041307600004001c01c030a00c01c94541140180c8140c42e410010b90240040b60071507222408820705c40f1001104072442900c0640200d0320014040c0704c9424a0010b120083e2540603c0800d91100f00f10014640000c0c00c20740b45101804108004c01c003c015603007143c000040d0300b0325a0b2594103100000381c60f400000d20000d06158045140207 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 607405350 1250 607404100 607404113
    0x203010605280e0c040909020105071b18020f040e33131b051e070b0619031e0305190f11120912031b010b0112050708060904 55
    0x1002804020110100c4030541d07080401d400d04065408142e02c0502e00b000a480c010038500f00d44035110310b458031441c00d03060100000050038044c1f000e0f170400209220000000c0d01c0c1801d2611031165080040b001180b402005201d101800702c1c44c2d02c510303401881140880c1d42d13840c045c2d509644001000c02090355484c0341c0580c034210310100c0c4042880c9241914055220404815094210f0030b0b03c94652010040340801c0544000b115207034513072225688007402481c4140080c15030390810090201c0900d90001c00c5ca5055007102c00c0550704948031a0910005103041c010205507000310101442041e031039522001d146440d0b0480001c04034265200081c10940300e0006c03144600a003d280d000092620a00288845615039440e0041441041c1e151845000000c502c0c0300c006940110602d080a103030700b0711018045a841e0302c00184400d00280c4000c684980e040ca030030a0310200002501e00500000504030b200c0103106501f02ca24000a0000c03044d07000b001c26912074800d90b81d00256880d0340c40c011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 607406600 1250 607405350 607405361
    0x15010e06040b0603070804120906021b01030f02040f08010f0e0303070c05030909070c02030d080c090105090d06051303030f0203010b07120e03070f060306080d050a0c030306080d1e02060105031009020301 89
    0x2c640c064400820003640c150800c0003540158000c840d481034101864109855100341c0d4010030025a10120102d61700c0501210200c0580c1c40614001c103000281000c04000ea80143c0c000102c1403000301c00600c0310741024810740340220031010040c043c000e01c2141e401d845e0b00c00600020100a004c00c84801803103c01c10440b4211100602040d1640c078000700020558034451104a03c640941440003103440d1007994028007444488254601d0004e2840064520782d1040f100c2da504203810110fa40c01041c0d640c402c1e5445042100442c4041c0e074003514000b011507201d60b00c1241610700c1400103010b454495400d4602c038591002c201b1841005140c0c00b9615420502501541032042c0c40307011928100e208065402c41e011606c050040395241c0c800707551117000c100b1204000680c1070298110951080c007160380e2640c0039040c00928180c8440a031410100800f0405001c070700c05206400261082140507264100a88050180780d410f090010b522188000c9105803c5030302c41e03e000081d9542136012 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 607407850 1250 607406600 607406621
    0x922020915030f091219020708062703070b0604090206071407080d0e100e060f27010e0a060e060d0f240305070b1e1b0d0215010e0604 59
    0x40404403580311000700200ea108480e0054441c40c00c2020031002100000d4940c1405011054a414140c1582e03100c00154402008042148581100010a0701050144a00441c0c0c00040501000d90340300600705925980e0741c2010580d4800c0240d0b2021514007407400d80c01170000c850106031074107580005003881c081d915010309280b1200303654039115600051518200c40c0342c0402c0d035001c43ca128400359401010000c1c030a8008000c5038441282e640b02c4c4852800d2a08020030103818642c40000c201c24940003401100000304c28241ca07481c034103101d002c001a4512091900300c08280c59103000c120814a2880741e40180402c1d06e0b410169559804103071400c0d03920500b02004200d100401400241240c0340120014684004ac8001d403815218803213820b803500072000700310b103d1034445a5961039109482a811040c203203400301003d01003420003015900c18801b40000c0d094440d0300c8203410b11403101000400d43d805500d03444900d07003220140d1411141004001c0d9029500c1102003070203840b0b64000d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 607409100 1250 607407850 607407859
    0x40b072f0a0b1b030f0403140c0d120e1b030f10050105130203091c0504050a0e0402010201060b0301180b03010b060a050d0608190b07031409010903020f010209220209 73
    0x40c026900144440c401d601900c1e00c605280c8400d24008440481c0b00000c0421800400000303d03580d417200c5200780c0240c820702d081c8881c40c0d0354050201658006090500281d001810036266242d40590140b00082d0a01c030b04120b214425500c6958030380d0b203101000042080e00025000956081c040140611403000640c1e5854100b944d1a100418003401f13124400c132800036034105001c0b81c0d03100392849901c5520040050240300003894240c0341801450303c041160401c8081050344800e80c001c8014112030301410f0241c02d1520004e82501e000d500504400c3c5400e1004202e00c01c03250f028041000010f07440001c0c0700002c034020901501181d0b482503040000080c0d100e0f02c00e54031400504407c0d000480c00c100302c41d2580159516618000b2007220034a000144800102d10700407101030300090207040c00146400d502024110230401142c0c1010140d5513101c0394400d06d501030040681c41507010008520341011400010179902502c4058010f050500e0040c43c04c10b0f03010b50481d175205030001d2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 607410350 1250 607409100 607409177
    0x5042a020c040501060504050102060907080307031b021509040509010b01020714060705010203090715050c0607320c0c090412180801020c07051e0121060302060d23040b07 75
    0x74021b406540f0522803075005110f10000281c2d1041b021902005684003040a1860405907481c03c980100110081c0410803210043c01801640c40c2e50803080b8281c541c014454071038040d001004210b500041c0a052240d0400304a08220ba0b404030b091000d80354250f0941c2d030340b103026002240d418003507120000c186610010a003d00a080002c8400031230300d1500356040308528a0354116680d0203a850580a45e522440c00702d00c48901550b20744680321100c08034109a640640d10380011003038112680c04041d41c002440c00780048040c07003200303220744003503801490360308260b0b031040c0d00c1c1021040c0302001c0140c0d003809c00011400d00b0000304014641c11000355140c0b000d0a07012611002584180c41c07185c098800c010079030180710852555401c80503114080c0d046000000c94450000422610700200e80d80c11020005945020207001811454400010070318980e03050010440c10b24a504004400e1810030000041c08a4514070b90104c1c2c1440d1055240c541c07416081c60020b1100301d4101d441d500003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 607411600 1250 607410350 607410359
    0x1803060a05060a0f031a060103022205120d050d02070c05090103050d030f06060509010c06111210090b03060a020a0c0b01030302010207030f03060f03020d020612130501050105042a020c040501 84
    0xa4100300d00642c011107a580f052991390100c041008441d200051004c0c03a407052905e5010741c00f009441c0d100d0010b040140c034004180c401e50b4040c4c3e0400101c80098174110314280302506012100030203000c0c020005020207141641c005d48a4050001d02042007a000141f43c02080140700484000789805455800715585a26255458104000c02440000d19143c1d0b0040000494061801100d4054654a01e000a1030740115102d28442200307952858590300c1c0c08080c8010b01c00148134088100b240361005d400d101d010300750107d40e503a03c405040341c103115801d6940da80105820340c0018203220016981c215900c1d05840b8107905000140000e00080000018940c064005040d107c1c400d94440c600b50300907a2050781212250b005d00101c0581006091006040c90b88031101c2c000d000510a6007865190034005c0701000080310309004254840700b504040000074081c103405444c0488007402032000101d910701d14400400010b400c0324280750040601c039402400500083c5101400600440d0b03141c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 607412850 1250 607411600 607411621
    0xc03030106180608010e0601090e241503010e090a060c2726010b0904110102070b0f070b0408070501090c0501021204150305070504090212040605060f090c180306 71
    0x2407181801161060b00c0d2529070b00e04030040302050398116291400e481c0d0070030596000080d0010007550520a0300b43d408185401000901d502c600407aa80392100c4151084c03000301c2d40c03440900070074003480d82a40210004d034814401d0380d041d9042104e000341c00d607480074080c51420048510280641d81f034507000201807a40001c05490201ea42e00c0a10300c84200da00c0b901172005290304c951003521040302c2100d61341500c801e0444510f0140b5100105004410400180344403106450450350f4031504501101c03156014007204000b4480c46842d03034203111003403c0e541603034480c000b0010142d13600c80f8005020020508182e90105070440e00800c40c1d02000c0c03a01580c8031086010b514054800c50b8080c00b40c0c10342c0502140c06550230350f1494121160420001e40142a0107492003007803000500000c40c5910780c034400b42a5001810002e01d80908040c02c0c0401299001b51085018040801541c000360716444075003500f001c4403038002541c5100701c0b01c009500616502c1c03400d51600850090080841c1d6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 607414100 1250 607412850 607412857
    0x5121c0e03030f1303020d0509040914060702011401142b032007051518150d0f060b1b281509020102100e070b280e030a081804020c03 59
    0x80a15549180e164424060201d91300d488006006a00220441c064503126a010b0050311714080c00116480c001580c40c1d8a220020800011240c5d01c20000c015901e542401011070780b103507a04140d1003c0d4106038103049411090401035018251400c08406608000034000302911400444a03001001600e40240420f50764001e000c61004c00b001d14202010020545204480c00103014021a00c5120030f0325034940c01c0403401101c035201d6541048202e446080d0000500c44a10744025581c8141c070303602c0ba046409100002880a00c0c00809010101803002100e5001c070040d59046c4404600d688540d01d089004002c0c2840d40000e04105003c10101f4995052064452041140c3c0398980185440c125014444041c2c01a804920031080750a181c0e40161f8034520900241c0c1d00091b00c0f40c4019090b6449503c82d042c080700000150300c001da101100b008e00c3c5c44030b6850240804140c0000196480d044c01801900900c0009401030100b00c0c0c50180314048071000e0401d546685809504545030f41 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 607415350 1250 607414100 607414111
    0x90311211c05030106020c0108130b0403020f1504030806130f020406170a050408041a04050d0807060e16231c021003090b04060f0f150609080a05121c0e0303 69
    0x461401e80c80d031159000301d090b2410707903400e94020040088000011a2207c2002e07000c92101e20a18000c1c0004c10003440006110751f0081e002000e002d0443e45010785441e68441070b00404000a42c103000000360b0000c3d2541c0c1168085602c4203805d9900160440240742e040f00c2c0c000a40c0c800940068141c0d00a40100c48681054408a509640d0a030400b400d44204480003014142c04201c2401080e100b170381d41c81c0c000000c40700120705150b01c403408203910f6811803070151007a00010a415003084018000c1100b581200070140250184038280c202d5000085d001d40c2c3e100d01d87c00c40c44011b04a1040003a61001c240042c8000d0b86400345103c43e41d003c40010901f0f80c0245100c2c1c10451a080c00f81c007038000c100d68048011f4410b59103d840e010010a90b1345001286c072601c8011807203244802d070003260880d68804210300300103071400d10042c00380003050f8090f4400b5081486250302080d4007281403800d010000c0070096480d50382000560b0820004582140840e142051800c00c01e4070000180d0b00c1074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 607416600 1250 607415350 607415383
    0xb0a0b1305191d0601030303090f0b190605040c0806040c0e1305090105010605070507030b0c37030b031902010e0901090626030a1419030212070309020109031121 71
    0x714041c030b41811a5180301080f402e1213034000001080028031a030b1020100d0760243c00702008090a6603244401c50310b040d900c003c400400c1a400d0141803196215003402820116020408401454006000c802000f051f146c8074564276003025030281d000d0070006011503801002216810040e001d44002004191515403041d8039250011800501903011200c2140e0000c0050499034070b103a0f42c0030380301c21004019240007070090042400090810548090b19012103a21017500d0030030074035491540717000c0d07900e95040600b010b40206a5403804295400f0210819207600d500b002a400141c43d44014520031030b070044114000001c03805100c0c0e00050940318071000140c054255a035007060904d03204501e45000303400c00c0090050480c019407440c20412500e926190801201414a1220600880744140400d4000800d00d44a076220340e0aa6400074117030508200c00411078000803c03100f12800000c116050004001c221070352040d00c01c80f4607424600b40d84652485a03100f03603464400e002d689542c071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 607417850 1250 607416600 607416611
    0x30305180304080f060a0b010c060905070e040302100b1e13110a02030408120307050a1b06020a1d04200d020f0a0c021c0809060d09020a1d090a0b0a0b130519 69
    0x140c000e07e0080281918050355400301801d42501c54000070041e52400f02c806101e181d0001900030312800d81d09100710b0107500a0710351105003401d0b032802c0c0c03001884024440d182c550140002500c048007203114180080c0c6040782c80c0200c03860090003c050100340d00282900c00f14182049690020041055899100c107850040040c0c03c5c14074114002075851102255052003040d4060f403240d43c6840035009004622054100e190302c442c022644081c1403640015048450040c00310215000404882001e41d010004c6115224541071246550f16104103484070020b402500c81c1035640559100d0301d2100202c0b41d0764103041002400c1c0302c1d44030b00300320300859084a8524400c810368850000e66500304808915090704d0781d04000e0390b03501c00342003041c1c51641c49001c2d10242e111070348608060003403100d05d09801c222410101510a100803d807010a9001c040c00c1800252030000341d80d00102c1030f20300802d034009500c000030005034081c0740788044149800c04200c40780c103003080160712584000104020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 607419100 1250 607417850 607417861
    0x16050d020606030c040c17010f060906020715050f070b011202040605190303081f0807061e0c0b131e02040b03150c0702031c0206151c030305180304080f06 68
    0x2114501142c0b40ca03031541015120740941d00b0260400c009044140c9004c43d0300001c2c04c1040c88852031b00b0380007000211166070b0140070342c07500102000301405d0070380028005149050002c0b042080fd4040b010100240460315903a1031105509a50304a0f90042d541e00342507071607000d0400d014240c008207a00c900e003000e4000941d07080600c1c450380141c04050400d08034a046403010340701300f10003500b10349003a4100e501049a114018180c000601100b401512245242c041d00034040f040e05008030481915900c00d95820540114504560503406820b4040d81d54074150040742c501040100609007280c20220212903a500a540c2c00006108075010010318140100341070b0390301800710111076070840703802c041407481c05604050201107100a081758007000030b1610740c00c00c2040c015402800340c0c1c81103050150305424494240d90003241560440f039401d9003484117000c01c00d4904005414103035110040350b1081032803444080c00c00922411030746c1c4d980d80c80c070801d640e460460071035101c01d0151001081 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 607420350 1250 607419100 607419103
    0x250e090d02010506040c0503270a0b01050f030c0607030f0e041b120501080304060c141903080603160506030603070e0c120f100303050c0f0601030b07120b10031505030316050d02 78
    0x25111b0090b96034003819540c88180550b20f40c681e84c040e40808030a040d280106040041081d0700120303100794000555549482d040c82440400414150320980000d80080300300d44411042c0ca1100c1e405152190b03a62114801c180c4003203614142c05a0000c2c01c250114070781103103800c903001c0300c540642d40302c040d030804084091049900a008410050b00304020400c0310512a0102c07010f040d01138200c0c2c50302e0040113582d240c6007105618075a5140b03240b03440080103050300881c2d00796001e072058018221187c205140c0040e400e4160152074450300380840070035030f203450400501010f071011a00d4001642000c0c0c00b000306130f802000309019107903580340004d181d48a0350380c0303401d02450407500da01c0a00ba00b180d4007500e06030011880c2d05180d2048002488284d0020480c1600035400b44428030380a040c510030007007480314140c48040b045428041c0715180b946a811780402c0c26142e614002a080e03031501c0e4114000f41c0998840c603411301c00850750805615000c9425003407684201308480e0308400c44541039 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 607421600 1250 607420350 607420361
    0x6060102070305120f0f1303150c0504051c0b0a0b03010b04090c0b071403070308060405090f0604020f0d1401020d0c0207030b010902031003081612030e250e090d0201050604 76
    0x10078541184048861030301e8a0b002034600d60443c84071702418030002d01a0f0f1011500704080c804d00565440382d00708107002903080e00c032402400641c404d000100300300802518038070403880f5035401079008900d688400d0350381400300428268416a175514034107000b0741c440c01802900c1c1140e84a54603254110031986414402e40d907030f1030b50125191944900d4031fa0540030a40050b4402e40d1801c15170038840031401820300060418501c241c40d1080b090400781c0920080b140020800541c1c1d0348000b42400300c1c6040090303000d038459411140d00245c80d040602103203510041c003c0080c05601c6664100c2c011100c1074018007118101c010081000c104d00c820120f980d040d041c4800ba00d9506d00b500140032107405600195442401d20102c403c10603680e030388000641e440300b0084600004c1d0400d5981c2084002c00402c2a8204103203000d001c80c00d107403103c15403249c810941a00c0b1224007213240701d01281041411074005c20000b610803e85240c42c0380ca482c0c0b02e20144170740c140103510340390000350685440c1c4101c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 607422850 1250 607421600 607421603
    0xc0f100c080c071805091009050a02040e010219110d0903170c121602040f06140d060e07080703060509031804151e0503150915040c18020309060601020703 68
    0x31060441140e469158181d806411003040d9400740c15030105030b816404076400c841c02d0210704001640d1030008a851704120200c4086403086081041e002d0108900003011050150112800a00302c820300080750300a10032200004001a41d070221607490070b801401049a0051a000303a42c403001c08030004940c3c5080340d010007040c074051604425201c42030301e0041c083c0041c0f1780049a41462241c400310803542c120b010301aa04d400c1d100c1007941182094081d05520b50025403003413006505241019102080c01070100d4002c03090600355000744074450b000303034010b81500300c19101d11076191010507072610b8030f47c0800d40e0824146004150102800402c80341c845202e0b40b15802c04010100c2013202410781d0502c012140280721401048003511a02203c4807540c03460141550149088141800c10700d903410010045006501048590740010a945510300300040203621540e45500e400c0d4011101c13a00000c414100c14505401d4241b42d82c0d004500a00c400412038205070743d20801281d40340b415020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 607424100 1250 607422850 607422857
    0x280b04031a040b0f1b1225020d0c06020f031614180f1f051e090d020f0607080304052a0a0b13230f010503101503020c0607020c0f10 58
    0x1480b0010180c2c2c4054009003040210b403100700603401d0001c106c0e04942803070810015800140301000b01c0f600c0c219a43e0030f45107407440c84246011400a17443d0321500c06c48501b4040750350303804400c206107a030407943d81901c21a40c043c4c69090110f81103803c44408150900421040030b070442081e0f46a800351042241c6000c01c440c2e2480c0c02c10f0a000710745c009084515000446074ac0340c05400040500d0600c00440c0c1695030341d841e040c0c02002c503551030039060380e00c0451080420000e0010f80310b0500003010b964040c1c9014405c08601004640a845501c6000c1c29032a008014002003017004200060751001140700b09240c0e48040748003190444440d05034680c4210b0031002000310312000d4010348080c22030a050303441c0041d80c1d0700c0e03200101d604600340d507140d081417808202401e03d000d402e203904002003880d00904603e8509070f28000c0a42074024480c0c40364008850b8074410703100f601115412811241566800d0a1280300a951211030540148c46005221410000c50a110704c200c03000701059035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 607425350 1250 607424100 607424123
    0x504030f0519030f112706040617071b030503040c050a0b031311030a15061d010b070c05040f050906070203091503091501060f0801050402070f02280b04031a04 70
    0x36410f0b030090034601c01183c3d0781512590071644002001014049890904120b806081034030500a4012012640c2c400d2050000344414800d031640049400030320b4807910014409a103400000743c81240070038104400091803801898101640301003d94085c0b8842c281510425440d2000c21202c41414054024940418000651142c07900c0c1c000c00b00641c0030f14012004042d0707200100e814041100e00035200f4513401803000c540d150041c4200360081000e19003a00c0e40c1520310000110000042c840c000c00c0f440f02151210520031000e00c00c100400c8001c00410104140b9101c9401400b400c5840428900401c000192010300100884003c2200208003a000c40180101c4d100d494101604071110b40c03045072900004501841c50315070103005103403a8103904c07414100b0300910050050304030070300440c014080708000030044003143d450175504550a5900000750b005100d00c60040c0c200030002c3e61440c030b4002410300010703001401500e00801000803940703204c49445c1030025040c1c0303000340140751700b9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 607426600 1250 607425350 607425397
    0x40303050a0908030a0c021b010e090a0f0216050f01051b0f04050d03020105060907020d0f0809030c070311032509020705030c1212011517091006090504030f05 70
    0x80d442107910010510001031103403180d45a108640d0421125000b40541c0d580880741400d070100001c1a1507155180689503c0e003141c40000e04038140c21100c280100035504c003003817070000260490100c000507403c045450b0248a254000c030010560401d450078042c80d601602d002c0018011a4420325507038079448075190a01059100946c40000d0200e0449000e10000c511031340e5042c9000c01c064029400840c06041c501c0401c00b0a09010703000c2401e550044102c2034a00760495031050300396a05003086502c5a84111240d82580324038600001c190060350404410401901d0346840002000d80440304086100446402440c104028220081c01002c40806c21000c0079001051094840d0040c0d03828003590001a514000410110140e4080040340d111b010b002080700d103d005281d440c2e80c040c4840e0f01c0079005845480c0070604840c5030014240000da04070010407605100c07042407002001095030701c0d0419001400c007620b044000400c910201d043d007a00c6101a902c2c030000c0c0e0907400355001c040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 607427850 1250 607426600 607426607
    0xa0e0111010504050714040e0f0c010e030f100c0302160302100f020a20031608041d071b0c080d050d1802010f030b010309060e1e01050907050d050f0304060915170403 73
    0x2c206c4101d030b1003904e9042420b20910140203080707400c0d440300300404503180b0010002d41403c2d0007500d000d010368413200e11241aa600014604031a6811001c00248101d00070b42c01c902902c580b80340c4914040c0d0340083c0c1020140d0000340d00c0e01590714201e04105145d089000d50050b40301e171003400400500c08682e8000c0c038104805114000740104003c503440d00c11220f51040038029900d0b0f0a48099070041010023044c0f480c403000c00103042a050f07125103240340c4200040d00c25507203c10b10030b203070500a08003030040102c180c25803405007962a0440b414020b05a00082540d4824501c110f482d030b040040071110420741d01ca440080d00c1c0d0503110800c0000c00321100700c0c010300c00c100340d5504240d2030f80703070800c08900345115000c84090600d0140140c4070000b46a040507401100d01d02599030b2504081040c0c034100401c00400741c4608460004210640d4181035141c031186030101c00c01d90000290010300e107034111f04403c04803003015041c0c0c080a0544103041e02c081c110b207200a132540c1441400100040d20 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 607429100 1250 607427850 607427879
    0x1b0f12020c0a1b1d1506030103030801031e02040e16080c010903081c060b090f100915020c1503041703190e01181412032412030a0e01110105040507 65
    0x1e000c02c0245071a541d642c40d02000c0c00c15090402e50029810248400c175643d22a0041054070300790f5940c0c1c03440d455079a005144500522001d00708414514000c03200c040c01c07404074503089400400520800071804109900e600c024624a03444441010b000180190041191a00118140c40345503c1e1480c50b2110441c5900401713003c040223404002c14203140d50a4484c2d10090400085a0f0740c640c0c0801003400034005020550b2841104e60016244910798000b600b4000e8622a4107078203c844480b4201342d240c078048518081d0300030703c03c100381c07864a00358101170b41c481c2d405100c544810084d655a01d100601c0290b40107a030203104841131954018a40d00142c11000d940d034000200d0082e1b1400c0c180c010030310030504882000c403030025959803440030009549124104000c0a00d9424071703002c140c1c400c10403018014480851607200c0340080d07558604428480f6805002d50340d50710115540184211000c81290b80460300e0358201103c00141481454400d03030784800100312090525884805028 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 607430350 1250 607429100 607429133
    0x30a02090310060b070c3f150e06060d05032205130e120a1706031203040b0901060b0313031d0d060b1203120106050a031b0f12020c0a 59
    0x1c079020034181d10b406a031103004000d0125030102a12005c0c0d500d0800c500c05810f9000030514000204242260076174034000303000e042000301c001070184164103040103144070001009003010614000f051812201500b0200c40c00c1c1c41a025524243d58081c104014440741e00b1014000364418800748444001074202d00402440d520b003803034442d554640c006549501c000b0914103100c1e48500008a00d000100f000c400905980b40c5040d00305094100003c010303202d8420400032808003840481c40d56141448030714511188001d6959a910381400c16485004c425580041950700c3c1c0000025411000f034252401000c4d14101030380454a02d803003c03070b0307106007402490080d014170b0b151000c0746944403070708828240d1240740003145d10140c082c100481414141840c8180d03420400a00785a01d50303035138944e41980c10390f04103140c450564140440042c00940e6862003e0762101290307201440d040031000b0005100d503906d40c00210041c5298400b82c2c0110803081003c1c1c1d0108441e40c0000d0800c00a042120 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 607431600 1250 607430350 607430353
    0x3080c071a04080703080603280c0909030c0309120803010b0c0f03130e0114030d080a020c160311180a02160203070e010303110105010312080403020f011a18060303030a020903 77
    0x40350790440d44503501c142a40c08803104500010b9003010590403090b01da61110b0100c0141c1100c05003a40f00302171048110a0604681c5015046442002845118000901000740d820010f4404c0c5140203403020f901000c06802141b90810001900780c1c843c81072440d142c8d4805000c81c10f59181c110000a01d80050810080c14000d000c080740300701c8001c0000d441c8800020790203807140751401c2c103204030b082010780101210803101501940d480e10002000d40000d40c44e4949849560748010b00100240184030401005001c0c101c4030613a5112404012000d9a0140d0b01d88002004440208100c0c00000560000b402c80d800e0000b0b080b101099019000d0800190841307074042c001580002e00385030068201c0503148418200510038147c4c4814202d2011105400800c481d5045880b28042010602181da04110346000010200761090001d020840c0c86d12000303010400c4030710884100c10003032115a46c0251225007922802c10310020296002d000060065480c64a0341c15200c0065403080100c40d805 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 607432850 1250 607431600 607431623
    0x4050f060a0309020d0c0f172d0a2003010e07030311070e010305010621150c0908011a0f010c08091908060907030510093201020f0417030703080c07 65
    0x750701c40000c02092144100d051003007087c104880300c482d1200f542c0090608801c0020040340c464400502c03403142c2906689201c0c01d551344c00d600481040166150030726103010390000720040088480004149090030701402130000482c000385422611400c0e0040200da05c1001c00b000441d000702a00c54810100f403055070314060301c2ea030072024040700c01c2c0d004448580d035038003082060a920088003c091440151a10340711001900d40444000440c5203054400d66520b07094460980910514001001084024044005000301c0f43d180c9146807880c1500480d00304900f0b80c0f080d072080920300c0d01150300c0490306060098810512104400544006ca0540c40152022900c00403c004040c880e080c0b00c00280f020a00311316003181021a24402e05048a06014490000500d6894140011810380318a906e41a4280c2e5080c000100340841e450074951001a42209802c903801c0248140c03810f0b000f012083c040205481d075030324480c2040250020300c2c0d21000c20b05a4036808000c009890080c100f0f02c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 607434100 1250 607432850 607432853
    0x12031a10021207030207140114070809010c02130b030105070f090e0603030f070506070e0f0a060809011104090b01020705030708120a2109031e0e100c0b010b040f0b04050f060a0309 79
    0xb00c0781e110203010340159100e000100300300041e07083c1e0304090120a20703041d5500d024001202c0003d0003500c2004050711000304404200e0b9100f400040380880d0010300408100e8210180040188968410f02e8025402d00e40090070090040400051991282d61010040c51804200c0c10038210b0140101d985030000b000046411540400640805030250016050300d08142c0c0014100d81200c1d402c0078060060a5070000369960796401e00c40c2140c6080c02c029500740d0780c2907040e40c01400341455160b074548012074040381d10305071030340560b036540e000780c00311214103031518101650340800e4410300b480c607800010315480c3c0180f9040600303102e07549828001602c1c1000500b915000100030401210a0390311050f18090580c40051942680d10000c0401c0703200c1000d880040c40c1070f0300191321601a440034030200000c2880b40c040282c2058104045103815615401c03205940e41c45441036074a407403502c0c140800c41907081001c4400b1101c000b0042520f5464003000c0c0a4160854045034081c15941c0d41401e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 607435350 1250 607434100 607434133
    0xa0b1819090807060c0924120902040501080f0f0109110d030c05010c030c030605010c0506060402160c080303090d0801120b0c040b030f040615060e0f030102042112031a1002 76
    0x30f1813107414003107140c2c0044400100403401d1036100009110f0850f80e00c00c1d228281e0032103040d0410307542c904a8400c1800c90817001c0501030f4501e0013900a46000000a5278810118501000c4030214050300e0850301c1451880f42620012100035003c5814001c85146520304038010700d000303a11030300b00041015450b0b203e0908640c0c05c0d0b0400320110391510f0f000c0d0340350b0307a040c4030311005001c0c00d0901400d6514a42c0300c50780c1c0c0b1100181601c0c05103500041500000032400102c1c42c0490303120b140386200c43d880d808940d40301c0d00150341c0c1c1e11051042c0003580d60020300402509041e2055607140184064190300c0d017884180014041d01d103550bc0420000c100d01900f040114840c42c4500419401030509241c44022511041c491994488019500780000b507408600c42903903080481e81c00080404e4080028024071650b84804181c08448101180751001580100c018034016030201d005001090000c0d000c0d5002c2c03211032586c040039070900e6040c030300e029802e24003c2c4225204030b5500d5411f00c0c9100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 607436600 1250 607435350 607435357
    0x20304050a050a062304080a03150909030225150c030e0907030504031103030702030a030b0f040516110c060301030b190e0309031e060105061b060f0a0b18190908 71
    0x2038030140d480780c400f180501308080b81c2445e0310181c43c158120070f00c0c2c203407201441030240701031003410181c83c0d081194000b4072800050016103080c030800c00c400380c110701e0041d545c2d0913004000f02c44404a5806410054280171801080b1004000d9500e4488540d503021180c04107030b03203812014800c05424090aa4494544040c032462880e00c0008042c01d243c20084c2c44918140a4000d007a84100b0402c400780d940441566101900c1d4200811100140b82c00200c1c3c0407900824560030070f140c03408020506442c22603403180b282e6079855240c8001004c10245442c4c080014202d500f00d801000104000340d100100d0b580d01140e080e010001000c00e610300d040582c0e0310140004066400811249a10319050155888528059a5111495080e042610380310501446590311805012403041140d441c03901d0702c20496440402030300c01c81e203804801381c0c03845003082e1820012070340340c0500e02d1f02c14140b140c52001e2080340d03a8882d11a03130395140f400000d054215003542c0d144070744642c0d500d400a101503019 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 607437850 1250 607436600 607436603
    0x91215010e180105090c0d0c051203120907030c0605030403120603060f0b03060105180709150c030e010807020604060b120a080d0c090308090d0c08031801020628020304050a050a 78
    0x184111410003000c811142d00d416840320b140c9900d4403042c400840000204019080310554107100941104e040c00400184258807060308007010003032001c40e1a50100062804196850880001f510f0742c1109581e601014000100380c218510701c10702125000d9009140d00a01c28a000311000f454107088200791340c5182d000300c40c0a901e81803000500c00312405280d4807402c0507001000c06602d40070005582c80c1a1040d0407101d8070945c4007164019219009001c0075001c1c1582110380e480044500030090f42c161003081d000200d8078180e002d840d41c407611206001e20110781c020015a240e64840c40010011b004007654450500742e01021000c0d002e02ca2950350ba401413550a45603e84044440c0603203140560841c10021028403e00c0090505000e176000d5802c15030301600000c8403803030b00546141c125080340100d07100106014000502000400d014000282e09076103540e00c4000c0d040c6400628601106248005031607c4010140e095000e141e1290107030f01220040c40040e10b599003059000c200 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 607439100 1250 607437850 607437869
    0x50904021c0b10030e060a0c030e1501060f0518130b0a0303030207060501050d0203060c0f0717030403031a0f01231308010b0d0b0402120106080f07030c0807050609121501 75
    0x41d020300030f2506040c81031218810382000d004281c4640905520b030310700100302d100720300da40c1e1025103001807080c0d02880080f0900c108840030460004040ca029071800d00c60500082c207003184421b40305200d58240c4200b420405003010b042c015040c01c00441d4420915a1440155904d01000040e51110580d00c0290301030f1300c005a45148a040200a840c416000f4030f0003a2600000140141c0b0f0020b80300303901c81039209100e0740b55110307414020490702c1212805400085d40d42e1078010a4030600c002503004500c03c1e02e04000914201224004030b0600c6c40321142c1c0818521010980c41d40200040684491441341820300c201581c815150650402e111300882a00c600d42c0600c02c1040034418105900340c2120703600204001951450380184005000a024800d02d84200c80c0000d02500580c0280001d8002c1c3c40401c03022040c9541d42d130034a440155008909918001a036000210b40c460640c1e1020f494149002c5801c001e0155680c0d00030900e00b0035102d24154039110610501c03da5001e003d80c2207 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 607440350 1250 607439100 607439111
    0x603153234020f03040f0b1b010606030501050f0d1709010306090f051608040b0402062203061b0c050d050c070e0a020d0501080d0816020102040308070f12080403050307050904021c 79
    0x40c4000d1030040a103200483d1944100000d010420444803004202d8008010b002c2c0d8800c488084030080c1c094044425201e50b00303010f80440c1b041d405800072030590720306985445500c0701c0a001c10105030030901c03000c4c01c954032044422192000180090405280c10b05021546503618040b02d021501224441580c2c1aa56001d120601c0c2c100c59000c0140303020703890304108a0a103900d0b0b102e1003490240000744a000000360b00c0b454255241080c0d021141c41c030f09104982a0f8a08103071026003558039140c00d21420004521800500407009440c0350343c0c100b030080241c8154454103480c99445580e850504c0d101d50b01000441e021101c2c1094820707203416101503110b400001d404010b80e00181c10200086d000b84503803100a903440300ca181e6200962002040710f180340740206174020701c0b42e03400c0540840d6000452005204000a840c2e101500c0307900c1e12a00d40c088000c1c100e814074002e880050020f42e0400100ba40584614050190728900074001882c00070b44a1001c407000182854400529442d907 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 607441600 1250 607440350 607440451
    0x306010f0e13030f0c0609150606090911041502011407020c1509030d0f12092001030e0a060b011412070e030c10031e06031532 56
    0x1045a410180c07480110340309500300c1c0e0f000790645010984110801c000010b054080c410b176a04480300050304054a403440e02070003a144405000b40d801000b011884a00d00010011828803d00504501000c017203420300d81000d01c44041014400951400c642d00c5580c80c0110351035000c03205020b41e9081e001480011000c40a000c00081d505280329070f0f00900f031108200d180c03400328100c10704480c6490001c00f1440b206200341c90b030b540000b04c2c454807203182c0300130081001038050000c0c07076007058140f00c0d100d0704039130300011010344011400322078840c0c001140d240c0009505401481c5580d40c141454843c0310010a10141d1b0b681181000c0d1018005807405e0103506500042c0c05c1c401482d090b000b8110b042c0001011031020058204a8010503540e0407022035030341c1701c0f0054041404a032741001d0181665070f080041c10500260064945540b03418020142c019201500f0381c00d412815a84602d000280d01c0040e04101000b0032500c40888100c941c0704200808400702c1001e500d6182e0300c2c11a05804 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 607442850 1250 607441600 607441619
    0xc3004120311010504030c0201050318030c013e181f1b030e0d060f060306020705070902040f360e010c0e0315090307080a120b010512040803060d020306010f 69
    0x8411003007200f640b5160500000c00c0d401090002c180d0780a080c40c59a980303c11822400f1a45401c02c07044050001103040c06405806401208a000d225181c51101d400e00010f0320000c100807a00340001c218248204014001c85000039004d07540304581070700005951311011404521203040f12000c0b107a0107030b500b6024684c02800c10381c0214a829200294204140d90240c107004501400c0c51003843c05088100c10000d0640100d40310081c004824000ba44d900d03d0075a01a400108085605004490011459a5180c400c2e1000c0b55016491443c60341e203081070158001d41903980030003d81c0c80604031080400303880d48484120940710440001d114002103245421200380a80f42d200304080146000b18642c1c00164254000540d180101e5994448100592461003035000c000c100c40c5000c107100e03103030a8000704c0c060420f03489020140034071040100115414401c0c3d0300c00149119031100490045001e0002075644104064011030148403540c00003840c12209900071040700c8450b40040c4200c0d102c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 607444100 1250 607442850 607442867
    0x70801080105070f0332090d08150103091a1302090615091309020d05010207030201060b0304120c1b090501050f060f1b070e0411040e030c30041203 65
    0x1800c00c020881c80c2030044005000070100c048003410152a850000740c001011842401e611401c8525035000e642d80d020360040c054011581460f80380650f0403460025400350044034450401843d10206003010580190020a5189002c0d6508180400301105100e200143e00380181d850341d103000b1040d0200e20400820038002440f850081b4812a140b0f5555000702c02a6404a4401c8461841410440010790002e100b01c0030041c0d402484c0d42c1102007405819402040307210300a600a00c5002d444810b054103501c82580c004080d001c003000e000105500c185a21a00c161185d2150b00803030102c3c0812070844c00b4035400400d0300907607070001080a807501c041e40c03405040050350710b035061810040321510207010390141d000c107603221000000e5010909000280c00303051b41c140c01c5e110030b0820b4101030300b4103a00350303040703900441c07501c415981c4458000007660003132502400100701420b016030003c941c800d20b84000800c81085030303480300c1014550201400182518406c00410594070b410014641c00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 607445350 1250 607444100 607444109
    0xb090a0c05010e0d0f020f091303090f1809031103030c040e1b03130503040305011112091501140a030213090c0609050d08030408090a03050c01091d010909020324070801 74
    0x2000e00f14100280c0c5424007010100da810186050f480b9109001003400042195205030384580303180308010480048101802004d80243c0c0d4140c616034031405100007820560042105031010001340301ca50301c0b0300d034006020407407113460003900c00c04156890350701e5034000340c94194109002060a107e02041814081e80c80207003a5074a00b03000c00c44940c040310350b204c003400c07010100e03041130703200d10500c00100115401954404020401300e21044514a81d41c3c20103400749440008a1000c226040c500090029407114a02c5a941b45646043c4020104160304076103103410241405001025070b8844030406a480e00d0b03050049203030f202500c1c0941c000e0304940c0060080c06103c09040c00a40c84000100980546c8101181d54940707403428200e80078007803100c583c0e60281c2070501c04010030034041807a49004100b0f03210301452030740b00c201000f903098451100f200030380a104010070aa04040d0403010303032071b4000307000d45e903246000a00005044404074614556002c004080c441c645500200060050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 607446600 1250 607445350 607445357
    0xc0a030e070e010918050303070c1202011b1116080a060510060207030b1e100504061505070209281b050702180c0903030409061a030708010b030907030b090a0c0501 72
    0x381010b0070b0070b40820741802100300c2e41d0f07a00c1521196403442c1c4000041521b810504407610392a2001b401454801c801c001190381c0701c103030740034080399138014001c030441080a824601c0300040302a17411142522001c018040301c0c840c1d03035842c80310f203901e40b81000041c00c500c60203011280315908003001520300c00b4052065031001540c0c00c1001a50202e20307401581c0d40a100d041090711035440700011040c40104005020300f0310414007060500e20014a0202e6000350f400f03214250b80e0319001c0700b960182c00850004284100000360044ca44191180c4d481a0025070314032642e02c071003000c0e10401ba46411050340b0a503170b8030400491182d2030820055a8046031030130320302c2c0949a90118040080740101840511101000f21711481050002e5810b07450021b0200d9444550b10400c41001d00954070800390b0411040c3e4052011864200403a031042140c1d8564a83c1a440c20000601c1980010001c401c02e0060350307000303c0064000f41c1d000d0302554040d002001c0300c082504004500220719400213050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 607447850 1250 607446600 607446613
    0x9060c0a0c060f020d08040c0e0109150f140904020612040807030206060a15030c0309080f04051516020d050307060204090902033a110106030317090a021c05150c0a030e 74
    0x9482e40000e02219200c2c05d0300d8101201c0e16245008000750110390020000036040000100e03140099900881d5200001e040550101d42e0f10f40300c00d446807240f8007031100002582d00300c0181504240111980051019288030f2406030300030148100c2d14030aa41c11510070800003030075001d05604205043d0003580440303400700d545141100d02d81e9155940c44a08040c5512550350303010282c040e0b4400c0c1c41164001d022640c0d075000d0b10111400f158040d00603140b14619000c88190102200401d44540c20006c61801c0c03205240364081182400c000042184c41d88020040a0f00040850010b000107101107000032a41b801c880c41010304220102841c13003880c03000241b001d00381100d10090340d00c8803140702d280c01004040d60301c41204c071681143d81e08600e0b903003001800003c1540c001407001c02156085802c1210751210658280c0b0b50121001c040e61090101f45203980e000c00304130307d4880740ca01ca0400c031000608185106545240e040301c40c990351400201e9050070303407030b054041d00d00600c000b40301070042c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 607449100 1250 607447850 607447877
    0x9031b1b061d011b053306061605030d1109090705030f0403030e2410060f02061f15020c0102010b040e190c2d090225060209060c0a0c06 60
    0x74042c0d82c0041e0703e04001410310201c00180d031241c1d031002c1c0036811009645001c00062070b40c41c010340140a508004409892009515805d030130040d9008103c02004c143c43c00141c05440d00070b004c100700d02a15180001c01421140d03c2c21441680700400752864050b03101c000039410011030100c014070340e009200302001086502c4619820040d405545410f0000701034070700b0b044840c540b11811031022541004d10f21800001d440149045103d402112181c1c80b006480340000c455004003400d0840c05039000d40c01150a09144480c500302002100c001c40b01043c4c1e54944000d03070035042003494000358000c00c1c1d0342c2007117590a01502001400c180d40070300407001c8140c0c5642e034880d88a82000710924500e00e4072000c1180400c50b0800a0168140704d8140411442e100d01030140b4205400340c00300d4151b100003401e0400c500a4800c0c001c40c05055400200c850340b00e400c0c90031022881101c525508100d20445030790b075600036045055a96000b020100301c0c07883c0c4201c448410b03403c02014003050f000c0342c45 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 607450350 1250 607449100 607449137
    0x40b100c0f0c05060a020109140d0815130609020c0706211d060103030206150109060e040b01020c10031d15060d050a0204050c03092401050409031b1b06 67
    0x100c4040e03100204449090903828418656841d541085034082030001e083c000155054022050305801034108450501800d40c1342c1d0b030340b0540b04003400045000000000d16800071301e1440c141801d001f41c07100c009018214266022500650044194030360b01140045045008201540140072507027031450b50f018145511070002000d021008a41644030b2084042d1203c03400700e0203448901d403404442c074030f58580c5000383d02c8690440300941d004200c041c2e080d14940c4124040d03422210a900d420504040b03d00c207000107055004860342c1544100120300f41192180c24280401c81c919580024605000fa0b000001c0c6501818a4108540c03210001500c003140c2c01c0780b2144c1006c001c89003490802e50f1440c00e6400d14418460103580f00d0718200030000f120451034000c500c200c20010559034144c282d9001c160044038034440408510089030014400d0381020b90000c00303224003906040003070031031a2400902390750300d0700300131182d00014444100c51010419a000d0152000381021043c0400d81820503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 607451600 1250 607450350 607450367
    0xf0f05040b070503040e040b07020d0215071b020a2607030c0b03060a0e0702070603050c0703090311042703030b03030315011b02061210080708060f070519030b040b10 73
    0x207015424000035168104003040003202c0082901c6200a48030780b801c1d04041d01030001c02c4032204054011b0340c4200e444a880420040394004010701c000e0701a44400d0003c503826924948003100c61003201c0d0620300560b89082c0e4101c010004502191482c1005412640013000a0107109210394041d003020310009400740c88000503a40e500304e00646a0750f982e400108803182586c414400b26181e8000e00140799800b140380c4055802c40e8400380710503281c02003c0c3c5128441c0b9107001d00000c240d1442400081c9030b046562080500080c0042503503080f080c2142e13101d01d10305904800c070002d049100030805405018002c07580c101100a0740c10741c40c6c050441034055490032591030401450284545902c0c00c01c04001e100e081e0042c0100361106140c00810307800d0a0103459120381001001000581190000380603021785282da800340000b601d0f2480f8104058001900040c240074003840301e01c0014200e1103448101c20000d55011502c05100b0003407108841400803158014003902c20040c3c0010b8000200 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 607452850 1250 607451600 607451609
    0x9120a11152706040f03030521010e060d2a0806071e11031e09011e050706230c04032a05100309200406090204030b06010c0f020d120f0f0504 62
    0x10400644402c00059040d01c00d5400209200a90080200a05034004054007581e0b11204c0d890040640d40380425407040d000340315184030b074050000003e0f442e040a4488100136882543e2403407091402046c0c00c40c0ca003446111000608006280c10800038408011041d0403c900303080c8107036420b9038003404408007545a07078442c00344010340040e1880c4031003c0088500780c614000a280c2e251042040a5400d584000e401a0018800307004e03020110030699220640c51000e40c440030310f80300c001c0c0e071044050242c02c7d00708810043c03201440315042e140c2143c0184940018107210341e40380d056140c800d0b030303440d00400059180301a9140188008924081440640e1002c07102091114500c500c21005400ca2640042c01d05516020400c20300d582a0320301c1c0701258040b10203006032a00ca41c00c00c4100c4c06144000b511500462020030047c2d405036000c800c4450060f18103d140d650641c0109000346400e410441d0b42e49107003070900325000c2d0b000b900d15030604031629090141d84c030b4007800180039000d2400b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 607454100 1250 607452850 607452907
    0x3010501081003021815030705062502061207020d0306050f131d0d09050d1205031f0602330610090e1e07050a0801030809120a1115 58
    0x200d500314840b074208000541d402480f9031200442d8590454200358180c48180300c00d991600340003240e10b800300305101515009070602c0d00b05007950f0055200500265a80c641400003d005100562100b030010618203460340c07900d0259003400f8100a19100744089a001050300d040414080780c0d03a09100f000b031408044914056100000b40f04c50000d00210f009003a44501800e44110040c00c042100c040c91030560b2124810542e0f0b40d424001c5098812000401c2d41c0d8050b00c685086602600255401c0316030400003c0864079000380303030600001e0320b0708840050303070090903003091400000700c0402001e0710200d00a6a40c1c014034000c21803140700070b098207100302880c59003d001c4510881720100200f9000e168001d041c1011502c00110300d42000c4c4802d035070340c21000001c02044c003130411a040c04125585041c5668619252040180c000c0146980e000d00310141c18980380c3d0003000b005090328041c051007094209200c04001849410304103214900c2010f129001c1c01031000c00301c0040e104200d40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 607455350 1250 607454100 607454117
    0x18040f020d15050403020c10050c0304181e0f060b09060a14130b0d0c02030313030309030513061107050916080411030f0708071a07030c03021e0c04050a02070803010501 74
    0xb800210000918000c110007624003420801815400554615020310a0329220041d119007170049030030344540d0f000c512140e80f081200b0001c84600072007017407980004480009641c1040b0042c0142d040241490710420740d214035103403c0c01039032482038200400b902808240f4120b00100410024000c0c0c0c1948c1c02030081050003d1035008200c0d0480b000703c0030b804001c00e0700c2c40e02d0384d80010607038010040d0182ca007880c08003069109400002102d00421405440801280d2a0394048010780000c0008800300242481a040e0003000205840050641070302c50304000b80e07043c1030062600c1c0d0313258095881601c84505100d180d0241110341c0c08900341c02d00d445012070780d66050010f06800f84d2940550503103e8407480010a0402103241020303122038000340d406d000c1d41c0b803610209250004541c600b00c05d0707081103010000b0380201e030300d981c1040c8240140c03240c110303501c09003118490074000141c40541040c3c40c0002e01d46883d02c41c2607482040b0040c02c60510b2025151480b5602050042d40d05005245 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 607456600 1250 607455350 607455353
    0x8040807021203031801110301211a01060e010e09060901090e03090a14180702190618050c0109080102030f180a052a0105191b17070218040f020d 64
    0xb0500030001058000440c1d5507030078030440c101410792036030f982d12981703518008200c8030386014501107a040310310b81c503000b2400b0a10b1803460f008400b01c07100215000680c800c1081d0000b106110000d0003045a915041da806d40240d002612090700d4041661040c421013080001a82e1800341c41d81c150b81d5445000202d42e80c0b5000128654403a03200d400c4d500c41d205400009076140082c3c00000c5e9140d0540b80c55000c1c1c0112103510790100d5003510310001581224092104045140d01a0b8203031034010703500072680885114a11500f03524000c030036905d58000325502d44095030010000b49c01071003000b00840c618a4408400014190080c0c028800300c161584000c591f0b0390300f0081c5800464001040d07aaa00c500c0ca060307422803c800b01d28054244035110401000d035030240c820303108400c003c03c0800103039031148142110009045081c00190011880a40011501c2004e48100c002c0c64011050360754521801000200c4100c0311601c0003c1244001300310000fa030700b0204201c01030381511104040d04c0203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 607457850 1250 607456600 607456609
    0x19060201060f320a05030106030f060e0a0503040e06060d0c020a060515060304060b27340e0102070b0f0c060609010b070809152214010504140303070606030b0a0e0c010804080702 78
    0x13140d104a500d0b40c21b0000c0072040c80318003c01c8000705840744504010304458410080c0c0c4815203104090b0141e0400e00c0b003040080794a003209a070140000b04028502802010b02404175600c01d40c85130700680c0040d81a13410070aa40c412241c11128400c174080900c5040400030321a41300040c4000c08140c0c9950b0340100c0ca40b03c0604c01074104501c61700c2e4007030300403400da85443c1681d0222500c4401400d04268171400000083e00c0d807101d025400d41d201e00854401d04140c030b0302c0300940d8140c2c0c11445800400204080300001400040204940e0140d84482080d8030f54a0f060014240703030b1090006600410410381d42804440d50341c0c2e482030041d134440d04147c0c001202c458854404801360400042c94408409100880c0c280c00440b600080d0011030f00c42c41e00c440c004032800b006070b0100d42c04100a001e14052400003d01c2010000e0491713283c00c00070b603180000c2e214203034006c44410b00480144041c0010b02d025654011100c2001045101ca0820000f02802000703400a0000e80c2c0010308ca41c29500e9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 607459100 1250 607457850 607457869
    0x10050a05130f0e0f070902070b0a0519050a0903090f0b16030201020408100c020105071805041109040f1d0c0d14100903080114010c050d0e19060201060f32 68
    0xb1480802c0054402c003002c0c3c19101d681040c28039040b40140e0b600807494a155200f62080030b82c00011403503660b520784c1038100c020400a061400c00c034042c2d513100304025019024545c81088040c501107151041490302807c00e40107600300401c441860701c020301000700058240ca007056002282000c1c20742c61410282d009101d1030300700400e20301802e560181000e041e80c0107004044810307402002a80c2d07032410202d94405940d020306000c040b40000402403443c00743c100841301800442d15600e043c0e00900020103d84e201c070300240999481314968000c0f1090842c0d0711504444000c01b034050380c20b0b03d07400101058140b10780200341c111842e110b102e00001c10407045105032152401041030709210300300500910000d01c910004007800c00030011841d4071810840329003a51040041c40d0584209038252070002240180680051003001940344010000c00407130300415203500009507281c100100c500080005030040c00c00001c0c2e0309140b4811000c180581801c4d102c0d803440d20841522100e001400c1c400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 607460350 1250 607459100 607459121
    0x70f0212010c020606130c02070b21130614040503090918060a150801060b310326091011070801140610030b0105040605070609021002010c0810050a0513 67
    0x41c42c0070a001c80c0940c00040380c1e8040c0b18101e85030404100003120302021380c0c0380625504016048900100b11240300d413070242620000c45c40c51100f0300c84051542080c0b000080300e1010340002c2111100003400168403404030b04900c5800807080901c1d25440c1ca0366684981300415001e01d0850340024000c04400f18541168240c001c00d48005050101014000e00070040d600c1007180030041c40002c04040511a4030200c5060428441c14981308000d100f44030251031080d124030008214888503520300140321540990300c12040f0b58900111074001682c41c8000e11503c002c1210200041500750742d40e02c0404900d030540d07240c10202c2210340f001560821107103a118403e29801e0115200201c403980c94101d204002c10742c0c0d8601c884080210403401d03500302d59001804140c0400c030501005104500501845006810100c0c0e01d4859a000c01e02c005030102180740180d40d00c0140210300e6a0080c4420b40104100f44a0076541e4103003070003c3c922004911440d445400c946589480c4c43c0c01c4c68000b100182c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 607461600 1250 607460350 607460353
    0xb0f1909050a20011704060204080a0305040305010b0109060c02061606051501081b0a080901020f160213150b09040e101b0206090607030b0607020a181a06070f0212 72
    0x303400d14080c0da8070761008038101c9211440c0048801c001c00001c500883c0c052050707440c80782000030074081101c911405001034031011307020000403641260410400c0c200d18425070305d596845286041c10f5084424070150341c2d0400500c4002000150b0b07006140c004881d80403201142c2c0c45881c0c0d001c21003240c582c402d0050180f03090500704081c145d81c0c0030b030351908410203072111001c0e40e540071584841d00c3d41c0c01e50b4002d444001445040c2c04240b150030010f512121400c001403600c0038414800c0c900341c0000b04051001221a000c0604500744000340381c448401c3c42200780440c4803c070074100d03140030150052204070300c0089601c0d00030f0b50f203c3e006600220440800d817911f0140c6d000d040d90217000320000c1d200c1c1442e0001455a0618800108280b10b40c8820024242c19140c11201b18054100c00c00074603800842400403401507078600e00180002d1651503802524181ca554094003038440c48421004001c03001d40c5952044e4455400300c1d18001ea02c102d54002d24215480000d409041400841c2e82c01d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 607462850 1250 607461600 607461611
    0x3180102030c15010f140303030a0c111501140603061003200f0a02060f130f0309030b0a0501090c02011404080f040e0a020d0f050103051e0304081b10020303040b0f19 73
    0x2540040c443c00781039404c1074420100013619101c90450303150f4201402605540100300052481100b980710803038400e03103440c01598585c40319404a2801204410740382001d0280c00040044902948503148000380c1680c10b2411131030b2000001d010688244809001d00d516442001e0084084550240b400411030850316100c001855080906400040180c800352040070301099030003d400100a1103102c051842c1864810681d85010702c507a04500d044042c011801404000107003034100c200c4c843c4002c40b200003503540c5441481400d41e81c03907000310000c0d6407600c04080301c0a61034052166000c0e411110f07071551000d8254004580380724550242c0200c80c440e1007446881d50450300286120303040040c060010040c0c08082e007086407400c2c40000c08a0f071069610990150365120760f0001d41c0c401c141070703c2c00e0a507254507890504901e002c00988000b800c416502c06490031000004160406100860441c6881d60b00d814012070068844c0211500b40d5000505030b102008900944c1c0d00c415509016 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 607464100 1250 607462850 607462873
    0x1c02030403021302090607060902040609090317070f052a010608100506041e0f0902040c0c02030709061d0405070b070c0617160e0f0325080105070203180102030c 71
    0x1140e41103400124410300c0d248910041c0800c4500030b071001500c008107502d00d85106583c0d460300510f00700d40304076007154903403000003580718181c881d007403195010361108444030321034220040003240000d104030b003800140601c0601142e1300c03a040d9078800407995000c9007123401c0c0b026482512480c02c1200d40d0790358200a03010964180104022191920345c0d03005103d191901e1040005036884046160500c0d8070b1a281d00c502c041450700070301f40c0580d02c040c00140b0b82c2102d40200c2e068480f61188030300452403060000e000c42c181001440c000741024541000380905200c0090340410a4003000c0005448460120303051000a019140c0100600340e1150341d1103103d07240000d821756040c40b840380482e00000b140c1d0802000610914465081040c00c0d81c80f002010105845820f1880c200c95000610f070740c0c1c0705149403410060385c3c2151402c840d000311862103801c006900d8101a8003c205264140000d200c03156070000161802c40060003a211141640b600040b4a14001d00c6066441841060441d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 607465350 1250 607464100 607464103
    0x210f0a0e0604090e1e0c0603071b05010c0e0402120a050402011103070b0a06081b0913050a0b0a05090304150c020607061404051002041d060303070c0b0901021b010c060903021c02 78
    0x61101c4c40300e00c10340f0382e000d070341c6004664030740c114807203100e40341e0081c02d4001e00a00d8103800442d440740e01428130540d0a0700041c00c0002144000300e040702c05a54820503001184e030440c0206c00d000104a406515080b246021041b9503170020b81a24145601c490204046a00036400d661144080e14200c0b51994254100a44004416203003224034515015005c5071104010520740c184140d8024101d0341454504180640e0350002094085c510a40e640002c0c0014001c0c00200120b0b40200d0004074641800c030840811035034041e101d207141d980f0800c010001c00c3c04241503a00105800c2c01c2180c040d103014008036415228800008020078506042101c21a101c01d10690042d03009070300b111013524200c0045022480385000b2a0070320300450141c544500e01103050301e90720241c00ba060300d003000060707a20400c00728207541100c3d800060225802c0345550b4100b108001c1d091540810300f1240c1140300010303006900c07003040600301c29100c10320700c1c0905008000b1408158000403000d10349518042000303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 607466600 1250 607465350 607465361
    0x20112020f070b090a02090630030f0417060114030616031e1b11070b0c070306091a0a060b070803091c0207181505190308030109020c210f0a0e060409 66
    0x4038407c41000700840c0207410309220a41c8501440d003c940440840d0810700ea000510b000944c0e00c26101c10006141ea085903000580020300851005180b0302a003407244074105503058101d01034046080024258a64000a045800c103510328404a070511008500710090000c1d8081c00c00d4030001d004944890480380d0b40840d0700ea0118218406083c03030840c038201c50446100443c4505648600320500c4a9002c900080ca04043c900044810103662681c4000540e0980d150070b4401c94098061300c243c02ca05462425801a050030381000300d18100101c0d60041d000d201c001074003c01000c0001034005904000d44490391200c002c01440d0124582c4000390f0318180b40c0140d00082c00700012010751a0381d540a071001d5002c00100d03100881d400c00d01400203054403079100044020006000101090740b6000860290401d4040581d0f04ca50300080c261500e5a144600d10300c903041e103850940030f40840e10a0f94450450b416416907141d90114046500c05890b1a0090380068002030015185980d03502c907 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 607467850 1250 607466600 607466603
    0x301030201020d080405071e08060103060213061707080411180a0e210901090b04060804021c020f09190218040c0810151209050703030e0a03020112020f070b090a 71
    0xc940c504444030b503044945030304c2600e00a02c550f1202005210700450800c0709145407054880c00340314a03548524481c50044280e006585059000a49803a075100d02d81c2d040d0701415041c02e00c010009032100845a001000400510401c08003101103401c204641e49040d80c4450000c140fa900c0400e0381c2040e6100c0c12050300c107100c0c114a052040700d8000c001180c0d420034044112002d030300103090004c1030f800c0b543c841000541000300c1d41d070b00032070301d10382c82800303070010305a256680d0441c2d282c988144602442c18868581002d0a030301c943c4001603880b1281f03c2d0488070b080d10282e03100e8664204015240c2c040340020310070103002141c0300f90410105400c3d102c601c9001c55060141e0380382e135581a00c2c9117100381d6400b070600e1100c06007849100d01081c41c00400740f00b0f614181e4081c1e00816a101d0840e240703c881265107802510080040c1944650b0320503e000084800f0f5580c1451a80003810000321801003c141f00d8000c58003403056440b070000e5a20b050341005243c1c0091900c0c808058a0b400c04500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 607469100 1250 607467850 607467853
    0x270513150f0f0603050c04020d14090c010e06040e0a1d0a030203030a050c0322021c0305070c080303101412060f04060e01050c07032d05130504020a090317040f0b030103020102 77
    0x2d4103580c0342d840c0c0500021243c100b005001012180414407020354400700c50030440c0d60719a213490800861030040b06214050032400f902c04101704000040c401a0f001e00d880e80300d02000d11040c40414056021030340c0084072104002050115075440c190055403028603d10503000c2d480c00310f4141500031000754407030098400100301c0c0750303103a0507900030034081a210b041c41d500c926a2084a040b5030940d08600150008000022004c3d45000c400100110064203c1c0040c4001c5420740800c81d2480031600680705030009141140741807400d490241c1101e20406a07070b034111000583d46921640c008907601040e0100340c4044d80342c200441d0711171030b000762411202645080301c005000345042c840c0314095540521038610780314050b00c0881c0c84001e00034100350324074100303082c0e508060120050001455820f40315182c40b01441104894028900d42c4002d001e24010400c00c1603050388280e0340e0301502c2e4000d0840b090000003d86614142c00340d5001040c194089407030208440c402c0c100554100d078402d90 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 607470350 1250 607469100 607469111
    0x60b150a081521190f02090a020403080310140315130204060305030f071b0f1406090414180a0507061808100f0c050a1707020a020612040c270513150f 66
    0x20490801d6000c10040500141e03117610440c4014030b08218165008000d07500f000d420a81c881d200ea110540c000d50310410740c0f148501040054011181c280711912000710068142038120700b8000800c0c034001040340b000b01800900b035000710340d9281d014402550b008000c5903210025020b40800e03603840b0003016140151141050781d80010100c516600351448545403101c100c0c64003480102003030038411916400b501c103010358040f0352600c3c440d2058444030750050b01c000c0e04110320185043e022080d80300d469a00041e581e100407400000e4907038111a241d00e03044442514110098480c0d0f411500034010798080e00b201c100d150740301e0390802e20500031249001c10640c110500251030602c150444180481c2142200d0741058002801d05541300c010750041c2c3c2c401001642c0001c405c0c4e449504002c074a4840041400203001000781000080c0000c00f140c01118500c548401070481c7c4c0b0301084400140d00e07440040d03210075105690110741a80602c080000d002c00041e00b002805d8000032a100007850803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 607471600 1250 607470350 607470373
    0x503030a020c040b0a090e0d08090a08070f05190308040c0b120711030f040b0c1506030a0b04021f0c030e0306011802030a0b0d0807060b150a081521 65
    0x441110030108840d001010038900302400d2001502e80031307016a600070040403000441d40058081c0d80180d0141c00040c29441048580140050030007914140c100d500c080202c200042d0340b01704464000ea008101803d5000c070601d03142d40340000e80c0c141c000000c003040585404250b00702d6200c41c0264402d0804d0080709440c2d4048540d82d0090350441904000c41a01044503e4007a140d0550106952010b403407518203400195070240d4004d60010301881700015015080700380920034090020b80744a41400c550a0100020395180130450001d0208800f040124085554078650018800c882c2c0349800d0074074002c400080c01c000700540c01500880c0d42e4480aa07035924012075814182c07195051f0301c0902c25aa45000c500a42000744041001c5903951100d130070383e6950240c0c060300c0b14031903d1016078414803841c11b58152400e61303809034000c5446ca80200307040000307881580c030070004518103413019941e030400e00320303c00442d110f4070b0343c000d80010800081180858440308030294081c040396a5001d09 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 607472850 1250 607471600 607471603
    0x2102010c0201021303020609130204141503060a0e0c0c0a1505060102060105030706051b0a0624060504122a05010e0603040f0b0c0706060f030b0c0913020c030f041205070503 76
    0x8102d03088000020020f03085c0014034091010b0a4406405054a84015240360038802260b02075004900e407009540400380d503c1ca44400710b90080002c907003074941035003841e902003600160030380030780b60502d4105c10008960010610a8402c4034121004940c060311b142e0030300750604220282c04d13008850800c0002542540005501e40c100c4801030010480341d480c04008a0320fa400103003003d01407102c0a01c0010310468204034941c0c0b01d81c016080042c460383e07010075504171070400a1aa11030302d814003004110f42038018050b035007221074844218910380154580720742d00c20b0f114101e08102034448901c420070003035807084800c1582c1003a210341c4031224601003042480d0100f11401040c001450161100042c101d1100a810107403c0c004541411403d941701001c0d81d509810100c4080c541442c05c0050003003030310703e03690406003100040e4582809c4d0b1000c103414054051048511a800150203420400c003001200d1800c02c0642900761902d0300c498089072520408001910640705110000c6101c5c5030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 607474100 1250 607472850 607472857
    0x406051207180e0a0b1e0106020c040c0306030807060501030b15060715141306060f0b070f03020309280e0c1803100207141c120203132102010c020102 66
    0x140c024070901d8604501c2441c103100300d02002032003a4581440b040703448030410940e2141441280341808620307046078490880311200e0550180c11a85e9801080029000f10b10601da2400542d00812603050340711042c0d000d020b403548001d210040006850041c0010b80d803040d4103272032080c1c407145251344943c1100318508444e003003c1644903100304070290010309071803d007aa15420510000c1827084a070b00f030703425440004039003202c040107901812404001d403070710501014041821070f422205040c8000c1d40301c6800340000040609251609400505000b0020380b10184c50003854183d10000d80519080b04080e4909003840501312080049600000780e8034441c841c003451014181080c0001598022480c400140315402d4045c00d00d800303194000ba8002885040d00138224107020282100803d49000c8240e003401021041c42006d5100881c0c1c031201c880c04a080d01d60015889441e8604821140c0b44940401800c102d04010400c0d160401c3c2e41c0710030001d206640003000882402c0b01c0690a0b0311 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 607475350 1250 607474100 607474129
    0xf080615061c0207020301060f26010603080403150e0111040e0a0605090f040303020d02030a020306090f360d02010605180f070c050f0114060a080a15020702131a040605 74
    0xc940c00c002112082c5907030301400c00180020000b042c180c0d540c0d0b50110140b0040c1d0412a6400c40f805031090306485102425003e114642000304822484e54881a0035800b0303c1c00014880c03032400d851003408251942160706030b4000380000b0030205030104503559a0703134864030400c2060704401000580d15500c40c131805084460150180100395280408000660b00c014400ca060541c20300944401218610180d84600d442007001662070401100b04101648020300c4201002101020041c81c00100f44020080d10140c044045040382080070310320170203080b0712801c64280b1401880100c00c0790b054000750100d50f41034803440f841c441d00140043e043d403070031200200c21000810200d10b0940c442d1400300307202030040341522224076030361800c80d0950300f1a00300c4400c400b5111040c0400c03403802d04884002440240000c00101d41c00ba5201c9042400d1121a104041e030b000ca17051040d51a0411481080d0609034003c2280a280c2d05500259860303c100140c01507243c110040303041d00b040c1d00390b086442c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 607476600 1250 607475350 607475377
    0x706020c01030c05270312040f05090604051b2d030406050105090108031e040b03041b05180609130f03230a1d0105040b04140f030102120c130f08061506 67
    0x10f8070700c1c814040117454040101909481046000d041c80483d070405440605a4510310b0300c00f091034075007000400c41c1c01030851031046107004180441250402d840016901600d00560b07164802c0944100221b03295490301c0a2240400450103060f2100b10021032040d48140400c203c50390300d480500070306007802d008030b4000340c1c020410004600c0038501507180b10201d4580082ca8542c445018422940094604480000e40c030b1809001e0b40c4d008101c0d62000d050b050340c14508601054051143d03100d0081c11711802104407901140300860003080030042d50740c0200d4129211116840d00500c009886480c040c8071003042c0121a041c1e0244000b00c1e204001c42e9902c1d81224082d40c440800303a1744040e038403035060000c100030010340e00301180c010304010400c0700403160304003208006022030034030602c1c00135100e41d2040120701c0c0e19500b0001d9954000880440258503604002a10290700d02641c10951b440c1c411201c001840850000d4214402c4410080c144419002c0a0138045c02e401050034210744d5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 607477850 1250 607476600 607476637
    0x1b0e090114181906030609170a050904050c0702060a0512010506090603190b130c032025021c031206060509040f02041a0702210304180e0706020c01030c05 68
    0xb0240c809003054200da40c14480c20422661680d0b0314040b54407503801150607503100c1c0d01000078801c0071a0a81c041800300d000242c0740c04d03c0c00500408a00c2480c000611540e901c50110b0041700354070054559080d80640312a580300c0d40d00b48040c007a074010401c641c0007403040c800042801e0030040c0694084800c0505158115181d0000c0c401c0c000301d004402d00141507950b2210034440e913500721112404041d4000008220210f044014290b40d507440c0d55901e40d8425a00794008150b00500304c1d171104070040d46400d40c241020020040710286180065440850207003010306000650410702c00d418404d403212840d080312441c0c4203050354035500c503c82c04950f003401030026030308268104a0015036034810041c81d060b01c3d07054009142a2182d008041010082480c00c21824a0040c2e401001d00c40c4d01104109480d01c0d406a54074460b502500014100c100e122518004403500801e000e020064261440513448103c001c1d80e0300c189982c014002800c1501d01c41140d4081c5040324010f0000c204030111 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 607479100 1250 607477850 607477879
    0x302060408031e240901050d020d02060f0706050f1e040b07050c0f0606010206090f03030c070602040b030f160c1709060f030a061a1911011b0e090114 66
    0x142d4000401e4042c80c1103002d07054144890364000f056105602e00009681c403c840078501d810688060340c4802d02424035a030061041e0764654116448095044845070361a014500c0840e00c1805454602041007401064050800444c0d0b0401f81c030582002d811141d05a031440052448002d050030020445034510b008a0040ba43c070109035940407119080482c603041260015914240746684107084c3e0f40c021600707208087da410310086402101c810020700280501e100c0c820344921010f42200708031100058000d04120b500d4058800511004000503220326165035018142e920482c1c07000c2c80c2903802492094180d0241102844640e08608604140b901c0c09070f880a42d54440806280d11620610141c00e8040d548001148109000c1c07201050b224a4081012105901030381481e082080a101c000c156001c0c4050b41401d0141c03e2506509030945e500304240107024061101882c1e41405000301c142c150041ca404e0648042554418820b07a039071040012074684150390300354000080d100012 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 607480350 1250 607479100 607479113
    0x9100503010c1b170f070804051503010f14010e06040314010501090516030f0e07060915050403080a0c020f031212010b18010f17010608040605100509160c060f021e0703020604 77
    0x1410408140038136191408013240500e032078100705421500e103a0002000d0210382800e035120441d05815400b403d041d5410300a6031344c145400c2c0d0207542181d1041c0007400b0700030ba02c900c01c10040a040586116900c03a141d052812200103c041e0502042d0308117000000e0401c224440d0030b10840701c036850030050020750f01d0220042c00000e2030002c00e080d1100d2082c2c0540301c05110250051186803600d540c55441c000035040c0c1c000c1c0c6454403c0611005020400124103440c04441140d95a03181807443c148403480010880203010451a4051088031401c2e48801d152800500034403184510b0704201d40e1380d0303d800000f40d2050b15a00000c1e5490609088002d50080a112a030040e45050480d281e206500c200940c4c40c00176030154000510398030501050080c0c0b40b052603009900201c1c810015401c1001040c0d11050207401e054181e9040c0e178a00c004240302d00801c0504560040040c007000c0346006004000c2c0d08030310400f01030129254003070010000c0e5182241c11140e8141c0190089513202d45410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 607481600 1250 607480350 607480373
    0x6150801032a0308030c1306110a0609030519110c150d2007030206011505070b070f05040b030f011d1324021b0d02010b09010e0403020c09100503010c1b 67
    0x29a41c0000038001c4001a64000594490722181c00c1c059100e00d681f4080b030300003111542c416010f100c0131910104c100100442d0321900c10307070460b41c0401c0c02d00407440c00b19014400c4102804007005200c6c3c05030700141d1b200000000600681e0102c40034803810300100311405018040703546880d90f040110b10002a05500240d00480004503428042d6416609180d4158440e03401180140c120030300502000030540070220464500e480c0c550b080c42082e83e12490300c0f840c09480182401059400b02e030f21940305d40100c0f406801c03042042d030340302e0502c1400741c002030000780142c02c01804044605240c01001c000041c1c07103503103039160f8480c50341d005481c0d40301001e6000305801500c11342c2d058034101010460000740103007580001e4590240d2100100c55040100780090f003400c59061007010059503803214003c905440ca25000803030341d501c484c6420ba140181107a04c1540000c210810402c89104034550007003107540590081c061050000001c60b03009082412243e25071605502c1c1c00e0100740201c0d02e4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 607482850 1250 607481600 607481663
    0x302101a01080a0c0e06040b1903050112021e0a0e010503150c031b04030c181b02030a0302030a1409030c070e16050c0a020a0f03110f0d2010030615080103 68
    0x82c1e217901e000350000c9416a841508003c0a440001032114900081855524200c50307441c6410041941008071104081015040107881201c0224100c417480714480800c0c0c0d43d4103001803195994070703651801c808525000b481010300c03a010341104c80901c100c41c03c00310746c42400142c2485145a42d600c07420242004011002540500180008400101070448a80152501300d1880c14003410354440c26040d294408140d030f1101c01021183c802c110f40000540d607200c031085c1400740c2c50ba078170074200c0340c010119070450f00b015444940c02d000c80302c2030120003800c0c2070b40d8070f00c1980c581540b124084000c0100c00d40d0307450340e02600d0000f640741c0d50340308501404c00300030614141c8442c459150001000e1000c0781d0080d180305220a20704004200154217501d4a1840958a080c0344000703080004104110001001e0709803140c0703140c105074104000303450000080c0700800b10b0708170002021004004001b24011001c07102c0c1c050380c0306820180511362542c101d07a40302134101c08030301c3c4000601c6c0000040465 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 607484100 1250 607482850 607482857
    0x60906120c060703031406120304090911033012040305070f330e030a1b0605040602090f030a020f040e07050a0b090a0506120103060902120105040302101a01080a0c 72
    0x7001120366501c1c1c1c02800e400c0d01907940400c1031030f02000f03d009100c4010301a40e1050300c3e0984072003150040442550100c2c0e1035410002a4510b19080c41128081c0052407140c0c140200c80c11714280c131030a488040c50184820030301401030340180c507500965110320828120601e025000090009101da0010407503036200b440110501001680c44510101d007802074400c4000c5a021426503c1071840c0d440c1c403250411040c1480a0a40704490b2a00ea03c15441540c0030448406ca42c44d58850228070641c0d0740a900c0034040203d0b2401c1e041032030003074001d0860305101d170041968540d040e01d000a0054134085d0001d01d402080f4290804100040842110f1000c1c94081e8810001e06036543c108000001c20070311400d181c0c0e0788245020040102810b40116204090078040c90215544a0380060f040d030b42e11600c005400300e218000101d001014040c000d009600305404c04c0100b503804520350072511114482400f11141c0c828000c0c00004c40c0078001030021703400b0800034040e0196500b1002c220000c031b05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 607485350 1250 607484100 607484113
    0x17011d0c13110a02460303091205030604060f030206031f090e0606040609060602060c0f0f041e09061505030a0b03061f0504061809020307260c0301020306090612 71
    0x80405800d07802006240c400f5800400a802d1401485649640255003020b1700764000b05141c5201c0c059000c81e118034040080e9086140d000305402a07026120072a0402110110010f01c00c05c020907a61040380c42e9070082e418610001220007000c150b61090340c0d4010030b042d007183c0c0c071158803007644024070160484003414618001224010b0b4401c510307003950410054009440d0480c1480180d80c0d0540c0b0086006207004010049581c2c04111580c000b50240c00e1682d0b03c55070003202400d5800780e00c070212020200058006603041403004c03590703c5d50b40e40c001c0d60080156503006801c101c0d03a07244212000081c0c0d0207180084a846900196030040d200100040c1d24000b41d0082403070003c0c11109034401c01411142030400f0350040391803030000c0c241107c0500030307107003010308005000e8003881c0e00418960700c1c0d0030712408541d01444020042d007110100d00e00c038482006011001d51484041100e4180940021b0030054281030080301d1042c2070141003a404d43d200c1308240800c0b418075180c140c0980c020030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 607486600 1250 607485350 607485371
    0xf0a060302030a090c0b1e0909010611071508090c0306090c0105090d1505040317150625080405040c0e0625080705010605090601080f0703051005060417011d0c13 71
    0x120707440000e4807980b109181c0b03c178801000d9042442804040c200f64000901c0424525502d50b6a654191241031800f400ca0368140c440a91030716040d3b8102070002c1101d4031821003074039032082c14140f0404158041360b100d030303000d00285521403c3c01e4403541d500d604401044080d550050700105022400a001d00e60781d002e80b904c412010070900c0b100304414684a5042c0014075605c015452119400d58025060500b884d12140d8181407480c442039008210108495a10320503001241210300790001c2201514415460591181e0b071090280030702c19413900d180e6101c5244a4025000c01d960082d108516000c011254407040d5882c100081c05410a15501e41c00065802c0c1c000e04100e91181d0000715a6a05100412446440c00ac2006040003249004c0041000380c1703d580c583c02031a21304000a250302c84100c0d4580b00c040ea508601c2d00600b001030b0010341c200d004003c09003e00980c20007004035101d8800d1303046075446411380070782c5c1540c40b0144402c810f14141400000040213a8800980003055 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 607487850 1250 607486600 607486613
    0x190221010803040e0c04060c110a03061e060b090609120c03250e0606030f0603010612030207140409032106050a0314010c02123f150f0a060302030a09 66
    0x241c202024076080403808001040c04d044400e41c000341c0b01041d290800741400001800c120f1350540c098008242400c2c81d804940f00d0610003001746800c4001403064070003100000c50003014010001e80114900342d0700140c03641140040d9004600010000ca107403254003c10007000741300d50903001c0990b0040304000e420315941045a00c10a03a800450b5009400b4101480034482c141130303004c0c0e41100c00384020132000f5560b402c201c0b94844c00b80d41c0c0e800c0003919803501090040c580350f04044600c4607800d215000307040c1c0004010741220b10107201a1080c0071541e09100c00d845030024001d020544d62140d240011140c0580d40049034100b4900260507540d44002440105059005071850b0300d11041e42c00c0381d84800e0003031206541c03180c0003d140c040d21030440c0c0f42941c46100581c000020a806520b29150b807161055050a6a0032141065036495442c079800c0160040e6205d84030200c0600c80c13020181002c022a11049a004111043c1c0a00e800c0f4260003a60000304001c01030f565450703081000844 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 607489100 1250 607487850 607487917
    0x70e09041a090a15020a0e0402130f080f1e0715031107080a030f0501060e1309020907030b120a020102100513060c050a1202030105061e0d0905010504030e0103051902 73
    0xb220040440e0701050074007101c2d2400381c40e424038203035004200401c40c00e034103c43e04a2000d00c0542d00180c0e105a00d4101c010504919001942442c00e019400903240c000040d90b44000e0200505440c0c140704c11800c000140e50780c030310944070240c1020000700030071071609610140300542410085100c00b501c01c0c000d1041c1c0d1140000f11042d440c082144c040841d071610654280450841741080f165060140250414000001d071905c951035041709059030b00a02e03000589800ea024140c19400c0c02e04400c09406041144881c074003404005580c81340c3c080d40041c0c040107098040c1c0181940c00101c4192601902c001807102c03405043c442d4180c2c0008085e0311404845584a9413855102c0c120240004c11000e0291900c0002c1030040c8018030a80d9a20001c0b1a020f8507411580c0c410559030314405240341c0034940f1462030b501e19208801d400d12406411682c4103034803aa9403480100c0843d00158101d81007543c221031000c1c01c2110ba106041170660003403081583c101180134641000b041c80092280 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 607490350 1250 607489100 607489111
    0xa03030504150c0804060c0806010c02060d091e05061b03130309050d050109050d0f02070e0709271b080a0e100f1b0c080304061e05010b03061008070e09041a 69
    0x4e48980c10001440600e01c03900c0480e03003e510304002682002c0700002d001c0a541e04010717105400000707004002d96881c0d445034500c0d43d8000e105140c18015042c0c0758180000100064601e800b40c100014044021072084d14040f08142c01030038110b48442d00e051031001803009049084c4003060703e004c40e00c0d076100040150b40340e100d600041118903491a10500b800407507070a003c10b229001d64a4200f9907000b040100c1034402040d02c0800698071520100e910f83c0301c03039000300c201420240f1441c00e600c580c5011100c03190701c071031824000544d24003c804011032400580400146d400d034080388603602c5a800c89030301c3c24148012214601c3c8418001e40803181d8656014450999421124a400318582c100d0f110700525408c0614400e96039484607159403000a00c0101402c0d90f83e01c0d41024056414801c51020f00201030400c9a507843e103001c00c00c43c0e40309503041031048a626440c0c00c0d078144225660703031084007565660780502080d28280003100102a0049410043c16180039041350302081c80144200d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 607491600 1250 607490350 607490357
    0x140a03090f02150a090501030b01020c040e030904110c06090303150f0d1b060806030a0b0f0c070f030e010810081c1b030f090b030714031e0403030c0e0d02030a03030504150c 76
    0x1140003603c0589800461b900c2075060609100c03041e80c040ea000300e0000002001a140801d286800600306400d502c11400e00c2c542c842d00d041c551052150528010b407450080480031124203846013116140c0d0390104943c403007851010f444880740c080c18021800c0c00940300c09080d00c81d4502c1c0315600c0c20b0100030b520f441d0000c0e541403540c0030070208c1d600025007504050140c01400360102c0548a920030b9420060000d07007400c200c2c401107040c450500b41110102c0742c10040241c0f007a2168680286054034003143d030b80c0003914034008070310000810950b5200700c444c000014410f02144c2c10110340181c0300d50f8140003e00070740207480c405460540ea413818034540309651f600b64038100d402d809030540400d44c0021704803550500802ca90190032091002d03500d05144452900c07940d4555800d6143c0c40d011038101c414105a0050100b0103425801006402800da1525141950150140240325141d4100650706a00115011020138001d130310850300b140c0200021080d0310ac0d0f102c3c40c0c0b001d5030701200f000b1002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 607492850 1250 607491600 607491607
    0x1f1101060311130501260f1609050a0b0a05010f0302090901031223220909060c2303060d060e0f060109140702061f150203040302040c140a03090f0215 66
    0x2907141076066143ca901c81050200140d506090400402d00000350810b5209030701a0205031403548100940f604403114442103801040c07076000200300003002c1b031003030224090038007011605a10070b50042c403c070940080e00e01c213000b92800780119406c007525040d0a090690030800c1c2c0300591030303084445010314051002071542c0c002c50742c40201400c0c0c5601d800e904c00b4041a400105425084080341c0a0309801d4040704410403100c0f650700c55140c00740d80700c0c5109520f0000d003101008010b802a040800c21900c03800e1041004114211102e04034202003200d0740020000543c0307629140d031a00e24154060300c000112586243d041a181a001101c80c0040d90b0080c0010420801d4602a5450000c42c1c500c4100c10390404000c043d54540b4090075582c10410000300044c84c1c40c2040d8041c50003042c1c0401104554a030030315029481303520a01090707010720f0401d180c10100e540a030300c00d91340114860001c98901003250204800414101d041100c00e003000d0f1702d010001d80c0daa803001c0c001580500180c143d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 607494100 1250 607492850 607492883
    0x90e07090507080604090620120a0c1b0302120c0a0c05030f07030321150e15090105040506040b04060603150b13051c0c0e150321070c0e04080403020a0906051f11010603 74
    0x10349c02c4001c190550300e80c10142c08441240c0d118400f10030301c0c011822083c00042c030900d0183d0a0102c240100d82c01c5a102252030306001c903000400f911520b000d11000c01d0010740381e07003d058581c0d03451002170307015611101c0700f000042c3c41502e400410110546154424890f0440070400740c0b030f45407004414206000f0024460b43c400b2030702803030f044030380390901902a0b422000416000c0c2014803580b84200e969500203203290b145d80d0001c40603070000408c100311071900d905c0d0180007000e90320300c040345860308408041221010441240e083c03102c40707544415414546002c002e40c030020620030410240700c0c0384000000401540904001e040128000705061810510f81407101508600381c81c441d41c4040441c86c80188103003080840e082007035041c90356800309804d08000c0e9100d246d000c0118490244200400e000c110400781003a61710858a40b002c841d900d1040300f060f121a07002d41ca0340300c0701484803003000400304c8880500d101e109042228020407142030a50842d13003158000d84502142e1068a030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 607495350 1250 607494100 607494127
    0x312070c06020309010c0b270115090212012d080d0f0e010e130b03060a0203150a030b01122f120312040b09011401090e07090507080604090620 63
    0x4054070051008606104400f000208294241031001d00302210b0040400d000e42c0c10700c40030300000c9588201e00d00e4207042e4003880900070320f140d0621045210100b40d001c00c1c0b4036641e001300e0785440c1c101c12440116900f402c0d9040754500d800c2070580c0d0540c21900b0844104440b0128400c0200980c03800340c03070070a03c00480031740a0b103c40c03d1160204030012040100682c1c2010800c040041c1c03d40c0d00d0040700096480c1030000380502940a58148160002c03c0219146500294400e80103403440215407502e50007488018000c900008010201110051244c0d18402d4003588032a8003e020309030b68820201584041400c8003c0146001085d0039260500b5040191003100080304c0040290700e040003100480300e4118002c1c000620101c0000007082c8130207800d4022004c4025030380301d6040c0c556503515401c0010100081204640d0084081c00610014103100781445040d9544a0b11829a14982004014040c0302400c0725007955516465240500f04540450004e440000341643e9200c01001031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 607496600 1250 607495350 607495373
    0x6030f0309051009080d11101404051b060a080601020309040e240903041a090402210a0b0906010503073015081207110607080423210a02031207 63
    0x150140444c00034208103403440095034000780c2e03109150070103803408101c1d8414144a500d0407005d44242c145180c4005000e404014180158411402c41e140304980300c58880c540c40c10784140e00c0d40001d0600c4591100c9000f090760647c03060701441035a142c2042c40300054211507640325000c030258041c200d000200a000c205030844411103035040380071490429400740d901d2146018885050111242900254040c1c0c1c003910220303000180305540342c0c4a80c150021040c40d0000c02c0d944280e01c69804100d50411a02c1000100c0701c000c0c0c0003001d1540c5110040d1401c1e4030140c00041000400381034140c00448005103c4000384080c42c9809804652288680c25100c030480e40348000040684200403440d40040c0c1c0c10300014480c885652940b041e41045100a0381c2d18980c1900302c0000200101000903240c0104162000b5030803e40001c021a08581010a042c40c091500912500e080e80c01c041d190b218050b080881940132200300c2e0009501003410700c11001ca0110b00701c040840c0340740c100640c14048 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 607497850 1250 607496600 607496629
    0x702190311031615020c032b05090a06031116060606020d0e18070215090d11060727080f030307082206020708040806040c091503020f06030a06030f030905 68
    0x100308034010b00820080f103092620071920420142c8102084681c024803607082c200000030140c0b0582d84940100300651104428024044102100c459489501030700a580d13030084003524a00b041d41c00d0440036401000c4240100c540314406001d143c50746400c1c80888008030b8401c1c44085070b1580341c1075010745410080d0555038140030a042103800280c98041003e20b01600c02c82d104007480d01d40c0d0100340c0c00c11141070744542071080b5000030410503540019000c0c48110b850380d200ea400c61102e4508a440303030000e40b5103000256100e40340150015080e69480c903815803010301c0d02c0e08142e940c290a482c120700d40b0f0b56040517030004010820119001262281d01056a0000e0180c8088a5450000360040c1000c01091903074040780c50b5043c8203500050710042c2c8440c408585650038182004101041584242d03d5201d040000710180e40014401100860380d014000745070307280b200400c015060300300500d180c502a66408001000c225040c07401070405000b42c0f80c81c20410700740020f120603400810790 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 607499100 1250 607497850 607497853
    0x27130b010e0a050630130308072a110a0e0612031207120b21070b0913180503120108191505280f1506050f0c03070219031103 55
    0x4000703a031101400c41e40035075041178a240810207402c403150500d059010010120089440800c000e401e0111022802140643c0345c520703445d59501c1040342d4502c2960748004900b50901d41e00c070282400002c0d0003121900c58003218412000380c0022450754101c1340c0c00030b102c6101c0700c01406460708050300e518294007285400755141c08280c41881c0418000501000c1c2080b004003007005105200394001c4008440050550350213095041d020303031030407c00c00c0c250103150250203c00207207421100d086510b01c810282100503209031030740f841d50041c5007111405603107100c240c500c0c07400102c0030300060501d0100c0030030350390310395040050181c13900920f40b1030481c000305e4061f9a40c001c20300d49581d2100c2b0030340c9040c3c041001d5a84c0e0b4940264403000700f01500c2c81d41c121442000110f121070300607481c50084000c082105107541c104002e0806800d00c1180c2c0450801c10007105854540401040002c014004a074601052503000c00c0c06240f0b800d040c00f6801d280d90808ac410044500e41904c1c00c84001c40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 607500350 1250 607499100 607499119
    0x10090f02090102030f07080717070302060a0c0807111509030a2007030204090f0605010b09032e021b0303010b041a0703080114210105040c08060c27130b010e 69
    0x500113540c074812008501104e26000c144c840401c8007400c00c4a00e1548e0180c0c00140400c0017013803616440d00010001c901502881c03000810301c41c00d138816020081c985644060041c3c03549403081e105041c92401c001d102d07000e01502d0b001c03c01c0100455030701610aa6000303683d9010040b50041c102280075030f06840b41d11400c40d02841e40c4c000021200141c90701140d0001d601016032030003a000c142a084024801403c2c0000020034009203000740002107415410350312002c50010860705221010700351000c11110360805070381c06a4056001e0845010a445554020382d00703403109030b2450300f0980c011683d0090000301480740500d03d5407910000c0d0b03000b0101a080c685540e9000c0c004071070500454004100e07103120440c0a41e600a11641d145811058082c0300b840d0039032036907020b000121400c0d1031a4668200003c5c51460010b9480d129a9078006151b0404100d400f03810642080c4000311002c1550700c0c00324030900d58078580c034085200c10055000500e184180005000c80030a03800c030a21489150 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 607501600 1250 607500350 607500367
    0xa03030b04090b10140a08030d110715050f011202030a06020a030e070b0901021b030d030e0c1005040e131707230a050601050301051b030c07290a02130501180e10090f02 74
    0x50b24030b4801518030201383c1a012111035051800b42d042f000c0e041c0860420340c4448841e040c1c4c0b010740907005000c190300c8986e0700c5014012941a00c10002501030b8420344c7d0580c042003007503010380300c18805c034a400306030504a80d000c0362030002240c00c0318aa2400024800c030b155a0100708419000c00c0890320784030810168030000741c90310a40900310051545604148074141c405125014403003c0c0104081103900c10810000c104c0d4200307000f050000011140070030444421070114840c0203a110940019840100e1407001998000301001c6034450f803008206a100c4082e50b000c0040e61031504014a000b00e001e06040740703040f42c1a44454000d91404d400e00481c2442d088d15400203070a013501450b40c13a220001007041074454000c0181052154404562074481d1000c2c403416080a150b4840c5280e0f1038038004d01040707118401441d0120324040508010b15401007101d0b490390400c41c66260300140c1d950303003083d0603d2400c40d840c801401841e00c0c00d006100032032240b84044e1107982000c50030800718 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 607502850 1250 607501600 607501603
    0xf030a020c0337061109190302091b0c03070308070e090105100507031404090603020a060215060d061b18080703200607050a030305040605180a03030b04090b10140a08 73
    0x4034401ca6030080300f00c1c5912504002020000c0d181580d20800401c00202d0000c550341c00350700580c4403148181c20480001d8410320444000d00c0917a40c0040c508650307a290030f9020740090f015942d504054440500c04c190900e101480503101c80e6010f0b4481b180a4503142e20000c002c840364480c49031064410100501c069100c940c0605401a01030918542e900a00d0505807010740fa840e10081c1c0b02200000c02141031410368004034116071080c0e4140240c5502d500d0103a07102c0911003000c40f450400a80041c03102e01d40389400700c084a024420005181035001d100c460392051f42c0710000d02086400d05007811100c112040c0b0350040003441c001c0c240b0282141d035545401004000c443c0162540401600c4055a072001210603003a885011901040485d160290103440210750a40701d0342d107440001004222246810950784a8038005884241c545a509400070110107600f0b40c1c1240c2e0700c0104600140194108602901005510700d180350300e007141c1e0082003040a42c1c000c0c0504103042c800c108a010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 607504100 1250 607502850 607502893
    0xd1803020c040c110604150507050c0a03031509150302090903040302090a2007060606180302210102130308030907050d1e03052a060a06062c030f030a020c03 69
    0x122800b05800524032411a0800d40d019084450740c0924000c3c8420040c1c11040180c804984800c28001550b0703402092b146400348a404a1141c3c00400b0118000f910a90104420070f0074401041c14454680b500d01c022158046065884030341404024019486c1040e1000c0d44a22940021407425003542e000c2040104c01519924585031a1403c1454401364441c084c072100e40030024140d1501c0740c2c0e080140c0604110f1007560041110701c18410700c00b1002280d4141540e40261400700d0755945a5401070740d5900e840481d9800d55802d2000b5554800c00d000a10011400784a5440c0c90741000308410b82815940d500061044140d8541140002c81105002d80c0d01040b41c0143c1c48a602541010345107449080c261880c40400c12005085240583c080d1a081c45043d0088418907038400840e002155034601030138011030408d501201411700720101480700005858140861046040d010a01c8c1030b000101c9481c0c95003001c5200f00b01d6079410013070303012050700450003801c500d50fa10494445806 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 607505350 1250 607504100 607504123
    0x31b1c050c0405040e1b010f170901060e091b09040b04080a1101090c150c0302030d0e0705030d0801060f08040b010504020a030e1608070915120201020f070801020d180302 75
    0xd44a00000704a100c0420540c0c00400c400b5005214101c1c040c02040c0e201c0700c1404500c2c0e05241a40e541182951080143c0c03075150040792104d05180d0751040d28002c180000815140e40c640d2190b001250741c0042421150041c9994001800240b03044864116003c91041c00e060260701c0001c00c21001c42d074454500703600076801c508220369402c98008111400201800703032001d55828a1400350400680044003000c4a032183d030720b29110404150110350212a010307000e070050740240440404d940195004884409490040350204ca544201090800c660800c02e03001050000004021041c1c02240340c4a11310307401e10381120305207441c1c0e540c043c081e1018040c00707004c2c0f41e000c28041805402503003c1c0d0074819007241241c801d10f07082280480040c9003801105654064080b00040c1060207004904400303001e00440603015060150003010007251010980c114450300085d2014003005000380300c085c0800c1000035954100c42e051010945210a9035408080303003035420302c07002c02d5003c00e4000110 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 607506600 1250 607505350 607505407
    0xf1a1305060c07030b19050105040209280e01170717030f07030504050d200d03020604020d330b014113080f010204080d1b06050c031b 59
    0x50070b1000320749181100c2a04002c4c58008000140300501d10008120b2020000c0d9420610a6a8a030400d01c400d90103900c030307415000a442e9a00000960800343d000c2c0c48492003900d161481c5a40e040c41c0a0344510030313030000c2050101101e400d089104140303c0e071006000c0b01ea01008021058449c080e07a28854015500e83c00f500c00300f130940c20140300d11300b00c9004000040190000c0840d908000c003a40c0000b400550445601b101e0310196800c02613500014185c250b00a0480e0740d442ea0244940c28003500000c45a101c000208890041c03038a00c1ca003140b1503640d6101c2c4550128a00c3c801d8100d8a8046810341400140314104040e40c3c0070303481c40e13040c884240204040d40707c021481100c028040400c1c03170710001d001013007010340c0b950030111301401c0743c003414126110004402c1c04e4508030f214900030311819820030580ba80c021401517400d409100811040c845010410340c44480441e81c05075440c4031514000070610088403440003c1c3ca12012125000c68545659220150380e1040c00c0000300180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 607507850 1250 607506600 607506607
    0xe030601082e0b21010c14070609020f09040b0405060606090a0b34030e04020f1b030708030f090606040c0207060c050c04050405031215091803070c0f1a130506 70
    0x148043e03040108164805000403c9150142d50410482881001d64410540c81d0106400d0401d11071b9038043c0014100c2e01d040d40c078000f92a2582005001c4a41c426600150803140b4800c2d40e89030504014801c134040c44c4103c02078140f40c50a00e0814101a19080c032510060100c0300d02c2c0d5640b80801c2c000c036040342e09c440766a00c0c51a00740c00040000c0708049030b00b0000c1805548028540001c02d20120707442903680f86c4800c000e500411040340a07405031041701c07c0b002e01880404241040e10106000c100d501203908000d4103588050141c1e0045401030300101e00c0a040c041c100e01d00308801d40d00300400700d90901c142c2042c107030000c2d80d4035000c0c403075002009041511030b024054180101c9060000180c030600141c030f0036040040d6030781d200c2850000181c402e0700c005950a00310134088240c402e40101401c60603181c20206402010340060448014001001310000151201c1c605c00d0041440e030361651407403454100d60100d030710050707602e01070082400c021204104400030200070944d01c04958454a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 607509100 1250 607507850 607507933
    0x70c050a0f05030d20070209040302100510060e0405191104180b0a0501021b010807030212040b060102060603190b101a04050316051309210e03060108 66
    0x1404a102101800c8011032818200c00e211000c0300600a180b04e414081c04040003415265000c0c08080c4482d101079042804050014680b00340c1854000d8002d1049a160018a82d004803c07503005413400c1c0f0f114400b0b0f42040060503001815081c0300541110200040c2c075087d0051014500e40b039140c45090356a500311559404121400c2e140a04009860181264160328044004028030750816204a0400400203019031002036000c4a0b20312407030140e200070540000650f440039002e0800c5062503005c0c0501500f407a2a0300610703100340d000705000c0d0880d080807400a1305003440070b8130050107030300b003112a203c00c44280003040f45e411f540001d40d140240e5a888003441c01c0800e0b60005441204075a09030180240310720080c1065803000c4054659642c0410b000c890300040f140b10359038010b8100f003201585103410303a02c000b0171030b40034400075403840f40c0800400200c8100c2d4010360020400c03080d81d1b008a810100000b501500882c2d0050003c40307108002600301d080118070300c0c0f80c8558002d00126 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 607510350 1250 607509100 607509103
    0x80c0a0b070b0a0f0e10140928020409030810050402251a0736150e040c090306050f01030b0f07050421030807021513021f030203011d0906070c05 64
    0x10b0004120b04810071485c14001c1c00c150710b83c078180000036540ca06143c2d91000703032841860402e02070b0000100902160f45815404070303850345c00b4143c0111441c6036509034000368440e07014403a491446507a9641062a25000704681c1184580196006a1042c420800c0d094200c6c002080c038044007603160b4030700210514100141d50380080ca07500410402c40d0034000e0341c1d500a11552686441402a09480d0000c0040b10955400c41d03209040c14001e400010132204407002d40c4034a03c035103185802440711719000301107020748030039810003000a00d000e4001c0040c0301c014424250030000150f520805540740d80c413a0440008003400016044645102048040340603000b00da0051100c814180c0c0e8416201a5070203245a42590613000b0824000020b0aa980301080c6e10f440c034103080b1409030440e1a0080e00b803411450100c002c03a04801100c1d0360b540a600c0a2598681c4015541d03001342e541e606084c400790754a000307201c405443ca031062082c0004040003045980c1d02800c1440d160a1081d060305005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 607511600 1250 607510350 607510361
    0xc0903020a09200c0106030201021b09070c0f06060303050c19110907120c0801060806010503101802040306020408030a09080a0b0105240d090b07020d0801031b08030c07080c0a0b070b0a 81
    0x402407440f0004400b1941901904000708483c000d0302510300c141d808401010314450741030381241c1c0c086405400a08994010724000c0e56150061896050100b950798460086810301e8005601081c00071131818582042041031461141080621040380f980540d901d40c2d045004584451085515000241040744140d202c4490000005070500a180314044040d0801c0720a0007800005130040300015002e50041e02144d0107040c0b44202191424901703040d0001d8030b41c594030002c00e402c8e000c100001c00300c0c4047c00508050490600075580e00c460040340600011420f030300800d01c81c1c0040d400100417a005003134003811100d054480741315000060300644100302d00c0032a043d5060102151054915160b41d00022240d4403a20f003071301807a140d04500f42e982d816044890700005e10007800510004044607a1010031940448080b556182c840c0d6046042d82c1045c46c035050b469024210410050b0410414003143c080c082c1c480c03403925070078050500c0d114803030381e103025003248100e17804600603c5069016 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 607512850 1250 607511600 607511651
    0xc140a230301021e0717030f19020f0705061009141303021c03230928020a060c0303140f01050f0f040203010b040302180601023409050103060c0903020a09 68
    0x2041c20044c8401c141a004e500721a10135a0407004211484004820b00d60850b80a0b5179518410041c40da2404803944d00600d1a0485102c6607409010320300b03024001e800074140c40e520880282c0b61514100d25400c84140d559400709510600340560a40c140e4070000005401403039055045209082a04040c1d180070502002c00024103200000f41b1103484c0c0c540d104090001507140c1c1c0303030034080e1000d00f0850000d07002d0f98031015503000041c0600fa08026031551b00e032a12660b049101001a1039000101b0080c1c49a02140210341d00191140400d0b506104601004415651007401424000318400c0220414019580034a0034a0b502905541c1c5e10105049402001403055503a503841d0340c1ca100d1076400910040303010340c4004850801e46240c0c10141c0b48900010303402420784803c004d004080141c10703003101101082145c0c92061103280790520340c0c0f000e0301540c0804140340d40b451500310210f80c40420000708000041c4030500042e41d03040316800888030a0b00c3d0101d01502500513203012070f00941c41 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 607514100 1250 607512850 607512877
    0xc0f080a1101050a090308060121020708120c0c0d0e130c030f0f02030c030c1b010603050307031715060a030b0303131a0307170417070c140a23030102 66
    0x90044600c0e0707210304508086181c540003440551640c00f1050305941300c0b408003c01140240c00001c3ca2544104c00321780d010380400d0240301c0103d21840d10311003268817008003a0b4100500080c00030354604412880e42d04090031105d8039103000c003280555912a0413010820341041090000c120a540d1032031844480108034031020400c1c507034003110180052403036181c41e04c03816041134410b03036400540d8401c3d684180f405050440c6140d546d4103c2d00f43d030390700c890f8032421140c0d8903611240703100d0424850706024501c1100110313680c142d2800c000d095103200072003400d91a001d44041190101c4601c1f00b91002040039612243c40e055103180a901500c02100b0f010b406100c04112319400e1465040c0c3e2004aa0701c413904513a91140b046514079192100b114058042806c800c500301a8001800f00e20751b11600034070241b02d00419105400c001e40d07110300300170f5414100c040e03424840c1507044500711142185c122204144035240c51004144081c1c000428800c41c5c151031440115500e0030340488000e55020030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 607515350 1250 607514100 607514107
    0x80f0a0e1c0201020601051014090301021605010c090b03040f02010309060b030a03021c17041202100c0e18160c06180b0106020d03060b0906220b120a0c0f0c0f08 71
    0x1e60a104014a0000582c0144100000043c007410801180d0390848025074488541925a43c65500303154008801c0c2d5401d9035003045441c1c0c10304000c1e034644481500c00d500100e00180180f00c000c04281c00c50700800030408041051100081480c040138440d60360a08000c55075141e1400c00e8402401494030260300f40c004d10311b0880c03c256000c0740e11140007512052107403440065103800c0700d001034040710f0601170b1104200030034007141a006024020608502c1102c080e101481c00d01c0c008d07692a2000e5102081c0032040ba51074500e440f08a43c000a200c6045680c943c3c84c2c40a9803646020704a5401303424040c4030039001c0184545500013406141100f01c01c0034242c450380c90040d00d007220900c900e60040c00303404a0600c42900c01d00448086540303405000b420b00c6a010f04102c06540040c00210751314007400c001c0315900b011205608010598000540d0b1034595502201c6c02c000ca00030071a290391850600c0c455121500990b001c0c0c10b031001c51812a83c240035620303003d080d01034002805000b207640031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 607516600 1250 607515350 607515379
    0x1020c0d1704020d020607050a06060603020711090c0301090e0a0614040507090908041a0c07060e040605182d1918050601061202091305010e06010c080f0a0e 69
    0xc804020890994031400c0c6240d0400e039518192205590007540301c1040746051016160100180c141c1c0c0f80070300281c40200390340d90344010444030258000008a90042002400c0c0b24002c500a004040107a0341140240f034000101c0003903120500038541c1c03403541e411144800c00002c024102d103441e41308104000b50108265000ca042c002168129181e1140750400700d401c541d0b40c007505101680c8041d4140c1000c2c1000c642c80000c0811030801340082c681400303080da4401041041d10010000ca4807003036503020607803040c002680e070a0b8002c41d000318052016900c002203030358031459001d181c0b190241803a8036050409038020501e80030708000c031120751081c0b1403202d0a041d03424103108d82811302003107201c10000e40c5007504240108082c019810480041041c1e40c0960f11140d48424a0300b4014502240703400012074146d00700e01c004207895502c1d4014005000440d850a0300841d00b420070307030400e44c6c45580f441001d01c19200c03041c40c44036010482c0c0915a004584040354220000c2611151741180c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 607517850 1250 607516600 607516603
    0xd050c0102070c231504260123070e0310020a0302090d08130f0302010c1104060b0a050c0d020613082506020309010f1a04110f0406020706090b121501090801020c 71
    0x301d400b13090741c0c0803000c4280c01440c25412860210760070401c4a418985003514038629009040c0140b06505101940b2424000081c406c04850620400082802d0603011400700032502d4014078100070301c00040c4046519540c001404003100680240140e9a1485d05108802900032200b0841d009401241e00c001008169009880c4c40d80d445900c4400305030b915003d0342003c003020b10011b40800d01d84c6000340c001c500481d40704d40d0b00c1d80c0c0180011903100c2d03070351098030045d900011042c400a41c0116124041c200c0c203200002e424150741c80201081d04003201402480c000d0140010200c1800240b001546004031609a4812101c0c6040c441800110f040100281d40101c17050380c80f43d441c249001e841300c0c4481c81110024081400c1601c2c20710b03041e00c00c1c40300500800c882c2009414003402100884220f05c030090014101c3c550181c040145001400b07071101d501e540016403001c009218030044602d803a0402d55100c040011401118004a401618007000c1600049600d500000c2c8002c0c03041d00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 607519100 1250 607517850 607517879
    0x70503040e0103140a030c26031501030501050a03120809010b0402030408090f090f01170f0d05070c060809100b0d0c0f0617010302090703020319020a0e0906060c0d050c0102070c 78
    0x1142e00d0301e84c280400d40742c9510b50301104801000303d140c400c60740001c40d0380f01d140300d42c11541c10642c0c0c1a80d00030f984482c070025007003100c607020303450117a0801c2400ca5a040c000d01b401041c0c00ea0760300f4006c601350755a000498042002c1c2c00e042181410026071890400d40214074400350140c000c55403401e003400c00e241c05038000c061050040d07a00c05250202d40c10550704061088004c008208803d03401e0504104501d40b04400001440c0b040b5110300d54081002c2c0b100d00e0342d2042603100c41d13a035044c0034a4425840006070344410103201421041003002e44001c07074800d6040d400700e6800140e0014400010f1022a001140034000100c100c8000c9104111548000142c807059241c207450a1001030901a5400d02400025000001e82e004102c0640c0aa0003550f01b01d107071415261070780b0003290400000c80e081016141e000903410070045440b401d245400315003123001603910502d015900701e0720544d2a5508000081007141c0004c0410003954298180c460341030f0300691b040d030303003036a43d124001c0c2c0e0700c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 607520350 1250 607519100 607519103
    0x10e010e01080339030d05040c05060412110a080616030f090317060d08030a09020405010905151908031c060501050c100903050714010e060c090d0206030606070503040e0103 76
    0x1400c8100100d004403002042d00c02080188402c1a201041640481550844030b0f00c1d40200c56901000f15540e00b4044c0f01400b6840a4040006020302e800d00b041d180b0242035034030407401031004210500c8101c921003448614160405510703101d06204c0f80114041500030f81c8183c60900030391003400000340c015500b030540c80807036540030701484405401803000c441941c1e4004010542e18170002003010b1804c00e01e264000d8001304100c612600c0c58031200c5095004440c4482a981d0b41c3d2060421860144102409080b60390810481403a0441003101c141c260b100f0864850421880612100040d010ba0100508111000d5139141c040e000d083d60280401180044201410a0b0380407486e03512a200b0b0701c076a032902e5001010380d02d201d06038402c010001360100f070b0104902000f0308004180c0a10074488442110000000d20106101c0b4090a200d8040c0018608140400c14100156240905050102d03011240b1a6032920f50074002203a6200d41c0100515900000c240043c5120304025010304a9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 607521600 1250 607520350 607520369
    0x1e07020a1203110f0a031202040f0303051b280606030203030c010e01421d01051003060503031b1c0e12030a020613080714010204141f26010e01 63
    0x44862503c090f44580d00710600c0d181c1c80e0300c550740f0000824031500b007003810740212110061070702d510743e5900700ca001c0c03081d0826030224500054001152042d481c0840a2820110103042c03401107807052042062042400780f5101c5200c2c1c1c884405100c220f5101e0001958010116a0b641c1c3c0040c800c41d000c0e18590108007900c0d40b81c00206d5078040200300f250020500d800000c4284414124403000e590000c0303403c464080012440040b80d0300340231048a0054240e910000764080d85410100b0941e4038207000c42000b0581404401c0002e03442c004140c0e045020080081d0300e00f01c4403102c9035841d0041c1c960070704207484840d08034200300036001105001424810b54144600425006039030b9624030034a542c0300010380c007100c002200c50200a1841e200503225000c0d01e8600019a128135900024013460803007183d5000038200210a052031042e030b0200c1c030a03034151081a60603c0e4007580b0032500f01040041c0a4089030f04020345801c400d140340098010030481f10030796110090048202824041c02030314 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 607522850 1250 607521600 607521617
    0x420030a030e100503130f0516030813061803150b220b1206070e060903010f05060901090c0507060f0219030605010e010801153e010c0806061e07020a1203 68
    0xc0903c10400c482c401d610079804001054407aa403400554890317000182d030345000741840c408209000d103100c0d1727000754051500725855100620003111540c102c1d80c4a4814462070b03810f41d0100c11107450240c070031280c0017016800750101c0400c1c428080c1040e03d4080360f00c12203920b440e8212058202180842c080c50780000c001100c00c903801d000410248103844042548079034000754841c0e00c81e0306401688440501020706048404020a081d5100b10000c090160b0302d50040001c0703410f10b40b00960040000f03810900c0340c61703030400b0040c1c0b01d881b400c00c014158036106c484441c0f07a12000e804417012864150b0185042d0b0001d050000c006112600400c1d0008074001c542458035807184000505903034180b00c80d500c1540888606944e16456400141d0002c042c2000c0404d10101c081011510209511682204142071080c843d003111880c13207904040c0031a4005001044d01d5280c10342d80c6d218002480c3c01250a58829006100d00411000950110030440003040043d040b880320312046101e40c44e00100b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 607524100 1250 607522850 607522879
    0xc07050a0501140f0d0203040506040b0f0610121d0604060c080105150a030908040f0819050601050108250302071a01150c150501030804030c0602070503060420030a030e 74
    0x300103058440c060000c1e07803203c500d103082d03807020004120040d10613a580d4540001400c207035082e03030011035003502d294101c0d404100c148860840c4403640542412114419844e048000950001074500c6040800124081c0d020040741c2c00d520201d030002080d2401036883c191000300310303070b0344604803011102c1a00707040918125901074031415040c0e40000b0940d00c42881710514201c09500803809800415403180ca0610105070070b003005002929071140d10301021403c00b04010b2030680440030300b14a1042d205490b02c0455000f04489043d91402d2901150720740303461650b98041100721000c3c0c907000341c000502c462200e4040e4000c0081520450043d50031084024414400c80001d22600404540d6000020091071140030002c58080c414941c0b03000b51007030700b1580b20490300c00346c10407103061b500002c09000b4008039068600082503e8030090020a003031030b0129403a000050002042c80b001030415400343c21103070b410f038581100b01808031030204085090040000c15941e000c1402009900e80703510 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 607525350 1250 607524100 607524109
    0x4060e07032c010501082b2601090c110c030703030f0903050d05040609120b06041d03040b120c071a040c17010609060815190b0d060207050607030504050a0b22080c0705 74
    0x80c0465403500039031f030030111010140c400c02203194001c0d00f01d050000380f11403018180351001d400381c28014000a1100d80500000e00f90b8038030449220f00507801228400d60b0365800248250030b81303a0510b011021040c40d00c0f4280c5180780d15800041c254050500800755155002000d002190700d81d5032020a90741d40c6c5c0852044945085801a06080d4007100085079824550008a1101660418003445840c1d8400325402e50700a60400440c82c480000c0c035200350300c1c54407541c54000106c241d01d24500350031075460070b0b0813070000041040c00008410001d421302c00f110743c034403005084180200441008544403c0e009000b035020b4515502d2400c3c80c0454001000211003900c512807840c824619124000d181d415900e42c2c000c00c0d0699511594170800721f4550300060408103102c0c6401503100c90340340c40c0050034080c0003010503080602e484100800304030009a44c4025070303040f60b04e5017225202c1e40c480405d98a00d0b44441c0b50b440040a462604000c822002028042e242c401030f2880c1e580c40b0301c01c20 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 607526600 1250 607525350 607525393
    0x40921080709082512110405010b03090304090509150a09150c1403060303041505030a0b10080f07120501140a09060605250f11040b04060e07032c01050108 68
    0x454a07900c06200000b068400204414079410801138014038103589030505840101111001c98010700f5032411705e01c090074907000716405403d224a0241c1586081c0052950301d0040b8401c0154082e128408220a000b05201d0f0291244040406410510b0161050304c09031001c1003049685129a071080d0b001000b00c4d03c10040c18007203d0f42c1c0d000c090780d0405d6000c50503810241500758076000420000a1550400c0034142d503014554540d0390300da250125014049030726030981540500b8000702c1c01107100d0360007074100c1c0c0c0c070040119081c00c4540307820000301c46000c268103452210900c0c101c00420781d48003015890242d804211100002d80b620345500400b9030f5010b00c07035140400d070180328103000c05440440d40820f00e010010000b01c1d2242c16251601c402424080070b0b0740d81c90112144030100d0410f40924020244d0580707040c0440d0f450b0108400c5460340003040102055990803d060300607203503841810130310b0ba41420f140a0081c4210115008140078401c0c03040a11408403a44246010343c0000f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 607527850 1250 607526600 607526609
    0xc0a0311033903280c050d09020f19060908030906040e0a020706090804080c1206070f0c05010501141503071d0604050301020c0f07063209030a030c030906091211040921080709 77
    0xb02414110b1f0f4818000140562002c100c0e40030800c00003e03900c03510303108240240c2c8200764000003582e915002016040780e0709030f00600180e0303308101d80507043d221242101c08071403070f0025050440d6542d00000c0b0081c01055001454541044c1e10402407202c0d0714050001e407410181a600c0b040c0c460010091501c520389250300103904000001091a40500b00502d0286540d003041040f00005a549608540090300700c0d04100721407408950741c40c204002120802500000b0031455030810540281422101c68602e45040050510503012500d0f01410b85c3c2c000c0001070000d6442d041080304490f2a0350000b11400b4191145800000f03075144204c245240140c04c207400003a804116640c6405c244104146855400c602000350161a880402192014a0090b81d03407a0104c969480c0080c04444240e1000081111041080c4a901d14400e5411201944108984090707000d03600800c2c0940f200300310107044090340b203440d0f5110a05462a204d043c0742103650b258110b50fa03164090310303410a24000d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 607529100 1250 607527850 607527857
    0xf18021b0726100504030e030d030504031b031709120a0c0209062205100f2c190b0a03020d03050403050601060306060804030c0302070302090c0a0311033903280c 71
    0x1032080c07843e4402c0d4082c83d0807038085d242ca41600213555001c20b14103030707100760003c00095641c2c04000034185d00aa80b940c81c000702d040b01034051091a00d0040028070b484503010f21041c9800080388000030b040003208141c400c003d412984818961001504548005509a00030502000011f059188c100c0410918022481d124162020a03100030002000000d045040d03a094074000814a000d21740c084400a020243d004414880c0403e000d420005a19404a2240c1620010311164504407005c1d132380403403482440001c14140700300010715900301d02d9201030340250600c50a841490703409001813040d2401041207aa050742c0e9082d04804441c01d81c42400c0000e002c075008600040c3c415206810750034028070440b080f040d102d400084003a10195108c80e082c03c070009000304145d4042c0544c0e40700840c3c82d98010b04500d8107802e104841ca0840032a595110301042e09064103000380c1d8244800104080d46c1c1c030f030300e81c5400c0405c4003076191007803242c1c11111210320451b200340c0b80502540300420441d69 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 607530350 1250 607529100 607529113
    0x70302030a0807060b03030f0a030c080106080705210a0e0f0a0512161a15041a0108180601030309140d150506011218031106010f18021b0726 62
    0x440b982c520307420800e011070381151503001c1c0d1505954204007510301c40781c40011070b6640c4c04c1e07061806800c48071081ca10605011320600100303c855081811326600c4840c85c00c099544104034104982d541c400c000c035440b5428180d00510220b0000b40d882280514aa0404c541140b602c200e25a07944c0c0050400c001c2c01d99011aa26080e4040343c2c402528418000c40d0340c1140005003550f0b0382921081d00b0b001c03105030156060400400c040400070110049006036070402c001a085d04102a40d070740103c880a061102042c0440c000b0704c00580e006204e44086030940d00c5650b180d180003002e401c10b510a801110044400c41071307451510803100700701141d02c180c07044d20b000d103518210030203080c004140c24140010014070440f029000c0c06071805440e0b40c034a8400a034a03081c41c01411000800300c2101450303200c54010310115584c10015019111504000700704201003440d100003a01c41c043d480c031035800c20119155003566001820b1000d803a00041014940008882c05071a0342030703889503d5200e50b1182 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 607531600 1250 607530350 607530353
    0x150906160e0103110d0504380709030203061312031a010309060b0604120b0a02040608040f020301060f320109061101020f0c1e0a0305040302120c12070504050603070302030a 76
    0x151040400c601c030605020402240440c40c201a40d0400660300c0c00321a1943c04002c200b00c482600310300d4030f80e4070301d00780404a214000d0124100201656030b162640144001c910581d00480002004503401801c0710020300d030003501340c0101c010340402168130769204000740342c01c14024011002903540c0300001d2100c501c4602c00450192003406415500c465652014420036110040140098200c0903a24100300d442032914245100c001420000340718070500c01804620303031184420b0340181e0040d0f9078010303200490000a004248a41c0f0904181684510001c0d40f0082100c90403011405418031501c41101c00d1641c000c1c0b04e020240c5c2c0e49c00180381c10b905000d802d00640c0d080200e0003050000504000081030100f200e0382c40884180500c0c0e100f052880c402c4080070101c68034905543c0f014100422450f038028116001d5408020310400408200c100000c000700401e041c40302c0010040d184c41c0044040c0651104014011980110700b0000054641c1c1000101101181c2d13019005040e5842c1f10b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 607532850 1250 607531600 607531607
    0x904020108040c2411060f0402060711030a140d0815040e070b070602070c0603020f1812010c090f0e04050a1b12030801091404020a05040b0607080c15090616 69
    0x10000c461091003e039002c1440094812402d55000c41c1441250800c0341c50800640428841030280ca25035002c2001c0011540c0201c01060700301c1d606a52840d00c98030107140c03e2003804ea105080b140c04d445034a0b84402400240f40c01c1955614040e0b041d202403d00e640411a60b503074044806428000051031181440e084c9903000810181c49482a5061507490b8001804207520902c026284250041084000d220719a80000024200c40c00c0461606903412300b54145406040300d00042601e00d84081d18598903440c0210b0792040c110382c000c100840702e1103000f50000540c1e028000e1022604640070071850680c00c030441c0a240c0001c02044a608156600344c10704002c800590000c180305000040d9101582c40c1809941b40f00380c403154450b40c10a05c0c3c0703404494000e02d200c1544002c0100784405601d403a400c450944400342c8002c0340d00d614803008182144244c03030b00245100d60005650502103070114a0000c86103403458004d59a80329802c0701c95648009880b241d110413906820301940350301 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 607534100 1250 607532850 607532867
    0x506030c10050d0515121504020607020a2601050606040501050d0f09020904030309201c06020f0706020301090c0f17060a0b0c0f011d0d081e090a0b130209040201 71
    0x2081c50b0007031406028000c08001e0f5a000c3d50300d030301520a10f060310304140c03414800b0b102e00960a44020041c8156a000c00c400305080900083d0055000040500564840f000c2d40b80107001c8160000a4243d150810320566034403000018443c0d51804004c5045450b00408036000c07102c05958181c03c10790240641c0c001010211074902100d5600d007003500041e1260542180714600980300002d2181c140d00700f28070b0b07415800360841c40d29107200000c03203003582c0c41504810900c00c1710503c2c105a102e5500c0e08500a108248041c0c03441407000c00c1791390802074907030021410382c1c21503801446029281d41d41a1101581541d110000c580c0140140c400c1e0400114400e50020004084034105540d03422011126401010031030010303000144c0080c0b000000340600c0d0803011000d489011500504072602e51990b00c2c6100f56020018a48040350107041c15441100041c4900001c100c20350030304002ca04d0340c5039500501180e07810b4107c0c00060a0204144040d4601a006400420540e0301d030b600440d58802c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 607535350 1250 607534100 607534129
    0x130501030e0c040509030a020601080105011a03070e090901020a183f080a030c09060f030e010b0301020f0a090e13030305040303020c0709060f0503010e030d020f0418020304150506030c 81
    0x72403070b14121400d03569805544d0081c10780c0c2c1e0140d591642c2c900380090805c10143c0107000c2d0b0340c2c100001001241142d50101c404c903031400b1007854890300d45c41c0c01242c418554450f01c51388501d60f00b0a01040d048194000c00f000e0103591160048400c0c640c03007e030316424103441270381c13250030909407006021000d20070061a0400a0030310300303000051041442e0400c0720407044c1546c055a0100718211141e80503c2034011a16203800c100e04480d2800c58000c01e54031100903184105a10740d418101400c1007500130450f0824014000e44d12805c0100300d4148a401c80094540021003402c0c002511804040780e15010310114041c51140c00c0b8561070640140c1800381080f8200740d402c0026241d581f009103c1e55001c0d040192020036001d1411144120030b410a0304501d10991402c0120016108008101c440900080202507125812082040400d000b60351110b00e070b45400e10042d042060030381e801544a0351103403032009021000c400e450412070394101c0e0300035010350116910620510b009003820340c603039 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 607536600 1250 607535350 607535353
    0x1260a0204180c0e0a0e150c0a09080304031b0515180105090d1202061e010302040b1507080306010305070c020906041508010c020f0f0105090718090812040c060302130501030e 77
    0x80006950300040d485213607208040c941d04140901181580500462000a040b94002c01c40700d50040f0840c00c3c003402c05000030001c090009030b0750f985540200e190030018070a1606598a850b07582c00d00c04003003c0c0860034925440200d100124161910f00703c004000220300080c2c600300400c2580840d02c1c90b1244030310754103000c2c4c01d101821540d500c840391034a03035910400d55104034085d418070280ca0900090070307140c410050f81c00c080e07082c12801d006003030440740c0444021a980d60100007040a07002503558845440070300107280d50910410300000e42c005c440a0340c0811042d139030b0360021030741c030401c240001790b01440e4000491b44610b420b8201d90b070510302400f00ca0090300d41e5119070500b116100d5034100b01503000704108100c6280184024106250250001e020300d152001400b525400f9500070f4101d2542628810145111943d00184c01c5547c84111259201c265180e1074500c007100304d500b11030f0300740038034800315a00e4424000c1d0703041401044000d91007a4100300c0190045c181d006001d8005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 607537850 1250 607536600 607536641
    0x191503080f13120b07080705071b0302091e1f03150605031c0305060a0b03010b0304050a0503180f1801092f040303140f0a0c0204150303020601260a0204 67
    0xc1e030380c8601c0107000700f018140b01100000f6502d061001d8a00007001d07803060090040400aa0a411904503201c0540c03010f8105140c502c6110b41200c400182d0b00b0103904444205c00b0890b13400181d48401e030368014032400f0064107030303124500003100c460503482c035070b07101e10b0030810401c0000c03400c4c0c0381d080b281c050106002c070b00b031078550780802c0c0f41039010504008000c0c460104400c0c19501480f03031070b8005905640c0c1c801c40ca800c00c8180c1d11684030603c252001004004005003c2c0701050210030100c550150980e0f1b90b4503a032001c031701a4002401a170358841c0b203180c8000482031500080c0011940000c40308400242e00c1c1507100c3c2c006000289008002011000300b0700013017120f0180700c0b044c0c0d10381019055215030450900805070420210481c616100400080b2408002ea00503500840c140e07140c241d0341640740d84042000341c01040081103c0c6061540003004160f001701d1014181d0700c00b003041c06070316060b1310460000802401410000c64025524050242c00d280d0040c1c081d00080c4d0000014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 607539100 1250 607537850 607537867
    0x609030c02120133060c020a0b130e07020303100e18012307020d0905130605030d1e0302180d050a050607050901030b0a080d18090f05191503080f 64
    0xb40024810350400c8641d550f8859581850034900c0440d90b0070140d005901c2c10111164200f0f000204280941c8040c4841c040f41c45086645101401c2d01401c10f4000141e2113103045003a81000f0780c803500a8030011510900000c54961000080d203119110b840c05c02641a49000c0345258405c5019228071680c55224614005060090058210480c0e410340c04176803111080000d2050044050038030406c6401402c0d002607000c2e4810410015180300300d5120900c82c500001007401040b07240e20080c1c050090fa0b240d80512500103520f507840340512103c00540c05004942103042384105a03c00c0e0002e0341c03084c0466000e046c8a030310303c02d4407807003041101c8101081b034440c82e01e0100101c849800160f00011405003950303043c0a040c58a04083c1c440c03450341401c007082c0303503101c0b0b40c41c040e01810020700b1000f86ca120740200d0700240003410f080c0c204101d030180c1012a0350243c00e046070913002420051041d501040c020344a03030965001602c0a08400c0390841c2e458100d658441009038241c08028060f000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 607540350 1250 607539100 607539109
    0x14031c1d15121506071203020c0c0d030f08010902040b04030f022e020705010305071205040c0302100f0815030d081e01140310060501050a050a050409050403030e15040f0609030c02 79
    0x6014900400700000358075040381042d55010010003203a004100a201a500140c80204100c0d030320809807c0c0561102c0310704156600c2c09080c000c83c00d070b101c10219481c406040e013003030800940e16555614001fa030781e282e855800c140c2c4114490708032880820881000810b14410007070b40007d10081014081d0440030140c8003070010b502078505540c03008540f0306a0304580400000b0000c21003070809200c985000718024000c1c0c010301072401030b5151160300007400c22203042c821002a550080ca122014856a94020304a40310030b004440443d44120108880d0341d4010f44030386841c40010018110014014402c60381c90f10050a00d0340130100d40c10a426000c03000c0c4046074007803c80c182821103018188010140741c00110b41c400318a444c6055000e10007641e200c0202c4d091480c07141045a59101c49440448241c410740d40305d280b04520b40001d0000b010f915400000c801c49500e011a42c01d06400a00311231b0020040d00e0040c00c01d80580740402c0090303d0342c0c00103c0702174020f050010042c4616000305e03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 607541600 1250 607540350 607540357
    0xb0402090a0f1503090206043b070219050c010f090b030420011b03081003080c0c0307050616060b1c1b12170d1514031c1d15 55
    0x1d0140140c00b4400d006407107910b00c420071030004070704d801d001288054000c00c00c9032169001d0014502c0f60342d6030316407150498660040d4000d140c481c03105080024606000f032544c40c140c0b01ca000500558041448030f180c070303141d0501c0940c0c001c0e0140820258074001500d05c0446c110850090000070003002440038182c1703014501ca24002c40c0000d0305148164a094203500d082d0000d24144504007407107800302400d0088010a0301d40c5070400c0040c6403144601e41d00c600030250301c0102000700001e2070010017030001c5590140584282e0071070701025150307010441d4500900020459009540c10560007281058000e07068401000d80f4028074070f04008664a86511140030a40341980602e02000d030000721010706400811801c401580c01400f280d03540070002004a0300c01408200c0440e82d030943c0075061748408002c00b0101c1030b140120703a54a00840714203d440220a20031302070301c007030859400301c91200b20300c94440e290342e0490103001c600c1070032845c102251055a0002841c081d9140030100c514000d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 607542850 1250 607541600 607541609
    0xa150203071a0c0d0902060c07120c2903041b06081017070302010810050405130c0e0f04150b090126030c03090d110a06080103052b030b0402090a 64
    0x355a540c540c0b4100485968100101d482c0c40d0700003074081090500401081e5664440e0010002c00c602401d0300026031140508a072441c0719024107540080d0340c044048150010900c030300181d44d4043e5440c5008100040c1405000d030350742c400b00d01c035501da10344800010760b801131044e80c16800d40159035050a00c084141d8101d800030880d000305100032001000c420310020b106014041c0e03213940050300384540311906440024140640a0040741090306052900c0002d4031002d4800c226619002402e1a0f03203c40c3c0350000da030019400140820140700b402070140c802c58135032040c1983c680f40c9543c1d02c00e0401c844105808880d0b03403441300c1000c69441d4103245000704440c4246175060a030309100b8104c145500114221154801c00444641c100040191011940205c45019a100303c0d400e020500b52041c5424a5020392742c44004104240c108000e07a05984c0543c0c101c4040c40d030003020851544200107001020b842c000e00e500030b1640c0c80f0350003400032120090000b504041400002c03503103400c440d820 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 607544100 1250 607542850 607542853
    0x8010b010813030903050709050702010b03010b130b1c0501020a0f020d02060103110103020c0d0210140412030513050106120309080109050c040213170a0209090a0c0302061305192108040902090a1502 87
    0x500c080d1301d40c24094031090137030807402008401f035010001202200401d400041d000d407550002c44080d81d031006209412002040302125451751032600d81d00070f5002c11541400b140a1000380088103100040314144a10503400130240d40c1d0a64688140030090030b050746040540030011524181024494404140c1441e00103141000000241006031102c00c140c407041101007000700310205110400d90820b4203400d040000f01501e441200045058940e10081e00c0f5608022000a520342600381d0b002c403050182d940e401d400350f222060242070f180b004ca4003401a901c450944046443c1c1a4000c00b2440c02d072042c01d0f42500e640d800843c1c2d001c2c1d840301ca8030415800041d00c0c01c041d03007440805180c2c0012190040d2844034120713510f482020200303001c00f90081c1070129083c01d4104500003014050301006003044000d41c00300c680d1b04101c4040e801002014200d601282c46075044003401d00d41c0f5690310607403650406040420150017500002141a44600e5120000071a81e000140c44482520b10b1f50 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 607545350 1250 607544100 607544111
    0x1050d0225050c010f020303061c140c01030b041107020f0109090c05040e070504080d0c050316142118041b1106091609021305060412030908010b010813030903050709 73
    0x28414100300b01e03c003955042c0308000c62118880f66001c0100ca0f4840700403151141c4401d0201a44d07034149052501c010401c1308501e0f0b29803102070b400102800c1c2a2400d03a0184003001002007444280d918208101201100a0003218010324056500030f445541c10301d00440420b54a03d4400151655102c07a0b20200e800041c1c01d008400700d103640c1c3c036801041414058a46440c0901e007546c1d5140d4070300303140c2c01c021a546082d001c2120034422651081d4000c4100c2070760401d2410710445020444481d04158810380e12200194420020440696446208071034240040d00021018080000d00c005500a0382d40c00c5c50070594036a0130440e6283c0074141e6031248013815101c0c0d01c41c81d09001601410440d4031200840d0600c0c480e550b0400c090b40c0c201000561075100907400b500d085517060f0002c41d804040410b0200b00048100c203680280c0d07009a9480ea280c1d80d89628003400c80700030a031454005080c910014100c072007280400c000492007480c000f540540d59481d2030f420400340d03400c07444400d0b89a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 607546600 1250 607545350 607545353
    0xe040911061812010606020607180f0f051801080c0609030f030a0507120c0512071b0305030a030c0914090402130507030b1807020a06110903010e0c010201200901050d0225 75
    0x2405200300360f04500003003203c2410620042c0d0384010080c032600030085000c0701110407100549a83e0001c10141e0b00001245480e0003540c446810180582b5000380c4c07400500b900c07080f038070300100c1d4101e41c1c580e0090b018890380c0e00c0901200ba8408200c40780c1502c00c1c40244810b8107010401400300d4a001d0b990075032650128a05207643c2c200d01c00d10082001400401a004150017052000380c0030943d41d070071981d80c1c1680c5060395840b49510851001c1c4180004000140480480107100002c22030b501040310340c40c4000309a481e5881402100c500d07000c1c61f006070760036042c045a2190841d00040044e04942e008400f0300c1d041d54011560341d00000d480d5001c444036030918a5000c0e490341780075100a1820300e0401c200030755440c819032001d41110b44420504000d5032080c811910408400340080c400100300701d100503a04c0010103010782c0190f03e001c1642130b0b401200f00f900750341100c04c1060b1a14240301d00c401115142c100d56020385055500700112908a41c0100c81d514200d0b9031980c424103801260b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 607547850 1250 607546600 607546609
    0x51618180903271401090302030d0915210207060b0a030c050405010609141018030f14161401030f02041401020c100905010305150d081b0d0e0409110618 67
    0x141d40034108003007549084005a504003801c0c00c4184c807080034681c41c180d91000012202201d1075030000e5003500039110782e5104203034400c02c40c070140c1c0d124008600d19150b41034021108850101c820702c0603410000d0b07140c05400403580042c880c1c90701401011818159400003d1280a13665000b143e56885104042002e070405018550040c00c0ca400c2042e41245803115624280284070039103807182151038031a40d01c05003d00828810070100b8419001c00540ba8900010b10041d40c90040e1400203145100c40344003d8009200300640301005403060000e458452410b6100701b040780014141501c0704a207080c4140d00348040c1c0014030301c140340c45003010420800642454088038040b8015a03441000c4030107170350001e41c2d1504943e0701b03180021302c42d5600c6800080bc0c5420843d541d46c020541913000050292035406015008018040900010703500700281d5175421002c60700a0116650380d80c804420300c0c01e540480c5946014081c0d0201541000000a01a03480322404007440f05861544039000d041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 607549100 1250 607547850 607547867
    0x706021e12030c07050f190203190201020c0d2a06080a06061d0301020d0c0203030709140108070e010309060c0801260a06020a021f1a04051618180903 66
    0x5600c00640303580441100e8444052200800401e2050000a0a0801c0110030000041d000900105441a50a0451840e00311035070840c0283d100b80705801210208502400d06041e40c26416001011128102010722040c501e080a050344c0318401000c0c1040c1c098803030078203070f41e407980d5201c0303644d0800e414114080c280090141000c0300d807500d403043c14001546c1010b096041851800e040d101c0c00840c00002a001e881049000c14949042c41c80e1a00343c2c44d0000045d6003da0300c1038541d40c0c00251a58000c248000d10b003403460740001d43c0c05010801d200d004540e60b2000700e0381890041841251500c03500309581d80c00003a40f0004200e0001000801c1040300084407401399401c00107910391b41e0440140c1d0340c0c00f1011024000c0703640060b805003c18000c02000d4100741468125045410404481c98005c081071001c00a596500c0d51a26003030345000d2090511170075040800c5c40d01c10f160305404641542100390342c102040c20050703001c46c0d002921001d080d41c28100d80d001003041400f40c07400800300031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 607550350 1250 607549100 607549153
    0x4031401181709060f2a0c09100e10030b0709060c0b0709030f06050906160f0e010207090f050105030f07050603011509030b2403060702071a0c070602 66
    0x74908140481400041c034001449260482c40102c20b40d260b0058160180c030400c4090383d4400e0380060300076407129100c40641090b9011209a81c2500312141042c20041d0152091150a81000b40078a029150035100681c0041955150301075084d1141e400000c0381c1e00c15030703003071741e01c4100b6000c02c00400100100e0540d20009501e841c0d01d40310b160040240000b5141c1200401010301c1400240d4058815603090300195008000c600510b04903040c44c000409040ea0306c0b04090281200041412804c0c0b01c5c1846000c2007035075042012110b05100311441c80700904004e0450182240003d4103800030b0040181c00c001d0a000015254509420189400e840603a45034441c4c01c078000400c175a80c0c0d45415681119194280000c09a0b84a103044451036030940000341510f0304075060004c142000d01b10003600e1044a41d000051607110402c00d552413031300315060350050303010003818071800d40c540090304009124880c901703007404a88030341d1604041d482e03003201006178001500190360181c01780c0054003c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 607551600 1250 607550350 607550353
    0x120608010c0f030504080f1c0e01092d02030616021506061b070f0b0a1710090207050102190e012622020a060807260f07020304030c0605040314 63
    0x36088800081d20300300300d0080100503d03550754001400d010480c82110300c030b0280c4140b4140d403900541d620000c5920312404090900e0b1420b1000000c090051061200c600d41100c075200c8140c44141c42d00c02c41d00100012050304d60316036802400103031010010a030003100d000034560080a101d01c0001c0c50070b00c2030309542d880003c200f01400481d44070441254008244030500c0c1d903905500342c10441c90028a58800d500034402d000c1c00041c42c201000c0034114503096551059180007100751130100c50042940c3d0a56084400d030f60401003d8541e6005100c101c1c0301c2c07000981044030500d0034021103040403075080d0106004a043c07642960b44030041041003c0000d005100c400f000300c0e600c4d0754440380101895418001000c1d403041040104c0f07190802c0705d41c001c0c4080d540070b1306c4020041507200180d0328a0041481c41030b4500d007401000d4910003d5680c810001c0c12965640e1802402e809406030404056000401c000f02c081044281c1e40e02c007070207240d00c4540d07403140b8500e032000d4108140c040c407400d513 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 607552850 1250 607551600 607551611
    0x109140111070807020f12031215062b0902041505030d020a0b071d0301021809060d020102030f130503070e041106070308160504090e0a0c0e06101202070c030312060801 74
    0x100f5440070341c0d10603501a640c8004101c02040030030701114210b0034200081c84082800304140d0300900c80349106402c00180208036041290074005180942d010542e50754010181c2ca07090381d0840750014103d4401e000003c224003106402090440310700c0b048442091f10070030814001070404000c10314611040784000d003e40441ca44954940c039101034a4102002556003445e09030b500e1002812001d404000c0c0210b666801180e80c01606015015949004041c104009201454115500e110898040c0c02642c07501d55074081c0c14050323900c420f01200b03500441d0700300418161420015240a04540c140076100da09050405001c1c928199010030301c01d1034200b2011001a90111045400140407003c150180084c940140c07600e0281c0d4001181c458a003042c1014a0b4200040440784140180000c200b0542c403400c01c041c401200f118050741095655055012040c480c06290304281000c0c280142012510341d944450b0595a42c020b0700013919010380e144910b0802c0c85880002d040c0350008001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 607553956 1106 607552850 607552853
    0x4050c12030c0c0105041d2715150607110120010915050c04050d03030609060b0304110d050606100c02040c02030316030b090c0c0f010914011107 64
    0x92510a0310f00d40d00f81c5500980860301030b12003182c8444880624130700210300811001e00340c00105103003005030440b810114440368482c500c1d0400508801d071000501c41d8100003020b01262505141541aa40255115412030702c916600001c100d005021b9800141d4890000d040701180100c084038080c0c0c02c0105c1903005400700c0d8442c01321380702098030b000004000c0700c0c42122803840d039040c100b2041c4668600705c4201d400300c03803180c507011a440b03460703c8140090704d01c00c0d8480c0b6811800841407108000300703800c6500d100c203401d0b5400041451a0740343c0a9590320058030b618060a643c1c4000c5030445e02c90100ba4148a4002d0418031060140b884000d5580d402206d001da141e14036405036101e0107110303009800340118001c01035019600c42641100299010000020440c820744400c00345408082c017842c406a030141028a401d800d00410840c00e40d0703850f80764a0a40f182c108500c10 = true := by decide +kernel

theorem cover : BRFrame.Cov 607374100 607553956 := by
  have h0 := BRFrame.cov_init 607374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 607374100 ≤ n) (h2 : n < 607553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
