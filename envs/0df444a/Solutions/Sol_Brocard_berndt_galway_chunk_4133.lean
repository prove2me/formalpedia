-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4133
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:39:52.438788+00:00
-- url     : https://prove2.me/submissions/3f4f1d19-26ce-4f92-8b5d-556972f10877

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 743165467 ≤ n < 743345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 743166717 1250 743165467 743165509
    0x10302101103191701050105030403120905120309160503210d062d080d050703020114040302070f05030304031a040c031403030412050a090306180b0f011a280e 70
    0x401801c0100a400440d40401e8072841c0c0500401503030b60440c09270382c0c201e07a060500c0c80762820a01d00c200010154200c0c0600184100e140751a202010000110701600041c8240d905100c0b13940d480310040c016900c0b41c00d40603404842102c14104a44890031880b00030000100d02d416101c0201c041070350b42d990405200e1450307190391140307944580002d841200c101c8400d0004010315110f8080e0720b40d24900402030601c500001e015080510030360050f181c80c040045000d00d94207040c00d00030f43c2c8440c039000d0901c003094107803004502e91030004144ca080720b501c00c20404c5103001541d00305184c54000f9004a601805070540440011656101d00f925842220019030b201d1410f820081400562101c0c0b0f4028884200407410045070b00c04400790580350045404103500450002894032009503e44c05004942100244040007415411881c12280c2d4803241c06042e54440c00104040c2c8268801c5050404000a001c141514420041c500450340c40c1040143c0350340003404100e043d100c0100704100d0704 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 743167967 1250 743166717 743166757
    0x12051f0b0a051b06090c0915010c020d140c0108010f0f0306020f070209090a0204150305150603100f0e1b010504180609050c12070e0f0103020705010e01020a0c05010605010503040b010302101103 85
    0x2006c12652200b040f0485282e5401d081c0a5002d080740f00c010003c0c0740c10002e811050b413040d901c56801410120358050304600c00e01d60b0208020f91907092154880e40016480c03000064400d44158020041ea003070900071400d42461541d0710b8000307500c030442c10743d000c0d0340a00810015a5400c41241c2c4506902c8015202d94031080c030400c4221299000c400c151356032064030501c00b061700060404034000b0f004096007038580340d90001071714005082010540481c1001c10041c140790f00d0342c105045142520080b110100101da0240790703c0307154031110600080e03081c0030811080c6160700c1d80b1010807040b2040028580e880c4d6049000f5114200d858041c031281c00203004403400030415902e64000a6480d02c541101044400100f8400100071101c0c101500401d264081c0f100a5000f8107101c40804001c5503200503180c5d01401d901c0e0008803e482d0380d440e018000615501a2003142d204551101542c0a41ea09643c00c00c9540544149030302c04010f014140921150b60401c000c040e070f0201c4020045d494 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 743169217 1250 743167967 743167981
    0x18150a0f0201061d010302010804050c0907030b010e090408160f060504350f0d0204050a1e23060c1c0810090603020607060507180612051f0b0a051b06 66
    0x154403982c0c0721a5208016440301610f561301c02075101d05403542441d1601c2c0a880714146a440d00a11284c6203a000644405000040c0e405d50300480d959a420b03280c480c0d490400c40c0400003802400c503805000700d02e081001340320781c0ca03941e80b0042803203224510b0800d0449241c0c43e84c8084980071a003c69004043d091001214804040070100f4190260b44031540300700c0070644011140600f03075003580424408550441c540c40c46030152006840d0142c000e0f003419aa903441206050004291040081d000c0302c070100f03800c1c984100a0826009000c101c48040040c2e1050006550000c2240206801203906075580c0c010040c1c480d250303903207440c2d44c0d1800908095210041302c15160b44030403100f0386080c078100016100c10040d591182d4008100280719602d0301c130180c0d41984800d00c0d030444480d404c10b010441c0c50700505030080c28a84034030208002c0d0785050614142c0f44000d40180703041d809101e002c01c0104600002402030384d28610b012030500c0100b0360b01c00b54407441c090385990300d80c204008100034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 743170467 1250 743169217 743169221
    0x309030c0507080c040f1b030f0204030218250219020a031e02010e2704020a051003021c09080d0507020708030705071403062703120a0504060b0a0b18150a0f0201 71
    0x6c00d1031000b00000040622170071040c900500c0110b061645802040e407680340550b068400031a00074000800d010401d1a03840c0180c001144c1d003442e00c401600181942511030003401140780308039002000300c42034045141001c40440036040ba80b00a50200200c0058808000940c00c0c1071008051801c041d02c61001605a0b000c244489004030b044c5c15800702513640b95603600d42400403600380212180c4035400480c140802a030440d6801110050301c8608441d40350f40140054054809421005001c081c00d200a03184001009440c1200a016013003850a940c1c3c80325030041c0140c0105c502460343c1d8401c90b801e54000f2001076690f500417080c200700411400b9207040710080c00f200900018035000d42c0a04499204044010141c8101c03500c2e15144001041114041c40d8450031003030262a18103000000b1700000c44c1d08031942400c2c040c4641c410309100c000d201c280c400c424202420302c40d116030041040074261000079440319100c9505a40003448200a1500030250307a11009800c82014010382 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 743171717 1250 743170467 743170481
    0x4090b010206160f0525050303010e090d050a0818071503060b0a08130515240a062007030209041b0f06050901080702030d050f01050f0f0a060309030c0507080c04 71
    0x242000f42c0fa0022401640040145503c0c501420026145c0d00c480099828103e5410301107004041050321100c184000000554100c46a10300d9440040c3e441628064483c01150305000108201b0312000c00d525019550040e44800151082006d0200c0d10304020b181003c5688205102d0f9407004a41d0f0003558140102005890b80c40d40091a14294120003001044014a10030801080380300560401406216001e000100c80c086042a4100b18111540b01d04440b03142e0b000c0584030710a140e1880c10143c0101c8100c80942d2204a10340d01030040000369258946c1010107280103003a000710050ba2504031103405175002d0940c203910b1048450003031200344090b0b001031089141006040084d0dd42c4803040b150a00c600307191402c020740312003005074a5805040e091080e42800c1070100700b20b1400d0107000c00d0488100702e0b4400300c11040d0005000c02000d12251842d00503072220340c14866640280c01c00803100b4401e1405418124032900d44900300143e641115403d0b4001e103140b0026454a809a51 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 743172967 1250 743171717 743171731
    0x30f02040e06150c250501030b030705040b060403021314070207030b04030f0302040b030a1b0516060203040807020d0c06080c120a0b03010e0a080301082e050a02090604090b010206 79
    0x14581070074208010103941004040611031089002d06021101800c0e050341c00c014412000c03941e0041101c2c07070105045426060200101c4514040060700f58802d02401c0800c14024010f0000f4909000500c00940800000103800607003c0000100585649000000200c0250030002d580da400c0f0030300c0d0000c1c1c00064800c0e021540300c4142031020600300e0017503e40050381400c1c0803801c0000d0010943c0030f07000e0380e40443d41003280842003141481041d00088003003204d14542101c1501d034458140c4150241c00100659040640c02036000144161300031900140155910341c28600a0383c006200014501000c46a2a4941404000c2c1a030060003041d00040f83d0240c450804402d90b01900c1624401000380084548403140b01145440a5018901444180e8190707441c102d00750070500ea15038820307c540d00d183e214490030050406e90460303041c10036090007050350740380c10030750401e0a020306000392070024074507400c01044402d60348150007003005200e6898085010002c48001a00b4464000c00f45 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 743174217 1250 743172967 743172971
    0xf0b0714120a0c03020a1202060a0c05040b070312140705190e0f100c0c23030304062c0406030b04110d050d03110405060703054303210606030f 63
    0x1c03000c02007410103a0301c0030519440c20183e140309900b03040b85001c610b08005032400c2590103056001079808203025100d10150032052000310305c290300407200d62003548144003401d00284402400a0f11031040e00314403203000800428101c0d907001050031440f0381510f56201091000903400c0b807081a261031038400144506152403800140c40102e090f032030464840038812000d030214801c110740118420ba402640000c01d00051a403204403280c02070740e01d56400400d40c9410b0701065401c2c0707000411242907441d40c1d601d070328100d00030b20304803103070320f8641683d60007401c001030f40c804810f40b150b20580c0011401102120154101810034081e41a804520315020320035443d130410220704000717a06440b054941c035002601800041d40c4e40c9260082d40c014550100000036000c1c1030690020180580010a048244502171018a000140680b0007604003440d5840c40d107015800d02019404081c40c0c1c042d007040e900c1781340c2594099026144458106100c00e590300414441e103903252040076040c002141381 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 743175467 1250 743174217 743174233
    0x80d0f0207060507020301140103030e030705031f1e0c09051507020109050f030717160807030309060305180a2f0d0602160f03080601121a040507090f0b0714 69
    0x100075181d1129025100500000140800440d01d00354411003080090203500d074665612890020088440309041520a00c0780e8040801c403403402040e1020705104030300c0304c5450090380d0f03103001c00a00b810482c60450000b9106101e92425581c0c0030b94492420282d071804107083c100400c005040b800042440340ca06004e228000050740c00865950a4a804507203d002204014001914208090304400204000800c2703080740728400046a143c43c03550715410b018225281d05103595101514480540060b00990042040da40207a201c943c000c00c400c100c00100d0328118011034a4003110b404201c410b1440500c0e61050640320903011005c150603080070155890043c030001e14800c00010018091f070b42d000660802d852640030840d101c0a43c441d140100142c042c0c00c002e40609000c803011404201d01e055200c07070011031482543e003000207905046051080040500000f40002400307007040c40401e44001c00e6a10f54016604024004504466518030300c034039261030342549850406d40e25500201c6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 743176717 1250 743175467 743175497
    0x209030a02040f1e1509050403022a0907110f0c03030d0b0d1a0a0f0938090309030c030c150304031403070e011e0906110f011401080d 59
    0x580400c20603012280803941e6081d031200361000308030f600b40b0142d090f44001107000e11480705400c0f80000e0400400308400e22507030b5400a40560f00111001401030f00b01c0e9805c80c0352242c136910091800843d000c510011041d4040102d0f032000f500f5110f0002294980ca90740d8840c803010003141c40a108039501034058070342c00e1800320b603490190304070403408547c03076000051003034840800000d1883c0e00300e500c0c014608e4195840b02c15030031040c0c40e8a15801e00b40000d004801344030b070280114080e403080001d00c00c1d8000c0d200703c0740521569000d180c90380c9041483d0140e1078001e101414040c60f0700c6ca0203107035031301800301c10076141000c201042030003500890700c40b062030f5407460f01131f4401948201c411a645c0d0b6680c0b8007122a00320740c41c0c141c04100c07008010300c004560702c12141c041c4000c080e02c030f124564944c500c0c0300003581c2d01c156943d00020615003050180718400c0341e032440302002041c00c0300c0d4125400e989890a440740ea50301c121070036110100400c2540c400f0880c0c0b2015046130300f00039000b2101d40d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 743177967 1250 743176717 743176723
    0xe0f01090308030c0a021009061e06030c3b091e07030303180c0602070608070c020a0b1b0708010b0a0e0915070c0501020c01060f0b210408070c080703060f020903 71
    0x78196444110b02003170301c0c0c0407140280408801c1403e0941c0401010405240900003851100000880d11100481800c44030810307208030383c180c94001c0340f16042d03146450f09100b0300c001104080700f80032590802406540d840751125005078117a900d0011040d146c0101105c3c5400a1159900c480801900c51b500795400081050001d41e5014600801c0ca0140e100080b040c00600b00d00060140d05c2443d00081c91513030108000d4181c411964501710a5124540c040350031580d0304078044d501c02c0f4290000c02001c81900000c0c000810048020185d90420400050a01025170720801090751205194101307403402d40000c0000d04880121000941011100c9642c1e0700444034075482114060742c04601154001d150701d155141e4000000d5640d4031140b480640a07241030701c58a40c404031b100302d0200780d9080c201d082d61005180000c00c0b000c402c80b110a4005101d10203442911210800c000e62001300d2051282c1e880580a48001403e03001c0c0303946000402c95001e000c0f03a034292032051002d490b40381e83c04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 743179217 1250 743177967 743177971
    0x604090201120b180103200105030628050d050a02030105010644010305030d050901020f0d050a0902120304080c010c0f0f03022b170705030708040618030e0f0109030803 74
    0x402c1c00954004001c02003075134511804010180341000708000801c202c040301024070354840d00010f0004c4d251510005550034002560710326400104c8606c030940041c1017041c81500ca400304c115941043d9034641c041a150f600044040c0d40030b400c21a661400d5040034015103004224614000310368003505021400c0364000d4464444965450301c0840d018020714500c4a4409103604190b4400b950303492030025600c0d40318a22045280e424a000106031100600c00d4414000c40305503182d140c82000382c0c400c1c3c001c2c42c1c000c02461807150741d02070311303809611603450400848031110700640d901d5042264a52501100c010098100211800701000007041585901d582c01d40c08484c2456003103003441c041c0d0808200c004000314140301c83e410b18140c04080441020200c11a2f201c50780c41c2d00c100b408420040708126100700108100f040802c2880d0f1140040340d6005006080001c1e03180d82c509038400080d60900400d60010b0b9641e440c3c610f0906c4e10040d65a2110400d0034046003903843c5588460043c040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 743180467 1250 743179217 743179247
    0xc0a05060d020409050711150c19020a0f0809090a06031112010209040f05070f0216050d020a0b0d060512010207150e0106050d05150106092106270b0604090201 70
    0x30105040300040099015900900009541405249010000208150006641c1904500c581c1039940d03602c41c0c440d4204d0b4050075520768058588aa00300c5804c019034034000c032480c00c40c41004c00210100704000c9041412034802e40c1010350315200c4404010b4040006031141d02010b1629038100f0014240d6801d2020081080d0785040051030748001e05030090282401558000d42007403984000d1038581c0d80024808c1203181c4546030400a1010b089943d4060380e4140360030308401c40d0041c8098504101c240c0040c40c4018120703180a500c96003510100d8000010300130185445503400d0025180080c400394161261340000c41c20111580c4441032035090711400340415640e80c03440020080c5081d0880c1d0007070318000e8601000c54039540340040c1d8034280b61000710381808101c000800d00c5403140c00e2035400c880481d04089191000c151760200c41c1101004102c83d0655141110b424030a05100402600318104030b04c0c0d0002801801c20900a0000404032803045281600001c0140c1c0c0082d4080c441e019 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 743181717 1250 743180467 743180479
    0x20307060f0209040914010507021203180a0c031b05010e180a0f020f19031b2105070e01020d090b04170f03030f04060c020604080403080304151d0f0c0a05 68
    0x2240d10000300003803003881d0a20344c2040c20402d194041c01001002007080c0c100c0d04000b0069640c034030f40704907141d01a5146110501000300041881920041c1c2011b20381400002551000f5980f42e4074210f000220350b004a40308441c130030180d6070071902d05090744014170007802c0c8a41143c560800040c075010707520060150100e010030105400d0540b5a20200c64607030300207811542d131111451013400a412a403551440e45d101860b200c15040d02c207001d52813401e911001082c1036139031410810b03501040403074940351007800103407406070303849403180200341c0654950307181c0c1c600e911580800203003803021408560342407098a900400210720424119011181c40c2d10601c8036844290082500f81041440c1d1091544004024055003c0321030410034080d501c149400c121075868641c6c10781c3c540c0c204480103000c0d09000d210800105040d01e0055503c40e104600c5280c1c0041c4030884c080442d256032901c0d0304150442c2c405804a20820046016040c20000050030b89502c09070004000001900403140610 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 743182967 1250 743181717 743181731
    0x30f0f090a080c0109050601120c03020904030c0204150e06030d021015080a1b08070e0109020708130e09010e120708070503130303030212130b0f0907120b0103060b03030a02030706 79
    0x14005200d180421507004140541e5500c0d5001034501818a17814190b409000751400018001034400040e2102da80c44540c05141901d140c007084440c0a00600540074000300c18505d000603034580c414039030030740c60707455060404a05120000640c00380080c203160007540080b80070b0a006400068402001301d04080c081000003c10001c5442e0f0b206031307405043d49200e059850317800c0281c8441040c003040e200c503801485d141d80d00c11001390364060034810103d6181800f40140160300c4d00741c005021190103a034207140350040e42800e103d03c841d40c0b68030074a4004042018040c51003000c1c010442d11011800041c13100b04140d29540316140709060006182180010741c4504004090060750a80713102140314040080d943c0c14003030003079485815000c0946540200182880880d07010146089400842403201030361443c003241c0c415000035000803a01d202c0c0e050700003031482080c0c81c001090740c451022030b1015407541c035107181a03034501e60119100b9041841540c0c3e13007a41c00001c0d036924640002002c00c40e8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 743184217 1250 743182967 743182981
    0x120f12050904050c09030f070b041517040b01051e091f0f0b0910110d110f01060902220509070c0303270b010f0b041205100207030c1403030f0f 63
    0x1442124551a00a41843c0402008040f01d4002d0180c00c14250709550b03052141c1c50b5050b403100e800c0d00510704003e4050005210301c08000620040d508498108018000c1d400445a8441501120100c91241402c40140001c0c1801c2c03554100a49090b40c0e00900c0720300000004400020060070010030000070180102c1e81c3c41a0001240103002d50703081c00140c580c40e070111003c103a00c40c00209016100c140203004003103110700e020080e0b207001c1d28081d011850104000300d40c2003011680c65032071441171004d100a03559081c428a0000c00c2900e600503542c110090101c1d4101c140c40540d0b0313162a0524400300445e88469000366400070241c40c0c1184c0360211490294000d04100383d0600007181e04540b100398490608803480640341c050b55803916140e81c0c0303c1c4d244000c2d00c021302404655500c1030104002003200300b507900103814030420556501c1004488001c00721381020380709500190b011a0b006041c8010244a600000003031400765246261000b88001c0f0104058024006010300c84005106 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 743185467 1250 743184217 743184227
    0x1506030307020d0b011a070c12020a0306050c042301090501050310030f0c081516030903140f04031b06050712110f010c0f1e110a170a09120f12 63
    0x40300b90300901010b030381e4400b414002c01c00b0400340a100f180c26186902d8020aa0200d0252606258051529840c0b1421310140c602d000e00c02c00710480e08001580b40c02f000050960050350f01c500541800307a0b440318034250040110041880003481c003442501c03105082030368400d1030b81d41a02d400f802c1c115a42e450398082068100701c03950002d8454001009900100541c0030314403000c403400390089070022844003084a000c40c50542e504031491007008141082070340260051010180241005010400b4440c0c1c06c000651003480f480442c4000001c0034810000310400410081c1c0900041c45005400c114000d04540701301040904502d15203941d0461603480340e0701503408405403400342c1d02a0001042081d010f02071031105400424244003861414611800800042520045404c02503508010050350401d091242001c9640202c502030400300e613421040a00005804503001e40d500084c980061021889821020f01600d0f450b040c0f901049805100202840d00440c600703120078501101035503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 743186717 1250 743185467 743185477
    0x21021209090a050721020a0305060906091f1809141507120237020109080d2406050c0601050d0b0609180f061803270f0619020d080915060303 62
    0x10f0610502c1c80019061710f0a8010700b081150b0703520280081d89501c0100200294210f0300c560704031340042e0010711101e0f003040c80b02f143c1c41078a040c5402c889840346a04103160015241d0b0200b41900c51408504001c0c9a40041d491024044064150303d803c81d20050502032001d8144001c1107001c9001217900b0b01c8950464114000c140c40f10201d507800c10b400e000c080500b110a0380f0040c003150200040442c010f0054811a03940f00c01030320f1420400403c10001004a980c0444014070f20700c1c3d5000000b000c002208000c0c2006450f000d032a115a0f070311480c50040141c000700c3c0108141a842d4002908080c243c642001e8101c540c10243d1b40c613805624200051008840d0107031099417904041b1120101c0c050313019814014000d040c0f0000111503c0c1c0d42e21843c914682900e481c50011040145811000c08243d9070007001d09074443c0740c6a001403015041101117000c138250f440e001a075010b40400ca800301108690500c20214544414900d0b150f03141c5850302d000200c0b1310000520f071507609204950f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 743187967 1250 743186717 743186747
    0x12030c25091410151407140f071814241c020901080714120a0507090f0b0d031b02010e1c12050f0315030a21021209090a0507 55
    0x86100b085a1200c00b01e808182c4081401c00030034900412941c150340051408010180c0301c0e1480350b020b101e9203191a80c481c070400c0c1c0c1d003004000410710500c0d03000d0008030307d0388a14000801c0910f0501c0c410a60b0303070110f4140c4010003450f0541d814400350a000d080c0380d1200c00c13a00056000010144540080d40301e4070310f0260711000d0040d280b80342e030000d0900104200c0c0207440c0c0c00b105030b89525041d5034a80982c080c07120280c250890328011440d00004000c181d400c0402a90311408241e90741a00d842c11b15048690103944500f0810000c1301c0c0c0344070380140f110b070840c4c0e40d410303030605500d004d04401a00c007074030a030503880b40d4403041c1964017600440c0810200a4415082082c24140718142ca15003034004580e94201514141d01c124400c4017500d10b560176240c401865600e0750f4860103104050319002e950140104600000450316030b9407100f00d0604907000030050500500002420300c820020702881c2d440b001c1c004006982c0710b03800e0060b40181042e00003d49a155080c040e19414020b040790 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 743189217 1250 743187967 743187971
    0x310030803041b0b0d14090303040f0f0506070c061404152f07020108010501090b0906090d1401050f10030512030c07080d02040801060b0c030a031a0d1112030c2509 72
    0x4d01c00400f1401869505c400140801010540000900303040109907000d030100c0e4002d0010401240c100f166241e640c0e44940c1205800e802d465403098206081101d204021130803030740c003c8047c00b000d4050300c4260f0350308021180580c85d20380e44280041400c510030055156458002c000c40d440b007144060380c00c51078180414031080d01740403804500c0c2d100d0034040f40080e01010002906500448040050303031038810000c3d0800001c00d0070f029840e00141c501c10b0744500030522503030104603400d0340d0007002c000310400841e0500d0604250003480101800c544502000e916040011079004605041006417650261b0340d2a10780840c6201640900c100c003405d030b101c0000303c138160301407280d00034000c880c4000024000707240c1c4e41c3c10480b0035008140c00502e007070b08100215441c0300c1c42680311006920884425052070102040840c00c1d00d06104400c841c000f1505010310784600c0c1c203226582000f10200003c51a003101c445c00e468071011a500e54012050104241c0c0000400341c0d030030280900016041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 743190467 1250 743189217 743189219
    0xb030f100606021504030c0807021c0209091f0f060f0806160309080a05030a060e0a021e09030d2109061416021f09060504030504080f030310030803041b 67
    0x1258548200c0d00900c0300892900380c002551900200e440030803c55105060403003956642c8095a1804070b50004890080d420050180140e90710410b0300e601c034409c00340c0500c0442c11841400807050000d00360034116032094a0322620722400e65074042481501d09404581c11210024a401911035600803071001c5002c19004a41d01030f0020340c0c2c1d032103110084010403c030340041805400b107803814a40030b0319000301007041d12001360145004503044100040c00203152a45c41155080c0d4a60036074103241003036000183e840e400e0780c580300720012903c5011502440c1c00300c3d41d4000396855804584a03000e0280780101003011190401017041c150031100c005014000444c64694020080809010160702c03980010440c680880300140141e14442e400424030103c0e28280840c0c00300b040c2024041d10380e190380e00080040c030360f4042c040c0902d100340c850740c0d165400e244503503041100c218058842c0e40d00900c00c104008020845640880b13070060803003680c944480c10800100310301c0c4805005a1000404 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 743191717 1250 743190467 743190493
    0x6080a050c010f0807050406051c06030501020d0c171308071e0204060b1c020c0c190f1703090904060f02072103090302030d0c0c050706080f060d0b07030f0b03 70
    0x180341d8440c0c407401d99405071405074689040d100380a05481050000703000340003d008190080c8014203501e0440c41014881d04005103040c8142c80702500100d8040e500401c0c540c00c0c105e290b010329083d023106420401c018103203400e42020b9401000b800344070341d98061f00c03d180601080e681150b44940e04907012404038000d0313500407045140382140403405139203030407000100c90411760152000e01c0b0072001216040508075982401940160803003008501444204201c19680c81004502a200c0428400051403800d058034504401c164404400004184c01c4215000c1b408411240900303411221040b030360726241842c3c001460b68001d0306010303034030004032032003444107081142c0040d902180780b44002d00308400080b82612118540140540d10034804c01185561582044003001c1d05403500c06010140e41d02d403149000025441003000c40d0b503601c24880d0340d44007241c1c115840001502d1035010741c41642d030340202c4ca01c00100031800b01a61162201e801510a80010006080081c100c5a035050509 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 743192967 1250 743191717 743191723
    0x3040812090418060e1204050105160309080a0f15050106021522060e0c01181211040203100e090718020318060a0b030f01090b010312020313090b0429060d06080a05 72
    0x114480f21907100d03081c9900106c101710b10448080c1c0324103030742d11410204071142032404403041440031400c1c42501c2e240441c664900700724400700e0501072460311090b0031881c20603d904040203010219443d00b0038005028460f00007548100781a10f41c84200f070183c1ea02c0003007006490740c1d40c00c0010f18401400800e420b106154004401040c00c3c3e1050390000400d42e80151982d840402c80d6035840c06203400204500d40303201040303140c0e8600031007803090031101d080f0002c0c040340d10403a1940d451041751a801d202c95400000680c0d030005200e001040e125052490040119140f082c1410249400000242034941c0d003004814004400c00210b41c0741c1d0800c000800302403d00814003d0180c0714051035260310220500903811000d8005000e103081e6421601d0703800040348112800c0046d803104002410090080341203084c010041e56100007a9a440c010400c000d40c0c8440d44c0d006000030241c0c42e66000312142c0341c0c0b96241508220323400381c2d41d1583c5000c85006014079610a107814024121a1000d0040c08 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 743194217 1250 743192967 743192981
    0x50409110c010f06060e0d15050c0316020601030507260a05010e010b010e33040f05090a051b0c0a1703010317040f0308030a0608010e0d110304081209041806 69
    0x30000030300030240d03658032400844503207106101c0012000041c40101f42072040c1a00407280c040d62043c0d044821f210604400e4540503113005400d0200002007000d45415042040c0c0d00c058070348090700c1b41d0f516580781c1a81d9a8241d024218200381c040e290741c400c180341200c83c443c80201032000c0d1640c482d02414024001c20001d24440350035400c12503200381640c421999180400001042240004841400140440d040d0a80e6402c0c0c203031146955481c80761b031900500000c003a031540b2120600d080c8070078040c1c220000351801030380c1c0341031406000204a800da848900d400351100415122040100c4080c5046c001d0381000e0b0050b0341049030181c440140e0f00066060b00d0054806006880311010442e80612442c400c0095000ca4032100b44006080b404c000d40d00311484000c042a000c0e2507910305421580f1003810420154081c4400c000300ca41c00001034203005c0c0b0300c01301035401c0615081d40f5640394120f81c00f00f100b06900025511105035130341d500020f81302d03001e0001c2c00c0b4088100d141000c020505 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 743195467 1250 743194217 743194237
    0xe0f0606090f03101a19090e070e0c130b030f070c020a090c030b190e0c03150402040605070201030b03010204080705150c121b0a111e03031c0f0e03160305040911 71
    0x2080c0034500c050b040413600d0384084207522003110446c51130f1408502c0141001d159200c007502810f90001401d40300450782c0c500a50211200303c0e41c515601c0041c602c4d02115a100410349070050080050395010710348426400742e090b00300002c80410520001d4540b040030342004000d1441c007204005581d615911071004040107a8603030450740410302c1100f070304818500c12a000340755900c00140c50b110344400170b0b40c0c200008039184a61300b00c01000080070390300a038000c9130019002140000666a06029025403440f05034021407030311342400320050b2500d41701d0082d103001e483d09561f8044219001c2d800c854103600c80d2019100a1250445640d000d5031048005058040e14400c18144031500494442c81042c0d001c0b82010340c031034070401400080b5402121604010411096428207502c06000904010441c003d41150300490f0307415007011164503007502204589400740c80049002e001048940c0500402682d480700480362500b00c1d19881150000d040d020300308407031415820250f002902025217 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 743196717 1250 743195467 743195501
    0x7141804060815180c030d0f1209020f0409030e030a03030608060f01060504090504030c020301050c0406120506030d0e0a090e0303011502030c060402130905010212040c0e0f0606090f0310 82
    0x203a9600c001d81d035104028010f0301160000804100c00104840802c0d50840200c0156901c0c240301c40c0009007005160458540412210080c0c0585164400100e9620000b0070744204a05a080c1d00441d4804244030210350055613100891000d050003105071103403189000b42129400c030f0346450002c028100a210b000280d01c01c050200f201044d4403402c25043c2c2d0100d5a443d0708080c070300084200603140150059040c072802000c0b901c09a02c0a01a4600c140700d030101c0300f81d99a18204004140c01c00e14403c800780107140805200050f580821111101c56017864049540d045c00000188410850340c81a640b0310318001e84440b0040d8040301550407078140c44603c0c01083c0b03c00340c00742d0308c1c1d21a80c08040c02c0c603000400010014139100c49a00583c01e04e42c080010000e80550344c903400c81e4003401c3c0f01c01c0c0c05540207040100b00060f50460344041c7c01d00c1240540b181c10108074414a040b406800302c0e21070b40000c0b4030320b03ca54540c1d806074040803000030708841800350420300328001400400d851700700076a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 743197967 1250 743196717 743196719
    0x105040e040c30020d14030a031a010e01120c030216050601030b0609060f10120f0f360602071a0403020106051c08031012080d0b010c0312050714180406 67
    0x643d032100c03606600312a0111a14120160708000d42600041d20444540100000040d2461030800c098014190700d51400204980900c50381c20104490031101c60400003004101c4000340d03440540c2d541c030007911402c0801c02554241080d40a0302031182010141c2041e0044101071000002d0340074101c0e801054032040c01c0e200e10080c415030000803218a034025800003556099428600311036100354016151619114120103602c01c20303034414a01010000744c41e048100c541010a201d003040d030b820582e5421404032a21500841d204030b4080242d00d404588805580500505404940c8056802401002d1150911051001c071003010344050b0015864a00f0100c0c1c00d0500060840d10810712a000d849846996a190b40d0507910040c24968007180c1c03000c000803420058030220005610465180741c440c003082c03407080102d84408106504100d0105c400b0170201e50008000c4801541038440460f070fa41d034424095500c000100c10f00d0016080001c0d034010361000c040c0c1c00015151044406003d95 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 743199217 1250 743197967 743198009
    0x30216050a0b07081b04060e011e02070815040c05061e0304121d061903090b0106051c05010f1a070b010b0c0111251b080604030806031c0503060105040e040c 69
    0x240b1100360441504401000305015030f80c010b114044123014140340003070500e43d09808001c0600039a00307203100560f01c812824803402c0c10520048006d410030b081200300c41c0c81c042d00d4804c00341c116449118014400055241003002e41804848a203215268900d5500d0515203091041c0415007124136001a400a0a82c10300381c0051100c8006c403034009101d50306148803d01e590040b00c04140c0d200c407c0c565a10a502c00050407240c0e1a80241615180c050319805c100c1c00030100034048681d05099103140070014040e00b40000004070542d42e102d00d03045141a40326840880d948070b5220301030083d1200c00c000048c0d0b0401304000380018904a0024455501041510f410071300401e105054034076041800959440d0031912035000d22402007010303400d0141c5940d00e801d502d000903001340e20f068000e04200810300d0740001106030424401d03001170410301c404507601100c080f040f404086c108000080465100d81c070410950303026065000c15405d00e800d061900402110082c458044960501180d2b4108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 743200467 1250 743199217 743199241
    0xa03080f150a1a0904110a0318050a030e211b041406040213050d050109031b1a040c0f060c1202070302060d0504170706090201030e0c03030406030216050a0b0708 71
    0x1d00080540b0790400d042c01d000310250000c140040003003502e5400d000c4100c1d9592a40510440b8080000c0a5591740341310010040580b0010f0103d2512106401d4203007000482c0014541d20b181e8140c0f50181300e94104500150030205604251200c1540c0004074051040001c600c13181d502c0ca881c0012000110200c1c244000d0f9040041003111003d10306000441500f002c1e0024036189600582d00a0256200d80c00580f40700443c840550343d5031365138180d000800d90403c0340d40d840340c40e00340d285100901d1343d03030340700781100a0070b245000707030380194102043c00c000d4254400e070003600403006040b203520b8449000900c0c60a1000d02550403888030320101c44031a00214440d000d40350040c00540ca071203c01003400700074120140c0100d8800541801164800001760083d24240348900b45c0400c0d140064000141590f05d0120740901640050b480b000c0e49950000c101c07412a0740a00340076880310807250881140601080028205e0b001d40d080400c10403100506051182195494010458640000c7d400e4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 743201717 1250 743200467 743200501
    0x10b1e19061413090e070918020607020f0a0906060c1a010608010312140d0b040c14090f01031b03020a02070b0c1e190506060f01140d0c110a03080f 65
    0x400d40740880b0321000407082004000c0341010103954262540d684054401300e40c1c20301d501c450b4039003000e0001c1c022444a40036151800604c030310100c01c1c06aaa4000075581d1044440017071103142e0a80640c0d40d242c8071001c000004080b031640402480c0d6465101604840b1001c100f121002c0c21441502466401c040300300f4140d40e516582c454940c0c0c299a04c01d602e211020543d401030211502d0706440e919070300700c0240420802d00c00042920b0200805000c295002c51340c0c4482070080303115071444104002b4050b284030a40031610607890034659001a070003030034001010107180c011660360054454041d0003e0034007581c16802c8400e1156240c196820901032143c2181035500504040c840785000012071452105586056030201015070302401d0019600b000b080b01c00360004820024203281c00c921840c0348017802e003840010183d104402403814802c40c1e10850f1910b40d00c0b041d100c00240b0442802c01e803074040900300d81c0754507201d0401030101076081340d140385c1c810328060000b0000c48900342da00c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 743202967 1250 743201717 743201729
    0x14071214060f0303120a1a01080610080c0903010e0c0913080405130204120311070f0b03010e09151807060c02030a150f14091002031611010b1e19 64
    0x580141c95140c100442c030706007201d056500d4441444420721040800f42494061074542a0000382d040e5004000c40f200d000c4244494140301c01d40741007140b2a01c80b41d10070084000c051509000c95514800807121a0281c031102940542ca0003118042942c0300140202500504441c2070b08142d44078118401904003281c00100685410320040029003418000e0b1f42070514000c00150405403a1910140c2c03503422120240c001540d05510003d60700b2741441031001034250070214400300b504008803400303e0300c01031244ea000100707804000791203450140301c0b1040400108119500d28200b0009a00090300140078140f00c60080c2640052418043e00a5521130b55000d4081c1c80719640c1d5840300d03884580280c904a214035112480c07581101000d1244094998008003907500da414484015403614049080f1000c0c25441002442a2040a8202d4000d8040245485580715a52800240c00752001c00010342d0402c0c0e01c071040c1c2105488080c084580c0801c16500708040e016a00340340808041e0500c542 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 743204217 1250 743202967 743203001
    0x18040b090615030907051012060e07051806090306040812060907080c03040201181806090b2101020702040908040509130b060d0309050a0b0306011b08030601080a0f140712 75
    0x205040110700005141e01c114400c1c04e9413001c1e80e0703840c085040382134035821410009408c030f4020f1a003142244507a501510403094658950314001d08040c103c2e03c190080d20480b15082c02004815948075412103d0341c9038060192580741c2490b241124298002e031f0008065240d02030002191803c00e091010311401b00342c0d89054564a940e0801021607002400690401118000300f00d0802403103410b6100500940200d01044440382d0004030407100260009440f035410800070411640d130f0b02c080c00544040d8840c040340d481c0280c47c1c500380241300e4814002d4005041c842d010040c040c481001c0c1046640948032800c480e516618003482c1580510700081002030b082c4c0100d1000e0910306001e103070291003400d101c82c0241e01d0b4000900c080841d54421035440c03400108200300c2d1759001101410004081c2e46801da9852180d5582600d03020091a0718104a046800524900e02c0307034000b4803600325902400c0015048401f2524850b50301180c0b45000b0482c410084130b8030200078814041c0300b0031030500c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 743205467 1250 743204217 743204239
    0x1d0111040501120e07080610060c02030a08220f050109051c110112050a0c1808060f1909030c02040b011d04020a0e0a06090e0609221718040b0906 64
    0x10b6603000391081d520200c031607486090f424400c2c41001030201070495440142aa23207800c85d1115041134182e00200c0c2008100401000103840029040301c2141e8810784d49625068507000710302050014800c407034410070f280c19001139500b00b140002e400780d1f8001c0e601c40030700e50303281d6050000001c1c49641c0c90441a03c06000e000205000100c40d5980103014136283e060100102c1c1001d007907610986140200784d40d201c0000041640106010711a440240054940c0f43d01e0b00ba1190b45821b00200350a1642d000640050482007510300d0b042115040084204091915800d0091042d603658a0890180b40380240c0741a196005801c91040c8501c851901401900c640041c00040d41180c101c0009000008101c8501d9a40b0002d54201030180b5036103181c1050728000d6241c0c50342c1400f80800c2c1c000d60000c070521002d0110030b21a000c1d40550705400c01d22a02c07141c80c050304042000d0704241c4c020303180455091054114143c00400f4140c00710703000e118000328401009040358040d114268850030f0908 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 743206717 1250 743205467 743205469
    0x5070210030605130f0b040c050301050405101508100312050a1719020f1b060a0c03181b030819090f0b030121020604061e082a1308011d01110405 64
    0x1020302000c14061000c204006c4200124064815501806010540220040c82942800d103c0c0d0345c0e000c0720322410380000c3c03884d20140002e007101320881c81d4108921540010001c25100d5203a600855106105840c217101c118001030164200c10b160100017002130401503c40d0304400c03500c2d80a080d242a0307403072014954030380701c0c4007e6000e2810041c00003010300c0700722100d41c0840c0c00c0d0642080e0031400b07800140b4050308250102c4005610300000d141c40d241c404070b042e4081c5550381c01e80325480003107100040702c44420048240000c2d84004e206080004107041d0002c4454240904a00e00d5180c20501d140c0f110030304061900c15000e01c91101d282800100680002520482c40800d02d042a03090300c0082600030070341c56071054000001003160040c054400e2000e000010400f00c02500e82080c09051803445110f01d130546945c0b42d519500c0380e100003140c040f110422585519010700701800d40c5070361620042e001e0640c1000000c0800c5d40549001c00c040f1060007003040100c080b48a0038030700382c1414 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 743207967 1250 743206717 743206721
    0x4080a030f05070917010b060d0b012307060b1c030909140603030d020a050c1219050c060a0b04150815090601030c0e0a09020607030903110402040e061e09070507021003060513 77
    0x1c681c00040b9906d071f82c0400c0058603104010000c031140c904000c6544056000090000400c09031100d00104040403030095481d03040c8103580b89a0342c41580450014a854000381d802d030f004500e6050010103026000080580280d001c400b140c084400034404841350100680181104540f025007542041200d82e0282e00a58014503590686080040c01c110071100264a40b202e80103c880c420200060340c0d42101e042a5081c850700602450018500000b5800c01e9441d50406417030311400d60744410b094111030340e49030408140f495004500400c044d42d80c2d40300543d203019580f0844001c0389004d021500005011403524141c9170450020100a4a04041504150001000035000301d5a030030403031005949082c02000040d029980310f029280c02d40c14085141c3d212030340c003140f00d240704000400002481a10182d409402100d00e1215010051800758500303145024080d48814803200300b04005400c83c0291a042d40296844c085030880c50500b039049030700b00e010341c5030300000d44150210004036a07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 743209217 1250 743207967 743207999
    0xc100b01090806040501020a1d01120e252907030e03190503120c0405010e0d0807050d08090607090609050d0c0b130302130213030b09120304080a030f050709 69
    0x6140c01c030301103603680450b03030300b80f0310103440c03ca9842c1d4000400c600903aa01c524040350041c1118111400c0150000028100c540002c003070110098a518081d03800c480103105031004038500c6100350384060850818012501c01500132001600d8221030707009107a100b45000006020200481c2d1440c0c00510f88040c2c41d07014194601603894401e190044001c41c1d492046980481c3c458801180c88003038446015440c2c0600038814942c540e02404100004d0380d0142061760104004c0d40c021003120410b06081c2024130034420003800e20f12407005400302c07d650184400e40300380d07961401e440710b0b0780300c900f03084409140c0c91042800281183c40c06210034602000b5010345140b1030842000d046588050116050300404c82c1c0b809940c1a1090800641c10126007011440c01c0f03459085141c5882000c6540486040d400040c0c42c80c490740000505034003040069451300c5405196182d00e9240610f4411300c2e42d031114420134000382c1002120727401c0c580305000d814011401511442d2070700341452240030340740780d030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 743210467 1250 743209217 743209219
    0x30c02120f150a0506010e061c0207080c070f0f15050c01090b040b070e03060f1b070606080307110d0c05040f09060608210406082403030a080a060b0c100b 68
    0xa01e044404200420001aa61091803240b00070322440c064a41504481d0020180c03814040181c07800d48203941c4110880b2000b1800c0c0340fa1160304888810140028041e0b558001e082c0003001a444140d0329001400b0000c590074040340d1a040c0e40c68100d400c0e01d144d00351007a410700d0349000d445040c0311402400a4100e1a0244000203102c0b200c0e0f440d03003103452a086d2016550203e0100a000903190721100402508005400400300d50501448224101ea001445a46022100054511580700c1d22085451060301310303130b05010309a02c4000c00798070fa5100303107011101130750150408005814096440d52007a80c0040e9854441071600b01400060404225540071803503842c5480d400103281c034400c00d409444840700402001ca2206015140300c4105220065004d005200402869a000440300e9110305940c81e84a240303010401a22003086042025a42c503010105401b0040c1e98401c020611400d0b01180a2081c2e0b56515000c28051003110b1031015940c000400013810b601d03854000d00c01c0510 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 743211717 1250 743210467 743210473
    0x3100f0602030c070b1615092306131a09010b03012009010c080d230604060510050a1403160e0a050d0f050a060603080a020c1906030905100606020a1b03030c0212 71
    0x2c4c1503038545642d40c0300c01c07444001f555519800b40d030601c20f04144e0610082c007071a01c07e20381d0144600c801c40d55048002c1c211101944506041410055031200a90040c4100307415a01c035802c2800c000d0340070301303040c2e01258003035031034a0404d1200d400400d415a001c0c2101d400317620710b03115811004403401c042e040c4082d100c0000411040f03108198520448441440844a5400e006107a480d44100801f01804461085052136000c2c8134a07600c11123000c80ca12094101155648401d26080d22907556401141c00c03a040084104182c00c0f02e00810241d020140c0d581380900920340c001000040030042c000c1e242c0240720050030b40300150702d0f03448400c0a80e02900072140c100d4080d9544005888440c1c10031070b007405000c02c2080ca00e5404003c1f01103d0f9504039044e201020403184448108040c0d485a00101501c0325946001e003e001d00c40707868452100f039000c0c4045515091b020756900c038802d01c200c0d40d8441c030100b1403103403444042142c07080d06d0345542c2c0c0b640703030081a40802280d107416050305e0324980 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 743212967 1250 743211717 743211757
    0x21c111e04240306150c060f09020a05210105070f0e0d051903020c030102340b0403080601030e011a0111161403030d060906091109030d2303100f0602030c070b 70
    0x1420f600c410300310254540d9128441c030407e02d0000150381a81042400c05401c0991260041c1d450742050819501d05030354500ca070381f030b19110a4030352400788035001c11154685000d22440716808000c03a05580c00c241c8030700c0b0340d1020200501152052146000e04590400348410f1a06d0180d070310118040d5009104440d102c080c10000030f030880e40b15055441e0310313141c540c900c0c45203804803980280b0000d40910a106000020b03031107500000c00c0040c0300500b000039040003c2c220303a020f91700c248068001c44008006624130020710310403001c110031400c1d0100c0c982040850030361800141c1620058100c0054001c400d29050f040a6010002d052990703141c00248100400c1140d5803103113034020140c1007000300d28613140082b940c080b40c44100060500003010007140355151400582c465160000c3c1c98240d14042c16580140c8500c81e034414022414900001888142c0c40300c0420760007543c10500200c0d0940b03995980c140d07680e01c205801c840d80340d001980200b0841154501400d8034500c4030320404501 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 743214217 1250 743212967 743212979
    0x9230906030309031c030e0f0a0b040305211b0a09030b0603070b0a03020d0b01090501210216051507020d2102040b040b0c070614040306021c111e04240306 68
    0x202e5684032090700d907100e0305014210f541d05000b00340c1894181d00c090201000a03407822070300c45c41a40c0000d4128034a540114040510030003c0f1245105c18000c030300000c0d03110845c0c0700341d070040540360042e0a114944028803600d078a0390455006a81ca0303190611c200d882c590359a10700260090282d81d1500072614001050200c000060100c0c061540d0016a90040303601c05104688846010b14100180b0810506c82660031203007400326038620002e69003000b40914501e4001c1e10845d0f50030450740d0782c1d85441d2030400000041d601c0703010718607010404040c0c3d152030040341d403100000324030b05c0010100d1039103450f10060a40d10150a03586000301500d401d407a0812005207501541c4040010700000807841d45101051012002400880c50103051198001c01c8040060140707000281456038000742424041c002903100164401c04070406201c0384081d04450036451700407525400c0c42c1d0b0328245482c080455460100d4080d07418500000b10075000502500b0700100d603009401050690f22400481c030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 743215467 1250 743214217 743214223
    0x60e100207050f100207171810020a0606090513030f09031208040210020c091b0d050403050705060a0203040510091a092a10080403020313030b070923090603030903 72
    0x54074002c0b8020640c0100100d4601d281c414184c402c061981d00c144448000915803c0000035011440480640c0b513401890149051006002e04d480d800329040080d100e61980214403149803a0080d002000500c1d607440c410303020f07280c007180c20203440e10700040030306e000a004107010034089180c0d1502314101070f00d981e40c0b14070303089006c0c03400e00104480c00100011450520b9a0405481b820300c00b030003c50003442c020030120f8a01a102c2d801c4c1d07410020400d60701d402c09009540e09811072207000e11060402c4d04001d000ca51183c0016500e070300030040000c034001c00500880c1d001d42e1340303e00123048000b40210280010000d620003200d072180d158040803055031200e11518020a407a40140c41200214824800062034018a000102c9405049a000b640d02c24860b581d202c80c690801704815900c92504900b50b21035105c85182c2051a0900403050080000080e0f02c81d5070a5184c5031038603602c500c01038403030008440302d83da200380c0c045001480c20f050840045400c070001804490a045030100009e013 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 743216717 1250 743215467 743215477
    0x30923070509181c030e010227100c060203060a12150b010221031b0406020f241303030204120f110f101b060606210506030a060e1002 59
    0x155404490107021034a8200c112640006204a40303402c200d0220210740e4440d03c540703e00c102c4407800211100d4941d1700a80044090301d08100013190344103e04480700400284002181102003500380d040032142c10b01718074105c0020313101d0320751146e20466a61440082c0d0300040103281c04c403c200310006660004405203485c01442116814085c03c00b41a42004484402c0d02080c1158442c01c0514010211841c40100c0502900c0c0307040d9480d0356580c01c100080149255004140c00d001800103255640441c58003441c5a8100c15641102080c0100609a03210103030008564220b1b2404518100c002c182000b103024424140507040c550b903046003018051a60303070300340c480d010b12202c1b41003000405550304504040440303c58541848030300200d075020b111010403c06200d14031041e01071084001e500b100c0c1d82e9134090005d000700c6440c0c85001f01401344030714403400c849168000c400c0d80600390303001d0f59105800c050000c0002c0c0b107440e00e8010141141003140390050040c03070300c100b06146041c00141 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 743217967 1250 743216717 743216783
    0xc090f0607050a14071d040c260f03041a16061e050901060e0403050c0c060307091e08120901182402160504050403021f0b2d010309 58
    0x1c642c4030301d40c1c140340141c50343c1d44400340215000f010080c02900701c0403071004050f00c6c1c01514607107144d84070710f4480ca0700c1000790400e118004900c0f24114803d01c4a104c1400d07120704460a490402c006c550090382e482c01030f405540300c80009400c0303005c9440303200006042c00c0154200c00c60400c00182e1035035412140388070a02d054051650110043d0340001e40591504042003400800c84246088040810311101800c020108480000e160f180e42c201003202d0118080000c02d015580c0c1800c2e080036082c2002c034402c000c079204100003100c03541c50030440141d080340c1480e400307410b440103004110010303139002c0300c030791414003580e4250750300705d0a020b8420700090000d88143c1c1c002051034000d42400448114100000c644c0041030030310341032451854003001c81c0c5090344c004c00c0c1900d46140070ba041014590491380e15120b41d8852141c0400c903a0003584c40154141c074601c0d21041d030310080b006409984a0400d00b69018a55807103915440b80c0e110010aa010b401100300100c0c81e181c0010901101000c95 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 743219217 1250 743217967 743217973
    0x20a090803030606091504090c0201050609240103050a0e1903020606060a050403111f20030a20031e030405010609180308090c190f0503150c090f060705 67
    0x941021101018080c154001c5085240107030004105115425140b8002c1042071001503445880c2c1041c3c80250000140910101c600484000d000384800c0f51210300c20003c0350089140602c518038001d1100a001c1031440c0c90b43c2140b0010741c098000648034801c1d490351035040324a945020b00000c3d034030302d007900813100c48414039050092810001622a5201d09001c024006019401c1000c0701d003125408440403040d03800343d000281c60022040c884560042118111041c043ea00030b04c1100140060546611007450140601d56240a6540c1190228184400318640c400942040d152078404c07113000c50b4030b0f240748010440a41a00c07004880e8425001205000c1000020b0003800042c00c210241040010170b010542c013003242001030058140a840d201007101c0010520080d11301280140c02c004850850411400c1154a2481142e0b80300200e202c01007110702c0d010a04c180c051517820008040c9441d02d4520031440d0740301010895014524034a850a651a00d9002e848014094406 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 743220467 1250 743219217 743219227
    0x304020d1e1511090a17030d110c07080606010c0f210503040309090506010e04090201030f020c0a02010e0303091807050c011d1903270302040f1e0920010302070b010902 74
    0x254000c3c0d50483d8204108000103006003030040d2550400141190402d014500050707142c16042c038218400e00300c3c00042c144c184030ba42c4086015643c0140b040001c020308654000f90340320400341c3c40d148192030080c00580c081e89148046403005407031001c0d9900074002645544000621100880540c200e144041680801040b0526800a03200002484006818001c2e898a240024a0944129012072085a65000c1c0c002964441e505c0a540404c00410442d030741c0388003016080e56a007030844201d0007c0c0748566030b18000d00b404400d80e06650380140c40d00346502c400c140781080d05403008000c181003120a00c458210345809010f00502c400d0040400340300040e10020143c01d001c070b9114180f41f41a1101c40317500000b54132210141d030411414400300d03003400e03151900c40303681d96640d400654070070700b003002401100c1002d900a442500703507407802c5a10445201d4844c000d5400c90003010b4120600520200714001100c0090b00c00b51340140340041c9803260b40d55848100000a030400c540310ba42c0810 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 743221717 1250 743220467 743220503
    0x60309010b090112150c0e031f0b1507060e0f0307030906140a0914120f010c030b0a1406031b280302072d080a05091f050304020d1e 58
    0x10b4054480c00c4203040140c402034480b525488401d80e102d891060741c410b148006c803841041c2c40b042000c00141610803914881c61100c40e003050114200c40000c1c42c0406a40719890a10041c1890503d0410300f20b040540c0354448400600d03080f401c0d600d15004c0c0b032010b084542c4050005005580c40303503c0741c0480038202140184000c40411070900004002c002d0708100d02d410503921000c807030300c10445c1a450290540440c450714041445480c0c0c0c0d108009009543d0b1906400c074121a09041c0e8042151414000411108294034403130407280d001c2c1c25071141d0207030905030010341c1e10005407030a00510040a0507820380c1382c1d01c0b8142c94400c400c4100c803070008200c00341d50703980302182c001c0c80e0650500c111030300d49060005a4000c3c6044941c03a070710904002580118900810300d8000e03d0b130329203e52102030302900542c44000300c00c1c40703003a10b0700394900a012003007404105032000350398513401d41d640ca0303080c052000740f100c4054520191500c100e881003080c0840c0c1540c528408c200030440c0000c1c1310 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 743222967 1250 743221717 743221729
    0x8070c06030b010507020d0c1707081603030f030e0c06030405010504150e03091c05030a020714150d0203040f020604080a0212010507020d0f05040e151f020304180605060309010b 78
    0xd041a410141040c07001c0059070b900805840d44c3e42d80481c2e1712400c4044a10f0081000c50080d4000e4a810124400400c800031021a41134111005401500c0b001c01e06003140403080b042038080140420020b40310314103424841d40c400c52041d14240120782c9aa40a60002500c940003150100c170740307a4480e810081000b00055401c0301e019030040c130500462104142260700d80c0a42c03e001d601441d40c40c640502607030034200707062a0007604401a6a543d442140c4025101c401e0790140400e524600001650981040010102410810340c0000d042605c902d801e04065030000d03100ba10201c3c20150207030056920600108000e041e1076000f0015072406105001803800d0303901043c0d010303074503107001c000d610354011802c14052412443e00c00725440c45480709403072a003e55000011910510030400c02010700c04201c03085207440461b142c582c05032202082a003822032007400000107800c140720402612580303640503c19002040d10100e400790302e400c08030b00c00c1e0f0012540f025a070ba45802c001e0366941000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 743224217 1250 743222967 743222969
    0xb070606140f1c050a140601031e05030d0e1c090f0b270d06060e0f010b0c070905060f040e0607030b0d05031917070e0307084608070c 59
    0x544050440040b0030340081d82c1c01e00d00801003a0034207800f10100082213000e2124540705a1322500300e49550448030b44090796000c0900049030f00d0010605241429260f0088071548554041d00443c0703000300130f0120300d000c3d1000ba15842100d108048540c418944002e404104c00181131752651005440c01c0e0040e0b4000c04158041c110300d0304100203404201d640a10000340d601d0381000c130b030304860540b44007084420552082c0a0f00291400700003040248d8802503041c020302c1c03c8001003d041c0d80b156404042803258404881907a07000c50400c11922402c0d0304520390118004019400002d000d801007420b541c0920f07044413181d0040d1041001d0b05806108000706444143d40402c10015284d032450354030700c100d200d894a60901c40502c1c9074039911445510100311480700c001d1130349040191002d807080c0c0c081c2d01c82d01d100e0b00810602140010000815540703540c007000b2a001c41e11401102d0076000c82c500300403d610b00007499402c0100050354814031003c2813043e10115a03c81540c1881440c1c0126 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 743225467 1250 743224217 743224219
    0xe010c031d011812051203090a1202030c0a03091a040b030106050310050607060b0102060a02032a190206070e01020102031e0a060302040e01020d0e07060206040b0903040b07060614 79
    0xa0585040082503121204032664018500c10211407a40c01006a504103401c4001950200c5000c80200f4041101007054651030312070741c01c4a8248000000580c154041191590b110b503000100c0170022815030342c0600b551004c54010389142655404080b41040420301c4190040b990040d410446110282c01d401e00d90041000a10300340303400c1031043d241c0e81c841807250b081040004000314040102c02c2c0100703030090000410340e030380e41d0000b0300c0d12030b000d0903c4050309030160003260001080d000c1c490084130b200f108844171032070614540b1b00c180d488600e410301d090350400000f80001e040f001c48040142d080810160010031061408820041058082c0b940035411a401801030044420706034407489040c000211840f101c5540c1c0d040c100008041d50b9101035489400d041145445000c103500070440445d22a400b0700a0b1111415602e9032140148038100046e84030700c00040101e0700800c0002d80080e0000162440c1c655105646400c0350024103041d98030a60303030b00081081c8090190340d5218540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 743226717 1250 743225467 743225477
    0xc071b0302060703120b1903020405070c0203031b030c150405060709080705090901020d0c05030105181306050601180b0a09080d140d0b091015050c46030e01 69
    0x4110780c08a02c2c6800b44900007428801e5003002c441c070b6041940c004203412500502149000203451082d100112001c3c0700c280e0007586050040340300541b1907184001c9058003e0f00440c0f51141444028a51b40004100991980010b20000708000c2050182c4148640740182c00d43d4035040c035003045800c11401511000501010180421036010003083e441c080394412210a1210ba840140c414064490000e1050703a161510300c07003044803901300004d90306940043d592500d26101143c00c0355681c4006803a210180d07220715580700300151300f80d000700c0ea00800602d0140c04500740b065802020384a1900310314a481c40108012803510350144150009019070001840789008004000d400381d180c03405040c007080d07400540469035411a4000d441c00003400f41149030745203000640042d441c0014001c1108028543c11300ba00031512030015510a600c10202905001c0c100c4c02e42201c4484815900100d0034140d010880da6440091030f00d81c6820f243c00c3d29440c2e036900146401804102414110b0b03040c05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 743227967 1250 743226717 743226719
    0x218040506060c1b0126010e060d0308150402090a060203041d040b0708040c08100509070b070302030414040b0d06090c06141c140103120f05030403051219050c071b 72
    0x3da00069810440b2012454000c41c1405040121854161998405150b0f484980c0807280fa0080000c0e2604039a940106405251038403010082a40c0c411800a0f00080d0002e000c54400307684c0303c2d07046070032175801440185032100d640007280380c0c003030150f1002c00581c001140400205107049681c01d05560300b80c404241c0b034035280d07940c091480c80207080c01e001c000c0c8100000342089220150840036000c004100c400e0031451940c0c2c00050042250300d90901d01035040000340480d41074042e2211180c1c1a00698142030520001041200c00745000b150b00c140c459044000302d0b01c484010080301d501608001c100b8500d10704042804c40c65a0344503008028564448031003003141c403000c3e183c848244032000e04200241c0724100c4040c10101701c1644c00039010b400004204494921120b17003008841e268031030210394a0314240d406000444020300494000c00502500c010b00203000340c2e0044005c03120514840c0126204000c9800458000d02081400120b01091000d15125a400c108156818240c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 743229217 1250 743227967 743227987
    0x180d0f0f080c07080a021204170f0102031e0a0f020d090209060f01020c0d03020f011404050f01060e0109020a18030605150a1202040213030b0a1b0309170c0a06021804050606 76
    0x25118011024004c0f1070013103a070a840038402d00281ca400c0780104011521140c468064078440314515204810318400c10200d0b040020041c02605c2c82040420304510a000985078224400c24006041c0c3e01d000d56501c030f4603d1041c400d48040e1222194000000400f002d8610500ca40c04074007414091088205581c15500b6a03070004400c04d461009a82e0040501424034081e841d1000c508403240700c550a0500b0034143c100700c200890300c60b0b4080c40c1140c2400718202002070032118240145141804c68100520254000390014500e0342d40519001d010070010b002031403620201ea40048a259480e6014080840401803607108c1d40dc3c4229800b44a49103040c4006510b0103817040001d0040360041070264051400007110001580c1103801c204580ca0112684c000900c10004c202d051025545403421543e40310b031190500c059480401d0355050b41a542c41d117a16a007111100072400d01c40c450303456001030f0840c0003404001240f02d5989100c5404842080709494000300564090b1106002c81000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 743230467 1250 743229217 743229241
    0x1020f0606041a1806030105060616020907170a090309050406121709060a020307050706030507020c121c0c0510110f2115010e01050406090905180d0f0f08 68
    0x31041c1203400060440111803030b140555842c100e90381d40f054003c408540030640c00442e403489042d0440080115690f24410409035001c0ca01d840c520410640464000500f03150800c960001c40c5402c3c0a1507086a120808450000446005914549680c11141059040b0b8620b8018000885003403240c00d0804840940e002000100900001d400c4208120740340021000c4620101d0043e1038166103520800c400b03940ea61000b20300b11070340d108804001070441d10a101d181d0041c4100c0e805030201410907010488a4001c064010585015101000080741c2c80399034111111301054490a0000c01d0605003503003030081071000c0d010304c10f0420821240d074207003083c2100e610754441000191a489107141c04840b90750980c90164640c40007406001c80c3d00c40e260120000d07039009036512402c6100000045400d40568440d000100d003107188140320101d004c0d0080703a40410440300c200380300e42854280d5464a00344000a4001c107080c81100e9a01c135074040000044001103090000780350600740c0141203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 743231717 1250 743230467 743230471
    0x80702012c031e120702060405060a08012c06091f0f0602160b030c0a0e100c1e15091703100f09060308070809030a060e030901020114041a1b07080a030b01020f06 71
    0x80e813600001200c40441d43c80d0310943c4d01038071000d06010b486680e8540080c001000038041e50000500ea07100508800c880316000c0c42c0d448a003e8242480c41d21900c05101c0002005000c0196140c400d545c842000000c0034036190042140c042542d040515040000e41409201c100300300c401d00e070101050006480a0040300d4205900d460080d94500c41c581e8100e13030780301420072a2588185030a4941140560161301880c0f000c0c0110705404905510014502c1181a00c002c01400e41414008400c100540b5030301c84281540110100310402103010508041c60348210b13502102401c45000603c40c148100d1403000c042c2540e204100143c03070954403980c60718003800e070009095000c00520280e140d00d0510820200b0703a4040c2c000d101e03e070184030304140c40750400c80580b401586000da180b15490b024036005401907810000000a9800e6007000d404010300003003481c2000d0000d403058240c0061024024007086000c1c40c607a076100cac4560310b40101035a00c1421000d045603c000c420660131080450a15 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 743232967 1250 743231717 743231743
    0xc010e0406151b0803070c031407020a030308180303010e090601080706120f06080d23040e0c07050a12090914010308030a0506120f06041703040c03080702012c031e 72
    0x1a00180c04241e030050410b042c842c000301031200100c06c1c0301d095500100c4032041544640c4a40422100131202c408050080f404041d502c071050700744c20400710340580c00c665004040400f0000840703402c88181c9245030300a034800c894400d0307028100104000f00344510b90140000e040a0807c691500718010300000100c140020051380d5049000050341da2948076400a00c02d00060f00c0032220401000791401141e880790880350001e412400c40d0302c0380031200301e400760f501003050658540c840c1c0510f00d210740c111200468083c403410301000041111004a016403146e00e0782d40006060400040c3c2c0c0a4078880314410020f07130500700060000541110a0f0390340081c00000000c1c00780e0300c840000f0801440d02c0000c0446020308076031070071881d9021640d144145d0081a4078414150b91800c0c500300c0380702c00c58019080381402041480000c070100020702003280140351142c2010740c211114807603003892645d49110046094440c0043c0d007010f01c950030701c1c203443d1146a080d08411174041a00d4048290b124 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 743234217 1250 743232967 743232977
    0x30b0a0b060f0f03101a0307031b051b030d021204110307061407110a1223071e0302091306050901090507060e15030408030117030c0a020f130e0c010e040615 69
    0x30320610851385e100c10043c0194040381c480c001e001c83c010040c070342c01500c0480000741010901c0001340750b803503043d01e0080c42a548003031800301c141703040628286280c8468505400100240d0812048600141009aa04800510503414a450209000850071580380c0c06900908000c1203130b030760041c1100e40001980c0c501c040d0303506010300d0401c07800a0101000344d4002c50608021031043c0680e100500502e104441d001645021492505108088001034071150f60001c43d06001070f807600e04003034441d0490407030010f410359281e03400034580110460300c0e8100000c0341c1401600740060360140c550040c1d2844020441102d1075118240c403501c080c0217070014803303c001c0c45516606c401903556220451003110030b0703ea050600c4c28603410341c000e200d42134404c1c1c40304410304040c10b408000c407510288540001c0075111619401e110700d500036a038038103902540c4900b61b500f140e00103000d107205405002001c1d04c090080350b80054415503c07104c203a030185c0d1a0a0f03050100e001c0000c4141e03c1c8010710b0401b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 743235467 1250 743234217 743234221
    0x5030307030e03131404200d2309011424061c0905070e0f0106170a090f05070302030601091116083a0912120e07030b0a0b060f0f03 58
    0xb030a03140d4802c20080c0c0d641501c88990002d00015020504101c2c03070340844d0300b840702c0c00c190398001100d10344400d02011265000c000d8403011403415800340034102d00c2c0198102c8003001d00d50040403218000c9980070300c45d944032058000c2507400c1001d101d5222840800b20030940c5c982c41d040c80c8284603000340031401035a0007c1c90b0a009040380c00f41820303c8800035002c0c00141074600e002601c0381c0840c810601c0f001d8644002c280e50300c040d0850b90b0306030b0307010340c0e2518454141101000c07480800942081180340d80c03040000301107115136030300c14101c4e0b0184005000643c614070615140810590054001c9407034960001c00d86e1003007100311406182031100340d014141c080c0c2400c2030103104400c0b0080ca505c03a0380301500081c507031208003805c2c680070000d92440700080981c0105c0a0303e00040340203101c2c014424505540724010201c850620341420000646c0c443e81013000e070300d4003179181c000344d0791501a0420081010700600440c00d03008000c1d41d019081c18908100400240124107101c040d8050101c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 743236717 1250 743235467 743235491
    0xa020103110c010c1d1012020702010c1202010e060c16080903010f0204231f11101d010506030a0f29040b07030e0d0813030507050d0906020f06040503030703 69
    0x16a004041c03102c008100d50001402c1c003030005041407080010380140640c0c49a03042c904003540d00780040998451141c8000c0d000b100070001c2d880004200d0602083d01143d2b070208020403088c1c03160401a40002a40c0000e5150052814800a0484441490800050b00150785400b2120b02e055400212240c0b109030000c006405807101074040901c1a00c0818000742c003102040c1c0c0b03549929039550290580140300340c280f10030542f42500302c600110a04020b6a04580700d18104c080400550090343c03065400d00e01000159410400348410751001d01c41c00300e50640f020312036640c121204400070007001c1c2c0640e80f0740001d004d819102a02c122a182e0008003524101000380340380c109901c960b0040c500e01440c01c184c81a205a40d414002480d02da42d18046010000307401c000d900305a140d40d481540c406000b040c1041d5003e2045041140178802800002c10070408180340500c030341c5034034000c181860402494840d010807602100c2e031050b420b120104101000302d0790422000e142c04980c12184103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 743237967 1250 743236717 743236751
    0xa110a050c060a1b0503070b0106090b040b0d0b1002010608070602060915090f0109050706030b0105090d0b0703020c01050f0711030a08130606050310050a06091418011b110610080a020103 82
    0x3003030701c032001562a14001d040100c04801000e0542c8680052380d002c0c2d0321400c00710f441d001c40f8016030401040402062200101d4480503203121840341e03001080c0c0840820101c0c40124603000c882c0003503910b03000103000c1c50000b4000c1c20040c2056200418407498901311181c0d03103003031046250f0060f0485c00c021410007402808100841d101060080c0310745103042c81d01c04d40d508600e208000002e0b242500000d040c3d80b240d412247c2c1c00c1001048207400304119101c1403a041806084a001e0503401c2100b592261428000c05106558840f143c02c2540341402020342450300384280101550410051254000c0d00015820740201404801100685191400c1401842d0310340149906210303081d950075059203680c105070700c250300504040c050195075440900a64000c0a500901500c000d00051104a107010021403824251800420300c00400c00b0350103d40368002443c1c1c80040c003103040c4c02c24805810444207030001e182400c0340741454602450f40b9140c00560070001d0425890343da59a920107055 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 743239217 1250 743237967 743237987
    0x1219110909040f2108010609061e1209060b100e06180a0306020f0a0306140310050c130f0e1003020d0f030c1721010b071e060609020a110a050c060a 65
    0x44031840314100e548035610310000c1901513918001030b5040e000412124400d10759030701150025100c1d240803088402da085084880308a4550070440764200e400b120380304e90b00130942c2c84c1d4001c2c0c10015090448209109800306011400c40600010070a03d03000c07500c404003200c0c24421304044c940603841c10140040c0848807554409003402c0e0021440c0701130f140c003d000130600301400761410040705a80d000505030781014918696807503000008508202076103500300e08da000007440c8290b49000382c0410700780c10105a94120203c070750300799502445040c0c02c0d400707025000840b43c02174001061031540003522070a9641c00c014042c0300e540322813200b09401039105810142c1e200141481c000b1b121420352070207400400c0b01d8542030340c0302c50900510742186d00f04c44d4142c1c1c040003500c074900699504c80e101341010145201000540002080c400f1480610500c40509901c90000d03076582000c440040c09420b542030303035020680222902c01d0020b04c00049880520a09071a043d890720074030401902c10500fa = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 743240467 1250 743239217 743239223
    0x41a190506120702010b0d200f06040603020405030d030216061107020a090c120510050d03050408030a050d060b1606050612060103120809030a0e011409061219110909040f 75
    0x70611904418071965040d2043d034455000700908459001005039401c000c110280255418250107200909030000741000700101402e4009801021004500030758046e90085000070b40c00302d0107110a160502100700e85403000e250035800d1490140804100701031300307400104034030f80c1c90145156901ea998190340e60759400416400d61541c0d21207485000c1e1507130010301000111207818000700039031684100d502443e03039055a10748a600341018001e040b0b000c0e400580c14030000b8040041c40160402c000e01310030b4104da9903181c030b500c2c1c08218035003512401d81248010603428401d03542500314800f00010300c1030704044040f5003901c600020a803203460040700a0107e0190f2000413050104100c1007203a49949079503403002983c0d6400c04691203000700d203985000039044081f442d0242d80304000800341851418242481c003804c1600140d8164040804000a010142c0401c100c1000d010450141d1031910391083c0001e60841110031018480c0b100454825951840854103000e44a405003d10f103074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 743241717 1250 743240467 743240479
    0x1050a1d0d02091e0108010207030c02090709050a06031a180628030308090c01091a070501110c1c030c1202070c0e0405030d06050a06080a020c01140c18041a1905 71
    0x81403540b003840c1a007204c1ca001010319030800006a1140140f003142ea6064040e0303982da0303806102e542003007900701c80500508100028001b001c01c840c1c0d960100c1000404841d2000280d40144071008010703d092070a980c0c0c81801c0c3c02d800e824155085c404a80e61105d0f0031200b8002119091581000300f9084009842d410981044007004042d008810580140c01c00d4040b20b418500f0f6600444010540f40920085c0e801039520514502400034080c11980341f1a8001184141c50100c003031400b500030446e2101140d100040f11202a80c0710a200004980c0528042c420036004980240149642c40564281160700148400901240300849400707490401e003070303121500741410680d60f280c0209420070344182c07402000080724a8003803203d404440003030f11100915629000008029041100c0f600025500e94128092404107854018420030000c08141d80740c1090044090040c2c01408050380607a1030821a00320008640644414a92040f52071021076410180d5501c00390b611a40040d400074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 743242967 1250 743241717 743241721
    0x8150a022a0d020c060306150c120a0c1a0106050a0c020102031b21070209060d0519080406020d0e03060c0c0307050303010906140321090d1401050a060501050a1d0d0209 74
    0x1c40041218074080c091a4210b54500c441c0c1401c0000900c016500700fa03100b1103005141102440310b030054189024448140c031904052414044003d520103010140020107041418040194800002810818410b00c54100e503040440161040c491840d181082c880010285000c581c401c1048800c0c07840102651406c4070b14013220181d03980c1101d14031b201d02e911442c010500c146002015101025001030115a40d0f45403c018408203408030201910707280130ba911000c06a50000c8400c0c40c81c0c03442540328980e02c51400c0700090511842160728000c0103134003181121641e4000614a40012540c83c0c0c803a55040030002451070742c801d000004101e4040440000b0340c0c0700c10340d071080b41150845d01c4405004242d4404041e01c0e842d008040344480c48607403070b12132241070105c0003500002102808100b80f008541d11406400f030205440389103aa9111000c003c0310301103c1c004c1c0c000a01c003e080c02e504002c8080c2c0090421011100c020505155000525240350789000d0041d00c2e158000c0c0c9210a14 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 743244217 1250 743242967 743243047
    0x9020927120414030f0a033603020f03070f050f010314010603061d0603060a110f0412050d080415020c0705130b010824130615170108150a02 62
    0x10ba00248522803482c1d100c503540f810707207041c042018100f140000001c0c0c40c0282c0d01d540c0c262038001c284500d0700d1000600301c0c0015070b40e42d8240e54180c01d211406000c828160b265104204429000c041c4090107504403041c100100904046110280c0f174046902c00350621401c0c004a000302401420000c0b0140d0843c00016841c4d055402442558008041c10780020003400350903040a00c1620b03500d0305a841040010710781c001550005907540901b40e003051908030040d03001c1c0e005402079044030150301d1549100004000c402c01c51040e4012560410311100c2c51f00f629030020b01c1d150310400341391194001910782e50400042c000c00001d403e00401c00c04040c0c0d458001c2c200100b59030b12080d40441c81200200324042484041109032502c0d0000c00c102c040c24040600c50520104012422400c1e116180030401c2c00c00030000a1218102d40e03542a1080c0305a0300001c0b1809060b0f018504a8000e225800040e40706d801045a000d6440103000d0380d202002900790305001c0829000c4001080070084a040c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 743245467 1250 743244217 743244253
    0x50303040b040519111c020603090706030509060c0a0c29040302210426300301080c0603041b081c03050c19050f070b160309020927 58
    0x80740a20200c0380d00c000c4a442c030b10300c1e030312404e2006869101900030350140c078a0a011a1004000c08900326102c1d103103203901043e210380055680d81703829040750400744401589846150b0b8410b50000061510b03050003a440c0b099031141e801040204003049441009002841c07100c2c140340960603182e08040071a81f2180c1604003419601240107001d40491a0910070040387c41710303507000b52035440e94505450284070030504100140c4280c41041050484c2c031400b00144031100c02c0d0202881c40c1010600c280110303842d40c00d060361310070003543c40900c01407088030000520f50780c400905031010360303482c0c0b100e007440c0b21503d5605c0d88400b15405209070120701c111010544c0180c2282109400c21103800401c2d050702560313403c40b01202c0608051100704000c40183c0182800d0101c1410710502d4003d000c540c1c29020b034013110080d80ea0034200024022120801c0802009442c12460108112843e076800240a000e000e0009001e2130940700b0380901c0264040020141106039030210384100d9090215608 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 743246717 1250 743245467 743245471
    0x5090402243006120a060e060109060806010b160c030f03020a260706020f13081506011b0b060f100206041b12030f1b4218050303040b 59
    0x4800c203024010002519188016142c07001c0000c0400e004680e100d0b4140500e21075164507941a0740318400d4841c1c04200d081c8078500c500070041000c2c215a6040074481c0b000d4801950140146504c0000104000e82d910400d0b5a0040f0007035610554500310760501e80b0782d034002d81e0000381c40340340c1c165041d034209034000900c0fa0ba041d202d40d11419507a450b04064080350844500d0140307018100700021780010315154018420030211696403400d02c500c0c2c2c10410f400c00c81940010701d40d0f40c4080301030700c80542618a440c1d4050f10902e481441c0c03540381c02c00085402e520010092003c032020300411502d85e20355110f40d20058020b021541030001241000350717502d0003990f042e40c50960181020740c4038400e8056803016240703150281d91940b500d6a504132100e40c40c0f1200502048a04540204482240031003002c41600030012061b24519004400d40342c2480c3e04240d421203000d076451514100c0d0042032404440c250244006852a0310000c90501c03000c002100910b9408008200410401007090085c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 743247967 1250 743246717 743246737
    0x5130201080603010209030a032d0804050124060e0a0522050901020301030506040b0702010e031611041e0e0a020a09050f150a0e060d0f06050106020d180509040224 72
    0x101150b1500380a0500f01d22804902e2038051300b000b9803500120b07015007980d004003054008422600b41003189107190300707100321441d0800210a4410320003408824003d6030503400e103540344010103100542202d10b4100c1a032050700103024000d002e01559641da02c81105c003c042c0078185005180302a600b0f130f80d0354500c0c0744200c014641380c03101040c00d80a052003070740d040c2d90b40b03c0028541030721071351620000c00030014411021503480d0101c144140340d061003d020021645000701405244915110712910194900e03103004610b81030700707000001000322032145071201030b22002640526030301d110350410034001d80c041c1d0011802c1e10000341c0c141c403c1e480399210307403070071520308402c0d440340c0f214880c1000c0001151580241c461209000d0540404142c91304810010081703641c84403d81d403115020120322000f40d130800c1c0d9500c01003140a03014020740c1602580c2e07141001000405200300e22803501c0078082c19004452600006046480f60030717a02c058414402c100d00108408011051040e5204c2f030410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 743249217 1250 743247967 743247977
    0x7030219030e0714060d150314334201180609050f04091e020301150e1b04030804030b19020301150305041b1409010e071403070203070605130201 64
    0x1081c0fa0113a909031191000201400d203003502d240c07042c1000d49920802d01c414040311400c0000051170000040f51044001b00203007031401450040704a4041c0c60034440c84000520003c1100d098401d841d1455010740d1140c4007075501c4030f20390130140c16481d44c0c0f03001c0904210407100c0010001c1c02d01c4241104d110090381c2d83cac80300025001703030165207106901c149800706070320300000d020b40e241c8402103000100001d40300003000030031910b411141504840e15010102071517464941541428080c8640290401e1070f0221a1442c2c440a03101e210001041c800c2c1040030568120008082181140c0c002c41e005207c0e1502c60f44c903401d12a0035000140e4203098100c0c19811501c03203160380d41c000c0c0c0e4101d959809010762203003c3c003c0158094203004004940700200b5200d21507042c6410a20000039280c09003d032410800140c082c1b1500b08010f0f00300c0d403c002c1420b810030a280d40d01504140090304c4c0640050307140d45405100342d140d4000c051008140c141031a0400c804044d0400c9115050f0703000740c3e50 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 743250467 1250 743249217 743249219
    0x1b08091e060d0e01150e060301050702031e0d0e031b060105040501122622050d0f020d0f230606040c0f030218130b031c0f0807030219030e07 62
    0x150600c604038588290007440078040d01c0c0010700264043c15414089000214003002c060001c0e807202d0410303400190740d0b1603e103c10f1200702d00f13013441600d5000100d40011480c00d4412902c15140f002d9031042031a0303460000a5136041210107800c194545844241125103c00f100c0c01741c80c081d1403006811b002d1601c03c3e200005142c2c58a4011030341210000842181d142c8100d44401d03801c205030b01000314030a441118109080034000e0700508540c1e80c00304c2e2400480360314003c9481000c1046e800780344288110103109010894a0b10b90707400950341254240240034032032804400030700d107848001d801c401c0260000c0d0840030030a454044841d0703100081d50040c3d61800308010881e0a190200c40015850403017000c94540a9070041c07420b014000002020030003c5000900401008254540d0880e2a080c0400150504004000d0442c030103040004481107460f100410510014000340c0800410102056070b1601981c101c44662001d1f107509084003420140150141803080c0410f00944a4044 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 743251717 1250 743250467 743250499
    0xa022503081e06130f0b0901030638060702010908011103160203070510050603070504110c0c150a051c05090109020114130e090c0613030314160605071b0809 69
    0x38a1403080f42c1c010852242c00d1200d01516004000c1182c1c1d03007003080d07510401c40303c55039280304402c1d000b144a200c02090f14002224110280b8014482071030b601c000000860190408501c000d1076200740070b5503020740f582000d000480318501a5408480c081d4608060030102c1c0d0011030045106480d00b035401200007403440c10480c3c6c3c030b200c1c1034009000f82c0c0101d05640c1d44560b03141c1040790060401811205a540c85a0000302141c1c0011000b850000000510452200c420f0150403003100085400c044030003804449808540300f010694420000001254200c190303616101200e00d400c8080c2c01c1000b440d044ca070b03550003080301d508140e001c0b0329140c0075841030020140480d200502c001c800107080a00d40310f0b44160700d0202030401ca0050080fa00e0504498444134050680c40014080c0040802e1a60801400642c0345501c03041010000300021a00c050030760750004e0071158031000c0007a10366075050b02241e00125440301000f60f41881c41040f005d201d550000303800c1c0410100ea103a881781c07443e00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 743252967 1250 743251717 743251771
    0x203010b0a05010c030806040e0d0c0b1003020105160f14060405011125023d0c021c02150a05071a0f04080a05040e010e0109140106080a02250308 64
    0x3205a500281030711289200103840380c003102d50844006040803c0c4500401c02c940e050141d4100340c080001c09022f0a0300a010394100119049000c1c400900b20b02429500002c005d4030445011000007100d1075100010020030701c2c07030882c00711b400c503d844580101c4100385d1074494170140e40999481d0f0809907405400c24008080742c1c107400205040c1d8001c0c030003070101410304107060b035026070340000c0c0344400006c0c074015004820700801d552030b410410b07403204a40008a601e090150801084441010306d401a00c07940c040da8500008190b1008030075071b8500c0001c0e940d894050581c1010f280c0030030f8007a02560014007038101c445c030482c0c010144a4120038480c4400008844000c0c56181c2c520204001c9500c2c01c006003105815850183d10346911502c1c3d45007461020384c02220540c10000c010490740085202d030a07203100980000d050154504040103054250242040c04515800241c02414140491180e002d40d0b041e07080708106881a42005008070408884491045c2080e0300300c0c0e041e0403191 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 743254217 1250 743252967 743252969
    0x271103031903140f1902280207060e010c060b040b0a140315041a1b03010f030213201c0906092105030c0319090c06110c0105070206070204091704030203010b0a 70
    0xb00741905140c0c1c0d0261162a100c1280500c5e100455003040001c41103140e10f201c01d1255807140034411514010750380020f2605040381e0003d010080d4200302003c10b42e9000008180141e0840400b15a070754a40c07000a0060000e906010b0b07105e00b81d49000507109406440c0c0d000f85803c1181540ea030a035801c480c0c0c408001d000c9400806418082c0528948011100d44454004141d41000c2d11464286240326405034003c0c1c00109001d61300c41e1b410000c41c038100b00442102c0181d84400d1010801e241e550f813060090168800c0c00300e2a000c00e0440342c0c0350354003540c003000000c0040280a410564248100106805030b000d540c000d1751442c0c40188100b0300014030006295542d6480d1655440c220b211f58aa00040e015070301d92110300e10800c5204c905801035072100c6008525115104d450040040c2400c0c203903488817030035a000890207070290703a040300135510081d4040d5100b5135190f4080c40060000d00103124001c201d103002ea82c240806c4a440009082901e100fa4000c01081c001b20301046019855 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 743255467 1250 743254217 743254231
    0xf10030615090b04050d1b120209011410030507050c100203060a090b01080a1a090f070e090919020301020f031807091401050d020f120a03090927110303190314 70
    0x81041308100c10304040341400759090081003814826401c0485403011404140c0c0048910214092500194a070070640e450040889440d130112401281004c00d291010301c03000c480034190b03074000042c0d409015004441008411a090b120386c01441148075009400941d1801d0040200060128005005205584e40c1200584903804c035569216910310141181041061300305505000030100354840540e081c1c0503500f600c00100c468a4000001004c040440010034071034480d803414060f2625010070040b181e103c04c840c003645004450b0010a02a1044810007184240008200001c00c01c3d010311400d8882c846030117172003116a1f20322402055031082c101b51039140717400c500100a40c0c0303050f0380714034001c520180c038038024055000c0015040d03000c020b50101d925002404654105030740000720340c006e080360040030440081107241d260020300714001c1d0311032100c0083c3c6140c418800b900c41820b2400900404503556805944540300314a841082860082420a040080954a00a20284900d038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 743256717 1250 743255467 743255489
    0xf190308100501140d0f1104060e181522230907060305040f020405011e0b120f040203100c12061d042301020d09050d0c0503070f020f1003061509 64
    0x50760355070b4903003242d05c800f4804010039590600b12420390494054a421010903001080e103e5240401c00381c0400101d420f114424030b52801e0000f000701d0000b5905401c00c624040118440200d100400d0000e070300318004440300e2240b0a0141451940761300f24528805800e06640c81d0103031300f0103088120202c02e41b0a180700f03403c0801c06100700d0f44607038041c42d800b42c005e10031400c8007419900454219170080e0444031084c00c043d1402040d80e5066035440740204070182e06603291543c0149030005606000d071a2443d02c21441d0046419550104542e44085140c0d590402500c810301e08050720149001642d0052982003420014542c0b01344080c2010003165a00400e00b0342c1d5981d03070764081d0480002105450b007000e08210300c0c5000002d201402004010aa001500c4000ad00b08035140083c030300008410040d0440d81280081c201006690301158000b806810b02d010f5440010616056501d40b40d4100c513811444140d845d81c1508418210707090100d0710052400400000c544522003805003220000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 743257967 1250 743256717 743256737
    0x9070303093f020607060f0c050708090f01170106030218060c0c011101021b0c04240e0615072a050a05010503040503090a08030c0f0d1407050f190308100501 69
    0x800040c48000b0709550351000746208109600061031504005015618540e4541c1c00c0c11122500c0d03c16001030480501302181420080e5039140a244285c07501d041c01481150480241c1d80d001e100c00306c481401c00d0701b03400401c4d030315140018000c3d0041480c40915421040c0e20902e01d040034400c41e840280340c000541007100504006440303001840d84001c4083d0750810580c1600006003203d59031162503400035204014590081000346c4d14001101d10f00341050b000c990501100c413034003030000c8a40e20b20400d00d03143e0b90b140c0050381605030300000d5018101c00154000401522444465003149500186a00071080e42c00c0350700038142c140209500682500c00c14055903001d40040c5034000d02c51812a880c00e0803a0022500c01856075010050560000c5880c0c1c83c070107410301c4941304201c81a4010210001c04260003001444289248840b1007070010340c00b02031103814003d0f5010040c074501140c4002e6800800440b02806284050300012103c001007001c0c3e03020f246400046840c16582c0743c8001e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 743259217 1250 743257967 743258039
    0x2301050f040b1606240e010b1b0102091c14010504030e1513030c0612050c1e070605010b2703030910021908040612150614040302090907030309 63
    0xf0391010b140c5060022503030101c0c1c00000c6180c001d240300703002910f1142e44410040031183e00340003d90b8100c0008641d4100c0184040b441020a45101d0b40991800c0c000c8005084d007a24028441e1068a68008810021801c01e0f44200e200c0c0c205824403600e02d03101d10894424200f07003241c0c0240d800400080480b8801261498216540742030381d0000d81d1710528248010240c080c0520a69000301c1c0c030799981d110104007040e0002107503181a55200401d000324a0300701c8110103540300c0c0020045140709483c0410708103600c1d502c01e440000398088002c1155503160303222507210303030000b400c0341807040c840c2103c00c1905a450a182d140540f8003800071420082180c082101911010044004520401c3d240600111405842e900d086000e01c1505079207605241c0020009100c1d45640002030b0b080442d05031400c0710443c2e080382154042e1405001442e00b1205088041c0305070380c4060b51081109040c04484c1001203040d000b182d102e034440c0d07448150780d110401035207110140b03c010381486a5618a50f1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 743260467 1250 743259217 743259239
    0x60406051009060e01050f01050a080c16060c0e0307090c05030c09060f070b0420330d0e06060904020d0b0403030906140603060709050a0b090d0c2301050f04 69
    0x100c0d0819036480800398542c00d40c0390442d4056441680c24200c403200400007414200c81000c0142c00030b1070410300d844200100a005071070302408103c1ba2410000d00c0151807040160880c1c0c03400d40c8800107015075100d01c4001000d106000c100d0b10300c640200000001d27044080c0c401c4001c55035040e01d4481c1143d950010358016508175400440c0c004200308000180c10302c1800c001c8c00d01500c1211208042d0074139041280c00541800d40c070348491031040c00003109070307038030044150f41c0c15200c981c00042030901c0068400181300001070408040d2800324901ca62442039800034950031212800b110216520b03035007001000d03002501c0194106099100c0070b0003103051689103c0c0d05c58001d050214852740d15a82d01030882d0040e04000000c150100144105441c003804660340010706490401055800d000008140807014861000c24800003d01080a0b80b2840b00860800d6048518200c81c00c0e0b5603000c4010345103008030401000c0d044980e00b40c6682d030251054400310091f03010028249402e0042540c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 743261717 1250 743260467 743260471
    0x212f072301050d09020d0c142e1806020a0201110309100f110d030203090105100b0a1d062808150607030e130c030b09130f0c09090305031801020c06040605 68
    0x341003134130b80c4802d40242e1540d007000140c90f4800c181c1807800500d0500d0b0030440c081c82c1080c49100344100b410380b0401c04250003000e114015110800c64165040c1d0300203503038010240421131003240034103d00040e6541c001c580c104215000f0388030b1402103401c100301c2c3c03a03c0c6c6c0b05104c00d030380d0300c81c6100c01002007031031041c80b10b8045c011042c00c0592001e00c050030031a1030901140c44110009400104100c5041e00a00030250854504c00ba0045014240350101040e805001020401c2200e4800d91440742004854010500762020301714980d41e04d800c14901002019104407000700004100228165074030401003903106441d1300307103010400c1d8000c0702081303161b038400e00060b010040d05040035140c03a544d81d0452041c84600d00800a0814025800039040c1d9000203141842522000b0800c0170482c030700320f00310305650f500050b2200c6841c450b00c1c00341030079003241d081180440c0c80c0c042c03075000300b6030058015802807583d1760124401c0e0001e4066907087c1d00c1070442c5082290040f90101e80040e41a4102302c3d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 743262967 1250 743261717 743261737
    0x3011208030723030403110d020a081305130c0207060906120f2d0e21030901020c030c0105010504060b0f07110112020a030207060605010804212f07230105 68
    0xd00454254025200c0d0a07540103c1007540740c0004240070825822442d1003206581c82c0020780020302e202354001e510b6000306c01d8040c1c00c80400007200d1192400c03074141200500700041582000000203a2074100420b8283c0400000d8070400a000c1500782c02200381d00c00311622a900c524518012416840103040d1b440541400c140c2c9130240d094500c071241c02c050400121030b1a48048000407000b81005a0b42210980405500700c0314805444025000c03804207440c41e0841c01a40d00d446108400d4028401c10680c500c3c24000421941c44581040d000a03040340e01c02c45081c0003807501d85100c1c80f01d9100324031410449880c1004048000f071007007804050075800505000302c0b4042c100d1041c1d0142d80c8606421000a03600040c4002000752a22405000d400d00303103000c50062a00ba40e0b54840822252056030119200d5045044250700c01d0700024980e079514084150328040d001051920115040304ea00100e0140d47c0000c5006a5440c0301c0d0000d6400707001c681000f11400000548155029041c06 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 743264217 1250 743262967 743262977
    0x20109061d0d05040f12050312010308030405010e071202010e031c120e0d140d021c06030203060a1b0309020105090603090708120703080c0315030a0b0714030112080307 74
    0x10002003411072103104007508418400480e4105400581ea0070302c2c901d800b01d8018040d0600c801c1c012088a54076130b106403400c410f0860614800d9080c8a851402424410303810000ca1000100030410040087c50080c8d100304028170400007070590325925001c0a0182c40007403401420002d0240d8480e02070b440c04041e0250982d0b8459401c81422200304200d0054030300031820304a00c5203000101841229110b0300607074054440903454480040c030f00c1c031005a00d12481c0b40701284100340703c400742d8100d51000415041c5a6141c003801007800c03015111911040c1c1c0b0034090359000940e00d020030f0203551082440c012000840d200ca00ca0250001c100e5544281e0410106100d000800d44900700211b00904080c001045480d1810b02c21a251503007280c903000c60080e045c0071500000e0b800c1301030141c000100108132134890744d07070064405412404d03c091640c184140c10700703002489103038101580625841c0e5a07043e500b00d655420084144420b20a665050b0b100c039044d1310210f64198095a0008000d10341 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 743265467 1250 743264217 743264231
    0xa0308060f04092f0a031412040f060806301212040212030a02060a02030a0b0d030c030e0d021302070203010e0304030b0f06092401050c0d03051503030415030209010201 74
    0x410b080302c104040442e0f42d0700d90340854160030f407000c00203400c40040b084050444621010b0100341030845a1200801d5006030b0302ca50207075208207010031810000303401c4030191513594440318031521215500ca90004600c5640105405080103650101c1a405203401081c80303520150f08445c2c1c014110500e0380c01e50003034036018105e0b492110000c20030603c4100c050b008506082c010803405002d40c4041ca075085d48200f08414036680c000c50520703440042c5000040e240c0e520f6491480150007070304242c0e0703030100c2482c0a134000c040d0001a12a81c850083e07588a051034a8881400040900600d0185d0b201400f401208100e000f0b54000b4000d46201030004100c900c800b0803810b00d145c03c160000c40321012070700208200103448045250b0300c04000c9801c4030050500c10352004680d00c0e0701c4045d250501703a00740448a981d01030003ca4080e62140d20446911303502d54800140141410794008105009000c2075000c140b6000050314103a424000380d050300e120254130254001e521007072100d4195500d441c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 743266717 1250 743265467 743265469
    0x12106020f0d0213090905060f090c0d030c060b0312040e0406110301180b030109020a05120708120c01050901090b06061309060f05101715060c0d02032101080a0308060f 74
    0x409030203a90905900940c550b0016644c0c00703074601d2640c01030b260b1140f500e104400411400208150814045454000c0790303140d4505007400d040280c115160889107105000d001c060380540303003034110b5000380403c03c000b014500405446100500607c0c842c038070240300501c03950340c0c032402440c2c209200d510001903626156015004d01d4100760700c041001181070307810b815054000c2c021826058070450081080529a500083d444038081c0101806251034000300b00c501d850401c02d200150444030204c4150502c022422089507002850701401942005c000c50034040050041c0364465030f2103c100100c0d0707030310761f410b100003a00094000d9901c010054000640700306540701d180301a24810080360101c03814031083c0f019980c00308000400700720007000c000c4a4180d0880c0c0058110140a40c81d4021200000c002441c0d802003400101003405a1039902e06043c0c0c00200a007400c080283e0420744111420380c0300c1030400c0b024420b0000c00e0300310300d455000003441401070075441200245101044d11800d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 743267967 1250 743266717 743266747
    0x40b0c0c12060c0f1902030c070b0901091505091807090812071b0f030804051813320f1e030301060e0a0815060109090c09051e030a2901210602 63
    0x49680c000d87c10002e00796030140018000c22014103080b4072400d01e0816000002040178140d0b204402c4120b580040014149204908036241c0603401008020806e001c01501c0031110800c1e40c1c060041000c0440002e46500d010501052040304010362a0a00c441e42d2208942c120404500480c10701c030300000800c52103000708103140598000c0510b82e032510b080c0400d1016101500b8040e0048141704070070005c0560400d525400c2180c0d1103c403610300600c40000405400348541c0000d400d1140c00d00302c440b10020000385848070300034500200c40c006001c11807400d030b41000450904070550030030001801960300994a078817400a0181485031074903698111a0b00b40302500c541000b5a01c03400003804160340e031041c0c0030340240c504428104460029240050b01d1074150b03120790b900811072100c90380c0002c000ca803542200520041d0070303540d06403154a03003040010090012a92100803100c0034055514500030414140c0b1028201580044407038440303100603c18400048803440d408000322061800c3c0343c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 743269217 1250 743267967 743268007
    0x2090109060f0608060d02011110020705030d0c0302030c0d050402030a06020c0115051f031d070e160503040f0b2e17190f0611040b0c0c12060c0f 64
    0x10300c00289031401d000c610b80c098561079000c042005201c100b8800243c3c1d40c180302e580d40950900f49800a0048a0700d00c608201440e58000c01551012a403c000e11402100418191110500801c810300b951001a4101d010a5615012020003441b4041c0c07042c84990001c6d8015000400710b2300d03502c0c856030b5a401a40d1003600c003101181d4441040340c04611034460741101404003101c1892400401500596903170f258003e41030700b0149ca980c03100010104940400321100d141d401a1242607444061003185510290307452030550421032108130401c1d11986c1030745d0095510207039003035072081c50b515120890f0350054010075015903006a42c82d50200b90317040200407888441d00240006183c03001c03442001140340500740d000c0d002443c43c002000c055150050115a01542009141c0d030f20b4103003500100036100c44000601000600426070326000c00240c8003041c04442145c030210131350002d000741243d0230301001c51554031a4000ca01282c07207040113400d0aa4034948510304025200e003a40581030306c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 743270467 1250 743269217 743269229
    0xa0e0d0b04292d0f19020408070f0e010905011203080601031401260106180c090f08061503030c060f0705070c030c030501060806090307120e030123060d1110020703020901 75
    0x42d40d800803c04071441c08940020b24000e100514180100c0719461030000c01d810340b60410ba1400182240040d4143c60190070b0480c201c50400d0703121000744ea02c03c07100b8000c2c035070035039105800025031300140d000b101e06032140c4c0140d244400d181c5a909507401c1402500e030505261716084903003101010550001c0c0240340c1183c000c85610120b030701d460044041c00302e020038164144101840301d12001140e00c900c3e100d5614001070341804446045a40162540042094213404500000e1180000034a54050403100030600300b00074070f41040517601d00c110104000150000b00000340e1001400c1ea0056004100b818028a46000d0741d483c0d2150003d00d03001280e2201c1417020510030b124003441100082c0250380c0040402e424009111952401400301c001e0041000781a442c060b14032402c250340501c20050020700815103044c0036460b2041840c0c002d185107460020000349240b40c007500c144d13859600300540810707600b00314092000410303408022805520030745ca00040180c80300d0708424001c0c56 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 743271717 1250 743270467 743270491
    0x20d050a05040201090b0901020a0b18030406050406080a0623060d0920010f091707031202010515060a050d05061c0f050c0f01050f1b030309030a0e0d0b0429 69
    0x9094030014245c210a604039590891080c40030140b80e07600081c42003480340d001180c0404075910005240d04107441d80d000e2310124000810f0004040d030304240600242d0b210381d100d18001ea5160040841200c0d4a44174580e09400c41e16400001d22503080000180d48070003800803458840f80c095080d0696440f134104980c07040c030140075130064200034254002010001d01e4010b074a4a0800c80c01005c101c001d0051000c8004003000400c81c07044100808401941d01a4000c1c6030f031600d498000e03000305000c507400740201c0403000000c0744d00c2c0f030000200c4481c00c80503216181403003c000c01850007040d000f48110303044a1040b502907110144140281e8001d44275402000c41c6070344510700141051024800e580c0a1007139822011040c2e0303045410342e40301d0856814419103a200b4144403200c0065464070580762030000000348412828080000c183d8241a034403040041da41070310a00c0440211f400c4080e2a800b0200702040004402c04a4021719a95010f01c1c4058807151510b0034100110944501c1d0300c410f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 743272967 1250 743271717 743271721
    0x518131b09050a08060106210f0603030e01210c02030f0c06190614040c0216061107140a03030c0f0b0f1008031204060e0f03031006140406020c13020d050a05 69
    0x96804440d24002c2c040c140c0d51509603c1ca449040d0303594000c10302036403041c0401000750104c4410b034601d56070b0500448142c18040300301d0b00450940180600d0100398001a0155a850b0281d4007400302c0b00ca07050f180100c6401d0780c10300b10b4804401003c2249030b90b4110700082004007452035810015014400c0c1480c080c0c00303241081c00330011040003404080d80410700f410020844801d040121403424031f003d84011501341f804401c200d00b0120103451024103845045d0740410010350140802d0084c40e450401c4a100320f07103c89582c2c1140c00c000c1d071460f500405000c1c0c240000307407140142d001e41d0740c4100343c4144848025600c429400074202c580c41181240d01d0200480551508441c10041c000c0001440c030708000400348104d80203004001030034498880c40c080640341010404a40024a418280d0782c4038217001c4101400380380184078500c0002d40c0303400724010200c104400c640481d00c040d00288001c003080b00510441d040e43c108041a40e950a00c0305c60129942801554400c1161401c00281e078 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 743274217 1250 743272967 743273021
    0xa0c0903141608070b0409020f071e05102903070e0a0507030f06230a1a07110910151418100305100902030a02040305010e06070f0e01051813 62
    0x18842c0d521066495110140401903010004125001c2d1203050b0b00269441140384400c21180c03207000001404080d0b44400e1001015821321045c094522403801d8075400302410b49510156203d2140070a425002d0000440700c040b10544840c0030070074080c6c19160310a035a00901c0403206002c454241c10765440388200540154544900314203005040303c02c010550618400320345455040400458804500501240a036a9210704600410043c003000740a07019a180c1d034070b440c1e000340e4001c0780c0044c10038120014601e040e4100d140b044414803c004042890302d000c021080307907490740c488180003405002e408418460401802d5805401d400104158200d40602c0290703800141c05600305407825051002f8084880190750032a20151400360300d0340c540e00d001800a11071a0300081c119031a069100322000004038000c0d2160016455080404d00aa1025160040034201217800980d0400003000f40a80075155158070034806005a9820108a080d030b204517074a0b05481d08051490302c030b119100e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 743275467 1250 743274217 743274253
    0x3030d0504210c140601061202030601020114011217040e0c21150306150604140a050a06030b030d080403020309300106090b030a02130902060f160213140a0c090314 72
    0x501c130081c10052140d585003820040c0868240d200c0c00130040d4000020424581c030035005810724901480e0494100e5070b49183c0c14440c000611001c9901d450a0900800c2989000050790220385e0705171401202599001c100e80000d03403244020348103a140202d00103c0341e0070440100c901c5155144106c41c45032113000c7c1007500c0d11100614444000c1e0601c23106400310744980302542c00b01c0d80450a00d0541054480004180180c19000141c104078214400210700354036401c00a15054190140d521885035054101e41310001100d001c4c0140e4010020740042e030a024959840074a42e07900404407110040612a0802200415800081c0e44401c42808801c03a207100c0d50f105554200d0041040c00110750105030381d070203482c0f17140581035901c41621003552549403c42d2944c0d202104840e58034240301003060308403c0e1145042c0d000302d455948804401025120301c410841100d82c0f20501c5680790300301c1001511024a140c0c3c2041051040000086c01c082001607c50122002912906003180f5074660 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 743276717 1250 743275467 743275493
    0xb03042609010c03110a060e0601050a05030a0c051c051e0606010903150504050309130c0306050105030c1b030408100b09060a1a0a05090d03080604060e0603030d0504210c 75
    0x25900401c11040009a03000036101602e2076050604001c1010300b1004075040046501002d00100d080c001402d03601000400c50a068580c201d4410504544800070306950b071040b11002070030b047c8900c2052015141040360a40310840c2100c090040380c0155030341c5420100c0307401c0b940043c0e04040c08610740e01481413001c164070040a18119036045d1542c0c860100b00f81c000011680c9541c2d462011030b0074030506000722480d2100203400041924800d2035258002c060801103240002d18200340481c80d0b40c4500112801382c501080050709025061003580700500c2280c4054401d4403041000060004040c03103d042d030386407009e200080a585540920070b0062008007030502c40c006017801840f00360001002e065414035402c0c596a2a500c079401c00b0b0310035108039504079900040310400001050b51240380c140c85038006540503c00c0582c0c0d414455080c410645040342d0507001448504c0041141d44e104613882402801e060106115400d400714100e10484400c00c00590030003040b0f4280304055803c02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 743277967 1250 743276717 743276783
    0x3040320041b02030d0213090606090303120c1d130c031a090105061b0f0a0606090e0601031106070c0e091c080c071709040608070f1403070905040c0b0304 68
    0xb10044035034034000d460781700314068400069030104040380c0e88112246010090207005504100f0700d42c5071301010300442d800744011400601d00c004041c4148440303003c0c06036185420f446014a007605400800c4a4510044003560401701d1040c0750580c2403024000e035642030220340c50000b10303010b90008070a82c402042c0b0740c050181d012031004004c580c451070112420000355246490b24400c1486c183d60a040ca9400c6505991160030018000c5c0010341e0700c80e81c12585009400c0000794040000b40b40c88030301c03d120107420044e01d07000030180780c01c00320000c1140910a40600b5112030302e54440000350f200a80d100b1025610590110140c95900380070180054030a0901034014a00b030b03000c0c880c0070b209000c0014800c01000c80e80e6107603420303a2020703204031140040c0705124103a160100160b480c1181c2c86426031803400c2481c0043c0c81c01d50300c40012815000900501401e83c107021456000c0c02c030141080b143d803139071504000b42c51a03583d00510b014610841904030036040ca0348080c0e4086803038017914 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 743279217 1250 743277967 743278001
    0x1614040e0709050414010f05242214180c0603100506070609060c2a03080103060e03090a06030902040b0105040b070b04080c07030605041a10090b030304032004 70
    0x100c180c584002902401c840a001021034103940394a0703ca46120098500b200b074a41c00c3c909003460000c100d8014500c41c6c0b688604045810300d520182c00310200c1441107660700402c135442e480441080c001c404901c1201050004640d4001483c92241e04140403107068000c02c94010309804145c5003840b0101c000541203680d1415810a031800c0c40804055114140c45410005140c03010048035402c0381d0390b000d4020204210314105001d018041c2503e80c00c0662451885000003503031110b8041851482540594036800141c0c29652104010804134110400071310080c019080159510b000740005001d2503580424100d1652042c401520344015071107040c01000c0c88140180e40b1040180d500142d00004090455140c0e403e18a5403031017501100c05950148100210a00110b50005405603208039500c000c880c80d88100400360160581d004c0c0000000060308102221098104416581000342a24a415a2655504140600e040920384044101141604140341038419091074210304044 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 743280467 1250 743279217 743279231
    0x90f010606081f150e030706020607020c04020705011107081801030506060a05070c180e0724140904050f0a05062e0302070b0109060e10060f050c010e161404 69
    0x2408100e0010455079150b100c001090800c51040c0f01241e004041c400816604110f440d80c0007003601d1802c1c503545020744910180069054400608517200707103520383c0940903072000034007000040e6201040548296407241510900342400d0001440d169106d0000607654003c40781106004803070852205050524104c100b1102d81c0300c4a0440b204e40c11580780c490380c0e0740300368940ba100585c010342080d8082d0200400300107500f600c80d03110003070861000049802c850b65500302c413400d00300761545e90092540f200303280c00742a600541c12041c90381141d44400c0c0c20111a50082002c99004552021a0360340c0002404000400740c441e00d50880002e42c0c250003840b1028a943d00e1030034042103209040000c0314903080c804d5100e80d0603503c1c0b50741c1c84a000865965642c500d04043c0c0a907005181054070300f0700104104400c4e05d620b090480300c4d59201c50581c5131485405940903002036089001e2035403981a00420404240080601c100455008908160408030609401500b1840e0300d03001d1403800348 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 743281717 1250 743280467 743280479
    0x2c0702070305030a270303031d121e0403060e070303200604030503070201020903030f0c010b0108040b04020405060d02040c030e10020a0203030c090f030f0d0e1503040f0c0f0e090f0106 81
    0x42160303042c0070a03041641a070b440300c084004080160417020000040b80c44404010554103820403a10705d400300100415041c44442000c1c0c03100b48060a2900c07001003009441d981e02e4020101c200da20202040700e50510740e4948451090361003c1810800b940c104800c01d0080507044941c80344090182d0111000801c201030711a569900080e00107801e00c0303c04800581418400d404a500042d4003505403519101284100c604070340124107043c089500b0900c003440c0c25403045404502c225040700c902e0019443d80e07024000108005818540c100070081b4240000d038039140209040c0000544d40050826203243c81c141c1041d01480180200354010408105560f50001c03c0e41d170002c80c4e24928139542c003180400100c4201c06028403d805006510124100301d00100f115400203445031108075188010008005851207000039584c403c000a10118011511283c06940800e1003603040520340741e280c100f07100401c8125405040036170100c504105500005002d41d40c11607080000a004050a040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 743282967 1250 743281717 743281723
    0x1050709050612060411070b01031e1e020321070c081605010e06090a030c06030c0f0f030c03090b0a09030215250203042714090c0f03072c0702070305 66
    0x440f00c00c800c0714445000c04d4255031654082c0401ca0150404159910007515084070148000d1100b5a0030002e9203074241a520407100300d100482d54050000c000200d12440b041000e1003203843c0c142d0301031151440104001c151802507000d50900398040603202c00381850a802034000c250811a4070b0b80200c0003661118103100307090400d640c0309003408031a030300307a26001c580c00d0b010b400400c5600140c1c4a2000082c0320342d05100e8800d5610956090051024100c01034441d6000701c41928002070384070f4a10b4510522a61018010264501c0c1c04500c2548d1911303050140314068a003110075980e00c81c1800d040640401c002500c50050700d1140b8424948002e14181201140e4550a000103112050054991081c4111000342c204144040c0b031b00c18520b00910025003540409412041c40c2010f4a019107054601a03840351450000900e07070010030406115444012100d401e425110386540450100c02101c40d41c05002c8101804a41d10203040c4442d5481c542c02414440942d0401601400411404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 743284217 1250 743282967 743282977
    0xf010c0c091a0405150102071203050316020f120306040b040e0c040b03030c060f06010e040905070b0d0b0315100f1d0601111b151206190f0902070203010507090506 72
    0x6140e002907942c6102000c0d480c4001c00c041101c1c0d000b840c0c0b0007004090b10f8440e800f018000c1007a801c8034000c1c3c3e1105018540b0743c1c2d41d400b01801040d41071001a12011001c2c0c8a000d620700244180d98850a40581041c07600d001c1203444007820758084200030240c00c00e84a0540ba5002c02c560600c20b1154802034640c80e09284207103a4003c60715a1040042520b0410807600300c81c0303200702101e0b09440c04011404010b8800c2c0c82d11030000e03040032441308651802e4060302c10b580c0d4110003e00707403061800c1300661550b84400702c102c400980300d10301051603a80074041110011360103c0356002500d00081c0e100d0308121641c10460550f070210030144003041400c3e690308402c50060002c4052904c54400607500030f9101802c0610b64410070412100044a114272054a00e000b51400106810a401c4519031070151510b642c1d95068100e0001381c00386800b10400781e02d1800610442d900d55100c4018004a0101e900b100f00030580015040e81181008d2095541c08280c5240c07035282c1070306110000740c19200d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 743285467 1250 743284217 743284229
    0x1c0b0307140f0a03150b0f010e0303160c090606080a05070f021506010516053723010e06010f0603090b182b020f0106031e0314070305090f010c0c 64
    0xb00c46246056100d400d10900a181c002c04000c1d101c1c048600000c000d80380e510341050040d80d010341c030416507500401c0c2241c0c1c481e00080c0950f051814140c4428035800007990b0940b881c4e1803c580c00680c4c165140302e000041d28a580c1c1c2d103039051030304001070b41c1920700103080743d02040201c443d1080d42c590301052404e00d0692464801e403060302c403100100c3c3e060103003a0146a025031b2007500c5108000d00010342c21050a4291000c4503109542070080017038011648080069840b603030010710000e10403034245102120000800d4840000f241d00180c03c441890035985000e5115400501100c004151518003d00583c6000e200b41c90007070341ca0007500341c006030000a200700404050603a6032818032800701660801d40d90980a5500d10000c043d9a1842d9000d03c03026008110322198440d8041c0640070550350082c51140000b03aa84841e016000c00c10380c0242c0400c540703191001415506000142101400307540c4182c0c84085940801c6416003c0b46403150502030120300860006803042da504c1c0807900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 743286717 1250 743285467 743285479
    0xe0639060711030904110408060f0c04060c0501020c0316140307080d050903070f03050a1202070c0501052a0a0b010e06030c10030209090c041a1216030605061c0b030714 74
    0x1050b005262660040c40b41d6144e00c0341c2003068507284c04080d040944100c482110881d400c1782c4844406800711003045e248554218400c01007445901d01071000516414807841c001846e10ba00300001c18156001000380d50f0b1808860724161703040c0084000315071444401c80010b0b61030106259645095845040c2503800350907114000100412000d1080c0d843d065045009960500c15a02d8000c06560040c845000442c006100a00c8266064401d6810459201d4142c440300c500740001550310f500808040b1800440400c421480045032074007842d0503070051402040030440510340410201c80503008004015410420048107940001e072503860010140c600c01610b20301d00b8400c030047d1140148803600b005814040c042007030000d00040c0102d409002080d2040001c14141c00f1591003260750846020302c04c6004264060342c8485c40c9407040c610b50900144480e0b680c80031a8660b0000d1903508461724001d007455003a41020b0150602c0c1d07aa0450207802110306000e9440841060000c006000700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 743287967 1250 743286717 743286737
    0x303070c230d030b03160b04090902060412080c0c0409030e0d17040b0304051203010501021e1509010902010815101107092c0a080412030e06390607 65
    0x3010103102480c400c000c00c1c00d44968071080d09015015084030b811445c000c0c4030b408241e40e0300d4920041034000f5a401059442d03e014135041807600908038551050303902c0340c020440003846000380e05260000d0b503c01c900e03160f09e8804040e0403e05055016440c0760107182484c0390307039000a622415540c412042107a0342c0445c621107007003120141090300c940c00e450360710000d004510210288082c2d441107118030120b8074888a182d1160009010a1090901503813041d0700d220300e861101d003031407040155108100c525501a42c00003454844082c0d07040c40d030310b943d40c0402c6015940e0111741e05a016040715420a00e000700b0381702043c0018608280e880400000d581800c49800701809450000d1420300014072000300c549000354041218480454150ba540c04251014444041418074859400800540c24949060380000c007110290808608008801c0000c004e0343d65001c0280c0510310061190344620114141c210075181c035001c01202c0c5844482041501d09000003d0540d44a0882d240c83d071482 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 743289217 1250 743287967 743288003
    0x302060426030a020a110d050d08041a010902072102060703020c070302040504030206060a15080c0f0d090b3111150409050a0c03020304030906050906090a14010306080303070c 77
    0x700e1144040009140400610403403110740c00070f000040300f4064518140c01c104608200144a0762010f4000c10035040b0b0240902180e00868199911901840030000310140640c0213540c40d9800f60000d5500d9507002c1100020f114507007041070103005621700c1c01240c44581c5c48010b50756200040100c0101a00041c0404440c0320502200703006607405002808541803501d0040e44907001114600e004049142c000105c0300c0c1004030719801b650351911200640d4071154008203035075004440700c17640c01c6401c11903401300b45401d10031900100c0c06541d440d0300c141025400076082d030f0168031580c4000058042182100013102d070100f85030742da005980060010703200010514100a041a0b0801c4000c04280007509a015820207441070507501401c111020a12609a0032800207550107000075507190702c18489140100003c180400c0000d12b0746003024202c03400140c60390100d4100003e0380d080c00d0503c1203656018080d2101070b00d50383d0080c1d070540c41c010600400040c0c0121015160401050340b08000e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 743290467 1250 743289217 743289269
    0x3060501020a020a0e27030a0e010206130803040f0b0a060602010e0313092d0f1b080a0e0718090209060105031b0307050f0a02010e060108191112070e0109140103020604 74
    0x10400032002c0251b0000b81440d964482e0426500c4601080002008001303640c80401c42c03920910050008050b420707900c1d200d070f411342c4d0001817040300d0740342004281001180c0c40f030400c54880e14040c1e001042942c10014000e0a40b0182c8841d2a02941306020380030314445002148400d442010780005104c45007490b0034480f25001141f1400b400801408800c0045040c0d0892034880e000380005101070316800f42010400900c0d002e44100141450b00460007064154002c0d0781d0100b6548110344580d40c84651400800e0001d41d5100c0e8440c1e130b40d120010450415421030740c4d10075401d080c03150442c80c0500720406682c1002ca80802d05007400000984440d001c3ea064546402644002580710003030f0603c042d00900b04c1e00720f2074001d031048200000324060002000c603100f110103000d03800e80c01c0c0556a04101e5070100a101a8003104504102c2c184242c2044454000c0a0303001241e219540760000c540c0840c3c80d011540c16546440b880144096103968085500321036086910640d404078030b07565424 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 743291717 1250 743290467 743290501
    0x2040902030f0f01150f0e0f120a0311010203070e0d030302070b010e0a0b0a0b0913090209270a021c050c09010902041401020f1b060f1903060501020a020a0e 69
    0x9445101000303000044811041c494426045490b62001d81d90f21694a0351440c1a00848540011600142c51000d0b40c8140c1849000600282140300d0400903000002d800412001a0010550100d00c00c1d0040c0350b0710880302d030071404035030000b180f45003000c0c10001c0426001e034090034040d00904440e682014841c0e411130700d1040d000090404a541c4440c2c0020100d14103480744070540382000300004452420f00c09003011250008001440c01c2d0316241407141d2200c0e0100000e1499070b84900404c0940c441c003200704e10482c820360307100340000f403031115018010813002c040b502075911030400c2c500140c65500d60200100c18101c1d1703042c1980d40130724181d460245203030740742030700002c2c08000002c103403049030090701c240c0380d8801d864100350311030400484c0e03a400c0c2c0040407045940f2003040d8480340900c248411075401c1000d08100e1400c204002e11350321603440344180481442d110400b00603500c5e0b01d4441e20028040c248050889000b20740c000a111740d4107402040c005411030004201c0019803041010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 743292967 1250 743291717 743291729
    0x1119020d0b041a0115270e0a06050612040204182604150908010c021209040e0c0d030e010f260702010f0c1d01030b060a0f050d0212060307050429040204 67
    0x4540d82c540c0c400d17929005105440c44082070604c03c00140e0140204030aa003400f20300400d0714030300c1d0b15100b091240800058480284c09541e00000b1903e52250b40050400c4402002d01e0341d22414644180002c40c0d9000e103001c00d007041c04449a00024082101003c4042c0c130340314074124065210088a0701c40c0c401c0e6840300710000d07a02100240e00580060440c1c0032504180000c1060800c04101aa11813a80c60640c4803480b0081181c40d1051400b0341c0403094046a40003203a01421440002c00c601c46500c04041d404203c510003a44190341c5c0c04030ba0241c030321040b444c1c641c0d4000001d50305003108000c4503200d02c9000c3e600c40c0005000600c00d6203d4064201402010f205616030a00060142c1c04141c200000d9040184a0701d91594024022602c0040010b025146800c401c1c1d04111051035030218001c082280c20024441850a42d0026001c0501d4034900021141007200415150240980c030203400785041400107000041d04035141240c2001d4040c01032180d101c1d0700000b500a2103240c0100e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 743294217 1250 743292967 743293013
    0x1f0b0f0d1d0604060609020405030a1401060812070b010501090e1317042304020a050406120204050a0e1e06030c040c110d080601120902150906090409031119020d0b04 73
    0x101d01035000018800f4003030350046100f04072240d00c0f103002e0010b03441207004070b9405034002c5240f180015002250815000382c06c3d400060001e03244d0f0906801c2c44a080b6600609110102e14802404080e00d9000e0041c182400e04050003440e100c1c00d8499020003c1c62903000c1c040342c18200c0c01740080b440302c002d680c0c1c80500045a40700e840f070f14084480c41490203c411604640100d5030b1041c2000c0c03084604030406501c5590030185014004c0b04c2080042d60707017000751602400005059150109010041c10452060003001d142c88032030750000d108045841c1c0c0e4544180418400b072501c01141540c501003050b40c000c500710882410940309040408011101c51040f8000c400390244c0c0311601c0d030300528003640c822429901e6112414140c2e40a910065840302ea008000c05600c004440100801c403806090141420030590014007103c540301c070140d011884071194030618070401d1160340405000d10800d258034008a40101d5510049103500800202c13400340841c003030054803c01031001e60500d07050707 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 743295467 1250 743294217 743294261
    0x91104020f1603081f0e0a1d070306020415020c0a05060c010e060c0a02010e0d0801140409150c120204030b011701140103110a0909030806090415060e1f0b0f0d 70
    0xb000740081400c84445c11004086009203040e941c01310035240071039103c60201115034540d25031610061600c0c140300e40c6142c200c0202c080f1000000d2081000a6026800c0140c4480c680cc0c0d8641400130103080c0b140854010454815065032040004000d45130250390711500d82c41c0202c1500d005140c01c41c407611081c0700341c02c10003601280b06c4008001c459001e5009010600d034600400c1d603107061103104900802d95890040c000e0000089040c040c6840c02407001c00d540c40a0f41b41c5010031000000746681d0315489a4901150f0350b0041a0180f9099283c0000c501d007514645640208107418010040040e4006000c1a0011025040407010201c4c8403081180740d6900e00d4003100100c0550401c0340a10350185000846203820321801c1a02605a161006c00d6510201004004200200215144a0080124407400589218040140044541d11243c0b41000c14403498012110035800d69a0244908140081c10072181610252003211011503100c6660440d41d801410030f03050303e01e90030210800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 743296717 1250 743295467 743295473
    0x22a0c13020c07050d030804080d092a140618190f06030506180103140709050a02040801050a060f360c110703020f0f03010219020105011503091104020f16 68
    0x401400304121290403250707665956414051003417044400540070540c00350006011819000003000400108040086c83e07001990300c0309000e440b01c00002c032400d901c80c10243c2c0349002020142e405441c14020590400d02402c00203409032240040a004070403c604082d106070310780300408501d2110201e000c130100d42e00c030720409892200301e100d9200024103000c0810a6424240d060084483c1d030308000c1d169580c255102c144c03e5a1a00c140000e10f8442c65000180060680c4545401070000c81e80150703480d0718081c3e40c1ca081d44c00141c40c0c0c240051801c04100001154803019404a6a11500c0e0202d451a83c92104548003010b0315190429111010401504025a030241241554548882108265421300c4954481440c00300a4010381c1e41403045280e4944800d8880e1501d0008001510700352415810b200300680c014140d40c0503070746440061190610400401a4200c4140790422064000f621000800c00010041c0c0c0e000350340c0000c0300c1c24000c104800300c03005820509801403880001340307 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 743297967 1250 743296717 743296721
    0x90c0503070b0702090f19090206120712060501170708130f0521180906030115081506010f05030705070305190216170c040f0204050a0f06030f022a0c13 67
    0x3c0ca040f44982c0061000601d110240d014480c020380c2146c1542401240600803c0d00800080c0000c3e82d0211041c0018680500518212031080e400b9684a1398090139184c8802d080d00c8581d00310754103124203008640040c008170300b19258000640d1030074400c00c1c1c4407540030458044010314050101e943c140480300c14094001803070012201c1100138521a6805102c45061602239901c102072030080b0903265000a180110086410010080000501c0c00c52030b0760340c500118855003d00c01a0b001180c4030102620b4803218a40e02001c2030030003904040c8071010080c0b0700d100007010f42090140125040317080c50301c0750741528032000c50100032078207801141c2070107503407004c040300c0445007118450381c00305a1411100490042910500c010010341002208201c09400d15103442714815609001c001540d59032030101c0ca00501c001a100142c0d46e00380240102560480c5403c00802c90040201c3e00304450f8403101042c04803a80d41d000d50384440107000407800c10100f210742c550b0207030051062b014900050307 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 743299217 1250 743297967 743297977
    0xf08010213060f0e2803050c030606060909130f06050106110d0518091302040c0c150606090522020c24010501020d050d061505030702060708090c04090c0503070b 71
    0x100581c0700005a6844080714141994440e942c000398940240300d142d4101061511000c14001080e80804440d5080b45911041550310903141a401800325030103a00b014022140c2042068030042d1070f06030b003000800d543e40009003980c0107442d0b107071164109001c480603c21442c645d0050b4103120550f03454030002c0c00b80c0c000001c4400c45020b213242281035680aa0200e0b030184114081d42000002500c0810107041d0009084c0c3c0021010140700c1001680c4621030040110543d440f80318000d0b4040c00d0060143c00d20a03400c5501070b241c02418010590090b095000b118400c0b10324102806058140f410590f01c0e44a20490301400842c141050290100c0c50101c40c8032140300c0301310101d09852030104140401c0c0310705805a0040c4025618062150004140001c3c440d235001c03543d513035134904d2032000ca1500004035000a0300401441000c540c144030168200a5500d802c4082c0c0c100300903a9a10340c8940004240302d03d40c1c8019100400400f038400c1d400400c4000e00f80e948950761000c2c00e000136400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 743300467 1250 743299217 743299237
    0x18030c0a0c03061d1e120c010507180e04020402160c0303030501080f0303160305070c080c010c09091b0e130504050307170a020d18090f090b09070608060f0a0f080102 73
    0x418030280b2466200000034403c001404004040d0070040b200c2d4503604188205e6010094001e10401c0c040030f82d9000300800804484100004491405c500000d00c01e451032070400071480071409003040704074040c0305603a4010b50129001640d0340a071010907081103540c038800038a110302c9200000103050f0154050f0b4100c1c0c07851001c2d11814118060501c0d00c80c842240c152100052010004421034440e80c07180c2c4c2d0010243c1045d0710314808a8030341003c66000089180f13902d0791140701029045038041000c40080180032405d00c8118514030303560840070f407541064020054612100b40c021782c0e40e0090005480358003001001141024188642c0381c0c0c2c0401c206407041105483d280c400c0244940c1101c40390881d070760240014031102d0404886c0ca00b103000400000d483c0354903001c1410300081c401d0386e40013007030100700203241c2e0458a4152034065004265800f5600301e034000f04107203034006007100d501000889080070054203c0000481e2006941c000c800010007000012800c000154010b060703080c9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 743301717 1250 743300467 743300471
    0x170a03030b01031103151809061006110a02040f0b04150e060604030b070e01090e070503040317060d080705030d020c0f010b0405130b04030e0306070e01091a0318030c0a0c0306 77
    0x4030100560580b04240d41001e140d140070400505d44011034000ca215441b40281003144142106500d000501c0040d104a076442d0000c1d82482400003212a141c00103000908000c16043c001028182d11411100c4008c1e028549840362a04120155409a81c04c060002c004020510840141e103003082c2e07440c0520030f000c0d6804000304465180401c00e4404599102e0f003890400d98600000701d0707141004110041c140000b181000ca00840c180074080c2c407d90a81e51160b44921709420020105039001d18560400d030b410105002090300c4080301004000d070400a030a0b0b41d40300b940b914501d14455440c05034013032403011582485001c1c0108600c0c080d00351400c002e00c62501d02d80104022100c095403030304040b00b19040a500041c50b9400103540c0103000e0704003030782d1414889000c00d0500800315040000074145201411066802100c5e13007000d021000505560720304032003c081d040744409031000303240b00200f4540c078811401c200b04031905c03805d03084152030b115a0340740382c0345c04e002819000032240a4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 743302967 1250 743301717 743301731
    0x30e0a0b1f05151806090d02010f031e0c02061e060d14070605040f0f05010c0f02060d06030c2603032208040621020309100c0c051606021903050919170a0303 69
    0x40350036000c1c0d546e50b88008115007402126a8015165004400694001c0c551907059484020313003424400300a51407035a40124a10801040082c141040240901d00c0c0702ea052003107c0b070032044071300c406a02c03c809843c010303448035040c00c00000c41007003180c410805100700a000302e100b59004005c0c0003150410070040f29541d440d8400d07105032140e0350051500040c1d8640056020031516100350350172600240202c2e01c0c295001d481c00098070880d410130382d4403c0103c842040743d1070b100c03100d0082180350f07a2241243c03100805078581e283d1102030041ca0300c00e004121091312580441d01c41000c0560f00181d81c60b580d41c0c0c0d03948003400400d1450007903072150b420401b004080036114000c580c401c11501020703000030705c80080f40c000140920460039041243c5900e04000107070041011050b1562580d5019510038a8030000920304508a103200e481c1180302200c520009420209a0b9410303102102e07400109008440440818001b550202c6201d4900c100f80040c0d046c2c0200310181a03034003d0350280040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 743304217 1250 743302967 743302969
    0xc031c0207050102030a0c06050a0b03060403032406022127150306010c02040f0e0307030e04061d0112030e06041404050f13020d1a0412030e0a0b1f051518 68
    0xe405454100d0011800c440d60001c0020216030245901c52b40c50b013800500400c480380428640300b07084900301c022039502c0d0903524410840180c42c804413240791000321076190421000944400c0036160354241e400c030790b00c0c105107000907a070280c034060701511800c90703182c0e5040c900002d0345c0e0b50703401e1480d03018440c0c000ca01d00d0700070f01d007004030313480b511060b1070b2401c0e0b0b9006507091000500002d6640700619690b15840302600405100411030140656034140040d24010304020441e040d5900a070404440707070540c1d164010000b00c8003411909684995803250506090990703200307440e03452503540030b00000343c0410040c00400100c1b4242d0402d407070820080e6668000d03400150701c1034400c4140307036074800c00c00d800618005500301c01c8039100e00b0002e66a2840c22096190040d02602c040360b5000409608410b02540f62042c503110300c50490050054010580315aa0358002c0948041c121800912482054a5450000d8801402d0103011320119040c0181602100d80110034040c0713811180d101c104407a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 743305467 1250 743304217 743304223
    0x903160f05150a081005030708100e0105040215160501090b070f0906080a020702060c0102030127050c12041406160207060806060a0f020a0c12060501090509100c020c031c0207050102 80
    0xb20400800c411440c15036400b10664003404014507070b038410072007041c0110340c0e510700f070040d10300a210342c01c005c06100501201c6541951480c07000745481d0b030f2400042002507601e0861041c1112802000143d4421a241380188a9414440041d01079820261411300b00b007049401c140c4200d44660302c8021868840008840c580360f0791007030600244000c404901e420000e6030041080750310003000685402e0a440001e401c0e6002680101c108140300c00803172040e0050b0350405041d80d034240d07000b0803151529254130f040303a01038a800178010343c0c0324000060801102240006086c14584101d40d01490b240b640081c480341020030240c0140501080020405d001da88510700502c8000d20807418400403a40c1120328148078a0b840003140304076003903900841d1011043c0c0380a010030520041c214003440c1080000c2c0d40041e80010b008030728000411000b842d020501070300480402e04003084803e00719074100d01c0c0468200d99079030705001351600d0050004004440004c24800d070340076610b89965460059031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 743306717 1250 743305467 743305489
    0x31606180f082103100302130914030712091d1b07061b020d080415110315030c0d02061911010e010501172a030a1e02090121020904080903160f05 64
    0x80d007040580d011b00040c545005800001c5407020030000303881601c1e464403040c405403405402d8282e0400110749060103a10148150f5071032042c00e144900034a02001c9c081140c0b02250601d40c00302003003022508158050b05040605003020154a031194900c1c289000141203e028004d0300e294610b108060a40c008281e840304040e2940b07420f85503555075281e5180c022040385440f1a80c541c2c0c0c404400582e0642c0c03020b940501d1074004a4100f018540080c0341c940b032020740081d4030502501200c640140d54413811900480d081d0150380c0c04184031640c1c2641c08d0326546078000e03d1035081048040021005602c41d60485210440b03200d4030380c09405285840d80618001405101c50000c4103180c1406002c6030141e20200207000c1710b1100d49d094980c00140c0308c4032451160207103500c0b1200415032900520f49800750414502c8805580a4411801d80c1100e80c200000c0c0941d1000c4c00040c05d2103c080d094490024000c0c1c01c0d038600c211901200c0b1203040c51400307003135101c01111401140c07a061500b03a185e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 743307967 1250 743306717 743306731
    0x901050709060503040507030b0106020f0609010b0a1206110a17010b03070c20030a0305030106110705030712020303090a080a1502181e0a09020c0c031606180f082103 73
    0x1c0d04160405608440d80c0c0e00c01030081d1400c2c46400303c0000042d09683d1968000c102a070701403e407541d80d0280c00d5040c40e4000d00142d15036070401480b0030180d074030302003164111065114040f140340300030714254016040702000758191031404611400e00d550003802c1003011081d079500c1408540e80320014220a8003064944000088685070030070001140015411242c01050030300c03002e0701d071450300040e14105600804600107040800100030040c0c100070700d0000d100148024246a9081001103135440c4000e100d81104142012850019500d080c070403500850400b41008090355201c8407a190785415514048658038000403405030101c50b24400d444602c0a103110301d2100d140070608015420b2050444a0300038071141c1c2d501d103016030b5502880c2005211044016846600c03c0003413030f08100052010501a13084041043d4221031130a03000c0f0191551400d111540c1040b210b23580c0310048481c1c002481e0041e50b00d1010409c0140058210581d0080e250070308034002c800882c60300346010035280c0c9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 743309217 1250 743307967 743307977
    0x8092e0b01020601142b03020d090501020f1f0b0d0807031103120a050406060b030f160c0f060e1641040504081c060509060306160e010c060501060e01030509010507 72
    0x91561804600020710300290b458070165074503080c1d05020306c241154000b1400340c0d04c058050102c3c0c903044084103000f0082400508603d180c503a00d100d80f2603241501d1200f00381965482174020300c031503a1000502c0480a400401c4100c194500302800340c3c003204d429004200d82d080259044c0c4000000c44a80c0501c00503090f410791a085103000241001400484815489030000b280010307070300020354410810342c0c49505090900c0e6a00d08200760380b012174101000001241080892000c000812543d64070201c0051000d813401422420448160840003c885501100040d44487d1000c040700e003c14003815003c09008607400c414000f80c071018500b00c20b1105640708041807400d0380c0080e80c07042c00380e0605464503000c500d04001304041c000440060721b5545105104508105843d035a0003501980100b0309804d2a540564904885000300030401c001d041c040d1501d648502144940564407180500c051f58640c5070240a0110042c001c0340042d00c6c2c403000030241704050103100e0040c1071303580b15 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 743310467 1250 743309217 743309249
    0x51f210e0f1e0304180e490509090a0b090f0711010b0a0303050904060902040f2108160314071104180c06050a210621050d08092e0b01020601 62
    0x340402424144c41c00b01c4160003800207c070b09440484182429102c40c0804148061344000e0388220010f820300340030b040c0b8580901f40184582d40020444001c85000c40710440141d0b1090030850184c07036526801d42d0040808801e100002e0b10540760309001b02e08a480b159060034031010320a080715074001c402640303d042071104101103401000144046a006030000c5595612411400140d0340581e025408600603030070200034006902500c5124401449524840900d503929120304602403540312295100c15503600307004140c0181d9070602d1001e1041c02d01c07501c0e403003142080f17840a280400300501031420050141150407010001c030300e060381d100300480500380c209681102c0e59000400c958007488034507840e55913103081410101112022508000c81e00318141042180c1a11b60b1011208444c0300b04024500001c07000f0401040c0754a55180450f4182e4a0100c0070b89000d03a407064001c8441c1e00c455048460410090b018081d81c6000d54040c02071808902c012a0381e0007007440b48900c02d02c40134030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 743311717 1250 743310467 743310509
    0x10905070315020d060f060e040506090f1018060509090d120b0f03070b07111909050402060d0c080f0c07110f0d0206040f051f210e0f1e0304 62
    0x4032800b0072001c442c40141481c150110711801c4030507a800100e102104140100040340c1e21640201040300181c409001505009012580d111000380c0402c54044a2400107400041d080703108a00809000c09400384240c25040080c00411a82c043c8a0190404074001000c0b503030b0001d8403c4d10340809540e00b0150b07081c080b111000a10721011701c96130229a20380700c003215a80811480300030742041602c09544e0720f12894a4a07441e00d0500c0c0b918001c0b50641c07022429500814008070840d00d55a1001c20903964920002e01c0c144039103002640005c0c81c020481c0940342d800060184100070010840480e03444a601903002409400c000400780c40c084072001400d41407803500e04800f10405000d04004030060342c0080e40640040d04003100800160000300b1584c5082d005840c101c159400c040074a002c10440c000b007003040582307a110010005a107a840030001582d0140d00b0104060064070782605001403225114940405030790140c80315905400202c003004011a012548040c0520441d507030002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 743312967 1250 743311717 743311733
    0x2106030606100e03070602030d0c03110403080d06030f06020c0d050f0912120406080901050c0406050919050301060b09011d011b030203040e070302071511042102130c110109050703 79
    0x30b1490041004140c01d0b00c40c3d5071002c0114101501e9031350003441d01c9400f550018030032111043d01d240105410400089680341000c1c048806480d04400459a81d80000740003402415080c3c0c00217145101403e040418082c0300d50140985284880a94003028510041180e41d402010003081c0d60440c1046040c059207040e55402c0d01d2003840c1f8050340d104c000e01300c00840f000d81040d8026008180c05404104c0c21400030303c41c159100504c04c40c1c25080a040c00001031103801050101802040b0201c2d0059140c03400c86018002094014000d011142e1180f50540c1c2642045040a021407000581442e00c200c100c3c004066240040e0340b20401803016003160103005144040540c1903000810021400038003c600e454032501f215240940d41e02001e24040e188044540701200300280b80400644010901908540c200c80e000004040c40705ca44c40741c040240590460021f40c000340a00c1d05c10301040441c1c1002d05542d00c1c0d500c8240d40c03030703110a8405007070340d00704c14000340540c00002042c00000c4a030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 743314217 1250 743312967 743312989
    0x60306072c03030706050f10260f010f06060314040b040f020d0c1203090501020a0506070e04020c01020301030f0c080f070506160b040308010315021c02090d02060a03022106030606 79
    0x32000c0200c03a00c10a0100f411a401110252440c5845504100880c414100f0007a0440700781613040c04518038102c9607641c07402101e11410704140c051054040010350402051011140000003084150b00c1450308030002c02d8607100d0303e0046418500b412810958800365184181e40128450720b482e0b94031b03907450649040c201000c03603205c5e904e64201c102144000307007010b010344650036a050300503081c1d00b005850035416600013030440d448040d040000072000300380c550300041c903801c2c400b080900c3c09001070068000c0d503000d0003044d0301c00320000090101000b034440955000c0d0581d5070a003915814000d803121512440c8460301d0b8000b00e0100a1130409038000c204008000b03891400246a0303550b04140c02c0402e56007580010300060051052101000310200742e100c0303a4908610300707000d02c11038200000d8150301d501c264641c00308401e0590380b01c020070311510a5005260b6552122030780303800350081d00142c01140e06c0607200361419040020b4501000d001e004000d000f0041955049e041280340001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 743315467 1250 743314217 743314277
    0xe0c01170a110c0f070e041101030c02070803071a0901060503030f0d06030f150b01020c2412070f1101050402010903020f0f045007170c1206030607 65
    0x10b0b4528844200c0c0740c010103040c00310f541c003000e8200c0e000000e00b000e15081054101030b0b03c1141c0007060000040c010382ca0940c00038000e08000c2001c45102000b40c3c11701c0003543c440f84844c0000240e8074208010103280c2e0304c00f10034540100b01c0d03a403110f0140ca401c854890080c41d806500c00c00007041c15401900c09811140000c0704c01249603516a600c0301041d245404085480702800c01581c00d0801450069240448082c030040c0101c050210010741004500c6016004030301c005e04030700ca00c40c10070200b1540c45902c82c0303d688413182444040240b0300c0e0368a4640c00d0000b0280b4000c480c4481040c040c00f801541c050307413240c0d029400c40d020080b45c0c0c03440f542e40f10350090003a504040c00f520349006001030908144041640c800b811014071007003100c4101c10884460f07081d00000c0340e100e04c500c41030b81000a03d0349a6481075036994015500c101c4d001c04280d0200d40b02c241004030014001c401004c504155081d0b109154a407002459528281034800d503000c182d40480700e9482290404025600c811 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 743316717 1250 743315467 743315471
    0xb0415080304031e240507030509030f0a03090606151803201201150501030608031903021309141014010206041101170f0a060b0a020c010507030e0603190e0c01170a 72
    0x203040d40c2c2e6011503450524498048400d40e090340e4175428081c0302c1c156125650341014045441d00c200c4442c0c50744507030001c0c00b01809001c078082101d680311750702007003403103912400400880d522094801c851040440c0850300040d240701e1101c094015440343c241c2120381c4030a00841280080c6460403c0b44d40d940b04558120310043d0300c5901408090258000c03443d01484110100c6080400050030364099401c004140d80c01045803a00c0c80244540c4204d03c1c0d50580340c0161100b06261641682d20441c0d405080500e0402d05203c5140c10b60103a081e000d9465000820301941c0e9035281420381c250104640740c05604605c001402080410503800c0411605241010b85010100200540f603d82664180300000c0f800040104800130791081401800c146c105041c2030500d60b100003943c032100100000d04201022501070b0030035000356104280858010040c45d12482d14882e0403085039900c10506050743d081c000e0030340e070040c00030500d10725010060755000f00201e0070000c01003c0110150980c00019 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 743317967 1250 743316717 743316773
    0xb0306101e0f12141015120c03020412081903141f09060603020702031203010302030307030536031b030705040e0709020406021c021501030f0302010e010509010b041508030403 77
    0xf00ca44603052501880340411007240c1409090118820070366049a401d018060252100c0c1603041801094100d80700640421890190038040f8040c1c091580545900710794070000384100065480078184800c150b8080d088108140c82c0c1c21002d541b2075082c400100032518000c1014009410035800044001c00ea03410101544c40d0005802c81d115a4040c034006a40482c1080440c81c090068203150001e24907480e042d94116000030341c9a00c01d20400134240100010381071405a00a0620000442035040360400020904002c030405800449100c0c03190281c0c00c5901004245802ca04404050260040a036142800280301c0104421785c80001c0920074191700280440300703400244044c2c8065406800d80c910b28045000e03c5140045c0722074195000803000400100384000c800c0d044035080f200d00201201181001e0f8014a0210800c0d2010f500700010170034610302c150000600b40b642620204429101071440c0500316030f042c018000c03950401c00042000c5580c12101d201d008500c0c0d02d040f200c030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 743319217 1250 743317967 743317997
    0x70f060209013509030c07060f0e09131a0c04050409081608070c0605091509060903061014010804050c012303130606090507092c010b0306101e0f 64
    0x2c2c26000c20071022030740000a8070500003400f554590308a0f480038000d6050225a425854554505006510421107250028080740d03201d03007c02c520808000e800d000036420040510401308018040a030703041c1c2c030390000040c0600b8402c80c9451081415100489c1450b0074102000040c1c0042541a15450b20903c0005940c48201800d242ca0314814284540e41d101507107041c0541c00210b43c08001481028000b541c0e040d100c42c05100e1030b00c00b075028441d80d1044400002540c0f070107904c01c815014803507541002190300d900034421080d40e0002c0c3e0405d103008042c00c01181c00117070445000f8a243c0000c0d00140241d40140c0c501103207480d096001004202c0704040072251034200316105510902101c4105003408131610950000e001220b07418000d034503284d40007510f40c0645208042182045118a190301d048441c82082003220741904540759507591141d1580030341042d100688a00d030b204440c1c1410a00a8800742c0c4807a00c07980341c54101d4090f25600383d8008000559910610011213071030108 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 743320467 1250 743319217 743319257
    0x1403060a030c121b0f05150408100e0f0712081b030313020427170f0d20070b190b0909150108030a14030a0f02040305060417070f06020901 61
    0x3d420300d01006030707691410382810425521180c400b0700d00b00319290014842c0030080c1c0c8016050754020344c4c0e11000c5141d076100815040c8180d41c00800705000b42c12492440b46116006000c0c0224030381d0440d150314030480c09060316032013a17200740e00425610494070000a13114201034817501211064549a400c52036021a0859204070f030043c9041200303050001c1189054801c0b03080a4500900c6480401c018110b8403074801d880e00009041c1c8030407841900202c00c410000c940a00c1e0b030201c1c40b29103030004408900d018042c0c54540c4424140c0e1a8014440a44103200303551595030050191751320703912001032200064071000751b6425600d0710380c05620b800c0c0e11004011402480303060018541068032003410b220050341030b04441c004c0e42003003003d80201d40c3c0c00548198450204900d00c1d41d40c0d00c1e02c000d8640140004554200d5050000c00c0010502502180062103903015036501610302e45540368580e030724401d00c140189105c0d040c120000c00f2480a03800340200c15418106aa4840342c030000d0450 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 743321717 1250 743320467 743320469
    0x31e020307080708010f030b010303050c101a0a0b0906040303051803010c08220809040b0307030f030507030809030a09180209040608011505010315060e010215040818010c031403060a030c 82
    0x400b0824040c14025000c1d403159010f4018281040f00e0240c090865440000e840010320010b020424081005403035158140010406151b000004012100661050290500b44140c266104207910400000d810140200721a401e8100409081c0b4141c250764040d180c40e003003a01c0c1c0c060340b0901d40000050030b071801d11903605100d20544a00c03500c0e1816010140d000c80c000d103440d0540f103500c0908040041c4503802903802901c0c0c1140c01091207168080420b183c00c2c203036400500700b005a081c0c60b90916401400400803603020307a440310750300d0b9074000000e5524071070800d141c000103150010030803003d02541c0e00c4c0088140d983c0009481c02804100240c10b031b44980c1c0001040c0d0350f494508880343c1da000c00c1104010403080c02c007441118401c003800c412098075442254203100c1c220500c0751030360b0300c24480c1084000d0b03040004441418982006403903500000307101e9001920092031f070308ca69070140105444959041ea610342c05a2070440d0400c00940000e445150800e98481010002840c9050190 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 743322967 1250 743321717 743321731
    0x312050c0a14030d0c0c0b04170705030f0c0f0d02030403020112240801150e06090a1b0e0f060c060a0c11030703170105010e03060106030c05070803070e0a06030606020d031e0203 78
    0x584c0700d40b031240386102140c005654010900192102440004202d100c2e09644036420162040c000c820000c81c80b503503449041c0000300b10740000075041a031010410301030710000c45d0300000c4644035486010115501c0d040001f1030782c05a032090000b0801588500c0d81c1100046100d18007023142d11016401600e1360004094100c00060943d406101640092242e00c2100b54144a4840c007545000100c030b0140f94003a116038010f04217880001d40d41101500006802040150345050707698045c84024000c40c0b5501032103111b091211066001440c1c084107481d6030000440c0601480e81f00c1340034080003040a0704400092040456103204980702c00d00142c070685d402915081c0070f40c403100f00e40501c40c940580040e41800004820240c1580f00001c0385415a209410b0014403d004548281d5140c0201d04000340644800420019215030280349c2c86c04400303040d9000e43c4900d442d500182c0580d00c0c240900e1005901c41049910a94400d07001000d201c200e0b2600b0b250074051a0042d0020b071b90044583c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 743324217 1250 743322967 743322973
    0xa0819061211011e0e1302130e01090c0e1c11310e07060f0909020f090102010c0c02013002040b0307230d021809040c05040f060312050c0a14 62
    0x7050441d40c100304101108140c030400301c03d1130405144081e0802580d203405901401d582c46070a0310b4100c0560480d1201410700384c110300515540c0c03850041f030700c07070034001c800c4c7e1a0706283c92449440c0c002c84181e000c100c0010100740078801049072010000e90208000d5801340c20f01024103605403151403035200b04603090005040b40300348901e07800c81102c0f441040144564500071996000c0540032805c14240c070000cbc41c107004001413400b0221070310701260300032131941e91001a00d0514150304c14010203a40b5000e0f0024040900349620558001c0b1507407801a0129075800410511a030040c00700030380165209a441c5511005245240b0032a0000c3d004616103590010500a281d0b8000040c500035000403481c1d02d4075481c1c48a420310303031800b405002e0a6800d401242071420032020302045000002e001d08807406500d42401d00d04d0040000e03224041c0141d2820944005511080c040e0b8801d50f40c01c00d18819801c03e06040c11900c903404031494185a020720440800025484101c0340400d01040000b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 743325467 1250 743324217 743324243
    0x10603050a0e1c180801020a02240f061003090609080c0c06040f03060f09060f0c0905010512010509070e0d050109120504030302192303120a020a08190612 68
    0xa250440e035490708611525409110a41c695608035488203031800d01c00d00c0c01c1c9220030038003011380314102541e81080c4842e5001044403000740c0d5002407030407010780000f030360f000461aa0580d9240000c01c141ca0603000c0141c1d07403000507030500304802903520038a05482c00042054242d101c004c01c449103a4812100103000298600140710200b28211707031084201c0e0107e2500745494040540c1d4103240c840106801e440d0003040030010b01c203901c0004083d4000105100303d0310014422001860310000a001003451410045140d502c2407090740c608101c0c000c00510940d08220800c0340500c0b004001c0f0081100c42000d41006454464503580b540f03100d400081035904c3e032460001c2607003140481000402500344805c0001c01d074000341c6401401050460310700024814100b485906201541b0310043c0c850303026008002d24030010052070f1465a000341b44089807035001304075050344036426801d000200005d0105110010789140800714211032400010003e03a0741555400c40d01203200700765199211022 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 743326717 1250 743325467 743325481
    0x30e060a08090d0302121801090b191a06160510060b180303030628030803070e011101060308071218090b010815090c161a18060403051b03090901060305 67
    0x1d00c1c501c03c1c045060550401c055128803032050b0800410055440300d6060040c201038400398000b2901c681c000103040710625003c50000901c40c1d41c02e12070202540351800c200320310741000661918441c80107003481e1074101003190082821510304401c3e00c150103095502100055280700d04002400c040c4c00d001c1d2990740c0d0010500c131030300c1c1c8900c0d010701030f8104008200ca5aa00c0c11040c81284c804007803c0042c064100a4540e041451908010b0184400000f0310035a0358200e2420750003450240c0c1e45503102140210718600741c80080c44000d110312000d205a00003d00110341c9400707810580c1c508100405040100300407400703025407083e0011541c2d80580f4243c5d580c02402c043d071040c1c504003644451004103001c2426070390014900000b2410106088504034280640c40c07090581240d160340788450750103201803207a5800d560182c2c1c440403190300740840c030b0408542e007446a80c2546541c0d007042812040c0009403c0d440c1c07139602040c0820410013101da641c074494240a021681c0e00000c0502e8054 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 743327967 1250 743326717 743326723
    0x6031002131206060302191d0c1b250f0b1c09060902150c0a020112090602030124090806070507020a050418030801081506210601080d020114160309030e060a0809 71
    0x50b41c69487c0303000c80005203e41c4001c04100702403c203e0201a00c0c0585c0c0742e1110700d4403406081d22680c50400080041c1644210004414081200168a090407035004c80340c900c811409500ca4550754032407074407040046482190241804800201c5600c1d00081c13455650000c035403e03000c00303c80045e1b440b00c0c1c0710107504052141c2e0344030101600045103800748181007140e490300c2440c8000e040180503500640e29a40c1900040700c40355100e281591a541c61b0503d0400c81c07503044151900c20800d103120701c99418450395070078040315124000360825844100048540e984000d00590b080319495800041a8446e4032a40700e00c4259900e801c8909480b07803030014046a0103038000202c542c4080b4218101c0780c03d0141407a041441114074034081d0f0100344660003500c001c900b11600701c1c05503000004400388085100145004aa0b00803c8041c0011111030862282070702c80c2d0501050703080248040074001e0f48030208450103828031050050003000000e06035031015445c1c4000031940350900002400c10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 743329217 1250 743327967 743327989
    0x110f22050a0207080d090c1d041101081017032a010c020c01170406091b080610030b0f0a0e12040807050303030702060c07080403020a06030e0d0806031002131206060302 74
    0x400301c02c1d031030030b2000d846040d81401803c0d500d495450b922a401020401c5000410008004883d03401c800e440545003c560107001c201c8043d664580700419200b1650700c103c10451142d490504004030550400d18003c485210a4014403540d100c02c1151650207403192410288103044101a1140b4141d0ba0b00c000b0700313585a200c103601c250b5100480451f541da0b0007030316080c0c541840c4242180300d9540da050280180c240d2090140a802e031503040340c1c1d54040d4041d92101602c1c1c19200704c840545a008040344140941e100240019400a011070f5052080c010340d02d4004d00c42d2a404079018038002107490500c4100681843c00c6407001808111034a8180218030084c501100914290700d485c0c030000c1c1d16200c00134130240c014140020301104000c3d00c0003d94015607005005c5403030355038031554050014074246100012600c6200c0300c4007402c40c46944401d22034603016018104290040c0c10a40c083d4010a1007541000091500403801c564142c4009859600440000c21024518014400c0da0004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 743330467 1250 743329217 743329231
    0x3240b010e03031c020d060605040f0e01030b061c1416170709020717030702010f0f05070c110105090d0b0a0e031905131214010b060412110f2205 64
    0x662034620825a07808000d0719a40600540301942034188448000300a200e030b030100c48502850311f0700104002d580000a0300c25110140d038482040e03134985903e078aa002e4244401070041104800064030303070408400049000c501c403200c285c40c0303003a143e0302c0010403641d440d41100103038408030301c0d80001205000d06800034840f0f03220701b1000d00700c100c0100d82c90341094005c030b080d11a00050102c040180121080d101c410f003000405882c0d0400c050000d01070708201507a0324000b41031025000e060103d500c220343c0140c0b041e88035a83c46403465130f40c0d10130400c901d00d440e90610000b40715070066504c5005181c0d854600c580c4c4504003501d08180301c03c0885a0404541c20030b0b500034401c0380201c5401d001807078101c4a0300d050998990030000071848a41000e900b1141c010480d52012000308500340e0b0125066510a00c000d001441159050003054045c0f882610782c641c407541140000f161006040d00301c80c2c2c0340603080000440a620101e04c8180d001c015410010900d0a504001c80c556442120b0300112 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 743331717 1250 743330467 743330477
    0xf070f0b07030536120d020406020607030b0d0219090606020106171603030819180203120a0f050d020c07030302161e03080307030f050717010803161b03240b01 70
    0x74140007100042c8440e00003040b642140e0f40c40c02010303420400545c146080750308007440d92a43d1000081011b5005445140050b01ca41070102d41d030319019010f030102413840070349422405015902002013411034040824819500428080b5102505020310320103086180c00104485240c0030303080851b1401500700c4003940d080b05400000040c0c10300340c40380490350146441e440c00d4580280b24490380c1384a00d4003681c5249421254058100b64585100b00240220f041d50f505802c00710a10003107200702c049e400b000413140040c03001110301403000350a144079034400060801001401c41e6103011215041075001d81d204c2c00602d20f01c2d8130342505100190642c0481d4800001d9a0400310103640203a000040050320b0202c00910154465442041b4040e41d0a00a200600b84184054850b01001c0030903074402071480c00116040100004a500155800c80e140811b03621540314005207482c401c0141507408101540000414140c0c801292406a4070083c0f03807140200400c098216000702c56000e043c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 743332967 1250 743331717 743331751
    0x609152306040e0915041211060906011203031b080f1b070303020a02010e010603140f060910090201050d0c05030105090f0610200304090c0f05070510020f070f0b070305 74
    0x307211503059608403003400044062031307120000c100c1e0420203581c1c81c80d0b9020b0802c1040005006480240400304607031501c1d002215080212210b4441500300c039150034942c8158010405080000381103081c1171301a1030300082001500204201c6c1050591000002551480c01d0200007280205807035042450310740040341022a4080601c032601501c0006400c0c540c1c0801c074422528000e402c51a038950003031000f00302a070389a1030a0b05c00d040c0c681c1c080c004140b180d0030044d481070500041182c01005100024181c0c00d0b840719010010b4220b8442c100c0c1080400e00c4103942c03010080c081e00002d0481c64a481e81c4035810030041c00001c40c802803894911a00c21007e00909444d072959003003500c055132800070140c0d800c10741000790b0641c50b100d0010480c03000107800030351281a0b500540094850f540c071301e542d4540d0804111003c0c00303040c42c06070090f0020340d001d841d1074005070700a14006402c400000d0074811a5151441c0101c00300d0800c1d038450742400200440305506100b003a0340503411000001d103031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 743334217 1250 743332967 743332969
    0x906021305010c110d0f0803090a060b0607051f060b04060e0315060607030c1b0806150405040803130318060c1b1206111204140f120307030b0406091523 67
    0x96165013071501d00a4800c604c03444240b05850601d403100300e80001c0307225a00d00f0040861a40c03040729000030b03240a498040000c4040c0741920032550141d42000c0100200310201c02203603a0340c3d190f8003048840990394480000c4082c2424041c1001700950348803500380300c0401050500f80301d14103039102c968402800070000c0e2035484000360380351a509031a18002410302c5281c5450440e8485003042512000b40c9000580d26a001512600c00d17900341d0f5010a02042d050107100507540c3c00d40c0c0042c114007040c00060725a03000d0f22080241e481c001d20b04081c00030400b58540103242401d0708a800000e00c1c005402c014040b0704444035002c8400c00d0b82c000c002c1c0385070040d111000c59140307400401c450b880300c4102c0a070f040070606480c0314121420841202e8101450172800f514141c044c1e00380c0d28000c0003440b18213804007040b03107507002c41034a01962565440003001c80c01800b802c2545540207550b940045800680c0d032040460491a0750000f41c01d40b81800c50140301244070740c0300819a40d44024450140e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 743335467 1250 743334217 743334233
    0x61701092d06090e0a17031f0b0d050709080705060d1e0b090f0610050309160801200301030c05010302090622051e010207061b05010906021305010c 65
    0x11a600390800040c4400601250107295840003680801040744100500c2144030725803011085811148041000c50164002991079007044d40c0058889140040c143c1100c03441c11000f0350707001d82c0319101038006030a03c0401c0d181140154000240301100840e0710010641c1c240700d400d42002032400e02b40d14540c07038084116034901c802d0044600800e004030700c64044c109960002c0e81400881e1682241e2048500b0000c0d0042851a0a03144207444110201b00032100a55180e4040c24000c1d1042002030030b003e00a88642d403001c1c01c42d0456129521100104501d01600500508003803030000c83c00040300d44000c0700c00c510b0750940946001e410801000011000c0084000702e40083c2005600c1e182040001100c0d40503030f00441e28940030302030403108001403081d0300c1c0082d07400458052032100b0416036130003509550b54105a000d07910440080c040d540c0141c455070030750754038852003840d06207460b9102820b48110190484080c0e8010a21640c032140c45440000541b4081c0ba04c0d902800494441e005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 743336717 1250 743335467 743335469
    0x4140f060105090d06020d0f0c17040b041a1501080916300c0801060b04050d02040b0f03010903120507020a0c290c0303070e3c04060e0907061701 64
    0x10501400048143d11503d074410030ba0049500414110744035a440c503510b0024004041140140c0b0340b034450b42450050007005038a001e102c0307410a039651643c480d070322a0070210000d0400c0d5111842604081020420f8002d4030341314900000d03c000e1340303035109000506000c41c040c0102d10030b0340008055000384100541c09030201c82112000d098010b0304150704002903d5040c1000c014145800032110602c4081104601180c0340180208401075884440b080507009600901394028918403001002d46800d4001801c0400c0c01801408030441c02d800180c21564410310403404100c080140841480f0340e8410103910840d0b13400035040c82d404c1641d42c2002204240148031244019400c10030700f424881d20203003103d441c60034a5994075280708160303e90325003003150100300181540c02c01041a090080300c0601d40200451800f41c0908a070301501c40e1907003140d220b6086401040600c0907541d8460081d40028105010990380d81d0070014403480c02c00d10b054003c0780038000c900800c0c0180c1c03402117003014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 743337967 1250 743336717 743336719
    0xb06210a110f0904060e0c070b0106021b0d03141804060503060411010f090b04030b16020f1f0f090b16080606160809040f0204060912050a290f0604140f06 68
    0x1c0d0340c403c480c000140081000e0341111074603007074800c200800c030b5402100030301043c3d003d402d4003030b030580c0d9032001240d03600e8600c002400c920b10b03a030b5050700c0c040c142640c086164901c681400512b0782d505030008c0a554202e60284001c00c029191207407050b040074071400f40604002d80c0900900d10b007d44034900c0302e240c0b0091035810002e6180c0e070782c3d1065118002c0c5a01522680109550780e540d02e04060315010026114181a03a81d01c040070b0f0b800b03030300004181e18000200340250402c2040a18404c8011102140c901c1104d0780b0b4058040c1305011a10410760968810421000310341428220008407045182c6404144140c2400b8040340355034140a9444000750903540380483e100e00c0c50051502c0c090f0003004c64005052580300c44100700740b60003800542d6001c1e03403030451241e40d41040000240000101404030b030001e585800210b00034005180681c0c0304071002c80811a179034000780c1c03029002161621500b039050014069140741a008010303220304086c0143c019414032414111b0341d004098681 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 743339217 1250 743337967 743337997
    0x20901030b0c070f060203100501020a0b07051b0a060e010e03030103150b0d1a0117120717130f05030c010915080a0b100309020a15020303070809010b06210a11 70
    0x105000000400c6403c01940501015095015850716902942040c0e442c90426290400080783c50351002546654541d000861540342da11551400d4900703a0040c00100c0d603000200e0a95402c0b41d40801581a400d03114040004440d20100b07895400c5460619403e00b140e0002c000402c089203103400d0b132071070517810307039500181c0040d10100052188001000040c0b1a14080b50a5a600341c000c542080c100c071a40010f616a101c607403103400e0f07200e155444810070b10900a0059001241142005c03699444822518502d007641c0303031240c00d40980c07040e80300a0341407602040c00e00c218141880010000d03942824590341c201e00b0044005035400c010034005041004441c00240307108100d812400030204080c1445284008250008019000c1c192069001c1c1c25409000030780482e280c1c44034003000202c2c3d1b024500310b841308401142e07a604050400341203036403101a03041300384c1d881c03030020000d02011003a807030040341465005075001e080080099030003c8c500030000d140b400c0c0c4070040303ca10728180c10744 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 743340467 1250 743339217 743339221
    0x10806010317191814032a190602010b040615050a0e3c010507030c0f080d020a110c1f140c0d02060f07090303050304020d0b090606040e0703020901030b 67
    0xa807011900075810056440b0720b240141183c420382040c1611000403185214001282c1c03201407a9201100c04140c40350158002e02c0c9002c0840403500004900c0001200e87d03452800020000900c0c07111403400c1103607061140d0340100301c059024460020b004a090350203020f02072130038001e140284c03d25200441030010005044c21940c0c800c04503540072241c010f0004040e52410250130390390304009449070414241550a1176040886e503041104200750594583e071800b1019541140d44166103001100e554084001c0000000e207200007411404100070301c01601c40e010300c44001c00d800d44820710745042d5006240311442c240c49400c0440581000040340180c5452250001c1341c0f103140201d034242244c84041008103010034081070000141e40d05500b02c900340d494000b092460300f0b02c1910120007103000480c0c1000042e01800242d640280024640304001e11a03455601c078161046a00d600160060710400c40d583c50144a0301d442000810014503100f429030f03000c03510000f41800050310344510400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 743341717 1250 743340467 743340503
    0xc13020c1e0a03050a170103060b03210f13031709100c031403070504050a09091101090b03072115032306130f0516090b0f09040f060b150309070e0108060103 69
    0x590311b041c019031946840303041d41e501e0500030300408421504a02c24040c2045a450010f0060160061014000001450703c013a111020100382c1c814810180102d40d003a0000001c50007002c01d004c011400310359441d6440c044030041000d03662242c2840c0c4107100b000c40e4800c02196000c1d6190360b40943e494030190b520707162010b040e5124040c5501c038075800718111074045211440c1b80c0114080510030380004441050400040d11040072074000d108072800d0510000707649a204400c4801039501d41e0400c00005107416000c02c05682d5407004850b107001280c070007081041000152781c4502c440311006804021040803610713072103a20141a002c4100950740d5904107000014613600341d00390b800310440310065204417100d000c880d464415010000c3c40c00039000e466040000340e00d10808002040d61848e43c0c3c4a0391181c01c0046601015100c40d0ba480d200d1190f684c40302c6403c0c0804200480c221a16441c3c03002d074031031826003141c00501214140d407004004034440060900e0640b60310000042807a12811 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 743342967 1250 743341717 743341727
    0xc0914090a0b031906050c070f060207020a0b07051b120d18080115140301111c11030a140a02040501091503141005130506030c0f030c13020c1e0a03050a 67
    0x40c0386985070048101e44c50740484107040001c141c5100f69028005940c1708260b94155010340c40010341b00403410280035001441645c000c000080c40200b4119030b86031105d1102d000c0e500402e0085034194003a05550042c96120341c80320442c21000c45900d20461485070410340c85441c0359010100b44403200080071514a0100a40c0d0050007240c0001c100c0081c06440c2c4107200501e41c85100d50603450b04100e44100d040601079800c100c8554440c05240c0407880d1200c102240b80304800c682c45070390361103480c410050000000d5000394951840070580c511222807044440c00041c068107000d83c4100b008212991f00401010101e4201c4e203281149001c0e0300b40190090100010380d50000e0485008000e03000b4035201d0314205980080d9005040b18004048032811290281e40250f45a4083e5010a003a894940140c41154102905550710780c00300c040400e55403410390b98448030064012500d58600d40301003000c040740441550741c2d440d200da2405000c588828860303601038100040080d9480c4998018 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 743344217 1250 743342967 743342981
    0xf0504200123040614030405070611011b090f052220031006080c0a021b030f03070606050103050c071101051602030a0c060207061404181107060f0c0914090a 69
    0x6190074034842069280c2c803500580c800e00071034000c07415644042408980c3d100540c0e01c1a64000f004045450410b0400e44802080b41103242503503491385500d2515803409508000c035008281c8490001600380002c90b1810781c1c007504034601450045602c00b04e0440d180148084c0030f07485c9a400100401c590040103144004d844140343c11440020501402d8071240600c2022a01ea0703a44152142c0c1b128194080e00744143c401404c0103070300018810769070100c407410444030705030300078215204162000d4480d070540d003088109403070702ca980ea40104001d50f0180542940b00700c0e005541890440e059484641d410b07440c4800c030f41007020200d56940e8070003c035242505001e1f002001ca03510524245442608a88107005403401030003141000160140a801c004c8103102610b10114185030070610034040d02ca840c000c45400240d201d0000041310244580185031082c0251800320300b66403400c00c1a4281d4142c000183c0c02c0003092101042040f101c0c0c6110002c81c801100c0030500c81e12113a160354090302030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 743345323 1106 743344217 743344247
    0x3080d060b19030c1e1205180307111309060e12040f0506131a0a0f050406090e0a0608031803010b0901050303070210020709090f060f05042001 63
    0x942141031941050b01c1c00101d94403004205c3d2950344542c41c441d8022a80010708101001d40901580d988010403003503154a03540d40c0c841055603480f4107200501910002e400220250760790080e01008141c00b81c03801d00c5031008a0815100614039a0800c90040c41072400d40c003242c840d800180c0702112002241110401e1418003032004c0c5510400010001080325a0041b507181400d0f00c00d0021b50306004030072500d51000f08800b90078010780140301c4041c4141480100103659014042c0d4042c5c03007440c2c4103851661901503114010f400c40c0e4101c081039000210760302001d45900e480d50100040114000c0c07100f504040240000124203000c0c0eaa01504104003034805070074041c041085030a807501c12541040d503a10f4428007216051030040340e180d15400780388803d10a03507005000500c3c403c81c80801c002d0809685401e04050007110481050030001c00c40c0c0490781c01045a8141d0f040307 = true := by decide +kernel

theorem cover : BRFrame.Cov 743165467 743345323 := by
  have h0 := BRFrame.cov_init 743165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 743165467 ≤ n) (h2 : n < 743345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
