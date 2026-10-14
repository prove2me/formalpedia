-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0784
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:45:55.11952+00:00
-- url     : https://prove2.me/submissions/17c31b2b-e772-45f0-8b4a-470148a66cc9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 140827338 ≤ n < 141007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 140828588 1250 140827338 140827343
    0x30c01030203130818030c09070e010e01051b0c101b060207050307050708030a0207091406040c0905100c020a050a030b0c0702010e060a030c080106050426010603050d26130602030a09 80
    0x400241094807000c00003807034005c0400c00d400700c4280075102404e00a40901c141c40582c041803072550429000e42c460302002811405c1803500780e00b01060350100b01c038130313030401c403248061074202c401c00c032417942441060594103003000d01d0095405034154064000035599070801415180d000030380c1009200f0704100302c51446500c082150001d035a82c18549440e504450403420040c040e20b00005002e90040c06403444115441e4008401c6032107407402c100040c40150b00075001d0000007000001e49030741e204820074400440f9100c507420a880780c1304000d0902d001d600064415450010144080340724120004d07808011003510584d18615400184c4081ea8046001c0c3d9004800164480e0050360640102e0500041900e8200d52a621000156400d000394010208a10028014660064407a40b2261740003220f4800000c1d40644035202e0f242002c1c5084919070116503204014902074206110241c001c14050000e42858107000a0300641000032000c09841d1a40106c0410a0701c00140d000d00070650303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 140829838 1250 140828588 140828603
    0x20d0b040503040608060307050f0f120607050426030405060d06030b07050d050f010522090c0f06020601150504050f030c210f150a18050106060207050a05040b030c0103020313 77
    0x10341441d00d5556540a401041d0002c2c8403400400c800742000103a101c16140000e104c2c595030203105040c8078043c203003103103400ea010326880c41c2150700744400c1c00b0a60140c04203986440d84d4508007100d10100c10341e000015070211810000050380d4040100070b50b010389504541e11aa1480342c0c1187d040500015000039203c401c0075014011081e4100008015016105106001a6448041503c3c0e280c0092040701d0300070001000f0755082c68001c60b01c80100696560002400d80c071152541d45803c260340d044910180081d0009000294040007a60700405159441c07644280542c0001881c60040d8400c06001d0340c0e000781980320555003408403101d00c00d005051042d51b5041000c056840da040301d45905094014841c801d44007080c0820302e202c03d40701c0b6000364034998440c20312410050240c540d05841031001c0850390000603100f030148a009040c03e6000702030300e0341840300300400e070700320303580058071032403070001c1101c25520045800c55859a003424010307240e58414490792106c1807030342c0c001022003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 140831088 1250 140829838 140829841
    0x30a03140c0d02010507091d0606130308040909020f030d020a020405040606090207030309060c231b0d020304090510230f0414160809061618121704150c020d0b 70
    0x202d43c154000c0d4411580b5582d41d500c03265175201030720708454034080480002000000003594a0030103800400d980003500c4030341c2c03002d82d54946a5403041d4000e50000f070000d580b80c3e04800254501508a00c0d00c0c0c0038120003800e1071802804c0c01030340e51400c604c402405544c551001605000b2035a00c00e100412858000307650b1440240741c000d0080451840c03c41c1c2c0d907407900b10098500d51017003c5601e25a000144024110481494038003c21303000644401103100d01c0c2c02d00010101d000303100104450310b954000f140c846092a16035070640c2c0e03008201c024410702c0d024041242200c074010119100c039401200200d00324420700403031400300a0010305078016090800e40440d650717442003006d2080c3c800066500314911004800c450315402038880884652019000c20303d0075666641940996403903060503194000305100705034000c412a03006041e60600706607000288485900e401076403001c05246030703103030034104409a0384c0d0768038886407402080a0142040c0842d207440d510b00c202c0755082180c00409 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 140832338 1250 140831088 140831113
    0x1120501080619020f09041812051b010209330301151701050d0311030d0f0c0e0d05030412030e280b04030c0308160c03031d01050405030a03140c 64
    0x80e00419100d0f014410450910034454042520030b8440d183e840d060032503d0700044030704100150420070b08141074000380701c91800018210200204030796260792211a01c8482c0500907106e480c2130203420020f44d0b4010000d19413a80d5542c14140903150520007520750f50701402c0c40e9072002024800444c5d10608000001144440c40c128440c1301f0515295100c08040c43c0302d0306c1a01c1104420b201c1c543c2c00182c0d00389000d0020f400354600d124090010740c1203038280400d83d100c200c1521b0910415040c1d460b42da901c0d103002035074006071458101e007060742d090b410b105080e41c4641da030340319a01c41c009500307c40303581843c1010710a000c082d50708040100b02d5080748c042e00c0215601101117001c65012003c0440e00014a482d002040c1e50459410581c10b0040c03070700e146c445420a030b011001c403190031551230021000048807842d01c000613601a545060f45e13148881d4809400d0740c07130305500704e041c4001480204006e607000500d40c0d09207640b52034210000b00058a40203030354042c00428519600420028030f04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 140833588 1250 140832338 140832343
    0x110c0406080102092106010902071b120605070f0c11010309080d060501090f06230706090f15110313020d0b01270c0203090108041704030f0605010803040e010e060112050108 76
    0x140302c9130494040080c406422905400b1440158000110360000c1004003d045c0385540582800390042c0441402c2c1c020741144486004402c3e00700d0f907014500440300c80b084c00310074802d651340142c40e801c001e54003c000707000c040d10001000b0402880401d0b021140d07500c99200e40c200500450303000f03911580352601c040342800a00000c5c042c0c140083d500800004030030313003000c42880850380651982809100c001100d0740042481d40701c84004200c007000500c00087c040e00c102036109024844861645409245c50040c00b0409500340e003240c0d04041060b0000700d80c2804070394111511030104c0402c0501840829901d40f20b0030380140c042005000005400007510004201070840c40481443c00002d12044200700d030f640d1000480180d03c140440169035005548694100c1d004011101410b0b000c510b40011030350281d001111003192404c00079040081500440d8054007642003d18102401c0c4440311030003280505c07403040f8800c5240301280003a4021500c2d444491072075817042c0480e42c0c440817a9075 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 140834838 1250 140833588 140833597
    0x20f07090615020c01120506010e100206070e01140901080619030c0f050103050c04050907110f0d2604080d0e0a030f08130c0b0c07080f0607020f06040506010303110c0406080102 78
    0x44191000624502c8840d101150240010300b058440500c1128801079030001054014001410301003507120f601840c0d034600c2890900d1902650061080d03180665004080341c04141480d41070010081c0303c103410b482c0c01003e4840303046080c0703000005947c4040028040c0c54141094420307254142c0d0f404014030101e40b68074001c2c0c031034810030400c0403503441c001101154030454003080100e40134401401203142400200c1c0d000030540c41d0203490304003491100d03800c0071801d0040301c40c50350024511807171180c1c00031003141c8421115014906240070140c007032180418000c000410504c070008060382e0501c207940c070001c902600d40085449140e030924014105508130403501e00458407920009a01210014890948a0307008200d6041145806088451a00400c0142d1040d01a0403008185050104103c8500c500b07404001d040a04040700043d0504a0090924916030403010400001c6800040e207603044960500e0b095145000d4040e2045c145220369060a52081c01c10350005000c603070540280 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 140836088 1250 140834838 140834849
    0x60a09051c1b0b0409020d020714010501060e01090312210e060114060c120c0f151509040c1a0904140a1803020601050d06060512070303140306061801020f070906 71
    0x441010780151607402c8190380b03d2240300074900742088180300010751500505040c2d19502000742c201807250383c0b8070b44403045042c21b01d4a941e5490340100405588841d407480b20410a0030032081e09400e54441c62101d2015401074024003c4145044d00d08030003000c2d000703440c60809c410070007140022194603501d60200b17100c0d882c0c0500300400c0217140c500d052421150032600032002014040a141c080701481d4001d85500703c500d000d0080e0010a481081c009107103180761203030005c18985414441400c651000c070030494051584881003200290300c0d03410f41d0041e2003003076084130408104403060051901c5140101034100d414881d41513043c1341c21200b50344c001c03140001c0500c2843e45841c0a04848000c2804c050010780c4194010882800d1102010b11840e00485011510585400104100300700701c0001c900306500c007042c10801d055100050034009803100103210b266003001070028140e8003a004c07280030034407403001c4c00064070381c000c00510f01c060744580207884031030740e80740b1542d40201803c1c4a403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 140837338 1250 140836088 140836103
    0x305060312120f04031824050c0c0904151401090f020703170603160905150618040b0406031217062d04140106110111030403020a03120f06030605180705090105060a09051c 75
    0x1220b180d9802303402a55a0094604000c1c041000081304000042d10701810a0751418042c00702214803035080c3c003400e22162942c03074002000794036254411003240c00e08801c20030010b2041c003e80c3c001941c00b14100d0304c03da00703200404111f9140c0100123805c1100703550501d01c0581400400040d42003941e00400d02c03414811f401c440c140080202481154481c1d000c4c001020600342a05003d2071a01d40e00040d410100644002041c1d5101d03a41c4e00d07100030050080c42d001c540340100300031600c5c240104055100400b580c03c0c0605d89204010325510503110380e8000140c5140800009844d110f5900081050310803028a0501c1d503900d800141050010b28401d0b004c55003481200e000c800c55080c201c900595159000f13011410054404581d41010328280740842500d038048240300b8a900e0003011b010b14080c1000054178145805c00c22030498501c10381101035041840100815a40c41203c04d0442c3c0c01a40c00e1940c0b015007110480d640341c43c0c1c0d00110b0380014000c4094094000a50305910540d00c80d060 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 140838588 1250 140837338 140837399
    0x907030b04052d0613020a0908030403050309130b030316140a0b0106020f060f06040b0102190c0e0f240307090912091e05010518030105070305060312120f040318 71
    0x3240c02c003c0c0d000b1900c0341d40100301000c0040b01c480c00c1d03500400504d40c05240400900381c8a00c000d034155030040d441965941e1001c203c80768a450003d80c51204000c40c04002c0102d1159800400c0e100d004526a514a41b500e4040380e605010700800c2d2005840700e92010742d140360200f8039204603000800e01030f56006200703006425104500016249000d00c08801410565681d88000c10014280c03114119046018410040310b400c644e0145003014907204401e2900003130708000000181010081c00c0e225410f8150301400f0317425801e4139203015a07054132009440741000c40c40103e07280803110750150980c00c0c50183c070301e0240152320910540700d0145940e28102141d44145402f501c640300a54807042d910245420401903002e40002c1415194030710001c85201d00380d10009085604c1200d046000c26210410480145020301c5010050070001ca150303400d002c400744180c0010300000b000020440b8000010405050091200000550421003000754082d02d840280700045081500d45044050110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 140839838 1250 140838588 140838661
    0xc0503011811092701080111070f0c03150209090714030615190201020d0b0a030c06050a0216060e210d0c050a060516170f13060e070f1e05010e0907030b0405 69
    0x1230002420005903541d00300304003915090042c2400d00011030f445d03028800c000002804454052859110035034006840d842c6103402c1c04a42c6100a201104120b000a1500100c000550a51b03400401c01c0e500c04604217880c2c0c10244561068003c000d1501445280000c0e0107a41500107111602d2003180074000702110a00340499a0400e0000a102e0034480c5800c1c421944548060704992a0030301c11220103418202d40960003600c26009000060b1620851551a0900d0900d10920b0006420846400345403120440d45031040052500100700021020030300744081001a0320700307150849410011420300c45003581a25541800c01008503024002860344182001031092290b1090038a11601d955580d020100344035a02d502160310300d980704201180301400304011300203007015041404c00c041c1000000300c5a100a0580041e01d0055420705200380d9074080c1040700000e48c103842494160711408805c0e0090031a26036040d402a1805e820030114030305038420040311920b180309a5441c0b00c240c5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 140841088 1250 140839838 140839841
    0xb0a0b13090b1008150a0e0402101d10050408012c07080c0103090501090b0c04051203190f020f1605090f090c0603070311040305010509010c05030118110927010801 72
    0x121191944850340c072610b06541400f4184c0190b00101000320014038084041c001911400c1642001c00036010391403c002c21070500030a54600c10140e0300340000740c0d08255241003002500e111216000300b014040385440180070f070b41540c01400403803000f4054540d14244d642000c050102c0044900d000c0304001407100d0001103006170903148034a0141c40070f4698a001513016081e05a003c40d00c0d03640c3d802c00038010600b5280498055101048243ea43e28904070401101424071103101a807a0010071244500c0c0184091400901d181410107020b40301885c00e09900748800943d0100d003d001d11120703410b43c0c04a031583c00c015514201c801c0c08071900c800261040400b030407203a001c15030344411607100241c980f6002450b48a01c6514001c00d4078400080c0310020307a001607104442070380d1202c0500c0784003c028000c0e02c0700118a85000c034119850003954104d000d110783c2d4020394846c1c0e0382c01c000c2060303008101200c04081010308215203400c00881c0c90303400c1c044020104002a441c0e03500100e06414107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 140842338 1250 140841088 140841101
    0xe0109080309090403140a030c030b0301151a040f0b04090c050f0d24060206090f0c01020618070f0b09030106080316060209040221040605010e040b0103060203060102010b0a0b1309 79
    0x80034010350070300c000ba105000d980000500181c0c240450301e00c2e050420f20036130f030080003030003065900400c00350003804020b011758a02001c140d04c284d0402e402200b4036000e010b1001c0403610a03290501034a024001e0b000420300c074a810000c443c0654103404650340018500500c21120000810483c100059200300c90900035000d0404802600304600d0020424642010140c01d00da0b42e0320710f03200c034981d043c00c10f684d01180e400400940c21440400000e141c091105140400412018101e80700d51040000e48980c07005000c802b145140c18107440000e00300b000064041c08261245c5042c654580c00412480c1d044018094425800c1810105603120040300303640020414440b00e080d0044150340d40c0019410500500390055800e1002d0006e0300d1882550303402e581490f030380c0401da41c10075091560950340140c20100324101c01d44140000121004065411a41c02040040c1c070780d110140100e001d0315006840c15840111a07601042d00c000400081032441c000001c20172034265522401e0094900 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 140843588 1250 140842338 140842349
    0x20f060a150e0a06091e060801091106031003020d0b0901051b091c060603030507051506031c300606031a01030b03070b030a02030a0c0507150e0f03030c0a0e0109 71
    0xe20501c200014090710040941000081d50041410b5482c0c91006045924101948a0071141540060008030f403610175180a404078a00a2145100c00e4803980c003500403100c015406034070000005107108040d601008081c40c0c1c0105860300c880ca0318108440c0710b48098440f56107551030300004c0307000b00d00d0b031010184c0c0300440b4080c80c50402c610f920400a800381d00500107419401032540c607000207807241c803c0740b01451207500d5460b20307003070241001454514900c101c1d0a40008400c20b00400d17642c000341341504401d00300b120482c250100f003801c0701d24240d001210204c4070903a40003402000722280e230080381600100c004005407680c0e11000c4059664040c5007100ca60052401070100354402d40102e01d15400150855002d641d68103289041684222004210b96502005100252000307020f84c0980e40039034134066040104685800300c540c440d801076140420f0350344a00b401d040000740408180881c0e8a02036030740380c0c84c02c401c15155035849a235017800000d0300b1100c20000e940c003860511003030741d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 140844838 1250 140843588 140843621
    0x1808010e0a062403081b030c0105040302070e0c0d3b010f0c090302041d06101e030b060d0c15020606190f06140d061409060405130f170a020f060a 64
    0x4c1c83c5445081ca582d1001424000c4151918500b03c48040200010042040d04100004161800f410024203002d210f0b0408880180d000b0140600444007609942170021108000110340e0070002c1500078150942d40ca013040034100008251810340040b401e80004140c80c6c0090000000121030703801103600680c0d036100462803200d028030150805c0d0344a6004c01c1e00c0d402c9000015044046e03074918004d8112000c00c00201500428011980144416089241280d095580d07150844e62a202c00c140c00030238480c0200e0b8000d44000a1181d6009580001c0080268040350203814a10007510b8420840d2a10701404d603480460204c0c480041e181000c03200460313540400c9a003030800890388180140c0304d0b0b0010f000c050040200444440c42060014003101d040302d4030f0004220709120744e4020003010184280e00d81010012074401c0c510003c00800c5c6c0c45000454000346601c0c0440007200b1000385030132040404200740303003056000031360b80043c020381c035041316080d03a034081f220713010b683c2c040c41907803a20b5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 140846088 1250 140844838 140844911
    0x50a0e0c130e0a061b03061d0a0902010c0210051b06010e040210030b0310090605090d02030d0b01170901050403081b09092815060302040b09011808010e0a06 69
    0x40c07a164403500320b11650405540c142c2089860b1041076401c00003000100480c0c150001103580e8152289200078403c2c0385000c81c00a404030b00c0e840b11240014000e150f03064880c0c1c6034004581c421014411400c1e0b0041c1a2404501400d00c020000e800808a0320207a2a160051244412000600a040350080504d129181c1e40c2c036402c0c8400c800d070380e061160506407202044450740d5018011400300d00c5441c0000070b5291482c1c2006002e40d4005403142d0b0642e0032030b2064a02c43d95021003100c01509007594082040038207140101c0d0468081407401c49402411750900130103400c1904014000c5000e07940340301107920b030781040115641041d4508603141204011203901418907000940d400900c02403401d03260759a0203410700c00c00136604203842d007490b91030002183e9980010850005050b03d45004c50602d03042000d81c000394800d07500c00c0c03810320002d0302c600007030400f900c041c54010300f1104000b405484201d241d5030356245141c00c4110f60450030101202076480b141002034020003020000340019 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 140847338 1250 140846088 140846119
    0x20303040512030d02160b15031213080109080a08010f06050315010915030507180b070b0a0605030d0203132c191a0a0f030503030a020a0504050d06050a0e0c 69
    0x7002d8100080340203404188403250000d802440900a8004698400e40740c11049281070340f00c8400c0100380d9083d2031030103040c2012a4400203070009540d0950001c040d40d03a203640801e034543e9140d60340902190742c2020503040c1080300440c0075003201005038036220300d141d8845a0040c4210f1403801494001201400020120040040c045200300018102180c00c00d80325550310081c0411880c005001c00d031690248456642d02002c545402c250040000038151704003407068601d4819004050300622014002c1102c041c15544008001c1c900102211040301030044042c0d200d070404048540e011008100000e00440e80c0449820f4140e04480c250101d100c18900c0c0d440d0603203000c2d18900501304c88150803a00800d03d403107414044890301845d8520f1406000c1000303801038941c0c01c01c0d8501c0f080042c0030400914000203694101c0c1d801d600c0961104080d45c4112910301a551199034085c0d41800d4500601c01c040e030020303000704000f00c0184134440c01f0700704159a40014454194010b5240304640e6030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 140848588 1250 140847338 140847349
    0x206010b1e090402070f0b0601020f100b0f03030705070f0f0501200a080408030c060606070b0105120a0c060509030c010c02091909060f0b12010e0c100201020d051503190203030405 79
    0x10400350110515082c600080081001c03a006041e0403508246015032070000d00c410303002000ea0020003440246418000c142e02c1c191543d1100c030b41c540d11103484000326802c560383c2950035a6202d2016007101c0c2c40d50301ca801d0841d0b50b09058811907143c1d00c0d4514001c11300a06035840300080c0d40e0180c40d041f0741000690124400e195005080c4122801601c00d80800038203400000c10007400c024000350707118003000f0000740c14040701500041c4180d40c10802400011954800320f41191030480e2034640c6040181405400c08003245402419200340a40c08223005401402810040c003013a8102d482e048030003801510721500c540e00295020381403100064001c07424601940e64451024004259540d05036105800d6030801c1c000440d80c15102c030140c1c000c50814040c121041d000c200000d11441030030601464441004d005081d0198042c003003050b50780c90017501115103810303442000700301e00d141030a003002910854650381131090003403800360328000416681c420859074008000e0352500b880d00c000c000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 140849838 1250 140848588 140848627
    0xa080315030f0c130b0f10050408060a1401080a020d0b060402070f0f020306070c0b063c0a09020a02150a060f08060411060a0c0f050102041e0509070206010b 69
    0x200d4020001044081074500b4004a0410003001000300401c4081c24104481d1500b0004c0451400f80b034490143c0f170603640c991240360008810340700580040c131666811581449250040c074000e226580600086035107503400b00000c23030241004917641da600c41d000c0790b0701d03515030b804007a511014040d805804030b5503550046401c81d10040005150803c0c66844884482000e40252100400820f140040d81070500000340c0c004118513112a01003c150344502d160300700502141d004614040c0350389013922000c0800002d40d4881605026000c852000991008600060440c09102c82820014071a134103802a926050350a4010300b19820002001c0c904405c40204000c02e01c6445080020781480e14040c3c1c00040c0c14410701070102880d00b03040ca00700180d94102824000e0908108509400340d0201c0301410031075000c4000103051140c0e0410706e01902858002a9034480090000c1407a50441888074003110b00c00c0d80c0080131170f929401c0c241e031110000d21132039a0500c81040312602031170300b455804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 140851088 1250 140849838 140849851
    0x1116080c0f19030503030126030706020904180f0c14060a081b030405150106050702060f0d0e01022b0903080105060304080c01020a0306170a0507050607050114040305121302030a0803 80
    0x1000382e48044500d00615120690068885070400001407148443e9081c0880035041e4140913000340030324501c07a0603079030300c54030502601c01e99000c502c04000c0e59894003e41c10849600ba00d00c2402c2c101d07801d191511164500003218001030010b40018038844090b6620850a0000d0809081c030086a9059480010080941408200300c0281200c01d6140c00040d601950041005011140503e115041d40325010f0f004001888070038403220005907603080c200e41e250070124120310740705c2c88000c0440002d40400b03040d01002c0e5001158803041c03055440c26000080c03c03080e0382d00c0c0365003071880d80300c90071183c002c28080c00040c1500b00511150801030000c542140c454019189012034210055089130065000540041e44030282000401d00358003141518181b000081c0ca40c0b40c4895540d06d640d0f907518402e05002e0700000c81d6610900c0303829888640b882001c7d0f90301095616141c5001046648803aa900c043c2c400b011010600090207a1780303803082198050003d01040c002615400100c0d00003c084 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 140852338 1250 140851088 140851099
    0x6040b040f0513020109060503090d03020a0302130b03060a0e0942040b090d0806010806040609060b0403021503070801060e280504271401090b071116080c0f 69
    0x34840074000c91091501c1002051411000500184001411100580c0c8000c040205c10300074411030340790100d40f1004c0c82c8814180103075200041c0e10260040d0040d4440d0203800c020170b280c00949540f402004600c52002101c50f246401d440d18501c42d420360382a1084c0400780e03c0002d070204450203c9900034091081c0d105004000041811001d0000407120349841035800407071300748001c0290801c0c5c92a00005004050221042104130044c02040c00800c01410480341c1c0c0c1c080f03000ca03281c507804040a0402c83c002800400e44521800c92940e20034401240500702c04031040c4229022401900c0c001c0c1841da86844050f4030b8918110341c14080050207561049071052207242c02080200084001500031080300c0106140400b0402103900101690110380501480000e00407040120703020a582d11941e402c0305049000030090042074607010003013041c0e0803102400380d07450b04464400d00c4d00201c14101d8081c0c5080e070b00a11380d03091051180c08100da000343c20016040ca0407003500c1043c441e01806 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 140853588 1250 140852338 140852351
    0x370c02030f03100302041409060601180f08070f08160312050f042402010204050f01201e0106080106180915020a0e010905030705010807050310080703060e1504080306040b04 76
    0x312156005983e07a00c0c0d030720070102c0c0800440c02c041c040e0901d6441203000716905460314041c242e84603d00142035030f040144443c54819640d81c007030b00c403202400da13043c040d04516444040b11076480c0780034001c12000350854100000c1e22540040c402210025210307200d040c892443d6a1907d4510b00c00c052401400000e0202c802401407101c00742004004240c0d5042d6424510f4031400240300e0881000d00841e401040140043d4880c481c0410f0310141c00e180c040802060500d210b850240002c10031481805202000c1d10b0150711128076041e0b8a140710002c0000c9075840c0744141c22034400b8860b400316107001c40301d091854070441e80003259460044444807a5204060141d600306d074084d0f40c0210104081200010b455644081040041c00c42540149511401c0c080003030580c0320014420000c1040000003d049034046200080c010252081101c2c1655184d241a101910054501d842c02d0f20034490200e00040c0700c101d4440c02a5007050400f49151103403c203110181c600c411800c0e0300685c41c0c58 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 140854838 1250 140853588 140853607
    0x3090a020d080306040c030605151c0e010902011701060206060904020303071212060509152b0b01090c2c121203040c06050c06150f0306040506370c0203 67
    0x900704071005100d0014941d4a1070981c0401044541107902542014039102e02802552a4884030f00c01c140c01c4210607030784410a5881c0c40720000303500254000d605040418108140701c0540140c0d035240e200746c0f19248145808040e4a40c0302c00f09105400050740080b0103c1e04a0602200e565000350010342074038a041090307161102050b228028441c00218014440401480180329500241a040380c850b851030030700e03201881c441c0589510052117140581c1c0300d485c0352000c230310340f00100c0001440d00d500003a003141420b152900007445940145405c250415068034400c0c1c60441640302001400c40c08025520651001510250321813030300907080500e000c903012810442c0602d00c0c030300240125605e1809281002040d40d8551000c401d000b030038000000d5001010074000c2d4013203184074440300420200000107240c0b0b00340c4060940c05000c1c0303005220900c00c011408500ca5803481d0440341004070030b000c650516840224500042184c803446080007102550810101b040c07662048030b003000500c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 140856088 1250 140854838 140854849
    0x3220807021801090501050105090d0213090b01060306150804021f0210020c01020d110a02330703020306120d050406110c220f06030c090903020703120504060e030c0604030803090a02 80
    0xb40c40d04002000e004004000490083c84d0140c4820b107402c0c0c3c20300b070b401000b14a20034003242009114011a10200c5008440c0e43c0c445c00c401c54100c40400c0070340d41c2d0351401400903e101d0041c50194501c1501340c8100501a003205e600aa030302400464011a020301044a50710f4072140250840c010700d50340c9005e040c0e00e40060b0030403a911400059171420f031010100c007210385545004036115414043c0404154000c6100030704200e001c00c110400f4000f1f11004402400000c19900040d880441800300a039415805184120001d807240030361329589005450b920b41038642440d0019004000500900c1c2c49542c20340840640c1c442100e06002200002800c0c1f800e000c4120400d181910404d6020240c3c3c9021342c0203481703918001000364900b19100e007001004103006800c409038884070f4150405108100e00c2d00299003000404845400744a0f00030141d612910404000030709040700301c246440c000c2074000071010018003403032400c0c0c80c580d030b103070451f40008000c2071482c040c185162000d600d40c0d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 140857338 1250 140856088 140856109
    0x30f070c0b0a2a020f16030b0601110a05150a050a060803090d08040305120901080a0507081b0c1e0f0105010e072d0306090c210b060f0c0a03080c0322080702 69
    0x5030044c00200003440d91946c41c0940e100c001c900008216102000400e00803905290040f90a20b003030b0700c1c41201c000302c5516003418944014407134802c00b805082c001555140031030040308081c109104944400b0b0004045d25494010090b0b00d4100308004040e52405070716a0810510502c0139a0400c3d5a0345c07540f60501c03820511254405c42c000540320441d40e4809800c0b640a80d02d0368080040d0b0911140060403a10f0042400070041d00d00400c00a15640000c15140d40c0302064045450311038038103c1c1002500000781c0c0c280c54a204080c00042c0324041030180300e0585070070341144c02c040e654284088450722082011000709440b0701c20703030401c080d0700c0a01d200742c3d01e9401d840100d8a94074010865044555026000b82003105080d080c05110b000002002c40038200c0310408100c0650410006a0610921610000a100000f0810301c441c10102e8070003201402900c80c1055a995141400c05c079100481c0c1b0105a81c80031805620088482c2c0c2040c24810301480c1041e007414001d0340030500c410748 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 140858588 1250 140857338 140857421
    0x140a080c1b0a0b091203070f05030a1119030e070305280f0303020a0806100c06090510091a13080d1802040f02130803040602121c02040b030f070c0b0a 66
    0x83c4020846055420000204024909961a8651b01c2c0000f401004050302d21401c03401c0000000100d428005240c01007541d09403000c4445686c4d466840b400c00c0c00c911700c00710643c0860b04045095110f0000801c55601f00d0b504203002c6c144458007100b40c40324103124a50901c406804219000000c1103403130039007598040c0729840069036100d110380d000d4a0a0001040e1900c43c0010103098a12568011103c8083c50351000021802c218107140060070622000c0e41d07180701a191074604c0e018007170020900048080407190580d65038442d001d05040c00503030f0440140c10a4070411404a802c01d03148d11640520342e103403143c401e031100103600007410f2352000a40d050f041c503004269690200c006003800340043c00440000c5180c40d00d010390103511030210002203841400082540300048103100c860000381401c00104650703a90716000110754039082507400d8030b0540d5484c0001081103001e201049042c41d0028120307103080d500d660940015003080c115810304418007103685544000341c2e1030244403051 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 140859838 1250 140858588 140858603
    0x1b0120120a110705100804020109150e0a09181205040302040c1d0d020330030403021c02190f02130501030804080123010510140a0201050601140a080c1b0a 68
    0x10040030010100048011065030b40d41110504000c282d03100301070100a424242002606641c13a03000584030f03070000d940013000010790f014040b814a580560780c222824000c41d002c1401c07584070015201229840d100c5046000a4044484041402c494000100004a250035850280c4075070100701515105d80c018404181015100c810ba15032845030181c0a03003080d039a070b80c05103617650006943c6032005802c3c03084c030419010025040c041d822881008241c1d98612143d0f60b400c1900c1c00940e40d500c2081002003220b5035041078801c02d403022544044607200c02d40e052244066036207501c0303046480c40f10b0807a4402c101e4000321030041c645000b690300860140310002c1c2c0702d924100c442400e490080c404a003030380d02c0510681917040752001c40d66041d604c0695024441641a0000740c0c3c0c031450b014010f0b0709a100110300391fa141c0398150021445141d081e44c0b1541800c81c040001c030414001c5130940400304e0382801c0052900c00c46040541441207a2080100354800d13241d041d1401c0c40c01900090f990390 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 140861088 1250 140859838 140859847
    0xb1c0204090f0b0103020c070506030606090306090604021009030c060503190e07030201110d0c15110d06050a0608010b03180c0414040b010b030408030f070509060a0e0907021b012012 80
    0x2800c032031084811410017802c0c207501d0072028404543d1a13074076074058144680d0021000c61065191754041e507410f01000b40456945082140c0802d079075603c101c400301c0c41104901d80600303e603032080314840112580192902c84103420305405682c140c00050a02072608400301d0811071080e890700a01c40082c4842010f40300d150300303500004220f4648c0000c840101d900401c1c070b10030116808184010010780040c0c440b0760707480815106c10090080c008201902d02d10119401c03070080245e41c0302c02c084420840340c000525a0b603601c1651504000d211b040246030040c400940c601e1800d4001d54280d0560a0513101e441c02c240c00082d0445010707070460410030b5800d404110800981040c8240501507d400b0f25086160a036915483c510008250000c0038281c880411a40c6010740140c0390b450200406490315035024600060241a900c6020703441800030700040b648640c00420243e05410741450b054910940e0140151041031101800000e01c2001068800211009010308a0044ca19040541d42c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 140862338 1250 140861088 140861111
    0x207030c08070821090d1b020f03030706090b090d08010e040b15090c07060f060b0712050f0304110f0d200604090f052d06010e060d15050102010c0206060306010b1c020409 75
    0x40c01041141039003801f100441c01c1295503000c10710403900603411100c81d6116450f410203e42103000d100380c0180018200440c5800b0000d400540354482c0890384101c800345904680c00702c0380301c02c0070f00ca820070090894010030089508203014943c8440c2214600090080510108445c074204945030342c80142c0102c0d40b002000240d00032421044182c083c2401454208440440705124468004003040c1c880e60810700c1c0903000d90300740c50512500444c0d0f00d480c3e14090a2040000b10102c1040348600c100d00f2403000b05182c400300d000302e4190408a90066001c01c1c101c010451184040d110350311240a101c00550100f4500030070100c4214110301081c03a0500300400c0708084e800864082e40701e424a551028031122140d41103034030500034030b4000d04518500005c15024454035500c001407605082c40380a10441c02da003020b04641d03080c0c6c000c21100b50745400c200d8503005e0555000754560440c0004000c01c0541c0382c0a400c4807403010400c00c3c01e404007500360340c0480c2c1c440e0f4802034500341c0390400c4240 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 140863588 1250 140862338 140862343
    0x1202010c03141005010f021504080d06080d090b0c011415090705120f070306030f0b150604051f0e030a141204180507111504150207030c0807082109 65
    0x11140a03107868031000d0910300f100194507180d500945042001c4403801040c964070800108082038000d04900342c0c21304141c00c040d0039070f0b40700300402d400c000d040410001e40c42c41d000403403104040b0546c1d00c0c505418101400c00d1159030040451240c9592601c5604402c0e5911400b5140a1202030001456140d500c0041c0452000000c1c250402c1c82400d009580f00341d43c88200e101c1d400b01410f13200140c1d40d95022400d0f4000c082680001e01030040701010074003001b5210380300c540940c109810240076902c48804118191046000702d82d040300418440d0b1207105400304d00c901009125080c5415402d614002081c0780072500071050390b143d0503400c9420702d0750005000070b0070542c60110005280c603062a00204010b0380c44940c00b10001d075a0400100983d1160400025181c41082070f203080300b40d2040154a98101920290340504690305094a03007a0140b0880304800c1d415214a201c6202c40c0d1038540841e084803a00356035802e020883c1c94101c1e0210ba0820410034240c401c0300d41c19050001c080c61 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 140864838 1250 140863588 140863601
    0xa0905060a0b040308030c160803010905071206060c24050907030606080606010f1d1009051e0f0105031b070803070314010e130204021308060910091a131202010c03 72
    0x10180c2d00c208400c0c00400d44d03090450758012003000b0501d035503034482100c18589501a03c0003600004021002151a00300d507004680201c0555032968441212485e981003250f11600c02c15010482014080b4002101d12170a5240e0490782c1d2001d0440e0150383d800c2e9410f8034801c4503400807940010006104006041c8901005040210000c00c1c03c3d1a12000180c10145032103018000e02c0f0301d0b4002d4406020f04803620000e81d0344003070f0010740160301d030b0807014000e81d11a004085c862500d8591342046402c210a540b1a681c074011b115420a18001c001562154400350032291001e0070f0b5042d030490001003100800d003040c800c0421940d40c2c6400b0340c00404442c1042c01c84000d08035520010008500d0b07088125800c0315100020225941d01c07440007800034810318801c0d20441c410030100142480000c1007c0384158070180a444810150203260b50454003c20340040000050110141201c04401080759008000311a000c0c032413449502c1d440d000200c0301c451080181c1d11855101c410540c94001da0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 140866088 1250 140864838 140864849
    0xc030703050c060a09151d01150f05060c0604030509030f070303050a1202090a05010e06090a0801052205120906120405062401120f0902090408090321180a050a0905060a 74
    0x82007841e45c607503240000410002503080c45c0c20707111004403940c1c0d40c4420790003a9149130030000300031090f02c60f07a000c40041c3c200d102d1401c100f604c1d61400079050610f0000c031600c110402d4098240c581e500c0da0280c9590300841240c40d054030408103901d01101c000c10184020310b0080d140c540e01c1e0b052040c001040111420022641c2a00603c0060a01d0311941d000c0015910242814850940800301140da14011026540d0b4000b4111307100241a90040d07001c640543c481c1305050203030107080c0d1480e10130b501400000a0681d800362248580c1ea02118000d4040241d009101c98641512a581d42044800580381603615800c29418412014565096080004800b00001958400800c00a810b40b0180f4080001035500c4015480c1c40708200c0d4024151664000d02c02001420141860019608116401c500910039521401803952121030582076070301315180d642d40340801100782017915030b0b034240030281c200185400c00710b4075640f00071088016103400040080c582c64480c0070820002d41c181e119 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 140867338 1250 140866088 140866091
    0xb3405070c060c0f060e12180301111207030b061902010c020d1e03050a060302030703050615030114010308090111030a0e010e0d030219150c0806040506010822080c030703050c060a 79
    0x6500004c0c041c00348004001da0070000020b80c413580d41c40ea075824481e0401c032520b0002000030302c09014451460141480300d009034000c12051107071045104551242402c00d5000018a400051105102390016401d4400c05030526040c40d01c1d40072102e401034508000d00d00943d454000c034600e07280e4100805054004540740940780078100c1e611603414040001c11000405441b5000129a440240c221800440e8003404450131550799042c000d4495009541070f1403503c81d1032507094161b240c14003030311800148040010800782d10359560000e040d801028020306211404c162050249002d002410907032206498000c2c03043c1d00c580c00104000200c1210a205003500002072010a03400038038400c481010301e0b04200116901d080007190800c03c03520050000742001e480f40c0000350300224590082400791002e1141d61917100c0103640c0d036401185c0383c1c00141e001c4d4040c444524112000d07881041d006000a134070b049200c4050034107690142d00c0a1300455000101e040d02942c003084078903402580660b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 140868588 1250 140867338 140867357
    0x1008060a0b090402071401060f090b061b0a0605090c0a0602030c030409092406060e0d050606010807090905090f0607170402060d27110303070b3405070c06 68
    0x8010340340902480e40000000700b20a510b548030340d41242d40c41038111541c01d41111651854601034000380c06460521901200d0000344500c6e5402a0001c40e00020605400c112421203c000500304091128200d4407a1003250004105544075080c00350417100064143d0300285010310080c041240c0c08601154810050070202007004130540e41038a4082c500071039000e1881c04c0100c0c569a003d0760b0b008840092440b044c100480341c3e400b02c0c0454400345c81d91074030041c90304100004841e08c13220140c4590002d000058896102d0071616510103824280000c499403a0300c90358040f920102c545820035030050b40308005c0201d0401c070255015006240001000040da8110003031000c0180c0000d00032000802d1440000401350405a5403c8801c0c840c6460407601007c80c850801311a0401e4a01243c440304041860502100715000319800086902c250741303c40100d9a0058510030881e0641d00401c03004170a0010500343e1250400002d0741c0c1d240e21307001c15051010a0710705940c01482031105940 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 140869838 1250 140868588 140868601
    0xf09060e0f0307030207090c110609030d0f020a08070c060f02070f140d022e05070e01030e060c120a0b0604030f050625030509010f050a15090b010509100504030b13021008 75
    0x41500c2982d0729400c000c02e810b45d88230008d850034110313001401002e00846040084900d80003001d000b4003894a08184220035400748420101c0c40745034001000140345000081526004104c40c01c04075110344000030b003442d2000310140c1280c0141100b00c1e103058600855009000d080501c005818130540041c0c0ba00142d4450041d5442400607040c00e5440751819001841c8800c03289062500c5802000070310462402410003010b041240c0e071038501007442c2982c1482c1e00e110008007184a10b03146074080c1d10300100c0c000004101030b0020f1101c15000c0e11001d96031016103c07000500011351003260301d400c000103186030090400400a16031040b040f00001c42000b130940d4031040700c24006050a00090030707150290000c0c05090b05186220312941004103000440c0ca80b54800003021000081044005458480300802c0d10709005030580020001d1002025911b04903d21314000c5e0301c0e03804c000707282c59070303a0355400b4542c40102c51501d030320700744808810194103044280401000c0545030001d040d18058 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 140871088 1250 140869838 140869843
    0x2130e0a020405031c02011407091706010303090611011e06051e0a060807110d0e150301080703030513230906010c05060f0604150320010906090303050703030f09060e0f03070302 78
    0x1003252605c3c602c99030083c218004d000b9800088400c101d91b42c00b0740b2900e044680a042c084c1d59101e440c4002e8115250340c0f01404000c29043d0503243e040d902c004240e841d1040c04c4440103081c1e103003030100307550301e20000d00e4031041e010303074040f14084600f008182985400200140a8640c51030030f1500f803c8541039040e203588102440c01920854107040740180c07a040402c881d8485000300c030089a1007440800c900c19900860000c05a0b90100c03510307500b46c50a00380310031160000b071003070b140345078070025050000a0188010702100e010022251110383d98446d50712000b00c0c400385034440340e1f50071000b40300d0301c9040580c00e1560200081c00c00142d0703944c1f80c0d41d41d103685001c000d00c5201150f040b01d0200b640c960710341d00711000201940d008050195100e040480281d030584002c80f8581403102445c11644d40503241038000c4400c1610341298562664a00b51101d07840181c084003056507030701203800d5400581c03141406a9001d402c00150074503500402510313104100703009840b0756009000003070010b50b00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 140872338 1250 140871088 140871103
    0x607020a1a0c0c03070b010905060f0f0d0516060e18090a0f170f03090106050a0308070f060b0a0306020d0b04050114060c0a020405040f06060e0403050a03020c0c0402130e0a02040503 80
    0x40145648442d030310781c240d0b0949401075240b41c83d2180400a0075400340009400441e047e151803460405c01d6071246000c2129000c41641d0300390700407c225800031001d103001d0004110182c00f03807003514000084588110900c81442c2c006001286000c0c0c03094400c2d081c0b0300c5002d90b90300199002a8414244400402c1e0344008624000302241c05061101041180541841c0c82c0c06030303100c10143d1a4110b220700c1ca031040d081121501055131a103500082d0701d1926500c1303101141d40040e101c070302e4640e40ea200c0d4551040c680d042504c81d2030316810380e80300c95214044c2d480c2c0154002d5400503101c12900ca600c800751402c046a0038403950034000180143d03e241007462003c2c420403611203649041d015012410402c41c1c030406548546040c081000b8030404200111400d403050004004080d07c030b640300c0d544010256400f40c000b0b00b0500942e0285030087d80103000c000c1c0c45000725020410b007400003400760392020f050358200c0c1440c21010840b100b00b00641c183c100f01000004c1d801d0504004c0440c1c1c1d40e181 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 140873588 1250 140872338 140872373
    0x70f05060903071a0703031118060f0705150403030f050121020307050301020d06030b100b090609030c03070801020a0f020c0f011b0b0a02031005030f070501140c1606020607020a 78
    0x2000208a6403a0b0360402221000b0150328010400311102e003074410104d03030007181040c0c01090814214036a4010038404403841c0050002e00074071001ca5075428054250480d164802d0829810020000410307010480825441c1c2542103540c418a040c2c50f004007591507180d0300e17901c3d4500b0a0010320402800e8104c0140c000400a410200c003842400020326100d0203a00080d010351001602940e03a103219040f8a00f41e0b030141000900036254428030b0200c8054a220300d0080d1036084c40209030500e410030040448000007411900680160070000742010075507800100780d07a40c0010303101000b41d0019180c4120b240320b800506403088607440400d1903c4001e84403d0b04006103581407004440c143c441c0200110380200c403001c0c0380d14010f880c0c1d4009620035a04403450711011507002840c0e20780001c0c00700d0111f110380e0150848a10303060041d5204d208074075403620000014001d008011604010807244580c4034400201e11501e0300c1400b0f814500064a84c0c000c642004982d140840c4241112100215 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 140874838 1250 140873588 140873599
    0x10519050307050d0203150103110309030409021812010509060a0605010912260409060f0b0d05100503010f02040f0501110601030809030703020d030c1721090307020301020403030f020f070f05 84
    0x1a600c4000b00c03594402c409006030351307600c08000d02c1070030a01a84440c17102502078070204204011090180d15502007115007400e2a4400c000500003419250090102510451800900d600610002801009032015644010380d034640c10000401c000300070307943c1c000091001c1040030a082800090603c60980a4001c00c334030301002034005c004641800720441c2d0083c030707c00204c0d04440044c0c2c82c02603209200b0201042d06145000c03030a151000c0d0f5120445001c41c2d80303203280c00c2c0304441e000e000d00001080340e509240380503400543d50b10b0a02546044140c10180140c3e03440c2481641ca130840051b401450401c4400b83d800302d092000040c440e81526000b840d49a125184240001d14010707064000a40004a00c010030301016041005000c0c451b1044043e100c1404c0e0301200d04140c0e0080800c074425445202c014090000380b5010100c2d000300100d03090300d1401d40c6540209099032b1140d4402c0700003841c09590307210020750600c8080c1c0320f0310516000e044070510740881090300d416240101031040c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 140876088 1250 140874838 140874841
    0x506040b0d11070f080c0609070b1c0b030102030c040302040501120206070f0501240e0702010504030e010c02030a0b01080313080a151805060103030807031d100504031106040507090b0105190503 85
    0xd4075a94151111903074840d840c400d086405203081122a0890b42c04406d407882400c1c04260f80d20320104070710040c1e4505c60480c60a0480500075800301b2444821807140096581000510a840a00045205512441c4800e80e194558410b200841e0016800154540d03010400180140e480310112075840c0d4010301c1402d42610303641013180c010801c2641e1414094054400e54120030040e03103441040b6218150004070300d603510034040e400c0c0e0b03800b141d0007400a0300c07200e00100e09601840c0c4182400b40050215200b2000315034541c10800e42c20780003664141e201142c00403580e041d00003842e0190075400c0c09014110250740e40c120040d0802c000c00d110700d03511840d4245514032805901080c0680000031100c03207507924240602802000d841140009082c0b408903000031652072044c0a03541c41e40c000900c00c000c2d00428900080c0000f4204404001545002c100d070380c0da040296074046c40c020303000740c84a03901d4051600121048107a06078103101083c48149107104003c0180c5410914504180e40d89 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 140877338 1250 140876088 140876111
    0x9090509031e0c0604060902010f020a05070302040c0306050a0f030506072c0f04180219030807080307030615020114010e1302310e0d03090b070c06090b1f0506040b0d 73
    0x45004003901c0404030710544d010442408880e81101590900070380b5541d61440d10f95804a80310040b540014081e5803100404000500b000e40c0589100481458001100c9403100002012151194402038500c034010f0360a1003402001c4c007016400c01510b0600c0106c00391903019001d90300100e4000441c0004915680e1046501c84030790751454403030014010400d09174480b05032941e442c59400164021200020040350301c0900b04902d50560b5002090f1a03b000303500e50b582801640001c000004241d1584400640200c1001d960070010005400108031203641c100c2c410000341e0140d1040081729003010a200804030000c0d2800341c2c040d01990034490300141d50101c0c002e4066010419074004083d005084000d42c8564064484140004242c4426030b0800400b00c3c1590302100020300914014008550842d021300c0d00703058990710984010034801071980744e40c0030b20402254a900340380c0f600305140076900111508200548821504541041e040404003031720740c0102c4400c801041d84c3c0d0717003800c2003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 140878588 1250 140877338 140877397
    0x50907030225030c05010f1a0d06060b12041a1b070c030c0801060f0503010209010206160905030a030e01020c04060b03160509060d020a0210020309060c0912070807060909050903 78
    0x100140c2000b000380c400403a494003c00342004500d05450a51070f1400d00070b00b160113030041018600d0200fa10040c2c040201040018501c11103404441c19a550780c00055520102c4c0041c100340c4040343c4c180d000c6890581484c2d02044080440041019040c404201e0149600d54250004405c415986500c5100c180381801e2041c080740c1002d014007820b210001000001504080c1c295103541c018040035680e900e040c10300340d0180001480c0903800403000074480721104a201c85c844585864500c242c0c1e41d0b601c0c042400e000d107450058000400800720107505580420440c19481c00960b800c00405140c40705400762400b028080d03400600084810003800c510810a80d0f8214100501c0503545601d02e02c0000300940c00003071407a02501944d1780708800200c1c7c1d4030940b4400c0110101801c2c580c2e5660031503039a150302280d8a25070012401c1001003059000b006101c002e407010320b0091840e03604001014080c1421903000e00c0d001800c03d000c2249020b000b005551540d400e00f507200402140080e00d901 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 140879838 1250 140878588 140878627
    0x250f06030218121f0603020d0204150e13230604140132070809030d05180a05010b011209030519140a020d03150b0319020412050a0213060509070302 65
    0x6503c498a07140c0e030211400003080e202500820890100300d094406890b24040c0c5a0910002e5482003084400b2405802c05420142d00941700c800889001354440168000c90034041c0ca01c907195160108428080009001000c00c030101d41c1c00e000311082c0864208581d030303243d0042c40180004508842500c000381c00350000c5c00780426078004c405900c168540381a0644461950413510803280c2c2002c02c602c2806040c1c1c41d40038100120146203006a000c90340c0000e031002400c4160140007400ca8030404060500c80310b1002440b840020400480d00300c00180070141e802c508401541c5032030805000203820004032020100340401000b0500c8140401b039440903040d8803140110680001c950040a40c040344915614409480411450400020048914049020303444008000300042a10842d400e0880030158000300005498962107190072101103031100402ca420342e000340001001c500d84010300c0d110914605004102c8103240c14009084104040c0c0300506056001030a410000d1000d042172 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 140881088 1250 140879838 140879887
    0x180b09190b0315150103090201170408040302040906021c020a090509090c09161b02091515040f0509060402070b0415150f0302130603030f110f0f250f060302 69
    0x544000b034501207000705410f000c480340020714041c0b5034581490340c0a8410500101c5d0180c0d00d242190100c9499070490b210064015903008406000000040e40e03540907010700d1911030000503031107d9900218020340003491198480660051003a10b0405034011000c0044481c2194046d555072a005501ca0031700c84020025504506640200310180100c0d401c00e501c00421565040303003040e0991403400d2480d01da060000c0d030010140d0040340c40c004031401c02c0360441c04014100c14450340704409001044e841640007401d18407041c4001c1029140a07001c4644c0420182e6066203450800d035940c0100c44c90041c0000d202d80030400200081810683c89140030700303004a0356000300c988990340c000d1400d0b00313440100e10074240400c00420841242c007840080381e42c56166901d00200f0f450041e41c0440780c40e0840744007071007a1050303040e40c0072080081a202d0300c0814060719801d0380e035180c0010310100c404051a02c400d9000803c018285440c0f400200300c51807807500685444000c400f0b07480b07a40c03220011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 140882338 1250 140881088 140881093
    0x1c0e060703110607020d02071a1e0903010c08060f01110d0302030414070e040c060302070302060106050903030904050a0c0305090f031602040f0e0618150a0207030302040506070606180b09190b03 85
    0x4c001110760000f40c4400305100c203400320b0b0219640c8907124480c101c2c040c0c005401010091019100c1c4000007a082c0741c1c8a0902c3d1509030174908104042805c50700b40780c50060016201c407003032000a04200b07001c2c6070b00410a1915582c641c1403103a074140d1b03801000c4085400c06500000041c240f00003030b07100d080ca843e000c6c402d0700d800c0c555604100c00e40900540341520400c00039040000c40034024400ca4521641c942c000d000981e00e4954259160303044140208d405000810a00142c0d540d1482068803070340c600030740014038500c0d509004044410003002000740d44d001030300003c81202c001058a0b444c5410a0110800381ca0900c0420b000d444448840780019081042200c8004000300715203202d036168403251101c01e4896446213a07164000d1030054044802c00021500c1c0c6616a0014140f40c1d00a00b070240c50103076601e020540a90020000b5140301c0d91b20312040c403000100048080c0c043d03145000602104448400058210348080c0032580d001130f80408030300710300040780c200a624103001403d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 140883588 1250 140882338 140882341
    0x102300423030d08090a02090c091203190e0a2705130201021c09050126090a0c0b0901120509120301080c040f06061b0302010f020f0c1c0e0607031106 66
    0x50540758040e003006000d21a000e188400c011483c8145003051151389400024407206e200f41e021300c130015501404c00b003107241003000031040e1a1500c0c0c040c0544200e00300d00540c1c7d40c404a40c6a081c4241500050300100003071100c19248998400380c2c00c000766010f140c202c00030602500c940b08400c0d00c883e4000e843d2942010f04000000340c0c024480e440300360003030f02901d03030014011083d0403100103940d41c1c402c0801c40c0c610007402a54840d0f25070086a46071400c0c80c0c03081100c1c0f004e040600080880301195940d06c1542c540701041038001d4a80c0041054003c03107800c041d0f400c0c00180080b1014846820001e95a90000742601c20800410356469407800714103940356102c1d0710103a220321a00001e40c0c091410201d24512010303152041034101c400b5569860202c42c610f070f401000d40888600c09030700310340d00c40c00c5801006150b0310003000d01602c0c041080b940c400044601e0350404106600249242c0c02c58481007502542000300c40c07038040012110160389410926090711260002600c0050601c40e050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 140884838 1250 140883588 140883629
    0x3060807090902040c09180b060c0f0105010302010906080c0307030e0102160c060e0303030610030b03031207050406090b181c0804030f0203060c07080702060a11030d091101023004 79
    0x30b0080038014020b803828880c00c1c8910340190780d40c12a0380308500350b00710b91002c3c0b48800d08050b8000031041d00001c1140b441c4c118034140d402d00c1e112003e4004400c60750354000410466800080d800c7c010415820901040c0c90038503940040c1d4040140200306042c0c8502c070700d2040040a42c1252400b19540200d9945100d0a040040ea0107031700303016aa011600c50202d10380c01d40f500100b0785e0f12274403005280900105141004401502c0c20041c3d064052205105515440c111249510b2203541c0d2a51032544076880d0000c01032804103140d2046c200b0311400c1001042c1d011401c0c4d0094038012054400c0c7d0385c8001c0c10001d880e40c45041d51409008007030082004010007144041720780d0024021011035107a074903034034006401d500c5000310007401244100a18001801c003d00035181d94082803c10040d0000b4801c0710f24290b5022452603a819541e8041e1102000264105c3c20785c0000700784028662010f030710505140210307c201100000300490701c5c241900b0304202c0d040710701070110b0042000c0c412400c131 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 140886088 1250 140884838 140884841
    0x21309182d02031b150702150a0c0b0c0c151e0705130e0604060503010209030a0f06020f0412030908010c051c020f0a0906080703050c190903021504050301060515030f070306080709 79
    0x110045442481100d50080104075034400f610121b60700200f204a42500c4401d824401c2d42c048140802400b5803213010002051400b50014810b02440d501155102540d14400341080c181720140251050b0040c24010304500131101c2070001980c4901c03c034055190107405699601890541d19448454260003043c0203200000b0350b806244141c0c0c061181d02d8840d01054240c0c0100c500c9188c142d417103142c1031004910013400c01103229004640044c82c1040c2c4203420401540503410500741000350510fa4001c040e84849001c00402d1498000c10405901d020000c00503c20b003482c51704507078014034005900502607411a0403050b002408590b540884110261481d802440380c07201060069000a5459000f40900c902c41c03d92004803a28009201041084140035004031034100400c0d60008401178a601e5521400d001204901c640c0b1350746030a040600b5910290440750280d2903400200e15242514000daa400040b40702891b080c40d0b80780e5034228001c10312130b44825082d01c106d880021b40c08449 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 140887338 1250 140886088 140886133
    0xc13050d02150a090e0a050108210c1b0111060f400c080c090105040c1b03030e07060207080a0b070c080a05120f09070501140409021309182d0203 64
    0x4490301070f091591a10300e084c0441f01c0034801c00c84507410031900d01d0340d17100c20740d40140c0044c1d441c3e151803401c18484c1d8803828900100c900c01c00050700c1031514003007080e40c0c1001451801d0070304400100030320301d0070740000043e1003c00360054842403080500c08003008900f40c0c000701a0f60300f034025002071108141d6480146410060295504a40600c0114040d40301050001400c0d601510b02c0c500c9918000612000b400841030760020054290a0507058178610900401018000d603000724140c1c4410306020305286a590003101554040c4408210b0301c0408502c0c80d0030643c00643c90090b596680c00e06444040c2d600030000c18081c8002034001c1c1c00c9810401030a4800031000d545c1d80d542ea54584450400c0c03205442d850300c40c0d4002c5104014540c498100d404880020002450400e507039540103409a070054a030442c0c1c011551081809084014400c0f138681885100401004505a440e280d0071500f4081602e14540404901410a03188900d07030449104e0303001c1d040328681072220f8404c40207441c9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 140888588 1250 140887338 140887349
    0x50411120c010c0f050d0201060303090b13031e08072103050403020c12070807090906050702071d0403020309060c0115050306190e160f0e0c13050d02150a09 69
    0x11404020195041a03900008045032220080c0408000007005650381d8014410856090f000d1040480c001041030094032008481600042030302820743c03801800c0e201c480c3d00a03c4240300140004017200003803080c00000c0780e03040a0210b0420f803e810321444001c43d10200905081000610359080104000e600090403104c600c0e01c42000f03c4040e02101a0f0302e041c0c90180041c3c2c06015141070505c3e1504852500c40822021103e0b21a5110740480c10200c170b41e880b070b000740c41d6078400d900280002400b48a034001c100d44054070105003000340301e000012004504114038031440780001c1c10140204100c0b0f04940c0001c013a1a00c42e1041e408441c0a42000540180e05c1d07a18000009164100040c02c0c07809110b00a41c0b807904c0240305102a8010980c4490191840c030428400c681d01192910350b241c080c180c8030700550019400e0801a10058001030145170203400b0801a01c40c46607a80d00103030080c4c030000c0710f83c2c4440718a980000b40e46001d042c00d0113040508000f4401c0142500700051070101c0d070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 140889838 1250 140888588 140888603
    0x30a0f02070b0a241512060b09040e0c060f07080d02070623090c2412040507151709100e030301170309031b010909140a0e03070c030b060607020409060504 68
    0x140c01280c1421004900c1c0c0d05000c00c81c141c0c134400d10190100360800c010401aa1406401e842c030181400e1050f10311560000e01d86881c0001d0000c2141001e0054442d0244803034000c050701e00618001c01c01601ca050b60407400c080d0046200d0003008800812200c5ca074564000c02e54072078081c0e041c0a0020000c0810706416000d0b100d0034800300340206020548118007035406041252612014421300180007002e08603100d0409000412020700500075200c0fa42840d9044021494103141103894080d09800840340d05201290710741d06a54011a121501904070260343c070f0b41c0e01c91250301440d02d10b0710460804524104604540010800406581217494006a4007290080c02d0070340f903240e00c05c400c81c050309030304000d43c1c0b50305490100244000b6050306140071044d050f5a2058170048400c10381d681b0101e06d00c0141072004d03030200350150410107006900510b1401039540d6503242c500d01607200090420304024009140766403294161181141c000d0404d2003a189945000c40003010211811140f10303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 140891088 1250 140889838 140889851
    0x3081e0a1e05060901090f0209031f060e0c030109090809041a01020d0e09010519050d050a292809030804021003060320040f1a0f011e05030a0f02070b0a 67
    0x18410790280c0750080401074442d44c09a420881a080500658404500159000c200c150030540b01042801103401c0c08990182d1004100100c10040d180c0c1a800503e01c0b502c00f605000982d40d400040f2070443c0c103188000203041105181000d0a4007903a0007195125180c42240891403206445098828000361b01385c40f80c507030050350292075142e40040e8076500440d0300b000500950810382c4440b1016000060880c02c0b003680e9000040d04421b031510100c03450b400c540302c58010401c1100141c000642e84400b45080008c10784d1740b460b01000014200c140c5400510000c2400011151031025000300e14082801a8540c506010349000000d0300c00324010240a52801c40d9240710f031089009403a881030b03c19107040e01040da032801411015103610707131251b83d5403411070218606210700c030400a2002e000c000b419055604214501c152010380506004140c03078103200702d8400008804041260381005512034591050b490024080f240c000c1d0700031440010350905000201240a01c62850440140042e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 140892338 1250 140891088 140891141
    0x90b0c070317130311120a120c020c060a0503070c05030301060302070c08160b071a011511010b0f0d0f06050109020301170f07030b0406020d05100801151203081e0a 72
    0x41908491111810388501c0c06080003d1103585e1525401028000300e400c0b0541d05110004550301c00003d220102d001c240f401d01d00c500e494010100c2c590924000780002164841c0452958425100c080c0c0070050004009461079000386084908180c1040441c1d0b140c0d0b0f116500a0000c3d0302085003500e585a2106000079201070005108604041e03090542512610306103184105030413101044403071390314017501180604414802c89000b030002d040f400b20340c9041200050003503051012203802607418082c66189a0300c601c070050a60b207209884a20141c000c50900340d214032207004008104c181408000200a010780e006141601c2c62903009003125640d038161641e07981c0324042d1000d0150050074042000ca0704418401c2d51040c020340c0d026140c517014021510884d04125122582c00407004000c1c0140c10b003d04c280240130140403a81c01210707090890a5070004280403000381000700a0b40040c1d08441c0401d003001c100681d1895200003410000d40540c081c0403e81c0303c80c00d03540c0100c29500700c1c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 140893588 1250 140892338 140892377
    0x706110d0b040e070b21070909050c210a0b030a08030601030e0a03170a0216120f050403021503090f06010305241e040821011a030622090b0c0703 64
    0x42c0c406148010000130785400004489034001c0103400d2000400d44c2800c040000c8000d080314403442c05980c80010050500c10080210b84020f0300034441c1c204140020142c1404003100d560032244100341000c1d003951030081c003102401c983c402a5405000d004140420403400303030080c0d0300940c000d0b241406021711004944da90b41d008400068001140c90001420201c11683c0c400e80100711b400d00035183c008920301082c46ca5500c0c1004032000710540030325110b090b03032010354490500441d1400b5850030b40b5640014070380503145031406071840303400408180e42050070000310518464031004d44406695034207006032202c0f0f42c801043d0404084080032031841c098058241d1144207500c0a080c0c6a0320b86404202521030020301c00c4a104200300045142c001028003201601458822864001c3d81482041071203c40c0d503108174684c180d002e10510281d0380d00c2d07180256a404a0000e86400d840300c02154001406e22214040c00011003c02400340e0461030304000d0160b41c0c000c0c2c03203008801114011400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 140894838 1250 140893588 140893601
    0xe01080f0303070c120c020a0602030a0306080105060a0918020d050d08070c1a07121505030c040207030806061602061215010c0309060e030a060c03060611010606080c0f0706110d0b04 80
    0x240094125130504002824004901c03000c10201d00d000300000e500c641c007044008525802c008056400031520343e00b0a58503000d0040035100700d0000b8086c1e400c0c41400718405c49058015202c03e240c072020310510810b40c0d41c40c100300c8240c000300815410700d1603042c0551140400d03010400029418000242d110380100d800050603030f8005500e291016100406040c0644054082c0c3c007000004041520488003074001c501200101507200c2058038586001c06140c08451002c05000354014084e6802080c0c11500c3d8030340c05001038803596920809c10f208035205a880003802940200c3c0481e003d60305201c0b004184d0322840b079400e03c81b40d202242d10300650b000c2145203002000185500c9040c04000c0c070542401303074072000140807503c100126940301e1082d02c070302c4026880000e40c1e0741d0303042084551040c440c03010302502400030003210303082c600020404100107000c82200c0300005409401d90203440b00311055142c100d1401c201302c1c0c5005d0010a01a0301c01c10b54401043e04080c40c02d071040ca410701c03a60 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 140896088 1250 140894838 140894851
    0x106030903050706090819120c140a0e010908010e0a0204060e060907030b01030f0204140a0b0a020706140c2a03010b060717070b0f06030d091809060f060e01080f0303 73
    0x9505003440742d0354050182a40a00880d03580000b4007c0d0610111010300c2c000e84c0800c55110003c0c1c900345070110a0031182441850000c1043c4071103000131080d40842103d417111190302c2c0101452507080016620001d403540841d0042d80380c02c214404d41c65008c03c0602e10b8601c211014010156a2194010100404d85034560700c0340b030500104500500962240e08070801c10304001c035144000c420240c00b26042036000d0b2010480001c00d0815501c1d180c2506400707001e52058003420514001e00c020760f104c20b217001e031000784420344916010007a401d4083c1d905c05e103030b6513040b5100c2615400b82d0440d101c040122102000340b003071010700020300d418002c2540303900e400f81c4168103165480c0c0303400740208055034250580b10070412601c4003082c807000c222481401c000b01e0002e040e050030024075141641d00404131041101d402d10a03c20702c010341c070300071001d0420b0b40c002003001505030814100416940300762075000ea29010000605c9d100065145040314424025103070003100d20081283c4034401250381 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 140897338 1250 140896088 140896097
    0x121606080a0b01020c0409060b0a0f05090a0e0303041e0c0b1b030a0f0c1104090b15010302040f050f12030406022d07060c1a010b1c0b100c060b0a031101080106030903 73
    0x2105c140d080c01d51195014901408001c00ca506031070010034004112038024070140c60344080280403e0524040c043d0300318540207020450100c3c03000503940c507800f001e04000c04202070801c40003125850031580d5903010380c00450320b1469036903c4850301c1391680190728041904c2603078085801a00808020f0301e01e040c2054032031700e00081c14510111030902c0400d204481280c050b11030502107485501c136206070603101e10504d000c0d034101000030400130449800100d0425004010500404094900660441e1800e441000c0d08140c0d000000b075016034001500728480c48040340000c0c0c8142c0c0000e0440b0200390440705c80181c00f91401008203c0708031003002c8001070b4000b410401000c0c0c401c812840d12a400b8118041c110056a50340342074110081c0d01c0303406500f8021907a40d610381c5010702050242c3e0604403040114010400224070404401842003080c4450998118180403954000c0010700d0b03801016041d00315203d18040c94052090407041e070028607414008203446001e840b40000d40b50b0991075 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 140898588 1250 140897338 140897353
    0x30601030c0816230a020a02180105030a0b0c0d050906061c080f0a0c0c03050d032d0c0e030703081b070e150d0b100503011506080a0b121606080a0b0102 67
    0x6043e2400340c101c15404c030200d442043e00150b10b0304200041c01c050b1a41d03031701800b0001c45a0040003000f0180028402c120100840108a40d42e400140c0303002d00782c1d000c03143c0307125a6603001c03040010340518016002c140e810241045034000d4080351440c07041c1401c580b1800402c0004a69a10018124900500060040100c508007200300350261007000b410789005203582d0019a0307100e030412030b50340c0202c4d55a030118545d044029054010107040c0b0100c8200900c00001a26600d02014000706032040c1ca50364a51406940790303c20a0b81c40e030900c001504071041c3c6a0303240345c038030006d521a440384401100f1800ca00c032900080440c96034100d03084c2c0320160a441c1c544021110426002070451039102203000020400103984407101c600c103009040d5403404003460082490b0030364000504001d0a0380d007480b82801460740180302c0340e070130251141c1700158000c505000b28450b072040c002d0ba803200c0d110390030140d5946110f1076084026912183c2d1031003c1034542d0000315003620a646552070141e0050017 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 140899838 1250 140898588 140898631
    0x313050601090b0f1c021314150d020f150a0206010305010f02030907180615020609070b090604060810030501021b0d0801050607120216080a030305010506030601050306060a0203041a030601030c08 86
    0x260004005c1c004214480701504050303000459250070342000c2c8001c0c6441c4c01c0b0030b180da05861454658880050400800341c01c000344c000031801c445541000b445030f66120343c14005078849020001218288008150f661a0400d001035a0790f0700c244022225507003000041001c0b001c8034000d40740034103403900c01004406e00b0042d5404207540c10380032041b10255500c1c0005804c0b04824060800b0b4005900030308803070700341300316007e0a140300c03a04109820b0004201c0c0c04056103c00f011031701214918a0021400e407504904000f0754129903102400541c00403071061001c08520f81e00041850301c120417030700c51030388103e010780d17a81e4403d11038503610090521400000c52a40c0d00418001481c0744166407100e810424901544801c6800044103680010000800c040e054414107014200c00c031102425803902d44002040ca00c07006080c640500c03408242626100c3c000c000340d030090300b6070180f4a079010000c40c990302c400b0303001251407900003810a2800480b06000c0c211243c000c541041c60b0004501e002d2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 140901088 1250 140899838 140899849
    0x10b191a030a0e03040909140d020c0d0f0c0311090a060513050405010b040e060106020d020601081b0a0e01090b0406062d110303190c090605120703020702060313050601090b0f 77
    0x14090740310307280c60f90b0215100c010180000c0000d811100e100107017002880c01c2548114241c9140c00f07140340c0c41072861300450340e00052003000e1410216030303942e450080c2e0714200039000c980d010020600ca608990200800a10b03200440c0408000d40700c3c05001da64031314107041a03401c60310406030070040884280e03034824010f8000390341c4039024200200341e6503007440104045903900c064020b00d0b500544014440700c0d506224141d4100180d1000b0a92941401c905648440c809213030f903603880d0041181c0800584400b08010002d210307900100896686d1143c3c858098010006018462450441d001c514a4050003940d5601040301d90325003070144103071240440481424001c01c1c1480700b20720882c0341c0880c040004601c02c4030503407600c080e0310307030191140410380c0c09100c056018844d02200074840c00b5806416070300441d0300c80141d28590f884201e0242d009110b45040a50400c0c0004104420389070b050188c108124440e1048034142da84e54030007581220030154096900412181d902d407180e2600c07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 140902338 1250 140901088 140901091
    0x711010c0f0f0c08062a03040203120c010e070609030302060601231602040b090c070b150409030e1302130302210a030c17030c030403121d010b191a03 66
    0x80112001c51031041d160742c114841d00d032004807907a002c030303002c14013400c1014004190000380c0304250aa50b00c928000001186569074075154040300c0200004042d558200320362041c1c10144240c940c3d454014a82050107456402440b0041e8441d100001076102c0c45400c1280440f80c040e805400e050b2564401140c0c5001f0198403524003643c002074480006a07100c00410000504119035240c849891052106480d1640b8405218802803070400c038500c4049411502e1003644104119003503558101e08040020307106a00903040780c03030b0040c420f007055001001c0c072021300012140e941035440008508003d92003440340e0070080e00501d1008000504100509400801a00d0950b82d411070314101c90601d000c540c0142980080c0707803501c8010620100c070320314a02c900c40c3c22104a140d85040300180107948809080181000007130107500ea2211060fa116051103540502010fa0300d01107101e84501800b0102c50191203200c1c07011400c108104014a0316044448180840c022303a24800e0450030107400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 140903588 1250 140902338 140902343
    0x305150106080606160212030409050c070f0213022b0515010e040b122e020c060f0a0b031005070905010801081908040b03090d0e010f0207290d0b04050c0711010c 71
    0x81282ca01070045e45d4068600c591800c41f01e0045865620f00014403003511006070502200300000c008860110b0003813240240b4458054812608a10300040d000c8000e1180903d02c46241d601c41020601042e01d58407082e007140482d200510280d220010313207000811510801901140d4041d40f00c21440c1800d81206551000041084804400043d0b03181e0425055820100f080c05c1d440d0851414140550b48007180a00318450131820b0161240342c1554915000e009100b49015802c0026804030079a0030000070100054182d0b900b00c040c03200740c00041c04050310141e0104038000000711b071551040c070700c06040314480f0006100f40d041d07400c80c040400b401b10b80d0542c2c03104010407001c18807502040040d8000c07411840200040e009001f0010406220440f02c80d0400c2040c0c0d040d0001e0b0355000440400352690f442c4088900068054100401019a80300303545a090205440e4906c0e88164007002d040401900e05000a03a240e080d5440e0038468280004c00307a07034400348060720f654420417000003c1071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 140904838 1250 140903588 140903617
    0x717150a0306060b03040302010e030708030106081801021611030a08030f0405030408030406020309030d0e010e0f03010b18101d01060f0219120e04061208090411130305150106080606 80
    0x1d88a0300e031003050340c00c690400d0040520010602040560911440c05240f922101a50600c0b689036144070840c441031003844100a94900071600881e42c00854050041e103c40085540d82e0741000c11810308600d049041d1449400d40b0400c2c082d60801084101007594000e08540c6181e907a40c090b01d02c04c0f203010304107031058070007800046800d100c20030003000540f00d150002d545440d0550100361030489080310750320030420642c00d45402d0381d0b0091014440084221521503d811002c00441d004062404810368080b140041c48500400040400c40c0224a401c1d2074090403501ea8021400d410758280800200a20740401004201e02c22606901540c078184183c42d42e90341c40100358200e1480110083d1944088c607559410b0054100c140468075060030b07201440311500d842c00032100303180005805011984005070300c0c1500e41e1588d1000591403502c40c0200d840c0e0b54252045503c0300c00300d0108484522800c140c03880c140900c6210340b13040761700b19a070f0319529649131801d1103c141c020520362580316 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 140906088 1250 140904838 140904859
    0x803120901090c060915030c090902092b0501060909022808070905070e0d0c0b0a030f0f060f0e0c03010302042d0b032b1404030b0a060608071715 64
    0x1a156030703d00c1000301042c0e0744041a4904155418801c2c06104040c4414035140817480c3c98840d030080d90700c60132a0710309840140c8503103001e80400c01c00300c4207881c1140162071071a03110780c3c4a0400300c0b15034402c5010b00020402d8686500002c404c441c84480060341c0100d481d00004601613a40400140400810160340240303a40c501d1014905980c1e90400303000103880345c0c2044506503002d211b8a0004004892081c5510031640740d142c9400d8141c02218498500010700c140c405010b40c220030101100c840040080321000452000100468091410191311400f00041d25403480d221803130044180400f1345155034a10390030880201860071030820060340d0300c884007000003000181003882611070b03a00414580780c0b100806081c003240c0140314059626811070052400b5202491420b003484c03e0a124892225102c41058907000e240d0008116030050803c102c47c114164002c5c00c12141d40351144007940c0caa0343c4d010f030740d000062a0100d040f41402400116085020b140c0c00198032000381c00e52000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 140907338 1250 140906088 140906093
    0x1a030c0f1b1c02010506010f050d06120c09050601020a150b010c02040f060603050702030c10150f180b0604050f010807030e0a0308060306010902190c0303110c0a030305090304080312090109 83
    0x84144094200318030341040030100042c031a070903411049403556100030041c0d4a0480d00107003009040170128030400001281c180b0f400c2445602000180c00b07800054030f000365171890f14080c0d031010350042420b11414400813450a5000041c00180c155126103000c0101c503c00c102440100142070b00c990400c034400c0328100c09601d80e486080c010004400010411900b00303403000e0107079a00901140115441080f45082d01c2d500443c0c90101d14401c041e010a5444010003606074114154010b004a4404a0000605800001d2400c3c0700c100f15030f0014071011450508108241c001c509c2101e420400029000741d181d8412400b0950151050800040e40e00715940741d40d103041c043c5c0c0b008802041d01001400a030f46001c2001c10b004040f0311034158a4200c95604010101508031040018040c0002c041800c00d4040d4100c12010604109000d44611510100550301c5624140517000301c0e140030080394060b41c1c04011a026103d0f903600440c50a81c0300d680200100000502440c844d542e55080d00c1300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 140908588 1250 140907338 140907367
    0x21216050a0b012904080c010305100302150a0f050403030c02040b04140c04030317040807030f020a0f06020301050f010306030506061e0307080304050108070207050108040210170106181a030c0f 85
    0x1303040055146090f144468000320006551038400011000042c030003004401300c00107920000c1603082c40c3c0071419454840c80b19a1162079504025400005c01c140c200c81d5800000c044c0080d00729542d1a02d15642c03583c00700742e43724071503404080c001540640080b005820203420842110300e001d0000101c03041046042c048000c0d01340c90f90148048001010001d2540c840006140c0000c0d200d03035090903051540d2807900e20b1191107801418845540c494229482c024800300e040385801c24400c0415140c00e203004c80007541f09005031845400d0419500444d54402e101d00303015079602c6001003c0c1e9895110030480c0c07401408040798044912620000c50540b0148801001004400021600c5604102c0054a0050014164011540400d204002980c2c0c000209600687c050b202c00301d0a1002c64021500203071040000700c409401500005400e41d03209048080712011645190020303901c0769000340301d070a09040707410320102c42400400c50b00c039082001001c240704140718080c6000384188030140d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 140909838 1250 140908588 140908591
    0xf05030d0c030204080709050f040b060324060114070302071404020f0414091f060c02040b0d0507050111030408060c03060f0904110915090f0907050409050609010606021216050a0b 79
    0x1e000070f0700414104a507410400c03480d0058140400c090100e480c04440320f04c94544001c20140c894014800492001d03101440110004010345410007425850f00c00301110b50784e01590110700003507038401a140c00d14a40b0003a40c250b598942d016100907843c1100800307a0241c0381241c594026800c1000c080c00e00d4a800082c4000c010041c5044601c2901404201d4400c200501440700b0062a01400610800d42c50544042c0c038420b00b03118086500034004100140601c07031016070080c0c101503100060000000d60344003183d0090707a403280c604581078589910f81c0190720481d0110b0784402c01181904200302e01a646c800ea001c1e00c07600300c420499002420550702650152032001400e03c001c080b500700140c9641d80070b440c18041340c80b000340d480045002448010300510013244808007050620f00c0501450b402003400400030310020800e400c0c0951203502c16902481190300c0c0c4200050080d0021900d05440410043d48508140348052141d120401800d400c1380d941c012007040c100061102184035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 140911088 1250 140909838 140909861
    0x24090f091a030105010605040b03070e060408031305011e0c051002071b050a05060d0f0605030f01020d050a0e0604030c0f0b0f01030302100e0c041d0d081906050306040f05030d 77
    0x31406100030580707100700300940340d0014000d074181801445115046801c40d412514030400c41c5980360303540f04044904480700795a5943c01007000500007a1001d000020340030300000e54510031030450380c13500107545041d40009144141c1e12040328001c0e94034013a04001c501980200c0c203a07214a1441d0451500b20b034441c02d0f048840031101d10705813040d00ca512a070b10b0301034501610642c0c0b0751030820001541c940504240700c0c0e861901c2e044048440405604110300800b009001c90b5030074030040c240140030f90000a0000714803482c0c040001d0781d48415020342d120840a10000c1d0040d42c4458400700c3d82019007280c10381704944021074210006161320b4100340b0843c080d260760170065040d4a002410250700014246c0014182003424050030000324001441c6142140e0020319482e00304505104901c200c50701d1016030080c0f01d041c1d800607801c85400d510484c13584480340661602d081e80031045500c03a0003030356010f038041c80020300003800c001401d200f42405141228104502c15012500360740913030451 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 140912338 1250 140911088 140911091
    0x10080a02070c090e071e18180c060f14091008040816030c030e013f0e010209120d0206040602090f10020c03070902040b2208060f0105130624090f09 65
    0x8000702c284411b4104c950103040151080300c50700e0712000b40040c2c032103880d220900a41c1c0300b2003240085031074141c0c0d11440354425115292280d8031100540103401080300c4c01d0101d001d81450601843c4140708171404118020700c8680e070540040320465600d04010000c42e0b5480742040000420304010003060b44491180d0b0704c1c14014482480e0060502000b42c880c00d0602030500e01481410b800961440b80003800b060b41110311104005800302a0b1440b030390320500340c1d441d00070701e42d514280640080c611a0000e07130302005141144540940c0c1d484061441d20300682084000c20002032054001f031288610007040c8010072014080090140814a6a00c90242e80101c03000101410140108030050240b46d40840c00c0c1454840b100c1e4442c86800b543c00121041d400100c26500154081c401c05045080200c0e06549440c64100249240a0081a119000c50885861280348034080c039002c1d107401a145034800c1c2e0a10506490398504c0c2e100301e40038407a040b6404180114408018801007501940 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 140913588 1250 140912338 140912353
    0x150504090c02030f12040218130611041802040906080d14030705040e1e090613080c070803040f060905190504050a0605040f02070204050105030c09060112020c10140610080a02070c090e 81
    0x1003014076a0010304480e400b607a224104040d18403034075403104409d90400e00107c1c080700b682d080d106481c0304a400c18030091000b03030003174400602ca03075024209542c0c180c0c404022890311620019543c00c00240100c00245802070310703a5900542d103014640164490404030b007480c1d203c00c1d9400740080d0894104011141400c00385180c3c180120803203800c1140380000e00079605040224a4610090b024050324032140000c801e1000e40341003025100070150401a03d8131180c42e29030740c50348481184038850005110910105051601c51080d20100c0742c000b24a60a80d0320b8181448040c000013409004c04070b9955600003619210b42c00342480c005102031006070f48200e1803042108503401a00028047d0f8004080c49029484011480b900000b0074203200580b02010340300b1501038410055045400c0c080c0202e404084041034200c0107580881900300040c9a03685014801c82d0000078091000040c4001d0204143c50f1095000744000703409103421400d01a11641100b040d5141070f00403a10329400104c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 140914838 1250 140913588 140913593
    0x15111c030c080c16031b12090609081c1707080601090e16050c0a0c0b04030b0702010209030c100309020301020403080315092e08060f0f01150504090c02030f1204 71
    0x104050308100707641805101030500b54071003c118002c0b2079072140c0065050050800303050141e114a220006040c941c0c0d01160014038241c00103100070951900031502001001c124140131300da80340103442c0c00720f0052001d000620500003828484500c51400c1c008400c04445032100341503050b5100c0c5410b91034080c1c0c01d0505c10001040709030fa40e4006900000c1030303004c1c8510400c03d0403900d203940100f45082511030245600c554100080301d1401008594a90000114144544041c1c4100ea025500300c3e00c240da03d10000340c2c20303482400c1d02140e06070131205100303ea81c0b85c0360301484e580302954600059024482d80c08603007260710503002501d24400c04400c200300096909500140b04801341c03141205818100c0c121003014050700724401c00b0616840c1005514070002881400400b160313001c95009040035241144480d2003928100e8085c1041c000203c0c0c130580d001c0452008070002da484501d0b043ca0414048002d0802d00300b1002180410441400e0b0b904010f4045c00110300728401c0000d1908061 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 140916088 1250 140914838 140914841
    0xf0a08010f0b040614030406240302040f051302091815190b01140c0102070f06020c060105191a160c0e060f01090b030a0e030c010e012415111c03 64
    0x29801040b80342c004010a20400e50711511078510142c00001403a101c1d12246440b00150410b8100c84000000d900c40102c905055260b11004890099904101e181742d00b0801c14140c1c0c4040351143c40c0a00d120b402100141030043e1402d038880d6280c010f60750300080b078920380c0f03041034030040a00002c00e01138002e000500081080d0009044000b400030080080d007880013030018402030300146042c0f10701091138901c896013901102d0b01a58000c00c4c6954208492500c90025001007940e1a07031446440e0010602d402c103540b08e80a000405030500152500d041e8140c420054200700c2c040002405000101c5074114031b2028120041c413518141d41031906144000d2440300000b81403904c1030088404968699810170208029201504060f030b07543e90f20703024032601a09140c41a40d005201c00a4195489101940328140302c0202d0002440544101d6000802e034503c200350031407070441039513410000c545101d140b01d443d44070103040c04030381141c000c400942401408403020306050140f20706000801d505 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 140917338 1250 140916088 140916119
    0x7020f0f0109031b11100f080a05011a07060209040e0d080901021c0f15090506030c04020306060d1d030304032a0f0204020903011413020108071d0907050f0a0801 71
    0x4039000700002040ca0700d00408810704076045003100002c1041c0002800316952010070107280242c80f80d01080003116000348401400009134001a6035a00855840403036406498100c5100459031841c10004681801c070a0340701c4035080f01c03015030070070250319142c441d03000e05a11001e242001c1c005881801602600080004061102ca41d1040009984039403030344004111583c030000001420980314400b640081141890740c03100024924000510030b0242c0c1c00240c459007003a01502e9010200005200503800b060320240d6008400b88800d14a00301244d000d80112001d5803180740c0d00840c4980c0c040d0456009403020b600150b1461188220385000902c0d2002e1009440c03514080c0141640329181e04501441d0024811900090103c1c60350350250801c4001101040d0803856a091554900000303440011302207020500c80400540424040e940c100c800740103e8100a4401800300200190003c004045d0710605c44248042c0c0a030f081c03450007034410611a61034a02d1554109600150150107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 140918588 1250 140917338 140917363
    0x7030c150807021203040204091406011503090206090d06110c0f060609040b1b0904060602010209030c01030b0a21061103070305010f1a03090309060c03030106090e060a060f021507020f 81
    0x140341d000d100c1456400a4502e0002241d44405516a1039510024000d402c0041000c1c0006501e41009803442b074001c61510b0490b81c0e80f15507458090b000000c180c0540355a1031000e540203206000c0d96045040c40202e400e2500c1c415900094004d550b101c2400301034000035210030442e8032244c0f00c0b404c080010050f440d00400200c03680340052030580c1d1900612000241032003061401405140380c1c1b641840140c8940c0390b0300078002d020454035440028004d400030342190744640306140510045d54000e201d124400000503040400141c03c202208c4044a00540c180603440302c040380c0d0901003131192190300c8038019941e03122035407810007140040070b0352010b810450540215290130008001300e0200c80b840d684440c200c0c0c988942c2c0300c072101c900314024400200e401c041d0000d41015514030210040d4141e803660707121031036207030303111841c880ca245800c44940c0d0704030289178028410b0350300602c100744400c2010310446492507102580c03031000040030b680d024003590103441800103c090900002e0b08014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 140919838 1250 140918588 140918597
    0x1006080304030b07110109051b031b06032e03080405040f0c0f0e0f10030203010e0c0705100e1906050105010f1107060e031203040308010e0619030308060103090507030c15 75
    0x42c195121040c0072100a00650240054200107122180003900300f88107454000081d0b82c0030b140003003441c0c902500312621300d500c80d014180c0450440d800c60018000001400740146083d517503840b044401c10868002010400d086080c5035040e00308a08060b100510b106a940a49403442c01d030a000540359651f12085019003000c405031409a07002044414550492a10018412402002ca4808a400402c494203c04400c04080e103698241c2c008504a480ca01d200200550b03848082c46980d00481000902c1500120f1012003030710b0301c40d000300922003416425242080400040c1e4081d02d41c24030011944940c80b80d004100c2e640e048100280368025504000a50b1160908550340303440c07070b5000d00001e11070b0485000205441c00c200407088100655401c55482c10b06040180000200b40308400415660030300290070713030520724001c2c804040800c1e80f044240341580c3e800d54401100900d458100350350358940c08049281080214000c41c090b02300001610f041001020b00660703484000000d10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 140921088 1250 140919838 140919847
    0x140a03140306031b06070204050112030f020a05030301151e030e070603090218070215071d01050903030a0806060f0406090e011202090a050604290117010602100f0b0d0510060803 78
    0x6071000700d0302c054160180482131040c40c1034100054624040c084007c0d400c180b0301000840d41c84901d40101c2c031210300945461102558400c41240c0e40c0807a85801089038000b40010069100c1814100203070441c582001210402000400584001c074044034100294a0300070207241d028040c09440c1c00f80686150500c49aa01da40108802802011075104065a0100003880301c03403081c0410050b12100072161700c1703e4140144000c01008641603c10b10748140420103111641c0100d044030703030303901c4040c01131414500c10f80c005444458000304200d4204e030b01000300b503d01c450b5020091014100715110f0311101ca00f0403218690050050700030003a44204500354034003582d1104001984000c403040041540da90320700109010b05414000081418002e0150364415901c07a00480d003007080a90b245408a15200196410711000303228a0015800c01c41e200d0b8403c00d00b51308031002660141724040350050341a030100c0e032581c0c40b2650680705034000b0b4442d00000e031017502460380207084480045040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 140922338 1250 140921088 140921101
    0x100905010504030f08040801050f01030605010902030417070309030804080f01110c1203280b010f02010b0a090c090810021b0109030806010327120f0809060402010c020d140a031403 79
    0x20b2107a4007003e40703030507a680758541c2002001e0084601030581c40000b0f11860401c48810169a00e00307010032940642080c0003c22928554030999115a0304141001403203400601103091952101c3c0096080108058002c0003003042c01e0001d000501d003440003456030110402a0a084510380d500000a0359810443c124900d00c0016416421088642a0607529210075620711600741c90004030343c0f514403a10144030b0000201da80070300c42c00340003038840d4bca18841e9610f04900720364251291640c89001140c091041d01455402901001400c1c140030000702e4440c120b061070311201920ba0100150001022003044803940842080ca14000000b8800d4940540d00500381c50002003c1904265a400038010860701c402e00300140743c0c1941c0d008484861250a2020090010342507200101c0c40d500e00720503556106d0f810440c42010450050522a12140e004494400d180719040c0d9102101210b402c0c00314054510b0305501c1c0e10b105000301047c014501d000740200d4004444940c0c421001e2081141 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 140923588 1250 140922338 140922347
    0x601120b10050307050d09050304170604200102030909101a0301030f0803130206071109070c2609120f061303020d14130b0702150406050703030e070e0408030610090501 74
    0x111510904102d6100e950b4084100c403540162a41800c031281841001801d10001000402c15196489105c503188103e00c0440385d9140c5051310010304095841c10041c01801c21000c00a0045c401441624500401d030700003c0c012000c182c07601c4613107506c0010304025590507895178220320708501c003440742150314640b1030008101c480140600407960004c0000c06400702c039142d0b40b0000e81d00500c4240c0358035244c14103180d071a900840d41c43c041d52900c00800c0825005010b8000002d42c080752a41580800c2074400c048824141480e84081c40180041c480303958911a0000c1003500640082c10340700202c0d1a024503040303024140b102019071b131803188030100358041020507508515003060400060080f44070a414800d0081c00c100200b46400c01107000d2000f50b00404016008580003492a03c840340003041d01c0c0300710303c5540c002c94404c002400006c1d000b80c11a4115682c1c1405862069681e10307000f2004220480d001c81d498100002080040d1505a9650700400e81500e0f1912445044c1400a030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 140924838 1250 140923588 140923609
    0x4050301051003020913020f130207060b012a02060d020c0d090509060d0605040213020c0304230609010c110405010603060518091914031201030c0801020702060706020d0b030d05030601120b 83
    0xa5841c0c1030011b00100f0343d250700000c6000c46030007401c1c0342085400b04040000940028000310307500c40c2802c001d18095841050024800d02c0440c0000c62804c039409058240320b07120480498100030f0611030000c0440781031010746885084a80541055410020002e050f180c0a03003003680700e4095507091044540310422980150356001d44001440c1d140da000142200381394079088042d9900001300c4021101021000c3c0003150b1200ca10884264510721401d900403051314950368105c10180701c080c00b25032003a052010f59901480310720298511300404601a141f090b0000d40200346c0700c150402c264101071f01a0100c8101c03615249a69040100066840701a403407000c4d40030909003d000800e2142d050b00807010682c0000c122a950a4054000183c030b000034401034aa01c4181640000e03500c20600840d0384981d03000b4011b91500c4903036601c9900a4001d004540305455030b58102501a0700d08002003540f400e00c035101e141d20380c540400010400549c48011620381d9040403a00c0d80d054417044000b4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 140926088 1250 140924838 140924851
    0x501110703170a111213060c1a13080d060e0a02090d0b090c03010f0b12030703080606070c05030d230c06010b09042304020312190c0c0f0b040503010510030209 70
    0x2250340f0107050000b1100d480303007200341413400d016030710328500c0700c800d000028104905550350640c00d1590700c4005440b00d08121002801c0003414401c00c802400d0f2607110300386c0c02100c2c0303620a5061407441e01d80203643d0300200321080415958140034440d800300c100b0a2036201c00455002d500c1c0c035055001049240700c50040041c0320000b098041140c0d00b906006480d00600d004d0003c01c940484650128083c004030350340140180820665440c1d040008003c580820750035484145541d100c8100b8455260f102510943d0582c1024101050b80c0d40c06001308016903955a42d039120000c0003440500480380c044142c1c4848220400c00703041c810f00d010803010304480001141c00e031241e8400c80810040c101052000351a50941c0d041c0701e044250242425000354002d408640d2003011100110116108048107400d2040d05000d010207540d1084d00c080d48810702c1a110329440d107503166009000440f00d500722402520f004207061005007824400d1070790101804900c041c03924070316008a9080140540003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 140927338 1250 140926088 140926133
    0x4090f0213180b16020c0102031e041d07110d0903060207060906061203020c0f0a050f0103110f0406020111040f060507050705030a150b04061404020c1005100501110703 74
    0x9950031001a42c00490322800c6260000a800d4291402844150003218905900b0441c09400103410b4800141c0c01070489061300198500341e1000300c25a4405042480c119500c1020040460281d1400c17001504842080d400120307282002c0c0300150192904034180002580225200000c82e680f0925803422250010390040c1c2c2c458441c109040a840032546c00740c9801c4c240880002c0b01c0800d07404849519003e035003550b02000d801002c004851052a2200341d00c1480d02005210928050402403000742c414100080c001181203c145056000f000902c1008040820108a80c507028090031a1090760f601d5210728042c10320005020741c1080d03010303050401402191000801804119101c0070380002000c4a0164545190031181608040784a410080c1040310340b00d4107080034010b25081d03031988201c1c01412441d141c10300000390002692501144103060a0950301c442c1c070300c6501c0c003e5045004655500c0d08000000d8007484a5130381104041c0c5c4649001c10101e50be0390460302860130008017 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 140928588 1250 140927338 140927359
    0xd0e010917030c0111040302030706050f0921010504210c0c090902030a05060a0501180203070f0f0e12070512031305010f05070503221502120304170d050a050604090f02 74
    0x2a0310b1070040304580c4603250700e0b1441c1c00d01c6480c150720103002241c2c4210200d1b0440b60310384400b11603074050351010b00d200803414810349400d0318003c0074280c051701603001542d0b00590039110701803c0d50004d54050b80d103185503031231142e8030020340d90141400030030310300305890101d010b07a58501103a4600d00c28101d40654903800101150f0302402034840180d042030464005061401d2280300624080c400c0901440045801c00c0d030807000d40c000d991103a10240c40b81d008200002d0700590f000b4070714003e0301080044c1c28508504c6550340396000d440b4014070340c0003080803d003804284406c059000b000d92010350f01c140301d440c0d58001c0000c0c20382c0c180c0740c0c00e28201024051014003170b221405015402030103400040390506032008904908540e900400391a65411540e91001c2d07a108900510b004005810140d0940c01540c550001150040d204490107666441142e8078511349401c440b81d9466001d841e201844129005806041d4002d8402c49040007071030501e58800d40707101c00351540240613000101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 140929838 1250 140928588 140928629
    0x21f1b02090f0c070b0103030801060207050103060b0307031d1504050c03010506031b0103110307020a060b1c110a12030203030901061a0405120f1c080109090201080c0d0207020418050d0e0109 84
    0x1004d540a2640c022010780715035860b854003521442090041c08014400c6e180005481e605c24014502141d42c12140586142c903025000c501820300740044444035120200400c03071503e81000f00741c40d045c078100c20554050030149000c504190000e00c449109a050505101c00c03540c0118043d116080b90944510203501c001c07005802405c00c00700c0030701c80c0003030120070401c1058002c201020900e21841c010005820702c0c50400000c0d0303c52951245103d01c060786000000f9020465000261400410019200359100510501480111412030058001000388040300c0404d0090700040c02240942009090503c0e0101c0b40d18000ca11a2a100f6420000c000c0742c118000c0c0010882403003007501341d0742075114900000045e00d5031000a40005920000002500c4001e0702c0788a402c0d5034140c1d12000142c8844400c414280c1005c0c005070070b01c130b41c20800840181d80e01c1c445c0e800c9092184200e03011010741410300b10305164a020341c0c0c00900a007408800e051b1ba9204081c0300c1960005408184e00041c0c01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 140931088 1250 140929838 140929861
    0x6150807021501060905010e010810090c12020a030204031718040902180106050405210a020103020a020f030d0b041404021027030516050102070b07020d0f021f1b02090f 74
    0x8a00001509207602c00130071120352202860b0b0a0356800c0c0c1328401d104d440d613401101c0c1c02e1403c4506070364096a162003401504655082800070751114a4440703105c184400c2c8a20880c6e22008050002c254001000c00400c40ea005041c00008003032030402d030920b1720411420800940d15100684242e03a01c0d0080c500b1540c40140c030008050000150790055038403520003a106510500500d8420010021028038120441d0420515010164050044000c0b141d0055003c1c2d00604c0090f03003940100c0c4c5071441c0c522810000f070800000b0040c1c0101d1591084820311080b00d80140900700d12130101c008000250f10b96107c854121552460f2100003d01014403c615802c46002d140390341898408002050203400511105038510040c0c00d14881643c0d01c00699a4080301e01c609809c215060001001600d00302200c013982c0c5001d4030200b69030850540c006280b49060700405840100705110b0002600e138000381d890303110314038494952507090791074000640c1c0c070400038050302e0500d03c42d4000a43c1c00100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 140932338 1250 140931088 140931103
    0xa0b0a0b1206090a020112060501020c0d050111030f06130b0303160821040b010905010e0a020a1205010b0a020706020d0509150d1104060201050907031709030106081f0501090615080702 81
    0x20301c415554036051a55509071244180d04040c3e0028407034110a19412503940700d600e0481e80144c00030700440d05c036003007803055224500b401038035155605c1e0742030040703003026000440c0300c1c0b000c40d1002025880c1582c00c00c506d6030300d0201c00301d524500e0042c0c40c110a1b10f000003162400c440a601081c040c0703085203403c0e0414403e6100e085a101110800007822420680140c0e00070b40c8a01d000c01c2c016038a80185e00c08a4400348254251a4101004148182c400e0740c01000e0300d01c01450000109030704003400381d05441d02030740f11401000000900700a030700e9040c850715003e0031b4244040d00403032400d44401403540c0540c12066110314130228003240e150480c3d904607158200040350034403114008880c0d4680300d4105120f042c001d9402c080c00200c904002040c00000d480d4040380100203c00d403407503d12915004517030401d404d90368460b40482d04207400c01c0402e4030404034103030181c00c0d000010300c0c038800e549040c1d00042000c1c2c01c0034000e012244440020305440c50462070100c80a0343e45d03000403450000c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 140933588 1250 140932338 140932369
    0x129071a2a03130c080d0f080a05060306060d150c08060103050a0b0102031909030606030606240503070e030c120f010b0111120a0c0606030b061e01090e06010c02060d05090f0a0b0a0b 80
    0x5d995103540e01b050300020f8a050440c410740342d220750355541038803e105407403088500e0350f0300d80c000c080001c805140007074016600c140203030345919403007194a00403130031214520300880104080030200000c80d030b41801480c0d41300d52010b070144003000910001035a2805001c03941542c0e41446028803803601d10a0f07410070010740d04031405000c115900d0402100070803c9014079000e0801000c4c4595111905900f810071038a41030341e5483c40c6940c3c1c20300845052075200401d07a850b0223a4030782c0740c1c81a911091098514801c0300d020301440da80c000f100c2400c50710000c24240c180010b0302c86405a0740004100c0100402c0150724080c0d494051000444203001c41d028005d11141c94a5400b0090240c8214801d1054009035040103008203507a28112a000303142c2c401e20300041c080c2405100c2d044890745d801e608070718181000c1490846503800034100b45c126030340441000369035408100d20250100012101d00b003200000e80a048107945a80060300e03c0180400300c00c0b5210824000e50b600c8a1800030341144 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 140934838 1250 140933588 140933593
    0x803010b0712050f04291216231e0a0906090b07020d14010e0a050303090105070801050102100e0307080a05030702150129071a2a03130c08 61
    0x6031100851440c6070000301003603030002040640340d00321030b008a04035643d5450b03c80e0001d04061420f590f104400c03894596820009074050300416400c25050b0291903540384000c03038500720f803600840c2041c0f190f800307040c501c2c01c002900301c03841d001d003d01032040101c015001042d0ba1792168100c0c8884654010004016002c800010b414400142d004164009541d45c0e13a4916074006c1c0e0320301a0b0092400740b000c0180d800200c50036070720002075102d80036004c4002c3c0360f80041085000c0ba94510f0402100d28000d0b515900700104001a80b4421310070541d1061907414001c4042d4141070000f5035a031540c048120500341e03105000d0381c82c0e40b020130580d080c03660712010a980e25460328000070701036002a200100948611204d4130b000c0c0318de0450070b5042c1d9001c404813440412034800c280441005641e6101e010120410184021038820504400009241140040b150800000c2610b1503c44104008042006607860b8901d03680600105e0390001a09400d4420b000b0007414101d00c030180300d41c086540303403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 140936088 1250 140934838 140934841
    0xb03070312030f050c0d0c0309051e011d1c02070816031a0114010c02040605060c010522080a0c02030c090f0a060b040f0303080c0d0207050a0b060612060603090a0803 73
    0x4100385441c003580d403140d540c0c14041c280716403009605a910030b480703082d07113404240101c1541c003410381e05c1010409000d20700421550084e403070f06804c000b00c0310507c1681c2858507000c2505124240150b071060704034921104c00d04426508007680740c880e20b400e48000000760741600c80c901031080020202400d546800c1e1280e0740c00781d11103c14821500e01c130484070440181207000c55202c640d10b140b412140007960b1043d03c44540b100441303084100c1d18040f40d01035514100032815440303103000350590f0501140001442d08094036607030a40c80c4100e0031142024200c1c03400c1000180c6510a55003004050f00f44181402d14510000b81803e400f00582c0d9044003141c000c0000841003500e10764041c02003100100300907a160708450b090b92041c0e02681420a02415040000038821260294014481e9400900748001d604941d0140d80c8585001d0f03c059011000030703403e211220020a1300280106d540c5071601c40100d80304407408000034030080c454440031002810340c3e10f081c031070101525031081c012640da = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 140937338 1250 140936088 140936093
    0xa030212010503010516032304051513080d020f0d0509071502070602030f0307020102071235040b09010e0304060908060f01030c0e0a020915121f03150b030703 70
    0x9400c00040d48030141100d400018480c1010b1184a0151800c040c0d01c003240c208680f001c1c1c002c0e05040c444d0821310541900480001c01091405030300441c03055020b0100504013103071803500c00b100600510500d0b0515200a4002040001146c42d050321400d030160700d8207a07003c045a1140110300881d00328504000c100103182030045000300030b98149255101074040352680899030b850b60b82c011200581c0c000c00c048003000340400081c0d5407140a903c000351804c1250765581c040f82c1150300741ea1780440e900d40d1104d032054006551840c010180380740e04000e840c05e140d40013680301c000540302401c82040741020480000d0290400c915031340c441001c4a030f4669842c00c0c01000ea060324803c0b080d090041c5004144000800b1180f603040b40c0c1c10461680d41c03182800790790388902c000034200181040d03003084124803c3d21500080c4032102509011148c0750f05160305082003c446c0100854121301400c8480800c0c41840043d550a0f0380e00030306596041030300207088200034001898866854412100300104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 140938588 1250 140937338 140937341
    0x50309060d090c060306050609090a1805161406070605060103061e030215070201050304170904110903061003120c0201090810020717030126100c0207060e0f0901060e060c030a03 78
    0xb01c80e44942802c0d55682c1e5078580480c1122414081e55074460b0040202200034a0506143c680082045a0018081029040e040800c00495004845039002500380a440c0700c0344000060080410780d446400d82100e203400581940703d101e0006001954500111f00140d03c60351011000d000303588410154003200c1c0d1055442203a0074401244101a0201c7d40c07040e1084141c00d0354412a410b8540c2821910343d0b54035a1001c0c0301450b00c1e0300010205201105041d0340c0c3e4000c044c05190180e01c419a03c14102041c503003001401040708225040c502d500700300041c2c5809481e030071000140f80208200f884c03031004030360808450b84403002e03503c5402045043c1030815402002c0c2144245c0d41140380361785242c08503003640000d1280c081d40c0008000300c034981d960760151404080e6400d82c01e80d07002c031a001c6000c0084440704900400107030b1040e5424424036030404018080c1d101c00f00c1da9000c1e00d45809000070500101405240c01700306110b040c010705500c030f01040d284800020010b980d200c1c0c503c20070050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 140939838 1250 140938588 140938601
    0x30809012c07060306050f0d02010c120e01030507080603060406020d020d0e01050109060501091a07030c1a0f0703020c100c0513181a010804060b01020304080d02060405010c0504150c050309060d 85
    0x9445008802c2d00007901c3d4080e2141c1c1c0100c5202520f008880e13051714041005c03541c010380b0168140010202d1040016020b0350f07410400c0303221612614008481c0c0760004046031341c01000107040c0a804c805200c0e59030340010b401c5900a51050300566540e01014244000c0d01420f00d0b02c503c25420a0701d42c1c50030301c4040d00142c0c1600c1010740c2c100803080e03403800110317a402401e100c0e1000351856000000384c010b51444c02840400d0003400d059003030222a80d2000e44a0200e21114041c0d0003060003840749040c49520780d581c200748646001d5080500141e21243c8558035410001040d680e100b9801003098001c0c001c3c0c90309a0300404041c203030950380e0742c40800c0783d0040040c05800e0300e10341440381d5240e0601d604680d0b400001070317580c0e0f09a40d98950781c1d1750050145150036415031200307000028280404001c09684500150b014002c0313404c16181060a6a6a101400c010f028041c80188803a0544480740d1610155905e000c0b11001d80c2130810a045d403054104094000600080b0309003101e11741d80054 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 140941088 1250 140939838 140939921
    0x1903031b120f0b0a03030c0206041d0f0108030c030406080405071a030a0f09030c0305070f0210050403021f0c080d11040b04080d0201050f150f041802090a150303080901 74
    0x1e001809144404004440f01011a940d125912007000c3c008648142c12401d4031034400390656107015114119444000e1100342d055400644400030490311502c90804180180f01031002541845003a40038142c490003a40201c03000c000240c0006804d0000800c034030001009019401d1003110019041503540380c0c01142c006411070700346040c100113160184074169560382c041d5100250000c8640c0c0440d80d541c01001c0564610a686a1400141c0e880c448210340030fa5264a48035030f00c900e5031040c4030341c10009800d032a03106a0b450240e00d20b81500080a150042c1e40309d460f169036203017170116030742c020023042416030103e11021802041c90840c100c01030090b5215074044408540d50040f00301d003a0f40c000c603408a0318500d0301001ca22a480304480c080b401240040012080342c55490108040740c1d1070b85066861400c60340914019801c1010f06c45410142a01007840400c7c0e40c1a420150110ba0303101c000e0400c5079000c0028620f079000e41c410026aa02518640700c10a07030911044200100403041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 140942338 1250 140941088 140941091
    0xa1e0c0807270e0a020c011401050f040501030804030807050f071409012405090102030405060d0903110f0601060c03050403061a0102010f0c0c020607050c060304080309010605121903031b12 83
    0x40c8182a0402003240d840380507400c1c852042d090500440f420000d0000c0d01303808a09809100c1c0840c00803081c05a10207540e125124801c82e98948410402200208600c0b03030300840c035240040c00820003030421601038a80107400c2c80d17950320b2180b400d03c5c0b9190740c81200312258000e010010034001c9451503020f00120085504146903600c0e041c84480c00c1040c00d200d094915011008070303420300d0040000d080b0840050051380d0400b903450010030169400071013800c41c801c0e84d506200701050340008565144840c1d1070001c10524008104007984c450040c01010b0030710542803500700415218504503070140d6408901030203401c8540e080403803000c102c850703120301550a004151a00402a101d599031080844c0c2d43c1422540c2c80f078003405226440007070280d406004034808905140c82d028000d5001e144501211682c03071500700e103d24215a4507402461241d11110302a020b400c800041440300d13a1200ca914440802c024681039000b001d0155044822141440303c20307006a41140d050224032145980 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 140943588 1250 140942338 140942357
    0x506010e190506010e10050d0e0f2503020604030501050f07020f0a080f070c080718090c0603021305091e01080706020604030809010b03031603030e0111030a1e0c0807 73
    0x420300c0e00c035441241c0c40c0c0c900c0300d61110031555080403500300035004041810041e450b0003248001c43c480c40c2c017480c1c0d008082040003840c4210300c01030b131050704103030741654016000030003002030780584134071000040384841103070010180d4252207588000e5000b19030003001d503591140e992501c580a0002204c03901c9400b11240c0c00101c0c028004204548001d00120251420b00d0107a0b44d502a550040c03000703014010f600303101d06000680410802405060458000d0078042d00d05104580382071040072350381d02c440c0e0400c50400e001490b400640410f0301c05908001d0b0322a4181c0c0c0e054014103030750303920042c0e02641c08814000c4c82e03d602d150f480003890035a00b04030260780e05c580c280e59a0328564071036a40180d120200150110344202c10150300040780030004200c1680c601c00003441c0d50008940c42c680314018441c0d4604160f00342c483c5140c1402424002d10903200c038000b800d2560b000080c4558056901c601d00b60f10800f424515050200704240d00401c1001708001000b400488102d40103004100c0a5a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 140944838 1250 140943588 140943599
    0x106030f110f030712080706090f21050d0c05070c0603061703040305030708090a0f03030e0108150a03060b031014060f060f0d0c0306030f1406240607020102030f03010e0103050601 79
    0x280702c9400014042d00070840b1502e03204040c0c00c05c0e40003031000d940d500c1003400b03000c00246c0c0034011580b10798002c210442d02c118050030201d0450700380e00f1140043e1040c400016404503004810386411241030708001a0040c00314109961910500310005e00d409a102e07401f0400a40603070140094500350b443c1024400d100c4048240e0702c0c441e1780400b030015070080c050540000c407403000804079040c015040250003580c40190401210b5660001c0303010914903c03c0c0340b85568000b00d40c81d84615010440c1070100686030100f8002c00e194040940b5041d03e0b00041d10315900c08000301e07042241004000c000301416811242502c5009548403440340c1035404e400141840d0510940e6010707010308481500d407610503464400204400480c0070305050b1180c000002050512040c081424091ba03581c00381100072410391401c11400500c4410004038985e2144503a11480744184204c0c20b0680b03155689400c2c40c001070303140d405588180301681e04000008500044100c200d00d040343e2255040b1601a602c89 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 140946088 1250 140944838 140944849
    0x1050705030403120e060d0509060a05160c080408031303060e030c0304062304081f06060f140c0a0c06020105010501020d0c12170a0b010212070c1e080106030f11 71
    0x150000d0019841808240040b90104002e8000f40409082411070464080c000c1041c40d040603500c200c06d00d039a181000301a5505001455101c03840d0282000f145c54040780480062005201010401c07454528800400129000b00ca01802d409002c4070707218031512707603214022606800212079050915100404410001040c1c81001550300c000d14105418041708443c04506200d0b606001c001200261944028541c018409001000094000382001e80c0f4901d51547c01d80781c100407103614101d0100308880e4440e03080d900030314051400b08941d008803036411585004000310700c0685d01400802c0c008000585824804440301d0350020304c050b03a6160010380e1640e200900d510003140c2076003800800186400103001e540065400c01d04220400001c000c038214400321443c803a49651203107030300342c25a0108401458120901625841d0908564891501040303902c104801c1c4030164003070643c880d904c102c07440003901c001c900030090550b0741c4c2040e070403001083c802552904c02001c1c3d181c8460808 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 140947338 1250 140946088 140946097
    0xa020f0405090319090e010e0121030509040c0c02030d020d11011415030115030b091e0a02061b1207060c0815190e040b0403030c05030f071b1b0e060105 67
    0x2c40014604007106400c0400c0041c41c1110300c0800c1140b85400480d041c1122020742d03020b0a03281200001075810841d416240d041640380d0450340d031070140002c000090780481103950801e41900d0108810740818001e5500200c00b40d4000c7d030500964a0b041422035000030700c0e40741d19031140d035215058480600e5960032900d0103204946004007070030009205607030a81d000c03040b220000d4000100618007110107445404c5a81045605400e80e005000742d042c1e0800502c00040018010880c80b40c0050034420340c0c8860a540090040f4008a07414440702c40240b0040b500070506e5007510805820301d4000e0b1304c641d02034082240e410b441c4c90640344105200b40c0c166841a442c05603000349603481d003070801c00450034004802c80001c41300e142c04101e8110502085015600c15000080c4505203880c010b400d942d40b01400608000051041020200c4c06100082d0800341909000701d004820642068010300d0000b0040c1c00e0080340007500c040e64032800b5a60301210307a2030380c00f1140c1d9220240111150b114 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 140948588 1250 140947338 140947351
    0x31415010f0c030c0201050f04180506031204050108151903050a020103050f0f0406050a0b03030403060f111c0c020a0210080702161206050c070c0f0807120b070f200a020f0405 77
    0x180c10131804010350141c801007641c003910a1000341030640c0e81145c50b10141d50803510601041e00c4400f4808c8609040101241c40c40204141c01e040078100b40000f02400030080c004805420340300202441904c40c0311000590240c52103c801909031a070804075a2025007550490000c1c2c074000004004900c02d0045d28001c500810303107105951915150040a040c8c081c1c80015225070320722007400107544c10001000110321036040400e1800100c039007501250301c00106c0340030300d19042048001410003100c4100b004110210000750b07849608804a281400040d0020b41101c003580f113000d0441e402c182414418801a4200c0d41120b13520b0b001100034a01034031845c1d43d0000386814a00c0010600e8000036481220b41880c64100b0340d241e05d56003d8040c40e40e02040b07008003005c4061100b20b5090081c1c0c005440304600d20040540307240d80e414001300c00244040108000300040020980c13060414540c41c0810b0184110134000500c0760503144c14100c04100d206807250b8011124038141030040c28400da0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 140949838 1250 140948588 140948597
    0x1107050112050603070503190b09011b051c021b010506030a1104091e21020c0a0504020a03090204060f080d020f03071115130e061207060e01031415010f0c03 69
    0x10203101a507018102c060140c5074180075000000c41c0946080080190318101c3c00007103103a107403440c05c2550300290050807910182e410038401d020304030142032440d41b01d201c183c81c14640d100c501c104600d181e99121819502c0c07803400080d00c038103c183d100841400c1029148000c000030f44810040550360722006800829000001031b907051149840d9100c03000035030041d00c00411100c0f204004140081e11000202c071041400310303502003804004403981c00c108000d0700041c001c0d9804080082d4560149200b0310f440b0760380004500070700f248079401481c403440d4040d1044c0501521081021402ca2541c007520b84507100f22000e95000301c0c40000d220f41c1440c10640a1843c0c00d420b13485440c4000d40f070a00d400d420145d254400f80c000ea9a030300c01414040f0050040b0302c030781410107150140c0c0d84006044680f2400d40344500441c8120041810800c50740503080182060840e0b00058003d0b00c9808070345858038480b44100100e90400c00c08e5903051030401d81c0c4604503403803441c0055403200c0c80d0100140006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 140951088 1250 140949838 140949857
    0x60a06110d030f060801050f090607090b1e041215050c0405090c0a03110307030609150e180c03120913050f040b04021309050c011e1b1103030f030711070501 69
    0x36000e68010007800d00b50310703000300300c4c180c58260f06400c0d82c400b641d40000c101b0400041001032281484499000605c1c6e20b0130512403842d043c1121614002e00301141c101c510b00001041c1d21408840844009010030b0244030300c203001c0b43c140f001018490314142c69185040200090006124104035010b8510013042c42240303454124012120390007840503041031594801614064000c0c00029602c64003290382c1c045442810404628252001200380280c42c40c5051010f21000c14684161680044890950207803070020040b440d240403c01501a5014040c4902190358401500010451404281c0700c50210590703103000b10341203c40c05c54000c00311824200c049000a403a40c0d0f032403038116000a1184900b05010882c1c04100c92620703c0843e02c035071000d0b2003c0380d656080b895000103500c41e60807980e80301d5040c11020340100d00c0007601c003002c0c9001c1c001140c00c2003011380c00213400c0700010b070850341c0303584040a43c9802588140e41a60102e01c0705450381d402c0010005404d415110181c0d80c203143c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 140952338 1250 140951088 140951113
    0x60409020d060302090c07110102010501060507020f0315130c0e1b0307050702180a0e0c060406030e0708010606090602071a091c060903030218030114060607020a0b040e060a0611 78
    0x80d0010084404031607102c1d0400809603503040e4100e4042d41082c0e1550b03a90300902d02d011101c050b141d481803410359040000400c03a00b030b00b003c2624020b54060b203a010138002c500c00000e05000d0780e0991416800b038ac60003846071b900d445c1d2143c02c210381c7c410581444071513150307a03c945c40e096003261404a15514110121080304100001c2e50304002c42e414040d0038040070340c3c00681b03408030041c81004000d10342ca0421103581c42c0340c0180c6905001160203066070001800110f1154410340c02a4014592145110900000204184070080845070020804940c441c3c60052155100d481120010f2149000104802d8008842c603150b8200703030102a890482c084051000381106200f000c07200481e10652030300032650134015180420300c2a54011780d00d0401005100240042215a13030003a0b141540ba01c02c5100042141ca0300407508441081d03c0384228800543d50310101d0b00300342c0c0300c20000b14001132110851202180124402c481c000820b139107409041300e8140412102110591100441249 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 140953588 1250 140952338 140952341
    0x3041502031303080904180f1b0e150a0b03250306081f05010605040b040504200d0504261602060d09030e040b19090506010314070f11030306060409 65
    0x1100506801541e040004445000b201450541e10035224038000158120719441c3c18445d4203203858000b2000d8141c2112511070810782c562659009140400506407640c111103680003210040400000c890b003a8580103580c0e0707655030341c0308102902640c50380102090003070458007581d102d581100c0a90002403140d04802c040e1031f0441c1d00350414141c0d11403020501c0a0144a81d0800d80d0b251403040f03488100c0c1c0c0d07480800b1114140c3c440001c0040500060211404e808125411110101c0e40800c9400b40d640d8001000035400c03403079074540000099510685d00c12078100900c01c50203094221146036550080c588151001c079444240403400300308800355005800004014140042d12803400d100070f40d090300d000c4a005100560125440c10250202850107014001c0300c0300e41910039640010040903102c00c02003407402585840b507103450000c6c589034072951164640d0b10342d80c00091002d080004024150321140c1c03050100181e01810003454501002003141d004500142409260919107800d110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 140954838 1250 140953588 140953619
    0x2a012d20090d0807030324050307090203090304170a030908120909190c090503100e031204031209151a0f221a01020d080402030a0b06040b0301050106030509010606080105030304 78
    0x5611000c0703103141d00c0c0441c0f031200241c0750481c4aa180020b581601482c4200c2c0310135418100403415200010034092030724082009400c89860070310250f220340f138803803034142140615040b46c40060140003810b89401c80005007424468000c0e200c0380801a100c1c140705842d1560b068078035400345020002c030892420041102580700841c40b8900000001c150444815a880d08582500190300000144040d02e001d01c5668405200c17100100015240c4003c071549038011340f02504d0307080740d054000500381400742c0364000d090b2102180400c2103074524a03040e604110040754002a85142c541d80c9a0198000c159000448100404510310b02e000c3d04100141c40640301a8000e81c0c1d51103001150851805014074851444080c2e00201e4100005000a24169080982074108031001e0180700158501180d0418543d0b008035940519075104004540980341c0c0540706a015840c1c28000185942d2561005000302010720091110b19600c1a044400640a0080310323416042044200080303100c0210b42e1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 140956088 1250 140954838 140954857
    0x123030c1e1203070c0e2a18040e0a081c02040801090302060601080f130f0f03090e01051e090a0b031b0901060503010b2a012d20 57
    0x4651000000380450140c401d41c0029040c19086507550809038a8050500e840c140c0300c0c00d0040d42864455120348200c01a03e115043c0145090f40200f20320060844094440c9440e01c0858044041c101d0001000e43d070214000251151006456a02c01e141a0140d540d140c1d04020003401e140c20552a085010303030104100180c1042030f1020180b115095001400003092004000980c0c0d0b4030301d04019082c048024075540c100a214000c22074921000e140d02a00721a003c942240c19541601e031139140d0300c01640307000c1e000c0303500072703880c4410107505c146c00005940c2d1005407038009903a44c806103c09c0c1d00c40c01584000f800300030040c076030b220b05145922070ba0114100d000415100702510119040041d141000545a0000d100e8408641030031140b4031700501980c50301c60716540c540200c4c0c00c0f00303009651500b005a11a00c403004645007411040105404280e0f00802c80722820464a5441494176040364901449070100444081105d21480783d1180200320740c44402c0307040c01c000010692154121 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 140957338 1250 140956088 140956093
    0x60d03050d15090f020304151b030c0c0803090c100f050d2301150e010216060f1806030c0e030106050105090121020304030507150e1f0f05070c020108070305012303 72
    0xa4801e07504d00031a11501501407005a403420036041c6002c40b14100c51035407410782e0501010200060010a410a0501d01c91400240d12100c8800c100c606500065015054100c0402448880440452056200344049030760546c055020b0360f0903542c0d6030b800d230140c8001c00d109000043c07280d002a0004108000003d9030003d20560f07c11380782e409900c1c02c0c0c0040301c2003010b0030000803a61741c0110154503031103801d00091000d05882155408501c13410300407a0104030000c0d0f00c281341503000c1d11400d01007024510b804211640c481100a004242096402001031121a60701c08503040620464080d5441a510285000403030300055504020420f58400300b00f1248440075404101d500c082c4bc02140f00ea0754455491030141000342c41c9118150300303445032501d04022511042c41c000748903268402c01c5e00306070126000d202402c41c010103c1c19a1419118242000c201c400c40d40550340100c07030b6200341c0f10840e46856641d002c4048a109005480c80754082e01c00c0d07618907246580080c03030703081002806c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 140958588 1250 140957338 140957381
    0x10228090e011a0c070306230108070b0702030c0904141207050309040e070801020403050318220e01022209050f01150507020a1503050108120f03180c0d0503030f060d03050d 76
    0x145445c00d82d00383d000381c030095038a80321174a030301c424048040c0481001100040c65941000811512101d141c0309400c0950000956041151001d1180c40d540b1100104040807500d01820626000380c803950205d502401030004603600036048509444849401800543c1408a0001808010301c0d09001e1890305100b4190005100c6400340002c1000d14480c0d40696140c8090004d0000d00d9515404120300c900c5040b0740c4c150581580141030750000d148440046503805d000d0144a00900c80c80c078040701020201d10041c08881040300340d01c4119044c2020030049aa2003084240a0000038082d00c20401c2a040d001c0100074451409060017038002800c4a980b940c3c0c82405c0d6aa022180c000000402d840b480100815842440070310b40d0841c82900f01d51601d880b0550b080d4641c4001030203650181d0340400c0c00000c56400704079079043d0717502c0034000b203103c100141842c6940303402c11031345100032080c08400102541829000301c0c40b000e40c1a11050305003151209010050030001c4c4011980d11444003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 140959838 1250 140958588 140958607
    0x1e15090c020316110102060114220204050a0909020f03010b090403120f020a03090302121602060309010b0a03150b030706090b1803060a0c03180305030f040c08010228090e011a 77
    0x80401d0f111445011118204100c82002904101c4141d000170304040c140f0301c8521480e00c0d50341c0580c25400900b0341c0e040c0c1403469a07000e58004d000e160442500b001c0e41c04000319205411740d00c45103510307000312020080243c0c50002c0600b80c0d0790900c0b5442d00034020030b000c58000b901440351310340b03480b1817001c2c00314860340c00c4500d60080360010815440001d48412180c0189901404420b04150707842100b1403900d12540840e811002e64881c1c000c2c000d039000400607417003002c02c3d80b0403002608014620400c560b40c0c0e04000ca50614002c40e00c2c0c80d42854581815814a1700082200c100c401a0721024055032420100b5081c0d07400c0784543c0e00300040350002140c202e035028407415200d0952a940064403504084e001400c85a45280c5000e1046500c030560004c0b83e0030905a030b6120411454400746940c452815910a9400b076000301a10741c000b0850000160440d40c03589004a144400e0300140c40300c83c18120f540004601c60030510414840c018000e0687c551040141045200040e524105826 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 140961088 1250 140959838 140959867
    0x8160f05030d0b010f03050c0f09060705030c0a020a0b0a12050a090b0705030a060602060f040f15020301030f0b090303040221012414060a02030a0c1a04061e15090c0203 74
    0x80070300340c02c2c0e5030703541c02d00301032668210b20016148a0039180402c500e03d800da181d07a115200d0039600b80d10590f00800c142005594040448081d160b208083d00d440f560080c5400f070f40c0b40b201d00c0080380315148248000c201d00000c181603c1854101d60384402a0644115080000745000780101c01015110001840070844200d2075600941c555644ca5179a403401c00d1810048402940141c0110740040c014408419034012849070410340046111800c5809498180da140702400722941d41540088000800d20201c440a452028003500c80e00410f5039961104d07a40b60720003142c0003035100541a2003a129994844981d400d020400c400024482d8042500c0f0b1840000501c209000310860031014814891401c58185801c441644c07080d042c584000b101035124000c0140c95410024410200401d00c90305424050f100141003032004c4c030605081c10252b002d02065000014a028000300c45810704080307100700742d290400d40b000d030f610441c00d160003540500041e075144411440103009640300e42a51 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 140962338 1250 140961088 140961097
    0x4020a020c0906041406060318120403020102100207021c080409021206040e07050108010308222c0c1204050c0411031f05090103030f09090c0201061d0408160f0503 72
    0x40e0020085403056008010510030018a59800340f030915010311a43c03220326041c00e8001d030044907069260313500c4d4281400c0f00382005040c041107100d40c02c48104442d0042004006030f82c000c0e800e58505e0306001121209a01c95010300135000314030b8000030081801403030341f5406183c0c0b0404a036860155581c00010690300403610450720030a50070140001458a4820786102032489005003400518240001c3c188100520000d072a41c07200003100480000904801d107062101c0c07000e15620705844085050040c003140c1340d0810400301d401541144030070f004051600c24a034a001162804110a40046a048000c2c104603428841c8103010a05c43d611402542c14004116648c55204d190000c80840200d0b64880c02e49005401913005020759103416841c141569010b040646c86009400011a2450400d501544c411841c1004800310181e040d00403d04980701003c480c5849034162400e0b100795941035030010080c1100304121103e2189150403110154010303002010000e81a4032801c0c1540c0c007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 140963588 1250 140962338 140962357
    0x5040c03060c0e0414040210110309091302040c031b11030c0d0809100c0e01050901022b17091c1808010f0606020d081b091e0307081504060504060603020402 69
    0x1c20320b0b400ca2801d25224030091040d0b07030345e16503481e42020740104149142c06d080400400900c0304c1d03002a590001c100315689544043d02003a070914000c00d40e02d8510341601000c900c0746003040d07a9580300b10b02c130740100c001c40d01c051082e01c0802080d00000750f504106450100f400c6020920800c80c018005104194842006844038800e9141104066007030511001007013140500d0f011a5003101030b0b1041f810759885e030080c24541c2e92811144010307407814108070502c08ca54250004443c094081c0358070114905416501c45959200e000c41c01400504000c1300d00341c401d588030709645003082600c0c0b00018000b080e00d0030311100c403190504100701d107203030250807890041e91580740814004400d0710400c3d00070400c0c0d10240440d42170099005100f210058003403e5003000c2c00426181c1620f01608445007004e00421405e0102c68000180f01d95144490031542b081c010600300003610700e00803d55003400c0c001a510b140ca1590f4079910700380202000f07801640c0742641e500300440107880790f2004140300c40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 140964838 1250 140963588 140963597
    0x1207030c17011104030506060603180d0e010306060f05030a15080a1214070206090d390e0103050a0b070201090c03060504110105040b040302040f3308030304110405040c03060c 77
    0xe001c20150300b51500d030104820803c504001c01c0001c0f0702d01140c42c036040f88086407d299251034054100c41a44800c0b0380c281010b018004118030b0a540012131000c0300c21087e04d080c8421070b907440040c0ea164184c542c02c1e00100b1820400507040c07001640c81402c2050500e0f469501c496244d10304546000040d08003200e482086000042101d90048900c004244110700141e10380003565010070180d0103003c00c40b6000c3c8605098210800482e41da420010311401040c050f8021196201d181c1c211618200300003401c4052100801c0a580441040341a60740000082811203003035030b941c0c000c1c200010245411950303141200c05c0007070384a24100006600450340844d641c20030381005010105404022810f0140070003041140c6030000c41038900b2a501120000780700d0b481c04d00d8820141581c12441941d07144008400c00752807d40c03941c0340a84c2094003844189454031081607e41e00d10043e00d001c1c11410b0210030000c101e1905030003083e070181c8a0614459019642da642c1401c3e107a0169030f01000c01c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 140966088 1250 140964838 140964869
    0x705010e011e0e0106050a05041d1609050108030c0a03050a1b0803010801050a06031e0c050a0803030f090c030601051219050c1003090807080304020a030803040503040e070806010e1207030c 83
    0x140340a02d03c3c0c42c46650f0020845540b41c14001450210310b8816940a640c844100700301505000c40d4803182ca03c0b600066681340314101e0f24540400e020750190300806071070903001180101000003a100aa001c04004140c10703105c80e00c05481a40110b22400d081100302d200b83e0a00c0c03001d4903408070a079032280013440d440b541000c2d00a42590801002c0307500080c5055810804248880e49440103c0040010040c55104600f40301103001c03019040290460a601380c00500c19074004020351050360b40b0203905001e511080c600544034045405104d134158868001480149002c41d10360000c1d19a84080715003000d02c02140f02c40340d04152005542c00d8020100d00001030030641c0109100e44018a000c1000d6105551019458007401101600060020000408544901c081c41d0080c1d80c02c070070244d80360300d400c2c0b4000c6e90313950280c01006103c03042c10b40410002800703800c07841d0041005840d01d0358003015900503c0b0810020301c0d406692071244020020210f0300d44010100941a8803220b8040c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 140967338 1250 140966088 140966141
    0x12030906050108010528020d0203100914010b09060307110d0207060809031c0b0a1e080d080c090d1704030606050f030607050a0e0102101b03140106090b0705010e01 72
    0x1100c030140d103c1040769041c201000a03982500c840280c0c4201800041c0c2400807964040c0760080c0507600c91070341c003980f000040c00f4450410540740c004540e0b21003024070040c00c806214070400c040c20303c60340b001d205051100212071301d09003020790f0780031010b03103051880240400580c0d0300d8401075140403000341c2c20841c004d01110394400b283c194051801e8000718504444180082e00c3c3c003010024229407140e41d40c4105e5010741d201a6624010802c0c5040090500850400081503000c02d10624945114920540300854010031845204525030505a402d0000303110522000000e4508110364400e400c0207052280484680580040c1d40581320000d90607041200340000c0c204d026403041d2080e8003030320402c131559031b01c4000c4401c0118540351540201c071f43e800050f0b25042d0079108050429082c0041d915900d0b2100f48012404c080c2503509204113101e1118400d2003540038090704000403201c16090003410100b0009090340740c854000055010401b0014500b12055030450329a0030780b0845144c002e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 140968588 1250 140967338 140967341
    0x1020a0c2705060f042007050312070206150111010f020408010915050c04050d080c01050708070318080f2805070203120301120f02130e0106060f1d060c030712030906 73
    0x1c459407220303020801c500307000000a500041d4404c00c076200d15100d882411043c44203010542007019000541526016240351050302c0ba0080c084031042c3c01540300001e000c01e880080d400380a480e20000d18003070620b40c00011036020b410002011815901c034460742000850600c000c00042c841c807400050041d80c145001c0c4548804505003000141c1448240003d1a03034000484d411034100f02c41000e4908100d2428194034007030300312404019440c1ca42080199500716400900c90f000035a0200040186803c4000058102d95005402e03040c00788444000d40c036058000b0408000700310001d000440310f1000801740010000075100010310041140811401c04003c0b00003641042c61803181558180614807513140380c8000302501081500200e0410342d01c5603164040d003400018014400d031313410a080c19000c2d010a02c240320000c2c500780401e248940c400d070302c0c640c1403c640e4800100702c0d040c03940c20000c02d500a0b140304402d80c00100141c0000543c600072480b88500b054a01244020543c00d003d030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 140969838 1250 140968588 140968649
    0xc090a03111002072301020a0503030403050301030201080603150a020c030702040603111801121212050702060103050d050a02030301141801081f060303080628080703020306010f0e0705070201020a0c 87
    0x4081d54820782c0240445c03050b0004200c4e8550b026041c5070240303800c07100100c1c501009990090010b0000005010902d07038404002d5059038001c6e203c19640d034441c2428590b962038024071464044918001044074284641c00400e0703590000c80c1105e0801c0c001d4ac0004084030941d902c103e550b8018001600708904000420700c1c08651004410708030fa600d45401d01810b402040c000130950b6a0070010350641d1030280c1c8095204051000b0304108514041402951741d034000e0000303485600c500700c001a9414070038400c07600001c0e2070b0390140d400c5900e003016100818144641707a81d0b0082420400c4c03460244503081450080c1074010042c680c3c0d001e449164510700f0380000001410b141040c8080c000702c0d401c020452b400000c01d88070700202c1000110100c1c1031007001d59180f5590000090001030690300011104241c83c02101582ca4030390b650001d04c03012194034498134221301310004c0050020b030b0260001d4440d250040c0145c3e804d0f10b0f402e59071380300380c001d040d001645020070420b56501c0d200002c50840 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 140971088 1250 140969838 140969869
    0x5040b070201020f0a0e010c0606090504061415040b060d020a08070e0303040b03040b04060605100c020102100608071503110307120f0e0c0d0203070e0c0306180606040902030c090a0311 81
    0x840c500100e844d6034169030311421302c0c124103020176004020700c564810300c4041181034104e0410001a500c40c1c1040000c0d000544083d20044c0c02c1c00c1840044624210199002e40c00c440d25515411140105010180180c9134801d41c2c003540521400c3c4809176240010700e9100702c43d5403140c95030700d00a440a01411001b50b101ea0180e44244010700003032031044110f9401c1500202151500c1c1e6a501d09500035103503a800181d005603181c000c044400b40c000b1600c2400707901c00d800b41c4d045032610803165021220070f84a400c11540c40524200000b40399010408101ca00b41d103000715080c50444910309080c0d0090300c9140019458007038210092155200f4102441c85603141440300f4080014200e079298540c9145c03070f10070412a18504110341e0104440001014039a82000c22850b10f5040c44c0507a400841302c460041c00003040e0701092101d51600a482000c5c010225070400e82000061002504001d1080c040204100718100c8150341300807840000714810303103101d03015042841c2404441c002c0c55446 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 140972338 1250 140971088 140971091
    0x6020705030d0302091c061a0114030103020906010c050a1b06020318130603140312060603091002070609052e0618150e01030f060501050a060219031404080105040b070201 75
    0x9000c56907011409200001d074a02c0c01584034005500052028010800010802e00000c06d03903400700003a80d0405840721310041c0071242c0704c01c0c0e0000151901ca40244120200c4070041005100600c2c0980d180c40c3c02000c10b140c0360311101c10507a940341c070b0100808810364224001c6030000207e5101c0300c00c01c8020302018405507083c008a507514440040c1400d003468403070030044801d070f070102c3d415501800c000c0d174010074808000c602c184440340d100d1b070110303100344101c1c110500010241c0c00c2000849004460000c01884c080c040089040000d4010340c50031a041c544810350440032402c201b04644601840b955141c0200521000c20082c030a160040c1c4000103060000c20056040f00c0c412801285101400101d07940c4450080b800315460940c0082410340b03110340c008030078401300345c40740c001d032910030344040086c3d0b601e4108000801c01184500001079201380300725803043c000b00304510000392107410280801c01a21003c141d964100d904071240681d500d034200310501c03951082060f0407680d01e000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 140973588 1250 140972338 140972353
    0xd0c0507081207050c030703120b030708070303030c12020c0309030c0306060117270a03030c050310030230010903021b03032b0501180f0b010801210506040c050a0602 73
    0x1d0314201801004800b1103828007100008589500900485078444a1002641c0e80c521092402401601d003035419403101ca481d100366565103041c002124401d441214008042c02850341d50101d01421030340e440d120820200b694443c1d10302e211070010340710a9070b088014540314403a01e81414039244080c401e0034480d6101205100e41640c01000c10303070081c5074a49894815540305241585004e000880c0000f00f00c01c02d1201c1114041c021804038642407007650288111800d10008031a80d02060303800006504030503100300b00600d0316a4694004001405c9100b5a2550454458049241c0c0580c00c4e00e85035143e1030064101941407100107000c01220b42e400384e01d2100803000ca45d4074080c503200640750706840e8414504800c0303a8545005240748080041c0b04541c2c64086080a043e504022000103e0030001100050318003130054000201c03040c1d403041d040347c1ca440211501000d01610094044404e405240041201840224031071400358024012052403e4140322202e52140c0c480003c40d0040398 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 140974838 1250 140973588 140973593
    0x806060901030c021e150108060c030a0911090f1504060e06010f0c0501110403121106060f040213121106120a0203152e0c0309030204180b0a020d0c0507 67
    0x3600c8200c58207181c0010600c0140308241c1c80d0059840040b041181d8000ca007051070b020009140740008109902a0216607940300300941d90781094400f80351404040c000101c1d92007540d4065032180d8003418001d0b40d40384540700400c2075002c007542c201540081d100100071103640c00e11504c21400e1300a40c2c01f0000f003840e024100001071405081d140c104540065201070b500e1140ca8608411078210008010a203254811041d050740240320490b503280300e100760140c0081c010201303422100c52071030185c2003a6599408200d240c50010030119030142e07090010b61495007d403c3c03a04044d1110b1002c500000c409400d0128080c1d28401d41244260410071140d14a01401c5203c103801c444000c601503105d49403101c04022080c04a0b400b20703041020780000000703000070584080c00341021043d5103840c144100c0d0049a008281c2d05c1c000e408103000f110100014100303584030f01c0d070b1000782036010400e410041e550310341842025210a214a07401185615140c3c8151180d00192186810141e00d04111503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 140976088 1250 140974838 140974849
    0x5100e04060609030b0613090b0708042003060f04050f0d02030c010605040b060a0c060605040f0209011701080c09090115030f030206010b070f08070614070c060b0303070302070b0a0201020c0307030c030e010806 92
    0x10081801160408562407a01046401c0008c05c01c1d404203a00343e143c9025500108811000c46040da400205024103000405040034409941400503002d040142d80c3c05600304400040a0001ca03903500c1000c1c1001c0403c10148400d880c0c0c0e13a80390b0b014541c0c0b240c054200500b5100c194002e039120f20324021820b42603030b94100841d0002032850a00d212800c0003401d001c4001c01a0303600c403070b400c141400004031150032607600038081d00e01c090f00c4030121a11083e00c00d15010800340203500b0300d40e1040d034080304285440b44a03039900103500000403c04690240e510301c00309000ea8400c8030480002504101055014440313a80944201d860340380c20190940c40b0489900d4014601401c0048001208030600c059600441840c540080704241d00e410b1841005026089403072081e034101d0300e0541c00c15030929010017201d000f16003580c020542c2c00d0034050030004940c071801c2910159982004000c092510a01c00340141d98040d803903140010440e81005400ca030720003030075241000010802c00c121551031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 140977338 1250 140976088 140976091
    0x3030a09050c18061002010e01020301090207030818070911040503010c08040b01060f08130f05070b1e0f030703151a030403111c140d060b0304030f18050d0c05100e04060609030b 78
    0xc546981d0170a521a005900400c00500c01c6039443d40000700101d00e0a81580080140c10b2003940e41001640d100c1c43c50081d00800215005100d8010020400a51101c1d03007240c50025041110f140c585a034500000727084400481901011405001c100000c0c00101100f19004002c9800c00901108660398000c0180b8001002400025a4a1a890280940001c4171006680e001d4111849a0380f078080b030750318030382106890101c3c80750802a100e08008484007a2040b10741800c580c00d042d61030308030054015100c03498080300c040c1c00100c0005802c1621096007610b5021642c00369a0343e0409040c0244424805030201c60340340d21421f901d1002d0401c4800200703a4200034034000061094040c042821845040407126800e4145440410300c0340d2000c0040d07014610a0700c0704001c0100d00c0304151922100c0e45118807100f15544410005800e2211321203041c0341c414901e10f15042d40b50f20001c5d03411107040110a001400369141c5500500b494070450b40500524140128564a160b9030415001c80 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 140978588 1250 140977338 140977351
    0x1103040b0106140d0c202811030a150c030c020604020d060e07080f0d0e0d0f0201031107080a0315151b021c0b0109020405090c0304021203030a09050c18 67
    0x8100c10180070f40b01200150750640d00d503110244081141c13443c004050000100b80c0d604882995500403001c000300242c9180304502c0b1011582a00b042501450209000e50b401500c0300c0c1c10595400c40d030f59405001d0030130312912400c0f00c0481240c2a0b510700c011a14401d6413681414581081c1c00b0200c2d40004030654816030440e4044100b44a5240c5000507101301e58500105101d42a4042164040400c828000308030070b074100c0340c2c05041a8000c4a02441c10030350301d42c01425000b0020b020035080e40b1100c00007401810007081c010101000c440301584080c4c0b05491a08002c22031010785907050042100f405507114241200d2418401c00026864003022814284034010055450202d11040c1d0158803a07001490f60fa40104840c10880d0000030405045404410410020881a9031442510180c401c0600b00e00d0380c60740c400410250950024001340e920005500c0b05a100d49404c02c015485030000c8000030803035101e20300d0250325204122000034807518480443c25288289401440d40c002c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 140979838 1250 140978588 140978597
    0x603070813050c0907091a2a1c030204031a0702100b0a1503020c06010b0705031803010f050a02040914040f110a12051f0b03060c09040e15010305011103040b0106 71
    0x1c1540c5802c51411560f42c0c400760304048404c04109a1507008081032044a24021401c45440c8544203404c01520450b810500e844007100910300059946200110301810f501007120821001298a02c04842400b880c1400180e00000d0610801c60a03446551050185c1c1003100282d00b8000c0010b0740368900c01c0480c440490360740d030807080c06036204017541c00107100011500317034040d6800c0c400402030f42c40701710b0180c458883c00340000f4030004050101c5000c00e40140c0a141000b981401c1c1013a180800d03142d49505648604520301524600d116443c0200803d900041c5d07114a8192400180d42614030440c02240c051030400005c83c2403816482e0600c0d6224a064940b1f01c44c0000082001c1a01d41012605400318100c4204000740090045907500d02c0b0454910300204494070031045d42c00c0c1d20041901600080003140c100c0c0340480c05400801002040443c0446029015501c0c0250b0090079076410021100100b003070010030722600c031420a42c00c1d0028950f113041d031103100c3c6c03506040c42080f0800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 140981088 1250 140979838 140979871
    0x403050310170a0b0106110c0105130503060a0e010e010207031d04020408060703020c19120e0301110d140109050609070c06022a10061508060d0c06081506030708 71
    0x400e00d100004040c124004240580d81c00c02e0351440c0c1d40d5030a90f03400312480c10340305002142150180c03142c00d100f00c0d1101c00504920910354011101d580003000c006141512103480412513950a01c4643d1090b01d520303c00052483c0308031085030944040003011007050348100059000700b82c0c004403800310040040c07a1020b40c04131490200d4024031a561000d11240034250901a002e81e154004207c801400802c071941c8010600c80044414403141e0021b1214040c0c80f070240d15140949074009007490000c000141d02c4142071854842540300305000d614142c3c0d1500201c54003a00003140c68090030b21134000b00510300d006004610500e102070100418010500000710420216404803515403817036401d000401d440030403001d800050000c4100c1c9031030262414003a00351805201c3c0e0b40860b0580000244860b0300c0420545140b84090b0903240c0058441d1280d00c0820b0f0240c3e50500104915562030500d0f00d0100c03032016841a4400515110700720800074040c5640e0f000039101e800c00e00040600250 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 140982338 1250 140981088 140981101
    0xf050903031905220f0803242b050703050322080309010215040501060b04090b130b101b020301021306080106020705130b0d17090f0916050a0504080304090c030b1804030503 76
    0x81c501d40f02402400540e000041022950108c40111188451840d1b00b05505c40508200000c0c0c2c0250b0041502c810742513400e9500001290034014800c0c2d0042c41521010742d10b9440d641e065600118500403020458045100c00903801036020001304401c84c0a07604001d000d00000b521a802600c80e2150328a101001c181030040a40c80800140070000329143d555541d00e100c000038100603907806103c0d541000d210070000c1480d01500882c1c0d400102180040d02c0300003001e036840e0032230b1159105070714004001031006031403d05c018098902c0414008040074a0b281e802845482c4c141c000c2003c40d00b0418040010703854800603445a0b01b002c1c040480c1e00e0082401181182c481030901800240f4000c0200c24101e042100030f1012400c02c1d201307050002c501105104903000c00356464140c0c12080d50340405180d12a0015000c0c2100503c0c01900d45503a0306030300780c51a041508880181035552544242c115003511031055840c1050300d07444030340e401442c24541da0721402803018051004c0000081c02 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 140983588 1250 140982338 140982353
    0x2040c110601060c0210170f190e03090901050a0806010e0601121a0f0a0b04030809060708030703050108150c120907050a031a09070302220f05090303190522 69
    0x21094201011a1903070b40e540c000081800c0c40ca036a00360300800c10f1450140e110380c4580c41d424040d03040c1d1000c40459407218408507188200042845031401803d041c1c4c0e01903100c0e50702070000c6000c06c1400440c1c40b0110381c0d04104031040c041e4840c502c02d42040204200341d81c004111181103c24801001400380c0e56000140c030541c99240050200b545401404800d1500c4d80807046160321060f500c06980d000807905110034a43ea5010b0200e80907001e0000700006462500204038a02c40074010b141480010303951940b141d0810380e503040100f0b88860040c420303603a007009070074a0010f004401c6070309410410f44a0030140300715075a08140170f900600088910b2420003101340100b01c09000c3d428100d070381b130a0141c0803410580d6030101905518011800543c8001000f5003aa5001402925000000141500c11131b01c89030000d0009501c5000724680e04003144207240c031034041c100c055556440d046c006a003059004c0840c115440d49000144110a040441c42c0002207414843d10303e05403005040c51038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 140984838 1250 140983588 140983607
    0xe090304080d030c090e0c120a02130b07230d030e0a0b07030b0d080a09080c03070303090b030a0605091302040e1612030311160312050f0406020d020c0709021306020601030f02040c 79
    0x140b004100206000100750000000c1005441840c1b035450552209e038400c1c0140d1140c0f621812800000300000d00c8100ca800c4001c10b9414030450301451040f00740403111104546030130380440304d5048900102d0308a50140143c1180d8020346000d001c400b0034598861860b007202a007044201691800c4000c92900c0701d002c07040409800c074004544074000450f000b00b00201c28001c2c0ca0351030054815191040c1030004d00c0d082500d505480b90000a814800c00c0400e90300001c0c49103548607100e41c0c00180729102c103000c850081031404441d020341002401440151b5002d050041d500e54802100ea00c01c0f0000d4142c414103545030301007483d08007100e03801d0440c003405132510200741c0300d40000755001c1c82d40686402921094420388038898800402e282407c225003044410500780152800028009000c9900426400d6245070b80181071100408045240040c55000360203881e80c0060704030400244020108001d1120744010110b40d811640c0c0c403440b054401c3d00c0203004a88410f2048042070080f00c005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 140986088 1250 140984838 140984849
    0x2041e121e050a0b060109050603040503040b0319020a031b08040c090c050c0312010e010602070305030a05090112050a0902040b030118080711031603061b0806010c03120c0305010e090304080d030c09 87
    0x303c1d0b00c55220b007840d590041c000d446031400b05441c80d1000903242403030810741f072180707420030040d40c1081d14003c002c0280c2d9000600e0101d0090707400070012040c0c84584040c1c19854200e550000d080d42400c0c4100b40760004206e5400180701c808800c100015401900003002e591425a022801d20201403080c2e84501901e0140c0e0401c3c000820102110001204000d040741c804005055180c0d0385c4640c00da8548101e404064801d401c1082621421030180e00180b450100614001c41d0203c10390042408483c3c080d206440c01989541004095190a0003820aa802c0860007005444012001201500d112080c0180f00d008003146040c280b000050b91000c0110014096a0011102e1210b1600364805400211800d070b1a0041c040307006100800c0941c041e00c0c1c50340782c03000c0903160080152030152000c00d0807000c000c06c0601d030000030b0040d0300039400081c4442d180451103506040c0d0f44000500014001c4685a10a00040000c0d1900060801c8804c0c031074100058403040c82c940403181c803050307070b00304 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 140987338 1250 140986088 140986093
    0x70e0105060a0c050c150d110304031706030c0a060509040b030c010c0215040b040602070e150f090a0906020d0e0f160b0f040b03010b0c0d03060e1609150302041e121e05 74
    0x10005240100001f0402c1c40109074003081b071900400340301d2110740419903002c2c00182c2480c240c1d0160a0001c006035820220050444480300070080000d0b441610300e400ca480050404642100c00b802c06000794041e1103000c4010f000c80082c5040001c2050f02a24400b0b849036180700607181d16041140d00310f4001c1c11141c6400350303030f4079104c000c003030360f0781c0200d101d58030004c3c01c40300c0004c640c2c0540346403c107031200300240142e4800e45644c0030845154000381c18800187c0e48d5913018800100144024880090602008a6100f50001d8014101101c40c44c4400f081c1c1c0015020f922048100c265440a55164104050301d0f6840e0410900d903a0250f50000741c01c1e841c0010011442681940180485a030220b0807070740c56a05e202811004e5a00c0d502c201340b8210042c1000c07404452003200130740103803252440e04c0302195599401891000c001c00700d009001c2980040c00f8420740100400c020b5408a0001d00d0500701c07403500310307203401d90000d484014110002c403007003c40c90006410854140c1ca50040b04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 140988588 1250 140987338 140987359
    0xf0f031b0e090f060604060305061c0507050a0503010e030a26040f020a090902030705210114060a0e10030f0c051306080c1e0d050a020a0b040602070e0105060a0c050c 73
    0x80a4621020081041c0c850325850000a943c003543c812203600c241000391100d41030905d04a0150040c280c050300440d030003070889085251440c4070019607142940580010103a82d490b01c0c040c00240404e641006006e03074101000f1910010700002141e00b20011441c0c43d10011070b169480a50705044a0441e03184c07500340070280414040098488000b460080320322017070803607403541540c00305c03542401d00941641002c2420800380c507194120301d070b158102182044404209810403806c40380b00d01c106448986644084c000d80b400c101d40c40901a0071201c00000c0361f0b05010f035030ba10600250344401010f607181c5005130350400210078001d00041c40b014141303003006181030803404040c01d038501079039443c4e104004074008586007140304109002802c0e420503690f00c0c070003002e0003a583e104040a60307403441901c01c1040180c80328000503006010320184030341c40310705000e030090400b8296441864100c402a0044c0803d0350381c2000c81d4091104c1c0c0c2005003045c040e901d00a0306104400000e103500845403807 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 140989838 1250 140988588 140988641
    0x15150e09010e0702070b0703050c1b2d0406090f05131a06060714010c02120a090611030c1c171e18100c12050106081b0c16140307060f0f03 61
    0x90160002c602c0020075104404203081d8402d89030144052002d030b00c043da0301e101034a5600c00345e24210020655604033000c1c0c3d2421800318040e600c40707902040c442d5a5655590743d04a20510a03580c0100020186c1801c840040d00c40f00d070104184892800d180c543c0001240c21960741108031a9001d42c05111800a040404c03a0140200084a60600980a04000300c0c01c10b003040c1c8200e45465031a5218000ea540c20060104ca0780408180080824131040184041402007005801e10440841141710070b90700d0036000041078840e0f0a0401603004e001103041c050544004400c084041c000c8084150740313507440c800c0d00c0d500100c20b0940c40340c090003411580003214a071078024400c408107907180c8075804940030348224201c402c24030407030700042e680b400440d609041604c20744003036400d0043c03440e0522055003501418007040a0460010510001c8208001618000c0b501d291540c12005415401d14011000c0c0504c0841007841f401c0040c0c0e004040c41981c025841a079060305001c81c0d1044103074a00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 140991088 1250 140989838 140989847
    0xf05121003110a0f150c0c0f03021504060903030c050a0c030309060f052a100c0518030f0604080d1e0c0905120c0105091315150e09010e0702070b0703 66
    0x5001c256503001c40d08a080d03005050400165003281c50a0090318915860b01a560b18a031481c0f9114404002c042c844030340110340f0444291001d440b00c07145240c1080d245104119400e20340d4030000700b080360140020401d41380c0010029081301d030181404400005146052402c0011610000300b40e071024007404030038540d00a01d0281030350020781381e990782440c1c205400d440601500440320604200c10403000440010280802140c05100c0115010740103807035494802e80300842d400d0400507002080b403142280e40300740030000299080d8040c1c0b40a00d410a40240c440c0c00050014164000004039040305080d00da004156600030283c402804924911481010b420305820740c5002541c240c4001c90755147c001070780d07446d80641e64010100c1010140041d203a0f07801582c042075104081e103200100e00c0006018451001000407484182103003000f0308454001440ba00140801c4400310400c030f820303151294218150b4103549184890303607494050072403802101b60000030114802090500030550070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 140992338 1250 140991088 140991121
    0xf03070305091009020a03020d0807080f07060f060305062e030510050618040b0a1104080c031216020405060301090501320c430c0b0c0d0f0512 63
    0x2054183c4040d0440c0c080d03030506403250064003070351180c0244004c000607d00601c2c0344613280d114010f103030704122198035100d078039411840890390080070002e0031900f0021107104da40300c2c0c00d450f802c081100e1819610f0741d540e141402003072812000b80d03140c0a800c5642c104103010390012200c0e070041843c140c4031301e0017907101d5031200d42e80c210590408011545500d003008960300c40410503010b0024035901e546a41d842401d014082140c210340d680760b9241c444411000500c0544040c1004200b4810100c060501d401020006182004400e1101500b0950300620000c03209804950109030754540200281c0101500c1000038059868017291189500358604424842298075500b46140c030705815104608050868543c123881504120f1002c0d810300c110b00100d5a00da13911440645804220048280c1c8503400d82d24241020002500500308884510918050030000d0031f0503040242c6007807026500c0d54881048018407001e070b1550071413107214405841481d40f02442d003940e10b040650001d01005c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 140993588 1250 140992338 140992351
    0x30c0f05090f040314070f020a03032105070207050f030106080102071b14030a0807110a0e0a0e010605060d1808040f03020108013201050705011b0305070f0c03050a03020f03070305 79
    0xd038000000c403544141d602e00c0e84a29015141c42e807040d092110410705a5018076400c480e05008107042c01c0140e1290f0003004040d61098940c510001c440e40c0ea61807245c801d0180c5114403038107220400c103006074041112800c850b41035031210450921280040c1c050406508002210b40c40450420103015030547c0040c0207680b4840b01d400001d484175404107000000317086040c1c1544c44504840000760441c4001c3c881076001d00102c000e080c0c00c110001d03181381c449901100d030702070076202844904203043c030582101107145402048414a400c1c085440390040000301080f81d50f8455a07a0136004040c0203100ca0ba41e840300559503126117918000034844198003041e40000c000c8800402c840e406040650406001ea4a50b04000403406c2000c08104660f102d5890400406010210020390240a4aa40f88010890411480000000041c01ca0714010594030401c940c68119110311508440d40e0a105ca070185846c56442d20912416070182c81150030f1154660400010011f1980d0300d80e1140c0c0c0500c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 140994838 1250 140993588 140993599
    0x601020d140d1401060e060406020c010806040b030604060903020705180a0207110d060c030605090f04020f1c06060509060603010b0d020903010914210c280c060906020d0305010e010b030a06030c0f05 87
    0x2400d5109102c688c1c05103004000243e4068010706680798003030347c40f03160701407001040840c142c5080f0f0003003418048e0a60301111680e444800349410160144884009441c0503590300385d18035444400d800103510040d21000c0403990000303402c4144000342e501c02e00141009041e07524801903501d030001c002c0038801c9140b0000380c54508081002d00d031030300031617005148a011185468580d5020090305844910040364041075103500b81d022000510b52252043e40540400600a8030b05000d00c0650540205076501c6440d00304014481741d0405801c1d40c1080940031401a1070701400c8011a0041240f420f02810140450301c000851110000e126141a801c180340800b142d080540942080e000b002001034158008070400c007a207100c215031056044044903401460030402d0b44662505200c00e4000c2c00c00540a04c409106407601049400800140c0740707070801a643c03400c0404000c0ca80c2c1801803141d100303400004200301c50388540041c0042c41e0010407643c4120399480e035695005c03c0740c0c827034075001e0f2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 140996088 1250 140994838 140994857
    0x4020a0e13031115010314010e060a090c0b0301050d0f0c03020607080304060f060f060318020909010204080d210903051201060306060e0102011109060a0c0f0c140301050601020d140d140106 83
    0x44008139040c04c0b80440f06240008070303425543c2d81d55281190300c030b0890301b80d941c0b2004000002001c200603400743c0b0f0f007034500041d1030300181004c4650b055a03801c007118548007040100000c5e1502103401d0400354110008a803c00714502c0d01403614800741d440650f024102141080074800528004d40c040c42c4074030010401e2414520f10102503511900c41c90f00c1c49210010104540c40c026081400000028944c800c400241940000c2801c20305403240c1e030b0a41c2d40031400784120302041282141c003100606110428044038403803100120240080f49607415110490901010f024a0550704068641140d00b0010344c0c6907140140142450b11603080020211012143e0650040c07150150040710354507006d107400e4850301031100561085a03458204001e00f4042e001150a01613004102d51040107900300311484c0803400c030400d10b07102c3c4070300c2d1007031f40750105002a80c1c1c0c0028000f007c1b0300003410800300805a005030320019000c0c2a800010755424024074502ca0210f01c14401d040c0c80c090789408542 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 140997338 1250 140996088 140996117
    0x120509010e040c0c0201030c02010209090103080d18080d090204090206030a150b0c0319210b010806180609070e040c0e030f01021213060216050c090108061302010804020a0e1303 78
    0x43c0d51411000c54040b40c4100d60103005035110790403802c0030364410b000143c6081d1014001c030710301c2c42d0240d105449201c004108d2518480060088111108401c07150407240c01c081e4984d42001c4c4035214415455544e01c2e0030030000c5440342d4124210881c0c004000e03075128503002c0d166001031300d181301501001c100030160200320104c0c0340b000d88602d03070b4084000310708114040014421140144850409200c0c010100c80c424250700788500c501920a080c0100d10f4200c62400903065180c00741200e4410141c80e000344281b0002c1c80b0485a0181d400c0711440100c1c1c840b103c0503602c1900240f50250410b041c05103840800b03030042c505140703e44c415800c850712031040b10710740da00b02d01440c100c0510101100000c40c2c4031020212201a030707503000f6580107140c401401900c280c881201181102c1ca0b400140301d8003410300d0802001801041c0d0b80c4054800d0b0301c0c0800520f03114186e0f280c1c0082c14400c1807000b02e019900da00e45003401511001217241e1490130710140300f1080b0603200e03030220001004092280171 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 140998588 1250 140997338 140997341
    0xb07050408030d0209032803030b01020c100e012003180402030c0901081009090b0f0907060203220314071a0723160603020a020f070e0403050306030a120509010e04 72
    0x32140d000c80950f0030a0044035102000e0b500400c00c05d03915120700b45980e4901c0c15440d03504000d03881400203280e5080305034a805815943c1c40d100c1103040d0340110209070f04980b54062040c90001032484c000300310b0306010006948004452607403610140e4801146424120000300800000404c2e031038040490350004100810303031004550310a0300c01003d200c500e903a5401b401d41140c0020241a0303000c40361391a1000441184c50002081d2459245001030000702803440594580001c9940042d20380241401c0e0007a59912466000304078500c0aa140c58210204d91440b41d0b02543e0b00c44c0381c0250805103440f407103175181c0544c001d01c4824220009580445401542203414199104800550400c03c00011202d52507042050808038003a018254000d0904281e83d03101801440c5c40058407040380c00002031901280d07000315002d0760320220342880807100c284440c0354407940c180390103076a95440c0c501082c01d14140c82c50003032403200240368500d106034009004d00501d400a81e104071101e03504100300070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 140999838 1250 140998588 140998597
    0x3090d05100e030a0e030316080c1e0a0c0605030f070509150c030d06051f12020906030405011508030708090d0206190507021503010b0706050a020c0a0c0314121602030a020a09090b0705 81
    0x1c116602c0c44641c040003a06070b0001d022010781075003c1d6180c0bc104444c0d26a5080d98011301101d05c1d402c070800940c00c100f01182d2142c00361440380317041e0b411413030a1200520154000f0b01610144600030902c6c15142c0d07a85109d81d5151070725419415280d52142c600d480d981c0c1c0003179081d41c213040d007448004a0942442c42d0410324528480303030301c3e90041240c640284c0382c02c8100080d143c20181c0800168195480320002140120700c00c100004030500c11014000c0020500e0b0811072883d00204641408100f043c0156040403100321078600d2407040c40d10014034144151405420702903071168007910141d8101c4054400280217455100f4000420844405030b44024000c1092000301031050300086041039220907400301d02e4000c01498070030700c410040d03d0910749802c02c40d28030005a20600400c0100c0080000b60660240100241440b06c4820809801241c4e84400c071318840c0d01240c825540d04115918003180c000c2c092440755901c807039040c40641107170303e070958811864030003040c000c0b481002208d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 141001088 1250 140999838 140999857
    0x70507060e01141e0f0c1b060a0315080109080408011b050307260a0f18023102040b0702030f0c0102070b0906040305010606020307051e03090d05100e030a0e0303 71
    0x1c03c4054141242c4103541d400030015254800c80c41e0514040703a0013414000c1035210a400c84680d12050540b140c00d1615580612040d000808082c03584080c2d00c2d01003e0754011041401c020503628110010314003000703201c0d40002070035802c00e1400020b22070010300400a82d220034000380041082c0740b40700080300200d10400380000e00100300282204d07201d035003c078254058282c905c510700345052a5090190005a80c42c41c9603546d0f42000d0840040d0a10514031401540e145070303400f144903a00000e41402000c0d104503418003140e4034007d5a1203441081c5601348180c40421901c864841800301459044000201d000f0b00c524501c0c08483c00000503080503c001c164001c2840a0030400c52080b0740d0080000d183d00300c0c03014000407000030000c0c090503010705426802035417156041e0400c3c43c50100703d000b6200d00d188401200c0e81c1213030004802c40e461b0039000d54a00b50410007610b0001d1a155000b50305d49015854200144500d8002100810403102640da808035102c19040802d512441800100c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 141002338 1250 141001088 141001097
    0x911190903210903030f0e1810060e0a2606130c0b0319020903010207060e100605100c02041107061401050102070b0a05071103031e0301031505070206060f04180602070507060e01 78
    0x10130001344641d0500c0300180280c0b44c041c1d50f101445012824030008041354000004205040080c0c0c13124005010b00100924a000b1030040c03948000700314032805074002d115403040300542c20459428040c4200220342d14210440b81c4601c0e00a4405450003070040089902d022150300000d0002d880d1402c0e2800340b00d26004000131420461106002940a001100c4d0155024001d41012607224132035048407003420009448003a140b00fa00d0340c11101d050f00301c0b5200300424031701405032540c0702c40c1041c2156415500000c4101070903e020903a4000d203c402085181420481a2140b1070110864102c40c0282c088403a1030b40c07074500ca050240240e001240000ea01400610701050319101e0350050208040c00362854450001002941c1c103120380a52503241000100410030899840000c09049e900341c00e0422144c00c14507402910307001c0190455102d004100380d00c2c5000d070786a41c00302145591800080540400074500100607400809054605016803d00024000d00a4070100c140c428140d54 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 141003588 1250 141002338 141002357
    0xf050c0a0c140706050d0b010c05030f0919090c0f050c190c09050f1503010204030f0308090705120c090609040b04030f0504090c121a0604091119090321 67
    0x44900007901d21040d40c04107008008854210010b03c8110b018144a59a042e5a449110280015241092000d90410003d020441c5c0410f07400300564072001442e8044a50b549144800a590f07502c1c807050344004000840000198168160300c0f8035408016900c4114078065116405c7d0348a000e0701c84040704c650003100d03041c882030141c00366509100788144a602e41c00381d00c814800007100e4040b1000c0200820b02e0382408044190340061000401c4110001d514081c25541c4241041900040003030500a0b600c010a030140d40a0000d1400740801500135120010115540c541e2900c4408055009400400224005003000c2c04001d20507608900c4000c455242c50b07804481900900b8841402c100041c44045800c026601400e02d8014869a410032400180d441b5901158044001d0800005103c00003500c16214001924103c0345e0318035000404445000a040762841030704c3c01e410742c00000410158000b90040e03010400c0da80a000e03240032440071811040807281107000c0940101c2c61051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 141004838 1250 141003588 141003607
    0x10503101b0e060f070506010e090703050309010f02030c0d020607091d07200106030c03300e120601090204080607050301270e0303070c06050903041a13030b01090e010f050c 76
    0x1030340c03102c5040d405030542d4070340b00c209401c591181d0041801101c1c1a0080001000741c40c14046041d41c0007034803600942400c0d0301c0c40d505d003540e80c803442ea000e86c14400a003080e181060700074800d80d6443d208202c29100c000341d054100075103401007222820081080200f0116040309922005036816a501c0c030001c4998480e0841a602110807050041208040d003001c040c00003001c1c01802c000354070070f6034207040c22402e600d020078801d54014401410403802c0400c043c41c0c07030f04004111314040c2c0542404e0b1004551540820100a108140b05800b031194100000d000c01e41030303000340b04a510100a683c641d845800c01200d081c8005c0c4600c0e03041c0582c1c1c040cbd0038905c0c0d004210400c1010100a000261129068016800c41e0001c44061001c15909a100400e00510b4040c01e0b80c000301c2d44001c0c2d331415081560300180d4811109940100701e40215403580300d50b0401d00708101440e04424500001e6a58a0b10200a0810500b05808035420100035100c0c425560044600461111114900f8a440c0e00f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 141006088 1250 141004838 141004847
    0x1806081312110607110a0602070206070507080f06061c0b0603010204081509070501080603120c2b0806011806110c09090d030e012703020c060c0102090f090f1b0c01060e010503101b 79
    0x2024103a03802f0908000090001788100040705c02800307031034042d0a001c4200b040c1d003420030790002c140c2030140c901ca6076007001d0050601d0910054a07804001c135151900d9020220303009000f1138005840034401d007200c2e01ca8500000c52458440e80a000807205d031107446200441d54410203441c0190158819503010382e00740460005422588142c0e4111007031030220707980e01000c009480e684822580300080c0c440701c019900c40005a8401c4080c205051703041a01a041c8041100611990741040a500c1948646000074860382800c150000e000c03c0300c0c0d003022912903032100340b09250540480d01c1c1009075181c00c1e00601600c4015a4071440019618800d440404940c0c10a070b101101107010b031003420400d41d41c3c0d0801501203041c19400050b124400d080900001200c80003102c0d226601040402c00401d245083d465402150a9240d000303882d9130140081a074000c004c00c4903069401c1c0000410720508010f505030407104101c084482c5a00c150300850102d40840402c0590449450541c2c0305144c000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 141007194 1106 141006088 141006097
    0x1e051503070807180f0606020705030d031107020f0103022b0b010908033703090606060e0117060607021507121806081312110607110a0602 61
    0x4000b440e5541d18100e00c50500303504103102e1983d030070180300e40204520701c4401074140030341d0307465460181d203070800e0b405118001d2040c400d034001050302c24020011101c2e030700c80d10580340480903000d001e00c03408000070181c1419000c1060484c0d1105a1460700c01a010015984100c0203210301c11800381c58100b0203083c100500c010041c4180079001c401c44403484001080070003078070801640c0c056004001c0c03010010030856482e4042c0026056084a6040ea104210800c4515214481a01c40a420f001c6c3e190010700301420907000d2942000b4810f420840003070000782406501e9000840d0301c05d40e8800c2a02d2150040b451008000340c038012809001540c1c20030440c0b0110020401070855886d125400130002c800c00400c04002601c00c62103281500610185103025501c0000340c11030410024405081c4190000164090700c01e500c1c403501ca05142c00a014001c2c40d913100c220180d0403 = true := by decide +kernel

theorem cover : BRFrame.Cov 140827338 141007194 := by
  have h0 := BRFrame.cov_init 140827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 140827338 ≤ n) (h2 : n < 141007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
