-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5106
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:46:05.887632+00:00
-- url     : https://prove2.me/submissions/59d312e8-9d83-47a3-ab96-b42dccf063dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 918165467 ≤ n < 918345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 918166717 1250 918165467 918165487
    0x1311060c0a1e2a050a06050a081003240c0c0302070e04021c030810141e0a1715090a021509031c080a0e0102090114130f03050625090b 59
    0x1038401942580b00c03600c21121610200380b040d80d201c00b0603610f1800d0b500c41c0c202050030b26120300168100c070001c1e554103103000c590850440350319101034103680d085100913038084001400341e402d4150800942001c0c00454101600410030703103c00308908014000c6092a240110741c2c0414000300340d5a0141042059446a101140c4490044140c1c0c1c445a51000c100d201010b5000c00b090b40994840020b4000c410f403190040e024000e010000e00360700809030b0040324592660800c840e8101c078002456003540d0b50303071280d40074041d4112003d1000550031840f1540500340240d00d405811465080044c04414100d43c08155040c1010a640c100c41001140c050000e550401c103882c02c003030841075a10561118480003400c3c40805035145582c503400c142c1100e80e68001442501c2642205a407410316000e0014003189560380a01300001d5403070b2000c8400b00d000f90300303110b400d00190b20070303002450107190550189414060250b4507401d0000102540340040d580324a203241501e040da449540d84001c405 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 918167967 1250 918166717 918166763
    0x5040506131706040b07090e151912030201150302090708092404021c050d0c030c0203030c0601030b010e0c0d020a0c1b0914010f12020d05061311060c0a 67
    0x5806002c0140004030110325038000403a115024900c2901a0f1602c2d840e11141500c40c0c40c03060241d402c03aa074000d8000742802e28005912449003a001e089886100400058510b00c031519800c5000840908802c260405509100d030688640c1d0b81e404400c00c49085500194030310070054a140b040210031804210700280520110b52502c7c10000c6a481d00c060707107200004440c00886060380710300e00c1124160b240d046510300744d0803103c0d40000545440c03241c650302501c0b9107508280c1a8104040c4030040c40040e2401c10041801254501c0141260362640c0703082005290140c00810900151409000903540440c06607601000c810b18013584801103034400302c0348040c2520014003c1c804040300300d0700ea42003424081058401452080c8042d1241c01003000380c4460078400c17048884841e200400016002941c0b03140c00901c014945031b010106900d500b49001030603100011007983c0715046a0410940e06801101014143c0342c9508101c03114000f1a1107404010340030f401541039050b030b01d02e140908 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 918169217 1250 918167967 918167969
    0x30509060f07060b27040b07050403050f07091107080a030908090409060e0c03010623010201020f0c060619080c0d0203030d0908121509180102280815010504050613 72
    0xc0001c1501c0d00c1d41c508205002d020380e50340003405003000542c6808101c25007040c40001c02c9a020b082e813010b44030341c0e858011a00d00203100701e08201c418007012000480602040c5c10034034000c401810080d00f48607604007250540145a080360500304070100c00a81c2c1281074841c00c00d5181000a016001c608142002c0e10807071a0440e449490282000100a96641f01c2c142c0c40c0d440008858030500840c06150807603078a402900746400d11000380320f401500d8612003000b96031041c4005402c1a120b01450303000703504000751080054020303c0800030716003030901408041a54100800f842e80e840e100c14a40c442510300302a9008000b840114010340d00c081044440322034800c00100030140c443d040013004c0d0b410107181c1c2d4441e20740b500041108480d14028020600000404104542d240c0d0302c0f5408001842414100c619502804090a40e41d007141d0140105006402003145c5020030420007030000d00b004091503685044401d0f0a82681d078848140c40030307120143d402503030b20071090182c1c13080d410711 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 918170467 1250 918169217 918169237
    0x3120c06020a11060c03270a0602070c1409011a0d1e060f1e060c0609050601030b27030a0c0c0510050c06010e0603120d1b08070e0607020a0303050906 66
    0x75440540543c422403c81c1c0c3e14225009581d000d480c0c0309400a0940700079100500700016800070000c1644000d41134003885030600c812262a03111a0740c0703405c240d800c41081510000740f00d000c01c000101d002d581440ca2408211403480c0740d0342c1841a120040d03410101c0141c1034080104100c4808815640f004a9034550144035a20140d84c903510305028040b40d00648241050080002440303041185148040c51051402440e040381041001c80f00a00c400350195000b54803040302202060040c801103010f140100ca003003001d8038181440d0914101014042e02805102d001030300005040071081c0d03038104902d4900011220034505080014030025000143d008401015000810b03401000400c0401c0c451000d6030a10381c0c2e5040740d490000c40c2101c9940c1c054000303a10310707203100300154010101c02d041c1d40800680e440e5404080d07013040000340640400714507070303c00b40038681c0d8000c4556401e030001115811b2824515501065100e00580300040c280500451090341c1681c07848207582012103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 918171717 1250 918170467 918170471
    0xa0b0303090405100f090b100c02011202040620030c0a1203021c0603050705030616181706071e05120c091f0305060f0f0d080c150109230103120c06 65
    0x40c03a10783c10160582d01d2144400941d2004000200c808187c0a51412003070018000c4400d200c1240c4c0c1070780d1800d48500124100846902c03410619922032025001900b480e030384a200e441c0408203c2e024011585000c1c0c1a1a031040c48041000100029180740203035014240c0008c480980e00150041c1c0141600c0e810264049030705a40820384541c45401185d0194003150501d07596034003807607100c420541b055182d21401e8200b44900794020304440c1c0305480724040324041c143d500c07120100b880030170840981450708050140060302d0b6008000038a880303000084032202ca0304080d0f01500506c5200c0c04888500300f50b40000e4020145c05040e20218500070f4000c0c80f410074403280c04040500b00000c0b4038046450310022884e1400c15840007d20460701618000101004604000312031000c0386040300d0340c070010809200c6401c401d00140740c1042130760602c01215414508004140c0f100c441002e10200313240191504000318240c071440c112500294109600155060101d40c0a15000c0020344614 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 918172967 1250 918171717 918171721
    0x103020c0f0109051204061b0503160809040605061c05040809040501030b0117010b0603010b0706270c1208030f0a1401060504150f0e012a0f02130209090a0b0303090405 74
    0x201041d0010850f15110b60306441d028540080310301440e019500034840003660306e07950491403846242910080da40208110703800c041c46804101140d9406100482c2c00100c085009010ba0510f40501e4026040c11911181083d8801501485203c8198204003807e07403601c02140512070000d04443c50b48101400a025647e1a400c141403440e0080c8624280c4194100400d03403001d20610526215000007042d1034956445e0074050005034000e944103135a0070341e036a0303c000350040c00360011031217a060381c11038000c820803682020f01c11610664051050103e0380b4210f440000c46030800c4a0b44010070011541d1aa00d840c4118002040090a0340207181c0c408000403440c690400e0103002141c1600c100e60305541840001101c207030420850b05c2c0c0100d450211a046990302800412800c0300e00c2103400d007000c81c910800800401e0301d0040c10303a0181c00401c000300543c24042c400764407403500400300b50314101940020509103600109a105015074070281016141d80a104640b1500b00c0200280024 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 918174217 1250 918172967 918172993
    0xf0902093c010608070e0a14130f0e0f0106080c060715050a091202150a020a021f0c09080a0f020609010e19060906020a0c0312181403070e0906070309020103020c 71
    0x30340420300035403001c01c1040340002d2503248a0f0824170244c01000e049003606d58902029102e2032100250300b560700009414424000300707418031070700706e0b20ad03202c48000c00c0c0d000d102800700c0e041400c90400c01401f44d040640c1482891000144800ca402e010360380256114124203068408620307040c11111900e003810b05105c012904c2e5081344805a0051078201d10400404030305a81c0c82c0380c0d815440e14450121000144240142c2d0701500303c0b040303540161000d01c62400e0050103900d20000184076100e6071400b604030003a9202d41c0300009003584c5001400001019100c03607d1000200381c00910826002510b80341c9079100300c140040e00a009410315180b1400c1d4240c0c05c5120310036008030000134000c0d000006400d840003595000564004040e80c580ba401c1d80c41d4002c861072814410414400440c1484000c1200c00c1001c03002065406440c21400e0141c6d0101b41c00c0070001c0e0b01c000304941808007880101403010446c143c001001d801d0006c0d00ca402c80c401600a40940784a200407030080e41100300d02 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 918175467 1250 918174217 918174331
    0x122a0203011b1812030206040213020d0903020f010c020106060c1401090c03030c12080717042603090d020a0804091e02030108030a030e010c0203090108130807060209040f090209 78
    0x1221056601c0d036034100b601c44c0380e0300489240c0824080d005a102d0000f081c05410080100040e004c41e00e20301502d40402c145031401070343c0c2041401c03030059000710400014200d0070b00c9a0a220b100510081c03254030315000b03004201c802c0183c070282603004a40100408180c09501c0400e0440c2c1c0115009440c550380d00b409003c2d0122504243c074042c618601310480c4030703c01e21016100e04d403079448083d564407148030311009c15880100121919400e000c8400000b0b44111104910709600d40c141075941c3c078095100504206481200c02c1c195800b0f12040000540c2540a44082d07035600f810000f404e030655404124021081c0002c0d1001c0d5100200109401102000a10040501c3e8800340800b001048040e401c8601c41503444006030001e0104c0b500d150300c2103403150340112a0380100b104040d15526440c0b0709902141e002c40b0002d0740003030b0352209402c0c14020301700f0040c0c2d0070000f001408019008244104130042102401d8070703015044058154243c80782c0c0103000c0c81d00087c40c440c0c6000010500d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 918176717 1250 918175467 918175487
    0x3f120708160801050112020f0c0a06020c1006050603010e041b030818190312050d2a18090513080f0304061d070302060f0f03090a122a0203011b 63
    0x60280c40c51401d841c460103640014100d80040c0c1d600c2451100d03880494000f500091914032070100100802c1500c002d040249040d514010700740103950361164510b080c6401c44481c1c100b00e4050805804009695503442a030341126409443c004003070b520751800b904622601d8021690461501d580801030052f200050502080d041040c0a01c110500040190842c04161503040320108540c060002800070209070308072200e1401d181d8103003002400c030001902c49200400320302821a1400010f16280409201c0811525041c0b0105001c601d004140c401d003003d00900d0412501c80300031660311b25440a0384404207802c80e8410740c80307240c110000e580591007600d00b500e0007801c1081c440c01002d05d50099042c14284507000b08440d503d180c1c00d01c027407070b0000780404c00d280000740410075416000d10020361060300301d1030151081e00e42503c0c01c4030301a80c40300e0742001040a91154080c07405400c40c95111103010b503211503a000044c0d44006409010101c0b02c0000c5000001c40504219802901d00f00c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 918177967 1250 918176717 918176731
    0x8090a1d062706040207060e03030a0e190b1f1e1815090e100e0114160f080c04051012050c16080703030902213f120708 53
    0xc90504440c0c0b4503800010000762501080254040f40039407820b54002d01b4054420b10000c50a001058405ca086d03070005c0350610b03d80c940300c1508004402050142c00550409140100700d0540c83d5112400c0c080c0c07004082098482516480707803070800308000c814000707008015816001404001c080e4403544520704c600244a242108844681c0c11540280c1504030003224524008600c0d0131241d10103461a070038001c032903010301005030155030b03003034060b5130303c0c840c100d90004c81d0f20f05104111001c490002030280341100388094964003d680e0041c0c50500d91031162411803c15190b00c5010b01d0705100d650301c03945e480f0311190300c038100c001e401c0b07141c0060032403040308100304507610000043e6040c840e01d13109d6030f190030855a0100006540b50068070440740a80341c0000c0709441540812041c1d00c2041110081a00d502d003565102c9404014183d0100c03075410744460207024802c4806000325804a1900030350840070300700b144c19400101035412188508011065030301b07000c0c2d0040c201c0380b0252005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 918179217 1250 918177967 918177979
    0x30b0a09200909010c0f1404150c120309150e19032d050304030f02010b040e0303060a050f031903260415091a0c04170c01080f010e0408090a1d06 64
    0x3d18401c0061081d219207510720b86410005a026030b1040300d000d1820346035a412803405100204100d0010b00402c100c04c4015250900d403070701750b4207081004904a0508504241c1402d260000007000c48804074840300c0f240c0004202540315480050404000c40d2003020492000e0401d4014103a10010302e050b0384003a1a09004609980e000603450307810441000c0c2c01250041000c64002131094196414500a610000920609050005003a6a05419940200d40c40401031101600c0c020350300a00500044424601c1d0f0b1500d2000702ea00e82c1582c140c3d41e0300c04803114802400b8580104d8100a14010456480e503480c000c0c00c03000701c0c8404081d1029114120b13640000c11071480c491050b9100d0350b0b0403651004105a410070b112034a0500102a07503c0300384c0a110000700480c0035680c4c000c0209107030029020b5000040001081200010003c01c14486002c0040100c0d1001306001a000f9422000094ad20000100800c00c0c140003540113228542c2c555a0740e00d80001d1006c203241c0610011544 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 918180467 1250 918179217 918179221
    0x5010302090f07023a0207030339020d1502070c1401081f170f0f07030f11060403020a0605030f06010201050114010e03151008070519030b0a092009 65
    0x100c0c82c1e1008440c458056400110558034103450024003010480508422021564440740f407440011641c905150250348015004d100b0180c1041e65020540c8400031802d030050900e581182034000f6003000510003030060080d00f015034880602400ea007540116803820200b16626071030000b580005810b543e80c00d0203080208102a58044442c815101651500b9040c0c80e0307040ca461101c40500314a042514031042d00160b90800d02c146151014603440c0a404004a0282c090b81881501200641e0f43d80000c001480090341d003a00440c0c04507002000b2038034400307000001c100d0301d1045400c0030394014860b800000740303681d1000085202e0b084a5035404c0c0707240c0303500005a003664800c0c0038145001c01c030551012a95403143c6094040080003c04943c4a0302c1001488541da07031054510300381c01455000e00f445803040c2082010010002580c41c9221444255543e00284c0f5042c00000c00c0060020081010300781c0c250044540281c015100d440c0c501692055400e031449603103800c030b0240000d000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 918181717 1250 918180467 918180481
    0xa0317060405040b0a05091e0c18091f0209040f2c070603090312090b010602060c120604090807150f0605040b03100203100e010608250e10090801050a0501030209 71
    0x81c80380550b6115003880301d5a00c400d40c49170702502000f04510342c203114031000418440602004914080021800750100d0019101030101543c041504c0840c410000d00510500f04400202c60b2030000040d001110840c00500c005000791242034001c0ea1b03c03a00300398452880342d00e01c1e4041d41801003401403110250190148014581d4107180c00c00070301d078002c4041080900e0003500070780c0e58036101c0e18102d0a180c0320750200030102c0d42c11040c182c0b8403880c07072030041c4159601003107800d401c506844280d82c14001d103040c5402c01c0140080ca4140102e0703c4920b0340742041412410b64481661020848980714450800c12000b4100f8001c800041030500000041301e040c603214000c06050054040d014800e128007041d000381d800900805121103142c2030015068002c1c02c030182c00f070401e07941c500c7c5440c1400000c0c00c1144ca010300905415600040d003c0500c01e42100780205110302c103440d81c00c0c10512040081e03801400d107a021181a5007000d08005044010303a0101d410703a0b1088802200c00e0316002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 918182967 1250 918181717 918181721
    0x17060409050d08060a0b070f0507120803130201051204030206090d0302040f05040216051c02010510080d0809010e010e0604020307140a030b060a031a06040c030c12110c0a03170604 79
    0x500c05007040d000002d450214030300c504051640000040c00c1e4503240c1d40d0b922001c00c042d0303000e83c0c030545413001c040c11603404015080c0300803c0204040c2a50b0300d0000c4080e20351b8141480058504101c3c0d001030814501164090015074401000c11031481e105450103090107900da22080303890401c5801910440d07134090380203100351030589103402c0900d6416070a202c00d110007503010003441c000c00440e5083c500d000401c200311034800030301510091120303c0f0300200040d094540103440d0030203112000710141310080c00002c43c184848690310b0b00c44800c0c0c940400c05070040c10303d40d00c4003620b5400d001c048201340350001640383c095171081d81151000c5640350503000006402214050b0302c908810010004640e00c0c911342600030724002e100d6854260360b6524202070384064542071040140003010050945007520a19581122500b01441040e1102000802c00a1411041c0028a42d1403050241382d0000400355040d000080e0b08070f0b01544468103000c1d14400d40b280300504008440700005000e0b0510b4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 918184217 1250 918182967 918182981
    0x703030c020d050f0a030e1018060606140708030a0b060c01200c120c0c0a0608010e090a020f01030905010b10020a0212120a050906120411040b06071a09070f06170604 73
    0x1c2202508145d40c84100701e028080a281c014150320075040c81610080c584c1c46600c0007003000c070488000005003440c100c070996003168014014044810700c50711101c1c1c0c1c402d0131611281d501200c982e940c0d076206140080103026080b286504600085511009010b05620a5071714000320030f1183c1c00b4007280c3d82c5819803031091000c006015042280e040348a038032484003416620b200c41041d45c81000801012928800c0315500480002c0c40001c01040304440c80d076030b415000200d0b400034040321400c81d004640c00042c0082e1183c109076969050501b4000290b102000e0a00000c001c078004002c4000001d645c0d03a4460b070300368442c0d18031041200c6c5015000408200c1f2802c184045030412408107415203076604440502e0303400040800c41418808003ca90f450302c0356100700f0f14031032a1344807101400100c809075a1414061042000301002150000094200d1511401c1e01704d01a07554103600c0c0c60800c5810b620000b00c1c034981e04404140e864102d054400031356455048070034941d58902c00c00c401e1301c4075 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 918185467 1250 918184217 918184237
    0xb07020705030a33240504090b061e04050f1605030108070501050d11161707050c0f031504050c0f040b131d070909050705030327030a080703030c020d05 67
    0x803041842d100c04c0340641c02d00040e0314401c0e200d180600c0859000d8291602c0200d503824171800702c4101d1100740d041030440c0b0003502c41520708000c41c015996a0740c2e0000030207042ca502c965651103400500c0350a00348010b03501103001c0c00510a6040520480048040548061440c202e41c10404884648031b00c080d00d040f41c001720020b080d000c2c82e2000540e0aa400030b40550b04160720b403451305044800050044c0710520002c1c644030704800141c1094000440d02e840041c00d4524200240008158006600510184200ca0103000e0144102c002481c00c070788004121165031100c4100010f0110108420640c517000342d942d059070f017141030200401c0b07070885a629540300984003401c0a09040540c03040e0504907601001d840c07003002241e00301d032800c2c074282c0c8908410381c0c5414400d401c0010030b0020b40d0040c401a0f0055040c0101011469003007800c2d4500d01b9800144424070302c032580d60400c0f21076495500441d00542d100c600741402000707070521003c0a4051f1041040d0b01c8581c034070420440c6d400b00700b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 918186717 1250 918185467 918185483
    0x30501050f130f060b09070c051e030d18050f0d080f01050d1112190213200d02040504021c050708060306070e0f060d05040c081f05061c0b07020705030a 67
    0x642e0799034481441100d0482942c542e60b50308000c6805844090311107018000c071342c450003a003205030324003680303007102800800703c00b882800700040752a1800429501c08000580b408515144007002d0100c00b414420780180c020711422000d40d801d0340001c11303915a01441079950221315510503001006246007845102d4018400d001c9610210f0a400c00003a000c103001408416600c41580c83e0030f03c0c08040841c01c24080d90301c11170850441c81c00300850150b054401e001031003012540d11912504a849005030030a005002a4585000103950b0444000d4140107004540310089071900e090455142c180801040e071800c404900c60328000c01e01c6501c1514001c0041002d6580d82008590405901c038070070b07030446441d1500c50225503460015140c240401c0340f00064503d410308000004c0d041c9607000156035044045140135410074047d054004507125140820151141000300300c040380d00704044081e112040d00c0c0e4000b040214080e41d8041c0703155070f003120341a5072035404040e160034859400030100d007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 918187967 1250 918186717 918186751
    0x190f0203040509040b270f1e060c07390501021911030115180b0a0e010b03071707020c0a09020f040306050703090503070507150c150e0f1204030501050f 67
    0x5c0c0480e005607a1203a00d2205034904880e1078564000000c0c0c2a81c000b980917002496030046d0701c00c3c104030507000d19800c14003102400c1038040d505903c51001400c2141c4800c0d0005180702441002e1004840d441c0380c9c6990348158000c3c0b410343c006820003442d80760300b11548011001034550700c0000c8080b000710310300c1400c000003032056440c0294902070682103a0503548900031200c10b2a107156510000b040c4140a4820046401c043e6504071022000f6051069220b400d007408088407104c1003a055030303090401c103513980e08c45200560303d1500c540f1444545242d58810011055030100310240c0e460015540140d4180e2224450b9050b8000d400d815402c00d00107100400200303a182d00026000000350400040e1b090781030701e4060540c0d03c000000c8d1005d03888084108070710381403803101e102841118034051050203015610b50003a42404500a88025207a801554101c034040c428007401080b10030480b0400c4071036100c180200c0e00544001e0325154038090000d1038101100503240d1003081c4050329407082c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 918189217 1250 918187967 918187973
    0x1406250f121716090801020d051b03070f050715060b1b07081b0a0806130c0b0a0c02040c0e0316060806090c270910090c1d040e030c03190f020304050904 67
    0x8000204502d90400c924402c4c0024030701d03030a2004000c45401184c011990346012101d02c0410003501d114a44030001c10410890f43e20742c0300300c4401c6900b080745400f594407661070a0000701c5845440d41040c540d881d290300003131007085440007451490054400398801c2d0003528003c5449821074130501541d0740142e14003003000d10220740070741c1d094580286524042038550a0031442e018040310360140c00d1081c1c280328424440449203c2d0700600940000d01e00d8895407200040070300800c000024011910784038240c510500071f0206c80b60101001d0110358444440510884154031030b4807800020448032004034202d81000442d1a1242200c014520b00c0e04199840215035082d5000000b03091740f1454100400c907030744818607503015149a620580e1076030705003101c040840d1504520b00d0140900d01000781d5400b00080d41523113015000711000244030105000050a5100d0310000c412903001c0000c410012020400003c00c04003071a658a103020214090141c0e9a4032a50088603884000f20b0006400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 918190467 1250 918189217 918189241
    0x3070e0103150606090b1c45020d020301020d090b06010908070503031e0c0d0f09060215060603100506070602210c030c0f04080d0305010e0a061406250f1217 69
    0x46551189102c687c00c210402244048803841c1c0c03008046c44044032102d10801500400e0401009072303800050784901c0100c82c10848102040070024020840f4180c00401e559082d810380b1020820308400b8844c2d84154138000702000310131500c030f0b4003050f501e00002c0303065400090340b00c080d1f0303801030011494201c03030000c00b5080c00404076110300341c03201c100558a00300d9401c0c4140c61042e13500f5110402142900a40501111865040001103502140700e071040c5000c541207031031b04188151803080c4d694442c84140d075084002c682106030008030004824081025613802402100003040320750280a0f80403207000c00034002591108103000342440454510310a507002031210100c00d1a1091500c5e0b070b034425080c00c00c520790f04c40c0004240d5036401040203056881040e60f003d0001241007000f14203040115416100070240365004590110b5001098221905800040c0810003000b07420200c20340f034800500143e00600700c68007803001079032114072800345008114a0141d4001007410f5600c00c220495 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 918191717 1250 918190467 918190477
    0x10209031506041b02030c0615030d0e0105041d041502070f1401140708090601050102010e0304061d0d0f060e0a030c0201030c02100519110702062703070e0103150606090b 75
    0x94020356840e2213904148040080e492505415009551141c0140640904000c4014000c0d41002c11000b03082003199004622040184101d0420580c00e20b00c5d000100c50728041c94101d484c01c41d000502049070344044200d011f1040c4d01c80c0e04196a020401103201040e401494001004030b10040090000034038241c6000348903030b5404000040c00e288003444921030080544074080401d95035010312240070010301c5001c1c0580020f000038000070009595443d501d02c1280705407010448450429002c105610103c0541510300400d10091b140d42030920076555501081d045809901e405c180012606020401c0e60a01da012703151160000700321f0300194040c04079200120114051003403aa1000502841802d0141c0010f41300c0b09101c10f1124005401c4402c070070f00c0004015800e001d41c000594401c0c0031510034010b03240f4640c1c50340c1d030003c8107500c544400b00300b0103074140110300022070005208144941201d010349a40c815603056a44028104c6019004920006100e10310900080d262003000300313 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 918192967 1250 918191717 918191719
    0x121505090117010906050c030a05090a080319020405030d1806031521050d1808030304020904110d060905010c03140f070e030c04020325020d05030609070302210106030608010209031506 81
    0x842c6180441c0c0e17998040316000c442013640050044288147d001c0f1038400c1d580c6c0807003980010841c0a4580c1c844c02030900000b00540120303040d9505c84400c41c3c0194040d980244406002c5507020301e405080902034914000b00d484403541e18500009000707119001d20255110a019400b00c05400c00358a04d851980a594a56250400d14200c41c0001d0080110000041e0301ea505d205064040039a41060030800383c0c003407400d40d0b0050060001503a10a010303140c0065009112900b0740110300d01041008111110281605182c07103550020b202064110040c062a607540c00c00107a0920001e03001c040304180c8045e80140d8030803000503082801220124008480201210707020b0025600003411b90b07200702ca619200d2480c1c040c801d0b07550540000c035068644a14006050002c00c6500002d0860000401e10351113800c0030130202d801540654101c1d10055000c1d14002800755501c00003200b80c80083c41943c0020b40340c05c0000601c040103101740c42c1080c0e0018050009512a60401180a400540b42c9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 918194217 1250 918192967 918192971
    0x705070f0303290f040608030f0306030c0307081b04020711090606090a0306020705010501090912031503140c281215050f040506151804030909050712150509011701 72
    0x2c8a0581c0c0d416000c071200340f481002d400c0c031101040a1041034098200748034055400e00710180020000882501d10415030001126180e0356050300103071030808070f031500343c0d0035015406001c2910700001c190086203640040c030a4a80c00b004409000492188400140c91859604121070113494074070500d43d00444003e000710300b441c1c4000c0006444080581c0201d80a6a002920108005c003e000341030041141c200104000c03011902c1e9101d814590038900410503588a1808001304041d040a00141d5000040c110340700f0044001c0d5540c4940010701c4610509040b0825059204028403c0d8109044001e494102d649000311645c451680d01004480300c0011400911113021148601e030312402601d10b802d0081c1c101414554103000000e042c10038000072005100405d6101c0300c501c201c0b0b00c0d51142070040b4907662400e017150b0401d007540081c4a014100400d2080c0c181e4803d8035040303e0498100300700f10198a00318203036200328440c4115a0080810401002901d098002d502c045140c8a400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 918195467 1250 918194217 918194231
    0x13030e040509010f1e0f15030b180d030f0e1227100e0108071d090604020d05010303090f050a0f05091803070602071103190b0703090f050606180705070f0303 69
    0x442050314804402c0392444040c0e114424917503600d034000c030701c004c1700e0030b2404005464507a42c01c00d080203c540000340a020b041804103121050604a00340803011441c140c03040c030002207200401525620542e51010b908003409580e08500100300300d8101088200070341e15250b08078440301203a43d12004091096012035145c171005456400c0f071301c10040d0a65940120b21480c540016107a59800381c059010090354003071070f50006005105d0104510411241c2540a0395040d000a000e0322800c40327100102410030000004058000d40110183c89c5405203240845864000344540c20009100d000110503030850100082d04090140c1e640007115144500ea0050781039001c01d00e141d006800841d03400723030300099810a1000309091400c0881d4101c015203507424038154110141c4000c288040c0c501c000500209401c140290301552503140d00c8051514a10b01d0703802d1072a1145801c88009000d9144108500050f8190290f84e900c40d0400d5264182841a15207407601d01c0300d101c0b18124181a03503161 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 918196717 1250 918195467 918195491
    0x40e060609181012080a0206090601060504061d040e010b0307051009030627050c010e0d0305030f0a0e010c0c060c021c08042607060e031812070e0f040b13030e04050901 74
    0x1104d608801d00030000159624103140d802403410200410741d010750703089a0b0040c030009501004a40403a051443d00901d1500140740301c8001e00c21000c5010391061030484091100081900070503401801242074804540d9900700340412542100a1903000030300b940030900000c1d62650001c044000180740c00f19a40085c80d000c120b466100d407209640680c401d0003034513915030b070114009013a502d0a0310004003c1c1d1071a0303400f6001e40006810000040800000218429542d038002d00101c2c00f81c100030300c048150000c014001d4900354400b07440e150308110405403d41e00018445c8803803000c40051161061114004960694003d04202c80c443c11211507480030005040319407a03c141c0104000740d4581c56071a161084039440051801990414801c1c42e18400c0403201c200100403050f1200c000501445641d24141013140e0070464183c0b000c9024040000380011105216520980c00400980c4600042e841d4004000b0002400508503000c408130380c2c2459040b03ea000340741c0c10000300d90611005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 918197967 1250 918196717 918196739
    0x30a090b0c1e03030a1803090303080703090c0b09150f0703050a1707030605030f0601030c090b040f11040302011202070c151206082413030509060717040e0606091810 73
    0xc1802c1d40756800481401444455441040c40c1035403d50505d81e000c042d07a58014105401c03520015080c00110000601c045001ea0884060954068882181542c81d018181d400f07800080010b0301400344800022081822001241c81c0d44941c0d028503814652079030780448907640401e4001d0204104ca10450311174014031340c141e0740104500c0d00c0202d040c50401c8141450614004014112a4441001000451909601c401c00d4941011700400d1901f41c2101180183c00c008200442c0da034600044003d200442c0406802903d100341d031081e02c4841504070200582c0294030000d4280c1707460f58410490a4004030005240300d10f241000d240100c1c40d481c0300c4c812034034194400002c5800120b9031000280403401d00342c054141042142c15103040c80c5001006410f00d030743d0000d040c0300300011082101c0c0d48034000d03a484d02d80d110320b40c1038501e990f15003400e08913001445501e00d0a542c039004150380303140c190166001c164018040341c01a8a00e900160303090300c0c1c040c1403c601488a50000700c0c40318146 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 918199217 1250 918197967 918198013
    0x40506090315090114060303070309030221150a050702070b0d0c0909020313050f0d0912032d0e10080402131e0207021801030320070b030405100b0102030a090b0c 71
    0x103200001003000303c041000008010046c04107209400801030500020741006030b640580341c041c2c40400000c0b840c21400a28110000c441c18800c1c820340b0351007030140034902c4219215110115081c06662184002665200001e0040d0407003504144009062038800d0392000042a0442c0392000341c013607a42d841d1004030380c0180c40050303907000d003996010b052120400507440c1c8180c42200a1016a01c1160010901e041c41e004403214443e440900e81c081c144990380c0f8605c2420854000f131040104940b425002c090141840c10104240303064403d118a4002020040385200e900da501160369640c0c04c01a060380100244106595105032082c041c540c42c0803c1800d03840c5442c00142c0c0c844060042061200ca043e0030940340300148001880000c0d0310000d0b58052001da0420512201d5a1502d01c5081090b190807440d032040000c42004140b00d00081c80b11a0b884401c034081000c06440801240c072403003844400e40106000c800100140d4000710003c00701ca40007401038605801c1c1c500030000c00003000d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 918200467 1250 918199217 918199231
    0x20307020c2806110c011101020c0f1608010204380c011d0c060f03070507050d0f031409030306060a05070b01140a0807050306130302010921030f05010b040506090315 73
    0x491200041d0254004604800f400e420b04001344007100c049a16561000100f0700d00e81044581d001000281c0e0b07094040d10b961803100400e4520b01030702d114005648600944003007040c0d03400c0c40c00016604006108a9060f81d0202550566840184450151126860a143c882c0d150044480801c88820f400030740300540322031001040110358062440c09802010003036130240d80080c42900d009a42e594211907549a070208090348940c1d50764010380b030501413924041d0440c043c406c0c48051031039000310b01c0c5002c03d0068404118444843d40380852554086031030041660042004c6945407a080c07001e018403141d5440c00f107207070100d182d4a00c03552032400e80c080c92403091190941c403024a01240d051380a01104030051030305903e050002661600d020300740c03110001c249071684060600c00c1d003203558600d03004a541d10f500b10503c04260544440800540700003403030103050002d04519405042c1c121900c20302182d05041c140020000654494541113900d4410040d481c070400205605091044907 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 918201717 1250 918200467 918200509
    0x60a05160f050d0504141b130c050706020f0901080a02130302011206080f0f010612050c01050f0d1a010206181e031201090b09060a05130f021605010933020307020c 72
    0xc2140100f5140c145101000e07004c034000c0c960142c426845030607034041781c41104003020070101c405180540c1c030350bc074a21028003500e000041404401a540c0010b2082e40c2c002e907124461540d550f03101804030b009070303103c03403d02950300301e002c0000d980700c0c6031a040307680b0002d0360018642e65112100c2d4542440740b07a0920840c0c00103800600503100a11410b0014041461964020f458035500d0a840d038030002205810b001d03012030009907400c03220054030000c03441d007031f0100503686140c481c0103200c146001c5098018810310b0005100c41d11005a6080d440449500408039160708820203040080d6110503614188002d01075400b04042044e02140240b0b081030002034003502e00410b00c80d43d8030000780280d0003039002500820003503c44140d914600700240f03200181d0944003a50000191240c90300481d100c080c2030031903a05000066114030041e5109800320421052040030681c8030400345a03003c22031410040c0b40b0410304400340c00469029519106440c4041107800019001a03160010513103408 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 918202967 1250 918201717 918201743
    0x3050705361207090903050906040605031f120b1e040309180506060a0e0d021011070f1520150103030201050f0c090d171b060a05160f050d0504 63
    0x200ca503a0700341d02042096400412107052000059901d01e2240300310030712203607111414014540302d0000d507040d5403070082445544a6907098000c0c4141c000f51003131403050045244c6061103130307600e500c044111100c01c0c03503032007203200503884031580072500500e002001c080780544041400c2102d039482e44540d1003500c5041c901c1e03040542021005144001a984061415051040c02d544020644040348541d1402180d0301c5e80c04004100c00f100070b900000e40040c0c54501404100c0d03080581100d0301d041581c1110680341e640e00382c007502c030316062041c8000d2203403040c2c00200e800c0c0f051a40780000c80300d054050040d404a8483e142c0342520541580540c5030502e00107108255080c096075810210b1303c3c0e0000f185081424025255118044034a840b40e00440101000c003d15141c3c00b12006407011907454807941c4040e410b40d0706c0101da0031031188500462001401040c40352090a0043e10340c45810441401082816038400d02101d04c0f010034400240007409500c02a4002c40c1d110700d00c1842100088 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 918204217 1250 918202967 918203047
    0x17010b0a0603151502010c02100b1f0c050f210711011b050312060a1d0601050d1d01021908010b07020415051c0201090b040b1905090d080c06070306140103050705 71
    0x881d00d09040718000900300300c0500b5a5580d0b18002f000040c0b520100c0d61101000b42505507103014409500600e41e0090b0034042c210000c002c6004007456000d00c22070044140c00683c8030800303203c2e842d030040141c040d20000c2d001e070754414131300300840d2400c41c50110031118203621980d00c0c54200318042d00010f1400720070080d8904118004000500454105203860b118030002001000002403603039040020200c0d00c43c6103e5a288c002c00741116070400c21101d42550012601d0103507200c50107144190460400340444c49100780b004604032070100741914103100075a400c21000c3c1030800d030078500f151a10720010a290b5600c142007000d2445c600b40300700741001c1c940b0005d009101c1c41d46c4018415a402d1000f00128142c0c00115000c0c030444400c3c840410b02d00c80c40650301405688000d40d04141030b035543c24200280a40100640c280c610102c4d055030f5107003402101690494020000079040c8071107010f14650003500460b40086540c104207007010380d200a601c81c1c581c19100c01c4114441808850094 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 918205467 1250 918204217 918204223
    0x905060f100305152202030d03270305040e2a1606050a0203040c0e150111011104080f010e0304031203050402030a1e03080a1503020d0f0b1017010b0a0603151502010c02 74
    0x22803a400c10780000a40d885400107038641c08d03803540031000e15450324200b9005420386071714403c10082c0400c02000920380d03030a009011b41c105024613030004d110b040104400201e005c0399201d45401c04248411241000c00501505410400c4034800300940b200403100050042c0c0100d602c5108480300c01622440e20781030800e0901d200d940001411110301050041010003024918820070082c2400c04200506400d01d40c01042c0344075000d41e60b032002040101d0240d001103102d1140003810300c000d0050f102100400c0b920382c0b240e44801001c1840780c01066218034081d820450380580010191400061291034851143c16564000d80360070349a141c2440815400c81721160b0046e4211798204026000d042540411107a54040a0300c01d644180721401045034641300c2000460340300032035094500b03010b0300c580300f1002180144958020040011034003c48148541045218010b11489816280c0b403400d500421905560126030340340000702182450482c11160410a01c603400058414115040281 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 918206717 1250 918205467 918205501
    0x13050d0503040f150f0f14220e1f0e060d0311061f0605130306110c15010515031e06060417030405010305011e18020721090602010905060f10030515 65
    0x40c028081c42c00904582e03c0300c0c0c680d0110005102c1103239500c408810a5640c0661514030046900e51103178007190501c101011103000b403040511200e94480581012100b40c5040d00480080e94500400540310380f9054410300580f502904201080b007800c901002e0900d030040b594015080a04c1100b02c0200440f07516540c000d01c010b260036403e010060410000c5103445100190a85840318503800969580400b16900f01d10706502310f070480280c0001c040b4610303030240f16003171280c3d20150000e480c01d0030400440e8402d0058403010080c070222001940300c0c40202400581d0004020300c40412402d1440b16600780280c1d68000460329a482c00c000141542d60507007100c1100d06904c0411148482c0e070700407007403d032004041c07081400c040c440c4800c4000e010741c020103000000382c94038810640051900356802c5404995504111980340c2d5030990030307030b1040a0f0050695102c0400620720001c40c99015070400c0c8510031422210760b50b03403599440c0c002d8000c050070202d1548020310240c400384000c032403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 918207967 1250 918206717 918206747
    0xc0d022803020a061409040e03041503050405060105040b0303030612011b020604061d0d030203070c02130e1c02070e10030206071407090903091404090803090705040b0613050d0503040f15 82
    0x41c2a0b510f402c0117012060180842d014044c60703c900001c04400424400e0b60040c14506017000321a100102d0010301034503007543d003690540550000840c4d2401e00380562012510041c0c011469521260103018070003a4851300142c4c43d5607181c4890750340c802c0705072085803102225030003004141003034200041150441000000003000854200c003400b0000714051204d100d5034140181c40b55503445003074980760007000009500000c0224540d201d100b0729806403920721000012110203551182441ca110302ca41c040071b1000da0b01100f400c202604281845a9010000c880c66590340c07541d0380c0c00310307456401c40c40c021100703007494035060741f0f5445d01000004024400c1140611034400c003504d01904e14003150041014210f80900d204480341c44641001c1d80b0540d0126110ba036901d051011142c5812460040314401d0b410324a2130030072403a00b9010f4614000745220100d0606103007100700714400c140304c0011107450106000c0003450174582c0d01c003100101210602c01107041c003000300c01001102480121 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 918209217 1250 918207967 918207977
    0xf0c040504030c08030a020c0a0305041e0b0f0706020d050f01081c09060f1806050d0605040603080405060325020616110d030509070503100b010305090604050c0d022803020a06 77
    0x46076203c05403d4803541c1203e0340655075250011002d01070700c00d00c0a080254413501c02d1410801d54003400170021111003e020b8020350861400341000007240d4800e15920701c9040c042744006005010090031141c1c0f1440c00145440600d41d035010030754008a401e50001c4844400400591201340b0103809560000008091100d40c3c4000150503640f190140318100300d00a0300355584180246140e9038000589a20510090360f00d840040c000d074040c0c0300c0c1140d4141003800016031418903005403400e80380d000300054140360078041071114903000102110a500241c03030300c110069076a0300111600d08100c1c0d001c0c002d50f2034602c0c0091040c558130312101c03040003000c4094030b64481010070f07103840c80b00c0246008074680d281c1a80c0503161518580003517916001e0201d941c5c1004c08940c0c0000c0d0043c40a0300e05008694901c03c8580c1c684104235000b60017a0459081c0715807514159800000c803d100418141000c400112603554190341d8072400d89d008904d85605005514041c0319a0000b4500f80ca88 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 918210467 1250 918209217 918209221
    0x702040c09150c030e061c0606030c0e04020906040b0414090708240f041d010b180f070c0818150c07171509070f05030105162f0f0c0405 60
    0x501d0342d8a81503045040c04000b20078030003404051181c80c011103004001411103813205104813007070340342c4030124800051070343c60924000f854a000340540340c1104500e0711800750f10050a405d000280d070000c0101d580c000c80406c00410082c040c84090005003c015011040b00c00d440028880c803040080c0c540c000f481601010800c00d84664900310a1080701d2031954240c90422601003503005085900c1c10ba4000d0030407500f20340440080c0742c02038140d00154002e0203444042000d0081c610b4001c0b03014003c0541800000300400006160150060640e281007130041070b040e110000e240d009034584c000204c003400700b0641249030400c4041d030042c000c00c50461901c903118031071a0303450919105a805070500181410b503940410702c400203411741c1c005018110b0340f8003180803c0d218016405181d002c119240004200e80c281407041c103209589000c140709418103107031400d0f220b4900e11000200d11142c513640c3c2d508250111460b4504140d0320800400e443c0e00c3c108202410840d040d281507001c3c61038201 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 918211717 1250 918210467 918210479
    0xb070506070516062a05070204050147070803040302100e0303150103020d06030b04170a0f050306030316230f0606091306060312140a0c11010c170702040c09 69
    0x2440c410f8842e030281000507100200350700c0926502c0d810181e07003404407448681382c1120707402c80d0007884e00d50b200312400c100036a20f07604403040d0381c6490b0314002050020201c2058802d102099001c0f10030551402e881402ca0582c500c044e2140d01951044611050110500c020141c040050a03030f4070440d00001d1142003440341c2a56540e0000410400c118000004440c1699002e80d04031079071071041d5402031108039101d04148040403410754044a03e1206001244e00d4804440107940340070425648080340c4803200d107030458617078101500c1564140070811030342d410400c4039501c0408141c856a0040d0f451010002d0b0281e03c150f07d652001010303082613252180901002c121141c1c840422101b500301c54403203855000c40d4054051004080c1da02d821004004d01c41e10100d0110f03041c445a454401180310034100038034034011401d040e0045030300c010340c160010302d000c080c1da00c03842418900407a000ca81610361a0110b143c03000b103040e80800c00907145096050500034100d02c0031035810700900c200c1c5000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 918212967 1250 918211717 918211747
    0x504170c010f1b1220070b04120c0c050d020a0909120f09060504090510050d060203060f1e0d05011506030e100506100809010f0c08100515041205160b0705060705 71
    0x20307540d07061545e0307070441d01030b158802c070300d558020000588680d906c070000c5140c0560340c0070003134030180d4401e401c25407520f0741c403403103254020189540542c0364540c0c140b8201c180284038100c0b80e030417039002074801c40100c2d01903428442d00d0038081c0542d241c1c08240318070704005401ea40b2800107003010402c5d00c200500c4100d811400710b9040703c22900c400545036890350703134160f1600e5260300041e50010507884504180035403a000355015402c110ba007001681a1002005608a018541c01c04d00c12944121901e151600040c0c00100902480c0049242d22441c1288c4049000640003100483d03a1440c04800d0107070b0401c2002c41201c0310f00c004010710308004002810640a40030354034200203c030700025040000070f41045500d40075241e0288009100140c0180c040d2004a403003070f40c070700c034440000101e52030a0000240c0d088250b100744c600e42030810a02c901040c41d0a00280c0b0307107104040005070440c06891042004010422a064030780032680340403030600601038400020400e0034000012a80005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 918214217 1250 918212967 918212987
    0x1b0108010812090402041a0309010c03021206040f1d0d080105040603050c120708010908090f03070e070302070305040e010b0310080f0d030c02150a0204050a06030905030d0504170c010f1b 82
    0x204003403d8032002804000b0300a441660030111411103540c0403442c2c402c0c2c0300c1000e0740c0141c040300002c4c00560301e4160218102e0080c2c1074403508560041010481508080d4020a102030070404049150f040305144003000301d006c140c24410b0b650025030b90010f0075038003407455805050111810b000091070350300e0341a1b440031600d80c094407078501c610809046180c1003007a60b0003001d03104024000103c8a003070000d840e40003a158940613103003541020704245000f0a10105844c644c16240e401074807002400c6009410800c003c0f001d0110070400420000e00c1c0040e507500070508020020307030724035051074080000304a90b4000d0030a5030291a400c1003142e40070444803200c0c0b42034580042e25800350302080b407034000f05604401080b25084180607500b4095002041034440649031014156540c030002c800b15040e031074000d800c03500309100070000e8010a802541d005401521182c152800407110304425601807055246580e6540c1a04040d56040740200d0118841031510000500c104000240195441e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 918215467 1250 918214217 918214243
    0x10c03140721060620010e060f1509010b041703040305210f030a0603021e03070b030a11040801020c06130f060504140f030904061a070f0c05060307021b01080108 71
    0x680c104480b810000d40e20300040d901405a0b0070301900342d031004c024291480704400110090145c031108802a0300500030001e6a00f100e200800c030f10ba840c41d403400540013000c0c1c455107040724107000c0e045240d544c1886d940d000c0c0900b0070034035548a10301078015414150020707010002c4e81003444100003041e80860103184c0142c0c1c07440107065041c0c10030038510442c420103509140001010081c090005a80e50240c000d0341d2003992046090350031a140e4204070410301d0b0b0305c1076042c0e00041050201054901c0a5a0001050140807603800e2264043d02402c2c0c0041d04604034980d03020400c940704d24810000d4a40069000070440745819241d01c454103c205603601c06040aa20b80000c10100300745100f4500c1c801c032048050b507100e80003501249840781d00001c0c0491240e42480d2010480181e006104000c0601c1240350614010700c0c0c2d41caa1003a00d43d56201941c02101181c0000340907281c40c80154400e500321b501500e0300c40c2d80043c10882c0680c1005000d81084110001408802000102900c903102 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 918216717 1250 918215467 918215477
    0x5060d02130f0b04060f030f051503070e010b0d09050f070e0403080105150306012016030b0115050a21060b091008061005071103070906031a100302090606071b08010c031407 76
    0x20f802c19061f0302410750356003404115841c100411245014000f41482d03450381c100c05a8030925607403d0906002c203c00c1c050301810744400c01512401009991040802910440540c0c1c0c2002c0c01801c03150500480754030443d81504050100401c1560141840d0f015010441d01049045000d00a100090100414150501020f0700341d22240c1440880c105000640d0541180d50211130300001d4085c031a0144802c85911606500119082e10b102e103203856080703003a0b6103c0e8285500e400b400c0703030680055505800f1111082c56071840181703881c00303800081c02080a090b9030b42e0203c101400a0070038552211000c124090051050554900002002040c1d403403912a458003000e00789600d000b0700300e212040e031502c5100c80000701205c080d0003000031603014141001a0394021340c0c00c041c40c040301f1220341401340007032001440145003284c29180c00c40c3c0041c7c00d150622a0a0303a0b4510429000203d40000c000201e00030400071409018509604d10185010b01c414101044028900d00018081c4003e203d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 918217967 1250 918216717 918216737
    0x4141201091e0f021f020c010305040b1302120d08250906110309220612080703050a050405040513020f01020a021309031707030e01050106140315010905060d02130f0b0406 75
    0x109852030f0301c8090f15001052110150140c10003429552409a00c4c00090b001d40803080d6101d42c082d1040520554000c65140d50780c1da1080703140360761260100012688001c05107a082d4481d04200040b1210203010349400784a0b0520f08817038030290216a112880121041000000c01da6002d42210110307200c2c1e040a02101c030700c3c7da00090560150b0111140c01c900e21040e0040304a0550701c4541e04140e04c103404003c500d40b20b9064040c5040e10315800303004401c0c10000c3c0c9000900c214002c207041601481c11030304183c0c642d000501500c1c426183d194140340090180b1041d840e0001506c0d0803590240020000080b1a6020031082070034600c03c0d820040d52010020f05050086440c420b12002801880c041460301c2c21014008060120401e406503103400000703d40d0034007d10020b001b0710a00310f40d40b419542d84000c0c283e40244011407681c100b05c600240003a40791100000b910720050103000140c1c4400001c40480e06441c0f659005061104000900300070070440d10003164180c0c1c02d1881c25040003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 918219217 1250 918217967 918217973
    0x19061e060b2a151e010614090a050406120b070806030a0807080d020f1201122001030608123c130e0a090605070c03050a1b0804141201091e 61
    0x61240708030b03038124024241824410140b1001c11446514410380b000e004120b40200030100040034040c40021a1a0b000030403100b003003440140c681315000900c1244601c0d243c4020400740d90641c0d00029100560304082e8003084420401d0650000c26071600302d450b450f1010021f0390740c030454030000d4480c1000180f52418008036200700c40941c9200d903015035498242e42c00f8041168081e5140a2102b128070002088007045070081c40c0c08171f1b401c41c0c24540e54015070541c001140c0c0c0d6002d00e00e41415a51b100000381d50a09200501c000c1001e285000d03214400c50242a0030b000484028401c403c0310324685070003401da0002d02000c40748000c507801d034880d10388100080741c80d501f0781c1048040c0d848150411646030240d4010781c10882c8100c4080c450f64030b40c07007016140c0007030380c0c1c07801004944184050007100c0d104203240019400b89a130407a44c041c2d0140c60766040d9510680140c8d4050301540d56207615070414629078441e041c50403000f081041c9480d11003e0034600307002c80c0034042d030880c0c0120100b4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 918220467 1250 918219217 918219277
    0x305090d033e1216030902101b0f050f0c180403140f030a091205030601091503020909040b0a0e0304150513081608070f1d060319061e060b 61
    0x81040088841a0358050041800245075404c803510688100c1c44054210a24841d018580d0342c10350151a41c00b03100502c880942c2c000302034484941400080700042008200340c22001c58901d805100508030320800d4006175810300d0081c480082c0507030203401410103501c025001d450750160700b41c60540049525101c2824041c81000030340c00c2180390103c180148002654400c401c0c00303114070805078400404e841705885c2808100c502c1404150305140c00c000072198000c203c41c5002c11880c005141880b003500288182000707440030794560060604002200c60350f41308504015207a9802141080d1800980401c12003400764038004101c00442d00006040043c001503001d45184402d80b840c80a8032142c4040440f541d10070300000c4c2c0326044000031000380d42c007058400d030b594100d80c926280d0240050303ca904007010385801c0d0984191070562081c038100c0c8409803061881031801040310900110350200000c06000c0c1d14500707034a8a041000303080d0b0b01c0e40840f10382c21001b030000485610981801e200c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 918221717 1250 918220467 918220571
    0x10203040302030d11011b050a321c020c066001091a13080307030311030c190908100606081302062203060c0305090d03 53
    0x3405202d0143d64105042c5c1040c118045944604002c00600c6101c0b08104045003080302440080382c000c01c184481c0d588100d00c0e034503000740b1002007425444d85a0665859484070b0642081d0441d10109102250700900300c800066510420341c29803c0c0f2018100c01920b952000c1d101200c150010354440307036034044294070440114207845840341000748411845544040003041d0215449402c1103400c0d0504442070003140da0740c0180e5500580a090640341e580d00c040c144d410401111b0305101014088460342c42c5400581203c1e00030f59100c0100c0c6c1750150503580c05402440c0da20505000b0030036403010302d03015191006416440300c8600f004820064907055919005280c03d4095076050411013045504040c2c00c07512280d94802150356652903520101c401508020f510000420100c480e0f084080001c09030706d41200303100340c070403a0b9036aa10300480740c101034035034042a110001c0112a6505210242203064181402d111044904125840c0300c65000f04811805049215074909100c810503046 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 918222967 1250 918221717 918221719
    0x307050d122c060a050103110d06020c01151a1c020f0c1b0f0609090103060b030709091208060612060603091608070f050a0602060f1506070b190c1d010203040302 71
    0x300c248814622160542d500071405a2030764400c00380803803c00c0e00c0610499040744c0d04003804010047c6643d0402110703004402055440e55001e0252200d820801c5c4a01c4d4580c1c60000c40d00240300b490100c004c54010a03150070f466596500f400752800c1281c06110112040002c28001603444110326064072482c041c02c680301f6828898442613103c03044a04100075182507003210b04010180001d41000f00038030a48000ca50080700d0300c4010000144640c10115100340300505461075652190604811116500c03420f40f225440c213541880b03a25001111075810080541e001803a011403081080c010b00702c042c04150041e040000011141203007402817000c1c44a1241c04c1100301a954610703542d2f5540940209a424194030000140c9490720b25002d40840b0682e4000e484665151a000400e007040109020080300f1501c01540c030030354580740100300c8280310340103d2100e81440182e190000f68080c04a24003185004414034066400482120306074800c0800507070a01c19070300040341903000340c0e40b0007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 918224217 1250 918222967 918223001
    0x80c041e050a090b01140d020f01021519050c090d030f05041221050c0a060c02070314010c0801080c060d020f0d18110a030f0b100b0a09050f030307050d12 68
    0x1000e2111030ba500a100800d0080c0410409640ca4803641d07202c03d8034528410341d001c00740c0e40031240141000508194440f20500650784660342e9480c0d500d101e1402181c02e000e07003038045440038400c600356102d002d4002e0080b1140c1d9040c1700a840c0420520048050f0103014002d42c80001100113214108880141c44040301006905000e0301e00108400d0840010181c50321100c0044610f5a00c034070151640e40400300024003440d00c140d11840000c00d01d241001003140030b07100c0e002c07010400c2101540c070300040d10400001c03406800400140030070310603001011240c0044010902035503447c4c0580741c80130020b000069807003219000d040d002d132050544484076203003403c0101f82c41200d203081030707140540680c41102c020079403c0e080002704055070000400d1a16410780040104100803e0150b0010b50081c00743c4a00b85c441c03c448400d80c016054200006100b100144a5424403040f4000041c4043c1c004500f000c0150350395944800c0f010802c01c0c10001e0340404551620b10681001951003840101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 918225467 1250 918224217 918224221
    0x10507080309100c0c11190522050705030a0c080603031909080708060f151f030b030106091b02120f0f190c06060e062b200109060207080c041e05 64
    0xc05802a117030800e06607407000d4001d400d4956400c1204800502c00e4001420000060809003040340f41045443d0300002e5000401344403c07808204d1243e603000f2610f5131516901e900d0000c0c540c40644510150007001c001d880340c01d0040903100001521558680180c1006084e80f20040031903000441e41e020351814451500e00040b080c2001c40c1450140551105503000d0b580d40700000022141e01c10504c0d5000074a01002c0b07a00c00c83d25124030440d43d00301d840c011800e104410006030139550203420081c031056641c0d03441c000720303c10749298460100300c03800a86003020095124001e94001c4002d01201c1600c0060701800811101c0c1c01c0300e00b00c0c51001c2c175401c2181c24040e001030080402080880e041d61a0000106040d547c11500c24842c3d40300034a042c10811115010960140078200d5081c0ea01d100401d88a000400d90640b81c2c402e00c0c40400c51100340c001ca080010074040450340030034155086403c007030250320000f107154911001c00784d4001c600e240d100c4d0703085255442d44182520401b890001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 918226717 1250 918225467 918225491
    0x15110a1203110d050106090602070f03030507060b0909060601020c03150612120a0201020c010c050f0910120e0c0906191a0d021902122b0603050d0c0c06020a0201050708030910 77
    0x8012070698010347c0e070708100300e5103520059a98203140e000d2800d5050441104200191041004040c440d216500c0403500e8900c20012403017241061300c07001c100350080400c00505503810401101e401c2000c4000b04141046040d159005600260259010769001503504214060812014541c1c0b8001e040e0a42e07200002d440c020b000390010491540300d94240100032022034410340035660b40d40d100c09541c030b02c4c00914004000380c250f90046a0002d002410103d9414a650b41c0b080c0d6080a2911018101d2409900100070740280000c028a00c1110a440100914200d13810f4030000e8481c460900c20682400b10414000b42c010160b12912241c00050b03c21541d036150261a165802c090f0200c0b044a02c0f0080e003503a01d17000e8144510500e080d01800b030010099424216400c404207074800140f041d4403a12018240000c070302d940404200c448a034042001800b100c1a0b00811841c4040c10980c506540000c0091091480c00303800b0b61008004103526403c103001e411500c41051800700310500001c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 918227967 1250 918226717 918226721
    0x9030f120a0b0603010f06050c07031202010c030f0515090a0b0913020108181209060904050106031e05091b040b0a0303020c1e1f02070e0103060615110a1203110d 71
    0x100c0d54070756203041081d6001c00d8200354080c1d9042e01c108045441e0a503040003c01c494540107100768550710321a004c40040403c101020030350b4000801c3d400402c40440750300001e810382d02c103518550055403401c0c04000b400f4512014170b40805404440b00303a8907840e2501024003611546140341d603c00c04c440203202000400d00954128075100382c854800f140d8904101910021559003425429001038800b80c020a02c1d48000340210340000f081d103401e00861074041002c5500036040b180100390385803442800307215221110038502a404a090209141c401d080740c0e11007852540380020400300d550000001c4e03880d5084061072070809482000030311380d01d0030006e6480a04280c19070080c41c0c44581d80034074000180400c1d4040d240070b0702c20f020140315444409030022141200c1400c5005003130740841ca101c1d540c0d181a00031070045902191150524190301c1e4295000e428040c24054801b1548010304400706445980c2034015004112580f2001816401341101015501d0048000203400707803248216 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 918229217 1250 918227967 918227971
    0xe0c030402010801120b04022b06142d0a021605070e0703021305060a03060e010b0c01060f06081f090212161404120c0b04080f0d0e130509030f12 64
    0x36a56840e07140d0340c1d40005c501c031400240000c1d00c520041d80004000d824030325064001a9034044180510348198022010030400c824021205107031591071003580149000e2480380c00100152200c0703c5010520b020f80b110561103c2d0311032600d5500d500180d40d140196040c1c5801d0080c0c1034a0105a111a01c0d081c1d4444e4000d0003210f8071070401d03c01090081b8864402c5d540d8409107200c1070542d071810041044420703003040364a5801c040d100c0001184040b00003c60768000e00ba5a45100c0e00c81c0030000001c0e09482154110300100c0c40041e01c1041000e501c1101c00303400c2510040103203944160112042d8416003a60480e50809000003180e110076114105410301c248032407600f00c5240c14001c1e80443d02c943c86018080b800c0d0304140401d1242941106003410700510601003c14003950300d8079200c842d034002c0d6100b07982c00d411840702c0c01c224480907c400500140c01e450540c10072800c03000022a000c04a103000303180300b40e88900140c4038410800c21507603038a1680300301035101c0500d183c0d20f004004007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 918230467 1250 918229217 918229219
    0x9020a030e12090f011d04020a0f091530050c0405010e10140d0b0d11190e01121a04060501150206070f030e0a0c03030f02120405030a08130e0c030402 66
    0x38111882d403203880403009907a00d4031001440090416081001155400c40b80c9080790008100325554200c86d941b5440108030800341501d039110240e818803409800042640c0c4195801ba040c50091400c16501461501107188080340481d01d002003000c000942d11000c91411024034502028070148000010140048501c2642e80305410702d10a000d00c0100c068408505000c02d100310107902603040d551300605110928903c00003400c0b4400b0001400240c220341056a03180380c03c4e00c0f01a0241000360264507041070f03002d089103086140441900c407007481403040420500108840c82e04008090b000e02800c0d2a06031901d07141400c00e0308000000300340a01c69004822401131448200c140003265042c81801c1c0d41c0c940d003682d8501e1841c00d801030181c00c1c0c25401d80b40951801400040c6142007404041d602030703925142030f213400400180c50000c000182d601c01003400d00081040f03a8000904107803007984003c11580711449101c5c1902000070540025024051031002c10000c2d005040c095482240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 918231717 1250 918230467 918230473
    0x302031b0616050403080a140f0d0b10020a0321060314011d06160806060405040f0e0c0406050d150b06031815061309050c0d05070f0b0f04030311010609020a030e 71
    0x80c01c001500c3e64030851100034000002403010303040c034900a0080e00200002d44100c10302d4259140b0a00f0f00a80c07201651020300d41e80c5c0c080d41302d02ca09001c01d445030300b90070034002032490105c0c2c0d0720007504480c5e001c2d078803d0b4980d000c00a03150303400006070800801540d201d5003104200c581c1c500c000307019190b10820000810300c3c01d01280300e15540083d0326030054103500120307503500d040c0c400300300c596250007003156800083c1004006200d4695100f05d00c0074041d0040001380320740d031038400e050034100703420040c0788602d050400500031952040b58081102d9807241d90010318030f4510ba00d82c1c014103802c402c5550b008402104001045032201400e071420800c51042d0303582c0080d40c1c1c0f81c01046000c07d5a4458020141c155040b01401c119408038a105000b0001c4401030020080051010036869100b280e4039007258034200141c101a098240150455610300c2d404c1c80400e40d210501402644000f0b0208200c9092950700f500080d03021b68003400c111a015561410700030009409400030b1089080d40b48 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 918232967 1250 918231717 918231751
    0x1106071a0a1d0139081e0f100504061406132d0f0b030c0a1826030309061f080601170f0604050714130513031202070803070c0302031b06 60
    0x110310000c8030138510f441618481c0e4103401c404403141c080007002c040750b12102c0c50b0060f40701a5483c1c0720034031403084c0d5001030300c0da4603181104005410300e0754484d90080e41050381c01e115a00f6800d0588400c20016210300b5201c0c4030440030702c0100d600c02d61080400c20b0386c0c8150320000c41020721444410f1025002c080000f19600c0080c22484d15070303441582020f0b4000c1c0003080e00280341e031000b00381c90b4032507141120b0b0305001c442039520f83c1c42440d400b512800d0f1814820342010502c0301144509481a80d01860444c502428490740303030300d401410a18440312807140101d06010450780d040240040d1012101c3d150707104c0d8403c0c51031a000440280c0c0901c510300079056402c000085040c03080360300501601e140f0b8139003c0701c0c21411480c42426a0702500400c08400140304611465200b1080d0042c00c8280301c006040203421603840f04144203180740100010404200c03184102c2c0d4000b07046280c17900034414607050803070643c011405840550703180200e424034040b01c00107115024220207240c2c4000c074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 918234217 1250 918232967 918233021
    0x807051c0e010915230409060509040f08030912041409160c031101020d0218090c070f08070c0302030f070503061e0c1b070306091106071a0a1d01 64
    0x750140e03507018002011000280310a138541c064124000003913082091007192121511500094100c0070071160000201d0100b080c041d55006200081c0002d98844200d410180c0b18412580c16a4001038140440000411082e090070071031700d8a4900c109000c1502c40d91a450041c201d01c0c1d4514200b4814501c180100fa910b243c21841015818219100c1d0707000d95507181e0f4162401a00e2070340703d000e155801d21036008141800c0c002450f2122440c10014850401002080030442c00900100300040c0c0074408113000a40800340000041d400c503010030345612403481d0004d8181c12641000b0741501403140109203c3d400003585400b981c0044095480942d100d00c4203d07d00031000100f030342800d40c45408105480c0440b0300a0010008c0c24410101e0701d006a1040361914040e903108a071401e680b00100d90910014018004800500b1949546007e0f2280c541c200c180e50410f6552045c641004d010030000c44440d48440d050481359216003884a4035100c81d540204480c1c1190701e18a21700c50021900 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 918235467 1250 918234217 918234227
    0x10905120a02180717220c030209010f060203180301020d020706140105040c270e012903010302010f030c0e0909031b060405031902100603110102010c02071503180807051c 75
    0x104d20030642e13400c030021030740401c03401c142d80b4080e0520103504220102c40c900600b03200c0044082c5801b8181302ca058920707500c140003031030105901c06208a01089001e1100d15030200c1180c0020b8905001c080103d100c10b00068020310480241c111001d00c0010312804101c001c6d002400003084000c10341d081c07a82c1e40d40600c801e880a06040800089206250f440c0d00040c0c200400300801c00e011855a000742c40701d610b5070603501c0a0304035601c908020046131041d0421000c2140c40d08862508141c00d55165600280c28090302c0030355541803680b03c15440400d03134442d070702915008a008268100505001c040c040d103903840440d21212400e19103000c11224170000581c0d0340100d81c040011480c00710071200102c509a11210307010110700810341032500511441c015100034500640013912140040c20001e42182e5003001079001b550014102007201840c108251030115019003004034603001c00f080c882c0c1040d0707100781c0e004000a50200d102014000c0000b0782c0e0b0502e400001c81204003828079401521 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 918236717 1250 918235467 918235471
    0x211015030606080619090c021606210225140c19090207151104150c0f1401150803030a050f1006230706051914010e06010905120a0218 59
    0x40811803c2003c40c05500b880c510111090031000010000a80c030b0398280000e55158203a4000140d02c084440300808002c0b14240300148400d080c40c049829000440d20790300440210205209913010a0005d0070007a0002e881007802d52000070360150f004280707850b80690b403820250741b04a1091010303501c45410401545011009000d07090701c02c0a19185ca450080c2d44183c4e0116142c00c480801e452803c1e041f40144020309003444100360310f07141001000c04a1207101800c10080200c0c510b08000464403a81403442e40b95044035248a002a41e100118050840e01c0118800c23046032032400105080040040c6004142c034031414000b40d16400d11888100c13809540034108503048820030001140214913114000c0c40c000300d0b002d210703484081c01c400c403070b040400309a80070b41c0c48d001084100303500c08003401c040c038019410400015805001102220b0014096604c8074034a040c0880c805030700880002c002044028082490307440c28101c4e294075220050b400301d01840201071050048503a0100240c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 918237967 1250 918236717 918236729
    0xc060621050d090819060b030703030305010801050a020a0804020108070e0a0603050103060c09211707050309030c100c02011409060301170606041802300705120d080402062110150306 80
    0x480c1c4480000e40701c0b5001c10102c0e0317080303880568840c483c6445403070510565009502a440000781589040c8140e03007552401001c0303610591040110800964010a9064100c0c1c0c0a280c5039100307030307030b903100035900555956000c1e03900603400d950029005901da00140c1c1038070302c500001e004100041da82910401494040d02e400c44907400c5000794599140035021100c54018003c00c131002691202a0103130307500000c0305803155080080c5100150030200800e00c11000145d841c46e011000780c01c0d009040240442009040041e02d103142e44110104d94240d1f50490340050410342c0c0c0356501c00a0709019590210741014038080c0b0030000c3c20718542480f49001d182c4540701c41181080040d400c1112020207880042c0701649000c445090012401c0b05003951000c101c401060f586060004110000c1c121611002c0701d684811403401400e40c0c0a4442500540c0c151540b603190120b2504035512543c40840580c07005d40c11200300001420024001c20440d120406200e4001101160072002d40c1c150740916 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 918239217 1250 918237967 918237973
    0x1504030b0408040e0403030209040c18090c03060902030f1e0c0f0a020a0507030b150d0804120807121e02060915101d0709051804030c060621050d0908 66
    0x800100d50300c18401540a841001c440e0f2900b5114a20225441400d42c0d058000a501080c0c1f01071328105403252010581d4036003041000a1000614485e03c940140509000780e034840003c4071469010780c0240780a445268815034907882c01000c9075041071400c079001300d5515501c0003440004103132020118000e584401116251580d1f4204040701c60b8402ca52003006c6114040521f004030780107000500243d44505514002424400d203140c0d140c149050000e0720a10544000c0c0d00000e140c06c04075803c840303100050401c00201c1b42040000390007a08006454110b2100d4401403091b4024401e85545040d060100340101c0619030480c0d0b10a022551140d4550085402501c031440d205802035203c48403610314945543c89042c02006214240c41030a0176140450078045020740000641e00582425150607188007082940380300b20401c05030020b0140300742c50711001c0074032080350081009403e500500305107810350100341e42d0340404400b02c1507c941c01150a1070f0011882040817100300c40303c034001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 918240467 1250 918239217 918239219
    0x2105030403031a030627070b070f060207020d080705011d030a0806030f0d08010e18150c1e07060506010503060a0308090307150207060f080402010f0e0a09060b0703020106051504 78
    0x5400030440303075411980c03c125100c0d1005603a5010008039100d0aa41810302841075407aa0582c0a1400f81c6550f044071500710200500901442c0b005036042d0540182010007110900e040103c003c1c80b8024000c0e400c200300110a03814001c3d0755004000344c0341318100810442030080e684032000094410390f04010b03001000340000b1180b0601c04190055001403e0f00c1c4c25082162030f96150681540c0031030082204080100040e001584046030f01002001c0d040ba072411211041c82d0700c0b2180101ca4a000c4280701c0f001c2445000d0031001d0318880c3e16612222404409510301d142c425810890742129100d00f0b1a0004006511640070750b0700840c00586588051419982c0e407000f10b4001084440d09803040400025041c9800b00303c01c880c4441540207403520504009000349603060850441003070003d41e60a010044c0d90099a420310015149003505086075410005204206503511080a80342010740c041181c510041c000c0000364403c0c0c000304616603841003400304c18540790701040b003048810b04c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 918241717 1250 918240467 918240473
    0x3020901030b090f0d0c17211b040f0e0a0b0f040b19060c030206010602030304030915051e04050118050a03020103051f0b030709080114010b0c01020c0a0f21050304 72
    0x10946030410119010b54900c00c0600d00c209180031210188240040d804581c1e41042c0440c10b85050b240310840100300345402341d140030014140d600d6903100104a4030107000542824540c0000d15820111010425510ad903500354030354010b011401406a0016000c0101e00e491420b4810b03810101c001520b50035029000c003040000401210003100e800641c1c582c10440b5080c18005804003602c180e0721014a101c0c1e142c20000e1500270160410020340d4001c0040c8400709800070b20380001c0ba503800d06125084d400c4c801c030403512402000240c0d15024550842130f201c0d011223801078070030384000b0381c1c4500d0520100e480c05004458107118039500716a00c5641031025510039000280d100c40c11000c1c003420700811f6600302d04130340401d600025070008044180000c0d140d0104681008014944c02407003038203e074119501e01610107120720a00b840b800540c0d600301c00ea00b034040d40c814503003101c2070303940b0508141459000340e014a0022507050050240f103c2c0c00039800e481000c800714140e0f580c01e040d59903641d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 918242967 1250 918241717 918241733
    0x7030e0c0613030f060507140c060f10050d061a180604021806030108060403120c0815030f0f01051f0806130501141906061125090c02160605040302090103 68
    0x1000a03840c0c4900c0000400800e12134021000c1052007500f0010340c41c036007150014038542410f203080607140c00411002c100d000000401c5508802032207a404900e0b01c5581d62a801c2c0f00250340100d4224000000000030312149600031480d0000d0340c49151010241c03c0100a0300d40051075503098180480c00114480707040644c043c2c2502c41c180d041c1c0403244440b01c000111949c00c2640030701c826921800401040550041c2071002e040c130140c20500203c00000340240540d600200403209109032051964990354040280140310345814050303c20b0300e41120b0b1618041c02080355001c1c03827204c0e540f040c8140c0c5041d40c1a0b490440f04014040c1003d03448403450142880c031401408d031100d40d04c40e0310001e910200a1001d5004241d4185000a07110021451500340d075000d0340010240f28404810361f210040106d401080b0200a91001d10594461030704022a2100c0b508540062450090004405600060103103020020342c1415420329035110003c503440d104600000b904685000700400c0011010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 918244217 1250 918242967 918242977
    0x1050a0f140d050f100605150403020f1801091a06030c0a050309030f0d1a04060b0306060d150b120a06080c010c0312090308011a160b0402010c05030408011407030e0c06 74
    0x600e490324075001074560b01c0c608070136003509100c01e8015038010704c0c5020352442011300a201c2561707e1140c0180c0440c000c6c07040e008a11010303019403202a40d444983d03540a1540d006114882c00201d140d5840c0c1302040d000385661001e21a0400c0104410b40c0d59103402000c0d030340308a080448940c034182544004441e140c0000d000c4040311b11042c8200048224507501a08020a0540300018011520300e04013042050780101180100c1c54040b092200700c0d007210441c1c0d0b006400762031180d900c4e9410a10a0010145003081400301e0902150200d1104054001020184030000c40002552a98003a0f8030480da0284910315156011413200302d4154010380b00c0844082c024140300c10300400f10307000d030015100ba450707045001030703480001400108022110380003161851000c250800c2800c0100440c08050050050243e00000001904580c0304089034040703a0b921406882d111651104014081c02c2c1c00c1e2103501403095820b0014040c1482440785c48000c00b0301f40014620201d0070002d03c2540c0d400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 918245467 1250 918244217 918244219
    0x504120c020d05011b08130f1101050408011118011106011509030506070c05070b09030705060313050a1407060e1f050904110c0c010203030f01180f110304020901050a0f14 75
    0xc02c040c8070080b500c20b106050422070041501c00da42e90904d04e00410b103160082032402040c0351109103001042d840340304240403030383c00020391040005110050318140540d40c0702140640c00c3c00d00b02045400188003030301d2594003044440c0488190000103503110700488a007207006501280041000301282c2c1103015240c3e00360700f00100d02a13140d456460070401c0c201c81c96030100700011280c00800404021100092000c0910f8a040216040020391104680c0c843d4921488012010404800504041d007038015440404c4580c13900c1c032403400741820040901c2d58a0305004207040043ca19000e90318460751180b00410381e00e03085114003401c02c01c20000c0c03400c05040100602000200741c5441c8a0011550070340e06d1142d441d1a0780301801d41c0341c0044005014115041407050110214050750114155081d03200100707146640040d4540041c040541d22420b100d041064840800c01c501005500507802035400100980e21002407120010003031180091110b000c0308200900d00d2441c81040031414 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 918246717 1250 918245467 918245479
    0x20603070e1507050f0d08010602030a0e120f06100503070605030f1302031b031c09060f180e01090b0915060a0e03030c070e010801090c05040209190906090608010504120c02 76
    0x100b503200c850101d0b005540d04950651120016026503030007006603440190882ca480c422035810030704002c0d1240514503800080c40801070040109580c0d400d02031800c1e1350030070119110380900b440b40c142d560b54159a680c80c28804244c0c0828030b8140410010b040e1044c2e62522480c646036101c0014556070010492a9034141a2094500699060010ac40c811004c0035540b52122103007004c0500b0071526551070543c046003540700035243c3e85c2204080e0204c0c0c0050070045241e00301c0b40c0381990001070041070301d000c2010314503010800404d0510f00d141130306c02e4441c04000710707101d135828002042030070341e0281d55681641114418508e80b490042091002501c1d00103400014800400e145030030400e229040c0d5005000c0600c14000003801d0240141080310082c80000030799203400c2c115502e81e00689001e1600001c040c3e156466526620195001d0500021849541c548501000b00068060242c9446c101880000c0301a014010540203c1d00304107001100c2592600c2550a000d14200c04c0307820003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 918247967 1250 918246717 918246739
    0xe0d030c1104050c041805010f1a0f0a0201050403030b0123030c090405190e0a03080601081015020106080d05070b0f221a130503120c13030303091104020403020603070e 74
    0x284480c020940513050450701161260306080d16620801c0d01441121480e601e00001088003140400690080300c03503910000d490f5080503c165085485480b1021616100014070301410075415800a8411030203603500b089083c0152004480c020920710708000c45d0b00c0001d4070510f141c0307000f00043d0f402a001c04903503854685080042419680120341c1524104183c81c80f26040032410300590341042e015070064260b464440d5005082107a000c0c1980d410000c3c9400014455803405a03250b01600c5401062201c41d041d83d42c000740070f00002c3c09107010500071105007482240c082e2080c1d4081d958841c02c0900304d990344182248592100401c0c040641c040c00c001c1c05840c001001c1c1c0044454000e01c0c01c01e0b030160181011080151001c0e2006100088007000c82c1c01041d408001e0b9150240920103400303058443c403240311a94043d5945000380c0d02c3c407030b050000c1016010b50001504d244111802c0c0356610103c4100000c0740100d11010750444400c000103106103115640400345060000d0100c4494 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 918249217 1250 918247967 918247969
    0xf09040b010509190f090e0706080a090f080706140105060418060e100311030d1209030e03061303020f0613021c080f0a1709210f070516060e0d030c11 66
    0x102e4884a00e0180213410000340502000c146901002d850940f0081c81258a0302420319512031007841104100f00d004400b18401240c684c100c00a61500444941c408501a003042d08a40d4007070307501200c40614142203030b43c801c2d00070541d16049510013010181420312380385040800341784402d82d990b00a1f585940100d2075030241d148a80c055000c1c0b08030b0412440c254500b032135040ba0581c4000c1d00c42d5102d002ca080c3c10f00d91208000302d004108182c04150514140f405032245a200e40c0585e92500070b500412804a405c444001c01d0b40e8025401c85d0b4883d072000c49003c0d02c82e14250788024031103806492a10160804a0000c0404003122080081030344050701e0700c06850300001d41d00c24180d140011007007880c55003c410700d810400ca1038003c1b0014100052850b0340c80301c50a100145c080d02002c5c02c00280c950503419508040009001c95a030790501e880c0184c0c4810415203138a504071203190000c185544a40b0300420418806043e15410010342c0e00c017941e480c0c84030001101d1880116012a0346 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 918250467 1250 918249217 918249229
    0x7020601050f012d08040c0608060f120c04050c090a140303090d1703011401110313030b060f040218010f180b031b0a0905030c060906070f11060309150604020f09040b010509 76
    0x44c0d50301650380c0016804c0900c1c242070412903c1c2d010104210400c4140320f81c2d507540110100107180120356800c0a80b1280c0b0641d410031151405895000d0715000030000c3c46501d0000500940d44201d690f000d280f40c49100c030340103040d25100c1003034060303106101011042c140000b104501c0c03030240b400031110ac401500101d4940d4000d0b04001031045030680c4203065035130031030b509441000001019604000c2149507112a00c0798501c0054160440351010444a0b00c1c1c103800409800b60184c801d40d5541451880110014611006603000801d0190a43d400c14401e90828030074807429210080c0300c0d4030388415010207401c00f410001040504d40015461600d0701030090500c6036081c1c56640601d40307840300b05810500501d003240e0042004000040c01559410100e0781066400342c4080c040345000d003400744284140048031604000e0020500845150004041c5205504842701b25038950707a00b0f0a0009038050700d0170f400c200725001d110520403803609400c5a907050704181b41641c1442c1c103000014103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 918251717 1250 918250467 918250547
    0x41203050405100503010e04020d02130f0b09150108040303020705010b131e0e0a03050711190305010b0f0105040608090a0602041409100501050f3f07020601050f01 72
    0x8154000307000c1105062128459030102d540303090007801d40d0b1608425414003040108000e104426125030b0f03100b10364451514503c003004012081080680c0c0b0a00c0074020b00f44c201c0301e184207a05a0002801c1010328410036079103048107a6490859403226a0150003941104200721095521080c421045481701c0b090301c41c0c0103c0540c07010441200101d030403d00901070b0207400400c1c43c14200255a140c400080e40d90480c1e506d40343c0749540f01704a04091110f4401d44c24404e90161070b8901898006449001080590740188020044042d10004109882482324040d41c04110140030400129003c2d4800b55482041d0400761340b0f001d0760b15a1000304a82c800d4010301c0181428010001742410401031070355010031f06407d118101c40c00c00001030070500810a108070120000903c0c242c40300c83c100c0142050100314940e0394444080e050381320803000c41d2591030000121101d40003989451001075500d049900180005c036011860600460302400e41450000012030ba0000c0b4040101074126611 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 918252967 1250 918251717 918251723
    0x11161502161514040308070507050f1903080a0605090609150907050307030b01090e01090b010507051b101803061d100b090705070309300c0906080307050a02040c03020412 75
    0x51030704001d403006141100c443c2c4481c6600000a0020880020b030401081604041075061994031038429140c0b19140007401d000c0c05e071250040344002c408640002c095010901d100c1e8032841c14555800480c1022100103200342548440310b01c000c1055810060041c0c1d410600d800e805840c106000740114201c02c005403030b0b000004000104024141e83d040c810351034005001d10b4810742d86480c080080345055010b003d00580707107654200700c2c00d0603030058040b00c0405030701c4010b07200c2010401034000700b041100d030b030817034005e460304d2108944051085143c11520b10b80000702544141c1180c5440300203241501c8042351b006010700001c0180e0f42d04100203c0340d60700704ca001291601c0303151705214118801a1440c0c4c03d000c0140700742d200103074116a4941c20780d8800310244802040010440c0d04c1401040b6403108408100c05801c014007000d5007440b419540b42c0d207003e00899950b102a29620b10550740040c0c1160802c0c040540180f80c2501300010303d40091502504198079910a5190403071520340031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 918254217 1250 918252967 918252983
    0x306150e0105010c080f0318070303021501050607030507141002040803040906090504020d0b060a0f03060f1104080a0b0c0c0303010602061504200a021612061116150216 74
    0x20054080d0501149000d048203180101c2000740c02d03913400115006078403041071948404000038100c03110440100320790250010072038900c9070766414083c0d21403854410011491040400110750381c28603d0807240e182d40d050751020b01c0e100840c2c542049405c0300071000f100600500c152104200c04a00141010300b1544001c4d542e11890300c9815000c65426501c58806030342444100b10248c0d94131049880b60b10f4000005a610756580000a01c00c0c40d0560010148203003681008010701c11a640300e4540d0502111003004507140408600300107008520502449510002c0400001038014180d260003d2070701100c00c0c100944001807500f1354109802a00050307002004100b6113640350001645201000c3e00c04100f07400642d03184219a200403240385140c458009145808a0310800212000380d030b81081c006140d43d2285000703541010030308420b550040c28282c03191144804402214590b1185810150300c08120365541ca24104000b502c1030507a944c2405011405901400070303c2c40d4a125610b1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 918255467 1250 918254217 918254219
    0xa02040501030b0a14061305100801050117271906150b030c09040506030f07241805100216062019150f090804030c08030c06150406030615 61
    0x10704840f005510f040c4605807000b0200305510207007201550f1101d0959000c0c0c0c0d180c044601c0301803a1140760340001c3d0030481d00b044040006a000e002035040e04d401b6610078000030806010389030181001d9680c4840c11009164001d13040011b0038000e461404900143c0d545441010301542840403941e000347c590503120850b042808480c255590007407d042c000381d03404c50405d00c88504840c000d141855004680da803000c1080c9035000c00c08640d5401c1c0404c1100d62072070b1180c504034800243c0c1c032080b188950100514032400c41c0101007020550703040071f504580d240c0ca40f8040000144006020900f0340c021021560300ac0c0000d00c1c1c00001418040d181e0030403140300c03030040101e212142d0700c503070441c0d8014502c054494220380c0061801c950b00451301840365400841c0240040014254000d01c0c00d00d40b10800b000c0100d1100504103c5c1d008031400d000c1031703541c1c04480780c036841054004607182e00100000b8403920030520b80c0c000141400707840015400c4d100d03030340c11040720401c00d4151203039144400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 918256717 1250 918255467 918255469
    0x1303020d14010c0519050d0f091505010b0a1d210102030f060d0b0f06120d090306050601080907060c15020d090210020c22020c0706080405010c14040e0a0e01050a020405 74
    0x41c43d0f4100790914059260030310a40360346961482ca00703010010003000080f820400a11500142d140405482c01003003a49170381c1c41c0903049900184015440c4171b0a24000060201d524801e46a0840c41d9440d4030a4400314006c0c0d032690706156296050b4080000103000312824030282c42500380511540005a983c00c08030041600180300402583c40703801e50a40102c0040c405440e40b6801409943d851700c3c0d10380f9200c00041c5020401d0100302d007144070300300c480c851495000c1c403200c00712402540c003003195885100044074002021120224254840709003048000d00c0341040200341da0240075843d0300c2141100c001c9003664041d0b40e04010740d03034840018005614141d680300c00c40c00c40ea40018070070b00d50321130b002c9650900201d820303403040da0041c00089038480864040710701c100303480402c0d039031030035240e441c05880039001b076800750341e40c1d807a101102030014014414030340018110308882d8101450900304600000006003c1070000d80c6402e035145400c2c9090140078043c080c585809a15541090 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 918257967 1250 918256717 918256721
    0x1009121103040303050d1d120a0912020a0b031305010507110613170a0c0f1a0c040e04020d02010e03060c03180115210b071206090911061303020d1401 66
    0x100c8808010740041208000080d00241202e07070700800b15101040c2c1d030f0003243c140201c049010500081c180645500400902d071400c0c01400142c40b107440342c00d8500d0700e648080210402500e070094210140a80a1000400c0f1340301442e80284401c074040080c00103036440c039003940c0c000d88410f408940c0800030341c403100e01c051000d56801510b503c26030503000e4042e01c401415901c00c04280000d1403000600d0052a881101e1076941c141c4c01c402d18143c4001c803494001003018000501d50500281000410b55140340c0c00c003100d0468642d00c5284181c0c0c1c07165000c1050014049200f00e05015001c10100040d0b103061044a02c1400f5450655841e480c00d14100005e070b1110760540b607040e03450300038403419502d44800c090081d14508440031002c01d10035100740c0303800c07044400c0c0504028814000c0008165000141100e0241d40c0303c03041c0503040c0d95100b01025116801e00041c41a02074091440c606d09080c800b800c134184080e03070191740060b0741c3d80100300b0032100402c096502c0880c1819404c84c0c42824 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 918259217 1250 918257967 918257987
    0x70320130e060f1b120f0907030f120509031b0f0f030a11030a0b010f1a0307121a0a120507050306220c09110a14030606070204050405100912 62
    0x981000e208441d4030781c00c0d50351290030052641e2049458040480d00242106200c000004140200c0b15525a981e00250380300800c100e80000c480441c580004607002000708a200860b41c1c018400c0035038070015900c00a0700300905806c0c1c82001414814482c491303804108001c0c1071540e0b11000c01400010301c2c14060f000308000141805003403d0003850301b0544000540040711900309000061701c0a803480020304180c00720f1000341c070030190607001080340750301784d9403500494100804e0a1a131140c223070342e5030361140803c562a40110f4580d0003c1c8911003015080700401c2c42c040a84008040048000600c6044003600f02d5030090a201d00c1e903000b080810044a0080d110071030040206207442120050000c0d019003e403203980030010040c1d002c1140514410000e411405424002a014501c8030903261300483c200c00001030300001c41484c001142001c07280201806411645010425000c0c08007400002d081103490b4407900843c910191440d10900b203425104228512041d110701c075000700040c040c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 918260467 1250 918259217 918259249
    0x5090d1118100b0c010e0a0311060112030e1306031407140301020313120302070203060f0a05070f05030601300e061008100902040e0f25051c05070320 66
    0x4403409010a4202c4060380c402103600c500714182d600c4036025020340c05010500709641a520899801c0c0041640100c25903030480000d01c201c0d0141da81c0c80101c08911440345001070045603903071800b6210350910034551010022031110114000f5540c0d030350500000c030182c41e9400a81c004d0170052207100f4200010400b40c1c01d0480c000e42c11401c1801481060840c1e030200200545800720724031040a000341c040d0f40c07505400509441c02441c204881c0c00500e070080b41d04280c228505400a0401800303903c156241c032640d540e4aa00355561003006643c40c3d001c101e2840000751181e640700c0010810120036480020445e000843c0d0400c1c40d1050744c0c944000500700c1c03400744074034400034040f6000025805080d5a564400410750031098004a0018100c0880c5100c4500602807400100c800016100c110f0600700642505030880c41065000c008980740a603940c40007201030000700440d0040d00b0a060507004038181d074009a603a68840d084a10740c80c1d088604004041c08107100c80c035041c0320031806011 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 918261717 1250 918260467 918260509
    0xc061801052104120807110a0311101802030f0708030715060b0a0804020f010309030504090f0e0f1006090921030b030a15110c030d02090105090d11 65
    0x8011251140194200426040200205038550740d011505480d090b0902505240d510505081c1094004103400100c90300c0402c95a002045441c2e00c80d5091042c05890300b400f500d041c070481e60b42220b020442c41300c00301141c0302e00b042103a20502644515999a0f10118401054041d10300c189410000c550003450340d141c0080c001005061000310880d0750445e801210280691115040c030380c010f0049030081d400e0000040f0380010030a40041c07a060003940200d03021800442100c2c01141036401c01d0300d0080005009100410540303010340c102d04480782c0115401b00b000c1550b01103ea28002c00303580221500c1d0701029050000104a03c1741c803020780489034041c0400083d0f030f160760b070b024064114010380d110401e41c180360b2090b1080d809205841002400e881003001181030400405415402d00050070b0314222400f001e151940046a54026084010b18105503401910310300035080750000c2c90612000b0440112159500e0941600d41442a0005c21118100c181889540c400050720701340c8a42e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 918262967 1250 918261717 918261727
    0x4060f0f0504020f18010207030c090917031303051b0d080a051f03020d050715050c07051206071d09040602070302010b101b170f030f1b2a1e0c06 64
    0x584502c21107100c05e10740384422603003480c3c000040303180c1502540003800c2c14082e84004108141290000c0107194000c0c1907850280d681e1400034084c5100689025500002d10419280041e00550141c0005491036a4400c95050780c1000f0380d040c03400e04c0c010000001d807041c2c10060960010300c516504000d208109058400c1d502881144015180c0000b9210306814521942048002c10162002c0c0025494080c1d0300c405040014101d900001c9522100c0d029620000ca1581030000e40c1e1a141c1c40c1070301c0201a01d840301201901d88140c00314051902e8145640086502e40758820346500591240300b00590300c07041402c1c000d007150400d65515201d81140103038002410340c81400a5840464111401103490580c035081c60181c400d040b65480d180f00105082840740079407009980304541c207400102e0b0707954640c0b03603a20420894070b440c00000751007405841070310030581c284224081c51000114400e298121005441e00160b918641c60a594501d16920000d100784030888142c4401d851803402c0c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 918264217 1250 918262967 918262987
    0x12141506101701140d150c0323010603050903070b13120201180b1503060c0702122109010509030f07080c1008041e0f030504050f090123010e04060f0f050402 69
    0x1040040c0f2a8400150f0311076521039130b560f01c1d0039803e400150b004149508604840001c0c3c80681a0140004003283c03408003205010350f9003818540300e0100000c040501a0700b004820340051001410340800c80c8010b01071a0002610800c03400d016042e580b030303120411011454403000c0783c6042d00001c011641861091918070300b0b88007940048941c003071b624401c2551030b0404008044485c6404030b6052146006028901825a00130700390540241d44034540142c0083e10150b0315802091000b6000c91440850480340390004098450883d0501d05103143c0141d0000003072034042845105552a08800030400540301c040084c0b1003280b030290303040d02c0d140d41c01410103095000014005800140100000c010004200d9101881181d00c0400c03101ca042e514100240135401c42c0c006c003802246400304039001440c103034000d54100e440040040c1a10480c0c803000519082d40f81d4000390600c04440303400c1d8000c2c1d549014843c0944100d0103640c0d041c0b4038200443d01c0c00c002c00c0d400309004030300c100220040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 918265467 1250 918264217 918264257
    0xf070305090a090912030b0f0312270603010611070f0608182a0a030c0e07121104050103020c010b0918010b0607030e010c0c030501061805090d08011214150610 70
    0x41c5072860600181c1547c1c010f0102d2315140000c400580c1c5030080e0b105d103810307200c01000a000c2d4a860b0943d080900c04649041f03840d0046103100241d03010030140300411010348549101400050198166400703196030301c214400b4080c458011002042502d820010814110820400e0050381800149128241c56100f48840e882c1c0d43c1076101c0c2c20b0a940180400e94688909071030040d0781c40156010126a10130f80d440030410f040d0b4000d800138142800c6418491010700414650890140c00e403458207150000641c025481240c8440c019500c414003581596075001c1d0081c428401c0780e07100c0c070405400403111380c01c40710711196040c8201014030910020a0303000901180b0240c0a0901aa1035515030826030380c40001035000400781c0d0700b400004104045040400b400c0c2c0074840500f80503613101d0a04840d152140e80301c0c00000112524010041001e04407901640c09000e0f81c0c06101c080903c041c114200002c80495011000d64082400b009040044400c4000e14252500c50700341b52204000d00b80c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 918266717 1250 918265467 918265493
    0x8010611011401051905030a0614010e0106080c03070e0a0f180213090b0d050d0f031d0a03080c0c03072a1a2a011e020a0e040e01020f070305090a0909 66
    0x40140d001c43c117985441e61910880001030980103040319418462441e1801c090014101e010200c4442c07600006900c3c0c1d8080913448c140d0340640c1b1411129a260284200140c02c028021404c120356400807980c2c544424600201412901e1008021641440c129407100c10131a401000d61900c10005482d0219802d500e034000c2d2526410003103081c1c0380389000034644542c001d102824038015900d50b1300805401c604401d40144550320240030303c001c8031403500e10021185440031a650002521007001078450300615030311011001915080a454201003895500400012a42c055160034501321110b40d40041e01e201d043c020030303031401c81414046a503006c03129110030841302d102c000c50440c44c8000c44030300441c40c201022205110079400407901c1c0b03002c1c096101640300700b40020100a120341034240210744a041d1180c9408070300062440502002302032103c04103460f55401d20401200c841c0080040581e00d0095030b031552103010403010449224030f00e50160740103520b0680101d0000d201d801d1180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 918267967 1250 918266717 918266719
    0x307051002160e1504060e0609071404030f060e030702031005040330050108010c0e090c070b012301031a0105070f081c05060904052e0c0801061101140105 68
    0x300800d0000c0e482c0800c03040469065048425011403121824a0720368462031800c0300f0b14121840880500040381c68074094405d211341104005003080c24810950307900510149004003070800100408142908030b034100302c4d480c05c09001c0010921200e401081c1103e000c680155180510583c0060350700e42c610010103181c40e40b00c4000030213140c0206005c40c0c594945a030348481c5103c910f417050107091807101940b180e0300e182c880003283c410390501c10410b901c03c15880301416508036000300102c0c09001486490300c48010441c0394000350000000c18000d118590301c4882d82c0413483c40e02000340000d42280750415103070031114401c401076841054608182824016602c20342401c00e42c007912500f02c809420300c500003480d03075100c1480c4c03d2580803904101e20300308469195072007080f00d00ca0013524042d02c40d0388000d03124000070110600e80e40c03910101e80c031060060308003191140195424683c0b068007180b003070341c010048113401841440500c94408001c2012072244010015840030600600d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 918269217 1250 918267967 918267979
    0x9031c09180612030e03011808030c0715140105101e1416050c19080c2205040f11040c080114040b06120126070306090807061505120309030705 63
    0x1000151036154000d0b00a030450540743d0f40b40355281e05010b8072042d40c1e4491140039618110001c03991030041000b07102d40d02d0340b08032240d19545413403460620917002a202941c0d0110450550000400b170b502c00c0543c040942440c8030060740c50003081040f14508854140240302c030100c240c0c00010740188007000e80e80d81d18209503540f04240b0500e2402401915084108040150389590030b0140020340ea1103200000c4541103403801c0c0007502c1011484070b47c4a002d1060740700a4184009140071510502602c6000b440307035080d00342c1035900320b090f65400da8040d600d600c4001c40750001e1050504008075111000d070303024403c410000d03000901c4440144a0400600d0020310070305990750305c03a001031440c0c3c4170041c0410b4450330f0f402443c0410b15028490b8000c101c41258219000781d407201b402e4001004614042d00301c0a2840c3c5407900504081c00086404030300070024040050701d1440340c14002028401140561070401040c00320318400800c0b00e40841d0300070701030318880e41d500107610400e030b035010b80710 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 918270467 1250 918269217 918269249
    0x11030703082205060a030f0606020115030f020312030c120f0c1204031107170705010c0302030f0a030b0406060305060906030c0312070204140c0a02010b090f010b0306030c10030209031c09 82
    0x3000e5100c2206070003c0e90710001c0060fa0394002d690642041a802d00300b10410016180d9805050f030032503c0c0300e40782e403562009058040000c221038100c520540d07400a000d0311680c030052000c1150552040b1035401031a60f01140300c81d80c4481e502051a40040c003003401c4051810517903510710b0b690042c0315525402400020008081500c01c0019501050044c022640d1103611203009a010050151040046108031000003900e5803141d41a0b800442e0960091813420001074140010340d881180820140b41d140c03e400010390b00d440c40f42e80c009064596001807141005c03030400400311006814144a07501c0180211026603000c165683c100004815560f0b80b42c03814400b10300075146021400c019080354504100c01c0d1003014008140000301c0303074003c01c4810029400c0040d90407040d40c1c842d40407229400188244240000115003141d8010102c9071902443c42c0050340c1090790600710340009401003401035903070404100e06182c215040d403902c01c502640402c0200180c1d5148114001c034001c00c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 918271717 1250 918270467 918270517
    0x161811160b04061d0c030f03030c041806050a0b0a0807090305192a0f08060c1c0f15050a0f08030f030601120e060403170702060c0c0304050a121103070308 68
    0xc010004c030102c0141e000311012403042d0480e2200d0f03d1150040c028020b01e41107015000003c0104ca2149020380200760406003406801042d10000204d07002c8070325642d000c080b130b142d074641602e10b000f01103120361a617071013040140c000d000c4640a00b140c000d010003c1c4050002a602061441c0c0741070329100c0c0324a01404a0030303c0b05a070409100422004400021042c9031681c2d039100344425039954461010039941d41d0384c0c140e0303660b51017100c550503400000d00a040840030500501902001b4081e4041a02c40c1c104861508503605503e801050540b41c103410001410080c1c0940300425013080d40381c056510b412180e585a2003144015419031000000042c0546e014000d251a10401c0507020000d122f02490341590701d1900782d40a901013643c01310b010501994461803503105840c0350307000c0d0446817651035031a04550041d07103a070b41c0d5501090201244640f503040ea44002031031042d500206044076824208140141e60780380754000e03000982c0620100d0040c004544201001d04200f481449090f5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 918272967 1250 918271717 918271721
    0x1b1e1433040801090203060c03040b04020f1512060118180903050c1b0103050a06120b0a0f0f020301180903051b031605010b030f010c1b05161811160b0406 68
    0x3520020310614042400708407044154440e0103a64425401c40b10310f5203c481d0401c0b514041150024403038414180000c0050900003001041000c018018110842000004c0c0e000c07a042441968145400001003141d15a80201014a094500a029035034282011a5150b401e40c144018846140c1c5034421441051321410840c0e5000c0c0c0386006442811101103100b01801d003540102d10b0000342018042003c81c070072441000c01303c81d51604c2e802c03411250781c0c1d182d00b60140300803d90801d00d0798a41c0011407070010b03030048040a00000030b005036258140a03401c1421018082c41e80318080c60040180000787c2c0080c21650507201d02580c0445ca55400c0b40c0451440c4980781000d01d12030100036400341003080541211902010031002e84441c4408107030380b0303422540300b00705c2f00000030078045280500a01001600290728040c005482c1807440700842110b11070b041e60300c84c64040d41132407007091403c10280708841c1e07000035030a141441c00c40205010401d10703440c4d082c042c1005044a0104007085195 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 918274217 1250 918272967 918273049
    0x6010e0a05010f210c4a041407020c1203130509090a020a030305040e2503090206160b060112050705180f0d060506130b06161b1e14 58
    0x892001c2c0b2117688200360041c22140c0340328056608680e01591100007525034817003240c500302900307207440c065241400003015000305100142e400c1907803034a1038482c0381d00184086200e0580c1d0340052010118900500032021502c80b1030000d03640040c84890307900b5403003007920781c102c900481e141462511146505400c01e40c00a2000358841003040c0008205500000608200c80003246e4140e0f69a80f00220460200341c1c0e002c110b00c4458440034003068030b5000e90f1045441500240c0814148880d4004000924031102d1040d101810180d040003203540c1e1088845160310030881c07043c002e9080004001d04070b40281000e44400101c904407103038440d00ca62110b044d0f01c64000305007000b944400d0901d28010312090b02d5450042c2e03028071315100ca065590150000c8050050100ca25028088030741500c4500c50b07001c00c45e0064810500d00a60003003e40300007018152806481450004101c04810054055404035680e440702c0d49071424599034048840d074106052040807891444020b00300c0f681d607084 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 918275467 1250 918274217 918274277
    0x142a0603040f170c010506040614010e271504110703080601050306270910060b0403321b091501230418060506070b0412030209090405030306010e0a05010f 68
    0x4003084d41d07150312105400c483d0240009036020450f258980c1c4a18011b85041440c05e40440c40c02200c3d403900303040440032200c03003802c540704078030100342000d6401e000301e04184c0303c00103000003100a80c030765460316200e81c507014141c1c5510145450f08940d005403c482c801001281070000120004089407100450061103900070303446161000c181c450309190401c030a841410301841103030110400c1100520540c4140d500140c02c2900341455640c60b046803101a1035210040c41c6292485000f000c40345903100041c0805801a0030003010038040c0d03003030040c0103a1105114840c5e603400c2c490364012440340e0154594082c0f0300042802164124110a080c04400e5000c0c0c4040c0050001030b420380c02c105c41d0480e445c003640b05020700d59581003003201c40d02900030054581b081d441c000c50001410710400841c2c9503036908000d401d04611600081344c0800484050316a0b4100000300101580c0c00780003d004440704441036641c8030b080c100002e184003400c454003004e10112458240c1c1ca1602c1403852100310030f13 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 918276717 1250 918275467 918275513
    0x90203120d0921090905150a062003090f01050903010b10020c0324012102210c0d030206061e12010903180302010f03020a0c142a0603040f 61
    0x1c5814100340081030415003e40c0c410419030000603400c4820303144078035a01c03459a1541c0e251428800040c5c0209000790280d12106201880c41344191940302c0344400429039a10380400005900d0410f0b04034407158000700c40301c2d410400690342c0c1c2c1da0740c00820f1843c480080c41d289813070b1003a620101b0f004014a031605588910060300c05110240d0014490880240c02d6040d110500800200126030001100344c50f82100c43e414018000310805850550300c820403070154959602454021501c0a8011091a4000313000724a40107410441042018400d000c1640e002e504507031a5240207494a40c054865446101290300007811214148005900309600030802c407001d005180200c0e000703102d105421004104880b17a100284001560741030100d0b44c0684984002d100445c01c224029401020380744140b00001d210800070454074000025405407100040210104405001c1549031880f00c5000034284020107103445502e03103100b942d410552092a824480055280c4406080220741c010b0201e04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 918277967 1250 918276717 918276727
    0x1170312040816120f0201021303020f01050706020f18030d0905120106180c0f111c090801090302010b090603070605190e100f0905010804030503070e011b030909151809020312 77
    0x145007062900d444c0d01c40d85508000b20700c5540d0903801d0380120043c0c44192214080c041000d0304000c1e09101c080001450900d213401980d0b5101402c98200800f5001907201c0401d01c1c2c1807404015144940c1e1038811001000326401c2400010a20205c40c0180c0303000c0c0b5500c80c510307800d40f80250411006000c200c1c4240383c1c120300303801c2c2400042603d52021000200c032200040811070144140b07011041c580c1015200840a105c0011100c6d94003401450410550b8107000034002c100f0701c6038100552081d8004100c1c40321440c01c020281c0000740c1000e01c80d41001e00c00b040050780120482d28905215400000402d0160b541641e15400400e4000c2e0880390034144446030742d41c0b02144044055030303926100000d80c0c96000440d40001304030750040c041001000400e0006000d0301079a0302c3d04205142070070b142c00c40840180c200050691045002c100142c0c030034070161982c2e0145504486a00b00000070f010303d400003503001440d68000204285640b2140101592030070b004070807000d01a911003580d50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 918279217 1250 918277967 918277973
    0xd03110d06090203041a01060906050703020a0b0403020610060302030c04180603050303012405040518040c030507060536060a03090b0c0a0e0f0a09180b070f020601170312040816 78
    0x19504c21142155051000d00755411901901c1003001d05a4486945048440781080000d595560050000b5410741c450707120140002400341c9540ca02c81c038404d034040d140509020100d22541111604000141741c01801042060440f040540d4202e4040e000005008280308501400030404c41d08080c0c030314000000003003441c205004180046d129001e0017134904420485040300d0324004c60050a80c40a1111000c0c101408414101600180181081c41c1001c0e80c2c1d0f5581450300107154010b001103480464541407410540c910003401c203400d45a40250703040c1c080d098030220000310700c3c401d21840340440e00c1e160191080d8440c0c2d003090f034002c07001442c50a20070035050503604508900d100040b000c402c0c560007401c0c60b03a00a1040032000e050061800d0515501da0090001041d4008600c0c2c5803032020b00c049100e40034281e0064640740c882204140c00007030002c0c24010140c00400700350103075120342c040320300d0000111407200988205c10780b0562540d00d841d21440c800c5075044000305211681190078 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 918280467 1250 918279217 918279221
    0x28080d11070c09060f230406301106030c1b0703021e130e0a02060d0c030c080903070b1513050f06040e060a05060d0b090a0308010906080d03110d0609 66
    0x4036801102d80411603030b6185a4841650300034020221150f0004c50100844401c00b074804a007000700003411410141180007280840e11650301042c801d5003042c401c1c104035105d03003400c41c0d104000380050303400c00245038544004c401c81c0d8180050045500000040c1000c403030005982c0f5903114000d1140008240c104070300e55901c114001a03108a402a0300c660f4213500c80040d0700d0b030102018003034105424841408000400000070502c103180120800040140c0e07806005001e84d40056500045080c3c04c3ca1004089410b1065501b09205e101300070b011b11a0f0000054409031075002d000242d240c1e5450218244c51041d0200d10740e040820200c1c603682558031504010300c0b40420440514081c0d80349401c10056800440c598003271600504081f42d203030380842d00041d41c4000c01030040c0c4000303400c5030355107a0504011507820a0030381011050380100756110071002e00505282c0818400c0608013007a460b200e0142518507400d061340c0e003c0103462940003505485030341001c2c0344208450390b9100c2403000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 918281717 1250 918280467 918280477
    0x71107180c09081e0f01020d0615090302010c0f1a181b0d15020906030c04030302060a02070b060d0c0801050907050a0f06051c0207150b030f28080d11 66
    0x504541403140601207540300e08100003c44100400030035210a035002030559854442c41250300780c0c01740c1e452410114030240010301e4640e2540038000f89031440d0a40c0d06009a900ca12a0b0040000e1280100007603a4809610f070340b02c41e003064800d48845124942580011228820542010b0410040000c416182200d202c0111840416215072000e03203007010102c480c5145010f94010401403885003c030b100314510308000140010010f103002003840004505810454030303070680100c006401d004050b0306100d11600030060300030650811600ba45c500c454404028003041c0280d4413002d40c5414840e07000d004030010040d1a001700814285418096200e5011780105800baa00d01316000910804c001102d83c00c480c016900c00713050110140304803c09011070f500381c00200c3c4d004c0c01403802140c1300b150240002c60703503007400117848101031042c981041c0e802c3d1000d244641220745480040c2b6260540701c0e052070540b00030001d5110302c5242c1902113000c1c41385155030851608160907485490640202 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 918282967 1250 918281717 918281759
    0x503180723040c140a1103252105070f050c150c1b0303040e0912390606060c010f0f09050c0a081b04020d05040b04030306080f060f071107 61
    0x402074001c880803e89050740502e10728030000c0e00070002108902d00c15480b46c00700804841c00d032071800210300c0d011009890f4003603580002404120801c030030400e03000d9981400c507200d10f05107a080500704001401a0045007070240800c403910109204100341442442c109200080c044000c1c2c0c2000e00041006400c0150079140310301c0390a01c1010600c600203c1d164130404000c00551405040684c0e008110b803000d4611082c80c0f291180100103010444041c0c041d21030f40c2d01100707407207900e261a80651540d420198402a07550010f483c4103011001ca40b9075807210083d20300640c1c5980e0000c41c640145007110b40c13001031034640031070344c10074244030b0708010700490042044506603a154001c000c1003800a2180d43da080e84030650301d9159280888041c000e01d10002c10060a000304440da050940340c003200d0440f204420b05003000101501442500040d14092000344100b03484050b48994076000500000010207051002403030b03c5204484a5000b00d810200355400b184e078a40f0b40c200d07529071040d070300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 918284217 1250 918282967 918282971
    0x303070e0a120f08341e0f1115070614011401080a050408070803090105060108011a0a0e12150414061e040c15050a030b030d050318072304 61
    0x1244800d103100340089981000d07409400001c01d5460307040b25403150081951407a251005d204080700d04113403000e05890701c9814120a990107103003642c0c030401c464819110261668201c80042440050200d00c00369202082040303101148002408501c908051070b118008009000c0b001c001190304030703004c401c0320403418003c030ba40c841a091a058410041250002c1c4544e40042c0031030000303030070140d08180a400d0711440c0050130303120340000d03610444190384141c2d110000d100d95964000009401050408051245031080c441d80618a00c2000e00c00d508001e512140590195902e1440408040342002154204281940c04c405c80a00440f400d450b0344c119800c802050140c04610706210b1220410424150a00d50f4058140841e0190055940c0610340d907010403081d0048680c19200c50054403044e03110414002c004060361803203001d89010f90040b1036100025601700052741d0b045181008100851f80748940032038500401035003e080100684030120140700d0340b030034501034213040c10349007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 918285467 1250 918284217 918284219
    0xa0c0504021b031306110109030503220b1e15031209030102040513060e010603021306050708070510061a19030504050a0501021602010806061905031522050708010b04060302090a080303070e0a 84
    0x150fa07088510708980900483c40400005ccc04d1402c03440c54614290006200c21084e90140b501c1d10701c1a84001c80c0d45980054000c0600241c0d403100b081440c3e48120080c43c001803903008600826114401e500c8e640c0340d00400031070541e0705071b0303029015200074000242c581003610420082c00d00190803503220b44a008248c0500100b6501d20a0080711000c1610b0020f40c2c412520300107040f00c4ca544040c1c4140d07003040c01401710034002402480010008007a141004c83c000e81410610130085001d071050045a98080046c01000a4241c0301c8581e034480c18180021709941d141040703414030707100130f070002c01d01d520020b8086004880b4604a183c0316000fa40c1d09d621a0b5504000d1040911a58201207088000080000003042c4500c00544c3d0024500181d1100c082c9650003094903003201040e017203a081000c1c81880c500300d1151055035842502441c20421300d502d8101c4400603403003140615000c060300040c0c1548030751110305d5404024101101100d60f01e1034602ca00400788103004ea540c034030078141190 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 918286717 1250 918285467 918285497
    0xd0b15030f0309090a090609230a02030714120a12021c021009021201020c070509160c1205130611010e0d2a0807030f110a0c0504021b031306 62
    0x7141440d00380148011032400c0381600c104601510300070119800e0540f0f413000300e400150300380074444010348030f0302100740e00c1055840400d0401401080c000c8660740316820340380c05070f41d0000301c240c200c2d0446201e400d000d80f500b0000c6140b2160002604126100750506c031410403151740642103044401c0d50949161205802e0005526409070081100680c020b0045496140340380c0c2c0008021440204640b07650094101c007107003a07800c1008a043c0c19045880200b20034180b94900340d0340841c50905903402680e500a02a2001e089080090000d0102d8600429264064000c0311460700130900e4844120356104002002d100440380c3d0305c0e900d9400c04400401c1d81c88009000202201140c0715110301901a0f2048800304a031070001d9080f2003008a400c4020411110050407074500940d01d4443c203a5003240080c0091003003a5003042da9a00403808130002c900c500c2000310545a00701c90245e42e0310100c031540c80305070006007410505400006106441c007018414074404550007a00d5160f048100e00c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 918287967 1250 918286717 918286723
    0x21101503020d17070f110f0d141c0f080a050615070f05030d06031401090804050415090204060c0b010e130308042604050a0915032d11041107031707020c0d0b1503 71
    0x5519641c201d211020032000081d0000160000b449c90041100c01130084498a11100c08041044078082402c40010482d07660b407203101254410b140d60801e0085003414070100c0c091800c103c00c684101d0b0000b1960800b0800c858a0340140a90001c3c101d9841d050381500d040000c2c0349601c41290801c2c104801040c6460060148090341600b0042150500f0329100604c40600303000041d0101a80704d038500410f10109900c06000645510780e2052602492441c000c82100c006030010014045040c04100780740a2060914104580c189031079a0262aa440c0200710820106402c800162440c902c0000901403240504200da40403035104010580d1100007100b1030b054135114202c0c0e144094428400315024918611f07054000b00c0303003409101e400420308106403012000031141410365005c000e0b03003460640501502128008841440d00080d42d4024000d195509210440310401c1c1000850082c02840246880b00c0b014000ca2002c4029180004014004032001d580850250100c0c44c00c0381800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 918289217 1250 918287967 918287989
    0xb09090f060d110f0a150207080f061f0302091305060c0408060606070f0c180c09050102030d0b220207150c2c21101503020d17070f11 59
    0x50310400410700151500780b103c2ca100300c01c440e000950b10494990588841034003c000300300328090708100c83e01d038840003800c0041c1d940c440803d5501040c6080d00c246000304516070003203412010701c020907a4055100c00c00d07240b103501c0070f035201d02036900300000d105880c0340c4028910310480c00e40340346641d40c2605d01d4542c06107008003884c591000001030140d081a0004003516400348201d0041040e155075510241c6c1c4e02c4d0742000034449805041c41c2c52511417801340ca409000f01d030925001c2e8500740b0000039928080c80c001c140e000d98030b4940f681c00548941011401100041fa09942400c01100b00c1501941c000c00c070031140000c011301c42c074604030a903100c1d83d119000d480d6900d004003207600d0a100720300b007403800b015030542c20640f1a10413540d56013404031a100d602131241020b010260f04210741030003c820780300341c41581825075083d001400101200c00392a030480d2481d034120024100030901c048084414205084001403034428001288400c5800710720030300300d180f140c01c441814001c1e90855 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 918290467 1250 918289217 918289219
    0x20f06060613050913020d051b0301050c0d0b04110a020a03091401020a14030c060106080601020d181e081b10091a0702011704030906020706050313081e040b09090f06 73
    0xd42814000f80c0b501c0c40581d90000321841d0301d954811100c0d00040e01c0441555021605075010761806034001e040d0040b06085680220000c000034a03090403008003501c910241001e01c01da6604041200b07544a82c003944118412180d02901c075800190065038480b21184150003060080f40300007105202241d04403401034040c2d002d482c0d01f04207951070781145484542410118007046c07010700c03038422003001014020300340c50390342c0d10103801c1c0000068202089400300e1410040c0784507212513401800041c090444403108454004035200b6204002c5030340c0b060b00700950383c1c000d03010600c0000745c00c0100c11100365070807280c0c80010075400b002501d0042c0140325004401100d2600c094082052f040588070060042c10f180701c0350159040b000303d41501c2250110045810054140f21207035040000001030800d80c24010b203942001450043d1402194500500c000340028181600001c4a20b00074900c031802e14030f850b201c0b41c0394034480b40c4980007114194018400e50000034100d40c403c070365036070003140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 918291717 1250 918290467 918290497
    0x60a080c030c01080c070b0a0f0507020f060103140a15060306180519020406090f14011502071505130308040801050f0103110f0111031c05151003020c0a0210020f060606 74
    0x1040b400107680c1840c0c01402c0821118007440381e81c01280d41c03424100c0c841e0400741300014400483d510004204c03840907104000310762000218401d600b03800650281501d03040b80407000204414281140740c400615801404140b008c04203060351400c0360081c2054030b00c66181401442241010000d0b407500021001d0504c0d4017070316441002c40d0f00c486424003164005040450203640300e80d04d080030788400000f008011603844280c14400039600860b64054040226004d85018a20380001c3d0740e84414050314000b0300e02d04107611549400f500c101c2d0903c404509000c0780300c950385d0900e5445904144110a415402e05001810010f0044000b40c143e0b03600c00b1113503221702121418001c0140c40c0c10f14403030506c100b02c1141c036400320082010b40700c0100e400701c501340c010076644804000d03120b014020341e810004a4102030845c0e40c5441d0030881e060325920b030060304e0b1100e44290a151000d0100c1c00394014002c1e07407400f20026804605031091443c00b0b01101d8480d02c503903050107624030820a140c0e0500e6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 918292967 1250 918291717 918291733
    0x203120c031b0703020d090812120c0d060b0a0315150c030c02041a0f06070317040c1a040e06090907120203031201080f060c09011e210203060a080c03 66
    0x411180c0103990010a10807030028140030904007501d40d540b004105402503401000880c540c1a842010f00000d015558050301003034801c0800d020705400780c0350b003c00800380c0240016240c20318120580c4c2a28240c0102889a00d03a04d45020711160b2124004400003030400c485a031050121100a008952070074021802c150740e20803084841d03514203407040f410862401000e80142e502c4e4059018002a8082d000d6094803040041144000d240d0182d40d0289400344808070209401c100000c040c3c0001c1d00040d82e0603030761031900002d1007940346c104441440083c0c58074030900301024040c2c02a20a440800185074a80c0b4041003a003807030803546407006500880c418455166003a40079a811440982100d081685a410a651140c0c00360400c0699500102400071040c0081080302e8014819180340c600c1c28003800002004c400300300d914025000c00740e0400c06080c0303100d00e400102004605080b401c40401c004400b00c00380d80141da00901c14246928013041c00c5402107000003400f4030040c0106400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 918294217 1250 918292967 918292981
    0x180212010e070212271f050c1014010b031017030306040b030c030a02040e2a031216020402090607200108070e091b071203062105101a1305010e07020312 67
    0x40400171000c0381c0c2000e0445911004a0078980e61510103070b0454407070b40e480704c1190f00e140d450706613009203000649050080010140030760008241c10f483c011130100da036079514540c1045614045da444072407122020701c403031411808044051400303403804503000c4c808960450201a0ba030106642025415040b01c1040d02c01031800d41d11100340e50840909440b4060b04448800b1743c0c036045500c1544088840c4284490a40380a00402400081300804141000c096200c00030a131070500308028041c075400034012800d0b944103401d460740550301082c18044606451600162104400c104a000c1100800405c1c0c002c1c2c003c180d2554125005040c08640359180000c102d000240d01a2854405008221840110794100034070228040325032800706da410f28001c4280d83c41c1c00211442d038000100300302043c000030400b144000101c032040c080800e0f048504030309134041500c140d42a9134400918481e407043ca00340c540000d0304032520194443c0c0103645500041c1d03100d100c0d4142860020039203c0001e002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 918295467 1250 918294217 918294277
    0x3060e010b0705100e1e06100e01080a0312091718150a0e120a0f11030d0e0105031e01090b04050a05040c05150c010c0324030b01180212010e070212 65
    0x1d408558203d40e81c018208100306d015070360502c01130303445070400810001aa6800381c000f030000c04080716020015803500e0216519891003c01c010100403000b80001441c00c0c4603003002e450290400e210800850110500025aa000d9228508100c542089640e81440c084114004000d4015040f034909100e02a04a4803404ea086c0e003140d200300100a0111a101c04001c0030780c600d0b1140a04901c143c4840c14004003845880c0141c600ca50b020f00140d0100980c403210f140310307290b001e080082e01da4480380955510081125402c0c10040c076901d00015842945030003600410b802501e0411080e10b07600c40b280295603046074050400c0030076120410180c1404402c107400c60400e81c20150501da00159010700b035842210090001a45414a50440512240100c1003038000340710840d00a49c60760703a489038441814812090704481ca8418100d07000020340403641a1360343c4a25100c002e68481c40109490304068440d0001881608020b03104204540100c1d6902c2c4035507455058007454401c08005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 918296717 1250 918295467 918295481
    0x5030f090a08030c160807050307060819050c13050f1e060c150103120c0b0708090a0501090c1d150f0d0204020c06061009060909020a030e060703060e010b070510 71
    0x504800a01e0700064524401c1c400b80514084a9000c0d21410b0080e1066403418183ca402012003500064001c110aa500181d4981220f10a040a43d2550307500003000d0404210055045070041c2404100444d550a440007080d1101002d41c500d100e20f0340b02d4003403059204041040c0c9410000c0001411181030700b0070080180240014415484c101d514603000c0c0c02c2c1b0780e08408441c3d840103a4130044c82044104480e58105d200380c2d1400c007500e580d60340c41e00c1d110044090614000c1c81903c0f030108904000c240691600140c01c60020b0050402902d05510541e20b10301c100c002029a10007541c02d2003c0c001c480b64082c42ca449d03000607854441104200b60402541c10007039010400302e08170001030b2201d0000e040c2100320303000038005514108003408680e800c1c2c50501402c000c0002c1043c0041034000418405951000c7e000680b075071300300358050300100540e848032601c9215040c100b240c0a940340c0c11020558031200030030f440c145d0f42c80351031212a005a900003802c94001c10b44014807449258400c003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 918297967 1250 918296717 918296719
    0x9072d0504020d1104060909050a09020d0b0a240e06032113031e03020c040e101a04050f0a0e0c010f030c170a1d0a0b1308040306021206030d0c05030f09 67
    0x11130310781120340612a0340c010390000300800c1c42144100b181d070b843c82c03144940c04800303039100b4807049803a5400150454a180801860701000b000070810b04680e990203400740e031040240a0504101d90400c03900301c0001c80c49400340d14070300310f00007443d14240030402a001650801c44178072003420610030000c582d0001e101d205010090128008003041c82200e545a18458682c1d035510300000360308000303040c1010403445501481c03c02803204410640000c22180c4d15045900c0001ea0901d6a10ba21901102150321241d0090409042c800389040d1028014082d00c042c0c0710400004250102c02034641400c070303400e01d012846000080068901030382001c080c0e82c040381b41400c14250500b41b07003040070308180e0f8002c0e020741c0d036441c0b41e44103c0300a08101912050341c0000b0080540d541e500c44207103400c0240140904401c40130004204a0710380103840281d940310005640315034001c02190103e041c100c60b50382c401c0c482e032512103a503540203003000155950441e001d14a0600c070105094515030114200c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 918299217 1250 918297967 918297971
    0x1d120712020c04021612030c050315040603060504050f07140604170a060606090524042c0a0c0f05121b04030c0312110d050a0e01090e09072d0504020d 66
    0x100e0b507075120320003403038412100419502c095070749042c4103204044030080c0006040c039000c01104401d4200c025258081d42e642c1e2b039a07410140d01c102040250440e075100a0006041070107210420102181540c100780d0741c00f08031201296102040f2601042c271031121904404d040000f40305250060106101e41481d14045034050310036a40d030401285c4d241d90013140000e5241400740030741d10b040c8110502d0f92103013203900790b043e41c07030003648034203d101d2813050740003c4041c98084088a00b500c0c0000c400c4140900d141e0070580342c203500342c40c007401c0c000481500148400c030b2a2403e2601507020b132007001d00f202130b44158540e1643e50700010541d089075000a040c0301400000300140d14480503001541c8210008000038040d0200603080c2d0504500300c1400d0741244800380112940710040e1461806246092040c0e0301040e0300595401d6401d0b00000d9122034a0390030010f210f14002118003c0b140100c070b4140006410706010407510070105040f6103200d16014003004545095009840400d16200c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 918300467 1250 918299217 918299233
    0xf0a0b1609050d060509010c140f0901090f0e09070b0a020303040308061309110a0b040e0a0b0f040207050105060f0609012f0303010806010f0603090f260301091d12071202 75
    0x90f42a40ca103e00840340952030310100a120903003805400881d242c07a04107820000d413003044500545c0240c10701840d9103800031817450516031041d41c1c81d0300101010103800c01c009481e0b42d442d0400801c104c0d04500725100711003002820702800c000301c4040304c4072507000d5402d64446580c1102d003681c0240409511003c201c105c10040034007071007104030991144501e5a440c401e0034081c85880400c540c0081e042c482c05010801c8140c5810420582c03181042c180014000444400079500028080b89a504a0701c0858118100034055100c035000b0041110411002003108040041d5440340c07013440ca00090000380400302001d120390440125184404000880c0011101290719580090f4041e01c5207600510041010412002000d00038042a280a0100081948900c10840b11000f03005113a442d540c0001c2070601c42480c0189480b07035000b5103103070303803540d540c003548011340000c90111000c52052040161301c10000030342d0131498003d03c00160b04012113a12080c1c1c0303070284051400c0542c0a0b482c0f07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 918301717 1250 918300467 918300469
    0x507021023090a080d08010611010f151d041203020a020c04020a0c140f030901141b0106090f18080715050906040b0106021609110f18030f0a0b160905 66
    0x141d0092003005400641d02c411510742000700d52200c0b42c1c00418583c004140d014621603000101034150703039560800609d44030a20445500421441e40140012403a2101440240d580b419151003112030b0242091030a810506680d0040f242c242c8000b00340c2407200c0080c40915000b600a080c5610490060ba200b100e411b4000c0350036a0701100140300050070070040c18041041508040d001c8001c00c0d4014039000d00301c001d0b42540c1c2e1142040490500c500361560004025000045900c3c0b8442d4080c5141a508080e250f40d02a04084c09825040c5041a4124010304441d1188410058a0703a45002d8444c980d511219069032150a00742c507804420654034503a000680262400307103410000070701c45860f01e0f0400750f48207a810b81142003150021007000b40451840c103042000c0d9040c0d1100058107180401c040480e030b11038030780481060bc2e400302d00040b1a1801002e80d00310b244e019026135100c2045180c9054841d942c01030000d010b0040d04000c1414081e0548071250300c101039040800b0030a8482c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 918302967 1250 918301717 918301757
    0x90f2c030717040f0b03070e0f13020a020615010c020105041a04031a1b090f1011010608210306100c0204090b13030e0f0d030c051005010b0703020f03030705070210 72
    0x10360341d4404100d0001e810046070000b01d81402c02002c0c039038400b60a600301480001c04070406409154495620000e000342746130b950100c45810105695400c40d5610240d8601130345070001202ca4020441d68001d100610b54019100c00e9070240c3c1c140e40e030a10b003c1c20f01c007440004010140043d503c00005010100008214a010a41003d103c458a49552901104032072000c0981280404401c00901c00044240c4170042032407a010000c844201c0e648061704003c50b030903003100607001401d40c06c0c1200042c00301404103a00e48142107101c1407c0444000f28080c0c2203900c000d1301c4507900071880d040148401e41c829400c042d0345510080002c40c050b07025840d80a41c0c028141c6441c074030b4456000c2c4035410182c00c4110128640d07004d42d4618059031410000030483c0a08110140c00d00c41c405003081c0c10000b0521a1015a2403030030003c00c601d5859582134142070b000f41c0002ca000d8452481041444600002034074414511075443c2440e0550740ea0a0005500b1605844020320031000300040c00c0314044 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 918304217 1250 918302967 918302993
    0xa03031b051203040b131a0928050618060708180a0c0e09060403090b0c010e0604121202091c060e0709020913050402060a03150f080601090f2c0307 65
    0x1840d161030f03d905040c00e180f898802c0c054101861916008800d0f00002e0703000364880c000710840a01c1004030385c0c0315030085003020804240301c01c1c101d80f040101c011511124480d020040d01842c1105c1450b0743c0c1132001c1c0e44410b4604d284451a900490003e07070807078811341c1c2066000502a41c42150300b44900300140c82d104440b8821100da0b40050000e100007102c86170b80c0c50380001c0620080c8858105078a002d041e1090501542201060004540b581c10509400484110040e2412940c1034900340c240451400c1d20301300010000b1b100c0c0c06070314900d003080b8000d40b40e0012004040c0a0101d00a42c001c044004000b00b04031041a115101d02c104900706001060041043d0000940e50714042d000300b04900c0142038921503c140303480c05120160f20364000391611465281000a42c0b008070142000e4040e0030b0390f100312241c060000002c680c1c00c2010990354104c81c55404280300c080c424003008410f440904103091011100040d0003509900c4041412035554004000d0b6440e1000a0b01c8001d055041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 918305467 1250 918304217 918304243
    0x510021015060813020d0b280b03120c0607231b1c0504030609060902030a11010f0c110103050c04050307090204050f01020c0915041419050907050a03031b05 69
    0x2207207041007100d03000001c40f0343c07011059a030742202c8507291340041c00c0d01405620103445080f2400005a0594091000c1c0b08120050815640d414005407040800307400b210305c4280c000d000b0f0900c81d9085c52040000d0310000c070a680058881c41d2b81d00c010855006c0380d81002192181c2061400020415604000b003080c9204031425000583c2d100c04440d14080000900c03050540c0c0303103040c8400850303205081e80d080e00d52012000c10605420304007500038150400b0040e5040c0604a181c004010b49803d40d80c3c0f4600c02a211f21081e002110300669600605032000741c240000100c46500310340c46584400d078072150b60307c0d4003420a912071022030700d46240d54100d41a801e0b4002070030b11051600d003401665560782403000f4141c0300030800102d00da08402914132181542616800c1c084c559458004020650400c0c0782d080142c64510b003100c0300a0044080400d0403890300021a2600d035001c14098103460300a050307540068a940c2e001c8038a0400c000710340d50280c0f04510801c2c0017480034000c08103c049 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 918306717 1250 918305467 918305501
    0x3121b0618050c1e0405100e0c03071404060c060c09030506160210020a0f0f12020d02040e06040605090610030908030709061d03070b0a05071b14030a0c05100210 71
    0x70750782c0382c03140c9481e0382803200501c911040c80d086151071401c28000c14090506582c045000d49441441101201c62500f000144e000003c00300260784007030402552240c3d01030b03038410b410703840401c14004040c440d0b13005600010360300080c0c1102040c2507422441c4010703500d1826038178032980e030f803500e508001c01510000004100075058548403541001800b1901030b280800b103160005116001e04644030b80d103c00414003003500240f020150080824807041c0041000c10b55485204caa4010003e5005001d04003040318402c0106642e401c040c030500342134071006496040f40b0f407101c408112141c554551100c04154030741c81c4090000d00710201850040400b0b8444500c02c41c10898060180424900c004249526034903a0442c160381c0094940b0403034400018003a540d80d00101c00f210f092041d1100540504820005e00c400134241e40b07801c03000c440124030151b01d103042040405485d10005080a441c0b440300c1d003c02e00582c43c0070700309041003840360b004540200300c04850070820b4138140100504201 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 918307967 1250 918306717 918306761
    0xf1b0816022223010509190f09021f020703081e070f0501060e040b0112150e0c0109060c081206030a14010209041b0512280b0310020403121b06 63
    0x6540b0700580020280c0c200c08030154610f00042104000c4051140c1481400c5007001305142d1807103411b0650b80180840c00c140704503140803802101800d10079908a0007122510100286030080316201008030340c0c242d01805074189151036111154100420904ca500c102c1e02001d00480150f0004208c138a02c41c180c20040c12505007409400c4a505900c490b142d48010b02c10040055544440076064540c84100b02c210719405080240c115040c6c41d048901c03071898141081a02c8c10001490845107100360303560f65415890b103078103e0342145440c00c01011041d060049044000541ca01c003613201c407026007119040b02c1140c98a4000d01d1300c4a0b40000c40ea50b000505811600b0140503030200c400c00d0140c40c040c0e401034450010401d10030106c05695100250010032104441c81c142d00700308184019642d4491010440d100c0000c10000b180c50388a0310907034191812071420303402603904807034100c0200000d40c00b00341d10035600591024903010100800501020000d02c441c0b06072076280c0083d003140341d109 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 918309217 1250 918307967 918308029
    0x610051e0c0304030c0302040f0c0903030507080d05070e040c1e0522060909050f13110d050303010b04090e0c060a0c0609021806030609011103060f1207060503070f1b081602 76
    0x2141710a6500271514108140c0100107a081454001203070351600e041c554550f058209011640114503800312118141414800a158415012568110121020001c012110740e06070384410188000303403e0303002c04014074081d15004401918090b40740070501042c106900920181501c9a80c0118012403102601800350000c1e034810513034840b4034403403601610b0030407403902c044080901000420740072001800e042d042e21703040342504616030b010084a03100c3d6100c8000b011290018020f01d05690320b40852814500400a030015003000c0c013030300b02e903d4000404006c4036130f40320340002640c046072a09407840040c0c684140791204d601c1d540c4903d0b03c00d4240441058144000680300c0840d0780e0402900405103401041143c2d0400800c4803c041890001d20200d1700031801e8580d080c04034041e58000081a50b002001103200318010341d65005c0c0701c1100d200a8a01860b402542001ca045c0d004038080080e8022004103486c2e03001468050000c192540011504405510311104208100a0b07400c48 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 918310467 1250 918309217 918309221
    0x615152a030717030105090a180c03200901050f010f1b05150a0903091e0b030f070f02030c0a0b0612010e0d0207090605181b0406090302090610051e0c0304030c030204 73
    0x1103020f0080806140d54541000200d942c0c001810108142d0f5030307401100b115460400096408c0c941c0020302c0404503540b81043e0301601440781400c5c0240340c0455481407185400c1d403005050314070003000f1783e03003c0307800000440341d00c45407034440c809020020300246503082e1030582d07001c2003521401c02400d01030380e100e94070892400003421360342030582031284100002e0b401c501400143c0740900c85444c141d804410000c1280805980700506141c000002d1002e40307400c94a1117413098046031128010300c2d4903180700300e07541c1c0303d400301d040d1031900200300c0c05001489400c0019006030004100381600304d040081a0301f160307138450340800550310880060007840c0d0184103400023400d81140400c40b0a00d0107020912800d0038a1705102540480340c0001c03041d00b0140f00c3c0001c42004501099201c548990010b0820042c50000b0781c400d0304160005980c1e841d002c2c001112400d03085d9206402c002c064882254200a280c044107000c2d8014882400e81c841c041000e080154010408051001c1c598014001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 918311717 1250 918310467 918310493
    0xe0708100b1c120f031103060d05070b040303030e1605180714190207050307050612040203012309121603080402030a05010e070905130305091c020619020615152a0307 73
    0x20702d0301b801880d20f0006400c2c019a58841d1041d0740382240c1c40c20714035001d810881103400000044ea03001c030b0003000b07140e0301d41c0c170914003c3c074030000b164090654010541042c803000d12510f54072a9a802200500001400016070080380d941440c2c4108030340a5000c4079590021141540c0d00f409030560030ac0200e1b030420084c0c00a00e820f070044e210260a040c08a100c902c516000400d11504040100c0c0c11900c095102c071031504d06800045281c0f41c45102d10380300100701a40c400f481031182c4c0c44241c64035031180781240c00070340c42c08aa2000703d83e0560340c00e840000e0018820b981c1800740d00e8403280801d43c00c0c062141c00441e0341d00a400d80700c0c107168801c006c80c1d2002d040400b510556007100c10002e0741200c100d0f00c40b0b4808035540d40414005000050b5024020500250006004282150b108220040e4400c1a5500d9020348141c2d5840d00d50f8075000d20f45c100d58881d03000e000e0302509248191454018840f6000b01c01c80100d0300c40c4484103860308502100032150746a800040c03844180500360349010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 918312967 1250 918311717 918311747
    0x501140906010e06041514070c0501120b0d060b1c061b0207081015090606030506010311090d06020c0c040203011e0803030103031403131b0303030e0708100b1c12 71
    0x28040f850389101188030f030302070f90240d0b0030030104440d10f030781e100b90041c03092801c00c120344050150355404910306a9254591803168602003a12410480e2080300c02d40034051050b14007070a807011542aa45420010340100c0d86038541010494251064540300001c108021600582002c00c102e04040e000a8028244440d0070045401201c0213104150020480001d20f43c00740002241c402d00884819118403c9a4049891140f6220000030a82c3e0180c0040e84285001d89082210901c200071480580c426004040d0f8001c20f1070b03a0000020304546e000e080001c0130a011115100c4144000c107040343c0c000c0c0c000c1599401440c04c0301150301c0610900801030041140614150352540e84c01500c10505480b050900007400300c0010b09544c202d208440d10b10b5000070120a818405d0240303202200e01c5400190300080c00c040502012502c0040d04404131941d1000800140f40c0c4444c2100003800000007059001c02d030188561031f00100f20031048040c82c01900003400d0301503150009880001740c2c086e84 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 918314217 1250 918312967 918312977
    0x123070308041403160602030a140a0f06060305070f12060b04080a02030601090b03100506030309061903050601030e0c190506040f060e190e040f0b13150603080313080904050114090601 81
    0x550610f10380c0c1060381c05141d071b010001585a0f02c58030304c4400603011402103403880c0646607041080c0030045420480f01501a00010021540c4605045055807400c403410004203a4000e41c0c203400c14841e21000b01c181e800070200240c0c10b9101ca00280c03d561041d0700c40d1582e40d1002c03480304150702c0c3c1400850300510581400300421030903070011a8648856810740107807242c1c0c4100007145510148200e40c0844030041195680d0b1600c18188601c1c2211034002c400002d24180016026501038400c1c0a602810f00c401020031864020800041060103240a14207480b00c000015a0340c85400c0a08080c100d48a01948503d00b00840140349000001845105413400910004024410b800340d4041c2d034803240c000e140e56a03440c02c0000710040c0140c4028400c0520104004084088d400140141481159401d600f00600740d140382c26220180070140a10808001056050700c0014804803810320070049542450502c0c0006000c88400740d003c4811205003d030000c1552601c0b4211941c4080309080c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 918315467 1250 918314217 918314227
    0x5040602070b03130f08070b070c3522080a051204030b0f06010513030b090c011806080711100504020f090f0a0b0103090f1202010e06070206060123070308041403 71
    0x2802044c0345940025101840c030240b2070092058000891b14030790b030040d03400d030124141100e00414000440505843e012003003040fa41125a805480740c0c0301c045452481c68415203140c26465140d48414000d20b0840c20112030b5000b08151401d0290007011108041d00805416003856803c10803c642c1d80c44146108020600014003803080b40c0e600300701d4040445c8002d9464500680b21b0348600e126420140002e548004100504918a030b4462a0004141d030785550b4114010b4841e80074940301c03402c900c55400010b00c4503d1283c0c2060343d00c140c442c641400c0710640310144a00b000b505969012074680c803441008198101411418074424091790300f5040351904109aa01070300010b4101041a61904200341c1242c0c4a43c01460400f07400440b618010042c43c0b51000e031030000d00c10300c60059402c110111a4030030f00880d40502c214450b070083e2046aa4010045610401070a200c403200f038103000c040c03100b045500010f4203940d8401c0d141d842e02170406080031888014204207810b1242d004001b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 918316717 1250 918315467 918315481
    0xc0812030907180621050d030b09010909030c020d03030b010f0c030e0f01090504061d09010903021906021903202d070503070f030306091418071505040602070b03 71
    0x15001040f039640d41e40710441049a00280d4001c0d00d50743d408011622000318101403100e0411542c5009680304008662448808001c15800e0720301e0303001d000e5800310110004102031141034101d000d00600c01c6c50500380400583c0d00044c035401c81114150f0000717544540e032030b4042d60000c90f66290b41105007800d8511042c43e47c0c0050a090101891a001d0340040d45150b440384d014501e0f04c0c0c00f80600410600149444424499203103041c101e940f00ba031029000403c00c064010b1061141060b050340c050f2a41041e600d0581e0601c01032814200c40695080010020101240021041e141800d0343c003c141c110351051695040c10074400d00184254040000c40ca6080090760030140300079401803003400e51004455051828000d583c030160181c080000e07040c0402c0001000c100f4070522a4400f0414031342c50b404020115a00c80d01d942480c1e024000c00b06806000140e48102c480c84201e0485040940f503c0c0c44020650918810b0b002203540824140909a014081c03840607286a545180c19880c01c50 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 918317967 1250 918316717 918316723
    0x330e13090822060e0a0b0a0c140c0f0406080c0d0f080a09080d11060a15030507030f0b010f0b03270f0d110f030d2f030a0506040e060412110a0c08120309 67
    0x845800c0101c8000942c6841250040c03698460480d0042c0e100008a40740000c0a6200cac0400580c0341d02c5010458456a02d034039052152500351822600180544059503050000712280c110701074421072844904000010b05e8040280000c5844c0d64a21040501c2c09010a1400c4045a81c501c24042a00e28400d0f40020000e092540420251004644040340507801001c6489035000980280a140c00c00700c02d000081d4070b1041014815034000300c07183c1ea42c05000c201d2600d18000c0039840c6c42c0c00c1010840c200c00d86456818120039100e000d01141a0302d03100c55140c03c0905894624940007400f8012115030090101541004010007600505012a05d0903841c3d1140b03445004800c1d5440c2c800304a0362450340325140700d82c01c0b210078092614403070b9070079403a03e50000c03201c0b11035190810000600c0b50516008044607071080500a01c5541c0f02c40e50740340030b021406040641040208010909144400c02c020003503107001d40100301d287c60030050207904200c01c0c80240c41c8281d40400c18006052000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 918319217 1250 918317967 918317969
    0xa062112032d1b14040302060930010c050921150109060504150602060411040f0f050919021c0602040f330e13090822060e0a 55
    0x1501d0700141c41190400c804003001440c42c24014000300d00b540b00a00c02d08103a200c040090580201048906406102103d940110403100c000c1007405120801c01810804047e190605000305164030b0964428240b448005603030b042080313a0008440e9044002d0000e1141e01c440c1c4030b80d840e002c0c2ca40480080841d51007010300203400300a45009444003c1c5031000d000114801c0602456540256502c01e00c1101920306030017051710032032408a0b580c606200280720401161100c1c2c028100540c0c840d222104c0f840a04490780382c21a40340c0c9503141c0a084184a60061108a248002002e060008400303107042c4c02c5501c00155034000d031800c0d4000d80d40c2ccc0c49600279043d85040e00c0c000c10310210305d0100080c2c040c56220002c02c04c0c004201180c030028180d10460000811070107502e00c1c009280144441064104080307021442c818140021400c0503680c0c0c10701c1000d050004120401181e0f5010030650003840b100c10300c0d10002031090b411703a000c80159070060000f490072002c02d840d40d600040300d8400c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 918320467 1250 918319217 918319253
    0x12050f0901111c1805031515040905011506090803091c08190c05010f05060f0f190e04021009080c1e18090c09090a290a0621 55
    0x82c0c01103410712400b040000e1070781c840b20740742502904480282d004d002c0c0402403ca07094407440603040850704e400d00240c141120602150762446988030802c6501d250103c1c0c0803a42c0e0402d807180e81c15800b00d107090059441ba0301070116104207180c0b510360003e2507802e0540000c0b01a0b0401c0002001e5035480035202540040e407010000603017807062074401024450200040e8040e0380080c00001e900d42c101000408950041d0002d0000c4204507003464200c400840b8203a50084072403001e842d86003800d24280c402882d010f809604988030000902501d400345520542c001100b2100300070071820a200c9140e09230380181842d408c1103080c015410303160030008206a002d50309001904d440030060f1044115a20b00c094031580d090507041c03402c824100011602c00c81d543c07080414068141c00c084070100e10650603007001d41005d0352181d40c1c0c040200b4900245203a00d8180301d10721031100410f0004240503145c101400541c00e440c0100c00038101030f0240a01600b9a030900701c200c04038055580883e00016 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 918321717 1250 918320467 918320477
    0x30302100b12070b1303170406120902030703030e0d0602031312050705060109180f030e0102011506050f0d02040b030c12010e0c071113090f140708030d0209040902040e01050412050f0901 82
    0x72000b0446011707419650f001416124944110f001c1009500b8001c005441c0f00b95180c1c4c10210319612500f041c1c0c0c204c04d80094066000110400c0440d101396190306240c0f0009144000b481030648514040c4e030020740e050b12202040403040700401c0300c020100062241c2505107130382403908940395603403503060512880e81e0701034580d81d210005500b90409170031001c0d403000010443c2186414000c00e00d070010020103002d0340c40e0034856103c0131091080c81084803555610395207800e104003499a25504203c040501041e020f00000c501c484042002d1403150000302c036110f4a450424505072412041070780840c030703a00010400d02c40b000b1000c00c11074910340e801004d0f607003c06647e403001c01ca910440190807400c00d460450904108030200000c00203941c010700311801403910000025031190860310540115038000c000c030b0000400301d9009005d44036402840061580060780110741a943e0521070a10701c0e941d110108802c00410510000341c1d08201d261860401c560303081014014416051603605000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 918322967 1250 918321717 918321727
    0x243201050117010e0c0d0f0f1a06043b1b0a1d0a08190501050c09010c021e062a011109010315031a071b050c0d050f0601030302100b12070b 61
    0xb070f40d8502200d0001034006c0d8200704280e03e9110aa0041c1030f04002c60a0007130402006120401030844c0c0050b942c88014580c505e800d24008000c10044403a50a04070310340130202c5812455010784c164003560000c0e002500e040c3d07161100041c0510340b0840040e10107890300344654810b003648118512185d05201c07140026842c00c110010b038445102d0351010440f8480d06012419000b9044240d0501d548100001d02c000d07211441014080c4c0100c40e80f06000880001e001c5e80980f070581152012502c0c2c3c40e541d03c2d0003d4000000c204668400c01c100701107080f15002103c454100e044840300e540840c60001c005d500c0807030900b01c516120348088681096103e0701c603030441d500302800a60040d80c0c040c41c3c840e00c514942d11940304131441103031581c012440d403484040d111844076000260b402e80c840040c103003541c100d40403c11169203c20065a6a1080608055070302d00d00700802400f0710300a070003c0a40743c803881042c0c010b885e40d2101e03060191070140c2d500d41c503802d00080c00800341c801381c001040c8c5131 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 918324217 1250 918322967 918322981
    0x403030807050f0c06180f1c03150b190e0103090b04030815040603050a03030507180909030507020d0606090509150f150a0e07030b0d243201050117010e 67
    0xd0141c0c001c035a07130500401061010700c0f551111340d802103083c0319040c2d0700000302c50b5041c1c984442446401100e5604280c00c1e05956902c20707030010f06092141d070408019031341c49102a41880d0056543d00e030312415402c4140180755080b0300140d83c50712003444c0a0181030550b6548131024000a00b005040c01060000300d0f00c212010300d140040240054002c001c096a01d04025030380d9200306009070040791400c4d0129112500c070700d888800300c04070b136044103581d145000440d80082801d030300180c04000d0180300e400016a50030100b0008503018401c0440e13084e041900c0c540840700c02034002c1b04c80340c0c440b2070800b0060a0301029254400b08020482e002642d60700104c6520780201200b20340e101300c030042c010881024900781140a0811075070704000da014400244000c4001803034020f030120720080800240030b504c0341070f285e101001c0404040b40440c0d0f4019907a120114041c900040c2195440881030f0030490f10f10000e006100074648116011004075080e0301010060146d24000c032070001c000350b51 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 918325467 1250 918324217 918324247
    0x60b19180e07150903020a060314040f020a15050324010e010e03010e0a03020a03020c01020303040f08090a0f0f17010c0806091008030403080408011503080a05070c0801061d0c040303080705 83
    0x201070480f0070040010884900034070344000740c081244140070502c07000c01c08a00c40d101d40700d0003104c2485200030b0303500d603030302e81c1401400e04200803640200302080205109c040542400c030004c4050310354603141d00300700d0b0425260408239150072001525131000c46a0726170707009502005000f020300f407040f5040b4440002c607001d0103459120305600d01c688003804081650005196a400c0c0c0a03500340c0c1d25039007191004980380c0c070081e01d01502a0011100b100c010400c50300091040340c5008005034415a500c0c02c0b032115100043e400300210400d40c0c0820044408501e45041b64100103000130080404420006480d410b405407143d400380304000d0020300e0144500c4810005458048100c0c1d4849a480c0350001090f400f50040821550906903103404d81d000b030341100400c1e654400191350400d80070a0b002c0b90b084c0c0182c03009032601c02d4440c00004a08801707104140107817003d8400296080382d0b05d0640c400100c4003a040d5901c0c0c840400080004c0ba074003024140d00310310b180c0781c140d961740c1c8110304181d5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 918326717 1250 918325467 918325469
    0x21050a1202190e01110a0b010e0a0b1011070807030b0406050606040b0d0501030c172a181b0c0309010e042703090506040605091318060b19180e07 64
    0x4054160b81140d201c0c915004806101034207000d81e20f40d0a141403100c03007581c48814200c070042c107000e007003001400000b07507180e400c650200c01c0c9440042c00c45103400c000f42074088205015170201e00c2d54402c407040c40038203002ca14043e0403680d0080401d94519520102095401400580071035561030203d5090766810782100d0051404140e580e40340c40c2115040300c001d020030702c0300700da01e00140b0302c0c0000c01e032000300c88000c00301d001c80c0054032651108a0a8101042081d0f60a074142c201c20462511180c0c0c5400c12540e0480901000e280d45280c2115801c443c1c040700c4003151075040081c00100740080d0000101c3e01d01800a281130f1130824512004a03000d01b100301c84205080303940a90018095030304d0558005140d000342c2d24800410b41d260240301151059000300c0c00001c0c0704109891050810101031040f82a41500000c1c103203820025140c28195070102c11a010398869829404c41d00e0030310042c1602811000d82881d40301c0c900108900d07440c1211020100e803030b40380c508180c0c00d0a0140f1140c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 918327967 1250 918326717 918326737
    0x15010e0c040e0a021e0d0b0f0a03020f1018091e0209030304120303060509190b010e0d141606110d09120308102115150501050c030d140421050a1202 65
    0x10b4458007442c00d80001f0303180703a0268601031610b000019120b89040303284441100e8018010500c0a04250107011542c580e9410707240c2031080da04c914040d02e0201840000042c101a60001082301310303091180c0b8001c0b81042881022401440070968642d0003004640440d03102e840c403c0c188489900c0c1c25000341000e9440b542c2d00503042c03010031500d100311080c11030300c41d00309900410020b0769803001503400109061016800009410402c400140f4030f00781500700060103002c8074903280820202c2e02070300041d0382261002032041c0d8000b2640510821200408041c281050340115080c00c80d655454186850003400b040001d101203a0191f034a00399600c0035021542035007100000245900a0404038100700702e450500c1d0340d250f080501d0041c400c58002a10495101e007045203864011241900108641c01e071078001003100310802c10343c51298001107039a03290071034024941802d1160303504001801c03042c1a410f5008060041c02d85c08003c46d018910903082c684149c41010710f040009000c1e401c004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 918329217 1250 918327967 918328027
    0x5030f19060603061805010b0f07080c0d03020903071413050c070c0605032706010b0a1b110f061810051b031b0d120908070515010e0c040e0a02 63
    0x10a203a0f5140c1c1003003060340c0020f5006100e91204081d000102e81d400d1103040d00d98107081c4129611461a08002d0403918010708400f8100304a920b040c03824000029500004240d0002d0b510107241001d000c0c4200030544814501258540c580100b030030940400c02d2280394594800001d1010407000041d904001d41002c0c203034480c2a241d0700d000d0031035417060b202d04040d1800180030440c28442c08402484500640024280300c0e483c05001541d581c204c56414400d1201c00a114200c00f100940c010300018000c0e0303454514888440140010f1060f0203c51900412003081440d5803174158820582c0e58040641e40303910701ca21a0241110140035126040404071455041010345500000207400c100100b51a1030b500103c0104005581c0e0709101b60764004a55035542c1c00c84000740551051007050300a2142518001c401d40d5100d0030188884800301c0d40411500040c003610407600c20042e4806540201d03540b07003508003443d0400100c0010140741c0002c1d0001441c0c004003c00111640340c1200841e60 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 918330467 1250 918329217 918329219
    0xa180f03030e010506060c0307110303040b07050601030215090306060d0213090b011404021e07030903121d0307080a1b080106060801090c050315060c07030c12020a0801090305030f1906 81
    0x100801605042c1908401c80d030034800842c1e0307580340040499500e1600341d00214a0008075981e03a40f0030300080400154540814400000c0540c2001700614050744a200544543c2d0f05602c100180850524121080c001d0207228450180d18001006900080c2c111680194000780780700003070390114094002105181011641000c00401c041018180c4107034604044236651510b041c031049004003000b01c20741c0181c0c00c20180034009a98002d24681e4000d00c2c0c0044d8054503911aa40d035143c58107981350000b403003044d0030707120488103843d040c545800c101e01a00c2164a4051120f0341c601c1c0c03000d000780c210511103001d58050088684288010315000c002800340d160f5604014000c41824482c204c9407900b40500801c0399031040c01100d2180c11040280034101c0402014801290800c1aa01c8591300c1240f0000c00410000503000004000801491160300710510502c0101c1c48191701c800c1607603045c00c5403440000d8005095a60000f091038a060782c1d40d035020190072000c00d02d69640d201e61803500d90 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 918331717 1250 918330467 918330473
    0x103230a05030c07030201110a0b0f0c04030f1518170a020a05070611240a0e0c2808070312110a0c182a050a0324030203060c030f0a180f 60
    0x1308074088078000d0700c5114019102d91070064071415004030007450071281c000061143c1107502050354200e5413410b859428180c50340e07590504485501c10079501807194008800c1c0c3e03210240190401c0448400820f40c2643c2c40743d80b82841010108020260400d02043c0750b05070324820403410b40419000400c4034a800e07582e01001e13285290142c980c401c40c0c0280006211803035610ba0300303c40070a101c4251010203035140c0080100030031800c5100ca40d035015658030100c180d41c4540c0708240040b21240c42400c0c03041c1070f0300e070800420103503407102800b80c02454082020070202e41c40c00c8e401c860035040020740344044007651400d18400107c02008510310000208040f070740c2104040810341e00d0f1404004841000044c055000c51802c600240380081c00d0003215094482c001901183c186800c0104d0b40d4071010b54035410500e480442a01458503a80b820419464108019a00a04c0000e666407550a0040700d0003004440141080c0b81c0c03640306c001c600b041c2281a8203c94109030010001d1104032101c0c6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 918332967 1250 918331717 918331723
    0x30201211104030b01060c0f0204050612030a081006020a0302100b0d020a170d0e0906121e0f120313031d0d05011505090105030a0219051c0c09050103230a05030c 71
    0x10005a1300e5504079400860300c9800346030284080761b001540e0fa00f542c030b195402c00c0050302000f00300700d40207051140040a025010000b400c00c40c00b494407814031031b00d000c003020380703055100380d01c52402c40d4040a41305c00030030780200b050f0811460f03c04007c2040d0f481e107000700ea06903e01e080001d4010a8010300041c90000d1a51903180b81d40c83d440540e00d000964000c1100e02100a8110a90044030000881c01d1854812003504080d0b400c50309441030f01a0980c9440d0107100801140b4400384c102d00b5024035141814082015240e90040180741181014101c00c0f003801448240201403140b401507108848040d42c02070141058000c01d01f00d130041c810f160041c040c01000140d55610303001600003261078176110707040304d044e508094004e1200c41e420341c00308000380c00b001000004406503030002040c01d45458145000c3c55480c40d08180d940d4005140c0141c0c52259503100c1c1c0e1840c0e140100500018034017640440c0300300e42076180440c581c50394030034950070488080b0b4005d01c24400007400c012100008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 918334217 1250 918332967 918332969
    0x4080706121401090906090602130e0c07030f051b0d05070b06030a1502250305030702070e24030f011a03010c03020f030c0703021e010f0f020c07030201211104 70
    0x2503a800e2000d000303000700c1d48140d80c1c00400d510081d01c405401440764900d560301498699016000110389401070740c0b40e0400300d1b0b20031105903062000c400403e200d01d2081c4049250081020b2105c6072800000c2d45004001c8140429108200032001038005015084c210001c4200c1c141d040a892541d071540401400c164420a01190558111400544149030102d145200160008921441580c0141641c1d0080d4000390240148551121552040c071845100c04500703541700745c4501c1c0d52810517607001b034030b4600035070310140110640608003c648408502000c041194031914040150520350000b400d2003140714202a4561030084030b41980d01c1341c0200718040100980c004c202090030301e40b081301079208890000381c2d001c10800120f194800c41c0f0700184105802841039400400580e8945031021700e40112840349613444000c09103080e0302520030400b05121007541140343c030300302c5000d158840701140301c00f034107109040c0b191540280c407041c58207440d124440c034108040c0809000000242d001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 918335467 1250 918334217 918334229
    0x30c030d050c0c0627210a090f0e01051804050a0803131a0103110109060c020d0212060106020105040506060406061205071101090c0e0f04080403080c100908070506090d09210206040807 81
    0x1481c01781602c2000104542201401071028004070041c2803201c03801301d9101031103c504100b0320410008900700b50524110182c03501030310111407075142c10208034420340118000860341200c041030100050703001035981c0c492039000b81950b07142d668104084d211030125907809040b0f540b8104950480c484900c007024181c070321503100c2344940c22a0f040110340300841405044041007111010f20050326007441c51440d8288001c100f103214030045410341d41840380a903c400c0250f07445030103200800030300744009540719600340c03810401c15207070100080140320780401c21000299540041102a4464021203e40440000007032000c1d13482403a041c140d0306254412520b80c8440700c8080b03200c00d154a000c180c041c6401c1101c140c00c00e42141c035800590b600281c1d00704594401c80b003070480100918001e01100a0042403540e4584019040040c1002d20040030140c41c0d420200d422800203410820540a40d0013100c9203921054a0180600540d0540034010358800008500010700740350003c2d1b14400d99003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 918336717 1250 918335467 918335521
    0x51b042d0e0618010602070e10051203121509060105031305192904080c0106051905090f0105060a050c0109080d1d0f03090d060b040e01020a090602030c030d050c0c06 73
    0x101c40808501288280114030044e0481c0c4010458483e030223038100e0b04000100b4610b8041070b070310310019844805001d004905500003044005c4184011840c40341d002e0200c85880c030b40700400c031000a0003003200601075030500c42e011020480002030401c4001300c0d543d10900300d0b0225120f1171030440c11078105110885450540c102d0000802140102000c001d1000d96000c501c0381c1c544c4e68030f010140e08a20050f803015075850100194640e55a45441040d96401101004076414001031020382c82000700481d4111410307600400031920f8180440c3c100c09150302c0c0140d01e8483c00c0ea4094050425280054101d0001084415030124960b111422a01d040d8680034403051200d605c054880c100b5407071040064009004281c120300340701d0018454030b8416040004c144000200180880d8545940010b5580d800310381141d22580101820014104c940000c505200780c0d01d20341c9542c0e01c80d541004c2d54464407080452000c200c1e031425607014808840030343d40d40303280405034115102125164505070030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 918337967 1250 918336717 918336739
    0xe07031e0e0c06090901061b1e030e0d02030c0402030c040909060e010e07030c0605031b03250c0c170a020607060207110a0e0a0e0304051c06051b042d0e06 68
    0x880d0032021204c801601401d041640d030b1130304c942501c07100988590305628411a00002c80090b203100300912141e4064400191580041d06006040c1082c3e0303a070290080d40310401c80c20150360300185d01c41c140142241d01690720b03038903983c2a9103240a294840c40007141010240010441241c00650000c580b010013002005811040c5507503c080034031000d401140e9044082c000030380b02e04002e5a01070110b04140030220050300480c1d807154400c84444804541070301c1400310a4600252180e14100a4504a410081c032a100c1c41c00004242c0700700c888070b402010780120492028030002c1440c5e80c006021607140d4401c1e0415201a41c803803c1c2c1112051002180307036005103003002404090f60a4200b6100706030356914141c3c0c0052400c2c02c101a6103200503c80015070b1341d2000d20000c2091040c0c0c0144100d490240390001c16540d0103006203001d0707842a207100355264611420703501143c0002808000c3c8100c000355004c4841e0030400351480d0f00c10a107002003800030b6802c0800740101e50a6440c40009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 918339217 1250 918337967 918337969
    0x21201111c090b0a050703020412030203071202030a021e0c09100e01080318010e0d0b100e0c2809090f060627050f0619020c011103130e07031e0e0c 65
    0xb2401c00c04014890303100c11012421201041d84030503448040c0f820b0040c5000d803035482441c0708401c842d904800690001a000c0100010010645086000d034002103082809584002e5260340342064182e020a414240705001427100300000f000c03120300548142c40c9804c00404e1f01985001502901040007200d40c000611480d0010031100a10443e410042000d00e00400440e600c500d044c03181a40504403404400106042d000741c940602c1000706034994040c50116001c4051f10000c1010307021217002e1100e42c40c01007600300b100d6000030306500782c01c0b084200c0d54401c0d1101c07003880d000300680382d281459404041d052507101100b606c6058803072052181c07600c4078030700da0350b084120254a01030f00f001040150b401c2130b00110b00c20310f40c024502d504005400340450b0311124a0301c2201c3c01644003045020346035801c0f0030703004e07081481070000e0340c81d2403200b035141c514110381446040c2c110032074000059440d80c440c3e44032844103046015100d964800302c007003c101809140c2c5160351280070350301c0f00d0441 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 918340467 1250 918339217 918339221
    0x204031b060915021203060613060302030a0b010201090c06030e120f040f090911090606040306020c0a0317040503071115070609060605040209030606060d0e0312090d1103090d021201111c 82
    0x141c50402d6005044517284c901424041782c0020748000e4014509020255031160111111030140642e0b44e40145c9a1134603041c2102a40c900800d05415640342030201d401007480702c11810161411410007141340000321a186103404090103030310b65404000710b00b4001220802d8000c108031080101c0382d1540c0307601d60441030200e403151a001881d100f030052a40f1502d003850468180d004500030100790616a5070b40b0758a0176607010346500005900008000340c20903811106d012603000410f80c034594680f610f51384490b564030a03014094841508401c451200d99280444c1084003405c4040150721603240d4a06040a4076030030300f040300d005003400d5005c20386080a10944401e9400100240256100c0c00d0507c14280d000400e00b00c0c00c603496080780081c1c04e001300020180c4d082e40d26803004091900050407406c00400075200070070449005034112007003e002068a8a20800302c030b0001c4250511310000703c1d290012440304c40d65500304103c5186042003940600099440407590311120b0b000f000d080c4007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 918341717 1250 918340467 918340499
    0x50a0e0403020304170642040204080307080c0d1110051308070b0901060b13030b040503040f0b04090b06070c270f0e060c09030607080a0f0501030b010303110106060e12010204031b0609 81
    0xf00304c80409800481f030b006222424554000303800149001c2d1601c0e991400e640c0107000603205407000050a40e107c00303080110000303001c80c518090143d02440c07840c858a450743c0c104a00d5000d42c5810104c0c40c8504480da850300d685070720451081c0d4811140c0340001030300703c0885004815520700200019681e00c110100c420741c0c2410350462624a0440d5550b4a40c54401740c400c0d591440244804900f05800d041c1c1000030707118a52007581c45901d0002d04400f961141440076004603c180703e01d80c0000c4210641c0400c2d114150130749144950005c6100c48144426066400d03900e050240203103002d072140d0300600c0001002010380d181540c43c095000349512400190700c1d055030182000441c43c031b10500d0211303013103402e4460100c2c50540641900c010740341c00307030002d03150340c030b01d04004104040c1c002c5c4601c400340d4008030090001c00d01c0d00501a20410340f240b000c9020303038a0100500a460720a40c1101e020b15804140060051948200196440891300505000c03c80459004c14501c070758484400d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 918342967 1250 918341717 918341791
    0x90c0f020f031c0b370b0409020906070209040c17070f060813080c0615011b02040e030f0c01050103020a0506030c040b071104020a1d040204050a0e04030203041706 72
    0x1515002101c000f090442c071200c8184201159a50f440050564805c0160a83c3d404105200036004552940c0c10106103607180060f0481906030204014a880385000d450440741d24020050300d41c1c0c4030b800454510b10461400070350211501c0100703c100501d9001c0f43e4107440b080081092540c84904100b40d0326034040c000d504020120800c00c1200f00d11422803191700030085264030036044003956400ca400e4110000745c820941198007049a000040500c400c4288800d1a002c1c0c2030351001c4005040e4105c1d0402c000e40250303115181202c0440c2d082003140d01c0000100519540e80c0c0f40020030600070003003800100d01c194110a00000c0d14038000301628000e032801d00c00e0502d8a031501c0800b007d07a52040004980044800045104540c0e45202400c000801034603098213800d8020910720328481c24a50040c171462045c0002d009a4642205c043d0645480c03541085540e11541000d82c514050b41c2c2c024480b0318002d01c0c08160403840450194003444200748550391007841c1c0c04034a071a09007011000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 918344217 1250 918342967 918342973
    0x21210052d04060c090b0403211b021219060204030b090a0b07030e19030315080304080c060d020c07081e0a0f0b042409230d050d15090c0f020f 63
    0x204000c10034a03440b059002c413071410410348a655903540c0200e150066401600c40f0803190207031a400e0032503c10985001e00641c9007a007566081c2c242e503004100c0042402074090241c090681602440800020540303903d0308007014269055481c040010390f00602044a21f2040034021620701000003844004030f03a4480c0b43c0c2e5007540d035601c4040f001031003581c6011406114000c050041c2c508601c05495645000c4e65010401c400f41280a400050741648903c075690310030001004841c8002c00c42e01d001e07241c104d07107159903480d803040307001e02a001c1c40f0081d65150180340d500040c00c7e640050341983c08007058500c502c4003018001c1031038039080e9908001d40340f00da03202d005e00700281142d00b0596100b4401d11054a00031401c0c944268001181d056001d00c80759158901024804829406045001b0b01c500001d00e501007680c80d0b03601d0381c5c5841000310900c81c1c04504c981146840b0380040311101d030402c441400c2d00350b55403c05400b074070720040c40710049403500c0c0100907a01e2012818542400c1c440c001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 918345323 1106 918344217 918344221
    0xb070c060b01020a081b0a02060a02010b031509030d1d0d020c010207120507091524080c0a0c02300f010e150112021210052d 55
    0x1c141e05640c02112804001317015003044500492072003c103020110f511842c110f103003c0c421103001703500c6040450442d1200d98150b004810540d400c0301101e80290000c680400c0c916810307902c50480d50001c10500008050780d40002c41e40c4803440100c0114903000207244c904180c180007407a00140c100341144442c43d0790412040000d0711000812458404541c0e480c40d903990207502c2100c03406c948a0356007105520015001c40020217a840991003040e02c10300104040501401200d0003048015010820400c111402d0311a500c9554039061004001c03034081202d0003016500303925054103800c14400b590602c002000c515604640000d200e00d49100305480d0070f4034608140e6a506910400f200d225090b00c0a40c00d0381141e5618048948424803030001c2112904c0801c0c1c1c0c4005485a5480306900032101c1d1701017403213030305030b40c15a041d46448105512800c08589016040414000f00 = true := by decide +kernel

theorem cover : BRFrame.Cov 918165467 918345323 := by
  have h0 := BRFrame.cov_init 918165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 918165467 ≤ n) (h2 : n < 918345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
