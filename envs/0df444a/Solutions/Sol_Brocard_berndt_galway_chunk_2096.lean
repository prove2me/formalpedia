-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2096
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:38:39.991922+00:00
-- url     : https://prove2.me/submissions/bec83ce3-ace2-48df-976f-1a28b3fb2723

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 376798561 ≤ n < 376978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 376799811 1250 376798561 376798589
    0x3190c031a060a09020d0902130e010506060406050f09040617060711070b09061602060304050a0c170606150d15080d03020702032806020c010c0212180609040e070f060306 75
    0x1841d81c03039039440004c0e00c01010005030369a488000f0b0000800392000029080f01c002e104031038a45100780d110140141c0b00740300030311480e40d900042254511441c018900414428401545e0b07800c003420182c081b4040191000603850b44490b0003094000800c00c41c0c900c682d01980030441d990ba0300856103240e10503146e004002c240d040901080c0301b0702804000354052680415880c1402060040e01003a207038002d800c840e90781c10541071903600c8a00304c2c1000e503200350a04800244030b044207034903980026820400b60a03180ca4107020484880d03a5221400402d038010300c440340c40e1035100d2080c5045130b0292519000b04c14a00385d450303410007246400c0702c0103061041c401c2c00c016890106270000c0902450985240c042040c10442440e1003060700043c000a2002c100744005900543c4aa025240d0725021102c0710b5403408400ca1552155400403290054540000c1c00356041280240103a0340d001070010034140500c031840c503d030500c01c0d80410303400300980c0010455142c146c85014080e00c0b2680030590 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 376801061 1250 376799811 376799821
    0x30127020307060929090616060c0c08030c0309010b0603070e0316080d14041505070b10210f02120607170f07050702130c0509120a170903190c031a 65
    0xf0342c2c13a00c0490010282c071214003440c0341100c641250f00b803030b4004150945070040c4098241c0300311102c0e0400c03100e441c0b408041c0c01802d805214081092f0fa400321400b461555540043c1040b81c102500b81102503407580104551550707a03002540c441c40c42a541d500c00700c0303205001c0503d41440010030102c00300c1482418000c039078021a501c07482e0280c41c2080701d00c080310b40400440a100d41c0d400004408030204040b08180e42c484001d1a4143c000e40005840e40c5a00c0000b840041261150035883c00c9000f0405003408032607204100f21364018211000c50b50300c0c03500464894a110445002282c0200c410008440e0b0403031407242b1450a1a01d5403152454810107a4040150280c00a8240680814031100710741c0d90282c0341c0d660031400f41c800d00c4110034803c0b02a105400c001905440f4070a8030003c040f9075a00000e50002640e000b940c40c1c4000d82040d401c55069034000c0c128141c06018481030030030300406200078039800d1841040c0c0296010f1450805450281c04681d8403811459880b007480 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 376802311 1250 376801061 376801079
    0xc13020c240a02071707030315090213050405070909060f030308012705041e0501050f060303090303031b040e090f10060302011706060d0f091203050603060c03060301270203070609 79
    0x60b80c00500001d0069407040181002d076060903c41149030000407001500b00c00f05603158100e900303132094800c00d05040c0c1c0d0b02e48079108140c0c02845881c10410b070160104000c2850181c1125422079550300b8080417091b00d134042c910680d041c5400851950301c011204208042c4d01401503401030106040da4011007204c081240303404000e00e41004111600d07407000c141442540d90816040022045c04100c450b0003a02c0c105000e450700700e424a03601c0e00107400160301410b0100403105240310050140d4030b92765414154041d00025408080d010000601012440c03a010b110303d20b0081001d034009200120303200c900186080040f60405950f14100201040141d800500c1c60850796207144444581c4d50760540801c91500030308082003201800d0051500702014a40d10104515000302203034001001315590550907504280d480315050b51110000915010148025680064006002081500000c01c01400315145401c0c0d00e1000b002c400c00341001c500e01001803500a00550919441540c605000d003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 376803561 1250 376802311 376802383
    0x1d0f0601030c0b072906120303060d0b0a0b0d03020708010506010302040b09010807021204300c181509230906070309020f0405040305121f03140c13020c 67
    0x214082c3d101203000410880e1800510300f41c0c11228141c0c1003031545140d14404014010341d900c901807641a03180380280040072048074031036000549118034211495480b08000d001c0100845040c1c0d507104500380c201d80d6680c60701e1804e85c1c000c0e80102845030400180600310358015111505161041008018a58074071041d10082d40342400d02c10040e80d1001016800c110380d200001902c1c01e00040d010035108040d01501d54010029000042d0880f00c4407108152141c07114030140070040800c0041100b0802501030035501e1300c0300708010034900e1342040000b0001349150040321b001c588819446031a00c041040540000c841c650700741d001070a11584082e15146c000e03000b40109030b00e40f201301c000c1d92034180508540c0c0c08060800c101d01c0ca07080c20000c00326040604410b1300300c00d5603004034500d0300340411a07100701c1041c412480d101c640755643c0c011074100710b560155524020168500d050395562031051107051800a00903996891451105017402e01402c01c41c01000782ea24503036504112640d2103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 376804811 1250 376803561 376803569
    0xa02010507030512091b0108101401021507021f0b010c110103200403050d05040f060e04060b0a0207030c12150b040b09160e1c060c0302040503011d0f0601030c 70
    0x8000d41e5040030b420100c6107842081040c0e00f5035130b0001c090014012000808042070a4200900210204100c2c01101c0107113055a807142c0c40101410144580016a44001d29401c0140112003003000245070300c0b40d2681c0116040310143e0030041210002c91001c0c1c0b4030181360304644508212500d03d0b40000780001d1940f10001d00840c181016400c40c0740d000b07501203401804020345440700e039403204040848540c094042120540180c0d1215000c15024205840035600e42901100d01142019003c0354445019030401d944903031103500004800c1140e0000340390011141d4080e080701d504509100290980c0c0b40e004100e1517400e05551808900c040c591090344182c818800304803680307a900010050008641100e034003809480500c0805d803144050a056101103480b190300403200c00c020800301c20941081c07c0280aa000154000035800f0f50146800d22110b0400500740707a16500400d0071101200e6610401070704140c40b03c460f40380704101d8a0240340115005014039811640d9a80b441181841 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 376806061 1250 376804811 376804817
    0x9050312120f06010909090803040c1703030118090b09010506150a050a050f120108030715090f08090102010608060c070b0a0506010c030507081903021b0106050306060f030f0a050303040b0108060402030a0201 91
    0x700c3d410760310902595005049504041c04690010b0808403560343c001d48044440342d1a80e0f074000380b1070300c0540e05005600f1f054400b960841e0320b0f0070130020f071010908004d401565a5040c60b01d0010360580c01c0540100109800000c07107240c01030500146101c2c0c2a66070118010a108020350f0300e070301408a511001e030303030303d800c0380c69503044c044494850098510749007520780520300105c1c1c20364000000e449041d0207007030002d442e03d4042000904591070721001400050741d850310300c0c02041080c0001e0420040c18800082d0955440d52064140401a941001001c00014102c024081104512034120105000411135818000c002910760340030010003d06200001c102c58007400740c5001619858113260802c1c183c80e1040000c020002e500800040002d035403001403034008072070140302d603100707503107014000340700f9510341c4400c103c050a4052607a940c18450512824070035401030100343c04a0b44140015901d81c1480d1411326a4404140c01094450b4042002c000144e94001083d4204a80a003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 376807311 1250 376806061 376806091
    0xc0f0105150d03120c020f070918030503270706171003170f0a02060601030e0102070309050f0409061a0306090a03050f031509040302070e0c1305100509100905031212 73
    0xf160a807102e084c0456031042c01032030501000d95481c0c02042411403542484290794004d40c4039264038040f150402408021a01c610080000080c094002940c000b406040d0981d07a071404191807420100c14047e100c00c0c00c0d003202c402040241c0c0c0040090f0050240c003d000718032480d180c101100c1e0070000e840040c180484070a4031041041c42501100e00004000b0751a0366a1081290041d685a00540b2114000780c900414600340c04410300c00c0e120290b515503a03812001d8038050420040380034040015074469696004a4002403503845002003e0b41c90303001011481d00c0c0d00d4105401d000000300504a19048440220002540141102c1484070a012443c1d00c0703442c0d1076a65030900c600190042d8100c10b001c03040c07005041c1c0009184c01159a20340182e46260f0754000201007500403005200018804000b09210500c0c1c080007500100c1d0369450000c1c100707000d90002641c0e03155605e01400100b11a140d0501c49801d0a000541e4044034070910f46e4500001010f015640300702c0100700c0d2416402803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 376808561 1250 376807311 376807313
    0xc060b150322020907030911120d030507051303050a0b09070614221215020c0304030611070501050f0103050609190303021813020406080609040c060f02210c0f0105150d 74
    0x10404580c105900900341551521701300c00c000e401400c5c080c109403a403208401c09844030340750020400c14010041300150070152810481030f000b92070080c0c400010312909000000314072410030060401076014800030012228141807949816601038030852203500190424084107070000410600e40c00508801c554a5840d034500283d400f02c2c40c003504075074500090300014a100b6400351074081a0140707110021110001c0000f600300c0c8100c2c8000c0a068006000800200c0c50541c0111004088100450305d049425030300c040c02c4680841e444a40b030801e950041c0144481040134690246035903004201a50304000700c240903583e0488020101070700003c0001d950401159603e03684030020301007103a03400390000c1c00c40c06501305015000c0000c810b030000641d50b242c01050390b80510340092422440c81e052500c100e41c11406410010154400c0036500b200401c3c541c0c11035030600d1091185a40c0b2041101e85403414114005103510041e03061100780319003040c0081d158440140e040f03c0c41c4038200342c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 376809811 1250 376808561 376808611
    0xd0f150b19030e03070803090f0a0c060f03090c081e010c080a05150a0303020c030c090105150f13080a03080a02180f0d0b0906010603200a140403120c060b1503 70
    0x203411206201030001103010004c006041011f035025003900c1c1706991101200c109080d03a100d280030400342000c2d840c43e1003002200e0180903048032540103440c0100310300d003280d19241d07460f2016900c155030680c8080d4038550150b00d20f00003d00c1c5030141d20001c0c480c100b182200140b280f40b02030815000e40e40d031500401c2c7d0484402c2100c800554001c3c1c101c0d1800f41d41da0401940343c00240c000c0a00a008071040c2000901e03103542d40701d050f92002032156082e0307001c186550446401c400462000d19000308551a903210420303801d400185004002011070303401c1c0b4680144020b0340506090404c0780180715000b804001c0b034503002054401599008041c90002d400200d0319461790320f0140100c030540c010310025840c00709050b410f90b03000340c60600c10204590038058444403664101e06542c1400d00109206c0c0d885141d8020b40d11034034041d03140c140703130710781d242c101031081458510404901168203030b501300500d40c014203416060854110b00c80104154140001340300080040b405030b15501d02d07404a5003a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 376811061 1250 376809811 376809821
    0x60f0a09061802040608030a0c140109050a111306080d0e0a090c09090c2a0507030b010b0703031a0112021e071a06040b0105070b06010e0301020d0f150b1903 69
    0x1800801c2407020780d150b01d940d0128080d00d0b00083e40520b05004021580c5140001250241c01d0302e96109607142c180c0d5180c1e03683c1c11b1403044880503195215205c1c0000300300c04001e6000e2181c002c40344110310714022003c03c1078404225001d018039900f00704007007041507400305041094072440e0030b00402206a940c00500c0c0740700d45412030700c42546402c4008000c20303030040d2038005550b9070020800807c6200102507503c2e00d20a5081e078002145030b0070741101128900b407403c07920f5100702c085440058480c0d03a2001c48403c00d8200000000000c00c828040c107606000301c00d01c0c51000c40c80690002038140c0024482c021480c14080f4440e00020400000c25008040511800c58028174a48400360b5281c01070b041e80c01c02c202c0400041249011540c00d00d0144941e001111b4146c503110b00d0300c0b81c01d940b02504404000c1013a410301200030395501d0961428001045410100c80c1c00240358100000e0840441e20b000340c540607050000340d028800540020100d03800388003000d110079856045c1200c02c030080c01c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 376812311 1250 376811061 376811063
    0x40b1305160f060201060509101a0408060406140f01050604061d040608010e1b06070609060e1c0f0e0d060b0a0f060c0c0e100302040b130219020c0d05060f0a09 70
    0x2070488080021006031041200e07050398055070081c01102d0307a6908104138080250703000741d008083c01c07004104d214803a4002c94040c100001c0064240703541c40603541c2c14802e040f14280d410780c4d11a00c3c41700301038030201046a8080b081c40314002d040d506040c0818014047c1d40101d0b400d10550f1030071341e00012050b1216100302c01005200380b042940307903c0441e0280c9011240500148501040550780f101c07442040401e0300b00c00b070101400c240c42501c41c1006032112540599000c0d948402203610070070148503548099001c034481c20720300b420803400104001c1c05c01580500300500703042942c3c03480d56581000200b9541000c4d02041d61742c3c2c4e04000401405076644568884010f0242c0000c0d100d400c000382100142c05032103204855a0b40f0004050a4907080310580c9044580220030b10040ca850ba0110013801800741c84001440d01041074074040380d00411000100b102d81440c000b03130b5240d04026007450160b0a440030f031024240d5940c2c41d03555200c041d10401c016983c0400140c00004141d110500306 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 376813561 1250 376812311 376812343
    0x30203070e0d26040e04060c0e10082202090f060301180303140a06081504030e04060e060a140303030133120501081902040b0604050414070e0405040b1305 68
    0x1481c640fa0031019921540c103815a06001e01105038014840002501c0c21640c0405100c4019503031036503108014454081b07160b05002030301144241c0c644500d108400c0010301516401000d050541000c001401c007600c0e450405400807424600589035000140d4100d0350b802a0070480341c0b60300c40001e024024000d0004405000b40d1009010305925401c200745c242011003038241c00b03441cce184c225402d41c0d145000d00041540104800c00901004044950b84640a494044500e51480d0005415600c041d44282484240340b4180301042c6002201c0c00b00130014a801143c0504255000c640c8a000511451034444a052000300d0310b02000306e0f000b04144481d2080314000c16070004050300f4613610000c00313902289440004240d1007000070780d03d00842d030606840c51110700300e80c0c208000760a20f00a565042a01440002095181e0740185450b52080392610201e138a01002d00412251498100c5407141c0d0a0009200104040008071a0000400340442c6c9081141d800c0c1a440d000c0780f940fa031f00e01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 376814811 1250 376813561 376813579
    0x60c1407150206100501180302060c10020d0902011205060904080a020c040f0207060b12060c0a09050409050d0219150b060712030510171005100f0816080109030f030203070e 76
    0x1c81c0d0b010400601c540030b4043c0304a04036807240011100c02c0210307a00d1402c00c005241003031015260a1015020b15200e0700200d69400c40c00c000040b05a80000c1c01180100340c69010510456800241c101f020002c008010850780c5000340024401110140000d0f0559070002500d5140c9442400b801130ba0010241041c82000b40b010001d0000754072008095580702e1404502031114581550700311050704040e00102410b85850030015499400444010184223204038006519101c80c0070b8110f0242c02140034100160715442d001e81000c2c0100d0088141100310341c01d001c0002c42000e80344600c00b140f0100000c0d541d16200c04200d1a200e94440901162100c001002495034035410643c8a0010300e80c40c0f54645640da11301d28000b40e005607460b107585c0c10566844401d80000c1d4030042c3d001000440051003265280d01c4802500201d0f0840c00342c40c1c10988041c9101034003210681c00500100d002040b011a46842c0284000c00c00c080010405030000b000c104090312528683c10700100c01011020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 376816061 1250 376814811 376814849
    0x3090d0c0c1d0103060e0105042307030c0e150105031e130212010e070b0913200301080106090c17071d19030b07030203060a03120909020f090118060c1407 68
    0x103030b941d02440304940050404460350011481800703603a010315030000174501d05d2103510803600c0100d070103d502d41c2d42510a000000010a8201890000a0240c2d07240075900382017040003e42030a05c000981070501800700240312020507803200c00d0a801c0707240180f1407030350307100c1c0114691701c20a40d80c4080e50101000308070803620b1070190300040d500701a050807980b01569800b5040200c0c0070380001940d02c0030310f040e035040811050381c000782d11101d135058001210341140b96500c2c40c584c00a812000ca141c0d902c2d441800400c0c058407903281c0d07078039050600342260030402201e80c00004008000744200b2900180034074140040e641e045641000040c048030002c00d61071800030034000984026a41068000f01003400d060180c822a070241101030030f259410360070364403140c2c210140800000c0030030050410024286d56103201a0080c1c0704a034400c5a90341807107400040c8241e9106219104000080804001c1c042e0080d0040300066440510f10324800320102d070351400d1080783e078803043d00b000c04000d00907 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 376817311 1250 376816061 376816109
    0x15070201020c07050f0a180e06071e1b110f03031815070b0609070c05151501110712020f1002071e0303020c040f02070c06080115030203090d0c0c 64
    0x30a10b0080141103510040d5a0010040c0c1003080b001d0b05500643c190b4400c1c0484010400c6070140002c1c101000300380d24181064803403900e41c0403110080020510210041c104078400070903030019045203802c019490382c00050083c000c50564004001c007102c10314003034a941340c1c04010a6486c000405030307515204020300c0d00782d00d0a100c10001e03124001d460780382c3c8107509d4800d007511304050300b09204c00c0c405d035030700b009001c0302e00000341818040c054244e012030005401000041100d5100d40b00d032108a040400c20315141c1740e01102010b050114008100d6424800018000e044418140e0300040e15036a500100380e46c02c619282d040e820000380861080e035503400240917411108030702c0726160342125000d001001d100d0240030040c01608100e074991a41d02d007540041002c1e0840000041c507200941d55004903044403a400310000c1140350004200d0b1110f1515500c000c00143e04044d840c51419000700c5895a00c2c145100c020300030046074410501c0f000540c1c0c00702524070b40e19029801078a01c1c1d40c0d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 376818561 1250 376817311 376817317
    0x30a18060c090602010519020309070e150a08031602102003030106020f1203010e0406060b0d14090a0317040f052a040603080a0c081603050d0606020c10111507020102 73
    0x280070a0b0245800600c0ba03105100b014861103140c0d000c01364184460356010083e500c0500f0b0104c1a204e0740102061052036501007074061500c48200100391025602031028030019940611941c0d04180700c1019101b240314421500280c1c100d440d0b000c503611589007a240049050103101d510070300352181c15903401d00000110705955440c0c080703601a8007003920b640d9072443d010700240350091050004000c103050b03085000d40c00c5403194030b01003240b640354001c1b5034058224903000081d03152100302224100e10b01c0c10074180c03c54505401740170180d400b610080c05604040d1103080000070140001024408000f4030740080c0b90f44401a91807000c14840b0030f0000105c941550350070141c83e66600c903032a103024840c0390b00316a4407501c0c490820900e01c0051f6140b101041065449900403c8030b6141c0040f1110010038a5201c0d03101c09454454840e14101121080d400c40d50a551010440c01d5a6136904e40002c440910280b4107901d21003844840a8202071290800000380d07850b420501ca0010b8043d00a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 376819811 1250 376818561 376818581
    0x903080a0e0705060f030601090504112a030a391b14191a04030b1305070302130204150c0303050a05071b111e1023030a1806 55
    0x106100c0014040c1e421030321490584241030384140d0801004510b48110800b0396841001418040e1116079540d0125080d90b0042005240b030f0725000a08840e650b03d41030707034404220525065030100250440f0400c1da00c1c0300e05400042400070160320b41d00503130b0f0844001c0880449202c000410035244c10032500c038100041c03500711001c00d06108505100d2040740c1781039044605284030089045002400e100c2605203041c40c20b42d0145081c600840c02061117600d091114454101180c2d460780f85040600300c00c880a040106140e0f6200c200b030780411000103a58041c0c03501110380004600082c90342c43d00910540d031050a0100814484050980d0420310f2100100d00076141400306588004504007210011241480400c00000010070610501203900a516101e14508900000c6c00b60000f00710303105007000c0c00340f522611300c0d1405247c18400800704010146003807a09a0481311216204d840498113000d0b030110f1400700000e5585842038001c600005940c084083d864501400c01801a140180f0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 376821061 1250 376819811 376819831
    0x1805010614160611270a0302040b0d061a10180303050f0c06010803250c1401020f0303090102090a060908030a0c1e0302061501090b0304022e09031a2a0c01090308 71
    0x95002d040c5d9211445820607080010407031032184c0c1c216401c12004201c0c2000198001c0ca46944480001d507951265001404c00c0a0703a0174000e5046000300042e20b807698a8140c100b00242070340c0c6128104120b2940300340c0754113081c041c0c0c0314200c0f061660264026018906c10600c01d5500008490750003000400c410340600000a43c0c0e042d5025030411107103a003100081040c80000010009643e00005503500790b60144150740c1d03014a0400002e10390703002a140750070384d6540014500403601c0c1040318400101550f080c040821440d01c1c1c100358590242c00c0c003500c04e0056207100042040b4458040901103031703400c40c42c0001c0641a0900035910035044039601c0d9281410044051990f0154400808840c00c220885146030744903030138000c0c2030142d80000003034904203001e20b20488450300f4042442d1a15655140c10351803031401c00258500c002544c0d0901007401100f40070300340501003121000d40d2140ba02d00d0070520700d01d40c6042414405c10700400070a520388080c03442015405900301c0d0282c10109 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 376822311 1250 376821061 376821097
    0x150e0c0402031303140f07060e060a09031b060f06090209090108030331020301050f04030212090f010c14070b0c0c0303030f04020d0c0503070902041805010614160611 73
    0x42804100d01c01641c43c00c280103800400e610009100700141160788440c280c040d81410302c580045d0b100303a004140100d0b0726644852000d03060340000c01100c0c1d032000c8a400180150300041d14050640b080d00b000e0045113008a261341414072090383c00505031494400c8041110316681c1c01210001c0d00f04c032914a10501d904000050301e5000082900e002e060301e90480410f01507945181d281005000801c0320b900f00d2030686c001d000d0380e020301c40d29102e50b400f8242c0203010f1030580b03402403d1503c2000328441c6c0b41c1c41401a4402a101c00502014001003030a040026400c103003800a843c02d000c10702c0c44018401c0e2800844c581e03400780d01034030000c880780c2e0032181e00c2101103003055200d00045492070948001d0000040140c034080800c865018051042201940e4030f0f50b000c207081c41c26940111507800c0c0c00080822000c020803460820460f0180c80c04c0106504000300285800031070808510800c4010410b00b035600c1c025801d11110030303031148003003160304030689801e042a00f140440c007050402c86 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 376823561 1250 376822311 376822333
    0x303042109060801051c06020f1e1e0a02011e06061209080d15030c06021e010504030c021027060f091805040f050a0f0506070f090e06010c150e 63
    0x40d99000c0142c030642e03291000360780e00b0541407001140e90911030ba01e01c0345002180802083c0b440c0f0092180c10007204400340c0c1e40b043d180303021602d03113001c1d9400d8844c014104a19410643e54521003500c008020401a5031b54807607410072030140104251407042c00d40c0c210103c0b600b404c8958801c0c4202c4140b034840c0211660840704c014201d4200c8940540255002c100e8140310850700d510440001851103200002e0b075450b6204c1e0101c02101e40c01501c0940d001d000c8011200c0380302080403d03400c0711880280290f25051b82d009003004450000203000700200c4d454105024010603591004085007441d040348026007060010307814020b1301c102404100b145456031074240c0b05009000a60304000310000615500300c604000400e0001d02c00d4070382403160382c12200010f0046c07001542a5014a11a4250007450300b0440e0400b1405844038052011200f07030b441c5141c1c6c100b44800200c3e05861000d4510b41c2d80c403401a5002e0411040040a1402800100b504481c0543c00944253e140c40f084035030305c40c0c507 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 376824811 1250 376823561 376823567
    0x150702010c050f0705070b0a03050109050117100c090915050a090e1209060f03040b1509091506040b03070303021e011515021614040f051312090803030421 68
    0x91030610307400141c010840d950503e614407008180c07862064040321030301c0d5130b0399400181c1034003d820000002612180100000e80c1d2a0250341e01500700c40e410030b403d1060f5081001e076100741c0e00340c02d0801c0036254a0501103060250070150010807445900b40450444a1101140c5046a016040c450490744030003250079012440b0340513140600900500d1003211808010400307400101419034080401c10010071410142800b960040740300740a092480d04260000c1001d800003001198010580c220400010344000683d0210314601e44c0d40b946450f440d4800410b020b448000744454240c8504c0e40e0000030568000b0f1481e42080f655254000d10030103441c903075800c0e1900841c3c4491000c08d04442489804401d92040c818040c0794011686414a240720716801c408441d0712100d040c01600d02c910180342000c0c010640b401c2407000b000c002d00d00d4004d146600c2d42400d50409418804200074000c01c11f4011044035019020401c1160b4582c0740070700e400720003d002e04000041c2c6094a001c1e018020f40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 376826061 1250 376824811 376824821
    0x40b0f0a06111212070503040609120e0102011b020d0518090c07050d03090210050a03021204061b05030f0112080d322e03170405150415080c07060e15070201 69
    0x1e51001104030b82c5c07640380d0200c070a500058001d40e07013607a450351403c0001d00d00803540418050075803031f60900e60182d44000390071145607010340544048034070140d80034a03502140042400b882410041d07150f420b50003955044045c4a0041e64000c8200c800b030181442003007001d842c100344141c0480d5580f00380300404605640741c2001c000d4119210701000c1a403030340528080c00510311507180c01400d154800e121800220310540b0169840e50740c0e0f08110030500c061a0204000c03540d01e080051850419600171f05050005204995484213041000380c20400090111000e00000900078420641d02451245481c41d00100c2001003400070f01e4008004642940340c03a129180e040c3c42d0307410001da035102520002c1c48c250454694810b803444d0100c005091040c440d090021005a03454586040c40244620002d40740251401036a0522041040c444030050f4035083e001d00d49001e1190b61101c41d8207402502403403a00604050034141c2c82c0c000d11034000350300700c5051441884020251195401623080721 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 376827311 1250 376826061 376826077
    0x1f090506042004030b06010c0b150102120f0d022206080105030d0306080303060907090b042301020106051f03021201120b150d0311100504050d0320030105040b0f0a061112 75
    0x2e90a2000700041552001071036070206041c145801c0c41000e6a0310410320302000c403414481c22114418050040d641000b1224041c40070407d9240707001c02c144200c4ad01c5024008003a50180d4002035985101e4444000c2201e20251595800c0a41c545401c4040d1400509024140c017034800c088140074060321038000d807001c0f9011480a949140c452005015602c1001010201406960701001540803002c03c01072008105417502e42104541c1d0b450302014208036014114111781c10028244000d6580750030100884240c50001d26210552a000750007074012020a42441d032800782c0002001100070000301c0d0301c3c03480307190381d01c0d050796440705400085180c0810f070f2908031a0310981400048d0040c5155107258800d0811507100d200e40c01070b0481501e81c100e40460750b54002c14401055241c060180498102080b468001c40024009945103940014031030070384180c0d02c035903006901c1d4031000100400303050040d01a88240b511414090203950b940c42020083e0b00c03d010702d0700018602c4c002a01c9086c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 376828561 1250 376827311 376827371
    0x90303030f021c05091513060f060e180705060a050d18080301051c120306030b01060806061206040b040608010b1806030a080a0216090c090b0a02151f09050604 70
    0x801c428103e010001c000041148500740b04507120b9000038a2100b440a219910b121208030008209151003400e40d203c44035644071150030204188a410107910354150b000d01d450701a02111004007840c145491030561005400002c0003400c0d04c8003e034068001d14503109000c000380641c50015201c4c641c1103c1c0c200000d4803a4000b40011711291405001d5405400704004038804003c41c1601e0306c032101c45900110101081e0394460800c2001002104107004240e02e040c034402c10315000d8080b420510890000f45e045030f5020001450b190b640b64801e03412400050002c02c1481c2d240d2070740d140241040da00207841080350b0f01c0d000c0094071403210100c0c031412002d005420061821703036600306240c1005101809501804d141083c4030780e4501949070007414404070101d00c0c14003111015007000329a401005a5041c100b0001c20b600742c00043e820a81043d40c40d005083d503075845000d130a040700010364607d92032018040050301c0d4541d900003900401003141d0411201c0b200c02c1070484048801040460f503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 376829811 1250 376828561 376828597
    0x201030e06060f0114270907090b03150a0321020c0301110904181b180b0105091203042c100302090a090816051b0f0a030807051606090303030f02 64
    0x45510601c03c03110030501c0c880442d4106688481c61070400020030400d05210030120f1210241481e0407c917050b0043d445007032221229090103154242480010129400c11544290440640d21a01d510100658010300c0420109541c141039010185a00c030031a8010f10403454081460b180c188642240c0720821100d507450640315205002c090003074070310303401d6070303005409010804a01c103e00540c05800403940046109424800004070b4491f03441031400340d0340e161203000c8015903041802c45040c8a000c403281440e1f092851007880c618412a0080c86c000381059a40c030840f03031051414804210411040e91440c2d641e0390808035a403600c0da200c080c2d407000000000c039450100036400410407030b014910661030442c60f00c400040314258010112038551000c03070f0054004c40d09500e02c8810020841300464289030784800101c14030490701010b442200009900410450208401c27421114a10b983c0855199100d2019140070007074403042c1e02080c01c0030440950400700b88201c1302050100906008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 376831061 1250 376829811 376829839
    0x13060906020c150c1605010e0304180c030b0d06090c050618040605030a02101d060703120b010c150222081e01050f160201021b01050117061005150d0c0c0201030e0606 73
    0x2e40420300d120071b40300c1d0355980001c040600000d10007030003c0c00c00241d2149190101451340c000311803501c803844041604c0c002e41503031a0f65403545421411f90704124082010449814404540c8405a02250740301000003852110b11001c0305103d001c906007240c2c01c2000e04c2da00c10626440e40c40408009600100c0c03034180d049154055070b40007681e041043c0d04a40003d07600c5c40400d1040d03004085c180c0c0030030140208600d06400030302a0022448d028a8501c00090b0750382c0d16070b10f1508546d4a120f400c1500451181c2d840642c0c0024009a038449249160455a8403140d640c0c485c1d071006080103100c0491007004c100e000c414081e1500903005203a04403000d45d145044814075220814488085540802c10070288044501031211141c03440800012194034142002446080c2c180340581302e90050020070400d448190701100444200f501e120010009a040c42e05540c8581100e001880b460107001d212410740c01141101c1e0b40b0300c00e8078100b0070080c14181481d03550208551481c1d012408201d496 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 376832311 1250 376831061 376831087
    0x40803040807240501031707050d0809030d090b0114060c0d03051012050715030606020c06090109080a05010501031b050d030f0203040b0c100b040b06030406020313060906020c150c 79
    0x1d80e0b1402240856804200b004440d1403c0e10964206148203403994018028817240d51400303801c0c481d00000040c68401250350301c43d1038450400803001805603c200040304468240b0444d08000c00c16103081145800c28a440d8840389003c0c0a014030030740000000091904028040b5007210f0180380040c850f0380840042140940310050007410b0a400200000468038008114103031524810400340c0701040c1408145188410081c913100308160411a08015031500400c40049010003940c000e80e550303440c44011303280c240f40366002c42071502c980030808082c00010741c0042d0507248141003021031441d03000c1a8411000183c01841e50200c140d02c030000019000780501c0d9114030752703401a45e04096907001c0a044a030888001c103c03554020030040380b420342c114455540921000c6508001c0b050300700700410b081d4000100001e040e240e00101054805071142c4461300945d6222005014800b4189801c0380690089124200d46100303215200700010240b254481c40f032084034818a051102240100e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 376833561 1250 376832311 376832317
    0x70f0302060d05072615010e0a09050a110a0504140603060603070305090a14010905070b030c030601140702030105010906030201110109080f0d0b090103080405120613030e03010b041a030709050408030408 89
    0x5004d000c3e81c0000d009440c107401c80050758040052880c8405807601b455007501000c004545903040154601d0900456610a24500c0a44003014000a00381d503921110400070040a5900c4c10603240211300050742a610100a000b503842100502c1e42c080c0d8004140f1a1501050352501d03440581800049c15041c480c3d4091a48000880200c80340301d82d0a4448049500000510720416516400382e1030a0000c1000010014410b01e907207185980340001a160080c0030250015040200c44040140c40d01d08000940c0d04481c1c008000708040e5964407465801002e031480100d0100d2040d040000589406100e00c0c1502a008407009181084a400c841c900e5440740b13a03444070465a0390ba40e84e001e5100c0356200ca01035841034041c01e036501e0503c0c2c20815100e40d540f000c090554060320810a60000c8101c10380d0302d25605007020300d2020b04140029001d02208846160805d240000c0ca4248402c40940b4141640066040c2d030880d035100c101000c282ea104176006860400300b00042000035070f070a001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 376834811 1250 376833561 376833571
    0x112050c0702120708070e060d022101050f0601030507020a02010804120908010623060703020718060b03072114041b0302091501030c08090a0609080405041508070f0302060d05 77
    0x803070700e000e4240d80066a440b0782860100103607030040005200c03821040041c00d01504a0064948440c41e0180c0003407411429040024003420310061501480c41a41302c101426240303010007800940303084266003d400764111072403070020f802c090100d400c4074008a0305060f81a01a942d0200907070f40e50712041040c0e00400d103000100100440001136020084c42010040c0c96000c4450b58500c42401e81c2940350691211064420031040180c1000a034000590704100da03c085403203940300c1ea1130101d00e0000e200c3e13584180c0c00c0400c0001040980340e404210542500645084502070007003040030213040300c07450000c8031520032041020074042501080358400c1600344181c42800a0b440e070340030540402c030075140a501c01652600d01d034215a018001c00300c5655045c0b0748103a440c982603244641d1481c85c40340c06480030359030782e00084c00d02512400311800f0301000742040c441e4610b40d03c03840303054960354803032942030740280803000c1005011048007200f03d80e00109410308001b480f2419900500f400380c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 376836061 1250 376834811 376834831
    0x6060a12030f05190c050c0f0a1502120406170c0406090911090d0507090b0d03050a030f0603330212190906050a050f060406050102100902010324030c06030902011205 73
    0x1300c0300850881202d50601944c130382d1440300324070003807603c3c51500d414170302858410011078426001c1c5031583c1d40880219043c1000000180d0450340b42030f03040c0140102e25031380002002401040b25500182c81b4105001034004032441962600403c92050143d802088001400907100f0003428200d5008003101c50171505505142403040360006007800340340801115a070300700c0780c42001103842c41d105020340c5010554517000e0703c4016136802060fa1150090030f030185555a24074095a118130751011000d950301c20f404074150101c07081c040181d651800c3d9032000c0100d1070030310700b0000f00180c001d85400541409003100380761540007940c03060600c46010313220b2003a5030308000404610a4080c45020720b82070100000e550170003151a103200c030300040c07090340114101501004680d2340019020750300c40304260000382c10311040c40120007a003080810380c0c0302d5003150203846004654405504089034401c0458403109070b521041a002e861070000081c0c081803000340303008000b90007600000d5101041107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 376837311 1250 376836061 376836067
    0x1050d0809060a1107080d05090112090f05011b03020702180603100f020405130e0d270e06101701030209041401020a120e1207060c0306150305040506060a12030f05 72
    0x4004520683c0104800f00001114a01e1022a07034a0030b00400c4043c002d014050441c200c90490080c0540c803460b2445130400c00c1c1a004900f201410b603001221580d4012102c041d82e8599051541c00b80000801c014408925182d00d0313131100d4001d100300e500f40707603001c1c01880d6044d80c24500000c0541d0010804d64050107400c3c02d45c039600b0107520a0170030f500d044010058460741008240141d500e2080da02c0f007919490410840400040002c03d0b401880c111700e0104145004040d40b142c01d0300f03450221440c51110014085035030010362500c41d1080102740c50364601c4944000c002c40d0018100f5001061802c030305001131001d4140540c0d041d45c01070081000180d00419a010380b802ca1780419001c8001440c00c4205028501301d501410802e04640300c000d0000c40c1e40c0c08920ba03224842c41e14000c0c01c81d40d42e8520b40b0510ba0007504800c0080888512014800d810460042d015120864003100c0c2c07401541c002400929004450b1000e03140c443d82909140f4580d65815170b5584190104030092101c28 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 376838561 1250 376837311 376837327
    0xa0509100801030b071427030a0302030306090a0605060a2d0e090109020309030405040216082b09080307050d060302031c08010b04080d0507080409050c030f0a0504080301050d08 78
    0x340008141615070341d0380d412540c0340d404c21500d0000701400d0310b0b003084804285800c0000d0002c081c2d512030080008920042c0d9047e0725100e43d5105204d629076098042c11009805054000c005140310f640103483c02c0b00d155650203900c00455445016555015505208000c07106101d64980c850300030206014040a81c076800044290301030010023100010388000206a40d0700700300c0000f50050190090035820340c02c0c640343e040d4481c05503004640c0139076800f05e000d190950310902030302d0495821540309540ca40e0020b240d80b07446400039400f0344114000d4040e42c50044030500c00c0310f141c241c10940a81c25502d41c00d100f141c10b90311009415030700c582c4401001c8003503070342801001c5641d1020707083c8a2070030f80d06000c040e102400c140e0240c0c14800e001e00040000c00c1000c2450b0072012120b2502c0755a6100c5468051494001c90300035001c0c0c1480d01d01000480e400d044d005500810304034100360300a648001181d000e03540100c0d03009003051010301c010031081c00d00c0c1c40c2980019100d4002c0358141280 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 376839811 1250 376838561 376838569
    0x3210405090f090c0a06200a0c06020a0c0e100e041b060f020705090f0402010c0309180218061309051009020c1c02120421080c01060501080612120a0509 67
    0x3042c0e81411000b01c0b19414400301100800075558210826034041a845140100c0901121112a4005007070102c0d005410124442030111109956000720325442c01c644880c0d00030750321000040d048505209840e0302040c5107902070401407085030004174002c1303038608080540000144c060300490b01403041c0b140940500032001001c01c06086c00c3d540e880202000e8074002803821b0341950107170b40100b100c0380501107142c0c414480c0560064081c00c3c031140110b01403400b11140c43c05640041d0792040c079214240c0d400c89080e001000c43d40340c1051400700ca039446c1d50400105100782d0000c0d1100c108095010080e180300c0760002c80c1c3c4004540000100540d0742c051550a0381e100150840264120503400e15460b503002078044554012440108110312810b090898240b00e98020003541072f00a6090251640e40c200d6074031030260303100420f00d440791708072194240070340807900820703000c1020f00c00081d44c141032880c452148800002e000b03042441c01001218130035070210301c05000b0080100003503407203521 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 376841061 1250 376839811 376839829
    0x60f0f1c0204060b07150b0117190518100e07050d060207020301050108010e062212030207030f0f211103090601030302060601050f03060907020a0c1d1503210405 71
    0xd088180880010981c41040211801a0400d070407030307070062002c0e1011640c1c0d01035144032004100c200207140058200140c0c0c50f5207500130300d81c1910345c0c094100504100d88600140e0380310b000390000c1c071898079103946441400d04031890002c41540040031380982046190000b000070700341c00c405e036071505850300046420b860381c4078000d41e1240c0c1c0024154045080c00d00c18140100110002000401c0c1c0c4241c43c2038030360101501000d800a888241da01e450446144c203101515800350009002000c40b820240180d00008400c0c0d020459908440d00c045000e4217814241c09499614206003842a003100b0400c1d100384c0c0110711586580764140301000010304010360007440d1460080213107603d503180083c680003000b00075a04211052000102807040a030659410040441e20328803c1c0d0707107148080b4506480410701401e18264814005281c01615200101240809003001c1c000d1741c84c0a44820580000d4250fa03405038840000c1e10b0a003070034054410500c454200c040f03460f0998400c00284100303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 376842311 1250 376841061 376841089
    0x807050307200f0c0906060901110c040609050910090305030112140a0804051005130e06221b020c030303152103031608040c050114130f0303080915060f0f 68
    0x90f21551503d00344400c200300d443c000e45400c50f0160342500c2c0440205c0c219000d04880c0c2410301c41000d0608002003828001c9203241035020b001041065a00c2660310040d11060303404607038500580341341c6000207080740580c0c2051601510703003514691030305a02c04021042c011094600548414007205c00802c140300d00105140101d101d03039103443c142010040f19008070071201052240030000301d180091a400481d08403000c035403410035250390300070200f0340c0091910442003034030107c4860081980111751102c03940c004100381d1034246204481c1c0690b030761000e446019070302d40e00030310002e030018030961086103248401030448000c07460181a4402181100800303c01140c002100300204140040100c0c40900903900c1e0400040c2001e45822400102c103008982c10040c4001c1003203158410003045a0500c003560196001d50b59489090010214040c00110300140000d0702180c410f01c0c0000e600010024110420310b00381d01c6480801040b00000071500b40c0294407035942d810640e4581c8145c540c68 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 376843561 1250 376842311 376842313
    0xa02040504080403030305070203190309030e03030a0c05011d100203070e150307350901240509010501030c1b020a1d0601020607020118020f0402071e0b16080705030720 74
    0x550131460050f09440c0001c1c5003404550050111440e000040e45818074402110700740001c0c1d02d01141011541c682c3d14164041d01484002020450329900499141d9a03174001e0000f000003080c036018050b074880301900c0111803640124200407800c11f840d4025a000305840c28480d0700b081c0408081030308224842104105600044100003030f880d0131070b10005084000101d9072084841480c58011a8100e505031b020344090070070002445907500350f03c0450507101910380700405a031245d04105458505000340c03400344100c0800081e0b55402401041140206c98850300c8203c0340d628030300011118204070036648020700c1030700020410740c0d402c4840010b01d0002100400d5140c540006841c000000c0c05001c2160324024928504117100c8940b1901e0076811140d1009001c40307000050045d0141c280081d01030800d0f0101d140c1d003480110307181000d40d4070402d0604055500e1507200256000698115004070304030794001000c5500c140c0085030f01089a00341100c20f40b8600d0046008003100103501d400c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 376844811 1250 376843561 376843567
    0x90103051501060e0612100f090209040e0303130f0807151a10050d1a060d020c0d0c08070201080702011d0c0a0f0b0a030b18100302090a02070203060412020a0204050408 74
    0x42002180d104901404403402e100c0304c0049003001140b082d208105080313481d01010004111720610712000310340249011045e02400c5602e9002083c02517018600d003600c220f140c12170306604250048241c0344564064014803264512030f0b01e8101c242c070171410040314020740410092000441d46824a00c144000000025455556034643e00d40c0c2c01030101918031840380b8060420005510404035403401528081c041980301c8074244048250712549203240d404034010031001c1d01d00d102c6a002d411144019400c40f8940c0c0200f80301a00d0440d801c01d40544400003c00c6014055401182c1c06604070101d4400014801c0025140d01d1800f40c207816450899040070381e801150b4a041c1c219503000c0c02e6200421034440d0b19095a0282034807030580b6030024035840d050b0000303150380c84880c0410394116074100e010345403a2154618401030b0340e9000480c4a0620032010550025142c82960070340707640500140107903115516210b40c0005046407550031813040501201c01a02d407070080b203000314800c88400351 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 376846061 1250 376844811 376844833
    0x31005040837050a170406140f0c070803070c0204021204050c0402090a050d32070b12060d06110c0a02031002030f0c03061813030f14091302070209010305 68
    0x70268030021981c2d4007007200c0d50b5000c821050240b004840e0b2002070b090059440903410025510808441d21407504a03c01c002040140061a00b040e1000c90040070002ca00e940d9004442250300c005680350844400244011400124814019030f044481c5080030440c110041d400282664029aa0780344088810030078081044410006810700034030465065090031240400b140e454101ca2250600c150800141042400101704006031100480c2002c14200706094140d50000b40c80405150418400da040000360040151306881c03640181c0821806c45484220800902c44190f00065804c0303541c400c6c045079510300802c001c103401c0f1020780c00740c890f07240d82d4010141088a400501c00c40d550041041008000d80707450990343c4102c281c10a26100d44a000220720440003401c02030084112140c2031140402609207103448480c8680c1e20b81c140062503900403212003e0500c20280024010301031030741c00f460804c41e0f02d42942c41c4c0003001414800642c00190103043c1c20703032007961250031001401c1c1e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 376847311 1250 376846061 376846087
    0x2011d0d0906020102032806050904030503100b03040c0308090a08030c160e04020a1809050a03030b2e0507110406030b040c12030503071b0615050102100506100e0310050408 76
    0x5000b054180001c5085203048566200c40d00080040100b104c0f080c9003920040401a81c01000074003406024000246441c0c07074081c00a90040d9550910b100f080c543c006401c2024030200c0e84610f074018140c00c0f8132441e55503000100d0f041001885d9000c040300b60089030100d0100003416540b0b41c074500401601440300400c00400704c0701e401c0178180350300c03100801015880b503c41d100222400c9070000b50040004180d00340080c51800701c000c1c00307806554180d105150f410340145c0071078030084070b4030100203140a080240402000409440e4407940c0a160f91085010740080c10607103002e56900510b413442e0301e00080031956503030002c946030481c40c0240001c1c0030400700d8000c05090742924002c014400382c3c0b000742007404024860400c008903101c42e025070302c1c8859030129510780d203d0000d00c4511004866918861900d0013030340d0040c1318012405601c141203010311809030720064424550340000500407640e1100703650080d6054840c030040340605068500c16188102e008142c200c0d01c90710070744804 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 376848561 1250 376847311 376847327
    0x102030a06090203060f090c040308031501030c080601020c150409020705280c03021309021c0b060627150c100c0e03150612030a050d0501050108130f0302011d0d 71
    0xc5100d1403052080200940301c815180d01c0e46d0908585400c5955106507102581e0f00c91a000242228004000d100407043c1d00040c803440740f002602d050224044003001150f6000046429a00607030046c20352203c941031941d015807002c00a00301d402d241549510b002e509a0707000034011150399100c0500d080e04210349058014081c0f08041081c090803a5540f2020545040d50001921a003060300b903028042d20150300c0140c10344e42c090b00207500f00c00428000360700c3c040c0e100019591401c200000403030900e0008112604c1c0c4202010903400040100c1095008000d1070243c240c0109500d00e4034030300026514040c028882035240242407042c0b0b50040c2100703540310340e0403100511070186003034501c654011a0600072900313240000b50035a620540010740114000e501000c03240000a50303503108550000040605c9221110107103e10b0340c0e02d40044404820803074110800382034400c0507500003a080b04040710300f14000d200104958400c5441a032580740102010b0005501a041c5403c4440e048400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 376849811 1250 376848561 376848569
    0xb120a1110020703080f0f04090f02120a060b0f0d0207320a080301090f060504020a031415010504051c021f031a0306011412030f12010801060b070b130f050102030a06 73
    0xd0503c0340e00c1d43c0c1d155400307400741c0c036810350002d5800716030620070380c030114140c0c0e00812090344107102c40c400308100f00000303501038030010880f0800a000a0410048c1d401170004441160241c1403406103013003170711881500715054114100c1d40030807490000c91050010090208000c40b4149401c540c5080f800703045950700030542e009070b00910742c20804110860166070449940e070781c006c180c600044080f07800400058025a5202317102080600009526510003120f81016903030b600000c2c0c5900e42c0c51850000e500550500041040006224a05000d00781d0f0002c105066045d0b103800e80c69500042c4002100340d415805191110183c00030554580500a820200045071080c10440180401d03141c001c14014104d1921141d2400d04442e1241701d01e40034055021301c166601d49800031035100c42e80e0f11907030904105030340000001c25021010300ca19411120800318461402d15603a44400280c0e000a240c41e4039441d41c025640003103195510404c240c244241c00044c0c2d01d02c2c10324500c10032a615600 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 376851061 1250 376849811 376849813
    0x503100c020a0308131407050a0603090b0a0b190617130203070311011103030a050103061b02100b060906180306010801060b1e0c030f0a0f0807120b120a111002 70
    0x4840520a41c000c515409420303010b15040c1800c0e0750703203800c548440c0341c40c5030000c00c1c0e203404524403000d04070701190960907640c08941100b215580e4040860555030880030140044240401007005184a81d02540281402401c0d0302800c12600219024980c016403003000032658548080c008030359071003407943e40154450380111200d40765401084c0d035821607010040006603802030320080350b030203202500000520503040b039660746400b809000c05414284400c540381750901d41c081181045d00101032a5910082d07004089410380c1c0030b5241c0250885c400309541045007005031350407030b0320303090f0003000e084940c4183d2409a848100500d03251800503407200c541c50b4034202c800d00a0803280c0040701c1c1c0c105010022a0008c82480740b414038544599035141c042c41c8000901c6404c0071200b140603040784e1410341c8a44031003400c002e50680b003004048400303000244080b020001080c43d290303c03001c0c20880140c42420004610040c2c80e02d03114142c04242d5004220760301803002890700c07604e01a64181148 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 376852311 1250 376851061 376851071
    0x92a040e19140406050a02160c170303071707030b040501030f0c0e1302061317070617010e0601120b040606050d0501080304080a0b13080f0414041b0c05010b0613050310 74
    0x80b02a802d80000b40008160946400c00b00c2c080803169010344100c950445e140351032442c07070ba280440c0ca400d0382e4410b4600030180c000007020710100200c10380f4402d00407500d0fa15500d0120f19400041004018140300500d0340d0342d0412406904c0c0d6100d0540654410303888808490380c3c60414145a050681c4000c846040e168200301d07001c03d48000160103d54180c03042c0c1c0d00c4000d904007503091001a0303040a1003080301e48040d0302c2c84904c00145d880458403191034692a0b60400513030341001900c240594038014040c1d2002c20b034254441c100c2c002400d000700b13030000741500d2000006826039150794001000a540418000151441840740710b004141c4c0000443c42c0500c0e041e00c0d1925403d560300090311089004000400411101e180c0e80704c0c45902015143c1d8409210042400b2604540112942c00e00d105030400814100740c4902c1400301400c5c0ca1045189221081c111401d48090f24102c0d4a5522261a01d0135074580710040c0031007041ba0041e0b50160b9040205051034404c9020b5400c010504003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 376853561 1250 376852311 376852331
    0xc030a05071a0d050f190504030f080901150b1804090b0c09060c0a031d040e07030b091e07091518020307030209030f010b120309092a040e19 62
    0x303404011a150069200301c0094161105040b900a08840780758aa04042c2001407084625006501c100c00c48202d104100603003500303207400c84000301d9000307001c60311001c0340301b0003940140c0c3c04540c030070400c00000c0ad511000002d041c0d03026005030b000c031450000101d094260071250300b0406005000940e420450640152039100c02c201000c0d04030050a08006421841503d404080f02c0000702010704503070002c0035515000b071140302140c00760200c00c01401001e041c10b180900075401d107000d41d0f40040101a04684440945000150090302306218400603140f8110102c212005503a6414000d03001d40ba207040311007000d80c1c50005180ca12a40404402c0c40f2070000d00c0203021214070f50300b00041c0c80744c3d100380040d03000380704404c2c0c0305038188a50098442000c03015000072740e825000382d40d160040c100d41c884039a924000d5882c0c19038800c24800002e85444c64900c0d24202400d00c80d91110070b000d0319100c2c800c045501c50f4100202148151042000c0810845101c25640c0e45586c000c120403404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 376854811 1250 376853561 376853563
    0x1008150112060213030305090103060902090117060102012c01110307090b0a05070b040b1008060c16050c09010b04090c0c031209060b0a0915080109030f08070504080114090c030a05 79
    0x41401440d6000d452601d00900340000d40c2e0555411090680704040d5980d2242006040341d08030007100d80c00207003000c8010600c4101030003641c2c0014410385a2983c9165220503075a41804002d1840b0704542d40c68200e017102050f43c500640074004a000f80c502d4182c03280500c5402d480d051150400050420400c0c80a89503004440c1412552059070058684460002c11213191140303c2c0041c000d0703d1302c0c605100c2442050102240030720070311003090541ea1794072000140c40302000c4800c82c03d20032040c0301140d420080b0800c034000d914800c00607030381d002003114006a2414020f81100400850119091200d0741c018840c0c182c4d00c0d0001d003403d205080485e0380060414038507640894030591244461020009541c1145503000c00c01454000c5003500c0d021070200412402c0708103c04031503103000c001240b14040c400d01ea000b940542e039200303980724020782c16203601201820b203008003c010400010089400e2003807441d01c9061000c10340c1d940c248a80f142c3c2c5440ba1350029180300e42c11040010b000560 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 376856061 1250 376854811 376854853
    0x11100c1704180c020c400b030a02012a080430020604090e01182001091d04021203030a02030601030606181e03060e030c12040e01030f1e03081008 64
    0x40106c422249821070026010441c4403000b5001d00403048042c5158030040a4440710140400260420807640c0c1600e000c05907139003614034000c0d0214042d03c1c012070914a0250302c03010801c86613400c48020880c195603a01c5c5941c002e6102d04004d03440011650b0010440c2c035046a0400d480000c0c000002c1c0c59500041d400b84168452400a0340d07030703440a1041a98203400c01c0342c0192207004000c1c0b1000c203c2c1001000d910b0b038075080080c11071103c11003120b04d40c01005100151440d40c20008a02400c05030004441d50000d001030381e000c7ca5641a10502070000c000441c4a04440d0300d0168684c10200009010f44139142c00000c148940700c1c4055421100f494508001c5540c282d003040000c2c030a0304805069072290f50030141145003000001c00100000100a00c000341480d070848100c840c000081204500440c0601441d6441d00401040440c10340b0030350400050140c0003090a805043c41850140e03481a0000c601281c0b0000030000603525682d6040c000b0301001001c1c101034415500c004244034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 376857311 1250 376856061 376856083
    0x15141b030c0304030e040e07060f0201060b04140303270906120303040b060f1008040c0512070911040f080d09050301110724050c180a0311100c1704180c02 68
    0x64004000101070611074484010745050241c1b04100804170f105100d07031120395501030600031a400841e100c41e400d02c144912001c0350300c015159406c150905074042d4108025a4a01d039242c8018040c0b80b8a182004031003007000182c481c194910542140b05004070100010045445502c0c0306210b21900302003c030441768072540c410048283c9030b817070b9400030360640040e50140d5084400785110040b500d800c0701080f0b01880c0103850902d41c1039561000c02503d4400481140b00700d810100c0b0400400000350446070030518000c21090070280c65030003001c615aa550720900803a80000700d2009071980062001c405054280d00074003038903520007080a2184911000105030305194146040c1450b40384005280861401609118908140381c030080180c01c40172616550081481d8444880c4c6001c03003e034070031240e11104031b41078460650100100c01441b500702e003041c02100c80075000080c040b01c400051f010050301203161514240312038403241108002200c529107242c061030f034090f00c0c2c000400359481 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 376858561 1250 376857311 376857331
    0x1305010804020d0f050a0503030a0b013e030c190b090705150705030f160506090604050a11040b0a0306240503030f07021203040e040b0c0a12020307050715141b03 71
    0x540185c1c600f00e4902040060050407a0001005110750003c09400001c80180266030750441680160003004900f81407030030118809a0201cad41481d4048a10460500c017600c0400f03aa0800304044206405c000d01d808102e0a91040310032084100010b0251140d04101500c000b40001c1e402d141c045640c00155900e5030071440700120303044040001c200b04541502030305191741a06d5483c0c081c40f10441d100013400480d00c60240c040090080c090002e2890701ca1900302d0018890b881a6480c1c0464058150030601e4025496250101080d01c0305684030000394031510000642860701d100806c222140072070380e10038440c83c8800070052503600100780ca09a844000402e03540d06581e01c0001c0315802c0301d80f0140b555000110300012030a40c4200164400d5003c1c044094181c0c0c1e410014001070b11030045140040340503080000d01c1e0010aa010355807208003820103a141c22403c0c0c98901000c1190000c03208010b80b16610340d000840800c81d00e45d0014903e00c1d085201032008075031001e040c040141801c6034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 376859811 1250 376858561 376858583
    0x518070207090b030304050a180c17060d020d02120a14070612180b09030a03110c1504110301090b01091506080f0606070c0e060f120c0d0203120408031305010804020d 73
    0x10390384c1801114000e101c000c01103036503a995000c440154185035000601003918103014110f241e401f6a6400c0742c10508518040506d5540c00c0810011036566881a41c010745810390010050f100d05200710103070300c054030090199400c1440c000043c0c0f070011f88811580e4102c00300c03c0260319046144c02281e18a14507000c0b9039628810b8804405c106005005810001c065040c00001040440209802125541c051201c0303100c11442c5100751242841c00c6040c1d9029201c10071088a1010304190060701c541c00c003e23241050100042d0070343c1c113040b1054442000c01c1d03004112488481c82218a050020303811903031010300d001409401c0e00070003400d0400f07003a800f400007074070b80c0d07212001c4801d41e07030344440c50001a41c0c03501148600104211602401031012122144091a1801c600c40c1a0f500c100e0080c05240769500500101550006049801d0321889540004408016003d840030f0469840156100c001ca01006c2007191165402a0305114143c024000540c440314960039a294003c0603920b5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 376861061 1250 376859811 376859831
    0x50f090705030a061e1d1006062f10021305030609061b090a1206050f01050609011103070c1502061803031b070f110f030111180607060507020304051807020709 70
    0xd074040100c1e05d000462621549481c4042052000b024403001030b0120750044031600d40c02d0046607028014031010500c0440020022420040b1809242c07008044d68102e00041844a600d0203040c40d511070656900420300c1603980741d100b0300f00c0004290840040c021802c113070210549800000e412424442c540b2441c080441c1401c1c02102c41001c0060640d0312841d60ba104081101e42d6200001c0311200e080a01081e80304090f458114141c41c0700808491a025800006440690307001220b001140814088900458400d000080041140403008941d001500c00c0c0241010300082c0b05041d46825a960009179500c00420350764002e00f580c0d03500c1d1101907030f11010300d0310340104070004080035558595581000b4089942c144000d80c1591100d076541c42000800d0b00382d440b24484109002403d10495105002d541241d02c4002005411a131401341d09407107010584004440740b20141c0d02c0040c040200341043c17901e212100c1c81041c00841d05040140d4029211040d502c10400c500761114a082 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 376862311 1250 376861061 376861091
    0xb2a070b0c071415040c0b09010e010f020106051305090606030319080c121f0824180f07051c0209060d0302010608070e190204030f03030504110a0306050f090705030a06 74
    0x3080034181c0c0703021120303016500c0c020134444c05821101120842110040003d10211070000d403056003005031140b15a00e44007800459609031102242c10840d9210080000d540c2c4415901d02103490303c01d100440e491a003100c0061404030003520f00c90280c6c1c01007002c41d443c6030820048440c1e005091402c074649403104c07034811b0514041c580c1c4001041c204e01007486290035102203010700410607107414000995945e60041d07250040c1d003079100c65050b09007040102c40502505800d41c0651220805401f800240d020940780200c04001c04030302c0d41c445c40091285103081c084840d03803400385641c241503030072207640418000003001d48140e010f50f80d05010141094001e42000c000340020200b26414556128103a00b01140103407001c16005846148d0004003030302e94001ca60690383c0004005440201980e0202c0c000c00b00100b0036a20344c030200945480c40c0d6114210303d0000c50240c60701103140d0030b2000604901201c00362004241d075200c0b010030031058501107450090b81741c016400080f00c3d0f500080351 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 376863561 1250 376862311 376862333
    0x1104032a0518100b0d200309030409020d020403060606020f010f18140a05030a0c020f04020c070b030a150b0a030b030f0601090f0213060809070b09031009030c0b2a070b0c07 76
    0x4d100c240c0e022845070040f032030b15488001c0e02c1c240d194070081d0b550685800400c040c4003c0d29a0440d030b8004100500000485800038a0f800c110345200515090341ea84440085074020f8024900580081c6038001140809001e0031414101e500c0302008242d086000c2c1800d01c030408640149000d66050902c249a13006101130780c2c80607040380a49031344901d128001002c0e86e000c5d5008911034001c1d00649051418280300f900c00c5180fa09005080307041c2041103d072000c2d00000d01260b00c2d03946907103000d03580c0081d07162074100404810746155100d02014070098152140344c0c03e658000e92141c40b180070102400a580b604554800344c001030110701009010019105a48012990692040b8005125540031801d01c1c810398810b816100c2894450007504684d11800b02040d5055001200041c1d40d400035a2142036158400e0808001340121903036403030700c908000c80c2c41c03180380c2d0000ca03407071500085030217152504e00d00e00e0030803907140060740d03a1800c62200c406000c071250508041290410055038440c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 376864811 1250 376863561 376863569
    0xc0809040f020904140603070e0c0c03040608010608060607110f0409140a0b24091e0703091104140f100315022a0c10031104032a051810 60
    0x902903807040d000050040d600000140e4003031031410385c480442503107003401240950f0008000d0440e01d454080640e000b000003a258481811007045841c98041040004200525a6071201d29256151200c080e00e0900d00800c1540030320b00800400300010081d206075a0700c81c0c422288451064440808140100341c100d0307008248105084540034825000140c07a22218815100060180e0f01c1c2e489001d240c40350b11144031520f608d030420b0760b505450104012a440f11756400c0d800307039203d0340d416640c9081c40192081400f20390307610103110900900f201c0d1044000740688041c020032000038050802000024445480740640c0000300302400e0f10021a8401190080c0c0c0000c00840d681003940000c1d0b00120010283d01001c2005c80348007134040c00030f8000c04d42c11001801e1080d51134800c0c0400041300032018400c042d5035594102d24800428040d101940c0204a54548210888001540c05408111018050240000030403007940c3e1415000104804109040e01c50b07110600b15102079016071300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 376866061 1250 376864811 376864819
    0x1050706200f030105040b0f03030f16060216120305090c0f040e060f070305150a0b07140609030919050a031424040b0601030506090c130806010f060206070201050c09010c0809 77
    0xb0340e1811007407030140618140c40d400c4404000600c408010003503140c80300c0b4107142e050707003050100992800003d400390503001c0c2407451081e02c51600da501d03001203922100c0743c020b462102940030428002d000800713840240c194101003003541800c41840f40d035241000f4189103c0c1110b9401407083c0c5d10f0355005004003000d00c04c00c607955820059482e50146d001210310b14002803a000000d00c440180da034024600003000303412445424140690078809070b00003c2c06a038140382c1d00d200c20851a1041080511480c000009161120043c0d0308000a89036003254021010b0031003807045c4180da0b103104150049035803100e155030b0064501e15460f42003e01540402e20705100c420032040915083e80540d6100714816907410320159590401036003100d0042c5c8038030f0f411000342d000040801041e28010b02d00b80d403110710141030702c0340d039103200321f181c4103098004c2c0c450b89910000410505804022a52b00507189000034082031820184030300b014040c0d0503c444c100b0500e07001c4041448280000c941c4a2440a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 376867311 1250 376866061 376866067
    0x70803010303050a11150103020105032d161d0910030c0b0301050a0617040b1812090f030a1a07171014030d0909020708040806040c05041401050105070620 68
    0x402c001d4a036070452004100450752a902a01069402103420300c801d04c1141d605005503403c50f0011a400d030001401030380d4500205d10741002142d0f90103000c4441c031350210744450300d03803400c2c600070396003184410160341c00d00111000c58002502202c40d80050050292040390303c035519140303509482039181e44050120f03591003001141c44580800218161007095a50ba880c003035440307500700c50003804220745855044020b8007050020340300742c0440740c000d5068404181c0c1e40c200d00d02000e007425400f80d0005000d0000040880503814400b202000d0360f00c040f400761001025580b2425480c401c1c94080b070508075031a0f400110081d000e00c10404094220072540c482e5803412001c4908455128001d444000000001c021942d1400043c07000051050f40e460b07080c1c00f417520110700302a41000e001126041d4061202181c460020080c462180c4d000da00b0701c3c7c07000f602c0c01081c4030854402c2421a1441d2911200600c5640d811000b02c9070307000c1d40403170700081c520181c0c0600061300c1401c00017002468000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 376868561 1250 376867311 376867313
    0xc080a0905010e09153007140a0e07051c1805060c0412021c02180411091b0c0c0a08280c0b03040f022e020d081503030708030103 57
    0x4882004103071402a00c407043e8201d005000c000c50118204c0d903405803200801c20b0b810305810806000341880da51110b40b411440f0300c10700d84582103070102c0c20b021130070f0740001420040300c00d20110210078100180c51070000d40e404e04c008002d032031000420000c148100080d40303188140e101c400030031018640d00c004000808220650304508042408181d0f1988104408105410015021070742103580000480504c1100707036080c00001484038990035581d56000f00e5030b00240e03c07590040c0e141c4280040700f2407001d1070207241641f00c0c01d5100740801c2c000e031902c20811000c848006982c0f000316055140080c1c035007a021a01e20719101c0d020080c10b801c0380714a2030004050000082c4882e4014040407041d0341d0121402401800084852000c2c121010190080044542c00d80066810900450040c0a8910b9503008a079000303081e400d03204030303e00c0d403001e10b81040328070314040512000300c92018203540c0300714440081685030003070aa40d005176030080d00002540d81c02c200300c614681c0c2c0f1600b400d44941e56 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 376869811 1250 376868561 376868567
    0x504020f0c010507020c03060615070803010f03021002070305070b0702040905120d0f110a0807050c0610150c0b04021210090f0b0610081605160c06120209090a0c0c080a 74
    0x1c104401d5105600701400708140c1400810000c49004024006250b0780d44c4a4003080010307020100c00d162401002c1000c0000b15003104001c5010340040080f1a00c040c1c07951050100c0103000214810464101c0e45051000442c04903601c400c0b01c5941203400d494803d54000500284084034009242d48a0314203444d034050301d0b01002c1c044118042008004003181d4800313000c207441011002c0d260100c3c3c00c00020810303600076181c2681210300f600c1c05500303125003001550f20b0508240d035030120084180e03070304008200502e94000c1c2844060719200d103298200356030b08404440f020b0130007031040b020051800f01c0c2e0541040003402c22140d4510500482c103150034140500580d100b4140d811044803070026000341000f00514118010564804056503166404441044140c01811080010800500429607011104c40d107269005087c000801440c2c2030000d0b103103c0800c04681d00c050b00602c5180601d540e80c1d0303240c0c0d5000d88a6080465107000b495011140311210450003040b52501050344000340d54 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 376871061 1250 376869811 376869817
    0x1e02160c0506210a2004030c1d040222090804080d1b0f02010e06030103060f0c0315140312071b0b03042109080d020102090307050402090609190504020f 67
    0x10060100c0c042031626402445064400d015801c3c0f03007420b112070755502007008052034a50107030303580b03100040c116144c0403001c2c0da020220400b000880404681442444501c8803100d0003040300000b18101c5021380b866018000f400104040d21800005603028814101140c5107010542c810008009140c61840d1080d600c1c0c000c4d0080c0c500d00c0c810040d9034000640204009181c84540e00c0e1740b014650a20740c1c9001c0d8010700103000b241006202507850302c1ca42c641d1409140650301c01c020100702e1181203201c050840e055166100308150802500180310000c013000c0500303a488031000c194000c045040820b1424a00030060329030340d10700094400134000300f4915045481d070404880c4d48000d541d0301c02c003002d03804295805400c034480f840000d450842c1200411082006a0a00800c410f90f40c0102d24140807001d0b0800c00545d4000030707114110324061085d0006007404803011810091000041040b901034108010b00138a044602c10344e80301d021007800c400401c0010025541e983c0c0011030708940390 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 376872311 1250 376871061 376871063
    0x604060f0f030317061507050a150e010b1e010f1404090e1b0a14030a06090b011706010f060302030601021c12050c0304050c1512101e06020304091e0216 67
    0x15901c0c02c03050300c40040000781900869004040c1200b4200800f84040e182d0b01c00c550807a040c0c400d0900f980005032100c251003003041007481c4001074102f00a10810309407a601204107100b1580c2128070350104402510040a0050131b10b424000940814420344900e502000b240c8451400420001110340e6182c110640003003c9030306940c003104801d44841d0340304e6010080564000c40302842401825028210b1004490000b01102c46d07140382ca4981001b01c03140307407505440c0102110014400128900e4030705840d585480300800496141c03a009561400781402807908141d000404a803150b88200103d6290145d40c11208800d9002128040c084c000074150f4044140d0610000500f900082e1041d01d20480e001009003a00d4110b6604028000903d15441a0b03007800501114010203080f105e070380e203e1001010003103082c0d403e00b546000114620240104a8407001405100d078541c00b2055a04a42003c1000b160b102004480448002c500038881c440c80352010a40000c441800b124a50507e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 376873561 1250 376872311 376872317
    0x60a18230a060b131a04120f0c0501020316020907170c030f100602030928081605030105070c06090305070204050f070315120b1f06020d0e0f180604060f0f0303 70
    0xc540d440015002c54084c1c04850700200940c10802c022000c0c0c2854114402450a603040b807030710740c0715a00c0c4014498940000d90740c1200e4041040c08114a168228018010034001581803006d0301c1e10360f03240c030800f11200034050003145021414090144909500c000001c2c000d0903903d2a1840a0300700c0c5810031600ca1020b0080940170944610238681c0840656070750b54040d516111422060148008851203248101c3c00c0049450000c0d07144180d0400140103580e0182c41200d00c40005c0c107005107440e03003041d407080c1d141030240052030342c0205039203c00503409000810210038a080c191000d00402d90085c0d0014141010018070f4107909800602c10b180d40d403002c0104c0c4003040300c02c0f041013241b401b42d07600345103d61000401050481e001550321082d0400d20a41c45401c50140300c402c0500740d0f02c03401c09a40268542084207070800c0e6a015074110030344406200151100000365404800000740d0090600c560101d030f2a91615044600540442e0f40e030f101c416507032010002c0080384180700503000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 376874811 1250 376873561 376873571
    0x15070f24090c0308070c0f0f050405010f120b0702031903050403110601030c140a03020a0e06090c3f01080606010207080318010f0903060608010c03050c03060a18230a 73
    0x900661880741c401426089006511040d007141d4a054480d8407010064800d59407107680002d480e0400b016640c081c0001d02c50984400b4502014002070311010307000100c248140342c0707061196400e116012070306160480f5500e00c1c5901c0d01c1c82d069095204500111017021100d0108156142c2c2641055000707511a131746001014441035a030795103c25080c00f005000030722102042001c0010440c006803000e034018205c0754800d5482e07000610f0458264422045200034200300b180301c0c644000344c00e602c040b0000c400c0389010f021600340280150114110881e00e4401c00c041c001102110000c203461000013045088156151059996a81c00880e50280148036924002c02c6a01d004015600c075500c0703020002403460200401528070000c007561030010030803240e02c0000494864000c1c1d400030074981000280801da8004001e00b42c4400509440c0d150504000b409083d840364075600040b0781070b0400703910250100d047c00c0400741c900208401ca460200812111340700308010011b501500c003800e02000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 376876061 1250 376874811 376874873
    0xf27050a060813080306040b0603040b16020a030203040501050a03021c051b0a020a0b07110d0503010f06090608060d03120617010e16031e140c01030c14070215070f 72
    0x42d680e0048400302031000495050320000f4541d8030103140c0000d4000c01c0030480c10080c1c4082a49600111410b4502a506070244441081d03154080d1007036080d0752000e000f0510b02500d01039030f244558442e09040201c00544c0d20b001500c07a506881141c6101c800c90342030414040141000b811041c0da1802c00028000c50941a00e92040102c660300601c60300a048030001c41d0710b8191101c00c00809210600117030720f0780b0094800040c800008201e4842d207030a0307101e50400b0701c01e201001d4a134014506000d07000109000a41d000718003558020300445142c0c4251900d454112044900203890282443c10100c01080e0210110514204106080000c1000720503030030085e65642207800850758000c4501400340b003c80c96001515000954503603422888010640e079602d074219110b179114074180c210380a28003c945e403502a00b0f0f103014a0740303002c0f4000340342c042e40f6a449215600c4000d10500c08210030070000b00c400000d942c0c941740c000b040d07103118002506058103107a01c0c80c01009020305100300b1001c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 376877311 1250 376876061 376876067
    0x6180906080a0b1f0b0306040b03030f0a0e03061e1003050f151e0f090c06030f0609060a0b0a0c0311251707030201080403030b150c0114090d0f27050a06 67
    0x18a1180720644d501d07803240f9041d240c02c100c0e40003a03c034030b4000e0b458a0010040f5201040100700101c41b407128036980e181c0300100105000980d55900f48607400035020b20130340b55030950745452010680203082c10241c0f80e4900b450307418401c1e0791000344280600c0c04020041940070803200f08000c000b6000170580e6071a1403070b242003105c1b44501501481c0691000c1140390750000305c65980602c1c91400c03106804001c9000504a400c05c5443c03800d4240c056041140608000040941282055070001d03001418505200e1060150b2034109041000500280c0141481495012040f01e446000d4911417a204903212400d90f0001d09168004540003d001550f900251222010183e1480c00b5111103411a401140d03045001b4005804043d198601c00c109035a458078200003540c40d0b0180030307130b0f00d004401210782510100000c83c01103180100801840d60030205002492541c4c51170003683c0300c50361000903101d650400e54403400b21002000c05040c030610f440e000d2801d94604031034900b003043c0c1d104411 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 376878561 1250 376877311 376877341
    0x9040b2206090b0a081b01021603120e031609110f040f080609030a080705092107060206070c050715090b0a030207170304150b0a08011a091803030106180906080a0b 72
    0x61780d40b035000500e543c0303c0c1d00168014100c1460f052044e1040c4110582990030f03403420303540040d10711710000882e41d010a50450018920320005402500340c11101c1da01301d100c1002588104584161200071a104204020045528080300742c24402d44a94440800c2c8003030201c5070050343c0c1280324a5020450704800041510041c07030840d0741d034800c10340d44d10200b1a982e070040814282c03c58240482d240b85608088900d4424540794030003030900c4c602e000c2c2c1c024980380300580040d0505ca1198010700204801161400a40b050a03c0c0a21078485070729040710f18100300e03440100c0003140805d10f0f800166245d001480c2d000d00910036210138140c1c1c030076030134080d10059070010190303500b140402141c05038a400031403040b0802040c0301c1c42c49079284103103801e4a00060070080307912401c4061303850310b03e41844d100d60002240b00d2048000c210740c070b540712358900c410b016000074010381c0324803040d040060241c100003901d01d00d4024841c0640e54034004e40d4031680302d94100c030000c030250b001610072042c407101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 376879811 1250 376878561 376878569
    0x504050c0c1b030111040303020a0b0705041206050903210108210a0f1403151305010f05121c0f080f06030718090503040e0103052109040b2206090b0a 66
    0x1402040c00d400b90040c880c1511210b81c00e4040d501c4502e455010041d10010708000c5000e03401400d009142480c01c1180d1030170040101041c80024031003880895041c1e424424440c0d48503400049907100c04008503d1402409010342c0c1144005403002800003410706524100d51507501110042c0050100b81400c1c08050002e03568000024040714040521600f050703101d4002d2070078040b50b056102d1651b280e02c1d07030080fa40f1212052001040804a040c2950790388003440f00140304220950420f080c0254000341441141d100f000300428a802000c0d00340320202102440c1c442109118207503d10292440e00021210808540d5110024018011314100d0610455008000c0c00c1e00904141a0302021a0028a01101c407a91201c0102c00904c0410080c8041c00202000180ca03614501e4a18038140b442c800c40c50b081381904c89038186070703030106003580c0084030126404142d80b48540003041c0f00300c106400c1c480300e0001056090303079481020b40c400800e8802c00380b810b1042000c1c01050000d04030071885 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 376881061 1250 376879811 376879813
    0x8070e0303091e09070e030c04021c091b060e01030c020d02060619030b0c030114030307050c0103020d0905010f050f0105010908060402060a05130603060e0609040b1f17070504050c0c 80
    0xd040b052a004a03030001076046201c40051440c0700c0c1010858482c1d04940b480301184031030042810070300c2c0800880302144411101540703814414824004144002e6400ea000e0360740f00e007480702c104491040304001209c050745580000c9a5150350060250f007100345ca140c0480d181040707490130b0300d00c00715080c01284c036243c0051207643c4400d018072041d0640701d1006162048000004000283c1414525019280503007110391a541403403a00c20b500700c58850340358481c0e88208400800030b0400f1a003507040030024200140c6440d040310b2030201030030703940d04010240e510340421050441c005500c072034014181c403003a03075003a680c0382c1005403608045405900300303c0d8045000100103150441c000c240807040c52619a003446c0a200e0744203411882a0850000720341c07180c406202040a0b44180340d40500b0845005016040c00d03140c01c04a070501400814111800b20400d1503243c1e1800c245000509445503080740304d511000800340c403020640110340c4101c0c1041c010074540c22410382503c100800b140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 376882311 1250 376881061 376881067
    0xe060301030807120e12010501030519170a02190f2003070b0702060403020a18050901020a090302040c03090519150c1b030c0210120b040603030e0105070c0906030503090108070e0303 80
    0x14484003401580c00000c2010080d0b01c0407038201a1b01c5101681c011b44019600216030395045103400c40c1004e1046040100c4881501d0220004c40c10a0189140309200414003075a10000c04108a00b04601c44c0007005009440444140c10402091842c4800724022080003ca903880030390140901012980c007036038542c3c80032809022001c00070004110f61480188494500fa07629408913403581132030741c00700041882556132100941080c0c02071a41c4005c40340001c520300105910080c280188902010b0300850392804074650503030103588a10b617074079086000c4907170715400c08001c07114109034000d007141c0700c0c2049401d143c0d80d50344501410300107201c1074032102405e80941c10240070040c105c05044d010010600250000361b11406002c0c220102a039907101c075084d1080d8044401e4030380c0c101942d4080c40c40e00408102090b840321028241003401d28005a4039186410b080501190a400c40303015149400e0700003081200000080c00003081c21780301d2140c140e80e144020341d000803074042e586415030010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 376883561 1250 376882311 376882313
    0x1505061804020c0105090a12080405150a020d060f05040606020303010518060307030f031205180d0323100f0e0c18130e0c01031b123206010e060301030807 68
    0x4540d61940600a4001820584454681429100140c0d4441d442c0d4004100c0c41c400d10200d0705104440d01d0036800c0c5880700f42000d43e01c9a6503100036048000d0750f183c00e00081b030b00c080603980480b010b051201c8020302885884800da10320030305084c42198880d80c43d22000040c11400401a00d048a20041c00e0442c800990b04000d05194402080c031580360141030702c0800016030700001042078600070350350600310b8900304159004465029200900c0202501c22400046000007041d0400356807900d1301142c11240c0100f03101001c001e00c400c100e00030340190100721803010302c00c0c0000100c40c00981c0c0342d05032550b03541018001200a403403e0b020360404100201c50300058011003611030328084c00982d40465107407883d00881c1e0844469181075084821015010760f0303d402443d2140003180701d448903040e03000c903011b415052529800c042142d210943d948007040d27081203440010002154004a1600c42d50074119607000c00c40b4160b004c90880c5a44641c0350030160305a90580380c0c800380c0c480c502030b42 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 376884811 1250 376883561 376883587
    0x9050304090506150a020124053d05120705030105060412110612180c21071707030c150e12011e0609140709031e050601060f0201150506 60
    0x40144a40c2e0000c0751041550040104c40e4001c11499429900008059600c00c0d0700c0107142012290030542001d01c610b00344496621420006480f4501c003031000c0c1c501c2c40602009003611103985483c02e100900d40c1c82c00700f2454006004100a405d0500c00e00d000d0b0382e0382c450a4815000c01c0c000d6640222080c001400702680e694141c4c0c4889020302844d02410036500300152503644401d80c007040380c1404074240a8030281c0003014503010401c00e40644500140000410901c000c200d400d030805840501641c0c4050005101c0704015001d00b0f040144150000c024580d50b035000d80c441111b642c02e0315100040c0626040c0c0b91103880030500d9032000e020328038900400c42074414046038034401355a60001810881c42001700c4442090342d000022400516200b10b11048800800b10403429000500c104a001c580c01480702059a5104c110030745000758141d405842d001050b0801010b13842510004541c558000300341441c0e84880317500901c104001006401d41214051048d40d401000030310441c221200c0e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 376886061 1250 376884811 376884821
    0x70f0311030f0d060302011d0112021605030403060203040b09010612170909180f070b1b03070b0a020d0b030a03081b070501090803010302010228060207021c11130905030409 76
    0x405801c49050044100750a401c039031040c941c040b8107950b943c600b0030840d60400c100310b900036821521003411006090002c5c00000c100b0324042c401a81c00910600303c8620000348031500c541100c00c03a42c0b160307200d280150003903209803000ea0302c01000f400043e649071814014070065506150a102d140c08056840c40d0200580c524100f06c00401408902c44030380750b0f028594890202a60080b0b01e8003a000030540c1000c80e001c80348880383d000340c40b062254445c04001c82d5140d140d000c00390400d4004411246040d800358881c01030560310a5001c1c05245c0161b034000d030600440e00c400c01c0000307407500b500b010764030f0002c098000c0205540d800007070000c840c07061099050b846030f481d04070310385500d9540e602c0c2103405415044580c800080014030039568104980d01001e89038031390f5085062054200480d8840c0e5144004288980014512045445094000850001005100c2650207441c5000c3c0802c4210b03007841805280c1c04503041c8440c44250140407400c68200020798a01820b0124020240c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 376887311 1250 376886061 376886087
    0x26270103020d05100303120e0601051c02031b030c06040e130204111308150c1603020304050612060f01020c0109090534020c0d1208040201090e09010b0102060903070f03 74
    0x1681c240121100d401460042620811048502841c640d06514000c0c00d00c00144102c00c8046240410000c60a41300240c0c2605446003200c4101c140c18040010000d24040800020b4250155140d80c4151070703d80f00212007944070071829100410030032400e020300d81c0175911a9200142c00140840c03904400401e24601c541d0000e0320215100c1408035010321030350302c5081d40c0d03d0480b00c00c000801c601107041c0729440010b49041d840d181141030055514030709025050110061070400701400d01018020011079001301409081c040d218020011001c25419013215954094a840c001440c200e61020401d8a1108416150041680d09183d1040e006140003402c4002c0446402c90740d400380404200c80b8090308480380382d01407910954404c02814900300790300c1e0754052020180ca40f0b0015408540020600c0f031149402a550358450004942403072181e40282c03034094984c406c2c003480c41010341041881c82801c3e000c5540300d4468040507603681c0b00d5204090450b41400a40ba0f0000b841101681e100c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 376888561 1250 376887311 376887317
    0x120b150f0f12122110030206070c0e01080a022103040501050d06051011060f0105060f0a14181507050a12050d0c0306080111071101030c051210050906090f0f0c0f07262701 75
    0x40303611800c00320000d02f03007078008254035030107032003400c04604c1c1a2000c002003082400d007c0f007000d070b03175081a16520b006901450713051040c0455100c06158031075100d0402000010710300c0c042121070714030180054031100001c01310b50092000042500300e140b01410f04a400140001e860305c447d0414041031038009213940020000180c40c0c000c21140003101402d140c101c440d1070403501205890802900e00c0554142d50130303001086c420207000c85c201090540d40b458200880100c000c500c07490858091040c41120031600307103058840e44896a03d43d01000580749074500030013454445800451860040b104010310525034102d02c298035502c00d4000c0c00744501d041c208a17043c22036648464181c04011a5450f0200e031070410104154a0310503c0542c001c14180c032000150b0600801c0302580c108014070000301081c031000424056044a800c941c030900d040b50140791100792900d402022802c41030b05410050110714208903042606a045610200d10f840041d44581c20750070300c03a000d40350b00381c0110f414 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 376889811 1250 376888561 376888583
    0xf020c060f12010b091804030f0e150c0604050105090111090f0604050a0b030a06051f080c160506011703040f030308150604120b150f0f1212211003020607 68
    0x3100ea401c2d54003070203084580d03040350300c0701c48075402d00c041e0710f180c070a8071044e9103448800e01c40801d030850b5541074039100e1890118031224a0001040440c01e02001040400c900001c103503240480c0499080e02481c8240001d1020b600c2e407250f800d003a94132403040e0290b000420130090350b4920340900c42503000c02c0068a45824540d0700d60010710380504aa20080251100104202e1400c0e4a072003240c01510302260012103001c616001c0504884400c9005010f00122302c01181d80d0001c980e00b919288202401611060042454400d84ac0c0c00284204450701030343d020110801600401924107558601581414491441e10103e0b0b844001900b1801c020015a107060040d0329200000d20180c5240d44003004a41c04034900200001c40050111034503120710340c0c03814406d40d10030300c68110b0140b0895481280141d0b81d40001d0801e100d00b411420307144100290a05c820452001a026a85904842c004c5804000319405107110f02150030381889000032009000524242c406440124022126190 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 376891061 1250 376889811 376889827
    0x20c0705030328030504030507060209011101020307020a0516080307150612080301061803050d0e040e01020310050112020406051207050909070305010f120f020103110d090f060c0f020c060f 83
    0x82550f001c22140340f0800c962426254020b114542c04480c096802d203800c00580c90640c03001005130007002d10007014203800180e00c0c6601e038440e125451100740440002c66890030031000c040c1d0fa030402603200300e078a8050310252101080404107450215149140510329241c0b85a441104106c403020040711059681c0c0c2002c00d8610301c0c01e400c2c400541c030075075100b80e4a5041c00c001070001c4603440d17100c0030030f0012400d00348001540881d0780b801268140c00c0c8000c008609000140142c06202140781c800d42c030100030000c40c1c004280039001228000e8880c84010a0300f80048000c0e446640123032800304504224034285480c2e1407030002c1d480412854103d00b080c010b603000440151003940d003800083e8032180180300480000e40c51400038051252080342d102d00381c8e40c0781989110041c0c4064103050741e44144032000c5026500301d983c00c00640c0c0c02000403d0071803400340c802948440c0142c480758a000d2181c0e5034903000303500d00e00e07a05501c0e40040c80310a00702c00800c4015880040e80d81400103042c41804 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 376892311 1250 376891061 376891063
    0x180d0b010609061101180b190e010f050105150304020d0f02040c020c190825030c06030509100b030615061903200403150f0908070f0c0602010b0112020c070503 70
    0x24040d100503501c605085250683c020140c50f8001000300090b4913112030b002c090140750746104525640a1b00880c05039941495401d038211b601103034100403d052540c0d242c01e065040d030108070051003007c2e003004140d88900034080040c01085844c446014200302250240c0707804c1940c00c0d0154441c400c1011500682e6000c5015030380074005040141c0c0c48003a04003c50301d09100040e0800f0002520485900d01c1c01d502e09070780308964204407144400ca065040113900c0c00f19103080c06190480184100c0f10b40e2510020005e10702152042112300980100c19403030b10342401559084100240201083d0300d5501c8070011040d45150550380c80b10080100315032000c4018400f075044800b80d140016038011050708080c1018090001c411850010001440094a50030002c1d040b103540500000d400004d01c004c08004040d04080503000b5100030540c80f040148140d201c210051007104c0d00a9015a2900b090b82681c1c2c002e4215808a8840844000d140304185e000e042d01b141450121283c1c142d64401003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 376893561 1250 376892311 376892333
    0xc08011202030c1e0a0b1c020f1b060a05070509090703180615030302160b16050c0d0809120703080910020a020909030912060f011205031c051504090206180d 69
    0x9413260210096070240c54640201d480d001441c0a011051030041003060300c40d403051942d03e0080150703a0125580c1c1481c50020b0995400b00300d1000801660382901c0e410fa81ea0721b00c00c440502d0102d0600c0002050f4520403c01d0381c002100103407a00419403074200003a0b000d02400100c0f002c00c40207100c03000c0e01262090007000c4021f00d840030300203050742c1981402410001104100ca01700c0d410380404205d03800780d4030100c0300e0201c4140c4903030889400790301d4080e040c01d5403802c5c410352200149800302c060040030b5000380030f6110b00702c5802029061080285455045520002d0100c3c4001d111800090410103180d003c0c2031050f10548034006800c0e80010960101a1503122050303001051404880c200805070388043c1c0c2c041c000600c1da1303181c00120000304440500942154012103a4014100300c4204140c5503003640000c82e155007188515004c10080c03c04480040200504810f403184500307052040000094003c4d00f440d141040c0d9107075125010820b90381440d00038450220205c0443c1b803003d15 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 376894811 1250 376893561 376893589
    0x251407050a0c18060603090b16140d0b0405061e04020f04180507030507020a0b130f0503120405010617030d0e0304050d050c040c0807020604031817010605030d030c08011202030c 78
    0x43d05800c8041d028481c41103034110f400c41e0051615041b0050f01003550307400482e0b40b00c1300c8541d00c03001044404e4411192880540030001c212032002c125120060000d4024648a0800b51410405552410100321101c0c1c0c051600001d2551200421403003418107400078101400c1c0007503124a00360762504c0700c0414040d60008000d0b00e5584034107110200b41c0c1401466007161092000780a00f0049480d200b01c1e041003d080c42004120022418041080310383e0b030039a41941250903070707448440e480004010300d482140c04803400d511f081004200c5640b501e0a07205c00310040320003107083c0811408801c00500c0454041c40f02c611040c080060103903104500c18602c144114040e040c50010305061109490421080006000c005020042c80560016446620540502c0c3c10a182620841420340c41c00c0103400c8032121441c8160000b00f81c042c15040601107800c1503049130034140c0240c0007241291042d180c5000002d1100004102c070030107002d0001c100340c0c001000d070340d114900c110002e015681c0500c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 376896061 1250 376894811 376894829
    0x308010306061220040f090f0c0f15140706090c290f0d0f05090d090f08030a0f0207080105070c05010c030618181406251407050a0c 58
    0x5004000c8140500320041c840c4030714001803048255140c0701d0200b90442c0c13072104000c540d00c15030519603070382e045a10078009120742004200500d00313201551030684882038480443c80340c5d0000f00b405580060317004413004500507485205c0421003c81e2490001e50449a07198014000100440d0300b511501500b1840746000c480250700d800c40388121030345101004403000c1055030800410096410482d03c0d480020f41125540b6450700000078000e1190302d01000c540d600c0d1a0402250b81e40000d481040c0c0920b03600c8000640b50307600b40207a5415600d00039191550003e02c09082c81d140504001d01092040303005031260304e500c6880540c2110350448000b40050002da10308014440301b8440d07000711034070318542440902d0800c000c02c50202daa07507039079901d010341d0b44120740d0344004400540105c042e0711021801c00304001842d85607540c1402e4450340c10400b4000c1d82c002e5030414400019001d030740d031600e8051f0070807102403043c109a000709074280c0d094040c0c02e50318400a80c0004135400a403403008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 376897311 1250 376896061 376896077
    0x9050a0b1513020a05030a0b011116060e040608070302010513080d0c061a01020705090a0b0306090604110306010f031b0503030a1106090a080409020306030a1b080d1704171603 77
    0x8004001d450060b20401ea540f0400c04409201c1d4480308690780b20158410128140901c01c004030781404020002001b04d02031403000240c554816006141141c215941c0e070000c1b0804041040200d4179544a400c51903072002c041003006502940c064240f0504038200e0034000e950f1a02c01d5410404c2010803600095a510791107402c00c2040d02c42c158010704c0c034001d424124100070300081c1d952001070141318071944000d8000794410411750001c80704040c015003560298106100c00942e6104281c6040300c00041c9040c2c480014140021058100c03161901010410351640d00d0300801d40040070f1080b101d07603141560100ba99203080004084013540360703035044d1140041f003030118204100640131200c2c50300f00302d041c100819034580070744068418218005959452701000645014081c6100520222940c08004043c030611b8210348210340c102015101d8503600900100c5402d054110102c2c4020306400c007080111ba101e081d03240314105c401d07108510b0040040042400c081e0003850840010750700e5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 376898561 1250 376897311 376897351
    0x506070209070c08070c1511060601140f0711040605030a0213050c041a030711160303110f0106170105010801020901320c01060612060518130b040c0602010e120d09050a0b 75
    0x2e80907e0242410b940b40200d00c0700520303c002178807031030003030b010604108001070340106115120040f1901d40c203d04840c079907500341e9890011500c184901007244620714007400010745060100303c21290660042c545600803400140c00070041c4406803e40401e0b05040c000410603181c1e000b4001d0000203000c0e04541c0b24070f03003004010f200d00c0003280000c41503042160500d840c0b10b4031190031410f80380e1505122507106407c1040341e00e044203100d0842000e40c20083c2c0010700d03107000100c105040c4000c6009024581c0c030f424819081c0d00c0741b45a1107000840c0d400da800320f440603011100c60001c9031995801200a000c00123003403035030031120355450240d44d1500200036803600301c03003103681c0005040801d0001d189000300190b5603003058030b410042800d40d81c1c0090400198841d61500c0c02d94046004122803d103800e005c8001d0075030340900000f40d8a0a50069480200020900c81000448511500d0018a602450f02404082c58111418031412444100140d410140c142c81003a039001040b25400c04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 376899811 1250 376898561 376898579
    0x106090e06060307050a18021207030e1b0303091315150207050a1203080403050c060103081c150b1812031225081003061a190506070209070c08070c 65
    0x20150501d4440d83c40380b070082045c0e0b21490705620854502c8040020b200d0141c240c240040c1c450800301001a00f0980304101c5a6a0036912076584c82401c5001ca0300c4c03080e5170380200c100700e030100ca101a07455402800171000701e20380743d6442c0c0104626114040340c0c0d0883d402603129145555008890441880e4030341e40b40090b41001039400402c000c440b5844c02c20320b4055502c480720344526001c0c2c1000700100c002428507020701e00b00c4006050010072500b00b07681d1390606016a070070003c1c0440340c002410b40c80180c20443e502501604090340b404e000101071622184943c160b004c00d80c40c89003940600030b04041580c0b000311508259242901456481c442680c0d80350180074000c0403040e01882465069038252074211101000c20082e0400c034145440b07071071405210b403415900090801e420302000e041d6044e141c50500b40807076021358003400700310003816015003640400d001c1c1a420400500041000d440c01010300d03500410325042001d40462203850304501944a030b40159000c0d0a1903104007e01a4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 376901061 1250 376899811 376899823
    0x40504140a0c050f0f2d0a080c040f050603030307030e010e10140a060303171b0a03020a08060306061503040215030c07031e080601270602010b19061403180106090e 72
    0x14044074030145d0340500314001001c4c500441c500d034094030290304814a01c2000200391031000c11004100001e442c1d51001116541c80c0705030350b140d009500f45168141c3e03106072401084c0c01250010023850035580c0b00c1604800400030440150450b6480302000b46968030140030103091056510390225800d840102c2601c0001d1025154960941c601300040021a134000e08402817040c80b0300c031300c00382e585075040d40403d124a11016040e12030000103d0110142d0180c0c002d1541da95142c9604405a840d4810142c0725001141c0c2140c1042122840c59110800c11000750b80c03062000703102041d10700300c0e0714004e00d49030412140c036080c5c04070000b0707039101307041d0403000c0403191000010b807242241100746001007406130050f00c4c650601c841901d1520045090381421060f0f410590740c00c441c01c07551201d009000c0d2418290040c00307110850100b118080791845240c05607030032034450103041b0b1014065080c282d400140035101e61241c12518100310b000c00c0c091200200150306021901f18482c00c1030070300b004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 376902311 1250 376901061 376901089
    0xb16080a0e030c10051611060406030903120b0102070501050705031611130207080702040b060c0105040501060609060503040b0412140c060a1109100e0607020306040f0b06010815040504140a0c05 85
    0x50394403813140701c0c900e9000040700e040e03181c1441c1b10b040c400c0d0545030036002c144403503487c00c1c1c2c05100424003081080e40350740a030078160b010b076071454990400009004210b801d05640c1d40d0051b00449420310003540600000c02d040f40c4203204807458020810b403d13115a00f05030200300d4292490003420b021524007038500b0302d41da080702102140f40100d680d0342c2c00c00c0f5100d98003000b809a0380790322244150790b48040c20b65400340e503580c0092106203080c0c44c2a038003c01c1e03540600b1004c50609880402c5013441002a684141c0d8040a028010b442da500e46000020f090f0903400108407001e6400000c400d40d00c00544800d42c8401d004007010f05100410005030341c1945401c01290703c0900410f041903a5400714a40c044e0440e00741100d44940305c070b001c0703078076031240c000b0181d01440340700c00340700400c080380100c901020701800401007143c49442c01158817003001d0b140c603443d9030000ca40300001841c0a60080d50050300c5050035524400b21807298906140c0007860aa0b0388000a460401140c00c0851482d500310b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 376903561 1250 376902311 376902319
    0x3031413120b0f010b1615051024080f061c03031b05090612060310180c0501030b0306070305060604032f042d020f072102030406090b16080a0e030c 65
    0x1560502c640007a09018801c03c62071006c5101d4045004d0100a007210b5404424804050202c0d00d005190240f40c520303075129642c030420b1041c1640081f440e0b80300300032401400c242d54544041e01c0741c0d1090f03291918041c1c0100c0e88510130100d6020001c201c6d00b001844030341300e51000b007980c0815150070304a030304e41454204c007809010000240d1965079401100c00d0648009d50003d4203840d11004285009003074405081210b10f17180d0728000644880d80e8018a00c0e01c2156032444035911100110143c81540d13000c0c0d178052748203501191149019801540d808138014061f01c0c00c0a03a291912200c41a0411031000400e01c2e8604900c101484100310031203c00054401f071000326003290301d500b50402e0f084c02c500b80c02c4a100f42c41c0092001c15404035105c8401c0c02c1c968075154040c50518201d64001d0710307904038500c456101d40c54105030002c4141c8044070a1900c51900e0b052070040c02c17015a9000700fa0140d0007000c0b6948400c0041d80b10b0026003e00c03051a81c030314100c15182d8080c907140450100721a441 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 376904811 1250 376903561 376903591
    0x6050a112b260a09060e0105011d01080c01090b0322140c0906090c0c0a1b0f0f0b09091e0a15050a150509011106040503070b0f1003031413120b 63
    0x221102d01c20429410480342080003418001500b460b500906001001c050154203001c0001020405809041a00080c24501d010103990305c600700d5a480c0217854070580032034608981000241411000f4507030003080305048040ba65039a100000c0205e00e10741003200c2080e804030340740703000b81020086561100000d03200a580340c10401c000076030620004080215190000818000503074040c810001c034654850207a4510316040704651142c480340d07001c0c3c4000c0500f84a00000c0c1c0b00100500b0720210360310b0001091030284480140302100c88014084c0388040b0004c20542c81c0f00d44888100c0e441010b00e03060001c0d050102d401503802403015036011a100f407110120034400c00ca031519099070212018144681d0303c00c01280180c0d501d0300040743c1e9085602030001004103210000c0300610007203229519610b116a80e80780c15615444044c0c1d00f034061003400080901c0001c0c0034400303000012030880a07550820b41c40000840c2514031a0300082030050403012084104203c1d9041940c0000325050303400c01c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 376906061 1250 376904811 376904867
    0x90a03021209040b13020703030e060411040203040206070b1f060201020702130c020f070b0405030601052b0206040504060b0904050c07020d03050a1e02030307020c010906050a112b 79
    0xda1941d5a12003440c486070002090b25a69955034040c00300040c001d06a400458822050706000717420030041500440c1c05c4c00c00480f1000c10110380c0c4da21550344000000c40009242c418407009410041080f600312808000c502e0105e035800c04c40b10b12079500c200ccc410b42c4055500007000074061255220500b5607006021100040c0d071024944054144400400180d50002000480ca864a0a4100c03d041c0c000c561700450034a0f0000014415a0401e0f001ca0300c050340e0720403d000f155083d015010040304446652008501200c0c20002111030008100c1410a501c07140001c044810941c4080c0d0031400000303040704642010301440e070744000000c0b421405c26030250042681161a00f20050400200203024000c4502500d50b80002d088102d80c7c5130408502c4401c080e580e83e1095070b056001d441031410b030040640c840c8284c44250741c00c0350742d89400c5c03103450b403800d032000800314408482500862102100400a1b1500c00d150380b90500380300c00f00704400c00e4018000d84102c0d4281302c140100e40704641 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 376907311 1250 376906061 376906063
    0x8070506070f2a08070f06050301090b012d02010f050103020d141501030309030b061e04020c0322050117010e06090403170f10061704060c020a050607050d05090a0302 73
    0x80c09154011400c107082006900d050400015590f00407843c3d810949a206440c0c803d251450041c2c442481c221008251281642100d0311102e10070500003410801c01803200820507040701d204800d041c18120902c40345900d012101501000141050229410381151229824010344042c0d030042ea00410442d411034001c100c0d03c041116024180d525112007080d9120380400140940c0d2245d142e00308000c0d616890010440380c8140320603216010441c02080b21842c210f003070700c0003c2e0f40b17001c00541c5c40384140d010700001e0341001c58100e0482c0018007010642c4400d00401c01c1c40c00b580c1c04064011181020005082904119031205840c50303604c00520043d1703803008246400590481d1418569512460200c3d00080400d40703010f118001902800a5100d00410460040d404028080b21312500c030342085615016801d024900ca00100b000308001c85e079154004001d02c01140305a030300c10802c0b0b850307886c903100007952036100050000032101c03003490040c0f05054110411001070660404140c03002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 376908561 1250 376907311 376907317
    0x4020903030910022103040204050105010302090901060f0216080106090c090e0c07060b10020d080a021e03040503040e241f080a0f06030501091b030302060c03091009060f0608070506 80
    0x180d0f0255100f41d5000708070a00030051903080c220129074081100501d2003414021b60002d0307130100e0180d0b0404001140b158024000c3c0d03880ba43c0060315500d002c0e8078000d400c458040e90040780c1c00640c02440179203520b00b002035004001a14191002244a40c603040c0210b0850340780203180420000000782c1844080e50700c002564121103030400c5d81c1e4641c040c6051074401450303100c480c15404511051011112500460081c000c176039651550000c035a10110709109034072403226074249000e100c03620401d9921880000d1608680148200d03800c1a454113050744034454240d5190503410a40c10f4126180c040d00b00750764039454001d8540ea084c07260142205442c01e24500c80c03840500032084001041152140d0007005548140c003010b101c5541d0364204240203180c0d602c4284c2d070b41016026441e0900d400c12400c0307000c80754160700809165942038a0301a407600041c0459115028407004e1855521442c003440007144d0240200146000c8040354140407604554403601c074580201504200ca5690301c03060f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 376909811 1250 376908561 376908577
    0xc070206040b13090c030e060a02041412100203180c100806060711092d07090b070f330c020606150405061303150621050115091a0402090303 62
    0x140d90311407801455060f0420010b4103d4029203140403034412205516030010200d000d0800b043d21015210002144260f00c650b0052010070152588100490f08180a008444020b00c5041d03511a000018070f00042e41d0098840420700802300381d190f00c0380c004c1445102815501100c0303415080001075005030420000912181c070074000403400c0801d0045010b2609214100201418040d2a0606000c20044c1111031030703030302444100b04c0f500400c0c01600c0045004600d43e849a4401030300d08141c5074025400000c4c1107558480b185c0d01e403000130b03628180060381200d07101300200b004840342c0c00840d8001c00200070b1b01070480c14004440e00494001c01d505810800a40e84419066081e1101c00c44174441d5030300c11600154001020340801e00300d0340710030b4140d9102e90300140d1900034110703142060300d441e40107040302c02c010348460400c8440389540c00001144600f00110720421a5020410580340b5588400341c500c1d106c1d241a000c030384021130241ca501400b11000c5081080344001b0940da4020114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 376911061 1250 376909811 376909829
    0x15050a0207090b120d050d0b06070b01030809011404031208161709160b0a27181b0e01030f0935160309091109040b060408030a0e03060c07020604 64
    0x40d5a030072603190100f00140c05110b0313000f100c0d190318000303100130540e900410312001400c0c42c0071000a002e140400c200c13011281c008035000d00030f03400c40e100d00b50709a12580b6410306009000d03031000002030103200a0f10003140104000c90300d000000002910428005103a0301606401c4071403020031310740040c20036107981c201d6105941d03566541c40e01b0f140340040c6602c21100c0c140507000d001480d10828801421164140e941c0d61000d204000607090b000030050503002c104880c1d8200510000d1000c1111140c0003011500c04640c05407580000c1e07102040244c07003040018184d248540300b650705805620041c1000c0d00c010031002c0c5141d1601905080c08113010000b080f54042e010503a03001c01110103074601d01c00b44126a4034003604000c113031000d413110022400f103031541100240c5050503208600e18000050002d42c9810880810440284050242d0320b510030000c2c480403c038014100046c00c84105140c0b40d4080b884481001c06141c00401000ca40345082c00f040f2201c01a02d0309410394040b01c11440c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 376912311 1250 376911061 376911071
    0x50316060b030102040e19050f18030403140c150c070b09061e0408060703180809010c051902090f0408070206071e08371d04090b0115050a020709 64
    0x11820303001802580d0314041d415800881d01040008a1001c06401400385c2c4181105150228000b603040d02c2c0c040311f4400b0f080d003220380054141010a06080500d494940c280c925103601c076500c240c00104400c2c00080340d50b000c0d10070b030901400c0054907404100080707591b840c1011861b00d000307a5100e6460191007203007800401c8004c00b5882d804143c51404400d194100480300a1409010044d0481e00c1400355501c03c550104103600d00170b2140b03000710a10489a00d00000d0700361514092544001903190400580f0311580e40031400c1480490760708003101c081140c5503c040d0040024184003e811108862219428000050100c6c400ca4141c142d0544007030b80c9401280c20100e001d40b208a190200030900c50504c042040041c03802040f82c01900d01d908a1610546d00104104841e404100001c3e0a02092a01c0b1410f01501602c0c54800710b01c075218291094650208081d1075020004540401d03081006101c4a00800c0403003040c03d0441c5409400c10078490300080d55480c1900c41c1e040103a41e19 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 376913561 1250 376912311 376912313
    0x10050907030903090f030602031f030b07110f0105090115080712032102030109050618092508010e0a140a0804091a040213050118120602030901060503071401030b0904050316 76
    0x1c0344c0c2d0500414441070340c1c043c2d80d039482c02c095010f075008440d4247c80c0d002003091074000318990300a200c16290407200c0c5409543e103290060301c0a0707106240d506040e102d910318108540c40c00b4002d05100e0030b0b407400007003005c90141d10310bc0300d081001c1c0c201442c1030b0000354082c44441c801c1c060742c4c640980c145c80c1011104251940c00111300a50401040e4101e0000001188020b0290805030103540306407101030302e40d001101c0741882a0402e940b0307401d540c4c11184c1c480d140c401021a00040351201031000c6d1901940d2114040c0c21214002c0b40c0a14079040040f5140501100056161803070014001074a004401c40e43d644c6050300c214041e030080260f031010011410425842c00b030a00040c0a00f003159a075441e008000c003100d459200b0faa001651034a11140968141180c03c011034a00d0200708582c05031642e0760201a40000703040c500c0c40d65880c580041d060b9010003c440003000c01d1036002d0031071440c40000400361043c003481ea9000d106ca480034000002c1b0000121054094017200000e400005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 376914811 1250 376913561 376913567
    0xa0c0f1d04020f0c070b2208060f0405030c0a0c0905090303070c03030236040b0a081513020a0b030406051303050a11010b09010b0a02010b030c1f05130f050910050907030903 76
    0x2d640d51050b503442245d41c046004a4288010000d04032558101c0301d0344d002030084140302041a0041041c10307045280403440d10642036440540041c45002500d0138059402905494681d880b801520b41803554002003100c0c400600c24903400400703104c099407441ca0148006050350445010040c1010342c001680004541082107441d8400307800e010303010b10704c5010801c44a000403490420303031103140b52042045261402618007001c440105000c0c3c5944070040400c01c4e69a10020228440a02c684c0c26040069503074002c51400340405540d62a103034100350410300125800101048204041ca003c4040402d4108040c1c0784c2c04245860b0460700c4080400050f03000d400c1611103660008141400851220002c030003902004440e80e008112000144007016a10039014181d180c001c5c41c440c201144454001c10140e0168600e820303c28900031021a204145c01095404078480841550040c8110728090b00f0940e00050710007031008005080c0320010f004000003805a00038956103564890030180 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 376916061 1250 376914811 376914817
    0x1202060a0c0b01180b040e060c07080c100912080402030a060e030d0504051e071a03060105070807052b120506011803051006050111030406030209180a0c0f1d04020f 72
    0xb030b0003980071545595680701d0b0340d40050724503110544207040055401e02da040c144521707110086034500820150b11040508803890340801c00545542034108090001034a00b0400005102e600400000e110303031071810002c0824900328140c504102c100000d000141e540007850b240c10940080002407181c540c0c03692a840e40c420682d842c4030b4035080804100a121002c1954003800d510401115403802c034103088a9115140c901540e91100c07030700b940d058a2002000c000d16880309042c1000ca20740000c2c2e45402d01141c000758000c5449600c0400c0c6034102c41d600c40f9410610800c000b4012018130103101c030140103450362020494190381c1d22000a8050780c07240b0048105c2145d0f61f050550743d5600c03804c12588903108440c048482d141041000106544182544502584880055070400e810520101d01a52145140c19030000c0ea940319400c41c2c10b62404840d000c0c0355005000107070801614070250001c0b4174030400d002070204040e401d0151101c15841030820010840d070040e51005c100001a003140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 376917311 1250 376916061 376916063
    0x3020a03062303100b010903060209040e031b0c0904050c0d0606170f0f0304030c06110c040e03070b06040218041808040b0c0c0a150c0309030206030c0a03050603071202060a0c 77
    0xc0718200e1450100c80c0700c294200b80c501d8040d01a81c00f0b20f07a40002020544050541e00b45c0050400760f0104041a041d80c0640301e120030007040810848031015140d0300e150407401c1d906500c406403070400700f60600300300001d0044020070794841501c0e2519407a0300d5181e5100308490382c0103c0c0f1124900381000151350214001c5c0803409020fc012003200c02c2c6840d5920071203454040d262040ca5901ea400c420000203540807640d008070307144501400c04204413030b0030980c995031070b455124a204402191f0f40394000e500404800d9801903441e25018100403284100c042c05050280c0d00c100302200010343c03c14043e000400f41940c0100d002100d074000103c090303000c01000340100c3c81c08900401c0c040200380003081c03250081000c55811960803410400088081e125100c04200c182071031100031070040c42c580340702c1c82c00388c1815034000f0b0350b039004502c5951088030f044c8250791002661000d402d806100c4d458001000340c000300f40060801c0c040100704080c4d0f1a000e44100004622416101d209490500c0340c6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 376918561 1250 376917311 376917329
    0x20f15040b0a09050a2108060a050a1509051c11010f0801090911040c03020310140904030f0e030a0c0602010f0e030306060304080d0903020d0f020d0801061b06060e0403090803040f0603020a0306 85
    0x441c480f0403000c506046c078a418400039900b0004038000c0e05e0698400c10540307500034084041c952810240040728410700111800b4003400950008032940c8448164042200d01c4030708a5481095117404500d85881001032814071106a2071041f07829444280709041d54025500042c43c1c0f001810044407600b80c41101030390150a0003040000140d0503005035000f50321440c1c444403595141d141c04c0b140003d008440c2508840302c0c00004011030300c6880444005070440c01e058100703621041c04642480c020340b5050341c00c0c0400103000c001701d613824070a4610300a0171000410403441d400d0a100c3e16880090a080e20540c1c0110100d4140300c448012138081c0041d03d1000c001d00281480c0c00703034880f00341ca81e0700f102203a01d448141c411180040345500c1d80e5981613840d0f681a80c00c001c1c0a80c1d19600d8040210710046800c1282c2c00068180d01c83d41e405482c5d070080c41c07022031802d80390081c6124042e40200760a9001030008014101c0341c0c2340c155040e07808a00700540c0351740c1040012001084c0651180b118 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 376919811 1250 376918561 376918583
    0xc01090203030726071203230f0f09011109040902040b120609060105090f1602030409021209010c0504080a0b0a1b03020a03140601090608040204060b0a020f15040b0a09050a 76
    0x801003460481071680c0c0c4204d4104180802c0750100314414043c100000d0501506103e4011480744250310011912a44616120318065000911001e0440440e0100644030000d010b0144098131040c0407a8040c144200034804003001c2c01c400d808130302030b403044180603d4645001004541d07880d000007110070405003421200410b8021042d42c1c8030030680d0102018000e8400204032410f25020b498803d06201c806000540c8400c1d000140c40f4048001c00301c05c500043c803020607d49403a000900c030048110f805400c80d41010032000d8212a01c4d01c0781841032280411040240150104440d40d03426001010f0708208d60b92801a80d000e01034502041c90000056414095420342560150018090a07501001040c03202000388100c05000d84625000c5281d600d002c05c045032041c0e0701d0a520a07c090000304401d030f0b44418403000d42d0011200c8a005d6001221035090305401001001000c603030b4440c0d210766a05040d16200000e80019121015682e103d605400030f11038100074840d0b1159010859040e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 376921061 1250 376919811 376919813
    0x9090f0118090525030b0702031303020609040e030a0e030c03151b0c070b03190b03060604111207020c090a02031005090403020a0c080c041d030904090f0f050a031e0e060c010902030307 81
    0x504c050190008a80c0d51440c44c022074022071000055990201503820104005410750f000c100c2d40b504036050040e8031540b01c0080c2c00800d1010710240409850680300c6d01921807441c0101401c02c0030702400c0e00e0090344940502d40a2980104982e500109481c1c041c90f0841c200280104d1144a810b41c880710b5440341340000129490340c00b0055101e1021b000542c00403008560001060319580005aa416031204000c52060300d05035001404000c9141202868607000d00301d03401103407404a80c94030140e004184d0f00d54142c109050203540c1300b01069401c40c60f40c41c06014040041425000c0c0c03601901d1110001800c0600821042c0a501e41005080758520380d6809220b5403450802c0b4018055800c00318502010010311004070350341c0c00684044c1d0f0034101f8850601c4000d040d481400e41e400d403d100861008143d0040c1e980942c02e0280300506503030f011608014000c90f00415a00d04421a204224402e840c0e00280c0c0245d01901120415a01c81485001602600c0c9403d0080c0d458000010000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 376922311 1250 376921061 376921123
    0x31b080c09070804050a0503070b07030f0915020306010c0b010b0d14040302190206040b1c1a092d0906061f0c02010f14040e1f1d090a0606090209090f01180905 70
    0x5841401641c0e014822200240c0c1cdc02002d8404c8400002c0042020045030a144596a00a141c0c4158103151441c0000e00688407061642e00a034411681e5290010b040d5890b85060b0040040d000c04510f540126420980d900942c1d81518081601c581100e040400c0c0440d92110211401011340f400d441c0c0d01c40441c1c0044004458040c0d4850056901e00040e8140050b05041e0034107141a00921031441079403150114411051070500306ca4800500c05400c0c842d06000000c224061402d18000300750038039000c0b0900582c030035074180c80e000340244100d18502c0c10391301081c1403409950a1910110202418206035050f0b6000c1c0302c1206258804a000f1980d0400ea14030a4032401048442900f2404401900c42800c02e050243c1d8242c1003c05640d00403c000c14442990091003507021a01e04005d42d0311481e08996081d0028810a900000c1030b0740b0702c1c9007007100160000380040e81d00e0902d514000e50b044021080001e94690700e07444040300310038080c0a10002c503544d40c008050030ac800c160301c6115 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 376923561 1250 376922311 376922333
    0x120b010306032f090702031c09080f0301061b0f020d14101505040203101217030a05040308060a0609120305070f030903050708010605030601031e020406031b080c09070804050a050307 80
    0x41c402e40003d40590800b504e81a031016010f804550051440c11a040680b5041018004482003400361a0700303408000820000050104011144c1700640300c0d4142100200360b40e445031641d41050f0024060100865200d89203c030322240c2c104c0751241a02c41900c2d1a0040c8400b0301065100e0340503040c1e5040030442d0980101300824542124214800e444404002c121700007500d0b10611900282000d1010200081c461107046004504a402c80c5585400400070303640100c44501103141c50b40240002c05401020440d0010000c483c240402428900014242402c40c400c22428006881201040c14000e0f8100c6464540009640040346541c0c10050144085407200f140c0c988144100014641c81c1840745c60f0590740d00902600440e469034980328080551038000c0038851500c030000f1b1005039901d201c0c0b50002c52140106803202d149188085010b04419031100d007841d00011210541e40e56807415150b40b1984605085103903883e281405440d200142c000282140300c0012040c0a02a6030311b92 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 376924811 1250 376923561 376923623
    0x5032a1b030708032d090c0406240f03090503070b01031208041121060a05011401030e030d02030c0f0d14100b03070f030f0603060209030708010903120b01030603 71
    0x4103100350851000455807403080e408050f040750424400f003001220407072010074450b8503d10f010307401c98140380c0041a15500584003a20180c5c40300d4003105c2c0a06142c02510014000d6118040046c21506041c50820000c1000c20741003060910121080038003a500160901d50850100d9444078031614014a82400a01081d1414014003003142c5e2002e1140e4121481240d001e02c490300f84c207e0300c0c81032000ba02c940d8071b00f180724410a08001600700c0020040e4034403500d18100b011a1030f51408a503003400207481140c0a04050400310641c02060340007003110901b15604a0041c2e5179a518420001e46015000340030040e10b01c0040c420b592a01190010086040031116400d8261074459084070583d0f954400c80850080500018280e9401346080b41205500e6086c08207580300d4516004c0100d070049d400480b240b69011480f400c8500303003003000720003a0140342c00810005400d40c0b000b030f02d002ca8460040303940b2900c460020509034031a801000003180c6c4a10520b603000c0311141b00c0391003800c80e444 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 376926061 1250 376924811 376924837
    0x30c070e011a0903010b0904030c031715010e040609020f0a0305010b030114010c020301060807081501140924030a06092609010f02011d03030906010603091205032a 72
    0x1401044000c0500300c414100c80b4280118100ea541c289040401600640c5150740d241d503980380040481e40f42c041e90588114402e50703401c9603240a9140140c1707043c1c0c03141004400400e07503804101400702c5420000040348000d00700110810600000a07018010681003d0702c002e0010600c07801204880b0060b04189903551814001a81c0394070042085000074411503280075001c6c00704205550080d01066101d50025002044850312003d50514000256006026541c0300c0c0000100c002040003444d800f5001e07880184008084d404001021540b0140007940c40047d8140000c4134000000c0701141c000f50090107660080300b080c14031342e00900092130180c403070000c10080e40096075522403001d4158190302c900d2604041801004540b8001d4644055041d9942d641c00b8100991145180341e01201d00d00c001541e40340b0f060065903052040680c01030702410300f000300c03000004130005c24503a4112010700d886610f0751341e2a1403112445000c1c2684000300110360b0301d2810f5004e6100b00a10304010000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 376927311 1250 376926061 376926073
    0x1803080c0d02061501082415180f150c07090509071d070807140f0708030604060501210c0926240402040c020102040e100602060106210c11030705030c 66
    0x1072543c1802121445240317000409480005141c0740c1c0ea040c20702262400d034664a4803041c4840041901c100d0515080794510401141c40c001040c0c4081d0b5805030004280c500103507e5541d40045100c210100e142100c1d02800440d040d038100c2d0003044480010300c44a001440790b030501001e40c603150201805007070030a240240603c9540601d80001a0050301c40359108012607031202d00848142016a25003058000c0030031140c14032002c0f6101130a03013a401a264155642010020007003140d4280c0d0009042c0441040c1401404419840c452541c408004c4041039000ca07141e01221894155048085400510b0215911031348921890600c286003100444004410200041d80c642140c4030300700103c0f90801c000070b80141130540041188440a000240c00c05480710784000410b1411a224008400b6003c5c0410109070704014160061880c0e003010314210260310709400f19044000c4030901f4440e100c5a02c0c14942d403081580d00c051304624420369407900c00c2864401d4480e40041c801f001d0502c103003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 376928561 1250 376927311 376927321
    0x150a03020d0501020c2e02210403050c1f0b221e05070e030d020c030a29010b070b100320150a110106150507140102040506030f0f090a0804061803080c0d0206 69
    0xb47c42256131101501503440e02c4000105004160024010411800c11805005807031031030900f00244200d0b50311002024030590101400301040384c010403030487c411303400c1c003520a10740c50074803600025071291100003040c0594002c01014486041d9003115081a20f0082001500d0342c0c4158000403451088098031502180d128049a584407200390059141c1c1000b4001300c00150b041805044c0c0704110300840c08480400c4100c0c1402417426844030050309800110701c0208640107500c0c4e03620401e011181000203045031102003c040700c0389560143e14420b4000140c06681e0407002204400008070341c690ba50300c2d0100c00030800860105199060340c00c2c0003010a401ba80d50810400c4801582d80c0e60703060821685035805401c1c24030980c510155800c01002c0380303984501c4002d512070100201e100c1414100300d015040e9035000103101040d241c0000e003076100044c00300411941100c5440c0b81c07041c2451006295243c0e92503d40d030002b0700131030000a10583c1480b0120340700c6140c80050702918080d64603 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 376929811 1250 376928561 376928653
    0x6080a030504140909061603140a02040303090e0f01030602070f020307140109090b0303092e03020a0e0f0f0906012703020108010b0a090b030c1603030e06150a03020d0501020c 77
    0x7091740c42e0040c640019000929583c03da56050302a8052481e000c1248030305503641d4407040d40f050b200590000d400040901c1070507000340420006048002d03e1040c107180012a03488004410701001b02641c0d0001402e9048c0f00b000c0d041540c0158006060f10115680c4030781d054101250361b0741843c0440c1303200300001501d00261183e0158040302402a6240410800820298100c07141c6005c0c540200c206048000140814208181440c59100183c0c2c23410302c050081c000d801d037260114494980c98003104690746441e0380404400c0c00030340e640159501c3d4100103940d2840e0a65500303220b14100e03a8108100b00600c1c244070200ca000b80c840450366600c1e00001c01080c840d8200000200344035400800842c00440d00075580080c03012602403c01c4241580c040c058081203c09a00090b1580240d4440d0350741032000e145c01c200b01783c40103030b43c010243c00850251101444043e00c5207800103104002e00c0310079011201c00b68114010703251000e00352222400400036528141d11446500d14042e410003030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 376931061 1250 376929811 376929829
    0x1080606120a06230102151015051e0a05220b0a0806040c0f0503130302071508090f0118080304050c0603100f0902030f0103060b0d0c090f050903040302060a0f0306080a03050414 78
    0x60b8003810000407c950030444c0910050645500101c003504005600c5083c0c0102e00a1888940d907001d660308150401c503101108400171044070900104a048140342d04070b0300321048009800c201144196110011020b80303803c5611104c20b03010000b4802000725446094248900000c41c2e0030840842c4026044862601512081c0b003c5082000400e00c0c04801061242c07215101e441140c11442c0c0310102e41d03480b441c0a58060011400c20800d00484100c1030242c51090608203000300117440780c84551060204112802602e0444004003042c1402818040c1c0b01c003400d070142c00383c2e50720309242c0600c43d1100702c984148034801c002c0c0c1c0000f040c482954003c03607010350250008540f4503402d58444900a0040c480e81c0d41c0d00c031040140e00c1d40014503480e48100280001a1300054074250040440150340009000a4080e0000c1005000582d141c0b010341e00c02060500d403001401c11120020f6000b03140541101080d1302c2036007014010503a000000744103035185030031a81d180302d48a40034098210707 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 376932311 1250 376931061 376931129
    0x9080a0f02210901140408011805010b12030307050c10051509070507080f0f120408031008190605090717010b1e150306010203071e1b06050901080606120a06 69
    0x280c2c2008102210341c421600c0044c0300c1e103424240c40c0b0b09540c80c00c02c603084642500c2c0840c04800030080034001d000b000e2180101500c0305594064401d10107400650b201d100c01032aa406111000c41d0a0034040705c100140308400140080412503070034848108a0340310036901c0320f1885201910f000481151107442a1115a980807800390f06103a806a603e00b800e412001050791015001d00c00f2a018032004400715000d68010711300f813503a0b0f09003094165541d68a90308500030503070040a20003801e0045030200c490250304568000b44a40301c0c1b0351001d080c601c0541c045080055098692010400306520400070020111502041540503140b0f4914008810860981c4203e0305490080680c1d5400b000b1940300c0d80510640380780504036a21aa540b840e00360350200186d00803131000c010480001900100e03400c4070712030841082c2c50a50010590301c2026245410004a100450026200e0030251102c100301c2081c81c04031480d1556030f541c01013108bc0300c0c00d00c0c08600000400601d0f5030344d000360b038440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 376933561 1250 376932311 376932373
    0x6090d0c11010302070b1504060f05090a0e01090c15030605040b010507060911130509060106020a05060a11040f0b120a02090d02040b1302070c1a090f011209080a0f02 73
    0x409040e250100354501d503240e0681070603020880b410001d5040a01c2501c41d04a072a41002400c41207014801290020b811049070104d407080b05108568403407080640c45046584041009108501c0b12405070012030801001c1001d07401021884440842e10f02000400d9660204003070342d81c440401c020740314910021408103604110190101342c2c103800484840e4010800701001b09180c20100e07d4485c644504510b000d03680c0c0041c4810100309000c6c0900400036407000b8020481a03450721500c42c18098494013145a03156040d40302c8101041c00d0720001c0503040428506140d07546003450540e800380c1c68400f010ba070140001042d015240c400c2d614441009890f101e4112800d9091200500d40c1104c030551000f81400c042000d000c080c002084040c0c03241100c00009450403d8000880c6011841c01c04442c0c4148121400c0d03803915081e40305509024a4403100c4c1e050304042180c0101040100030381100000220341c101d00350880300d01c0606c0042a400c640b0614181e100e40c2c01c2c0f0400309003251000b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 376934811 1250 376933561 376933577
    0xf010e0117070e0c040905090303010506120403111c0219030801091104090c05070302070b031b0f07063204051b1206040c05010e0301020c070618031b0806090d 70
    0x1450350780003803880710528040d00301c030201c0307484501d00d404100c01180c1c4442102c60006061011144500915410448c08401941107505002c0051124009d2a0301c42d91003040f41c1d800202410310613140501d004050300c4c250340301818085150320754107110b010300301c000d0f02c0303a030b03174020038242031000e604000e150035503202e00b010703420400d180d40a0900b8842a0702841814031002c1001d00ba02e202c2c5401000d0361392038a075070703d407428940139040107030707960091105400c144100441e16014a1b4000511581141c40e1551103000800110f500e0150b120050001c03803420f0740400c8207113950805000c404004132490b021440b4528000f180c017907000c40b4000c010350010505092040b190495545902070000d0074202d0781a49411172500c0e044088409503030600c080c132020821540c00050130000c1b0401a0020740c90300390034045807961240d05105010400c04107101c282440c00e500c142c41c0c4081c1d54004024050440c140409501f6400c01d03015242c428020380700450201500003810743c0ba03080307441d190303444 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 376936061 1250 376934811 376934819
    0x20406031a2d040902090a022d040b07020103090f050c030c060708041509080f010c0e0f09130c0909080403170a090b0307030603230f06060607150906050903070b0f010e01 75
    0x1c8140702c50b01c1040d4000e41c03141c41034070059907034488207072040d001030380b0041c1c0741c0c403900024040035007805d5071503001c440c28050000c02d803000d030f08100e50944129444481e62040c4e944012002041c0400000c0c00b04502030807614204030021501420110080301110712045280d81080702e0b610171106d0040c43e0203010002080028003218540c0303811895400c000342030036030b5404040d0401200c0166081d0f280d540f40045000c05400c10f640084030102520b01f19516036010700415092a0017425400068012030500347c10010b04c1901200904403001080c8820360303a41ca44082d807070304940811102256400c0130350210a07146030a81d1081282562940009450999160b0f0564006041d06007015205c00300030002c0f8803180c0301c604a840303051810688124181380964240540d82a090040c0d4002d48148903841e83d03007905032901150005400240a2012141503004080340e480050815042c2410024190b00100141505600900002e615a07440e925200d60801090045454980243c00140 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 376937311 1250 376936061 376936129
    0x40b0c13080c040e0d0e0d051c08070305010f060918060302040f0b01080105060708090105160b07110c1914040b0907021608030c07060c050c031c0908070b040b0913020406031a 77
    0x8501c00e0041d8181c41101e1440d031154905001c549449c0e40c04243d403072060081d00759040c440d140c014424820121032070b5043ca07030010f201803024400c0740d070784a00031180c00840341200d602041c01960700400c101f0500130341c1c41d40ea0700501381c1c1c4020360b80850800340001a140c10320804442003241d0280800380340089190054030590004e940c000c3c89860424050b03000180d072124018000c50b040d0711003040c6164106440352804d142d40b61503600400140140d550003884624841c420703602510030070b0510510101c0480d005014003d03070b07a40e1080711101800180d07a000708030f4050110030304440344000c40d11281055640d128251207480c91740d1040204028075445807040c507400340d200f00e059492915002c0002440d040014030a508100d403400301013000607410196640082003c0006003d120f4070f4502858403900a510410700c03c19800a00c001d0a03070b41d848222403110680703403001c5458a13154840140102210b1090403510104e899200c11f5519185014209554403d00c6190350700940008503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 376938561 1250 376937311 376937329
    0xf0f120c0e0408131d061903060b030a0c030b09071a0f090114032403010e1b04140106020303100501030207080a140c0106080f070906030b040b0c13080c040e0d0e 71
    0x42c2c030440d005104441d00c4d0403a88142c1d900410440158071400b60110003c5949284080c1c070b80e52240600d0010505000400d10503802180e8001100050402d03510020904140d48408001c1c1800408807000c010866602031087c02482080100c0d4083e5445551f1122440105003626500b100c0c20301c5000d0040270b40348001c040c01d0106150003605014060f80c0400c19810699001c07100d101d1041c0021001521030b10718500d05c040c01c4000307020ba65040b030301d8a912200381d580030040e41e0710118500071180d00c6641152000328110100392000f503940d100c000752603410035600840c2c03000952500086941c42402a25540740c3c0001401e49003102c40b803c00d4607601552090089400f90038049031160407070a1080c107009080c0c6c4005003444041c14140320b030605005400801035540b0302482030000c5803a480040c2e9000b41e01420700c0c0a40c4c4c80d81103910314a401040ba10180b000304814011030824804250429089020355040c44401200c07441191905810001d000000b01518038191aa04d01071801c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 376939811 1250 376938561 376938563
    0x130e09031b1f0e1203060d08030a090b04031d0d0c06030209031615091a03061504031e03020d02010c02030d020702150d05090d0e031b04150f0f120c0e04 67
    0x121562071502403220010400c0c04004814034039918590f07103205080920454000403840040d2034918682840051203464017400301a104c0c80340400002c0644803185d1007ea0f120390012805000c91034a40703001003804100100c03124100e8400f4103c0081814923001743c0381081d0b44000b040400f103082c000304400075000040d407990305100317410324a482440c181c41400042d0010310004802c6048000f0081c0c80c9010503405002e1070242c410107505016280019a0b8014004584804102c20009401d000d18081c0740c101408040070720b1082c0310134512522814564031f109800303944050150f200160700701d07000e01c222100960801c2010112002480d4000d002142c40249401001207407003c1c42c00b140d03000810701c186e819681e2824011024000c10400340045940c0c61f10100b02c0b9401c601282c0c03180308004c403010365005000044043d59489420100b18103801c109040081507071501106c0c4580241c1c49102a00088808089600101b564114800c5500503c0c0c01040701d16120120480d83e500400c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 376941061 1250 376939811 376939813
    0x31e0408090d06060f06050415051b010204061205090f0604110102012003040606120507050402181314070e0d0803070216090902100c0b040209040302100908130e09031b 74
    0x101040707664800c035003800300c280034500015a05040003189000c0080036040700045c010203020401180c01c0d540007039200001503240c8151503014511000c0040400880300d441b45500104020403038540c4030103128120301c0c8201041c416078542111a980310805004001c0050304204005000710300c000c0004500c03000d042c0300008075820402c4041180fa61007a40c0d810244c8000020b1009102560003580b024103182011103410014555805a80b10128070596006980100d44140700e40622800c01c060904064807801007400d032441d2010088c4400403488080c0344c1c062000c41c401522401740b92001007005810700390014015200c2584982008000c68110320544d40d0810003003000d0104080144602400400c01d840b0030b01c1000401e1a2200b403150810007030883c410041004002d805400030340550301c2e08565280c9040c06c9060440007001445500d003050072640412200000030300070081c020070001c100e01e49031b8520100c2c03100240c5140d50380f9031061040c004900c141d852a80d45098a181c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 376942311 1250 376941061 376941067
    0x6060406171b032a030d0f0203190507020d050307060f0513020d150608060a0501080d050301120c0305030a05130e1b0a1b08030a0b01020c1f02010b040504120212031e0408 75
    0x650001103100c2413801c07180c82114460205070203050800660068189506080c048400b0184000390391b8016006200c100d01c0c100502607170701d54040c90890300ea803500949801000c1c1101e080ca83d41d41c0d40040003c5441c280f4064002c44040ca81d44581e0340102000400035048041503000c11034801000d980c207882c4004e0a0b8107444103900306100c0c400040c400702000e0101858455088000c0f128141d0245034075801c08007a100e4144da002003160705441c40d1540c2103101c40e2031401c000d00c050802e03403c0186030741b01c001034081300513421602130641c121008030240944c9403910195020403105035507843e040d0616000c1451140d6808003e0800104a40360074203200000e50303101107403640141000d48401c1d03800000c0c003103c0840c83c099005140c10a00003020030002900116844035006003046a00c0004104002c0007107100f074126140005000384140401d04003401c085d201b10001ca0111000362280a003070a03179030b8456000b5288030305400404c4400290003403031412b142c0c07400240100d80c0041300f0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 376943561 1250 376942311 376942333
    0x10e18121c0e0105101a040807030f081902011a0a0819050f01060905040606050f0f01111f140f011206020f1207020c0301051308071502071406060406171b03 69
    0x4d106291243c00c00c0d10850010714903040003080a000d814010a050035801c000610092030001140c60460b0360042c2d00c82810002c50401ca4018000d0b080c03800743c10f07540c1d4082114490350540241400e90105404800e40035403903000c0100003071245c4500c164503000300d414203c01c0504000ea20720041c0c040c10642d0440d0020034013050031100030350454070100e5994000d00003803040510900c4043c10b010340e0590035814080c40010f01d00001070403814100721012134402c480003800d0000c00500b50251032092245e00d1382410f4a00901408400360500e1800c1c0e00015050030900500749048615212459002d0741e0780713450b100d01a40c443c0b0056054940108580891038292619261084c0c030b0b50382c06085407a07004810982515405410441d898204800040101710b90320215840568440f0303400d004507141c0751600b0007a002c1c40002600900207118640f0380080041180e0340700320011542042a1a02d800950346285292042a902c5d40e114112141e80c001c1d40c50120349050b200101100c40c40010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 376944811 1250 376943561 376943563
    0xf061b070c060f03140105010206150321030f0f0708040602160c06120b0603011d060a030b0906040501180819020703020415030236100b03010e18121c0e 67
    0x4a40c040000640c00d0f001000d4266490700c14031546981c464840c00003940f5040000b5075640000d468031b80082031510054032140e40400540c030200d4040800e4903001005205200310a030070440d50a039040b02510005150b2080002e9164460b420a850b076035043e4959407074810080d00328203c40d0301ea00c0012080600070905040e440c10041140e41e542e160740c108034020043c252000650711502440052006001116800c00c60145c8644c0d2103440c80c02598444c80015420050782d030001e00303050901c209101c04401c0115001d0304c03550180e030082c00146004401003901e4612010060201321040c00f40da02603d103c08410f2400356140d104482a1a1310380c0c00081c1202d44180203489044c015031020000c50510201039025032003070280e000b109200c8900207281d030429501c520160351400c000041c0c1c0210095100c10058a030340d0000d55141c1da1181c0c9010a0420b0035141c03c3c0c0c0f10b40003400c24441200e40055031100440404800d10f08140703040b81500b005980300703201d04407607035110010100c1e00a8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 376946061 1250 376944811 376944833
    0xf0c04030c180e010e060705090a0e07020a031b030507030c060b0a060e18011404090c030510051b092d0310020702010f081012030c06140403020f0f061b07 68
    0x303400d000d440480a0b01005800807200c564101d2a0380f07034100034120035200408580e090713000d4124201141c0d948002c0d80041c8603805e0719000b01540255030010710036070a0340050b07400c0e41a80310361100460b0b4814039030f1607039a004010b0303001400030300204441e40021744601c501d8150203104040c040b6000e03440070002406a8481d800110000f441c01da0004401d00e804211260a91000782c03454120b541402601c500c83c01d0f845200f2801542c6030b01801c810440c1c4e650a0000568121065541030700d00c180300e00e8080e0405a0303c0750115545000380340e2015030780d07400301c584001001301402260203480414145081c00a40b9045040440c800c0d40029500c0a01a06900714814100103a440043c0e1001600c03540385c0040040801420300c0030044c603078080d41061000d50f102e4503011141d1a201d498111180040c002c07008001301d0410802500d07514a0104550041c1c0c8a502956042e80c0c030140700b182e640700030300c1c0403442d80c0d40990041049040b400b18240803003000c000c0c81c18034004894803204403881c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 376947311 1250 376946061 376946069
    0x19031404170607090605090603060d050c0a0e10140303070f050f030a090f060903030f0302160602040b0702010806041109040b0d020301090503040e06060406080402100c06051023090f0c04030c 84
    0x14001c0010040f40b90740c00000b020180c491800c11504242143c00800d4090100802d9540200b440564043c01d1000170007031a400018010100604580c59000300d081c0176005549045006502038004a044020301810b10700d25a0041c00035030508000c2e40b0360202d10034028400395035a00950300d90b40540f400500040247d046a6120403000c07a240c4030b25910400385982c0000300300a0404400c0c80040c0d400083c40113030a13318034025032507102001d41c88158107a1007100810302440002c00180300c808505c05800101c0c000d80b100145a41c414040c00151000c55603520480602003116441c07a140941c40039420311000340a01c101d88046a010908540e8011419281c80c0d20102e000c000350841c80c0800ba512810603984c0c0d5082a20309007002e000d00f2400707000207100b00c0080f1150703514580700300d00b0483c910307800202c244481d0038000320300011119640a83c81c0e0712a501c90100e40c0c2003403240002c0401040c043c107501b00f82d5031420b0416940c89e0703014103220500802004000041251611140054 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 376948561 1250 376947311 376947313
    0x80d050d05060d120e0f090f01050105030408090d030c02010201050f0103020f120106081203041e050307080901030b15030109060f03260c0303040c181506030c020c04051014031903140417 82
    0x7000c101820070900200046e9075600c1001b240e4200141c003a264a0100d04540b8282006502c9403034600d82080d440c011003940c5504648550086414198010f4146181034000c4c0c000b0400c43d1941e43d94191080001d00020703411207841031000b402420000354600c5903003803800c00080d00302d441f0715013a0f042c440c003a0420000001e0100c148002d0010118514864070410000100c3d01d045558801d51a4011084043d01e4140040360b1044964001c5c0c20001e50300200802d44114881e025041940c03a820a000c0c072960640303404004a07040d14202c01541c2503c2d0403041c003c4c01600030303280d03940300c580707000000c01d400d170000717008010217814200007171b60140e480b90030958051420010b40003240c0c004600c01d052b1a03410301c222070380200c03089010b900c265030541c0b0300840c2803c04000d0582ca00030150000640191a250402881102150140c001d84030014a8906004610b400301a60340c842c104101d0048104001d4040019004250f8000d483d0b0741034100c43c7c01d1660f01c80c40c1100c4a0710100e241d24407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 376949811 1250 376948561 376948577
    0x240f09010f03050c06120705030402210a051b01120b0402210603100b01080604050601020309030a030809070518010b07150212061008010f060c02040e010203130c080d050d05060d12 79
    0x10480d01344130810300243c0590f00941004000941c20443c0310001d0180c5007803202c008086030940d00c404101003000c2011011040c400b48030071419540c0c4580c480000c0e5030350b0051744911042500e451150902c2810140d4618200304c2003030844800500c0398020032a4450b07402c1100d40140041c2891742d80511444021003281850040285810806081c41165002d4035014100c011a80c0154410fa00f00300d040d40c001030700c0d1362240010b07480c51048002d103542c1442000031400030164070840c214030444140d400d840340143c0c3e0310203100c5088048211040702c210080014410b207500b00000d440514020102042e00c50190b41300e01049038040b000e010000150f490402c2854148030002d9000c5005611b005482e0b50314002444600303a40724008c441c20041c0201c181c0096580701c2e04620400c2800300c008654a08000001d01c05088440c03004407540c0f02c00f140000b5041e440461400c0b04420316449692411981310300b00d40081500030046039010300c4074044000400e00040f80c46103203510321b84807411 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 376951061 1250 376949811 376949813
    0x406210615020d020102090901120f05030d0603050c0607230703060c0806040c080603031803010e010606030518070806270a08221206050603240709080105240f09010f03 74
    0x10a01222102da807044da801004004007507142c200e0310504690502c4c00100640f1a01c0c90010032a244962000d4220f1001150b00b514882003944803d00301e07403213007084030055242c00f800c0c0a2640a0303024054455003808401401c000c415044c0c1000d4000041c09990181b500d039516807003201c0d480d1114100040708141003000c141050702c24400179210509150f41d02d4038200000940d41d100b607540380201c800d92810386501544003504500e030428000c0c8000d012494076014000c0040c1400c03181c0c4070282c89056500c80c0300310750202d901c80903554964042c00e15903032103c443d03402091f14440c61580c0c00301541c031100d42840b01400421042c510600c54196a4481c1c44054825011134441078110f0490000e010040c5410104130104032551001c8081056521900001e0410040760708071414103803030b00c1e00508154050381c0f03e00d1043c0540e03250440380c29102c0348e1041c200c41d070840701850451919071081c2c0921210800d280019500105005454041900800c03040d40e0282c5c000c0070050301c814400d00c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 376952311 1250 376951061 376951063
    0xf052112010618090b040906020301080102030a0b1f1b0605040507090e0106270603051b100804020d03110f15180105060108070806030c12100e07050303040621061502 73
    0x1d00400d414500191103605504a15540803010312400110070340c0e50340d01c45200d81b185d42001041c6a00040211348941e507076103480e03010394401c942c84200986000c01c10549441d1000c920b043d03c443d025022006180b02e040b060300d00d1641e81910f0f8441d00411400d900c0000d1481c0121031103648a00080e2a4081ca00501c1e9010382d641404202c1003079041c00740511601140490035080d018a02c03103000040e040701010f41d0000c01e0181c001600e903000302c5c40107c0040d2150440215004000e55032410f841e400b5550403140c0700c600361002944202c800c1001008240300c8c924404500301c118085e1549021807212003840c00c20590790000b0f40110b1a030810070f4540c55041512001d007110070003403213985400c2c0c000a09000000700200d05000c24000400c019450411140c450580d0181419000444000305c0d00d95556060900c0400b150404490328103424010440000312003001d00214105030825009980c440e28942d00d600240180504d0f0114030601e030f0080c4030003440b041807201c0340b4181000000b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 376953561 1250 376952311 376952347
    0xe031c1e0e0a060e070b07030305060d02030114070f030615050c1e01090212011a060a020304030b041109150f010507050c09040f0b180619200d23040f0521 68
    0x991130301d03000b25030108a40d07a1a50201e90900d5814074002425548a030001001804c6800c0c01a4056182c901a140703400c01001a05002d102180c996080041d00e080d412010748040f400703004500c0c05400302e10500e4601807005400280c00c400305655010325020b000a254005a05a400300c680d100c904042c10f5080c00c03404460903155440003070080403036007100b44140c0d50b58468818003030380001a007080114803c4c81a140515400595104241050309000340c0c8c404101ca1000e100343d8840c00420010031403041d0699200c8000383c071402d918181c038001560f541e04a04800c0d01d150040450b00116540e0302e420b800c1c4220b00c645c006006d540c0480c01d0889207248010844640302c1d4458500e15080303200000e400380d000200007580300c90580d88005035406440301c541048844075000c0c07601ea461074400c2028040b44414007404024580d001c0060301424251107044214040221001c030700030441d1003d400c1e404900400c1120191088000c202249900040c510f00100b031000c5900c0c003406c0c0d100150 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 376954811 1250 376953561 376953581
    0x6050a06080c0a0e1206010f050f040c02150a1107050f0c030d0903020d060f140105030f0c0a0b0702060903060a0903091502100f0f15090e031c1e0e0a06 67
    0x501510302d000300001400d8401c03c18000107220400b61080385564429001035850480c44003500d540c1d595400c500c0d00034141038004d00d4801d4500c150180c660341010f100306e08450300e055009104071a101c0c0800400ca00000d09180342e540c1e26003240c2c0800c0024400240030b141c0c410001040081d06404909040003c406000ba11a402081e4240c081c160312600e84404c0d81c1d012500380303c003070100b0700d041002409407001c80c003580b900b01100b0580c84110b690502e8102e55003903003602c083c800109080c0c0d07200c091100d811035024984800038418405200080c041d10b600c00b0304268035042d05800000c0c640342040304d5007000c09842c3c1c00300780d040680c0044800010503806603103545205000101a448000c1040140c4e0400d588100240402c00d064116080024202d502000120041c1100800e84c4400d400341070360076400e062a00089071000001c451411407880130846450400c0c0702203001814200303403032a04000320032560000280c0603204200c5805140d40c02444505c440b07280810584100c4a5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 376956061 1250 376954811 376954817
    0x90519050a0914240405090a05070b1e0f0f0c030301030c0b0715050a1b020c03011d030a050f04090f050a0c080105060d020a0215090304080f030f04061b020d050106050a06 75
    0x1289902d8903501074100c2d40000c0c01c202c1c135044407103800b07450030740c400096071003183d21506140a220301c101002c2100064035002da0290f03100b150b03d0788048001c1e80f03d403035270036104001420070100203e000345006c0c22507001ea000c1014940f40c0d000c0c41c54003035600b2080081901d508000010400c00c865040402c000380302d00f038820380c1442056155044102c800020400b189501c840020f40c0c0721146500103900c40b030914141106c94086988001d43d20208021035078007a41c617188030b80c0b015020a4070050f00740c0d06110000c5160016040e4100e40540007400c21080d10f5605000101d0800c0080c01031150075030903150300094501d4140c0b20740e0700b40d030348074001a0280400d1400600903a1114002c60300b22106d14080541d030f03000140d404074034206c14001402108121281401183c0d01c000c0010070031980d43c0401c4445280544020544920425150000c1d0000410003002103d00529428400050304400012040b4080d004603c100504403001c8901c0c0c0d40d00c050a001074a40f1007501401f8041c245 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 376957311 1250 376956061 376956071
    0x190b0f01050315100806040c020a12210c03270525030f080d050105010f050904050c0d2c010b01050904051b12060f060f07030e01090519050a09 63
    0x1012528a0910114460400000200042c200c540e5050f60b9014620090800c003004001d110000341031a0056414a1003a81899218000c244c400035811030354070340280c01240c0c0052001019210f030222040b46800d0b5900c900d41043c030000c442d200c1c0a43d001130b2501e0100f20144007003e101c100c000c0e248445964103210b40d40342030210344001444203800c0310108404941c030142002c855050000c40d84020000c08410241c030081003203000c080c180c0c03010400d4060041d40d0300c450040d2401040b480828001a0f403e0040354090701d81a003107950054000440e0b03900d4010391044000940f4807610030310324410950b008003e54000005c105201000809008000d02c1100e035000900500c544801070348555120000709000380650301c40b0120380400c010702d150b510050711240345040300d0102d5255100710302c205040444c81c20507004540c5141c1240443c00e2803c0500e6070103440c2030320a1070700c49e81009188800855641c4a54411015140c00c80d1410841d80d49440c0411000100395009034031407134108 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 376958561 1250 376957311 376957331
    0xc1b09073c0504090f0506030604060902060d0c0c0b0f0621030c0a0c080c09071b030905060a0c0b01090b0a05090c0f0310050915100e0d0204050a020319 67
    0x4075489011a501500700c0022030700d400406812030001841071800315003104048a02a0000c0080c0200c3d651340350b0500140c01c1d0050702130222132044821940641040c07002900040cbc2ca5070140080500c0201a181404c0c0380c004da6108685c48846440d0115203d0031400b0300380034240441940c1306c40540024242c074a40030005c01e0300310705682c200b2019103246200010100134180250345240f050442110b410b12054213005030348130030758800c2a03510f004201d042d119604042d10224414075003078840c9102c0021064114031521601682601049401040850341d03541d036100030294104955036111a801180c03c000c00c20b640c042c0d0009100c207140c640c0c6043c582c0c442c85015030490314211000d100643da08000e02a42d807203498a030310030103040002008420010354508409032001034414500b243d90301d92510a01100035000340381d208115000c3c186696200d000341441890025042c22419452a40401d098600036218400301c2600401045424208201e880c201640303108024400c40c404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 376959811 1250 376958561 376958567
    0x100603031b050102070503280809030a050d14010602010e010b03010902030601030b070504270b01050325050f120414190312110705060a0f060503030301050d0302120c1b0907 76
    0x14024500745101107000150240442075064842c581e80000a882c2d5a10807044010001036401c61810b503a10240c522440d4414428480148a1802d201c015442e01582d10401d407600e4001c0000d03101081e03210003d1051424000c3c0501d4024102d64001041d1507168202150035200c1c0c20200900aa14001c00f100140c0c2d40005c203241180d411440382241c0d82c49151040300c152140360040000b2041401c0101280404039008101c0c03514803440c08c100b160074400c0111003522058036840349000602e01d4801e408031050503500d01000f280c2c20450300c0c00a103824210940c1c0c02414944240c4404502004140507941c441030314101e64400141c10b18206003600d00c1c2501c00e40050240400c51880140d041c1498541c2c4040e14070000058140d031282e080f440d001e17603603c40c221020301c0e0050030300000703000c1c0d6400c03401054150741d40200038500707613802c102c10701460386070005042d02140b1400d8040741c52001801c0040c01c4280180e400340c0782404040c0244800c15245aa0a0340240030750070400009940c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 376961061 1250 376959811 376959827
    0x22704060c17010b030417030f0a0e0304080106060c05060106031b0806030c0d050a030f031e020f040f0e0907061409041d1c090807030210080a09120305010810060303 73
    0x40d10000c005244002618115015640c0d001c07545a4003080800105140c0b02813405140306030703c58070001d006401502c001e118503001c159407840b6014150004101c05070f034540c01002406c00200100c0381056543c0d04d0a90070b64082c0d502c203a020900112a03c0107201c0180803c6014168a007001d1141001c402c604c601d0000690104404018281002c100580d0b400e00100403503200003801072158851030f040c25502c4003140c0320210041041642002ca409000b030052070039003000101800a45024000310602079848100082c0d1050010440429039050662807600504503240b0440503525000c07680303901d03020301d5801c1282030000792a120480480c1c054101d0f01e480300260340208106504c0ca5403100000d0061400810a000708210060741001c2c00350414801c15007a40c54a02480d41c2c0d003099501e903541400080c1d000b0f089100d1280d0514000c410054006500351800982e001407510b0311212425001402800640c0311401008004000c2003c03140c1c2c3c05a480080085174915540580405 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 376962311 1250 376961061 376961063
    0x601080c0f0d020417010b030114010603090c090c180b030f010b09060c1f06060809071505130306060f061803060b040b0402120906094c0504022704 65
    0x2000040c4a020281c03204041c0c800e04020704074203545994440f000e4a1414442c1d6032940c40d651f00c0e004013506c29103414000c0181c1104094107600c56a424048110f01802d01300909440d0543c1e003850014250f0010310503007070802d800395a10b5212200d81c0c40c4550305042554021003000c00140140080b020415910a044a100781c40c40c0f5075400c1e203840412428003894a00020305d000d01d42488050500340c1d1141448008409000c001441d210b03038081e40c9000d0282d6847d0000d61003074009000c1c0f0000d075204200c803504141445824285929032030308102115400440b0095226402008011003140c0060702914503810802c3d02051f48044090301c9108620028208a46a6040b0607417a11940d1107441200000341041d5925103c0c07100034007400300266000c4000d4803980000030002c0c1004160510b01e00c6044500500b00321410841030203000d00c2c15400c070f031014600a94004001c00301202100d030b400c1d000380c010a90349058010072280b25925801441500d400406000d0f14a400051043d802 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 376963561 1250 376962311 376962331
    0x10e0702100b0d020d03030911041a04020c120a0302130e130f1106070f0c0801140f0403090b0705060601021e0c0d14030703050309060a020703080c0d0f020d020a1403060108 76
    0x1600000d000100034944110f0060740001c00c090006091583c5a0000401c0c540501200001d182c84201404100c80c10041c03107440c0703680003e5a0070318620302900140030400d0000300f2124050000c0c0000f40b8140d000142c504003180e40090f00040703500a030f454030401007015004d00c04803071400304003112403141c075604c00610485108050804022190f136004862201c080c0106450b820545080981840b00d07020580307100130b2034400012802e205020740072114110b401860b906440b401e041c4441420f003d0422010711441d64404211038030313032002901c0c0807401400108040e00782070001908001c1e0b04415880c2c07154a02491002a11000803207901c1c051042d5038020f4000c14070300b022034803204581c000071940d00000070000d00b0b0540c0b18015602403900300098030807985a401920040744183c1200602258003900001c05100c9610040c0c000048541d40c040340c041c104610803822a4060866944216804980603a680e903219421400303a00880007103502d0750500c0c0b0006040c8a40007000c044070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 376964811 1250 376963561 376963571
    0xe0f07021609020d140a021333020f01050408030a0b0a030c1707030c17060703200c0309040606021c02061b071b151209200307080a0506010509010e070210 68
    0x10412117034040403040020280c68038913410840c4125020b540807140e10750490130b00e4100403c6807940c0511843c02800360003000585c0040071170070510703502c00404103c0154001d100d00e80c000c41e8401c0c02518842c1c1d1094070083d5803032400841d414200c40131650041e0184440f5401400001c00000050702914024001860311590030401705103401440c0d040106400008400000c200d0050113500c3c17880740d0284281d40c150741ea0f4080c204c0072107110740c412109075803040000b00e100c030341c514000f0241d090918081d00e01c0c203d1072401040070399440d03070304c100c005034420900032842c0e00c0300c00740fa4050000d41d480940301d9400c0c20500450f2852a030300100009860016135a42002020700c0002c011403004005440303c0e07540c815659042003c50003418003c603001d03a840d10300300344481c8a4a5240c03540b00140304c840703001039104d070000c00c614800d05c1900351080c400045001802040380d042d12512441c014003080d810b0005014040c2d01c10b80c132504e40d800c012003d200c800747d00443d2010340c00c10040702c0011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 376966061 1250 376964811 376964827
    0x20a060506030a02031f0e030712051809100305010605010c05100c0908100b03012307180b04091a01030b100503041a01080a06061a180a0f0e0f0702160902 68
    0x20420603a040000d50521621b100110608020740d00d20f4034544644d42c08212125148015680320300c1081c000030404603584190413030050040b8050040020b00030003030158081c2c460007243c803920702981d01c91240100d0309030030410400c0900030000035003000c1c0384c4450445156901c1c5e076610040002c0c807d504d41d4940800c06c2200c0d1186900100070301e03080b401c071285512416415402010ba00040a01a50030b2204007071004140106202c120620a2603c858907541c1d15011143c3c0610751814101d000b540580024602c1003e101030009400401300000d0b02c00c074800b41c0298001c000742070442c14941444034100440e03581e1041884180c2240c1002c2d030703681d0f6a52800303804084410344c1d103428012907070f00046000c0384006180f001a0344902e81c104030081c0c817028011101c0d0049103080e001c020040001200e0316402d0000c0148410000c1c2c6140e19032901c841034206180d043d6000340582a065404001c2111840690507800201c18000362501c1086408034084103a4035001d040007035a000601c2d80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 376967311 1250 376966061 376966063
    0x36010f18150e0307081201080c0607030305070e0604060201060503070509010b04030b130210080f07080f0c1b06070203071502070206040306090311010606080a0f02040807060c080d140109051303020a06050603 91
    0x41e0502e060a0183d80d950303031041c540310040743c02410301c0d400086902000031030303a2600000c004040500040046080c0803203503030124083c0400815800c10004605008140c545452001e800a04001d0b0000b0400b2410402450300c1c01c240c1c0e602940c4146020001004000042012241a00d030003080c3c610b050340d160b15503411303082c00c8900001e42080580c140c202500d035100c1d0065001c2c0820016880864031004000c9500395001d846840802920a01295450288400401100c0040c804244e4054000e00d507407070400400315001c4000da0000198181080204030038030705565080441103080131307440e8010602c9805907010040555558829200501d402280801419102c0c2d800a10045448100003005004113030390042035a8201048e14030065224029a015583c400c0c0090009030325001003201d007034100803002d03107280804000801d940803041c050599041d24660301030707035503501d41b5800b403040710310051040c45200d03e50036001b0700003980440e2071200260881c8000c80c640d03c4090020b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 376968561 1250 376967311 376967321
    0x1205100e0c12010308040302040c0509030c010f02121201080601060207080a15270201020609010902010c080a05041805100e01060516210324080a080336010f1815 71
    0x50000030142c2000008010248008100307803813007a40e06118111300030f8005c0e50f2501442140350380c113402c5100c10b60015440b5450b030440c804424412070b488803041600e8500c180e80102d8040c0c2d0dc1c2e083e400018415000c08010160041070640b00412000346440304031920ba400680005141e10304d283c129400a2910740c20010720710080e400c241d00b100358420b10044c40d40c03420300e4040703026005d0880080c040072010310482c0c210360f406841300410400e5079590218180e12a00701c138000d00c1030900c40403448084034980301d9440c2d4054a0009440c2c01c05001d0425407100550101c001c4403880c40060102e16402026204010a000314040c00b0003050303e0118a0a4000ca04500c48440d130045003000f129410342010205131011002e035054100e4501000c2081d10840c02210131a6210350010400110061700941d4400c41e1558407011034200c02580f0200f490306911120b480300c0000301c035462015030038411111001c0c80410100042d00b4091040032211100b1791010b8443c030854030740d4212843d90368003d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 376969811 1250 376968561 376968577
    0x9021c1103010e1c030e010b120607080f0603150414161707032003120c01090c050316060f090302180403030c03060f0915092307080708180c03060403030c1205100e0c 73
    0x7002e05000004491b5654070070490340300c40010074142c0400e91203543da68072240111405005069140514304100c078403a4009041141e05061600031503074170103014401c2c05003107100c080a03a4491840c140e59100700b120345582e0f41107150820401000080d595020021070075440f130412580e00c078032100019040038145509441e5420000400010541c070650000d1050382c810f0398415600c030b840c0d0050668a001c54030f14031201d0100000c0a0000900a0b68004028112868041d0645840f5030200f44201485510030010003580d0051108054050042036030010326450104030f80c81c40c0c0343c030780001c4200f180320700003405560701840b5910b40d4640c03040d00080c10001c2000d0002da0680308070f030340f01c146180c0444500c4001680105403290b12910f00540500c20559511040351100c0440c00300742661401b20481c00c3c40b44022087c0c891306e060110520540c000c0e140040c031b800010001801341c2010014142c0e01510305810040d05c1c880c00302040c0c0c2600c0a5800c907081c180d6605080d01344078820340310 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 376971061 1250 376969811 376969819
    0x30a02090c0307110c060405040216051002120703050402010806011404081509010612030203030c030a0623010906020d1e092616050d0609021c1103010e1c030e010b 72
    0x420422207810090045000b10341c00d503104503503020401403454036210807002507a80060100f00421032441c0070b8026254a60a08a41d03519110240c1da52500d00b81109906030038568000c40d500d07101d0024000e000b07602294604091005244c150700003001048003d0909050240003039020420300b00030800e880c00b400100c400c4030010b80c07986421402284049a450402d5801c0c610042030096105c40078042107545600294110703107402d02c0c640f44a41000344481e90040e51004000768200d0701c0211580c035245440c480140c05451100010300e0030142e0741180c0107660114601d20300e2107a02c0303c0c140071071440d03500301180d149050400460f9906581d070b014182000070030311a1111041d0310103d24041c44510340031101201202d11440030070300c0452251a90298800c1c880c2008030340e25800809200744014920114000c03074100080c02c0c200003440549003039403145000d041e40d040034882c21800015020007004080d96042d000341c0b214480f80542401c060310340c60b211020f2402500301d0040504018 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 376972311 1250 376971061 376971079
    0x30d0f110a050a1e12050306040902060d020d0e0f0c01081509090d020f07061b03020a050106141518010f020c100314070309050d0f050412080a020f0c0105030106030b030a02 76
    0x200304a60b44a03d240c105030740310b8a40404400c418203200382c000c0d0243c0c2e0300400220a0700c80a01044e10642c10051003140c01c16100c203595001691420001e02108007190710058403207502e1007140d4202e501a48000e02c09034008081c1011000d4001000c0c0240b52007460400303400e42e031350818003a84000b50f5a0058200802400f80441c9100100d100140384605608690844c242c2c2840941d4818080c81181c000c5050898030700b04804404110311b00507030080c0125030b000c80240d0346080c2169140c3d4803503070360a43d0b80d1020b1821803600a110408000002d8190b42c00c101545950390028071168400398140101c0c1003404400d03500a00030400000c000805015034100c1c0d03200f025015160385080c1802c4071004500007070245000b4464020059001001000c40c82c1120800761307950020400f00f04c003408410721001420703c25400401191520409403951148000c5a0291503c2034481000a96403c001c11030700301070342d120381a64110750842c500030554092000119003407524a07400030350048210 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 376973561 1250 376972311 376972313
    0xc051c1503050717030a0905061b06010e07030c0c02060d0504020a031e060b041503150e011506170c120a020d0c031a0d0206030f2205070f06030605030d0f110a 70
    0x42021012602c1382c4401604080403001c54030340700e118100c006008120101010700940c00e10402a10380440705400e8403c8094200c3e1500d403600000768000b61050350b0701c0d0108a51107602d809960038820641c20b041000010341c1c6e00040e6540950180140d00395500c0c0000340955452002501c011608044501400d003882e8102c148039043e036140139124242402400410740c105417152034034003207103000d40020550441d070380c0280d0a5100390402c11030a40b50240100244000c0c410b0320f8004410341c2e82c80c244c461404001500e8500b42400d40c1e035880c82503c040143c844420300807240d02c1d50201c24604110790351496504002c3c09024008542a0b142952070380500303406074410444403011210b940d1079090110708200d001000484020b420040c20300c041090902d541401b59080080c035046021580002040c4010750004aa001d41d03c0c2c0d4444207007001016504803104000d13019625040c00101c0c100004690b07641160300c50001004800c12060504610440e401201100e601e010b84140c0e40c21 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 376974811 1250 376973561 376973563
    0xc07210b0907090b180f25020f07090b010203190c0c0b09031513020906030a050d0c170306280906170601090203070207030f1a0c0309010f0c051c150305 67
    0x180c3c01052680c500c1d100b041c0d00245081d200700b1000c0a00040a0070660b55413950720448850701510912410300d04d2107408184800c40d900312000341d05070350300410035102282c2290b0b19020081d0f01088100e4035144508550341d07804030443c2e01c0e8100c0c5100d10f1807002d640c03480c1142d04130310f0b004d0040d1420340c0807680420548510300081038001070032022510080d4002e24042c0c0c601c1c10036030340d81c49070030751080380c01006092403131105611100081c2a60036a041545503142800c00e84080c500014207840900402c2043c20841d40c42c41520a031492400d500c0c2400128031080500001b600349084401d5200440380c00003c2080060460084284555a81d90745540e001b1042e0070b800761183d0041600225844885201352842460240d004101d403510703503218800e0244400000382c4409010a059450440c0a503912030b00aa8820000c15038038038196405034212501c2419454400e801c104040c00c01540c408159041444026010000d5269100d44800100100c000c142e2401e45916000024020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 376976061 1250 376974811 376974823
    0x70c1a0a02010b04050c0a03110f0301061e0206090d05180a060504090f1a060f0d052a03040c09020901210207030306050603010e0a05040206070206070b15060c07210b09 74
    0x2200750001d00044015604100a6510441d40c9400509080c0040c1101c40c4c840d17040000310004071a00320749080f0700800c0e150080e0744260044804504020341c6030501c0000e404514a604140d40302800c81030070305851180e02c2d1032141c0c0b4154101710300803800c000e0600a24801c08854800241008080340e61440040d0107500a0300c502c42c0418a00344904444001c5402200140503454000b800080035400c200003841d0041d00d141c03040400f090004941c1743c542445800e02484015154170b03404640386a410110240400341044030020600a000000f040f404218081c1e800c132000150701d4021100040b546521542d800c0c0b11410100b25a0042c0c45429900500d001030080c0d42c184616a01e03001803220034803080c810081e81150b072400158a00c1c403281d0100380c000d132006021030300d050400d4000900d10303001802c05451000083e81400078a8840380440703081c05105452140c03d0070300f040d071555240d190601c1000820030b00c0d0b1449000c00c00003004195135565018404c00b1650820019041d0341700 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 376977311 1250 376976061 376976077
    0x91e090a02270105191805090705010504270b060f03010e10050d0b1003060504060c0306151d030f0105070906030e010b0f0d0303110f0703081005030a08070c1a 70
    0x2d6144411001c800d52072050741254020001d58540059180200b80b002005580c0e91403c01d0101045000c80d00c0880003280d0514504110070215080c00c0441c00b135828114641e00290620508100070041d0075811038034810400c000301a44906440000c1c001800b0f80801450382c1d40c091400500001000d0001c0082c1d81a280c0704100c03c9a0342d41e400d4031074403210b030550140587c810074403000c103000203901400f440c0e40030b070412040c807140d1a03495403010b044e5070059904441d11611581e030350080725854415400102404898201b0f2444000c40150004003200d80400c0861511407101001d501d04100c4400d01403a41c074001c001c207161140700200010714500610001a08180607da03002c1c0050180c1f0291104c01000c0c1e001440450003042030040d0790b000110181030310707159449142517222000e42100f0703443c07602e5103555500341d28000f0304900380248544800000b0103001d2250361400a9040e407800d61103007801c0c3e51003400782403044014400fa4080d108000d0951160801811070b04060142d103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 376978417 1106 376977311 376977319
    0x1030507051905030703030e12010618020c0a0b040c080f0a0302151801090303051e040b06060703021203011d07050711060d0207061103010f1211091e090a02 69
    0x1103c4175500035804200544003604643c10110011011301009038000c008203801c00c01070411102038601e054850036404910662016410800540e0040c0c1000175041585461f140c66000900c40f4012040c245c06441e10708844524002900300a59901da0050724520704000510120217000a100681441d4420568601c54400f84960303110b4501a030340100d001d00d0a4580e46c5610101001c1c60840c0c081c00d8010000418840404190440070483e03c1598414003400d0480c6080d480c400591100b44000000103171221107c103030305030840a40103800e141941c071031304107407010f00800344050001000c0b42e903e0b418918280e4000c20740881a585d0042c14000240c42c0e13441102c041c0c111001040c100000140906404104641d00400e1029000b000d000015600c85481054541e078090103035690402040411f052040d410155564008164140b450a080120350f80c1849050981c01 = true := by decide +kernel

theorem cover : BRFrame.Cov 376798561 376978417 := by
  have h0 := BRFrame.cov_init 376798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 376798561 ≤ n) (h2 : n < 376978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
