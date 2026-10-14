-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3268
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:09:56.542982+00:00
-- url     : https://prove2.me/submissions/a88e9d60-d848-40d0-b18d-0ae3e3c69994

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 587589928 ≤ n < 587769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 587591178 1250 587589928 587589931
    0x6140a0509120c040f020d06050604150806040b0d14060c0310050d050106030812040b06030102161e020a09060e090309010801050603041704090501051c0b070e01020a1e14060103030e06090f09 84
    0xb0700001a036a41484547c40200c400580040d401403400348428400213084461591400809090500f20750b9070f0600001d014210b0300c0001d5800581c88240c41007046000140e48542e40000400e4a200da41c42e444800c605000884006d802c50312680c034100414200701d070071222550701036000840c80540780d440e0709031554020000d0341c0380aa07840c402c03c428001c509005a070440300c114000d41c5841c800c00701c0003141d10a0400003600c88420940c0c0780c04488510041031b2000d07540030300030380402a51181400000e058900c561055540c0b05030000b44002404800c5801c0e05038161550b04041e4200803c4c0026a000140100c41d070003880103150b00c4201d80c01c4050802440d0004012400d90305007801d10490b0191855518035440840c2980300011707800c4414558072120f0b034036085c40039101c00c0d40101e15020007514040c202087c1040660030380c03080c120700c580035517014000206001c5800082141d440c802448007400203401a1149900761405d03200421610600920304400000c3e4000020340c0c1000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 587592428 1250 587591178 587591201
    0x1806130501080901020702090a020f12090102180a030203030a03051b0f03040309050d05070501301d030a0f0e06070210020706080610080a0b0414010f06140a0509120c04 74
    0x4450400196a0002c102035120996000079401c0842603404904109005080029050303008190b04000c0380c1d00c11f09440400e12501c01e1302c4600d0130501c00d418000c3d400340d80c43c59660f28003052800e02c50300302803491100722a80a0021881d2290b1490201c000f040050221106805681240c0d2101d414007405002c0502038070740c40035664245882c000c0c040d11000d500c25405084d4010b682c10102c1d50105507401210020f0170010494004007507041c7da0768070900c198103040c45103141c080300e04a1640d4803480b800500980c0c07144080e000d2402d841e80d01c2c003c03100e5600000d440d6042c1c0801c1148600181794801e07001415041c00d007901c035800104066031070300c9030000503480020100840c50b4400440f40c0c004409480c100601c0d041c001d001400300c44000c15007a065500c4a4000c600358543c2e40c07040d60340000c03000c10303030559585a443c403e11048a40c402e03000000d105211600c180c0e40010101c0d0102c2d252503d0310b91800d41c2002c180840c08107801350030112409560880c41c25900c40c4c0c01024941344 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 587593678 1250 587592428 587592457
    0x5070305031201151d0f040f020903060a0e070618050405070806010f0f090e061201060e0f0a18151103010b0403020102100c091802070c240f0509061806 67
    0x11016a55800e030600e05900440c3c001078104c0e80c0d5040c10790000440750340f010406100c03164590410020403e595000100140c02502e02000c00c0e485248981c0a042811011001d40700c80d91240e1011801b65a10840c1080b01504500420407949000300d1540038001c256111041c078403944c0e0400581150021640d84011540c00800c200c51582e0000100f80e403110581444030a9024140f0020079500b81401060701008034007000c42c0c2e6a40d1400c810181400304840288030b42616034044a40c06102a00d45a0000d0b6925010442d00d4015020341c0f9251041030304901c142041e240c0b6480c2d08503040360302501d041c681d24001c048200040304025406803000704119a0342d80e146100091400301080c2c082e80b4141d00e0448244c49095120860700220380070040da1056100c51003940000901c00c0b000010680000c240e40007442801c840a01384080310405221000300040c003c040d50181c0d811042c0200040c800c004d41592803800340c0241ca800c0c1803102c4180943c1d04810b0201d400c41e44181c011f602c40a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 587594928 1250 587593678 587593687
    0x1104020304080a020c150d0b030f030414011706150a0309050a0302011a041407050903030412060501090609150e090a020a030804292d0706050402030c010201090b0c03070306030507030503 82
    0x11a010015a84082d00644401b805901004200302e424000c60741c5160409844e902032414594042150f403880d0f10120051b20707034890382c61a8010903076004c85102408949030410b80400e44110000641c0300f10350192080f81ca0f6850507032032041941c82403880e84289a590b10442010680400c11505814400c2d00000f032007007071001545100c025802c2c04035102c1c4d41070a0108070529a08844550010007a08080b921499500300080c01c0d80a5a00002441c44140200005002158010a040381c0000908010742c1c2d0f1519952000c1e14035004000182160300842003203840180384502d903110107194150b500038203c40d4005510741c091648180d0300407602042c2070014500c036445c55510302100c9030648100c0c02c5036400b01915805445110300d484001010980c4440441062020a4180c2c901225a44020a107803020091009441c181c1c003a215401246034154014410000f031107810650403c0b40d5510483e0f181e1190740010b03d80c104054071200000005402041f201e030185201c0d00145446 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 587596178 1250 587594928 587594947
    0x110108071202160201110c061206030c1f0905010507050613240914030301080721060c02061b0f0d0b030109060903110d17070507140609010c0e032107110402030408 72
    0x4070b00f1000055540790800314070b89450748d84420440d00a408845220b1050307544d004002820103056038081c6402c00445100810900046645080384000c40c1c0c0390000d5403500e0b2001103e050041c81b1005185504c20800306a03a01000000c10707800d20f00c1a64108001402c0c8071800e102002c0072043d14400da5250950780301088040b010120b00190b64000030340c203542c54454099600d0540b4821500c0203a9104031088034445014038801000703421032000c1c40891000f0784001e507250811a0007010f1560041290501c402402d401c480d4542c4030f00241e181443c40e0b006c54040203100c00c0820591542d41c40070752000244281c00790b040968025180c1c090520f080020140c1010904a0000100710702e0b0440708400300170580040381c100c1407501d01145c64926514001e10700d041311600c040540d11468013005400907054200c41c036950900c0d40c50503401015401030594940c046210012480d01500c41d0a460100000141151034003030b41104241018500c046001ca038400d86040c0d84001000070659003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 587597428 1250 587596178 587596187
    0x6041d01060609170601260114061207030b070e18070503060a0b0913090807020901240e06040510021501121202060403171503030d1d0a110108071202160201 69
    0x101844000d1410016101220310788504050049401d0740350108002d003c200d80c004011a540c804100080281000c405490003a01402b01c8a00b482000c4143e000c4d490920041480011a44c4c030903030104680e00ea01c2d10982c0c80c403250300758081d00220702071005003004402c080c0041c041c0a2944416942c0d00b094000d00c500f0100d0383e0001c0101800810001480f0380f2901500344100c1b68070303540001c02040d00e10301a0700501c01c2040107940580f00340004251400d148100a5144810500030f104080402e0b0040c0c1303228950f0014507601907000d120070849424070a40356100581c03584156501161f5000880c15040000c1c0c00c07620450101c07010f039808010b22200b44248d203595a00040a061400750b4000b00716a04048500e0700c0c00c00302001184940341c5002840b080082d004058a440c5c11084079602c1c000c140c80c849400c1035030785184901e0321a10f4045a441d01003604a40260040a03201c8011b6a000101410719010031000c002104402d0310180301901541710244902610414180001031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 587598678 1250 587597428 587597447
    0x6030f1f06051503010b0306010c050d17220209060303040e0112020f0a0819150204121104050f07031a04090f0203070602031309230c03041a060d0b06041d010606 71
    0x34020f20544450081c061a26015a81124585e040c01c036074075522000120344003566182e0081081c4251400c03498090713086240c0030030740e0b0740700120921030390703503418654842c44e071000f130281c401040360080c00c0d000d410502041a44000060116454240c0d03c400c18074405a01760b002d003414605440c00d02d411460103007a80d4101801c200d810b402c07080d040000c0107481e1541840c25960701400d000301c00c401c00c8094150742c0d0b07540c22044001c40d101d6071f0b0ba03601440e0130240c00000700e94410703403112014098030342031151038003600000900c0c0415a80703698003980200940848408a0680d038103640e80301e581c1702c1c002c0301185032244140000c262924818146046000c0e001641035400a00000c018001001920821603849083c08101c044000d030b682000e816414003040c040b14005002c0010b02c8034188c00550069204602c03034174140486410100c00030310103031a4246d102c0090601c12011030825022140c02c044010000034101e001044020f1079000802c400302181e9448039020010990090a001e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 587599928 1250 587598678 587598689
    0x90803040b040501081008010203010b1804020a0e06030a3c0e06160509060406270506070f02220f0b010e060a080403211e0b011706030f1f06 62
    0x860825041520200190141e400740310b04004055000644c0105240422001001c820000310f5a81d6140c2c0841d1100360300401c14400880c0682050200364100381c400c80745980140d9641101c0140180c0410002c0c2e840a09100342c4103403039513172401005c403810041d00c40d02100d032845130f5101806038003c809000c080000040000740b501c130b10340304024008242c050713108426030858403c11040b0001601e4501604002503008070000c9004107500c1e0300130701c80f800403241104190305880d40c510110702002c1c107030f17004032600420309110400009051841006002d8801000c042c903840d148003070995042464800c0c0018161901c060f00541102480f504004c2c002c2072a081c00180b030120003180c500d100c3d10000d40308120004001a003410303c00c000c000100c0e54030200c00385080c000d0f40301f400c028018426014a201a1181e00126442c06500c20f410082d90107850714801c03c5003041000c00000c2004100c99014080d125120868401c140103800340d902030048050100c10380110391500b101c0f01e40c2c109 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 587601178 1250 587599928 587599933
    0x108151302010c0b06041d03180a15081e0403031a01020c1f032d1404030e0d060219020f0f0a0b16020705060d05370f110304120908 58
    0x100d80540d80c00888242e4140c0c020480782d81c66100c11000c20700030440c08401e034034068941080d0070072003c0044010072200a12a410440d054056020066150020701c10f100e1002e402001c05241c590243d605142d208181c14610040030056011280c03020f40220340890000f580c1c5c080e11a0142040d0354022030707040c0284002c126262801d40803500303c0e01e1408040b00848410303003908940a10a801511048003007490010150b0001c012500024010136214280340f0306001c59200b41c2c0c4142d0040922454040d65025030b0688100c05010802c41c465100343d44c3c40350200641c00c444080140b1400000d0380a600501e06944d0080b6018200300c0071000c0400d464100c03000742c1c00880c40d242a4a50040200a2155040380048506911380502c80d4030454100a010401c808090002e5010301d10814245590803110199014408660020f0080386204010380e0344524a10030200c0e0f02142002d80f5481000502040304801c803a0075403c00c403000c03101c001c0c5803150302e000c040c5c4c4140c02100038106c0400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 587602428 1250 587601178 587601211
    0xa05100303050c070302030a0c090c0810060e010207030c0b12010b0301060f180e190509060412032f040501120c090303080402060d15051915030b1206010815 69
    0x11800561651101078100140030a50202140007032000130300031a070050844440c80d542d072070322841120a40c4102605c141c07130178000d00801c40c00748203200d2049043c6100100820b00b04801561040e208085035030452080074004000074a2025074000907041d1440030f142c5030a0213450064100c036051300300e681c1d03848050004101d49070300030b80501440c0220342031405100140414400d0034440551000c400c4d11040c40a0004c1c038540034414000c582da0000381440907554071403d0980e2942e054900a0108500e0030800c5980341c40317a400680000007280d104004450040e180d282418cc0509070003054010008041015680110000015181c40242440694001c030b4024000c00442c1c48050203001e51580010119680d01041f601000c4d04000100704414441003101440940c9025090261040d00350300754010030343c1030041040301c8020000003003131041c0750000c5005d40820103440c1d0b000301c43c82c0f00040301032009000075406444108018130010305180b051081d00c05c4040c000c0e188d424907601 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 587603678 1250 587602428 587602441
    0x6040315051306020712030c0c030e04020a0302090316151d061308030c010504020118050307180e0d050304050d140706200c2103010f1203031b030f050a05 68
    0x1580c90380c119010690004807070361614010002c600321904010a000d01c0056110100101440c0d801000c0d02c03903030781c10020404c42c00c80a803148480722030064041140d119144110f85025002400030341114503001d8100750a08000c00d00c1d2840003440c0c0c6040300150b6805200c44003001c0e2a44050400c54909900c00c820718505040c08c003444018140c0c02480d00003503480d155905808002c0081000030120ba540f8041d0309030303041c020b1401350380407800100d8015000f058582c1a1402c08151500100546902480c0a4243c0d00c4103d81c040c400203002e48858151345d50720340600050b01c000113261115540c0c7d2400b4504035042446801c03c407011f100c0541d0104141c0400384d03003601c01065005030300040340311012107902041700d004100700503031242c00141c02e80c2e5010041544450300907061501d11108424460300012400f09025040d5003021880040003078840d04200040c49500030704000800c021014564040044030141b0031000c03d44500340000e4a50b80e5107d03442e44040081c1e410010b90801a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 587604928 1250 587603678 587603693
    0xd0f0e0a0302151b300103080d050f010501120b04090206070b0a0f020a09090f090c08030a09090e25080102030a1a0d030206130201031103150316030512030a1b0509040b060403 77
    0x1040d043d02d000d40248040c170600b0749240b14143d4040705d04964503000c1d03070340340392208040d07100030301c1040c0c00d0f82420082079090f410580d6841c1a514142c443c080802d41c130300071040041149500565005407500200405619010010328665001c0e01e284c4c07506241c49100301c4c007614190840c400348944100903800c0d1043c1c4c0b2910003402d41e170100342c3c0031500f880303603039059006800c44150180401002000000d03049200000810505101c1d48480b60314650780d07943c80c0121242d06403100300300d400008a4102e21034210603401502d5500d491460395068a8142c0d0508903001280e0000302950384140c0c90b01d40e08900e00e070103260014101e0340e04000d10300ca9a4001d45a803400b825410582198118030070442e800398010051121143c1da0b180e07103d242950000d5612511071165034001d00844d800c081c401c0e4064102c0c0c00540384c10a00038000f02805c48100f160a03440101050b83c42d6649417201000041451f0440764104240d035500c9403030320141801c203c2101c1c245901d0501c00c401c200010400115503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 587606178 1250 587604928 587604937
    0x6040909061409060f010b031801050709050114040f1203050f07050a0201034b020d06030303140408070f030512040b071115010e06060705070603020d05060a0b0d0f0e0a0302151b 78
    0x2084a440c0c990b00d27041e80c0c40b80c00f0042091ba50800c1d5007400100240b16510503140340440d60242da811000c0100c05005950174401c900482c948411618001d110312501401e130004124840d14046141000464a41d14103800c5002c1c2243d00390031000b001b2040d580d040c0211140e080240740c21800c00304c043c00c10011402448800c440c07040200b1080d049010038460301c16000c9910582041d5503491000722410014191070004401181c50070890302019404400314500c80c40d4404a95032400c052521400340f40d401d0002e08808001003048502c4010b00c503c03188074083c620554950040f400c10f100054210103014a560071107a015505803c0c002000243e030904448400d01e1071304542d1189004100c480c801c0e00070103001c610a211001600641c1a402443c4d05031480e8020070803500e9807010081c400030584108c000402080c4204112203209901c14151204280c83c0098107010311154181802c80d01c84003500075070000310a807071440034514606a40201d011880c1d4094500149012001d8001d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 587607428 1250 587606178 587606189
    0xc05030d0e062205180a0c0806030a0b0a0908071b05060307021009050c0607080a081b09040c0c1b05150301061b0f1a01060f080702061506040909061409060f01 70
    0xa0f5144007142d51400c080500042c0c40050090107603113400c40f005051151003552072540540c94071701d80000d90b920a024041c09aa0000c000c0c00054910341c84902899001400c682d10751603076540c82a0001c0c20600081002074414112007026100250072018038600702c4e448a030090008108029005a01040102520303e01ca40002040030950400c03e14150f0354102c09034222100003055401e01034850003500760070b031303d41d541c101043d03841003440b8100700d8228441904e41c260510550210b8903003600400300c200c00a141034041c20250f41c03540038041000d400110004110b0040500050410042e4070070503404290105265524104008108074964655004900c800110120810401340040d4101e00d4001000390010340c00d03d5a4540d15000030b00c501004908a20301c1460610700684401d8403031041d940107171650ba6a0003403403141c03016804000d964000c000b04004035001c41d15100b40d0000600030b15001507030545030800c0c0c0d1184c080103041d40e200ca03031000d002c000701490b642030710505407803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 587608678 1250 587607428 587607457
    0xf0f140f070e0d051e01061e1a0f0c0d0f020c060304020a090203131b170a03020d030f021b060f06240703091d0619050f041a06070c05030d0e06 63
    0x268642441ca0800100d0305c0240d110340c41843d0004003626054003c02c0032368000c2e00308030004006181b501e00350007590780700e207410201140508e405a51110400f510126000c0900c031840d084a1392449414509508468808034807000802c424181c0d0412005000c5001036402ea4910f041a40000c0c204100501c030348a03469070000300040d1142c40404241807003581c00320300d0340c900d403a548d405a210b50403603006444403503141070381c40d19103103200080c03140002c2d030944c01030142c88150f610110047c041040002901a070204648208020080603900701c1c1c4c6407003c06403c090800c0104102c0c0190017820841c03107552205c964034800d030b00c06030540c00c45011070004103a030342d00503240584501d01c507540701d0384225504403115400c880c1a4511780d17101d01c0701120302041544180c000c44c8403081c103134043c80e82c00c03258000408000d4181548454061031043d021400458039a00006ea02a40310100480e000000f2610820a90a08001c40c6995060a04040d24408002000b240c15409a85401e00014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 587609928 1250 587608678 587608699
    0x801140d2d050a050d050304020d0b0709050a06051308030c12090a050913120201020c150a020c1e010b060301051315051017010f030b0606030a0f0f140f070e 69
    0x4429035041c0400c0c081051420916018142c102981c82d81150b60044d5214091440072080c5c032445201100e101d40e6008200200c80302c0c160701d40c5502d58800600b494140040d43c0004501035071703503009010050019540e01a5210741c01e26040c000c61010b5800320700d0701d60043c4504007a121000c2208102104294003082d01c071036200340090180416076000036040403902052103142500814412851402100c58402140100310100c0c00c0380b041542c0100c1e59007003405162210600c50b5040f64010314032344009403c2011110703c050030710802c90080070524042c4c200c2e600c030100b800e0045900c02c4008590b0f103400c561605020841c0801c550b4504400c045e51081ca10043c1002001c0d008003501019101102d4000c41c4c079000751243d04924913504880312030400001c0e000001ea0261810380e94444d14403859030b1201c80c01d01400f0782010700b0010f10310791a0f851a111380b810502c5401242d10f0600800f00307081d09400c4171140000d00241c40403001070680e40030022705541080f510b0125100603079a8440300e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 587611178 1250 587609928 587609963
    0x103110112050c131e061b0f11180c0a0e01110607030507020601060c0503040b0703030e0604030e0f040504020328060e060708010b030f06060a022a1809100b0a0806160801140d 77
    0xc0055987c0014032005107665071109120140c800c0e849842400d43c0da14903941c100c40e1400f0a904d500301c5040d134482070b00f0003880700002d214070494101c103401814030f1041d400d0b0004201d4204035040b5640e900180c1e4410030030800030360401c01940140380509002c06115030305d840300c07501c0b81b24a005c0c1e0010039500180c40d4007058071940c0480e10845c41f0400703840031420f05240052100d42c4102c1c246105440380c461640300c40c902442158041e90740180104110308841103100c0c1c0d0030903145480c0d00c81c025980b10020120795240a17141c15442c490010340103e00e4a010301400015040e00410824a030500070899403103548005181c018000315021034940e442d1040491030f026280c5c81c48101e01251113020740c0281012021008072920440d4481c108e4000e04d072501140340070031941f00c40302e0740c003030800d0008094482c0e00000c1c0c1100041d08050020b619140b40c41c0c64240c064030842180ca1016842e900c100d90706c840128050024500d00c580f0041c68600056102e00d400303c00505040c4148038541d65 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 587612428 1250 587611178 587611217
    0xb010509041e03022a0d02040507030207050f0109020102060a2f130b030901180c1e090507020a020406050a06052a01231506030103110112050c131e06 66
    0xc0026844034202c80754007460003e40301c002c0012444498020b03040c51740c1c00c0c07100c1c02d48a801d030508058200340a00240e0340800020b00000740c07011090550803c21000030510a00904200103002400070a00d00c2452000a00d0039030000d08030030040d4606154540c6c2c1c1a01c100080218401c60808a0410f0011046c082058440e00802c1c1c1e1200c1c40000c40003032107401d18800765104000b000020800c12070003103007401411410760001098045900e00c14062032103140d1072110842d221407550f1034142e072607400309002c83e0b07020360710800541c2c00400707440704600c0c0c035001e828082d110544002010710b103440c102504900603640c1c85151107e00301042c22170754414001d9a44029a540000d00c900100140521490380d405645800300d1803c1d000006c28481c40001032800b0040c0182001d8a180c0c81c40d160001e0710150070f12060b04100e00d1400c0c6a083e40d10a004e1a8007601d440300d40b49942e400204040c04419107079621250000510300c200400c60300b4081e5000c0100c916600f0248038018100c46e0421 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 587613678 1250 587612428 587612453
    0x1d0f01050d1b0903150203010e06011107030b100513110d0b0d020907050901090f0e0408090d0b040b090c0d0809061b060412140316032c0d17040b01050904 68
    0x84051031100020b1015501c0204001101d00904a07003191200c0001000240d10003401424000e2140e900444c0c0c265108041112409032540142c1d4040c039140d82d94040c444070241d446020043e00b40c1c106120034034000450030b0940c00c2d80401002016407840030003100780201e5004404507960f4095a0138180c680e0500c650b40c282e40100183c0c03862410510107407158001825060000c0c1c9014000308043d00441001d500359181c8100016169035165694201540000b98041d00082d060203030704000303800e280e0030501072807051640800364648032041a00d4140c14103045031103414083c00002c04100014101c3e07041e01801c1d20f115544081c01101072060203e00e0701010803902c6200e08220030710004545500402e043c0b03659074050350b84204409223060000b601e00b40c000c80000d22481481e039000e40e0050071034800009802606054890901c0b80507604146441d2098020b00d9000c81039a80c05802c801c01030b02c410341c1790807003420aa111b0030713400e820501a003402140c2030404502444451555079 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 587614928 1250 587613678 587613701
    0xd080c090d060203180d170408090a1e05030118021509030f030a020102090a0906062712030917060408030a0e07030b07180b0307050a03020d0b03070f061d0f01050d 72
    0x3590390f0300f0010310b00300d0007030355050f14110344d0b020759000000210b00c100c47c2e2140c0700c0001d2406480c01c3d251510f907045a40e03c0458030582c824440e00d000500c40c840445064032215841d000355101324a89414542515500c45071080b0070300c5020039002c01a41ca980c1c480c0403d8850041ca16115104d02011900c0d0030080034202d00184000b00e02400001c2d070540050407131030029074181041030f1345c400e80174080c0c1e540d60107408007145040e900d030422012110016040750000212041c0880d64400794030200160112081c0d0010b44c2022050010340300d82c151b0032045807442c01c005c02c010f15003503d801c9401c4c000507003203155480d1501c000001d900002c10442c0003464000030890258140b22601800310b001c5070404000398040d4039000212901c00b102580d11482c0300e41c0b5018940388180d01c0c114000e500c0081100e0046030350301614110f5850801c0b004003d4040d50042d10300c200d0038060b02800c564142640342c0d030030784004442c81c040c1d40c5803600201119142828481c3c1c03913003105070061025200d4245e41c07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 587616178 1250 587614928 587614931
    0x216091d030c0313050306040201140304020414010b0409201902030408010c030906050708010303020c21060109091b030f02012a08032208030609070207030b0c18030d080c090d06 78
    0x20710740b03500c010004084807944020300d040d800d9500c0c0181619054100c2e400b03030214249801d1840c12040d8400199406440140005000320540c192404188020307040015582400b0400344000c0c20b682c800d50b0a0300c5800140c050031140d144080030b80c1e91241e03207100d031503201000154008c02802081034902800320340000b48805c051400700100145500340e001e660043c103010101d00f905000300c4409043c0e0b03405901078080300b140780d01030161030720031070040d44070384417048000e00442082480342a0107415214408160003519041081c10890118400000c0c425440030400000781c1d5000000c076810350a081200b414920004480394644611840702120180071115004000300000254070941100c2503411140d0318a400229050400d0040248540750800100d0382c1403a00824455101d20203104407002c1030744a035280c1078541700c140da440c00c0e084008246c0100003818108541014401070380200800d2580000040c0070300700180c40151881000034100d541500c40d00c00096074182c01000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 587617428 1250 587616178 587616187
    0x6180304090204270e060c0c030d0e3007150f020304051c1713060b031006060f0e0303030417271311040e070e180907060216091d03 58
    0x91302c08400103a812400340840005a00390402d4644145840c40c140d1500400690755480c0e00000c0702e5000d0080202c040c07200b403050b1401c000b103034050790f006054054003400c40264064034090b9450f844a464907694510a03001c20503046229040d41c91140d00074004044144694140f0001803000090039101680000104414808000354040c110b100203049032860b0079440204460700203400c11007005804824000ca800d18541d00b090708003460281c0070000d50142041d001a1500b040e0510055000d03459004c00c11615800543c1d40c02200824209900030450610011783c883c0702c0200000c00d000c18414a01c04800c2c64007041e1440c7e1300020905008421001c110880038080901c105441200c5408c01e90ba0084e03d5802503aa01d000d401205038201030915102c40803d150042100c0200000078813502400d54400d46503c581400e103a0403207101e8100750320800d0a08181d41c00c0442550710451046084400b0600e4480454120038000a4000c880c1d24030343d111800c080702805418070010130f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 587618678 1250 587617428 587617439
    0x9230c04090612030f0e061806190809010c0e0907111203190509070503030a05160206120405100e300304060c1d150f0c070608010602010c020a0506180304090204 71
    0x814441c1491300075142c808283e1240b80089070754450154810f90000428013011040c0d0003c2070600c80c030701c4401441107045c140c2c000c0e52112440c115032403640000d404803080c0002228203119051a0843d54540342185410314000f01c0c0e00804090020410410002c40580b1b500702c044c0121780100003064846503480c103000441d5142c2ca100c06000c9200146040040b4980030301c005847c0007214806400746007085c1200c1ca00b80c2e01c5030000c2c4514101c3e02c2402d0041380050743d41d080240f2044011000d8404141418141149403850750020301c5c003464036258440500002c0000c0752201130345d5020081c0a14030100c4030036499411040f000e0005203101100f0f01c800c004013600441c140c41425035031484c0360905029400540d028500546400c800141c41500c2c4540c0301c03c0013000d0482840904030300d021086002d003890044158004000216510018040f5550a0042b103407007448500c0109030040007601c0e540d40b5480f02070106008070301d200c200e401b0b01a20600a640081c83e0040382151959510b4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 587619928 1250 587618678 587618699
    0x10804151b0f0816051c050415061e05040c02100e060a0b09070f050307030b1c06051e0f1f06030506211e10111309230c040906 56
    0x220240200b6156415641c00c288924040762160020782250b8803803074a16141552a175100410701003910015800417140c04030a8014140100c0c8208011810344080e442c1d03c1c0100c81980d00203402c02c1c90303201407128800d60441d82e0070050b19811100000c0c1d092080909030316101d102071284112609141d030084003c0404502c0f58800c1c2d411000c00e21406203280308202d8054400c0358910081041c0a600414180c0702d41c02961b070002e42400c00040c11140c08001407045e14003903c103051140c0e01c0121503003c012450084641141d103c2e01031202d04001c2402207a0041c00040001501c84140360002c0c82d620051290000040c941086c4591150b495420040240004544241c0600d002e085405000b6442a806c054064481300242c90400c407241c1c1c42641c0007051403182c00251107605000600c0c0200c41c414441c40a85a441c030a940f440c000d503400c90111a01d900c050001417801d514035015210011046041605100355560f03599240508011180284d801411145240c111302103000c440d030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 587621178 1250 587619928 587619971
    0xe01020c010c081501030216060b040b09010e04030f02070f03030513050901080a210c02012f070f090216080a09080a06020408010b091611030f0a02010510080604030e01080415 77
    0xd0f2055131038009240340154180c4c0f00320801000d5407003100309494045003c030341c0003402541c001000410913280c480c0000300000b1080c0c010740002110b802c2407008054108a178204010000c1c000f0b00708075490700c509c02e000392440d44005010310600040702c8061440d651a04005072034002c2c0350b80c0003940c44040080c1c0c1c0e103000320002c4070741d207003441c04441d424500c400305000380c001c2580c2e41c002454116401100d59403407604500d500401d141a0350110740c46000d900c0352044003110000c040552070300d0a1440b10303002c581d020103503079071042258100c0b0b050300303583c07120a2a4101c4005a42d0306c5007135000300c801443c1988401040c0c06000364105c200400707500100200c4d92010001c0c081d01c5424002c005102c103043e6034892514100c01817200d5801e012708c151060008149040c2c1e4200040c200c078200460380f0220213400140d540300200b1010b084030741580b034080d210b468010905803a041c4c3c0c0c09820300d10100c584506018131100040d007004004505041d20141c038400c07d2100355002007011201014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 587622428 1250 587621178 587621191
    0xf1a1905091005180609060c0133030c060e060c0102120109060b0c0d030e0c0604030b0126150a06051315090b010e061605060c2208030d0e01020c010c08 67
    0x440b11440909600c500d05480000b40000441440c1e504200c0c20803407150b020120b8070343c020b142031101444c518000e2103410a40e07100c140030b0300010250780003e10000001c155403981c00c02c00521050010802c1b801a280039201d25051264282400700300003002c600512620751502d41c00005e820b9244860040510304a49081005004064807404401c050380501c291060140d4070040c10b140c0d0300c5100307400041000c0806000e6030039103200b52010940c543c0c082d41003904c1001480d0010014104421003054201004003c0c2004148442092588582c0b4201d000c850300001c41d00482c1c15070400d80d0224005000080c10f0000810b01c6601d0b48019200e1a01b292000e41700b03200c00012001d21501031803a010905a4510003036818040402c070568101500c11030001030130000220000354100102030161440408450b00c40f007080340c0c1c0300201e5040041c14242c4c15881e2070308104d00c00c800010340300000000308000c00c0700b0f00010551402400380c440015595820802c20301122604002c403203000d01c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 587623678 1250 587622428 587622439
    0xa020306070315050d08070209310b060906060a0c0512120f060109050315130807080d0b0a050109060c0609150b041b0203030f04080c0a030f020609070f1a190509 71
    0x6513240e04010300700d0b88000300682540e030700b04514401403518802140e44070001c02188003001d10b60f80214490114030444454000205100070010300c51508038141c1d10407411103c00b4414508900403512038000d00c620f0038180101900002d0400005100701d03481021210349180c0c4400c0078030580600c801080d0303245501c10170381c1c50220701d041d40b00b081d8200c00c0c0c0b20040c2c010410b41c09036140da521030407401000d451490440b4100140042d00c010f00a00005004100c0c1c1c9488404081030742c0704440b06010014440c40309080e0800050760440310480881d907440c14090680c401906104002d0701000c0c80c0100000d80700c1180640031a140da02003c82088141c0303007040a122502d07003080781074450110b8000544c0c024030016420308a686203940d8024813403000369007010202c0528901d8004580380840c0410f280051000002d9410400264040c00420042107c540b902c4010350386015140a0f51001c02140d072110303500c00840c1021140d40151150b4091120031076904e0040264000201c0640b00d031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 587624928 1250 587623678 587623721
    0x405040c03091101020c10050f070c17060c090d020108061809071a120105040e071a04030b0606070c140d140606010828021e0304030e0934020a0203060703 68
    0x13948002103048450b2030181c0320b820104058035041d9030300d4104000130b50041c0c0003040340308005505814168003c01180324000c01c2e1200300201e0b28200000101400031031030b01400340203515038400081d01a0182c0a0170b103040251900b41c08a0144407105c100c0f880502c81100c1486062900050810111050380c00c800101800607a0003082074400d1048801550101d90014030040c0303011340c4155010364040080b00e00b8141d030791103884c44070454610161120100454100300340543c0340c01f16603100504692940c5442c01d07035528005401c80074040d0001c0c590800041d100ca58031401e103452015900020300841c0c28001c1d40502d90307100d604a5140d40007454807404910705c40303c00401d051040035040f219448040e20300740500300a4000705005410009400c15041c1d00c0c6503a00002e40c0100d0080c2c2c9c41c01040050b410500903002005011a070b0041200480110ba1031400c4031400029034011215501d4840503450032840c3c1384800c400a9454040c003010b00c0710140d05a44111180c9142c0d80118940c3c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 587626178 1250 587624928 587624963
    0x3092906030c010c0503182206050a120b04060f0f0204030606032109030f06150801290a0302010c06141608010801150605070614010b0c0f0127080405040c0309 70
    0x400204d000380039a1040c0700001c040ca25141107541c1c0c0007000b602e5009054410702d21000b41001c4244918161940c8078000c0c0118105040c40c04080c2200e4582222048400e54a0510400000307102401040e942e0400160b60903442c2c0080c04aa041927105540f2188c032420142e0040c201d07880100d44489100303a0b600d540700d41c2d003a1054010442d64039085080b5155494401005005050440b1900d41d07451042e514800307280464400761050200010724528030100c0416140288000e008900400103540c0c4030300d0781e984000b001905c3c0d0a01e03000031045590310b040400303851842d1200381105c981c0c400b007059101c1001840c000301c0c070403030780c80e007135640d0340c480103c0d0880e003070055042c0c180000b50340280a014040c00040c1003c0f403140f000054030040c4040a03442c030799000e8003e03840105c000555250301c0001041408401e84040000700b024505000c6c160381c407002d40e240080200700074031142009000245050350010000235205200718401490010020201444220340e8031940b403505401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 587627428 1250 587626178 587626187
    0x2301020f070f06080a06240c15050405060619060c030c021c1a01060c030804031e270524071a040b0f06090a180c0306060f06020f0a0303092906030c01 66
    0x11102d0050744880003039140756101c0400d0080084034418404151311232800181c1101528a20325910a00003450742050b21f0300300d04001000d40800d12506461010400100050440b403003120710608002842181d18600ac0e109880f141c4e0300a03501480c001c10140310113080030010401d00e440340310802d18040b1206c400040000080c024480020300d45d10800c80024041d81145030428000c0c24000d40d030703c1600340071200d00401c50801c0c100044448108100700001403150880400703100c15404c649905013400315190981c0c17110b0f100d092240e0242d010b194103030398004031080950030015125882d116041d861121001c152403ca0703100c04a0310001e0751014103800c2990207000f0050030485203407900c0c3c001c04040d01030f07020180c4c491070115042000007105c00703c556004602c00d26000c43d140b4908088128505207551020084d9085407507841505d01011405880c041d5160034001541001e50400141c0b58651898000070381b54410030340f0084203015415680306413004c80444005030681401110b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 587628678 1250 587627428 587627441
    0xc04030503031b07080352050c060c040828060e07170610090504120c030e060406020f010f060b070b09030706051305010c02072301020f070f06080a 65
    0xd0480e0024000726284003642c8018007550301038401c00c40e0800001d6101d00c00554016a2404188030703c440912891810340c0750050100c100324080746800800b5118200500b40100040e403810b60020048491414001c605441d11002c181c000c9410500d090440b2840a81c09402200040d00c43e0b604150b01c01121400302000801d81407a080e500f42166a6991000c0c000d03041d8a50700d10701450300302103420035651001c03d40040d900f50040c4481d05080b04c2000e1400155081600c400d03007003078200404a41c05213044940746aa03864108801085401c04079906410810480e0744410006000110698000f45100399504000000c100c910b034a03400c66400c4912922600d00401c60a00c005e901042000e5101580301c0d810b042900d203001440d5507104100c6908031201164003044074000002d2107424400d800e68050180020028a804c0100030a1501f10244d20114428025402c854403039200f0f12030540d00b0b0f0f000808a489594850403240c06004a5002e0340000940520004440200078003406 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 587629928 1250 587628678 587628683
    0x3070612090212011104050f0d050303040b0c04090c081602010e0601090c050c01110421200f10210911010f05040e101802090a140d0c0305010c080c0403 67
    0x1403241420385209400036060010059030700a0b14404010072070042800b503001441c038079044044e50307241800100040441c1c000007a9008142c0c00703000400103000041102d0308150403000c039481540c0c981d281030006100e903070426402c039418081c3c00700d58507070020740c1c15001e8108000c59609100503400101d080320301d102c183d54603036405040104818605680700c0d601440c0d00e0701d0064034142c1d03031020303d9003074908101800704403010006080003180c62840d20f103d98016103090000c58107045403a2004452680088410034820003c441c44a41e92610b138200da0003140502200c01c09400800050505540b106844481c0791810b0075140c0318003050f10400ca140303503003c121035900c041c61800440e5031a0068110b0801c0c003000300000300d5280541010b4911407041410883c0303500d4102890b40c880b640d03520407424203071030041c44034102c80d42e00c00c022401a10300415450190b02082c400143d09403548890143c54a101c0e02404002d11106401500710303402d050b11a030144d900e418400c0e41d024411480003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 587631178 1250 587629928 587629937
    0xe070c020901050f060f0c030406020f0303010605040303031a10020a03020c0f031905152509290405040207030206010f0e0603070b091302160201031a10030203130501060e04030806030706 82
    0x603c01450301400304c06003400042c0181d4107082400146c04c1d1b086c4d105c0514080c1603480410f0412265604100032800001110003450645d403400c203001d4a82c2c0110700000301810740318140700c00c001b413004081c0d6828180c0100403051070711044d08040d4588801803001e50042c026611303928101d09060174a0300d10554081e0051118041d0407545041030380100308103c1c0d203809071466200c541c00203075141501507a004c400410b40803e4800c03c044090424404403c240010344104008018018500480450201040343d00c500761140004074248502d40115500c148082540700915a0005005040c0c510081c00040200c0d1606a030b081d0300d003c2107030250383c03690041105201c1e591805000e090304441c0034004141001441d01c004007030707801083c1045200301c2280003130b806645e803500441e80c0307170032403080d04003e821140404100768010b4012141e05040d00007011074454403444402250071030b001802040740315211082c500d080c10090344d050b80042c061102050003450080340720406c039a01a00e4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 587632428 1250 587631178 587631181
    0x50a03051f2d030803100828060b040c03091a0412110a0f120e0a061b020a091113090203060a14191811090604031b080f03040e070c0209 60
    0x190144803030b14103000d010041016020650140000503040000355200312141a00d82c0703000b03590010340402c2a4400c400d107900c854610241018404410105419012043c3d41d1030506400d040010f01040315059420501d0308003c842c40a80c95400005c00b20b10441c05400d1a448130450130607962402c3d1405050b0b80c8070501001c0c82c15006002030420300360800240e07002000039032194034170006010b500ba602034011500c04600c099105104000343c0d441140c0c800e4440d07060040041c40304d001c4500b1981143e07120440c0e1425503544071030010080014050510010b03032050301c4510b458003d100c65481446c0700078000300300341d40301c0e001741d910840c4d015002060403440d03d480c1400d524002a0150740188080c001d4030080b4250b6070029003d040303a0b420040304560b00c1c40c0400c04894401d100a0384401c810b000070b4030310f959501c003103404494111501d00c0321421214074a411011540d8004c10fa64410507030403501c0000040040c004480084c3c116401070750341e500e415116a41d02c80c3d00203612400c10740 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 587633678 1250 587632428 587632439
    0x120306031b130513050a03051c090b06040527030a02060c041a090f04090506040c080309090a05060303040b0a0903050706030e1f0f060f0f12050d120b0907050a03051f 73
    0x911840c1d00020254039141c084d110340c0c48032400d0400303241060300040c0c0b0005a101024405044c10b0212400301081000071a03042e44410032400d0014001c94811034a5a01040c524400a80340f21070502d070b0a15135002000c20a0300c0160f982e4440440b200240c02200700082d52070b50700d1410b980842d200c80e0002200e50700e0700c4400e45550b030301104085d81c0c400c103142d00620594949100c0c01c41e29500c10b000400d1942041c5c140303404c3e06d503902d030301c801d41641c81000080c9140e110069081d410100c0544041500c1d00e0f0a00080c0c1540504d410045040c48049048030340c680d4040307482b5003180d00038000d581d4040e813912012426604020880038056100c040d8515440410344880241c41210030400590441c1d1000f603007050b05c2090344215003034003040c6e02c00e00c03e071240300d400f650061a0810681c2c06160507a510b141e00d5401080241051042c0034000c01c8046d40c594115411084000300143c0f0940b91407500a0940d41110425400092500c000114040a000b003800c14401441c078980500070700c5c06 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 587634928 1250 587633678 587633681
    0x61006050f0d09060f020a08041b05030d030504061805030a0905030105060a1502011104080c03060a0c0804030c050f120a0201150303120b120601090204081b091512120306031b13 78
    0x80f039040b1002035031050000d002c078001381301402c0600c036035a81d243d004d4103290030200c002c2c040a0000f10301c1c20310035000c104004e0f500007600080d01ca0302c43c10089955a101d0503c0340c02444420044a122180c84440f4010400048003d20030186242ca0b030328441501c1c5c400b890708170707001110601d801c0ba10035441407000c0e4410301007880800c1801d1001044040c0403501c10f004a41081e03106180c0381d44004c40400d1507140502031554020b50020341041155001d4000404020000d00050203001148000c102031141c20701020704e42d150f0242c1200d540400070300c0c4100c103a03407162030703440019442c1c50101c0004114000d2003070110794056030f0b0b201003030000d00340d941e00901c1040340059002e00c182c1c1d51500803180030b024490007885041070060b229807802c01c9081c01c080808e6004544143c0c08000d0008941e00c608c0340c05c1c0c003c041c403503172201000c00c5800070402c20300c5072641d840028410b0107241948041c001d00111700c00e00054040e50402c403005a1071980c801c0390100c138254003052102145840300b006 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 587636178 1250 587634928 587634941
    0x10020309100f020a110a0b0c031003060207110a0518010b220902040503010605011e0302030c09210f0109030219111503101202010509010c050c0a08061006050f0d 71
    0xc100603541c882840e5902981240e5007011250071164022940b0032003280c00c00c0c00220340002610185c680c0060355514a191588010403041c9070348801300c042040c24103c800382c40f02945e800b4004550b07078007103402d08450340e018002869128121019010400d8241581010b800742002205254142d0921081c000590040320380c0d041000d54900e104c2440380b1001c1d1078080148051100140e450303040c2820306003900c00540140c1d040c410340045540400c1441038034a07800c1060361400684030344600c2d460748414414100c881d42d2000c0d01402080d8200c015070090505802d820007200d181031300b001010380c00d842c180000a409a00a04205081e507040090441c901c5441401c103500d9254101000554040c05d281d01525458404810851090a004c1820b0083c1c191407184540c0c0d4103181d8002003003481148045810002910f503400f0030040208816607c07060028a45401c1e10340b03481000d0b50300c42d01103480c4058500340fa02c000402c5401402150092864404510315149580d8201c1740039119 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 587637428 1250 587636178 587636191
    0x4061401080708070201150e090c1f05090f0411191412060a03050604030f0f03290406090608010b010315030507030b0903190c1a0105010e13020412030804050d0908100203 75
    0x4031002d854032031f40c3d200040e06000d004c80060034800c0e8100041d0300362905880e0112140608403204a0b080800c0345055140e11f10507080ca44036503103020380700120307110250100c0f400380c01c542024807081c0d03064400001350620050180c03180480981c62801100c080104032030443e80042d08009865008006a030501d40c0404c0150142c0c440c155a075440b9031826a080314158000f8420149000c881c41c2d100c41801d80204907480c040c09210000100a03042030202c54101c0010301c90100b0107501512141c01410042655680800c108d90382c5140050282041c0901c0f540024500068107544030403241144080d039400c0300081c01503504540e2032244080740a806540d80b44014010304a80c14214458088450055583c0350700c0d0449038603002040492042400407049546030040c4040e0f60b000d261100402012070700391101c04508042c1100901c43ea40002d45c008100d42c15100501d50080ca64902440c814000c5641042001504980c4107100380103410b80344d04022803480700c40310203030061600102c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 587638678 1250 587637428 587637431
    0x414010b070c0803030c040e0f04080318010f0c05031009020c0a0b1b030115090602010c022113080c210a020f0a08010903090302090903090a030f060b06031504061401080708070201 79
    0x191503d000b28a107400441c0d4250000000260510940f40c040d40e049030003540c108854141c905255603400120f010040c14946d152061445010855409410040040d0350064007003204045616008040380e10443e08511552600400044c05a13024401c0f0b0b1035008004026140d03d21455840306001d13030002d000381c4202040c20500c2800c80d45e450700118001e24a160340c1040313400305218080d2207000b00b54040c10569252424481c00c40b0340200310f01c00c603851065024606560002441c0540303010b00b440d44040c810030300301c1c0071494400004500c2401c4e1011030f070f00d031032401820a4503018007010a5102e0800d400800080005041c00356020501d400001e160b44802d580b1401c3c0c4908481004500b0340c001552030004000358103010007000c1d0001038110142d4903168001d030225161024070301c80100f01d103071188800e200b4046143d110012103207005064990701c2c10318040340c6401000c1c1c03a001d903100d40d181034400100d0130303480544810807600c181c44e140030541e1400d01c20f44185800408050655 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 587639928 1250 587638678 587638703
    0x60d0f02090a0b09090708090607140c0d03050a0510050a0e07090b0309010c170601172d0711030307200c03011b1d011b1e0c03020f0414010b07 63
    0x40d51082c1104019000075103a694071384046034204031215601801031000c0c0502c03907090001e555400b282d0396034000703039a0a00d10510500740309454072601c41c00040003803074010030080d071001d154144c015900a1042c0a0180404d8942d08007030008514940300b940c0e40501c00300d40800101c45a0350740c2d140e00c40d989040840c0c04030b03034980408480b6401200c3c41da005075500e0035624000b41d0401010001c0208100301628280781800c0060a13141070700d40698000e810340070000f10544041c0350750095965000754409000c82d5401d000ea030380c0390005c0d0b0742e10000c54155060b08030040d500009592007100c4595903210300e04609040c4080d90000001804c185004414481c1e0940d24240140150203108006040d0704c0700c0a201e00404642c68420040c0515000700b44a441a0303074080300600144880100d50721021025181c41c82820380340c40d84012500c040d008111042c0f1100d0760b404000c40b40295041988106170714200000c0746c40c007003c0210001c4520005010350002180907104251140c14250030380c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 587641178 1250 587639928 587639947
    0xd050a0f020708191a040c12150609050f0108060c0a142b060b0310060f12180201030c020c090c0c030f040308040f0614090103022a0706020d0e060d0f02 67
    0x51980c0e5150300703035405501203840e408110107500b41d0700c1c0ca00c0f0034010445007406d00f5501c00d580130285200c0d040031000e000746004240105503002111400d0280b0013003041c80d95030390700b000240c10200c030221000d45a10000003000507012641340c1c81040d502148914110900e203064840f02005808280484010b0050401220385e060580d51503000280040c03145e48484a00d06094400d00d400540d2607140601c10700072202294100001a0390003420305d5490010025401c071162001001213103c2c1070308100412400b200e0780c074400c2c1c102e40d000313036414030a441180c030050340c3d6400a140a00d402c83d01c808006080820717400c001d0694a8503040943c1d00d002581032104145400c170303410170358075504009001c118025a08121500030409402d00a8441e145500006100d010b2614070905043c0c0014440240f408c550221108400f2016021100284c0d0414129a21103950007010058456048620b00c45401500d94862500d0f00030030391761914100d1550070f000351906100c40780c0059024042d1448 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 587642428 1250 587641178 587641183
    0x1504020910051806090601020115090207061b050309060c04030201020d14040b0a0801050a0503150a0b18070203070311010e5d0f0f13030203032a0d050a0f020708 71
    0x3101e002058000b583d400c15404010b07410a0142c0120b055a141070035100180300c12007a80b4003107410110006840b1241410100040d1060120030113503000080e056540c06504900035501807201003045590969410b040d4080030f1086000280c05680f001e1443c40c02107204443e00c1901ca004513540300e0405903960260021600a000c1e5000450381280060056003004003113172000780002c40003402590640215550252806081c0308505500c40c40a26030b01e0304e4880e500d484805000c0d043c40d410789400c1d4402900ca0b049032a045000500c5074400c0d11098205001e03040203035a006028104070b50f02c00304413448248840301040b00e00301006102c6801c1c2020814210070524041e0f01518030425004225220180d040d0250148000203205a03041d4851440079121204152490070390390324502180c11021510541c0000c1d4513110000748a54411f0041140b802e03801ca0385030352040e2003502140210f03228915041000b0000350180070316900c603403140c00100c110038002c0c0156800fa035107804c0e0150 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 587643678 1250 587642428 587642449
    0x5070902072d0b0702010603050c030625020f0706091e080c040b03010906050403081b0408030a0e0f130e010b0103020c06060d020a1e14090402030d03110d0614030d02150402091005 79
    0x10144c4d41d0381404100b844030a0005552b600f1040300a40807a02d030805051a100c82d060010100502c4041c81e4076950038002c00060404190400441d0b590f940c1d120002802d01da1300740682454014128000408100c4400310384080d520742c40068170100c0c40e400c00340401011a251131950564130b62014002054030703807084900803070107551110b040c0e00d40341c0300c14030f1000500ea4044504c3e6000f00400c10011101100780e0b120a0414903007201d4821003030000448110998004e164000e900302042d4030f80441c6039105a0b1103020600081c8200c1c65800c005404030301450305040c00b03a41040001411038645040751400c072500c01000c0c040846c1e00c1d5000b00c040c0010711036000412400079142031200030b440324140742101d4012140243c06103000d50219450b0000c540e5203905042c0c880710180c1803003010800751455007000040400c00540c3c0d8480c03246040410102c03040c040d0003841c503600c0001d8804109800d12030740c8074020040c1c0e82c64680c01d00c003000d00300811f21a40d07880145008030b01c99480c1d03000d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 587644928 1250 587643678 587643691
    0x409050708130f020d02120d02070f050f01020a0f0614040305090f0a03080d05091e0102071e261b101b020a06110403120c05070902072d0b 61
    0x165500e00000003600c1500040e11100080914241c00d00c0001c1000043c6a0312503416100280043e03079920205111400b01158070643c0d01400e07600540715540000d1001c21601c030803140e610a607a442c42440185801c2c41c0006005801001183c008900107130555107089100700303000568017050b901d0318441c0d903000303682c02c40004100040450180c582018094008401201c040304c2180c40d55440c01c903075120b00f03440030362023546410000e04150030a1012064506500410480c80b501c0401034600035845080100c510354419035240c510902034841d0706600fa64810004200155529100071034801300103101c0e07a03052410000269114185224001101c210b50010070030701103c036440c603054403101040e000320a1006141c1d000f03400e030300140800f4465044180045c40c0b641800400c90300d03201d20b41002c0c010324034050140b0846607000d0500000c560248058841d103e841c0c01d00310060744200c12002e4048006245020003140d404c550030502c00c2c0605401c185d1540241c0c0d81d200841d00c040351759 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 587646178 1250 587644928 587644931
    0xf01050412080f010605070b060112061d010e070537050d0c031406040903030b060c030a080f01051005030603010b040f0b01030c21241401091d04020906010e060409 72
    0x240c80100e8102825039001100880551404c1d81440801482409076a00140800a002002c10308903402041c11022a60b04084180902c45d25454000030b0702000c0600302d041010410000203642c0c0c130744075955009078140c0d61214900700a03002c10020340414034682e0501d100803403184000056610a008122030600c1d10b9041d194080b28214000300c44280c52003000f81800c080c54140c000808010640e8020801c8a00080c0d121031418110014054a1040781d0003820000c0c1c0c45610000c00405445075a0a075600c00c8456581e03500703442e140d00404c3c4100c582181004842411550050300550750100000c4c0000510745000c600003402c1d41d41e8800c02006181c1c1c0c81c103660702e1950349805488107d460504120f1100b209410321a8612405a072102d5011540c800394800e4200b501003508080c8084001900c4043e929560000b091600412049000c600030340c40c00070380c0c140040b80000364030610001c3e0250a40d269000e101100c0b400500c41c60401c140c800400019a50380d070054005051050300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 587647428 1250 587646178 587646203
    0x270204080c040b0f010206011a04080613290403120209090711011505011b0309080f0c1e09070e010210020f031909020913321204180e0f010504 63
    0x60000700d4038140e40c028040d13000320300340e8141e5980000c1d2960459803480c282202045001e460320700c0c240981d8000c540705006070001e10038102c5510a1030f00080f4002e910a24502e11000e0107284c50b12041400803080d07412450005002c41d01030b40703c4840071002d80c8009460135041d40001071503120b0031500d600c00304485041041400109120b00c10802c00304500901505082000182c010200c0290003d0812003000062003003500c00d20f6a00000d013014800c0710005110840016243c0b1005850076020b1411202407a10948851308252404031001e00202d1981e190084226614803102c4103090543c400c20300e56240304034a81c4002c1a89040c120603690312400c083c0105059950406207505401e0306007031a810150b0f40b00c400c125040300107180382403024a061b241803004800006200346600082c00e1819a08030020540b141900d842d40c0700381e0305500c40c0d20303448200500850080640110000d08c2c80744401220354414004540d246088a15138208070264074290303030044500b00c070070392031158 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 587648678 1250 587647428 587647453
    0x12313083f0106021b040906020c03040303170907060e060309070f090f06050613050907020a06050a05012909040b0619051306050a0516080c060a0605030d1827020408 73
    0x5001d40503000c00d1000c1d04462170b0300107481900000308619244a140d41d180c001080003500d50454207074400a00130b8940380c0781c0c0c0342400f03000b0100d580800b60703c0460900000354480804212001603403001c0d100c10070069007550500540b0b810003003a0b00c4051144003030100d042c2403803c030118000c10460b48041020821481c6a0050303540035808280210b00c14451010f80c0781c820304ca091b05840050703840d490b0903a20074108a160101a01014040d10b20f0081031150300096a00458140ca21403030b254240035490200d0540d50343e429008120503400b050282c1451b43c0b8080d080240d9040000703200302d081030699500d49040c003482e08290400309400050701c403446111000f40308000e11a0b410554208010707145c004e025403140d0104240b000d0011074840301000418410f48049a89550480e60945021b12500700180498003401c1e20910860303d14542c520722602c494121502c0a03403014044501d84403004551481e000c010f00c0959514102d65510280d1030701c0500010405070703000300b48440161 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 587649928 1250 587648678 587648797
    0x130507140a1e05040c05130803040603050610122d050a050c1201030303020a030906140106031d0309042304110a05010c1110050409020c01231308 64
    0x160310480840120810074902c040300070310000100c1c3c4003a1004150300c00030100c03c40b814400d41141c8204c820000f400030845010000150003034803400c2d2000c11a503155241046400c044540c42c0400080a1b2003058800c51680d0f042001031103180307044021090021001501c402250b6000641290b540c0c104102c00804540541a008600c6503482d03803504050604902c1d202c001400007400f4982c0000f50048414800c2c1d01400300d00b0382045040182c6071300c102c00a01413070020b1003104006800d24070303000a07588841009050144984c402546410149001d00000c4d240744c3c00e580204808050381c184990303d0841c100d92107217100d0341c0350300e40c0c540b00607081010100c0190481e40c100042e00c030b49000040c101031340b541895002100c4100010724452400c0b2018401c03504210034860011071080900312054110408050b508040c00e40f15030090b0541e80c0b40d2402c1181c80b25644040c1500b0800450014030080100031960048040d1601103600e182d0907224400f0014441e0110911215100c003020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 587651178 1250 587649928 587649949
    0x110a1a16020d1b150c120213060e0a0306110301240c060b0a030501020c0304080c060a170a0e120c06070206070e1c0c06050a09120305030c0313050714 66
    0x6404021540c24888000a5031102003a91480070321601c8100142c40031a0411880c41041d0720201c04030808808080c9000980a181240c402080c800043c2e940c0018082c002c0d42c504078600403403003014903e0b00700101c550062400005400204101c80032022501c0d0b030280400c05481084420358a51500c408090610103d84031a5452400500c800c0d088a07401a0281030705a0840f8022901104003400507a90103910781c001000c2e5807000500e00c0b1a04004005407084400c2030701a50988865003007404014400c20b840d4ac2d00182c2c61200c1010021959407205400c81210744001800205a82446181042891050f6440300c0b0124011039418030800030300d13034040190310281ca90b40c02d061a0140c1a000c0c882941882801c0340356510b6805080c40120b841450340001c1d502d00d10940c0d803c40507240307503c007200c010002450120701242032400d142451490a078581d69982c40c50380d5007980200e1941014022403601503070f00c075005012400410401000d0b00c940b20f59800c0d4440c0d40300c00c20005049 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 587652428 1250 587651178 587651191
    0x51c060f090819030c051b0f150106020111072604080d0302040e07030b18070210020403061407170114041d0c0f1005070209070504120f171810110a1a 66
    0x20040103078980c603800b8080c0c882c103c4031f0b01000e000140340e03145ea00e8101030010a02642d40e1141c603810b0141d10004a2000b030407611035400030011058407009075190f601c5100c0b005800c9055203c0f68101c440544507400142c0d00c520311a4a081946503a0100c0c00e100015425400007600400c0500c02e00103602e01080d0000154202044032104001c041085941080b40c102001500c000000b94000d00a200003003c80c0c1a10200315030343c5460b854504000c01d401c62054000108450004020f0b5000341c0c184840c50340308500d845140d0303182100c40800c0700804214550811b80303618030307001c0404141c1e14001c448240407025002d189814000c2c02500f030100e501d200c2c4280304020304486416001001c803072180e50140c0d10059140d44144040e100303840303942d200141c01605400c1041c2440300c00701b01c0402092280031042400c00c0c1d1100800300c58000c041c51014000d1400000401500e841d041c502c54205081c1080400c1c610f4500c466030800d03070f0284040c1d64100c2c003107002d2a004601440100d61045 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 587653678 1250 587652428 587652431
    0xc060d1a09041e03030209040e0303090d0e06030f07232812270b0a0f02030f060d031404122306180102070203010c0c020f0a051c060f09081903 63
    0x2401c1e8039000f14284040c85050b03d90012459548203251007a0102c07540680060814080c2c0d911040750345030340346e000b126092483d0007581c41200070b00f40308107071884400310010101400c1d9141c7c142178500009001c3c0103041402003080b0301c03040c044011100d18034610ba4a8140355102c1d402c884018155580d141040100e82c00c01c40d0030f035210690400d01c005070101a1070700028a185d008907003001030020208130680507241d0001c42900308200e1040c15031080d021042c00303200c4140304c1c190403801e03800240e540700605e070280800240c11303040c00744102c451507003c1c0c40e080e02c40500c00140254180e0003600082c1c502a410100082486500e407800d50b07090000c04201b0311040e82284000b41c451b4000f8001d84092400c080b400075074240250103a03642c498004000b004020621000600344148074041240500001320544003030340350501020084480c09824411000c0c4600785040e10680740050480b9040d641d0003001172400343c144580d030116442420314603035541b01460b0609205040400f840c2c20076 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 587654928 1250 587653678 587653681
    0x513020a0201150e16090302030f0109030f0302090906011b12180501090b0306040e07031a01230310020a020a0b13051c0203040902090a0305010504110a0b0405031902030c060d1a09 79
    0x120001c000d01d41c0c8040c03000b221700d01d141080142104c182240b03a201a5061094542c090f0200d01c0c10352004108600c280c80300a410001c1281c03d4059010301c5c40d00d594803641c1d010001d0585c0d406000421104107a203800424642420f99414900c99a8600c1600002c3e11442c0d1042c5000c03500b840d4000503060909000d8201031420400d02c5c0d2030300c4002c2c00c140c0a01d848000c0003c00c240c08022080c080c0d40e10031024103901c1c03c0c807610a000a07030f092007141180101040c1c01140c1110040403003d17001c8014025156100da074101210196121003182030442c42901d402101103505080001e00a010148010711a42e405e82003040c80c03c2c8203660328042d12a1081040028150000100d40858001d00b1025803a00c5510340002c04445090f031001d040b550030281007004000d03084251004802048403107a022680310720520425008034040c0b1601980460022825400d03401038040010344020211201d8500b0718000c02c4654000c2e4992501040d180c1d0b0000443c02050071f18003050b00d0050340c424003d1b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 587656178 1250 587654928 587654939
    0x30c050708090411040503100b0306070f0503040f1b0314010f020309061306060e01060806030714062a0f0604030e010f08040201030507110d090e1e0105060c070513020a020115 77
    0x210b1240c0280d051082d6900c4000003011001c140c01d5800405005040d1048401c05900700c001034032542c2c2c402807090141000103a402070003282c40284a0304903039126801c640e901e40ea20381007049015002e5690f407455107000c8428a20081050000d10307c02c45440c00c1c9480070001150a4907031400b942070340c4600600402403800e10000d0041e50003102c1c0da40d20214030600d814404002d1106800c21100140c1d40400410041d8001c84203501610054045804459840010b0b1041ca000d00d440150321840410443d1000707840c00d034038000c003814116041442d10040800c0d081c80e1005010041d0080d4000504000030702d90003c0403107020f0103007030810440b20107000400030114503005000906041d6103501150030036228586028078442d05030100c0781c015a802001411241c070920504940050081c001402c0525002210200e1050309142c0509a4203007010081103804c50440861a40f0810800040d07035550050007140b4411038000c01039540140040090a446103900134049105454008200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 587657428 1250 587656178 587656193
    0x70905060f360405160807051003020415020a02121506010c260408120f160213050406021c0e060403030b0102011104081c020f070320130903030c0507 66
    0x202810440303030316403800d14265000050490301c10042d040b407100300c1284406519610715a0740510b0003402112103800d498042002c1a10030360040440301e4010000030410b0342007003111016003140c00d050150415884000f0700420828030720901c00181d1007403c0110a50030151200c448000e0400050901d8200d03003c50280084030180095041064800c8070005000b45980b01c4080704104000c00005100040c2e01903502d9000b902802055018884140482d25032510848440b4488a441c003401c0000c00150b0101852440b48180d030001d00c049400c8012240510860b84120f06c600030050715160a5030f00c0340c0d10401c41e280030031260352424140c41401c1400040d510340c4194949408900c2040c0a40102d0250200e580c6101e240c1d03902040104070b1701d06c08203144485540d907101051601a61103001c176a280110002d40550342c0281500348080f401001c090f14280030218680003003c210403001c2400c0a001c014001d4100d070ba01e491002c01c1644c1030043e1784004171b461405908050490310b0780361 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 587658678 1250 587657428 587657449
    0x11030d2a080c0702040e03070b07020c0111060609040503040f080601060f0f020c150405040204230a060507080f0f030c0702090a0c050d1d01150e07050f0a03021303051e07090506 78
    0x40b4000c0049241c2d01156142d070008010341090b001a02c1c3c442003285040305558105a642d10094003840300c90700010b500c121a580001d01c2484010302c2c2c00d4452506000c0c0c0304001420603100e41c002008045001c8040030781c00340040050200801c0702c0e6250803c024200481000c0310300811664090321100903030b00040b40000e250045440100900c07580c00d090129200380d5120f244c00c01e00214001403910840c0504e18480d521a52070821b110b110f20040201007000e41c01541c000c070380280701c58004528103030007408454017083c0540d4684007440e2070b1400c0c1500112406024440e00050030300860506c251101e4000e03220301001e201107a07803028003501034040d60743c0e80d42c040c03070741c5180700907098406418184407003100700002c00000b83d6118050b0036100490045c0c41454602c00041080325108d0b0040300c2219010805076400d00d00503038030480280d41700072140c0810032101d0303402002140741407241d1550164240b4a82c80780f02c0000780c0060400c0c516600559101d454001008020b44581c405035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 587659928 1250 587658678 587658691
    0xc0706021b01090b03370c1101060f06080702070302041517071a09010e06130e071b03051803070b0d060806190504030221030103170a02071511030d2a08 67
    0x80d8051081c40d10171418020308130f184501b5030008820111207408440c0e00c850081c000c50355030304000038025180c40e400c3c0c80b03241c4220014901c9007081084014410321480d0f40091062041d50081640ca0300042c064882c00b039a2124003058800e030411100e001100f0001d046190030019000c041c1c03802049003114111036000d0b8220001c0083e140c42160710a481d2030a402100801290311001262281c1c1d020442c1401380340c007130300f4443c000303d0445405010241800180f562110018044598088407550040e070f44443d4900608040400c080c1d4091040d007010341103000140340c80e0183c0301240000c3d2480d0f03600100c0d5076000b0f00c0610200c001803440590840074a01d401007502d40351460224500240c0c80340c2c0f800c444240c0000342e0400f00c003000065048a020f50034100c2c4080321026495454414400741c007000d0303400301d0401c100c40d0114240c0080c03c0c00c2d03d1f00705010706102e0101e01c1c608542c400d00141d1809903440c075007000c008100a2203592140700401020300c0303905001d0b002030200b40f0041c082 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 587661178 1250 587659928 587659951
    0x60609060d1101050d02130b1308150705070606030506160e010c0308010317040e01080a03030f0c120905121210120807080c0703020a1d010603021e0706020c0706021b01090b03 77
    0x140005c054540d01220114601703074080c01e083c580c1d15030521880307030095400d03081141000702000980003c0003500c0c10380c0b07403118000c05089441e0010f042e00d0316441480d003210352a445020000c0480d20905c000b030701c604c4200100e841031403541f03800200110759070f064881c18045540c8007800800c1e4010b18040c1526400240c621151001c0c8041c2c90711030140c2e600500d540a211000441c4040000c0307260002540f0907282031185010000070442a0741c085c500040010b0b003015405a00e0921a40003080e1041c042c006483d040569071400d00565400000c3d06800303400c451084c0b0075600702407a0008010100c142c40005102441c0d070340c0582074828190094001500030440811011050060744006d59000700b1803000c05944070707010100c200c0c0c140c0c503c64448250400005003035009000300c0340901d00b2000032012640c10b403462011a90005503043d1003c2c0ea00b400b410009540c1001114080c0c240748d0000c1c040c03200450340e0444c2e802e2142000c2c40c104205114200407410503d020340340c00a404050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 587662428 1250 587661178 587661187
    0x1009020d020d091505091507050a03150f14040203040302060c031012060603030809010902010527090a0b1302120f06060c060f27030304020105070201140c060609060d110105 76
    0x4840103405451086880c07185400c000c00708200c407500c51a040b904c460001880183e40d401e0780151280d0003000c00b413004000d00303c0020010b610600041803100b401d41800a0701103000000f150184850b5003140e07006100d900c40038810741c403020f030358904849801c481c25031a516041c2c1e802511280050240350a401010010801c24049886001e016080349410015801720508040c0b01400f55840181c01003803145000c221140010700070b0050340c0740c06031142c43ca0048010b01094610701e200040c41c8807075000c20407024650b5a9401c00902880005502142e20a0504104164107080c1004140002d20400c00d804580f000e0a00f4568054450f18107040030307a44440100d500e510072502800d046000e80001c020f00608500a910300525585506d0042c0c011b138030342d161216445a200781e040560007400050010f622a80082c0744075803061601d00200301d0100c5600b982d82d00800b030326030380c0358001108110003400d0104001d9803180c0121225806481141c0318035002028900301c1c1ea040050008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 587663678 1250 587662428 587662447
    0x90a0533040b030f1603091212060801051905090313050d11030d09090b03070803190201060312080a0c1b0f02010212070b0f01050d03140307021c2006100902 69
    0x106803801042d091101c165a442c00044500009200700c54040b00c12840015070880c0360301c00d200c2c3e150382c1d40e40302070407941003c02c58500383e603c1180c0030500c410f0b668844902240608003800b0f81400741e84140354020741d00c05450380300c10540b0401060142c0c1607106014240241d013120640b20103e5200340d1304101e0a10541c04e041001c0848903d180d501403050b201e606180581c4000075104460364441c040001003007030300800d0340300c0c1c030f8600ca4180740c0c2c0e00034060901600c501840100124840b0700000403100c0d41c6e41da03034601500d08803002c0d01c0454000c01c1041070f801d885005a41011f031040c41d12008640c03c401111000c0c00e6008005040902031020400469000304004450207081700d041984900d81071411403c2c0e84003c13a0001c0c6000b0071203000058034107000c0e414084d15a4162240344a00d03803146c40c4200180c100400c1c903021482594404c0e044a500407141d11003000b040d030b40718511602413401107450303450f0441d004552644440204042c41403024031100a5640307528015a0360301e0083c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 587664928 1250 587663678 587663779
    0xe0901090b100e01090f171606020c040209030a021017010e13030e1504180b040b0d1e0209010303050a39030c020a0602150f060102150405010f05090102090a05 70
    0x190000d821505d07501c100418002c01401f9800403d01103401141c1e40505071301002c10220f0300b148594005030b0301507205044180740c6a00540218640501211180740305a0000340f90440480c80c2400030501440a905070214800f0b0724902525514141856500b040171940507803402009001e020030080100c40c84003965248c10107504141d51680107610381ea19849482d84500c0c1b2408080c80042c50040092107900301801180386001c0020260f1030403c2c526222200328520280345a405103402c8441400144e807030801c100d018500a944143d19000c80da0700c054440c1d07812060741c4c40c28484640d00c1c440c64418142080842008241d50198200014a019030b02d0750814127009602043e82c0502184556000584a170140b21800c0303425210b0321809070f40d0f10f02d900296201801038100b039491628462610040d00e400c54400c00000036081000c0f200074044130340030b556058459400240f0610246091010200070381030844407804204402e1001850600300484c1050104100d1042035002040c031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 587666178 1250 587664928 587664947
    0x50405011e0c02070828210203040518060a0303030f0b1509040518150403051605010b1002070b250b010e0406050c0a050a1107150e0901090b100e01 65
    0x1030304210034180c0c801400409000e0340c02e44100184100700c0000303251140080e48003145a07020a074842d0001001c1c4101220030f8221030b0075504440e2140c554518032040400c0660901c50741e9000e1925a82842d040000100c4170a0380d000300e0118010512280c0da81d4820168100e80e498100058000100d0000ca070203003010081d20340c2d00c40d03070540d00041a50607a20003800c0c0400100d400304015a505203100903030108110b08081658400d82250070b50180c081d847c0c5d074025000c4c1c204142095010f0718060b0307050b00d240b0360448469444240031145810300600d48080c400c2d890001d060310f107040c00f060b42e825003d0500400c0d61128495103050142e41150942004150890080001c540e12503000d00f007984c40a0740d0448003075141c440002d4070000000e0a4034021812030341c0b8a403070081c418408490030086442d118526001d01c0c2c90000b070000344110040106802c1c1d803540707048070001c01c040000c0d07904140c1c23103074131028200b111800003035450303081c0c824403081c40d130138218122950840103d50f250203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 587667428 1250 587666178 587666201
    0x609050303272e02060907031202070e011806050306090a0201080c04050301090803090f01060b0301030201120f020c0a0b0a020a02070303050a03020c030a0e100c02150c100c0302030919051005040501 87
    0x4180806038040c1e08000b0484205410102c0b106442c000c00c00f40407661448111920684e54104d0a014000070b4030301c0c008202e00c60b48910444807a00c0d00c408884124001c2a84040a200c0c0030341d008075900e025602510001705000c030301400c3c45140029005498480da034078024100100000042c600482c41c50545010740000b40c02001000151700e003092143d8001d0360903140b50f00c0b41c82032154107520705004d410290f80c4a86180b0703045903e9507006641e00040c0c0c204524001e92241010303001d41069202819142205000816908140342000e000c24000036010140d0b10f0f004210413241d10340c000925030101c941c149451550360303040b9003040303009003d209400180c0340030010324920003950104108104080844035103035110004501900c1050756440000e4003c08903510b001a60400c2c00040c0240c1c2d11254292100011440071420884080914010110340d01100b03015180d001000380d5808649140c40784003241550b92034440d550013600841d06220364803a40010f040140a4010015141 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 587668678 1250 587667428 587667439
    0x4060e06240d021b1903030c110a06150603020906070215190f12091a1008060c03040311070602030d09020103020d09120f14090607141203010807060905030327 70
    0x1480000740c207002c4c4d0700c044a20401e02c07056039140440604041040c0d40c194081c00c0c140841010b07a07039003d4001d8000f15843c01c0c10301011a407660281501405504061403040900280400100f0201c0000180303580001c0105841440351034880d4440d18202d904c0c40390100ca0607807112488020301710592090811100c111146c070203034164504d4000e442005d03862107945600700440300c0c4107c640c5c11500702c0310001d04041b150b110784a2960403480c06868005503d01ca490b0115a240d2040d41c0c500754041e90681c90f0a20008108010300d0b0b84542c5010005018030003511000e860500025500c3c05041c0c88003030360f1551400a036045a000e80d0480d001c501c90100d050103070380058100148090800c41c5190040b6440a5284c09481d00c10a03502c1c00c2d00c544214480d080804040a200d510342021700c044887e00c150f40070000865104210441d00084000140c0d41d41c1c0d030500c07035100d04204e45d03540040700348440a03806100351348d000710503500141007010742c15042c2d02d0885d48042c02d242010312010f8102 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 587669928 1250 587668678 587668687
    0x909091115040608060d030e120c0307080c040e0c0d11180903090405090705010912170f07110123031302120d080907060c08070510062304060e0624 65
    0xa07000000780003100c000380c484c4001551000107225040d1110a00240051980390340b40c2c45c6454401903903c0340060001c100c51602c0c444d20301003407614000b40c200160a0707002084442c090326085c056108089407c01c081c0851048110100d10041c5404034004c000e815400a801403d07224001240100c0c045a007446100b4101909180d40703035407100301410700590408000600e040c1c8001158412604103950301460700e407408c900211030300d042e1032045400314035402c10360040080610141c030f6044203d02000c0c0d503407806441c16030441d41c030341515103042c040c0b201c480e000e902c0128000c81c480306150403c61907490380d0714a07144080c001c4c994002948a1020520900203040024020080711500e03191190b01c0c0e00c505608642c2d808a40c861000080c1c01040c1000008094001070141c00b4440c2040b204007250302c100307040c250340068000e04205a08000100307071030034541c2d094550003d4107450400c505400c20000551b0340900401c5140203805601841c05c0103890282d451003046912a0f0807501c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 587671178 1250 587669928 587669959
    0xf1039030807031a060f0708070206180111070806131104111c050906041209210605010b130506090604032307060503010806040b0403030e1903020708010b0109090911 73
    0x601c5401c1e184000041c0c90000140d030703a000559400c0e104140010700041c14070358159004010f40c1d008143c12182036005000040060304d810016280240300b459200300b0b03c403a09000100315050b0600b04a4240d4090103081100f180702248440c0c0100ca003100b900c004030300906101110986949a00d50410f1401da860f1500303e403042c1c0644411601c0c6250302141903141300c1500d0640384140d41044454100c03401150000750f4005502d41002c81c10300305945010342c0c44070700c82030700c00882e01c08030b1070740c20846035130300800c0030b036114ac28050644442d040c0e00b8440c001d0204070320b200d118041c1c9030080e0030026000030f8544d00c01382501c0c01161f0103014401050a00580e003032002c2c0060b004100743c3d108081002c682a401241564180e0300d044000b8000c07070b50346803555198040c000d030081e4107040c0d0382c01041a001505105c840d440c40c0c03c070a411842120a480c0080c5440308507403021400303924002c501040e50b83e0143c0c3c1d0310210351510700c2c085070301e4006040c0740c10030780b0307848803210b900c000341d031a00480 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 587672428 1250 587671178 587671187
    0x1106030f0420091f0602010209091f0b040b1c1b080601050d0608011b080618040c03080d0c120510062307032604111915020106050f103903 61
    0x260140c50765805070310350710313041a1f00f80d0207900c448583c000310300030003d03074110b9070720200e0005d00100080300b0800a0b940c0c0400300071a0f102c0d4006054074240041c040552000f02c90b5244500c41350a4020000340c1c031100c0f080703006940740091a40802101e5004114260f2084065600d0300000360800c00103155516480b078000c0889209800c001088282d030010268025540e452040d0303409460000c01810030640104031403002001118403042946000c400700d1040e9018100c16100c0900c0001c08800c9040058841490f00c5583c084840c105400c20844110025a2100b201c10908019405042c0d00201003260160031f550380d01506008103e410606600001c01082c88510345c0318190380fa00c8140390081800c0c0120307005450311204040c00055400e2a92401410560150401150b10303201d06400a820608807840001030b91204014000c1c0e103060002c03841901000c641c11080c3c440d0720580039042ca1ba1110030441400059580400e000700005155140c04503003c4002e0301520a5203030140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 587673678 1250 587672428 587672461
    0x1a090c0102070b0a0905010f03060305010f1e05090c060c640f0b040b150405011a03060102211207031505040510170102071106030f042009 61
    0x380144185640001e03003000540499000100550710f851040b4142401907802c036880c150320788d041650302c840010104000380b1519191200620000c110340c0c90340042e41d148141c0b40c0e08200c2005144c881480200b02c00082d9018001e001911000d40740e52070490700a0402c00082c40740452055880151550b126004072041d240020303020b8150001201c11103507140c40f00303035894128000d5060f1011030b80c000c000c0001da80010340c4942c0c040950b114256417039200c00c13001680c0440c0d00300940360074040244d100f11040b11400f90184c40c2004198500158484010100c85c003080c2e220b5070001c04561940d1080c003501c00900701d520080c0307683c0780001c90412242e50000081e08200c0d0088000705010074400d0040e55800442c003440d84180d03500342402c100042c07038064840422520702600000b000d44904cc408030031905100700060300c81215003048810310a034108142c2c441c01040080007621100720107126000707508001c00040210b00c51400300c1c501d880c2c1d0b030070f40d82d8424072600400008210400141 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 587674928 1250 587673678 587673703
    0xc020d0b1608070801050904140d0f1d0d06021e03090312061e131b0306080d020106061b02010e06031602010e0309130b030705040617010b0603221a09 66
    0x19a88000c5580803941407500762540070001302c0380d400400407440c084880c903400070300810750381480f0022201d4543c81c103180d8040400200300c01058101c50380b600200040300189600c80070341c14222103980000c1d160180c0520042880b82c0c089903490850b544840101501288030314603603500d0030714400340c035526040641d00300c0c01d034a03070a8002a41424906000da120006003c0001310325100b01082084013200b4aa41605c010350780c1d118a81c00310300d5001850f06100c6151000120942440d2095051907451f4110360207681c14840e04100c0281d001741203084012501e01c2c41030f203210b401e10040381e40c11407000c20207901c91720220500c00581c480c000701c00701c0f40000360020004002c0c5504841e8480c02078810b1a54041c6048981081c2d0006a0304101050270000b0241c036007090f2203e001400719002600011407900c012511201101424400c0e8514001e086030f1403811890480d00c0500c421000498400c20303040f144084500b00848d4007145045541c1c0041c01005914002c00343c16590840c0c001741 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 587676178 1250 587674928 587674951
    0x305071701020906070303183f050f0d0f0f0516020601140d0201020118051c110705040e0c040603060b100503060d020d0c030605010602060a0605030d02100c0c020d0b 73
    0x69001500c0140308641d0a020064009418940d254406400501c4504200e030014518a84000006000904000c6001c3e4064440f04031030340c1c8448000c5c0c1409030401c080040d50004900c1c170340b03e8581000988242900c17040029503640720308020035001c0c1590581843c915418101c1d00d142107019504018800c22003540006171080311100c080307980d52800e110300e960512164600740d2950900424440ca0b25006000200e214203400742b01035010120094140d4203074000480ca041a001190b0300074003511518600340311038030604620705449003114861355203d6580d170702d508005c000c0c041c4400c480d504030040040100c17030b82c0c03800c0000c0503004078130541d44601a40c454030100c090017902581e0103203002074141e00c1c1b48441072307090000c8a0f41003541500c2c840f0f200c00300040082d0f12402030a0180400e41e003c4d11050404d1410340040d40c81c1e179000b09119030850710088060b41c1d8005004812070a880f94041201445404d007550402c003940c0001e50031944070108003040c040000f0885000d40ba00450 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 587677428 1250 587676178 587676209
    0x2040c05090901090203090c0904050f0f0a08030604020d140a090c06050703090905070201020f070f121106070e13090302150a02090a030321061401090605040605090103020c0c0a030507 81
    0x8115a00d108800100342c1c00190000144054145940595031240200048130401c02c4800c0c0022420350084a04498651001a2101c1c5010003404a01c0c0d00b4002d090003003202c00420f0b642c008050000410341400b40360b000c143d02508081d02d4001120816510520f841c1d9401e21100c00c0c0040c205030903040d0795035003410b40000350686c0328404582d192901640c3d4000643d00b44401e400140034082c000b41c0442d03400384104400c5211074002052854452042030b9868003180c50011507400650012105100c1803a52880d014003002c80c0e000e074450301c5840e04014260034032000440d40600c1003194241d551801703005104060300040c407400c10448480c40500d207a42c640b001c01d0181d01c1284500c0c1e402c10b2400808000190062424a42450b8100f0560700c0915018414404075012544841400c1c4038a0469940d00d50300108000044c040524105181c6418840d02034064030990341d210b4100350f400144460b10020034441d18031580b4005040b180450b540f800c050740e81d14043e01400210310015503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 587678678 1250 587677428 587677451
    0x3020a0320070504020f041e03050f03090f10030e12120115020d1b1502070b07020d091e0b0a050a1b0c1406120903030a0b06090a0b0f070605070c0204 66
    0x840c01d41c04000c0300003440d865081c6420710029400001c03034102c1846082c0030109041170980d04400303460420341c55085100e45107090a600d01030074030705107803441d0b0800c120320022521003031101c40348440240ca2461000900e088102c00420f09001c62040900079030201d04c3d10919403500425032603c0070310140225903240c81600341d202c84900801d20140e440300060408050190b4604640d640b00a110718002c071003192100c0c1200458810350410703480d4009402c01c1001030701e03c0320541013402c3d8070081c00302192083c030287c100c018a0084802c0741064415808601d0f402c4684c40d0040c0504649064607000d04500240041d003109403e00041044081d03505140c1c40e190b80c800c0c2d1641c0e00000c00c51956440c00c1c40d40f403883d4074030008541d08500c040088005a404011401e8001c00c110300045a8903c1d103d480042107501540d03e0070302c00c0f0004c000c080742a90b0740d0851481580c40c41d0100a40d210030640f80000b95100d86400104074034148001c004050390001c1d1030440c180d00a40741840800841c9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 587679928 1250 587678678 587678717
    0x901030b0103061401081e0a0f0c180e0c0714060402030609031e030c0d02070b01060206060a0e0103120519020715080705030711030f0d0f150e01170109060903020a03 73
    0x500801007044480690306a00391300c00d20003960414a151071090600715280c007030250307c1008843c0d103800f85480300480340c00c00c0c030316120740c40c2d048006280210204c8161300c07041c0d10024070b901c0f8a0102d0100c0c1070200d210824100c0844010703941c013010420024600300c03035264880348125810b034460301480c40041c100305c00100495203100a0680c120520b140850f40c0040c1c2608003509c03400c0040c5080c02910085030144c80205136490050040c034146604d8840300074030381a00200074501409400b0001c101e0020aa00024190703036000d1203c1491100c076800803074079401103000990050317001d03a001d405410f0700424180305552405003085007000c616a410340310341106030ba0030000240c0c02c10005102c2c0b80302e4181050322000c100262850071030b4601c100b040503004010008480380c0da070f02c0e426000c18030034031a141c20303400b10382807441c0c1180ca080c0b820090304105200c0c0c9503d01124100041401c2c031700398081110582c0c000340800070306049050007540d49841c4203003200400d5001c83e64001e14130b002d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 587681178 1250 587679928 587679941
    0x50303280915080a2013151d18011e350f010c0504180b0a231008010501030b093105100504020a0b122215020901030b0103 54
    0xa140c0c0360070b8500c03010720119072111000300483d052940d503104016111011000014040314600800b540300d00c02003025480b511450343c011040c6813440d00080b2111074220700c0c00d08080c1340d0301500525604c2c2200c007191440160301e0804820f40b8106001040240200c00d40302030b6140e80e1a100e40c80b081d116480340b01c0c41403611007421295a4100a04205031308107000e6a801101d0040541d12010042c819890030354419002040c08070b00301203000d010190400c028800b503031191020030300405002c100440e02c942c84500503943c60202a08040e0768490b810018101904406417180c0c03030240b80f00b440141800801e018050002c1d0070441d2280c1c00e03151800030300e40115401d2503404510001b03c0030740384600c0716070840f1844014541da9038001284040c0309640d100b95414170046642d103071a104101c500882c68101d501d00c51001d1050312070198940200316404110361090035410318628080e402e44500115006042401030100c003200046a600980150700080e2018040091100015000e8824 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 587682428 1250 587681178 587681189
    0x219140f0c1c020d060c03020901030c0206100918050d09060905062a16290a02030306151b1e030705031c0b19030308010e0105060d150503032809 64
    0x7a0031041407a4141d186041d00b5052000f440111010200c2d6a58410f60388010918000720381e010485620650f098080c0d8000a040c62028220380c0c581480d000e81401c107180110150313503549030b00b0840c00ea00503070240c0807600c1e002802c4032000610408002c125001c0340c06824005404604d0000c1d103414010240e6803d080d8181008040907100b00c4090400004400003c00a1040d83c1c1c90500002171174407054040c00e10192000c4607406081c03038001c410b90459560880c280c504000000ca415808015260440340c1181e01511540e0b50002454003400303070a03481507054022050303a0040103000549101813039450500509041800d203402ea03200e00400300c0141c6190010002c4000180c98448403c001c110580c2c000a5241c03225804200310034141c50501a140c48183c07018024160400320340d50040400c42c2e018800756051a001c11a140204c014444005450703901c4031180048000c0e45601070000941280e45855000314001c1c508041070901a114803684058820040e00c1642050309481 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 587683678 1250 587682428 587682439
    0xd141b0402191101110c070e06010f0f0e0118080616020d2709050405060702011107031e030e060c09130b01170912031924060f0219140f0c 61
    0x20ba800b1040d600110075005081c0c49560341c502d061031021483c4068a10f985110004151040c05c1030303032078542035101824075414480328610b4018950751003c03400607020504e1510340403031983d030070041e98000c502003204001c1c50840c00000c60f09860009015215482c003007110082c0443c9407405a0301d0301d010002410028400ea60550588070302500501c943c8008511241c0c4000e5865041c2e8003140c400755002c640681040f400d0141180d0f09001c0c0741c05c170000b4000c80528040032950003801800200e00406070100c0104104424503029138004075001014001366125890a00d6501d40c543d400b192180c0d00c1004004203002003141a40b0450100803010384842804441d041c511a520381c80c01081d280f01e40c4250b0040f9000c003064500654024504150449048402c0980ba0015240c00e507808a440307400094001070740d0006d00c0b9007d8115642410003c000c00c9405c001203040c100c8003801e001c101230301484c04000b0030129071320911070142208152426050411819512048a0010641d101 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 587684928 1250 587683678 587683717
    0x7050309061005060d0c020c040906060f0f0807170309040c0905030d020105010f091d0708070f050405092104081b15030c07020f0109091508010b0102150f060d141b0402 74
    0x4110b0f0b0103085982107e00484145620030300008056860045080321204d49410301000078102e14482c0c0300281040c4444010b00c00c0c00e144c07550340c2d960f00d54403400c076031400c1c490850b2804060070700c2242c0814101030810700c180b044101010341600050f2091502a10900409441c620301c1032080a058845600710090014901041c00c40a85001e00d000c0c0d203403540224070700a8a10040101070003d02c02400500207031842e2001c8914164034541c85140210700300010007819000218840000e120000c1c803040c44001d0828400c1a540220b8122500702c1c13003295110201841c4040130402140c3c022256101d84e2000382240d1882400240d5642c80380c600280204801403409807016a00790406141000c041170b91103850030140e4512240c4840280640034007840b0021003802180d181c01c0d005c4c002400c0010114071901140107004040128921040001c5003060f034038807200071080ca80000b10011720b0782151603200d84030502d1244914200d003940f49800300d0740c1414004e5543c000001c0a403403050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 587686178 1250 587684928 587684947
    0x61510081302010516060507020d0c0b160e0315090c0d031e030f18050c030d051e09061b0708150708041106030112020a0518220204050705030906100506 67
    0x241d041d600072814080705014100751003215100c2002d0f110b015010200d900c1c18000c60203410801040c501200f044840d070704a0f000704000c02c009079080b4829171410410b021620300304a0346405022001036043c00307400d83c02d003240c0c000e14007002d01801031841518110b0b07545c0d80c10001800103081d80200420000d5024600452280740345007510035180c200030078000000410300e0300321600501c1c0c0700c840c1851062043e0a00c80d00708198101c0c0700003540148130414032184040c005018801440038080201c10034a20f66054090507904070365000742195072030f00c148114802c159003d0b43c080196078807424900285a07400001c2d88040101c180804031003a40f1081421070309004014000c1e03c000c20190040841500d80d100118001c00075003851550a015520400090051550025115940002200c4c0e20501c0092170641c020042e17180c1840f4180c04410119483e03404031001039405450702c81000b8010b078106000314810035003c0140ea16907522510f04c0f45128085015441e0041c0b01070011494 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 587687428 1250 587686178 587686201
    0xc07030b0a0e0601030309030519080d110405030d05121e071b02100503091209062b0908070204062103051303140f070509150f010e060c06151008 64
    0x4009403034010114440c0002c20b1103038609002a44201c1c00160401ca0401c14800140305501102e140b501012050745d41a8480c40c1043c000c9d16448254070342d581b4198071243c44610101c5000300000b138191142910302000c040d000c1c0e041203203004400b000420008403141034000c191005c1e8504680b12513220380307407800c044503000901542e15005000041803000540e40e0241c000131075240a0381c9055980c5131000e080307410700000503140c00c4403d04c28003d40e01290b813140260f90300c00c49411701840d0034444030011040000c80c0030f42009000c07847e0001560600c00075100034102a03000340c0e000d11559689100c2d000088648a10344401d0904641084d03001921980003051400d100c000290303c115101d480e6480f032503190401d4031a440d480a503101513042010b0041e034006107011121860f00d881c2003400c90181c0390f0400d2805100304203080358806241c0c002e101240e99120080c19541d111544904e0080d03940800361000d000b601c01c524030314030710b624000240ca50700741c00c41e949908141c0c4030b012103101c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 587688678 1250 587687428 587687431
    0xe060a06050723190302190b04110d12020c010e0f06070f0c0b180306010806060a06050c01021201090902132007060216031d010504030c06050a0e04021606110c07030b 73
    0x103c602103080c03250380101c07007003141c51207031006a0003289403480e641c81e000c1d140624410112104004054840010618203e8500d80c042d4211912a91729a03082c80021100f0355400001004c0c500130090900059a00043d14880f161003038a51070301c454103840401001c02d20840c1b103207a01035420040358001804201d50f15400d20310683c50304603a1601d6000d00c591a40011000303050f10301d030584c85025a4503080106d2401045c01c0b501401007818400c001c60414030407402034400384100000c0e1350003490342c00d43c12a07084080042995025585499135003000d030042c40c00c1644102c0c0c80708460380d0908800e208660304000d8480d00981c81554540c0d010b0070a410956040c1c800c15401d0103002e80602c8009a1203402c0c5102c3d1b5101000caa600079101d891002c40300c0903450400109000c20b00000d41c0080d400c1007910001e04200d6101c0525080031a102c001400313090f50000c0c000b04408002203000c164004180e0303c205000d10030000c84180010a9005042502c0790a40c02620100041500c040c00079 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 587689928 1250 587688678 587688713
    0x506040e010203160e0910140d150902090c030f130c08060705030a0509060c03060f0f130b0307080a080706090f020a030b01061103070c051903060e030703030507030b0d02370e060a060507 82
    0x4010491207455003464141042c0c034ae042444d40b25210401145412030705641d107d62201c504030f00750300740303400c1442c010100141203114180600880609200c000342d103c6004011000071034445103031001009020b6001a039541c101c4506041c0030070305a21002c9000c9200b1034a42d1451800c6940c2e02003000f001441c0038004540041d10344690814544a80c01d00c0303200c0808044002c5092540c000c141417420301c4551284989070000c64908000460080c125410941c0240001c55890000e007010a10002030b0710000398080c0405d10000300b04011588041d04031001e648800c0c0c0d00314002200246c4a104004000300020754940f002c0c4402d2400e888990f0241c0b0104020004107a12555103804a49400800340490740c004200342c81010303850b00485610018518041c44100c0811000c216510141c2e14000d1141100b80c02c0587c0d04292803030001a145041510034018012041a05024220601802c0c20070b0380320000044540c01c003240128100c44803a6501c80c130f400710075240d04a022420b00d034403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 587691178 1250 587689928 587689939
    0xf0e1f0908060a020712020304030302100b040b04020c300d021b03160c1508151f0c0b0f0108070e09031c0c03050601031505040506040e010203160e091014 68
    0x2141c4900200491489003072420700040e40c403609414040300c0f984080d400c00d000c5500400080c4002540420309500b145480031003c207481c14400c0029003d001c00780c0000b41c02a1010811408000c0000b400301501c1140c0500745011403518400d05100c140c100541082000d0100018050070159500074254102d0204441c5641c0600500c142d0440c2d1141c4d244038500307048a00c0b04428000c1c038a40d440c000b0030000750700024000710300c100030b04024030042c003003001c041c03400c100c0c052aa2221a01300c0e482041c407804010750340240e0080a881c03500c60f0740c0c09603500781c1c003200000c00071403900c9041c0f4180c0340c000e070003006445d140000d2030300084d2000301130140500090007882c2e80c0c003e5541040300f05000440740403840035610540181103076402403c59040504214a1030640f640c4481d130142074480036075010440d81e0750440490041d04601000607603070361000080050143c18440c4820701200150f9501520f00f01c400e042010849042c0c2c3e655040c0c00200900f007007407604026025442150152a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 587692428 1250 587691178 587691197
    0x7031407020a330903060c030e070b2227110d06080f1f0f020702121516092d0905100b0f2508030106030605010f0e1f 52
    0xc02c11581695016400c8250080c0558940501c4039442040e0854a01c640d5020500f43d02c40090907640d40f4800075203090f80d6101d03030044240c4260040c81c02d54511a08a4003a00d540300d035030f03007416072144003803010081c46103d00304000c00f5400011012a699200c82220344240441403950554501080040c0e00e50740710703455111044000041c103030883e851b94000039414540756219003881020003031403045400074a13501818100040e5034000b8284081000150380d060081144000e108114010354420080401d0703c20741e080010728806021822441c1d503d81d0344980141c480703e5080c040000001c190a0002401541000000040b511100c41112440d01002c958041e090300070581001300400d03103c604100c201111240302a004000c40d030343c401d25010514070300300001e0060700d07040070342102c0703900f284205003c441b51080d0555400c58060342d80c1e561340d000c02900802c00342c8191808242080c1040060340c3c040c1503046821000030300009943c4031001e15008000e60041d42000c1070120028 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 587693678 1250 587692428 587692433
    0x31104170a120e10051b0604060b030d05070c05040c0c02040f1401080a171308120c0610030b06091807080c0a0e0903040603050907031e0b0a0203010b07031407 70
    0x11149a0140140045110608162003450700100d01c0e40b0a00000c209007403402d03150075070880c40741c040b503142c080d8951040700b8000340c00140081c4038a0b55403242400b0310061041ca80c1c0a034807200380440403540d0b0941c080708203848c80e01078400d0141100f43e0000042095040941020203080b565141556010500d6800201203c1d43c40304030281d096035602c50a44800301d87d04003e030141540701c0080140700001da9070b0b04c00003400449000c006542c0480c0d20200c010442640401900718902910501c50303501511035010740003981d5a0015100c0d0078041045a0745000d9200d080c0d0360021018681580d4a00c00d015014001a2180c40c0c15801d900d03040c41c60303c205000034405000e44902600ea60012501008010082900302848100d403403c148a180300c4000304650441da803500b0049481d694504409040a001d07a201a000d003140c8400c002504441440c01c2d242d4910409000303546449258007071089000074012030840315800c0220102090254006921121650000d10b00e8400181d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 587694928 1250 587693678 587693699
    0xa0c02040c03050405150c09010518061b06100303170921040302030715090e040503040b18010807170105010e0a03020a0f05090a020703020d0c1a0115031a030706031104 74
    0x40700c006000940d500180020080103005050034110503003200c94803410300c008140c0b010302c2002040c0e41804000941e180d440c005c0e100d0411082c20f00102059181c02c0b10310440c86100d9483d81c070302c01d00350042d00c00040f00d500300d4072684c8060380d825644082c80d07400f110245080c0703094058400f81d000d105001d10f81d07060030844c2031900c180700c1110701502d413101d207180305141ca40080d03a002805481c0f00c4251074058079034000103a5045440c488a8100503450b107041503415803003240c001c60082c05001a201310210000c10551a00000a0769000c07600d940300402100e807000b500c20030001200031003004000c00d41c40390b02c001340c2e110801416080d11903034950004020402c5a884000c0d0605008001c10080c07401002d080e5200c0a110f009600d00380c4250f41c029200c541c0e40c0300f04c8050000c00050076080c0702803601c500d000340c001c00c1030f2402156115800d15001452910340600040e003410b500c1c0b11410240214081501d00103001810200d040a0303003680176146188854104c048280300c00a844e0000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 587696178 1250 587694928 587694941
    0x3040323040f0504050123010c080d05060a06020a030f0509190909050c0607080909070c0605131203150b090609030607031a0f030a15240f060807080a020a0c0204 71
    0x512040e0303070341c0d490304030399000072500d99019600c00e03490000108401c40103240301000c9500901154043e0508031401641c1c002d4101c03601821031040072480181040117980110300441c821600b9401c2c10344e07110403ca039200c0340b6800040c00a14001802c9100a008002030440c81d0720042c0103103406008981280c011a0ba95400004015112000d58050010620107010b01399020354a0307906d483c4594035404410306c103611600f40650700c00710018011a10803926200c4a55001c08140054103001a000606402004e003e842c03a121200904100ca030007441024000040381e281100010304d40841c80c103072604142c045c250000700800c001c507038595040c800a4132850a5440000710300ca030005007403608010201405002c1c541d00c8020717110a03a0000b400154039607101c00c0c0b8440b00c0841030040030180200d00c91103085400c194500c00015001c6074a00002c0e11001044011800d955010803201741a045d40c080c0d000c5000720340801d0140009800074408410141080c1c80d10707580c0d650100d400c8032034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 587697428 1250 587696178 587696237
    0xf0e10200d060314030408070e090102040b0c010207031d012f07081609090309050607020a0504050c25022b051902040e011103060d0f081206101d06030403 68
    0x50b903600030300070400c8012420311a036001200440c00d1070b00302000316a0312030517805615868019000095a540003d404450142101c14107441d00c62a000c0d840c2030103504640c0e4210049100510324031141643c0c10500d2038030520507503540510442640c441c8103100d520296059084030854034103005010204608001400c88070003c14541d0300c0111603c000031016041600c02c54205040344022aa00200d04015100220b460300e41e16a180d1000074400c01030f1f80d0000390030038145420042c2c41c032032507000b80051400e0f1502501b14440c0c01405200381c03481c0700400075801500d100c5134a600d008640740c900040706403003201e07120304100c41c4c4583e0301d8041e840801c03020b403a440300400001c44c10a030007519070034200072000780001154944090541c1c00000e00c1d00d4002e20990b80003000740316408541c10300c1380b504003104550790340b1007611000520340d013105d03218082c00a410a0031103140c89020700520050540c6824041d00f1140e81c00c11245038006002501041606811140052900c4003203411001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 587698678 1250 587697428 587697431
    0xc050d0f14092d0303070503070c0c06080709050405010f032303070501050114060a0e04020903030702060310140307033f0206010e010801020c03090d0519030804060f0e10200d 77
    0x803945070126800d84414148183c408104000d560070707001c0c0010550f034001510f800c0883d101c2e40c8075082100c150f000e600300a081901ca202c0300040c00c0d80c010300d426010307040b81e54912100070303220022322098403020b01c40c030f0100c404640810000314000e130454580624140080e1400084226051071443c2c2100708195056591000108016641000300c0c00406c4016140c6074180305040303001604550300e114a10b0300807500060000000e940920841e204182e000300b41907220304241d203001800a0725030150000c203406200b280085481c2c00203d6400b141c1d0301ca844080051070f4031200a41d0000130030140ca02c1110f44d02c9540e844140004149003161206078020603180d032402090b01c1014070180c3c410441d81c2d1040000d8042000040304503080d802040c7c8104040e5025480d103545450210300402c8a0742524013118420564409041030207a4000c10050220b42c20b400455001c40c4c0c01c4440500803948209800c0e100c4126540101c4494410150360180c41c00300c1c0a80b40c8601e50100c0c1c100da0505 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 587699928 1250 587698678 587698693
    0x160305040b04090c0914010806300304051014250206040e0604050708010828050f07090f05070c15110d0906060f05100c0516030c080f010c050d0f1409 66
    0x4e5902c200290000c240c1160700050002042c0f00290000002400c81401400e0340d9a40300305500c203004200884200007102d44100d103415a038071036100c0c1c106001d00c600c80d0502a2002e03030840e204441080c10b20301d00d03011107450025044d0041c200c000f942e1700c00b4480032803403404000240e990a00500b0050000d4003000c03c5620304101080101d4000034100e00034031890710014000110001071203600145040700c020030302c400700100c3c00704501503000010040d1081c0c035002212001301241c0309088900300c03182030110881407090213054030407c0321040000ba84000344034000c103c404900c501080344489000503484490200c3d4a40c50748401070301c9078925110800e6404200040c420745c001012002000380ca6a410080090800f00306041817204000038040d611090240520501d504001c003040e400907078541c0d0745848801d0180b1413181c9030303003030048110810202e0018090300c0451010707682e915141801900494000b01901c11240d02a81e9480d0451310045a00b01c0c010b1340113103030503801400030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 587701178 1250 587699928 587699951
    0x10e0c1b1c030b0109030b070311120405010905121912091208070e0915010e1201060609050a170604061a030303041a07021209090403140d09060f11160305040b0409 72
    0xf6203400c051018100303c0070503401c0011415081d11030350084031506d4017240a6803c540b403030010740a80d8641140305846003042c007003084015404090843e00c01c0050350200c3c25601809551402040900e03404918007590380c1d465248182d01013403c11a40b000b000a190500781c5468401410810102020503108014002e2442c0c0082807010707240021a540c0c040340c41d01074104400600c00e0380c440b03814429404092925a0b840103409103490403802d00800c0400d0340c410000b00215224440c2c1402409107060109160504030030101150400a00400958a4aa603020000c1c03d000e03514004148000401c100c240e9001d00c02075004074000c503069070071a81942c4a00c00440000340c002d500f9940000001b4140f195000166003458408452607480b950322401c040d554503032410486540510001350340c802d900c6469020400c03d50060900300700240a444140c01110311802c460510054244501c5010150004e1888807144c0710703141c05404d2030356400011040784c000ba004540c0145d10740c81a5901d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 587702428 1250 587701178 587701181
    0xd060c11060c04080304150c0f1101030b041a0f040e0d0507060c020604200a090207080a032409091401021b0f06060901030f030c080a0e04050906010e0c1b1c03 70
    0x42292100c840c19291901e0040d91030345e68400ca1142c18000d5102d902d034124454002e214555003141c200d92242245013503403608410040030300d000300340881e180105a808a00b003d10910703101c1400301e201013900e0a803200820040c00740031058154015192444408001014032083c4460491500e4181c0c41d800d0761314240c0b041c0c4d103c4034600c5045500441c10480803c0c400d90090b424086080c1e2a80908152a03020615201094011240031800000c03003408004080009040900550f58100a0f403900fa60f0810701742045580c1f084100d40ca07082e010b01040b1450ba1283d18094803440c00102e68405101d11542641c11003c0746500318200511191026101448400350a00401c0e028164030318202c40055806401170001a0080328200c00200405000d212481d03400344d080003c55407182c0851400501c40151070056a000e103003824080f90f4240303400200d2505a5468807001f490036038031010070102d16003140500420010b800c804d211382540d03060101c038010004150310102e1000000c01d01a0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 587703678 1250 587702428 587702431
    0x100f0b0a0b0c030f0304030302070b04030e1309050304060f0203091c020102280f06180b150105250c0308030a0501170309011218080f04030b0f09060103110d060c1106 73
    0x11075401e041045a070301d402c010040320703007081824a01a40f03c0e260303800c045000b4010030f2002001050070100b07020515810101d0310f040389030201e4070f4031070f00c0d415004040309456412100070040e074424001408514012404498030904520441c1d007400041000188000d464890080410071502108415964148600f80c00300b024598203080381c200d0010504a4200070f10303005400203503445001400c008003600000c1a01d429206051b03110026810050801d5a05031920200d1852808244405500500940c0c500400e4184654400c040d48020603030520300c056022141d03c0e9a410740800000c0c010000b4501030100100b00040310b40c1840c0c3d5200d9540c00e00710000500b544240016038181c0c1c0e1002a0035080440c0d041c010800208910171022003441c07100f40103003600d4011030428241d410311030107071080b07a00070001c41e109900c03580e4458605040940d2403944a412080043c8085034101e03041420041d4050040500d480c801c0c0c1301c1c60304a54400002c000007410801c0d004002c2d5100b0000c0c607 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 587704928 1250 587703678 587703689
    0xe0f22091103150c0a05040e071d0406050a090b0f060703050c0c0a050907030c020f0f01020910140304140a0f0b090c0603060d03110f010608060f0106081e09100f0b0a 73
    0x2451400c1c0f89400005110b20001d00402d940d5200080c8201e43c28412400c2c3c6000782520f060342d90741820b0410001d042c0100d00340c0c903c89480c100207242ea10307529042c0a414126003000e0f1000d90302d00d0501080340050030309450070b80d81060444a64a0031919180300070080e040c00b907911301d41c441d5a8483d2690800c00e1100c101407040d0100e540501803640c1c2c030150613400c403145050011790308201a0b000ea050600d8003100301c04a0242507503800800d90190028041182c04480021101843c90b40646140e014800440c801c40c005000040000b038907404031319140411030007210104842030391050304150500c0e40448040c80510280700f40004100031190702c2a900b150220f00f1443c14801040c2c4080800c04d02504000d0207004800301c0031005d0000740e000d91900c2000f809840d44480780d00d59203003030039240e2030003485542d000025600d00c100c1d90103000f90201564100304e501620b0380e4004400014081c3c0045018400e05407003040340912540c103c11240701c6001c02c8154100d42000160011039100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 587706178 1250 587704928 587704933
    0x20d21031406130b0415120312060b040605180627030c060a0e011e081008120403061a1908070806040c030f03050705060a051005100e0f22091103 64
    0x140907443d5141040741c1d010800000e40050310003c018002005021204e0030742603498550440441c24500d2101041ea00c030740280c403151170070194529100100c1b8028401d45514105c140414000d0f06c1c4500010541d001625038540791604001002401c941d0200ca02451001c9040707208912070241c04508070715602e021030181400007102d10100d070003845511600c0701000013100195106d42c0c05003141d4021266180c4c1c911030041074860300582054402d554034208110720803c0010802d400040400c1d0703005031182c14501701481e541d502c0f00513011801c84a072451a010740c14078413075100c419640710040d9a05c101d9840c40c5150010a60a21b1300c10b42085259410400800000c07403202d881e510116070744244203190742d40c0c2905048585001d100d1004016014110510801a0311900940e000b1021600803940e1240d4401c03c0017440030410729000701182210140300d82d64607044008040510001d00600158003180c110000e00b40201180170040302e0b651150501804001c141c032105000c0182c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 587707428 1250 587706178 587706181
    0xf0b03011d04050d0e04110c0a0b1f0b07170c1c0905150c0a020303070b040c0b090102101d0a050307120801030c120609060212090f070b090904020d210314 68
    0x2152601c4c1d01d01c0200c4401404042e0031804440d89a030303030290204d5104140d030544c868038180c4d04035855041488080e2598800600462072202c0a20310440784030040c55a08a41c042c5070034a4110690411036060701c00400918086107154004d0008041da4400d14002d0303c03842c08494076020469107090380b4001004001c16081c00b45072035100a050b200c21340c40701c0710303516003104190b8246005c11243d0001c1d0180004248402084076500000e03000b644558003100308640c43e03544004442c02003040d01030040e0b00503001f5802403041d55001c8081b00142c41114207100302c070722a016180035000303130040307a02d0391000a42c1d0007800010f0504140c4d403007541c600700c000b43d40355407a01c48a120341c038080c421340c203a2003070016420407426a0000741100d9204609640b00d0340100d0301c910000d6401c96540c6054002c10550814521021401c442541c10f074910450900b4820820711200b00401082217070417038140c1c201180807c03150400a105c1102d01c1c215075580c00480040102600c0e0011044101c030001c000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 587708678 1250 587707428 587707433
    0x106050a051903020a0b04080f011a04090201110706090e0a05060d1407030f0b010e06031501090e070b0f030123030309060304080702040c0503060418050c010c08040f0b03011d04 78
    0x35a03142203a004441800e014a0384903442800c00d05503030f100030760190f4040000980300000c00040d10031140a0425120300d0b09141d42c4260a99081d8203044013801c1381c948800c0e2403858188e0054401074010300d82820745c01c1c2820045440c1244a8010340f0104406000410460b000085080d80c00710940c10705000c03908100c400b0030200c0c0942c200042044015503104e0703401440400408000b0341d0050b6090002d4901810320100310700d82030244400303500c4c07a00000341aa0070001182854003c0c86a881c0d015a0328120300d40c0010009880c2c80c2000d405221700000e036038006a00984142c000010340c01b0380c2c0c2d5140040b22405000b8600c0c40300c2840222030815542036501006442c9030841c01c0d035000e9580c0ea214540307001c1e184a42c0500a5015203001000c00c4625031201c0923521600c003d58007001a4108003000040d501030100e80205594030040986159502c2041d01c840e00074071a051040c280307601ca00d4060345c4100c0c40d4010113403100020004101c075102c40329000d02ca045060100344080d04054 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 587709928 1250 587708678 587708689
    0xe070e0a0f09121103190512130b060415080f0714030f121b0a03030f060911030a0b12031908010b04180905030d18140d09210c0b070311010605 63
    0x6046010301113003107000b04003403a080c4125081030741c0209216060090740e0030043c0003500301c0c3e0010781021860740001a88516034410701401d140e01b00c1180e00090b91000c04100240111441c04c0da001c0040c0318002641c00350811482c0d0f1144880c2c8081c00e0020b0800520858801018084510070340c048041008401c0001c6500c030400c484003d8050340d03031a841c200480c00315050f085c00c1855031240141030010f165140c1c0c0850804031920320140a82a03076603200c1c82c1500d02140460002c0700c0300300f010540305a004d500030903c141000d0310102c00b0490007840f8a043d6040100ca00100381d551000708030340d05901c102c01c0e0703014180c00c2100c20b0806080030400f07101d00280c0c401e41e6207140d40d50b1841009000f0204142d40041d07072854030910602581c58505d9240101500c4100e4092848801c0311005490100e03526011220660710582c02d540780c03182216030700c070303260180300b4501d044144031030b02042041c100c48000e00070700603c150b40e42195140003052001c0100002c01d02d41d15250b02070040381d81f030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 587711178 1250 587709928 587709953
    0x4509020f06090d0b0a09080706290612060d060915382e03150605030712020f0a0e19210c081b01090b0901080402010c05010e070e0a0f09 60
    0x1325018440903691810288014020b910003c2c2000c00045202c00c10480d06400c01500000007c4906030b802c004c150384070035003080c03142c1641e40c442c100b03009a00b0070341440e07003030b403a0301010003008019490ba00f0380340c540031240160810381e444403e040b0714075001c070380d10f020f44628440c0440c1250000c9e941c07002c4107a0380d80344400c082c000030000e00300b040d5a90313034a18002a14600e058043c2d01c4501c800030020400580100502c01c010030704180b2440382c6203420414000c102d0f81c0a840301c61640e030700d400c02103901007041c000600da0340e03500340801c00c1108a594090100707900b46071140da00c1c3d125894104200c501040c076020000c03841c0d050050010020b4403840341b90740914800c40030001d0b6070300d01d09a04e07082403540050b541441615121030010388113154115240c00b00380c0f00d00c20300c0340e01e902001c002407040321022400b203043c1c00d002c44d005520540f00d01e44594098000000d10b035081030382641c00d00015602c005442c19039042840300006c500c1c451801d882c44c99120070000d145a80d510101c40c50030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 587712428 1250 587711178 587711183
    0xd0c0201080a050a0906140601141c0c020712030206010302041103130b06010c200f01020d0806060d1d01050406060f03050604080f04030506010b03010e104509020f06090d 75
    0x45440108801e03c4d000d400c1061314950041d801e001400118480180e1000100c6000e400140341d9551006050051421614062003090010388a0101c4a09400140c269468028110701c114200043c1c0010040d0180020398441c5c1c0c050f021a509d103004000c15500c4003581620740d1030f020800d01a0064444101c00300007580070702210b90726611600140d9070a2101c41c400341950150800742190500c40c4031803000e00110445503203078a01420401281c2e02c0540346960f0010407810008101645441c0020f031410402608010406c1c011403e032209907083c800039140c0d0756031b448406110030008103010780e00241c50800110340b04c1c80c0c5151680d95881d20003900c042c090b010001000303503e15413218100e030007440d0800222510b03944d4601140000d85d2092040041e5200043c0108054a50000b0031204440740e00d0003580d6400f003903001c68908000614401d0b540303415034070719090300e05044840b81c4141307038548070002a480e0781d240140407420103007242e1540318007020401c450680d03640102d400481038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 587713678 1250 587712428 587712431
    0x1090f0501300c0906080313080d0f080417071b0902090609040b19180506012f011407031514180901021317160b0d11090d050f0d0c0201080a 62
    0x48141880c2e00c1c2943c0d107030041c24205041000c0071400e80d00000040000b031740c2d4020000c0c0340c19920340c205138071081042641c10025402c000c59800d06403081c1000741e0404d000300d9500f50008040c107403a8080d0f0340302e1a022a80701d40f00079014075200541100090041c00c03001405c0d89000c0e100c6000500300d01c180000c06100726a10301441c0b040d0b4807000c00d00d14500c0d0344c80c24031100d516196962a0f080c40110280108600e0a10001843e25417254100100d940f820f0604400080c8110305a65000068a41102815903071030301301c880c50100c100c0c507c5004140c0c94500040b5001c0c1341c420000c0254640d0000f1400344100c0c1d58425080c1c440d4002030812131207904641e842c0d03450707140014cc060702c10300042480e0300d121840085608403250380c01d007295480308012070b04c007000002000e83c0b01000c3c1d48035040d004e20341400181d041c0603041c3c00a100d00303621003445502d00001c4100007496824808825512a40a5840010001030401059034500228140040840030a0b800200305040040880001e42e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 587714928 1250 587713678 587713769
    0x61d09031b070308040609030c0f0b0301050103050403020f0105160f05030103120f090305030703081905060f13020c120901031410060513120f020f10120513080301090f0501 76
    0x607481072002001031070340304581603070700c40e40e0b180010b0540d1814001941d122180c080f000a52040380a03a990846004051082c21603280c0b00064009200090003501940240c5422544192083c0b10b00b030311450f0852041c26488100c0070005005215580141c4180b0070308200500100340040405032820500e49820200c10b43c5c2c0020895054910f43e100502912010601c0010036401c68035040c0701342045200c1d02c02c000c214803242c2041d80c0c000d030b54003a0802280150b004c2ca40c201015070b0403074030002d4030001d450a1224080b09203000305070120b0300070b02540894981d07195a8980600101c140300d00081c0100b50602006081ca40190f511a07d018071000191880e02103044121076002001080d074400f1402e451070904c03800c070640d442c00032403191002e828400401d00d0198040d4910b80510381d180d100c55100c8551541c000c0101420030318215400700d40500c00100f810008502800c90a0310100d903424420381c0364029980182c1029080b0f000c0040c452030201000008030612030968207801c00c04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 587716178 1250 587714928 587714977
    0x90d030215040606090b010915080c1b0f0c0f091909060204290415210612141b0103240f05090a0212010302060309030f070303061d0903 60
    0x420311460740c6044400c0c1010200810302000d50b100c2c404450b98154203202d518001001164a80340034080c210300203e201c090b08008a11611107958884102c1241030b00c0d143c0b02c0010040401c9004401c1c1c640c43d030222403450303891103091040c0c0401040540751070001e0014400061280e9500904070007080c40306c1002903e14407003d401c4588141c1d0000c00455456880c0e043c17580d0002c0b04008880b41010104441c08040c1c00600100c84c101c03000c1003441c054234041541d04950203280c0c01003240c100c19076190701101241c500e1084400406e00b07071a1450500240345404070030003202e21400d807010703088000e010b82c2c030041c4045042d1a481007440d00090f91401300c5a40d006441440040280f580c442c0000840e940020100341000e40b04102c7d4210450ba440810503801d921501c05246016a541c00c010401410280045c542190f001e00c1680d08010071502c0c01030183d00104416400283c9811040086205510300e0a0301110311b14413030f403501c0c5401c00d659540c9204100c00514010f2900550401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 587717428 1250 587716178 587716183
    0x40f050d08190315120308070903050d0507081216080a15050405040303140f0601030e01151a040306090818040b0102060c13030f140106050303071a07030f05190b040e03090d0302 78
    0x13150900c420b010165607440d9001740d0b190f650f100804402142c02c0c5004913248034043c800d003004880d03211000b007030078510200089906400844080301c1320070081c880c085803041d4000e0704502c11a0b004503c4400721003240c000820540c0c0c05081d40e03401c1890a0b2082240340020103616040d00ea00f0f41d8003140f25100e40c50101c0c0100803c034100c1d03114010f144103000c40726002103080c5010790002d036010301c4900c0c5144695403c0f03550a204074401070501c4e20040080440c11846810199001c500700f9083c160340752114802e0702e00001c02160320000008108500804d0b00007103c118003406d40d82000000320000006c0c4d0b6500c000351402c50401000f0488202c840007001644001d190700046404071346500b03103403500d180711080c5214a42942804000300f41030070b00000307840c02c0135044041c0b202c0c684825003210f607003003001400343c801701501c490810088460074054a40610420340b030313400418510a48071030494441d244400d02c260b007071001502030802c002080d29082c241c11204a44110040c0c40c00b6071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 587718678 1250 587717428 587717441
    0xf01060b16061d19150c0c0b06011808060118050603030915130806091912050a090f1517061305060f03010905060709050a05150c07050411040f050d081903 68
    0xc1c2148a440c40c054131469480318034141080c410744950260380600700624080d0340e0b001d00000c000854401064000c184a47c201540040701130500c1c024130001c0c0142c07502c0454040c2c0054440ba800390004219807004c00210540000303072050b040240b4100072000135120700c12030510610900e00807209201c3c066264007140c42851503c10607980b01a0796800050315030000319050b10090046105a00e15508010b1050708a1540038200f00c4981407042c50075a039903081400071070208806008085080c90500c01e1440107000c2d500c260401007503290b14004c201000501c075800c1c160740d01d00c1c01c0c40096200c140139954034041c10b00000ca0745650701c0c4081003800f007506030055810740c00e05a1000c00c1c8003022030400d0080c0d009035580c8080c20f46440501c5020a944d1003460f07000016500d0101c01c0006880181c1031041400003640c480c5540d0b400040e0544103004d000c3e820383c4000007000c11800500e20300d1600201819144803036018032507282c18086d800b030411104141c80844d030042c44950310a40c4100c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 587719928 1250 587718678 587718731
    0x14240907150306031109091c0504090c110607090f1809050601030f1b0b070209150a03050d1b050a06020c0a060f020a080606090f040e0c0901080f01060b1606 69
    0x2900704404001c008000c0d0549200a0701d8000c10315035003040700c0c10030303104061203a080c0b4402004104880908654070041d06408003080003c203000c00f2407250b03440d005042d901000c030b40e41c41018240c5204c58906100c4058814410710134565001c0002d20041844c40e003c951940a848604090040c260342c0a003400c0e0744014900e001e084000703c20881154400d030091402120200204000424112140341080c080c0d017548020900505005180800c07005038416108500120848071204c00302c0c1149000d038208441c0b6802008105040560011500200c000015900c0380c506040c0c1e00c4c0d5540b20040d501024040030b0700000d401c0003003d01002010300e40359000d002041142400c038020402500444030f10800901c072540860814544041038550310344000b07141c8ac203442e48010402006203c14102d011403030140c5611000b0700d0741c42c08001d900038200341c4041e01942400c0c000d01801c540080c0c110300199074060055100d00801070f6109450390380d10100c0016904090010814502401900c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 587721178 1250 587719928 587719949
    0x114030c070b16140403030e130608010f0f0b010311041205010b090a060e0c091818100902040e07030f060c05160818061c02071a0103050a14240907 65
    0x1031150090101a40d400c0f0052259501d01c600d810101c4500c220f48510b10001c1c0000300024140d640310314001c141f0103206445c0c00e400103411a5168000b0f0300b0750b00c03031141000390a0756032a1141070000741401245a02002403908002800d40d0303281c8180036000314091003000c01d604075801e0b400c00609603c0468090001001d81c4038601c0c04aa285025204a010b090520a240404543c2421021065400034031009080701070f0362043c083c0c2d1008118004104c84a44c50a1618a80000c2070500407980c124800410104d4007200c0741c01444142d4291881088850b40001c9007000070544980e2030a2000703900110104084224050403203250250841000811100e2036000d0200b1040c00020941018149820040c1141410400800e030083c2e086170f0034031900d01012070803c00314580c000c01000340315000d1000e1400d840d40c120201075409810844880d40100101014032040b400c80590b00e09500c0f0044c120aa0a20340d0204c0711400750140e03143e0702044101090800805110200152010100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 587722428 1250 587721178 587721181
    0x31b01090f0b04140706120b01093c0e040b04050c060f0415030b1f05160b0601080901110702010f1e030b1203120f040804080a080403060e03090114030c070b 69
    0x24006031aa00540c1c0c1110003003c1040080d504c40404541a012904662500c8400002900c40003003d0000e0441450402c820484041500ea03c400d0100c030b158580a0006002000e81032000c1e4198815050054404041380804020303030702503180810390080d40940384150540742c9250207071500b9603407407410758810808900f00406840d0310780a4800c50304514a410100c60b11048158112440402450382100d402c00594a22494148a03502c10380c0440c50824609088080c0320200300751852411540f0000d04020b0000540e0303c003503002d0300886210000c01c081c40003155080c4940c8101e002c0281440000100400312500a810154000b0000d42d11102d0b410b07082c4100400521224524510401c1c1d983c181c4090f0074000003e0f85e200210f801c1070100d107629101402101441e0003402140e501004110200e820001403210f222141e00c210784190303c072070a62a00205540c00d85060050b02e034070a000c81004c1d1f070b90041070070043c4024008425665111a0b01c0508035110360900900300303105400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 587723678 1250 587722428 587722433
    0xa0b070201050f01050405070e06031e130203060f1005090c0c0a060b041a1509040b120609071202060d11090316080c030607120203070903020405040b06040b04020c031b01090f 77
    0x100018491440c108600610341c1c5c81e03d0801c802c0310415614200050310034184c0703113045d040c400c004540180d10018100f0250b1802d0004c07011900040310806044102e400c0031008508081040303c0d040f40442013200a14544411060000c00040c45000d00ca400740c45d0118078410340d0541207035030461400c03090340e12100342c90803c24003824034144c1c120700540c0740c944c01e100348905503014050032110080c1240f95940c3e8005004502d03800c12980d0b942d015544415081855031030f040e8801481c0c2ca0070020b411940742100030942403549035482840145080400c0400598501c0126000c506001400051070f94100b824a60300f4000d141290790180704103981154103900344896502241c400c1411540c4460100007459200c501c00d688107004100c0102d0401c1a641301034001d103030700c00c08504c3d0003400c29550f5000901911020b403003e8918a07142d00c144010741c2000e0003074000604055506600e00312008111580c5c07807058210080790001c0d1009a42c01062081d00b1196205030041d050001140060 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 587724928 1250 587723678 587723681
    0x1629091c110301110901030905071e080f010207030c1e0615030606091505012001020f0a180302030c010f051b150a05010e06011110050c0a02070e01050d0f050a0b070201 74
    0x1420140e031000142140c0410302d1405014a80700b408030344040a084c9403201005502510018004071114050888041a0b000903009155007460000d5030901c42d8500d454036650130082c180d484003410b40d00401c0a440401e03002058000c0c581c0d848100c038241d11a01c08901031f480c2204110085c2418200440031f0f2241d04e14000c80400d40c8d014210030801195501101c5007242c60710782492720304140d6060104500e42c000d00b000503404602d1a0961007000028a0290132a8070013800c40b41d1041020607240d455aa00c0031000c45d811540518101e015070441d00001c0e42e64401030040e07810811000c00c00043d0922071401e982c0898144a62417100800060207036032501494080f64159004610001340031040c80d01841e4100c40003071901030f44d15120007004456240c1035091411551080c200b10030f0b00c0e089148a814852a40040d815885007441c072030080c01c0c92450303801404500102401030049544401d240150154800500d140d01c2001e890090f080850100000c3d02c2c29045400b0000c0e4590103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 587726178 1250 587724928 587724979
    0x5150c01060b0c102903070b0d0204060912030c141014070e0d0c0504020a11030a080f07050a08010e1e0703020409110a050712030e070803070203162909 67
    0xc64080d954000021340643e012101e1034294424510081c0c1403207081780c6a01400042c44620103000d403003c040c4c64080740c00055103e16090803943d42d0024080103019800101c410181c0744422030300c0c01c501050b407001400500b802e0345c00b41080c5c417a00ba18903940711081141382d2038042110710500001c1d00c0300d11001c000ca403044400d0f00c00b080700c0c0148408185442014401591362180004104500745410f0100039040300304400d085c0b105580c41040c080394100060030881c0060359500b1440c1c46c0c101808c42c02d902c03000c0d04d040b062120500604240c0d9420191450558001410780c0109554181010102100b252141300401da0f0800c24800c24550580042040c0c609200090100c0c010a42c48100b40344180b8040c0ca00107003081c0986000110120080c2468040c01d02d40071850140007003600b41072178501d9100001c158030014907641103080c203018081d0204524822000b42d2841d060b40e000f1006d0308050009048038249860803100032951040d991152009030600c00324200074140e10010844 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 587727428 1250 587726178 587726197
    0xf100f03080712020607120507021615140c1504050304030b0c030f01080c0a030213060b0a0c05120c120304031e0504030201031a1003093801060201060f05150c01060b 73
    0x500d0400311443d6400001e02a001c0c04913540c90701c42028242103058000c040150541c8114056010380c2c00c8020407200c4000050000c844a02045245603003000e412051101d001c21040c0c40c040c442411501008a107821245118240e14815992a440c0c25801d511441d00001c04240e1160705102d0300f01200c90143d07200780d462107540003441c0d80702d5070556940c20101c07a0171030b4001140b45090005040014041c0c0031010301d107070007040140c1c0310175142e030480d08032171100c000150720061010300b88581002240c0030740615200151828607003e4003142c070b805204503428001400040440d0415105451410501004402c4c4000b80d00311f64078000c1c4a544944400e078000307414601441c506c03074544003284100000c020280c0901a50600d81a000303415203031004e941b144610005070400303880701d11400001c037010075040c1c9044008100600c01805040e00085c0031a89010014000300d406141d5030816a50121224511820a044010180c2c800c0c071610030a1542428000108001404084c211214 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 587728678 1250 587727428 587727443
    0x30f0708070203070203070311040207060903021b0402071220010c0206040b070503090c10030605180604142a040302041b08090c0f0f01090e1515070b0f100f030807 72
    0x440703100c02242e0728050b0042c041d41c1500903840410002c0d20440001e0012000500050308002a0303480f4031049402144081c0c000d07800c100700441507694520444881c0c1002298110b0401020762168202015104000702c180030070340d81042e90803a102c0001024180d1440002e00c130003515018000e450f08003c3c0c80403529480341902103031003203001c0e20586e0300c1404003600a02498982004100c43c10501050081c14580d8a03031020600307131980386224104541ea102da10225007419400c0c041100d485111448410108200b400540d41840411400ea5015030340c4151801c1c1d81c0000181c511310659000950061500c00c0101450b80c00c82c0c041c10003003030300d511044200e42d148403415807a070410301070031130f40220014150821840c0600301440700290602d084420251a50035203200c250094948208009070104504514030740440c40c820740308800c0c402a410600c0d41d82d519052184040c1401c03d0166003100002c03050940114200002c3c0380406552006641d81e041408541d03000640c00d45501 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 587729928 1250 587728678 587728681
    0x10e061c060510080a05061f030b1f020a1704170c040507110a03120f02040f18110a0815090a1401090606050406050a03141512010b0a0b070314030f0708 67
    0x41c60039014928485146442c0c0c40d8035590340d022145c2c001c1c08014000c40e8030a00f02c481180800c81e90540d2096030b40d02986002404920030000c00c000e8408900304030b01011402880182c07030319030102c3c0c1e0304003643e0300480c0c45401525100c0c032070161313000380d8200c4000c00d541d1a0725208011400211313982d0620040e282082242c036400d408842c20000300c012098103520250740000043d104008207101004a83d000061102c401d54400c7e003603030f0141c0d01c1048c009542c580b082c05030543c4204040c1009101480030031190200045c40e07115800386042030380078041d20780300154003030040b550640480000104007420616064000400500705000e82d0380d86044900c00214031213542c0d00c0b401040e2030a644586007440d02c1c005003280c01390300c0b510b4441d0406031181350020030105c550728114041c10382c0e085d0a61482c0149400d100000c0103621030021030341e04103500c036803a0b9180c031543e010035115500702040d5960b07168241034a15040c03081404000c900d000003085007144034030031120301038002a0b454800302e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 587731178 1250 587729928 587729939
    0x8040618080306130b03010f0e07080610061412091e03160204021309050f16081b1b0303190e0622060902031614100c0809010e061c06 59
    0x4940045008101c8881040030503050319104070149402c2c0a260781c04640c80380c111020a0a40b01c8603544590016191070700e043d0300d072000740014000351003290010081882c03c101d8070110154540b0030700301401049007000d40c10180d294111502101001c500401d10704040c0075240d03540c0f8081038204e9686040188100710900084202c07813070b03410001076480c00307000030b9001c01c030003544103032500e00440600d80d100040384519801420f10894403c0d614050900e4900301040b04043c00100301000c118644c4100640744036498851100c2210401e00c035070701c58800c0e4421020108031140300060500c000700030045203a00b42c8824143d09401c000007844204c50b007005456840318181e52000702003607250908001c5065959014a015024000205d5418104d401281c18641d4a030321144508400050078004c80300021031240252000392199511042c5000c0010443c0342d4407200240030100c000343e0314034180c1c03040e60408980c110080207955242c000101c0d8410a414200321610102e05012001a9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 587732428 1250 587731178 587731211
    0x109080f030913140403020309040b1002190602041a030a1d10150b0a0518030601050d08130911040f0501030501030f080a0908060c130510051210090c080406 69
    0x5800191004604100005040144019880e00e0807000c01d66229105041403013554101e5000d1402500135503a0b81d02d99209001c01c0d40c000940e1103015840800d01c6035410b542c0020200312071100b0030441c00c1606c05900e0044c019105aa00c0180c5041d0000102d12045035083d000f907008428080c801c004a070352220801041030480f00c802507054100503404001c42d421900902d480c214890451141280c0300c0350000034982151041000241d4049200c925203410591041c0e00d501045008100d00d624000028944034a007490061138100c012698071900c00e104044140030b080a44010701450444003010b100c48e80161060341c600da22424000141c5501900ca154140c03a0000d1000308280a80d858040942d44608501e00402c0070754400006c03108418421f0600545d071040721a5503c10351a03005203071003c101e401151207800180c21080302160000100c400d0105010181d882c3c5944a840030580c840b906d07402180c0043c18026046200c07030703110f001503104a11402081001382102c400350b03107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 587733678 1250 587732428 587732443
    0x114161b05073008190908030711130905100c1107120b0a0b0102070302040225140c0103110a0315030c0815070309020f04270503030907050108040507060e0f0618010908 74
    0x38085481041517483c45100b4414080d655070242c1000d1001c83e607600a001e14591000d40d060700e500401100700856440e00c02284c0f108020944418403450710b40341c50795500c0b6520240b03440100c650381c0080a00c441e000e0848000300d000d24400340c511b00b940c0d41d810b090300a440d1310030482d25520700700300142e0402c03c2403284205090303061340100601421503003804002c0d403000c441d510760007500a8815510107105803043c03500314030500e0080264520014080e190a10b20b917070b0745041c9820900c48142100d140e90070348610585620300170070118110b2002041084c481d0704064011540e1000205181d680000e040c04400040030101d01c181d6125001207040320103201c80298401c40483d900b14880c909a00b08501e00a400d0200e0f5040844500044020b1404040121290380003c010840d24090a000c181d00600003800e064000d49016995561502010b004103014003014110303a4481c0c0c1c40340080c9604594016052681d1914100ca81d00300d071f84d002205103800a580030300042071403640440c001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 587734928 1250 587733678 587733683
    0x181a090f0a1a0406111b01110c060a1d03220e0f040605040c08030a0215060f0918010605040f0f0e07080a060f0e030f0a020114161b050730 61
    0x20304142e11a40803a050720040548161541900c0e020b00ea40004550001440700e8111150320801d85964180442d0950719102c8440301c0c220300034800c00b107032101d000c00c052364010041c0b50300044250420421130380102401b00082c0c0c0f1440b0100d0201c1c0000040401d070440c401c951400c880c0300c1e83d501c4040380c098190031959442c000201e1400318000440e02c0d0011030b001803040c030002d004181c80b032214a282d5000746500200503442802002c0512151240f401d0700502c0a44a00c2040c80200d40030075444803001c0e10541c4a5151361130109803c00082d4410400740000500c14826104d04101c500054504600750616040c6013200c20305089400140e004125000c03074025103400c9440d6101c0200030b00400303108000c92520790003510f00c1d2544c03e000402d0b203c12a061102d445003403040c4000c0c03c607040e160194810100078000d10901003c108140f00f12080c50345062001000301e20141042510507040003070803881020408a900289810280d610071105600010b08802e070b0302d2020100c1800303e401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 587736178 1250 587734928 587734943
    0x224060a0e0a090b070909060e0105030304030f03020c0901140f030105070e04020706090206041e061d060d0f0e07080c04021603032304050606120d0f03181a090f0a 72
    0x20800740348450001588003022a20009a00c541511604954070048a00c10001501b00d6828080b400191003220050001035218201c60741c1003c0229a4074803175400050401c210f0300440904061007001101d03005030000c0c1c40c40002c0c1d690740c000364283c0e1480da01c400d441006011038171403260805103c0d2620400183e40c55144001d581b8090200035032100e481618002d0310b5101001c05030329400b0080000304034016000c029600d103041c0b04901d00e0040c4d00808208100c01d4802c1030180d00e1006140000700301180e01d20f030b5038a4440030079002030500601c0b03400c140307003803100a0f094060049000002c40381d080054500031303100c07541040100d10400c0c8030340c12030301c64400c211000320344039501174030601e4034040910208102903240301c24881e8045070304460b680d021034104a030a05040c0c0d141840d0940d07100c0184040c21080001030424401600300708200740d45c07400301e60300907080003000000c41c6802141341d100c0000450031100c01014110b030204d0091080f410300728011030000905203240380d00080c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 587737428 1250 587736178 587736199
    0x30712050a0f050d0e07030b06010318030503040303020f1b0a030212041805070e0d0605071e05033903092803050306031507020c01020f070f06110307050d022406 71
    0x241030f5500d40101440301c100d83ea98009024001c04104003400203103001d500c084a9a25020000506a43e40c0c00c01e0862007140602c90003000036000820b50381c0144d813604002d602d540300e05e0140b00bc03d024900180d008065003c101150100e40420a24405402070342503d03140e05a5404d42c0080344103034880c0e4480c1424080240342c0c842c42c142c6c400c64010900c2d151101091646500181e1400309840701518116030718028015440e4102c01d01a084407000c011506251001c544058541c1c00018149007070800f01500312243c00c0c1507520000e84802901443c0c2900c070401100c03201054200715841002032080012041901c091030401124031019508104400c0360b8566081350240c002801042d0113119942508040b145849209072040b0200c0e4010008c101d404c00c0020324100584401d003519030003841040c030810020b502450306551540c00d201c0c1e01443c1c4421028958441c0e10f2010f4100c5c0180c3c0c0385500d40d183c0c0803801c10325900f0030901c0c1070305001101d0a000d6140d1010ba840682c00f0890340c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 587738678 1250 587737428 587737457
    0x10b0a0302040e0a02030607050d050a0606320a180f270b061b1519090812010609060807020118030f0e1f03110c120702060c0708030712050a 62
    0x10400f003c0f095a030f50548104c1c00003980401e00e0100c06a800b0780c04244003060250083d0540c0c400d05521410600050040901e8210702a010035a92045404400340324145445050b24034072130030409017004155282e4a0031a0a8000e01c101102c0440c2020701301c0d540000684010311b085103034144c81b0005090030000742102a801d41402c08071190b0002a030312020080443c0e62028058008801002c0794101c610050307084440c20807086691820b00c010071034040c01049610110b041b000080c0e4618005010300c11070400c280d09025030140e40c0201d00100002182081d40300c10070404039041511520318940b1041000e900b0b0f11421400d0140b00c5110500d88008284155001c00403003500c0c2c14480c0c2d00e0609440032441d01003503201c0c00320014154262010f02903034180302d000580b82d100c6034154103040c1c1c600381a0ba114041c100701601c041601040c2c031011340d56004102e845e03003001d607421100c0d0f07180c1d6441c42d19101d400684d030540e2203400181440c14454010400c46016624599848013401c0104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 587739928 1250 587738678 587738681
    0x807170f0708010b040b040c080412020c060c070806010803070515180114060307060507150c1103031312080c1b0c0406180506030c06070f02060d1b030608010b0a030204 74
    0x4021150892284442040203100c0c10300419000d02501d5002080b42d40800f41400159076080410502407854243d003008000d5000c5100c1e60050340c003a0f2024603c0f965001c0492502d00a005600d5120a0006000101170400540342044071414401d071801e50780c0c5d038066244c0728026000040d11300d4100e01c0410008491310500d0550001901141020381400388514608440d1080c0b002a5140c03502c0e014440310b85420058400182401d2034903900e8131105541d0302c1c1a42c807482c1856920151070b00000c2d0020341c080c8045144c0c0ca18501c2c100c0e5200d103422084560806c0142c4015600030031000c40300c04003e40b1400145100e0105441000c1c9450109000f8100704500340345080403d00510301584d0a0381d4803405840c00810480c0a5080c0c4184640c038001d08455000e81a03900c40e501010448929440d00002c2e500b10a402803d010342034440ca0000c1400c1307100740100410000c5c540100091410b10b03010400c085a0b0301d55a08000c2c030303511501107500303e6050b4108194054140740c000c00051a16 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 587741178 1250 587739928 587739959
    0x61203030b0a0f030b07090b0c1002030c0721030605040227010c211209030e06030408090d1a070201060503061b12100519050d03030f0905151e010807 66
    0x540b00042c01540c51400070301c0c080380c5810855404010710140200d60b6403182001010304113400100f85804101c400f06136551007103091007042d0640210010318083c42c00f0090390b0049410a00c0c035141740380711031016252441079469410204c1e00d40384000c202400c0910985913104408544010030700300c13121440c986403800c81002c9040040d2012600005880740c101120076100a000c2d40500e4a12020007600c030005055111103264a4040b07040d0100e540a1859540d20105440583d07a0ba141e9040c4000e50340f1030700810503045001e0300070072020800c0e04910048014600301d40c480071b07626002012800d860750f41c41490f034190b20840c0859110351580400701d20060f18942403a00e82000650005002e82040760202c0b80b502585c80100800c1c20038205000d83d400524042c000c2031420800011802e4120f564081d01701540c031710301c80309104c032650311030400240c12004440782c0619040c4600e828240880c1c2041ca040b55903807007800403014216003903050305e540c500030300034540c14244030760010b07001d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 587742428 1250 587741178 587741201
    0xb0906030a050901091b0f060503190b011e02070905070c050c0f0d1a1501050301031205070201090302031b0f060903071814070c03021203090c0d02131d01050a06120303 74
    0x180c031000e007000201c00440e054202100d00300a8090a8a400c007c47e003c41c00399441002404800c000f0440421488180000f1412000c240003c85500d420300484400c0c1c50b84400b85111802310806145003600059410102ca03a0005c051105035603070081160f000320404401800ca520483d81c0800c9031814148070942c0c003c02030310174402800141c54607900c1411100882c032980a2003800e01040000701c881106100401f070a01c02c0c07a43d40f441e0740d01130200e01a000d589040200201c4c49208582c46110210011031b0007d0071124100244401c0f101c8003407516080901c0780d003120b80200e95500704401525200000140681b500624003148503514040030100c043c000d50b51262007242414101c5812805844c40c0d544800401c0042e19000c3d141418820045680ca01d09004001b17144500007070a1003010025585090910710b01c1c07010a2b403800002003181d62003814958440d40580750302420310f220000600c020301c4192103080810701121824060441903603220700c4075001081c02074104820608 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 587743678 1250 587742428 587742431
    0x132102030d0e04150e01080c010f0504230a080303060406090606021011040b03040302100c02030310062001050a02070c0e041e0f021e0102100506030304060c03030f0e0a0302070b0906030a050901 85
    0x282545040c24013080c0d5000292150720640060180710000c01c290810000d003030070072310ba060f104110058a0f40c040c510a800300e2800340350750491300c00e09881d1001c1e0001406004000c049444501e280d0310307071b04101c3d031440c011494024009030300350380c6010f03240c2200c0c2503030040c154100c942c140fa40301070080601c0b00041035000304800036043d901900258852402580030b8030002ea650309141041c2d03810800f2200840d4810301c1840f0005511840d803108881141c00e111904108204000d030100c0243c12021005510f80410005200c4558000700101486012b002400c940c071100d1100c06c10703400765000f03040b4020140003a0410041001c10403082c6020304170102000625034001420000d01d450383c4083d28100104049086d41c04010f00b1101d0b1140034002e212924181011941d00d0040348070341000c0150f052081c1e401d240c0681d2001d0703248070091500340102d002900034581e0303c0810000c110014401d81500144c00c0d07403160300352515000002c104a24689460740c50b140541400303400c0c0e007644e5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 587744928 1250 587743678 587743691
    0x150a09050d1404062709090b0114060a03050601022b1103041d043305061e0f010c020d0804050a081906090305041203030b040c02010b0d15060506132102030d0e04 71
    0x1000340313140007004000b03006c404203c0c5100d034500000d0302c12060f0300041444001880d40c9156982d91170954a00c04100d2030001107030f54400340100c0c176200002903030600610802000107410a00c3d17280e01c0588005a0f02d03004050440d80281e281e4a104621070080016003105910111910f200c01682d0424050090403800d48007805110006c50a5084840001c4c9043c031100e00005e81680600d03a4400401c0301d014013a41c20140c2c2840d01403007009049442182802c1d10015107a0250318501302854000d05040c0550b0001d15041107207030b016000351882100510030010301007078006801c9250f41e130325009000307683c100f95681501801c01c155003102400030600c008540c40078502e045820490295a0105016080d42c040c0000c4541c5960080c04590420703100e8251910b508204048160340005822280e0341c000c503c1c5001803109400003a0703c15800103c07007444040b0105110156440f402110710b1501409480c040b054460210094150304107000350b0743c0c1e050055401360346c014000b03000442d81 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 587746178 1250 587744928 587744987
    0x6040903050405120c01020c040b010e040902041e020d2a051c0c020102130e131403040b120a0606020a0209010b1308011e061d0f0405150a09050d140406 67
    0x5a00f4104040100c1d030b222044900486d0b80c10060881907040c182e03010003d4020010000f400e034805808524000d944861000d0115101c41d4007001c0c0710750060100b15040e28400c1c1300076003c2d600c4007101e800d442d400c00e40722074141e40080b4a806500c0102560900240f072005500740c416402c2464805a4140911178054410310603000301030311520f160b4001a620300840c07280603040302c1142c122113500520141040ba4072101009009807040e000324004128407240103200b40307103100301d811a032500540881e8031004195181c5034503000e080c0421050102544404049035076049001001c1e42c444000801041141d200c0401480f84000a41f03544034100d03290211142500c210303001c2181980c084180781001d40100c0c2c40f80102404403091406810212494031108150703002e401e48854141c610042010050b04002c4041d071040c0003e0206594942560107070006d08906005031994081c2401404003144210b0714410b041c1c0d201401c09007028240300040710081c40c02c0c2091190405c02074440d079034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 587747428 1250 587746178 587746189
    0xc0901090506120d020c2b03080f16020d0309030509030109030207150e062218020405040e01020c0a031211340c0b0a090b03131707020906040903050405 67
    0x40d200c1410046402c0c00c2060a10030600384050141003950000700c1521340c0941e021690462443d0100c6035850100245004800c002203221503a245818008520104240d004150783d0300c03a0100900703030300c038650f2940e8032010070714080086d07400160400000002c0003030083c0d05c613040490083c60100d0408601c80b000c01e00312200070a099000d40d00030042003001c8510380c040390003541d4003803921400c000c1c4c1c00c10200b8485d001e0000810502051742c0303100510100720074803100003400103a07401c02c02c030200c0c0380b5098001d6005005071401241800c1028201d404140222000c06e0b111100a04e40c41126480c1140c44542e50100d1092071030b220107a00e003142c40b0204c06418042078550840c60882d080568403082020750110412422200d013003104041020401400101c840c040b50303065031000100e00803034a0b103440307411221340c000c070200500600340e0035400c402d0070b107904c0340d04642880e080071100b20089007e1624029030225000d0002491410f060b0006070945219040c03003820642c40c0c4000a1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 587748678 1250 587747428 587747431
    0x8070c0519051003020a09030f060e03180a090209131a0301020f030f0601020c01020619150602011a09010f120602070501020a050703090e0f0a022a0102040302041d0307140c09 77
    0xd284940d10100b440746140054008041c00030038141185081c0e03107101b01410013001444041c0803401c1e0b003d092410310442c0c0e00040091030108003a6075581101032104445c0079024040310340140c20001c0045590b40d4684219520008000c00c510f4428411301400d9021309460300d0110b003c4c04503a150b014484d2000d001070003036611184109a00da1134044001c1101540c0140103604541c4007080000c8266004a078680e000303d40f081143c160422208007480150012600307900703140c42c1d4104005411641035000114032074803410411180c1040004110014800b0b000e4004681c211030401c1248044070502c210017103115440250078018903807281e1f070881c1c000c100ca950103c0c000107141c40c1050b0b4000d030041d0103031075801550b2250741000052140c22003001489241002c0e40014102851060202403100f03031040b00d8510f10707082441d421900d001c2d40152008a0259040c440651507a207034480c2d410f0700c0886140d0084d410003240313844010040c1560721364054103020f500001c1e20700e07403520744c40076 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 587749928 1250 587748678 587748709
    0x515041506140f0313050c0d080714070503030a03020d06050a09141608070c060915020d11090f010c020a030b040c030308010b0702130b030c04051509011d010308070c05 74
    0x2080e0149030000260402e0301c642c1ca40004108108a242c1c10b4a21070400c3d2900101d0908043e201c0100501c3c00c540b07014500007207a980038403e10500b1081140d801d0041c10744611401c00d44655500b00032109584003480d0041c19407581060020f0303e50a44603034054030342e0700403230440400d0240e40c3d4404100f00c2403407904207510703868550714002c0102c1c4010003010b40154010303000c00441c0000c1440280b031100060b140808100100403003105010b104d0300450485500035090b0004a0b9101500704001d41c0018245c0050302d051080c1a9581e50b07000e4160754031000c010b0106080105001d0045861440340c6204903404042c0c1c05d00800441c2200314030030311651003410000c502c03d045040103884c03850140c0c091403080c00200304840040c0c079aa01d1240a241d4074600224903102400c001a06040c404803034541c00c6807920040100024881108602c004401ea4456040303980fa203c4060841801c0d41210f8070028a04004000180c011b0008000d0240540780d8145078640320000680c01d0120301501 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 587751178 1250 587749928 587749961
    0x1050403150509010b1903260d1d070321020102040e040c03150501052107080109061a060901050a0806240309070b0c0a080d0b060a0809100c12051504 66
    0x100325503c8024429915401d1040740c060f4181101c008010030b03518803a01004196800c41c4105400030b8044481c400401004040d0894445110f1404200103102c030307095002030451031f03000844841002248101c2542e4101c22611301c401e150030548018420801071850840d0340c01c0000180f9108102d02c01e500840c2f04a104c110100d2542c1410740d80001e144c802007030402d01e04001000309a48840c954512100b17100740c030100c1070b44040d040a0403d890b41c0c3c404aa03d50a007042403040100551040481d403d10741044151030480f00e0a2003083d0140880090100303400f00030540005020741c0b0980e0340b0000041090208403102820410754600d1040e000326008404028171500301c0c3d040c00403601420050307103540d007084040c40034180e035004c0c0c0c1d038400b501505c00016692204001a04544041d2002929542d40c034250400b0050560b801195950101d010305c180b106080d0070745004200f0403000a0361800275109984007900002c0102400d0140240780c039441428903a1501c1c060036840c0710b01c0360318 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 587752428 1250 587751178 587751181
    0x13030c0308041a0331120314010e04051f1e09031b050304090b0303040f0e0402011b020306060f012c0f04060b0f07030c0519150e07030b06010504031505 67
    0x70f5001d00d42c000010820450003401000808560a08040007840448010b1090480d40700c0c01c200e580c44000321301034980c03115116580865500358000c51030400713150100e080580e030b82d90107911020006860050540d01f00080480320f80700a8818848010441c400029040b849c00440070641d602859480c001e558403592450203140e002050354410500e04007412000104035910709881c4e10844c0214540c0c1d50f81d4074851680350301c00701705032000341128655a6241c1c079201c1086424280c0c003241c080b400200e41251084044100d0030a010420354040c0041805445030f00c01c101070126040c0313040d410030000740b52250030204003160154041041520451030741e072101040c4412101e10260382e602075418040d040006016103012224450080d00c6040d0b110180f9240071103020002c040c1c040c100348500c2e100021554191810318682500c20752408020035004132085c000d0700c04a102d0080c6541110100300040f50fa0310000d1584190f05240c02840c050f102d42e07503403420100a650900c88103907078030b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 587753678 1250 587752428 587752439
    0x30507300914090118020d0f06050f010c0312110c03071202070b09030a0b07051e03072d0c240e0d0801230301090204020a08040c1a0405010513030c030804 68
    0x200380e0002c2d00701c52038041c211004038008190028018440c4400604400b0b0880700d0101c2c080d8107580801030b00d4401482040b41d101305e043c010340264042c80f40b203102c0c5012140255130003080c00c00d006a40c19107940c050001d204030460001d040303030204104bca65041104010a401c14801003013482d1060940400540840307400034686503141e00660a800310411460340d007503400242055159500c542d0032490340e0f9030700074116003500908406031300c1c40c2e40c240400200801c1e43e0001d1481080a0f0b40c42e901d488103020340002c92101d100518114080f03030a4021980e140c400e440d1082c5090041280080c0030b078031028200b02180e2201045c0e200c0075954061818600020f200c0103440c6041490500400e50601c0c503a2101003401d02c204540c8940c941401c02002d4030b080d00440c00523034004004548860140344050090380085408444003005044041124200402441101102c40041ca0700b0035080100554441c0c1c400c04143c00f40814a240000c0002c1d69040c40c00c015500c01c035240d40e1603d2400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 587754928 1250 587753678 587753687
    0xf111609051b04080a08030411030601080303090c0f0609040f0902120106030308130201090e2517061504091a060f040e070504120b0601030207150615050f0703050730 73
    0x4026490034002c0400c41089454000101501e01640080032955262568038208041c03000c0b11000d150503000300c0000084100300030024502c919103100035160309014010410103803000f2440341d194400070910107204a400c03d03500c841c050421043c2c001400d50b03204d40028504880c0d09402e4082603441e04424002c05a020f03519030f8005408104192200d1115400039200c94a10f00444c08050801c10020360001c0031b00c0c8094140000b59440c240001c10b05210003022001c0c00804030202c1581c2e0350101d070f0701d03042c0000e4900240148600341814103042086950241c812074440e860b01c005a01c5404c24140e0310710700103004403004407031a03035512032400808e4106404003c0508003848401e00042100060081401c2c50840d071101c0c010a55583d10001030b002030244d03100140080080c5d401071f412204035544132000f03503001c0012004180300081c20403106031080c0d040800503180c0910902c1c00180c02a8054114148280c850800c04040e00c1000c248111140c0c00c0c9030a82c4100c01480c10510b90403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 587756178 1250 587754928 587754961
    0x601060c14161d01030b06042307170711070311060c030d09050c15030403050d020f03040b06091006050f0f0f0705101a030a0201361a09010f11160905 66
    0x6002400013585940c848010707803280205041e00a5480751250360000c0040c001464a0780191401e06da00790510440042c0021491030403161040c034103c000c40c00c0c0314082d0079146840010b0740d001305121400e640d100340072982c1c2e030586a60803650030f0200e8000e290b800c0c0080c1c034800070149000213984000e401d00311310380400328114500075000d4242080741d0001d100100e81d4860703050300307082c0c0d510114210488024440c000d9142010000030040c4400c01441807a242c0c028442210725200c070391210f012510820440d48035a8000c10002c0020082c04141c080142c0120300c20111803e042031903680070041030354444d00003140c1c141c200100c5014032032510300ca418040c2007a070b610001c664030b00070b02007030341c0e4444258003038180f001803c0742080540740c555a0040d01200200e01c400308002c041d0f001000c5044030f00910800f41c8d1a02503c1280035014025640100016507465019104808080d100303001a040e070074070240600600e00c11900445200d480c020001d50800080034030706010200d600440 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 587757428 1250 587756178 587756219
    0x2031f140a05071409130e03030601030e01020a051206060405040204031b0812030105130e0d05070b0c0328020d02040e0103030f0905010905190806011e0e090601060c1416 75
    0x14182c1800400390b807002c40c3e40403c0d006044103075903039100c0303000142c96081d00c006d800d0031041c02c0c4280b1000d0320801001560103808282c901740b002d138130122510f078240e010704d2400500080d414001241040c0300355101540101d000b0748001d103083d0b16a000304080e603006402c2a24000b0300d400c80c01440c3d04001c2207800050540d0006005590050003696940e48010320a261045003660745078007611982d5448401032240e01803c0f265842c000000103041600401c0c001c3c0d030b00855190004103c0600710f000c4034414004080c00300d4965060f1f00c0d85000100c0e4024000041c20741c24400b000840116200400c042c020300c50700b050710783d80741d07190017002d401344544102d04004400d20200308a98010186105030344044401009480c10103441624004084d440400700e4400c0c41e000048820b5032082c03016408119503130344803013661500712480300c181e0281d903417140c180e210000412806108004c1c00c2c200d10722070050915480c20006400b86801466200c8004518815408100300b00c00f8500c1c0c110000b9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 587758678 1250 587757428 587757431
    0x405071d07122a0e01090b070204180605010e010e241c0f1a0c0c0c0108060d0b16020d0201180602070507080303010f0e0606090d0f02031f140a 63
    0x1890052480c0c40110260864003402030000030116480595049051090351080d10501d004081c50705040d161540d0411050200d03070a800d803d802940b1904030f140590700701c1500d203490084a5400d01c0028000b01c200700510007100e0a60f000050854012103009140d130301d542107900c0d418113442d41b041a50250010503078131003003602850a40c03240e1140c0ca485010499080c03442148852000f010040c0c1c0b49802000103200840a1081042c54884450004188130502a859a4416404800c1d02c14000d100800d41d11020783c14400d50311880000b03920007000752900320a01155a01e0140301c40c4180c58040051820b09041c0c82800d44c10070444456501e00e10091004414030300b4018081c0a111102a1026400154032014403904205140003041e0034000ca80d565a51850b021248001c0c0d030107510404410400032039034901d0900161103291a006041071030740861a5900d2034003ea11b450200d07018082e0300080c070002d103080740c07049001d8000300802054106c1c400c0000b80e942c6400802c0f01d10b03910b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 587759928 1250 587758678 587758709
    0xe0403030f181101050d0c1d01020f030d090c03151b02061323030307020f0c0301020a0f18080d1d120d0c03090e07030911100e040902060909040308040507 68
    0xa25011090449541000581c0f04100c070520040341c040c072825403080303600740c20841300400960384002e1080090f054001c20000f480800c600498440e02503202c0700721a0783c422700030031a10110f04d80c0f240c070300c0030302c1004210791450352a03503440c5060388003864242c1d01c66507030b40f0810420b0f02007001013040f00b81180302074074161a2445014038000310314070740500f140c1c81c0c40c003000041c06880d10b019003d4154a00c1200d49038601940001d681d0070701d04984070030900502010145c0360405009944030440d8030f0300d42049106500c601210138050038152207040f80c1004400103144a000e0203070074000710017955590403900b103091a1040c000182c9c100d030740c09101405040814200c001c6141c4000703105030b1134103030b00101003030804407402102d68214070120040c09061201940d0103a001e403004601c00c62180c0d00344010700c004c00a040340b111550704042903050518a106140039030040802c188014800d80c10054004040340340c11208580031000b10b11104d007400103200040010400401007a010000c02 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 587761178 1250 587759928 587759951
    0x309030b130206031512100b0a0909110f03010b150901180f050411070515070f020d140c011122121101031802090a0603110d03090b0705030f040e0403030f 68
    0x3d440b00030444c454020b50f03045d10715402d0392616009401450741104441e024284219104020070400007031511825803010b0003e088002d1380110104950040c0c07641900c2031008089c00300c2d40200801c480e074155610002c14040b030ba0707914090804020b549064503116a42c0100240400d009500ca5092002158501700704403494000c44209480040e078010900c0007c600e00840140104400289580903a0011180720b00f460b0342150302c101159501e0031020b8551200698641e42d04880741000a0002181c001d21203041c1c40041c030070818040000201440c00b07041c200015041410b54042454030002c120301503110059002c0d0140031108002a2a03200c00c0d40ea240a80d10000c1030f460515440b00c20340700c1c18203040d112006501c1d80181015850349846151140145480d000849259071002c4e8404040e007000b10f6001d10b80c6a164aa11050728100007100c41d040d0010202200c030f501c0100854512502848040d0004200d80c9211004a04152801400350358a5405040107103160003c070100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 587762428 1250 587761178 587761189
    0x30702060105090112050c2b080306190302210717030408010f021c091b270506031015170d02062404020903010608030a26040506161b0309030b1302 65
    0x80c03010442d600341030708c80009020003d12410f03c07010740c8101000f2800b0814442c038800114426001100c807500f04451182c00b40303640c280a408081d4028210f10b421009034065000d140c281001746001700c0d41061b13940c40481c01004a007084194a5400105040042480034013910412609660041d81000641c1405840100001c085107000036181c07036500c0d0a000800301121203041c1c00c40d810420303c03912644280c1e895081550200c2040643c000d4124041010b48903160040e04001d0290103001c01c0b622000c005003004d80b140c10b440d01001c2030001103e01401010003a04e0b10110081d010110305200060b0903d8001000000e07100c0700501a5054103c045041e0044c0c03c0c0b085a0068941c079180001c20300400940d00001114400052048480c40d0041c00f440807a49400e450b405000040600c012482541520014a40d52140021890880c0510414422280c1c1da20707104040071803d0241c03400c8500c400c0780c2500840d089200520034086c003c81032662180c031582210100c0521a4040303603 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 587763678 1250 587762428 587762443
    0x509070509100513151107060905010c02130c0806030f06010503030720040609060512010e030d02072a030c0e06030d030f09080d020a020c120c220203070206010509011205 75
    0x9104440c1c1142c8890050701440680c1c801c8001d01c42c4090b0b016031140007560300b940440c100d11000c6005c1140c43d0780215000240399055a003640e99000d01c5034500401034400c400589c0040764800d000d03000c803030001c04d214828001c0005040d919680c141c24030009042c11700440400c1741095401040061001d510008100c1c0d410a074001c10708021800701e040070810591554414527409820414005101c20384d0350070000c1540e4080300c400d031450b065006880c0c200c4d0803189004125800c103002c60030030094254044c1c03014500520388400c1c00603000300d201029080e40313070503c01c2e601020601031080c000380705110f0303001d458881120090b6040000c0082c0d610004041d0000416480d00c4801d9058080b5401c038a0030143c2c40140e07141c0710042c2065080283d081303071155200600ca41c03a5035400510380300340c0451010000c40042e0083c3d40c4c46406124034200c00048020321a002c119140300c0c10040380c401144200600c0d030180c602c55042004000040b28181e101c0140b0f0104640024041f460118490 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 587764928 1250 587763678 587763697
    0x20d02120a030207060c020a12170c07050102070b01061106070c0b06090a110a0e10050a05030a0b04090803072706121503020d0305030f0604050f0411220605010905090705 75
    0x4940328401c1e00c00c218040d10805600400390750602501d12141030300024034030b0005100c0c0e402c200c0d0b5100300b1001126041611215006148040340c0496620b550040040441a0089001520340315031a00c510411500a92020700010b070018440040840c0030311900d5089900c034a04840e611070b00b03444880e40d0040140029220388006c0e4041044072040c0c0d0f21603080407800c900c1554850f901c01401401200566699038007400d180d846010043c0d118100f107a0300f400f006d803119815602c1e21a4224010243c011000350003e54604240c0d0200741041d002d54890700541e91402e40c6103504043c141450384448d41c0b03100e0104200002401034541188102181d60601800065003643e1b92544504106503a44065040b040c00d02110303080c0360780900218400da60020502101c1c0d1980701c14001141c20803140964000f0b640008100000c2981e0441d1510000040c0300703032001a030702c5400a820300e00b20703000c2c9940c41d5070342ca20420455800a03100c10061000f00c03601c004070300d0718100240c401e01c18001c85 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 587766178 1250 587764928 587764963
    0x1a130f020910170705030105011508041e080f0912060124020a021302040e09030c030702060906090a09020a02100905061f0e0406150816030201030b0103020408030f0316020d02 77
    0x10000302000714010028003250345043d0300d0240b004282510340a081c09841e00a5007020000300300c030704106025819215083e03444250603520f9440b040e071108814480007070a400c0b0b0600c1c3d400455000c2c8050035500180000442d271b6111908c04207c000c0918001d4100250070440c010442d00202c0d52a4400440c0c030110700c64441056200204d0a01495043c000d40c803a4081e040180e03110070960113001030b206a490000c0054640742c0126035680140b80c0b0205917544104001c80060608001901000c0c80140015050a61341b8000800c151001d400c1200c8136039020500b6081d040d41000710840321401500100490100c3d9100c80d5100c3d04001d194204043c1040000640c1c142d010208000520402001940c181420714202c0060002d0b00d0112582c002da55101207610340c1c1c089600026102c000d141d01203e0b070f14503401903020709020702c4020b040c180d00b03010000d040d178000e00c024100a49000c0034250f0f82d14010391070f0b02d41d1800001c89032045600403020903a00f1600020040103511900c881c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 587767428 1250 587766178 587766181
    0xb010807170c160f020901051c020112021b01091203020a05221a0304030e061204030806010908010e0115140d1e02060c01050906060111120705030d091a130f0209 71
    0x200d90554403c1c114018004041200e40b01d0500c004860f4691079140700b02ea00071401d0f42d0701e508100b100d40400702901410501c1920395001980680d00058411100e00c10150910070000c1c50380c40601040e41d110012a51074049090400070715030783d2060340c80c000d4201181401803070340c0010414024040350903c0800041c01c44c0203140203401c0f04500410000c140c08248852f60710451005410940741140072401104200d0100c3c80c12005450002c170011903558166a103644080352162009403a0b00d052042014012811450a00603820009000300000c00c00e008549040098030030550311801546100030040703200c03a035441304101c0c0626001402840c000182c3c3d1400c00714480585030080d4040e4000440311500701043d0885441400301d02c1c217035203082c1c0d5800010740c0c05210f40d500300c000582113070b00410044102c14001c0c18540d400b4108076410424145d070440c0442c1c184c0728082c0d80d0481e620203145248040807640a5200207205d014000d1030b0425611144038148c0080c000303100358031310390 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 587768678 1250 587767428 587767441
    0x120a140c07080303010b121b07031d060d02041805071e02010f060f05010f0e0306011205160803120703090f1101112a0a05030d0c03020304170c040b01080717 69
    0xd1a01600300031007030f60340c1c9503981c003401442c0350300c01090141c404240200189504064400035003503280c3d050b40b9946040f000355401c4403060f650b0344480940c3c0c00002d1255a4a03200c0c0300c05001103140d0090010f0b619410407044141695044c03e10080041c28002004100356000d0800241c690031020341103c0c420818030f0aa014083d094007085110746008000540383c1101150f04e01101c0003031300d44510b244641c11040351b8201c0c2a80c038640d050752102e0700400c0000e02100300302c10024080c0c4143c504402d602d1003501103544095012001c2540007145021050b241410703059045040c42c1410130041c8141e50f201e00545500c1d00010b404956403010041141e402404003480d103100b214143c9900b03444001d40c3c1412868541c440201044d5400c5c0040c0050410b4503401c000e8810040043c100c003a000c1d98121001d4406000803400c50005200005e030f0810324140d40c081c801c209602602000384240c00707203c110b0b902c00701d80c28100030120303041c0701880f40c0003251040758086122180c20590783c1d00c6d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 587769784 1106 587768678 587768683
    0x191503140f01020f0a17130803060a0b030f04050606060c06010b0a0311070c03060b1c0807080913060503060f04080a03050907050d0501050105040e0f100504050a0b0708040302120a140c 81
    0x30541f03402158038140955444003004011190b659203a50310b4035440c0d0030540d0b002c41d00d261803209110802c10103000e6194810025140582482680c2032856540c80061090788d035001c20000e03100ca4501e20940104003501214241d84c0d555040600d040d00c4030914502c81641c2042c070300202c04090349004007000110054124180c0d80c01007a030b881b02c04296020000c110341c9400e041121600f15156021504100b400c01000024824604020700d41800700003003420209281c040100000240c00c20203139a0010300a01d0005030560b15800128500120f40e0401c5a0120211085c08100201500058143c4005072010302c00c0c0d4043c03c41d41c9507a810107003050034a9030881901010f400049a015070fa000d400f40781110400d4510342c80d0307004072141c1500e00e6000030320f82604004c185601000503d0f415050b040225180200f601001400320505680045594000144100032040c08 = true := by decide +kernel

theorem cover : BRFrame.Cov 587589928 587769784 := by
  have h0 := BRFrame.cov_init 587589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 587589928 ≤ n) (h2 : n < 587769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
