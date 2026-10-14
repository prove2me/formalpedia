-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0283
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:57:32.787108+00:00
-- url     : https://prove2.me/submissions/622fcb36-b84c-40c0-8398-0a19025fdb73

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 50719428 ≤ n < 50899284 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 50720678 1250 50719428 50719447
    0x206010501140f0d0902040b0315010f0b0405031c27050907050c0a0204050603010b030a0c0806060306070903060216241805071a040302030706111e031824 68
    0x40d075040101d03000d600041e1030560f10502c80b00c294020310b00203500e8141c40b4660768045548542142c44080000b80444504c0100d400401d603014000b0312510210003c51140030070030500d0b81d01110305550024005180441041000650b4850020300c61401c105400708883c680050050741c29110027541150514600d0408040040300c85015094009108007003200c5100500702041400d4119012103000a0594903075011070b01504058540d2a4940100074281342003040043e03111064400f02c1c3c0c22580c103507550344103160b030b030742c201340d6004000c40c1c803054003000042e259400404c000022501c4042c0c90701c1c40750303944006200c80b0052010380b502c0c02032181c400205603403080720030403110303144031040b9003049803903464441006008000e91864900d680041c1005080300707d9004603800380842c0ca42c1c658940008000c4c0494000300c044902904003001c20640404241c1c00e02014003030080d5103031085001c0c485140c000081d080070380240314041e44100d100c00c120009158030501840f000c0d42d07000501c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 50721928 1250 50720678 50720687
    0xf0f070302070b0702220f0c05070b07030b0108040803100504050c1c050c0711030705090708040507050303040501050a030c0e04021602091e04020607050a050d0f0806100f0309030306030c03030206010501 89
    0x1a0410040d064003440580003683d28042d00101d1b8812040319415803045c0c07101100f01600e002c54400c244141800070003101c0c5076104001740003250003042e001b8140c0d00ea070300003101550b00104030341d07000401000110740814005002181c100d2030f9100080071031550382c2d000c60203071030044412a04007400459808032007601c0888071595440c19050030403c0b4500511f010156004600f030240100c9903039095085075450400150000d032400400c2941580b40c41c46000303003101d03400c4604542c140124000012503080001c2a903050b01c405031200d5041ca4441001207004006245010080050702d0151021503100e501c010000000403289032414202c450060008490000d44080501c820900a0301d507003a04903110740c0d4100d541180c202e95074405c141000d503c0d10b4040300000e441800741c04100403c0d40e8001a500121241940b1165500c0d0303901400c102120508d01d281c4000304040c1a2055200d5129a10900c0c0c55480f07030800081c00b545030348030380d00602e45541048003d40d0140005114540c0c20 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 50723178 1250 50721928 50721943
    0x90303020115050603010902070f080d0902030708030f030a0b1f030507020f0a0c0603091502041e0509060d0201030b0d0b090c0a170c0108061309110112020703020616050f0f070302 79
    0x50610b544615103088041501444140715481d0a140e01007800010400106026064150842803090b1035512600841d0002e0001003001c922a202d1203800044860021041c0d5401002200c1d42c1411541c8400b12407000d00901c2c0e02c0d01d64054220381c1150300f12100303002c0309c400516141e5000a25032502e20000b0749444020300c00d94415030712105007400041d42070040c0d40141c3e2040d2a0105a01e00c2a00c1d190204152400550040782d0001c2004294802602c0c00008803420120741030b0201c647e030308103001d003d5038151585a0040006a108030265000b50080c400340400504554155503442e22100071811302681c04003a07a420002910f00c080c43d2405a01000d001403640d0302650443d01c1c0950f50750b070440da91899041c0214000058419a140c00c005050300703244040920003a802450401481551044054082a050030650f00c000c1307003038825546895850740040c6240c1c1c540b012030340c0049681980d0700040210030014080c001d030555003d0304100c0c0025101c1619480a8900130741007005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 50724428 1250 50723178 50723201
    0x21003090c0f05030304120503190c06060b03062d061308010c0207050a0608100527010b03100303080417070506070806060a05030106050901030b0307081b03010e0a02150d0501060903030201 83
    0x71540611840d1303800704c2180c0442e0840d4056290030b21107454110700754025a0011809487e040030260a1a038000030151070f800d00c10442045942d0b11503903081c80d180800da80064001e8008181d1071a120900c40b00944030b603214407001081280c001c8001496584a44a403018401c803214082040c2c3e2400d020390440183c1900103040e0890505011a403c0a003611814040000c1034000c50341d80100305d110b61000d000c010740300004480001e001c085103504610010703940e0b140c1c071400008002c44803070103807401101491110b04003146540c070f00b143c2000c40a882034422100711480c01800500003001000c445100d40050000d500d489200a803891100a118901680c410445e04407890340c4002242e040d68124100f80e525006000c0049000340320001200d50144103008002c241e80000240040344c030020380001c05049400d8006160a865201300d0050341d90780080790740801454001561841985140b80c11410113960362207603000d840f4207a10880c0807030282d61052040c03590a0141c001ca01c0c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 50725678 1250 50724428 50724449
    0xc09180a0e16061e14040902040311040603110d080919030c08010902030d1407060608100c020304030f020d0f08030106030603030305060d03021506010323060102150112081303021003090c 82
    0xd00d4294003908130ba15840324007004410aa08414009000b14840c4040f00d0756142800c2d240ca4540d85804020342c014001a14030644094840a0b1131034039000e2402600d600c000140c00c855a1901801b50144403144120303280d0070180a1b000b02600c8040100440a012030181c940c84c62460a15400c1c05c1d019410008003070341040c0d00c900c0075880c000344041d40c850440c6001d415819200c2d50540c4039000e1038400a015a04081001903c1000054480002e8000d03040c10005000092000e03070b907078030580c40018105040110040003600d0034804d40c21103140903121790340080e0000d90315400c0c00c1d03000f6001200030954580060050543c58480c0550000081c0c490224007140340d2800780d510342c1c0c40900d50202810000018105034403030f800c15520308c3c080d040e11000d0150911401c2e00000412510640184908202e121041c0400103045049a0011711040d0f4503c001e41c4075030301e00398060910554a61020b150000c01600c1c0d04e2111015101c50395400034031240545040c0d2040f45982e84401c0900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 50726928 1250 50725678 50725723
    0x30606090e1501120504050a0b1003020901031403040506040b0307081815061201060303030b0f01090b0301060f0203091003090b010b0a0905010513050306040302030408010c170c09180a0e 82
    0xc101c04003080d504410700003540c0c00c900c454100121194203441040042103400c080500c02013202c00a44460341a204141c004c00a940da002d10201c141090700c0b0281d4811020307001080031440f0803100001f0001c18809491405855002060b8a1341c0554041e0141d0f00c0004104202d050380120701c1d0360040041c42030a840390803400f86c40b42d0b41c0c0752000f62040070381c0341c1c00010078056590020070540038101c910003401481d0307a80c02c02030000c00c4016152406901b071907000c02140c0d8812903141096a030208a600c1c1942d0914204607100981800e070002580300800c5903035181c3c0da80d611605085c08590b0707004184981c2c03d11303100d8240e150690180b001c1d003400b80000c0400796080817100c0c040d10030a186c0240c890103510030f030405a6025138005e54042c020502888245036010004005a40002c4000c4c001c05032400301c03c070340810340354160034945005000451020320b49a00240500035005203090f0b0b10100300c50a00d4821841904c040f100c0590b600300416a41c1810710040c1c140244042081000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 50728178 1250 50726928 50726939
    0x3030c1b1218030a0c15031b02060112080705070314010e010e1207020a0504020a0503040b220f060f0507050c070509060306010603051b0a0305040b010905070c02040f0b0411070303060609 82
    0x680c0500c102040d03402c09202051411928200101c85185421511040caa6951220700403140140e1071040070011303041c10100d01e00315500c0000c402c842c50041d4020001d903882d280b52034800c01c041c460111844941048190080703407080021002031809000321601c1d4100035400c4908641c500482c01105905041014080c00008038810702c3d02c005480500341d80d1905480002e42d0044540c00690703020b4404038a20711007580c071201031803007a44502400380c150740320000800c64001c00d10031061142440710403460009803a8841d00c1038040c1c8100008a5040345003141071096800803540c04000038808186501d18103030400c0700200a240603140420f042c2071080101e5190041405548103150315840864a102c00d05c188003000300148903c2c1e01e4482030324500090143c241918150f0340c01482d00300225101c060351140314014a941e84540b10280003580c03e00001e0100c000341607105664030134080d55952101d008151154034401451640c036240c9180280450384e440e04040104007002d03506220 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 50729428 1250 50728178 50728213
    0x6070212090312040b030a0b0d0c05040209040207150905120f0301091107020a030c030611041202010311160b0402130605060708090307031a0a05060f061204020a0803030c1b 76
    0xd03a165200e0529550358240c4042454444020b00c0305142400c0050002015210913000c1d60207041d104000388600c401c0b500420500700c22800c0090248a0700da0402c000c0f0f880c1950060040010190001d4142804c03034490004070269120800e103104d86070103440c0308000017404034079240d5015680302402d00d0030441081200e1b0205000342e0b20020b6035040122040724126003034030f19481d8010041e01800c0e480e8038141c244180284000c4603524140700d1060703400d464480594045d240944000802c002e2507800441c00351942e081c1180160307104000c40710700e0424103075490040314094560100303903080520622141c07045424000044a1406606000c140d5a000441d40380030b404c01c0296494065000000703007441c115a2004241c0a401c2441980c00c414503440e461052050000401047d500c000510480f811880403255104008100124009412040d1180c004d4005050044100e8030b03600f6013490760b41700f80ea0102c100b0300701082200c0ca007107044040200e5808035002a011010303d5030034405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 50730678 1250 50729428 50729443
    0x5090c0714030c0d050c0c0105040e130c180b0f0a08060103030c06022101090e1b060c03040f0b19110c0405040602120106030218012307021f050904060602060702 71
    0x10301500c440708000e02800e03000c1043e91804828501900d00100c4c18100203800c0340d2100c28103a004d8010082c25070044d40c0100180d0f412a01044441010303542c40006125500102ca0002c884401800030046031020308104d81c1001050701000014071409400100302c92020341c0740c445481904c4895041c0000300c0702048190440f0b600d402e14035840b50882c90314130042c1c002c6088141842003c012043d5140300b03030000e41412180f101401300481c100500c1c80070f45074440501400707080c48160109a5079070811500070114106d464013620700386030f1a081c0107001c2c41d007641c2c00705030089804907600c10006a1900d1921150540d0700f450480c10009a00741070f00c66030700007182442242d070781000030240141a0100e9040050b0300010340610340c1c5074a0042c4c029042034944080100d03c2c0c500800c0310354054146004116400003c0b183c2d03215002d05101d84c03d5201160403a004a07020f803001a41e580c8060340030748030300180d850305a03d880d00b801c20b110031100c1c0d692104045500000c1440403c54001c10304c0d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 50731928 1250 50730678 50730683
    0x70509090a0f02060d022a0102030f010608090a0602030108030403020103141b070204180c0602060a0b0112150513020309060a0506061801140f070b060d0203100e010f0603050606010201050105090c07 87
    0xc81d030702c14560000601a0241c96074003500079000040c04ca03144010640c444588183c0381c040d080b107404417000e281d8201d02045a1400c400030544d0300510103a13000ea4285507200c0c40d40c07030446140c0c914655820342660000c1e03110410b90740c40800c05104542c0c140c0140709200005145588052409048440c0030800b0f98ae0042070f084130014901e000d640325904030b6006501a1a08054142c040c1d00d030407a0342d00030b10720400c2c005006401c041401c5520350b00581a00c54016510040d50040704c00c00440100891400c0516151071a90b001880c0c4d11401c40d00290181c81c000016103900e05402d415042c8980186699030b0320b0310b0401008076a039514820740f015140c40301000c8000e856483c0041c0c41800041041120f81070020654001401c10f071002041013030303c5150b5903041c548454040c0040d4a5240304c001358503401c8414a580f4220085d4001c010240081340040b60440d0750b090f41004a459a400c03ea800e90081030800c1000d507024000c07070740104820b86a40e00180340201d0f00116a004a6000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 50733178 1250 50731928 50731943
    0x71205100c03020405100809060702010c09030201080a090606080f0c1503010b03060a0504020f13080d0f080405010612030905010219080d0209032104030308010806060108010b09030109150509070509090a 89
    0x1c41c0c030300900c241d042d10080c10000d00b006805040020000d04207540444500205201b100002081c0b14418092010316042584440300130f075095900540300118010203d0421540d1204424042610f5014100040184002824140d0f500180c003504200b000a00c050207000c515007052000c04500c000c80e81141c6c4100390f03070394482e01d0b540300040504003190b021652090000c1541c402400d50b0f94000c0000420403070540b8801075a0b03000e52510352004800100c0400c100c240c088031540d0140024642c01886240001460b0b5160f00a04c2d06c80c40103000280d0019041c101d083c403c3c0e5804105241910000c0d9100e25005039007607031050518440d08590417061794005c2481400c588003001070703801e40c0400e9003844036054010901603d507500144000e40000d0806c02c000245040c000c2529401144180e4610086030b00b404071221060740100411605596600c41e041d011403103805501e1203030120000081000e0500158243c9001c425030040343c0f04149030418030680e480000f810884042d03004a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 50734428 1250 50733178 50733191
    0x6030506031005040813090b060a030504030c0c030c03061409070302120a0b041a0609011a07021f1e0906021b030114040c0806130f020111030d020c07050307120510 72
    0x460b040811030a00c600ea403d0504050000300042e035000780482e040c000c03c41c5030200c1e0f52922540c0070b4411304104c698111104201c84050346100c2d4214503442070107810b090041c1c10f010f564411044032103a1083e180c54000311300074010801c9900900040c0f21440540c0b4682d0b05003410400d403222010b200003440f076040e08542c6204044240070041090f03030414550045440c2a0610a21180340c480e010003c0307090400c0012487d28248910505840c00d0b10510314074640840070300d09403584005416030784141142c54a28001100780b0f0703211800143d036a01c8084106c030601c454520071401d0440325061001aa02c14060107600045c8800d039a6024001000f1069408020a0040c1201c0c004400065600000c00c4240050426014100d0780c0c44001c50b0b80e1640c0d101004007800084100041c17510b210720300b4000c0550301c44d100070785205c003464098030304e403109142d01e6804036804030520b021a41c010200c1040b880c6028404078004003050f041111482c2030755a64582c54604e070258201e001c6a6520 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 50735678 1250 50734428 50734441
    0xa02190e103603110303030c0a0c0224090901080105060303070602071e032705061b07080609070305010e0c030706120f0903050304060b0a1a0702010e090703050103020a150801060305 80
    0x4040d1841900740b0020707141e600035141c0380e00702c80344500d01003642d4140300c43c00b1044440c200001241c1c4200070200740a82042c14501e02200c1c491039000701603900c0300551002210040d074600201c03909044138060107654a42034418480000d005a0000b0800e9240204002454801104403200f640d4480801a603070341303840c903117242500060380e1104440500588403800701034006544e1032815503d401c40c2e90b00c84041d50000448070065001c0c2031b4102c1c1003445042030f030140011848034402c24880035181129200c0c1c07052031501d074088aa080e140d42c044841001840130038030666129010413005841070084460129a440b11684181c0b000c010100c10201d2542c1c06540c042c01c03888c5903625089c05450010b042c0204190429a000d82d07026103080c1618a040c0760904814046944117007240502c40c44a07105202d4541000d007050f070501c0a07018180c402030b40e9004001d0300c64615030710005195411801170011404244d04102c1c145190950f000c034102d0b40100381103045402a01d000b050f50359509 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 50736928 1250 50735678 50735717
    0x10080706110f0106030507230303040504020f0702030105100f080303010506033105150606071a130b010305100e0f071203050c0102070b0105030c0103020418150308030a02190e10 78
    0x100b4008503951030918040100300c40482c0b144115030310b00960205501c02c040c600c1c402d052000001c01d0f4036a000300000c100c18100390b005000c0c02140b402c007203820103240f50003003070a4641c103e4080c0106d0b04003181c02d01c01c04850031500c201070514800114150340c10040441c2841c8030280060111004660418503510050340c08100d0b410020a56140701d4070251510507500e0301400b0509090301421b07400a80703541403041c103448140341c11010740414808009441e001d0713a04040c12441c2c000c2000013003100424403180217940210f120380010a94004000d400c0011204030544c143c60541184858515121000800d0340581d10001004030044030913150030b4034288190b82d20112254004140d40092204810000e030484900350305603096280fa4400440483c825406410780c0c0c80b440d0365030760000c512180c1c4401d85019444900c1300903540c4940f03400b03181e90411500d200c03100e0780018480a803200d010b000310142059908000d244042800c2c001145070740281d20840804c845400d01e2000310408 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 50738178 1250 50736928 50736943
    0x201050423030d030f0b0f180a1803020a06050108011404110301020717070b07090b0d020f130b07060c17060d0218090a02030609070b091302040305100c081008070611 73
    0x40849528000719503004d00940142144403280e2854072400c5041814141d0107400070001c01440145121441058400040000f8040502444c0e039660341c021004460104800001e010350001c010200c19440c001098400503085200c81c0d9051a02e18001c240e418880c1c2608290700c42e0141038000d511402190080c0241000603012088031322009044040410061545074040c0c1401d20840daa82d160503140d4409078801d101c03008504100680e0205003940c00707001001503502526151200c202405403e0f9900c039001072105c2000000d544d000c1110314419032010750401d06103802041500801105120fa0080400b8086c25907000c2c00000c41d5a00b0017818400d90000c444002e003414401495940c07440ca42508074000e02c50400803c0e0000c400103608000c851a4011341e500d4601004140850b01d581021103000c0541c09000c0400098003d1205411500301400001003c1c0d01b84580107217030340e80203409400031035040e107001d0150300004a00c400940d0b803141800c1d040d01c035070104610300e072404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 50739428 1250 50738178 50738249
    0xc0426100609021206010804020f01050a090803030717010801090309060309080702130204080c010512070f02031612080a021201060e06040f03060605030c0306090c010c020406090218100c02010504 86
    0x1030040040b90150791607015001c07040000c1243e0099969a400558047c2e5080c0d0300039502401c0c0d01c1d5003500c01d6104800800d00701e100c625124804030358880040346560401d460b2040465078500034514200700601c207087c0100440c400a0060125644021300201c1440c064081011349407084c03001480103103402c03917402e1940604480e900c0f81100203800001d40040c040d00105000300d62034500198403840a885100c1c01c088680c2d12b0796251030b4800e0300e041703a040c4290000d600091000b01184800310181c40d410314080c44070042c0551002c400101a5040100120102441441502103404d0003162090540e0750600703260743c2d07009450000502a008a42c0b041d00080590007001c002c00005070441401c40b00c0036000c42c2c0a503881c1508140e1526822500b0040c141c6c02802200042d61090707102e842c1603400900300194141e00c501459080e070744070b00c2071a00302200d0100b10031410300b04100312969001641c901500d000d611603000814901c9181714809090100a44800442560314901d513403020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 50740678 1250 50739428 50739431
    0x80a02040803220614030c070203010b0607050303012420070f0b090907030504021c030e12010b01020706090602120d06080105041b050411041203180b120c042610 71
    0x1aa03c044100e08106620f240c500036103802e640004085000d042c0454448a0080080e41956036540340e103540c0750441042642d241d901c0b1b0340c4045060712228000e06c1c456000e01c2c041c5d60703a0360400c0c01c9001400c41e803080040c054840c0c1503101094580c0091049e4203d10b00315030700e00f0650307a02c09001d490701c1184c0c0c01240c8a1000c1d00d40c00540309032654020301d06443e007503c1101a940d00d83c20160216a02240c0281d00b04540b4610304165036203c10700c0c0703168548a4180060b540c001e13034000c101800c0e0250511181c030780d594120000103607010090300e4010140d601e060340b40706081c00030085d00d60f0210b1030051445000424031003c502103640021000d4800d90008000614190408001f0418001c980c1140c01086200100359401c10b80560b1885c41d10400090b1300d014035280102c046a02070748415001c011030682c10403080c0500021420080c008507210940b070b0240300142c25060070300a88030300c140800c100010000d03c501180c00e2000441101e281348a862410340310141000044400c600825 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 50741928 1250 50740678 50740687
    0xa05131203020705070b0702100f090e18010e0c010e010f02030904020a0905090a060303080c030414010c030b03010c0206100314100615120510030204020903120403050d020c0307030f03080a02040803 87
    0x96505901520742c1031300940844200e9940d910b0194581e01c603803d006500300403440c1301e41c402c6074000d680300078404081745440d01c06c040e07840c483c9011000083d6011040c81544646550000e542405400582d1100001901c40119a1300c00030300f030301540421640c140300b0001407815025000340b0a840c040074016109541e540c0306150001c11403981e500415200720b4080c80801e80909840c4201420749030301da111a6460b48481481d003d1941004100f01c5034540b990a4106980100b030080030600030720b135100851501c0b4444100360940b21400544d03004c40d0710800401c94107440055078842244d800c0b20183c4502050400403071f0419050f02c4c1c01082c0d4a08018002490b2110100d40114058803540d544052810300c03076046050b50001c1d5210400030075442e8061001d0700d4183e0003400e20440003000c4031040c980c1d01040c0001500194001d0380d0076000700003a1a0b46640510001e04107010072005801000c0c2103686140c1b100c004240082e0030045100006a0082910303030448016001300c0c42100d44a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 50743178 1250 50741928 50741963
    0x40f02040305011b031d0604030e0d08070605010f061107050d0302010e06070c05100603120f02010b03010e01050103020901050402030103050d1101180f050d0206060d061a09010e0a05070c0b0a0513 86
    0x4c00800b400c43c000080c41c0c40c00e03010100711007071182502480460041e01458607552000c542001070b40d02000c0e80029511941000546000020b000c418842e140203d076640c50840302c400e0304141c4d81c0c0240240a8500e03425240f0000215210040d035800300d400c4001d40d51241400c81c0101104004c000661040106100182c0d41040c66a0b07010b9214904071000c44082c0000142910214031009149144101420300244e00440c040d40c1c24a80340d10000404000c1600000c0c00c0d124050703524486079540d42e0042c819410800d0181303004d8902a02c0551070b40d4556510b003942c502c000d01d020020006000070200003a4429008204e4405401c42e40684854003401c20040c44942c400c012a5144103103444000054004540580b00e88801031045440e0b40d041d4940d4006400c100c910021b0203680c00401041550f40d034800a8003a001c401541d003007500d00080304400703c44028004405000d20340d4002c1001401c02403459510540e03c18010915803a07070610150601c8009070000c002501c1c43d24078081 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 50744428 1250 50743178 50743211
    0x5040522020f13060c030807080601111608190309030f0303020d020d0203160305040b0c0d14010608010503070b07020a060c020f033403021507080d1a1002030a0905040f0204030501 79
    0x103800310003400504180d40c2d84009503140f065178000200850314480c00140402d000d500740c0c40d80003c060509600743c1034070307402c4181003041202d81d1940c550401c1740113004900c01044111204075404100d004042c1c21520094441c03021440010441040400d4034020144a0740640700000c0d00e081056469841600407100603400448500041c8117040d006403034540c0c424000e003401580c02c000074007803a8a80c07800c100d9031039002c2520080c3d06034596990800224000c1c3c112402080d080e51140038650400d020942042510381c09a00f00c1c0c00107004500160340c4003004201220354a0612424003645071000c0380e0307419440c040c0140e050043c0000c0c1050f0b0440c0b002d4030781002d20541c83c46c9524a040b2840d07100c8190003400701a411410071a0600034248000004049c0a80203603015030800f146001c4140640300c144034003c0340307482048400c3c0087d0802d82101c0e840c403151800910b0404165003002017401b40180301d040e1080d604c54000cad12019025030b0480b40510b0f0440024864041034640101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 50745678 1250 50744428 50744437
    0x15080109050a1802040e0c090a0b0109170c0607021201050a05010f080f0a060506120f0a150b010806011d04021b060906040308070809160602010f0b010503010605040522020f 76
    0x2058182454001010704440703110703801c00006031000f20354442486409210041404002ca240d4511440307403022420340d43c1e46d00d420702c25090000b0100d04684411300042c0005695031107282d848125283e40b145041022031030340c01c00141590135580b503880341d00001e6502e10140c08184240c0d4600b0f8240460807100c0e030400b60690380e101d5144040e590741d0b04440d944c0e0341c2075405842025040340d609030000500c65040b035a0081c80c002c1c403030240c020310119428288480b160041005600486548081010384c2e1000b0000b03a10200040112510139000a444050002c02c12410444550007409441124607091000380300b0141085460b9030416100f007071603d50401c4162550301c40c1000090112800040b45846954140d450851949843d101038038000f4000d0056002405405d00c50950511107001c1c03040107042c95400070034402c844d11320340790480300c0b6540c89904000c010401070040c0c80d001000c45045400070b0340e5030003d038044c807200400b03260316006208505134000540e420729a05620040c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 50746928 1250 50745678 50745689
    0x6020c010b0f0307060c0c0e0106050304031202091c0f0804080703030e06070203032710031415061603020309060a030b01080703020310030209040807050a05070801060506090603040b0c04150801 85
    0xc0000010780350400000d60025540b156041d4403002e41030005500c86c0800e10b503254480c10107940c10750740302c3d500d0301f403805800d0b084640095804010003083c1039003e2240a420440490f0451408000c0008140c60350f5601c06209600c141250710340080020144440740455000300740207444640384c4103459141c00b41e07480143e0004007040f9005905140003021034508a900a0040d450024103c524041c450101c10182411200ca4841c83c0700944030380400700f40c600d566070b400040501c280102d4050241300a480c2d50101e6040d103801c04155200d2004079407105194066a55001c1c65600d4106c0c038521070601080c0d001000843c068448980540099800402c04d0b2220201a961164210200d0108540403201c030004d002040001d81401300440750401d01690042c0e2030401e068035030629100d1095000c850755404540200142030083c41944041c1074111001c51410f04900b0009100c1d01020344007030090900070f00070030100402ca0048030001e2100e11100b018800c02d150015000e040c00340320300c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 50748178 1250 50746928 50746931
    0x70f020d02010501180b031c0509010305010b0c0703060f02041208091f0503010303031d031602030c040c020606040b030f0f030d14070203070b1b070609150209060403060902130906020c01 82
    0x100640034010f001c0e00341603e200d1000c51490441c403544031400b0340070a064294143c0282c8040061003090360018041c000c0403070b242d055443c2c0806c0700050444c2d0b4143d0086184003010301c1410190140804d04904490700a5004988445070068110007031003039500484000e9041420381c1d08000541018040c40103003201d1904e1210f0740c0b1126440043c06007031000000410400040c80000e0017035001070802e41d285082c00000702c044481491451340302c2ca50482c184101c403400780046141c01c101094a908050f40c0a00c140c0e071050001035a1108042c0c0b100d03100e42c0d101e030401c11194030200454000c2e52003c00481d5410048021490303103a6114122401050341044454040d80d051001c0361806081c440d4000c62402c3d00c80d4481d8040301601526072080400c0c0350132282101403001d005000010b0141d600010041500d2504001d00c401100c400400c0600600c00c41c0407a54480301a0b9003240e8008001065580c0c4074030014181340080541c520500d40341c207558009000311039002c0d00e0441a103900 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 50749428 1250 50748178 50748193
    0x819020f0c03010501121209150c0c0b090102070b030a0b03070e150301050105010915140309010e250b030403020102090d060501030219050a0612180803070909050405030304080304080c0105070f02 86
    0xb850300b44e800034081c117035060340151540d000003001c002c3c030321443d41100d01d005421103481d6442d4940e05008011701c403000580c101c124000f0b10003c41b140300000d04412303554502e804900800070b0b480d1005071052002000c4040002000044a60003080030f100d0014240e61943da01c0c1d400c0036104510654000c040c07242d030a0800c0f0180d00301446414180e400503103994801505e0030500a590b003804480300c40412062008015111820304060342c0200000c1d800890b102c640940150b24080c07a180c40340d80700c01184540c48188100c040c52190a80318954074183c0e0700d5540341410381c0a03126507141581c100307108510348070a010280d03211034180c81c0308075040f00941d540e50482545908050141c141d114003038030f17410000b0700c0c010000e14442e41032610703012503c0004810f0b08442900c20301d6047c0c90b80c90000080207607850b48454910054410890704200606281d00c0d116581d01004100030407412000000c43e0078041c9950582d113511030850f009001a02e00520024480780d6140003200161082c2e00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 50750678 1250 50749428 50749453
    0x20705030d26060906090406180c170102030f0a0e16140901050f030c040b040b0604031a0609070207060c060603020603100906080f03090d03050702090901020a020c040b09040f0819020f 81
    0x55030b180181c0006180341c8040e2540d01c108200103034042e00c11103245035540381d070b04074242105045425040c02103900f207001d40c7c941052208400308400020903140d10400400c40070501c068115500400490400100742c5000403050303280402480a090541e40942c07000100e011000800c42101c00041d14282c01c1da0b6656001c2c80311a02445481d298103405c1244041c80d141043e81c490b00d158200204003286400e00d030703008545031b40e00640040e0b030400703c2202100364200803e010b50340c000c50f094411130b07114603202000940702c54442c082c00e4100b04600c206e582c02c0c8035040c2c00c030b40e01441e0001e21a659905004890071413002c1ca5100b0144590b003801c0740064120350103d00000e034034070400d01030b5181c0384044d02008005103110320110300340002402800c006d82c481c1012988500255400160740749080c10300031303141c009030042d00351289007000e000c104180ca400e0400f5403c954072004ea242c0c0b502c898940070609004124550280d158182c5000301c4440d40000c0b41014a14802e05540c000d0a801c0b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 50751928 1250 50750678 50750747
    0x150408071d0403020a031107090f051f05010203040303140d1a0a05040614040f020408010513050f24060f0316050913080403030807050706020d0e06070f0f050a020705030d 75
    0x2c075005005604280c0502c0b000ca401004860640c040300c078266240d05456035070510440b81d41a40040c4d1480c1e0300c10410034800840041c066002c50307800c0c3e81250301441d1500003944c91040d07000007010007010204004107180000305640250700304640501010400001d00406080704c0d66045204081c1d64500203054189485001d055500b031194034245400400e091002030503400c150542e5059003040006502002171044a010b600070400107100c0c2039407410320f1480e080503244101c800b9080f10b0391403203034041c100c00340340d1540075203200c00c40250f5100320002fa4000b0701e04950941500a884c4804a0364282d6469007060314800c40c0d080701c1c1034940340b141c40100300c40001c00a020120820090021902511030b582c0d010f94035250140c5403480690710740f816030b001a8150810561109000050300d031060020301d902a045140c4203203403203048000213040454403106c01e414000c000451400c00c0e4800d011a20140c00060300b240d0a2611400e0010000109214807030030420012603000c03048403a0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 50753178 1250 50751928 50751931
    0x30f100503250f06200607022a1003050106030c0203070f02010c0507090204030c030c0501021f0506030f0f030c01050105060a0806010e06160b0a0509070501140702150408071d 77
    0x10340104008101004030a08a8402d2100071906404080001860b8801d441d03105014102e907603650100740e2000c100c84103901d05c44a000303c286412110400c00d24070b50015000300200d20661040c1500d21106030aa4240c0d11000407281c2c000c001118820903240d09a00421304890040c2d4080001103c2000100c0e100e0007407090040110307100c0304000d00598800c001c1d0665803405107081e200a035a41d00d1003036049a005a00c11904445044810014041c070304403000010a001e00241038400c00c00002c1c1708600100220100d000d50b03070780c00850610748040051030883c010710f800f01c405071103181c885180e9030b4010558400030b0358205800401e5504121003075a000c2001600d90030855119000191a0701c99248103854004030b00f407054040e890300050510f5015402100c6019050510032030385001d54030010501c40c45031740400010031950342d1002d1007000e400000c0b20901d031160b0051002442e440d114008102c000a0041804201711030081014411280101c1c1e400e61000d81100e60f45151850 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 50754428 1250 50753178 50753189
    0xe0609070506270901030f0302010b0906090a0c141204060b1503010b0c010207020d030c051501050d140c06041d09011415010207091b0306050405100302011202040911030f10 76
    0x101444003081e0101c40c1c441c250f904540c0b0820b4011600e0080000c151042e209900603034440780c0b40c2078a4000e054081c421004980c070151a403510629201c00810480080504000132132580c5618804a25103c0c01000d50501d0900c400c09503240303100d1214a85035017003500c09a412600e050b410300154903084c803007400b1034440340c02014116842e100c1140102d800107055500955000c011041c010b03a01c1302d200c0071006103e501c45015076401420550b00e44609402d1031100c500103d001407025a40707a0382ca0b060300b60ba008015070180708218107182c1c02d02c0a9030105942000c1c0118010410449188460000c4801e800d40c001c595a55801000e090f503080701a01c2d902c0050000100d07075652070440b5000040c0788180112400642d0b1008050100d990102c01c1620a800030310803100b02039450300500c030013000c0450382407007035080000707050cc0301a2080c40001d05009542c56503000ea030116805580c010940e40408202401c50b000b0300050341c1c0d10455411510941c1139000543d05c4a815100b14103403038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 50755678 1250 50754428 50754439
    0x61104030308070503091606080f13050c330a0809030702060d090222020406020106140a0504181403070210030903020705060307030e0f1c050406080609040c09050a0e06090705 77
    0x1124200c084d24142e001030114101400b84034040f060000d102122100200b242e540c03044868900302c402001081d00c040e100030507044843d0b1201c030101d500051890380d240000c5034543e01c1e040d03250010181980c0d408144d412a41d8003102182c08190940021b002d02d145145c40d0314604c1c1e40e8449413a074030b074882c80f1402940a01c2c14406103007000440e0f442004d110748041c0220303e0b290080d13808204010405e030141e409068000409018079682800743c0002844096200555240e4030710000c5c5610030640034190169070741d400c40c18880d0702c4d540000c400c01c90704402c584070440780780b072034660326507000f48800d03400750500940b409480c51003482003101d0030360554007400700e0701e061030100040e40d440a0318500405403101c0190442c2c105c14000042c084100302e0083c00070072100f501c103003006401da498010a214007484104803080d045444a9846074085454140c0c80d50350349482011a0469004001c460b480e0000b0441c1c0113140e54882c48013203255a084408540e00c0d040125a82c403e907004468111 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 50756928 1250 50755678 50755681
    0x10606270e0406020904020c0615010207080a08090f12010903030c0e06030a0b0f060d060e0115080a050903040b16020a090218090411120601060306060206100302010e01110105010f03061104030308 86
    0xc01d45121550400c0c41554050326001e100e00008059030000541044581c00c101c05108940078641200c00c84d1b50003e0024004080c0f0300740c01d4540300c60329160050118400000c0c00c00560342c61580c5903955000083c003032860540920200742c020124036004901180c40c20f001208401e003d400c2011420038000d18581c0340d43d032031003000300203004140200303600403009e00708035001daa4500018042c0220302c03d07000604c091415200059062040e40700000c44103e07100e0b42c401c45540201c007294440c03000500414940c50f020300140c91803080d45d0010740c00c8080409c0d08441d003910480c0c82d14059008468104105841d41106001c034419000340782d020f44114508040c003820b00c000406d5100b8003420f500242060b444010480089003290001350070f4100d440103015135034040c401c1030302801c0244010f0605145c2008024101c60840c04064184440342070341d0380440e071040340c00e100c01e91503040081c00156500d000745486403c0d80e0100b22102c42c01c00b5405650701e44410140d50440c0c2d0140e8810956 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 50758178 1250 50756928 50756939
    0xc040b1309020d0c0803130e060102030304030804140303010e0a150b0405040f060e010b0307020d020c15070f06110a0210020f0702010e030f0303130b0106020604030c060e03091201060627 82
    0x201034019007260024003180041c00442c08841011300200181ca0145503140c2035620030710340380c0b6100e810400c40d0100460600c040c2d82d0b400003c0e254001e5050603d044a40c0b69410005508800221050001d200000000c035440d618004d910b4007507155030005208250030200807a02040640c00f6a640b456000d01041010345025049010380c4c0781c0c0e050001409980710543c13044000001d0300015170301c560000c10302600e160704011104190360540f025203000c503a0000003e881c00819030b4044807190002c510b45060000c0e010340c003880c4642c000010001142e02115410541d04002002d0015010342c0311200c0d000d25403030084030008200c0045852501c04558019507019000048040d09442404503030301c80c20200f0001140144c6040700314903400c1546241420700100142c020301c045401160038000000d410a41810f5510b500034400700740700010001107451400f074090301c20382c0303c010382c0d040240030101980500d040c0d9810740d44210204001d00d4948480660500000c110254100c108111 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 50759428 1250 50758178 50758181
    0x6020909010e19110f070602070b130819050c0d0e0910080601050d050c09010b0304110a0501050306130b100e03010606141b0709050103081306020f0a02061e030106020f0c040b13 78
    0x144900b131004034100075403211104404d8100c004100d86c8241d00148010038019802c82c032651110211086e07504040b003e50320a1498000e0000d020800940341070464003490041068600c0380542004a82680d503031072070010002c00910400d01e018441d4100407580f40c00e80c1d0001c22094444003c01048103074a04001c1c00929401008141c403140625201c0c00b8040d52000503042c000c00d0501200ca0f00c5c2d0902e400c1200d840224a90058440c0010070350400c11a600314056a40c8410103c62030b01c00a07a180e030f94040681000d03000c0d2a40310840b984943c00e10341e08440b419040b4034080d0003c0144544410302510050040c0790000301d204402c1c40710f4015101c400380480035003440502510000c40c1d8414503a02520030a8200b01c800350070100d0a00c0b086d40541081c0c40c01860603100406d07900c002c440e003943c0c5440306a040a40551000140d480c00b40d4560808080000e003881480d5540e503949003002520390f0800180301c00c40d402642a18451403030329004490741d00000501c1c041c0c248401400aa0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 50760678 1250 50759428 50759441
    0xc02060c041403030403020a2402011e0c0c0204020d06030302011d0a020907050403050303012711041202030c0a0602060f091f05190f06140901120b0612010906020909010e19 76
    0x40d80b504c8100004001030706c07240e07400b800402e00c030340e48a2180490660810b8161400d50903210442e0b00d0b11165003035441c0080c0b0041b20f0702c40760341c4000401d0b070308550084460481d0b02d50040c5d0032070f000140c03004c109506036000303001b16402940204403401d41c6441ca0040100c3d000f55841d026400031540e0f00151800c104201c1d0000140d0400e245000ea80f60b5501d070039038100764000602c151081c143c1c0301154441c1c0c219003240030041e22007001440140d00c1030340060b0055004a0346400c00105103002151400c2142144850005240f004031943e1040c00a554202c1114130115105260340824004d1800042000600d08403191740640701007410244001850001e050003954446642c000c0c544c20348600c03a9004007220340070b021400d0b60034482c519018039000c3c0d480300e020342c250000412500c00409554100f442d0705c5850940c00f512540d00084050b1000a04014694600240303c400c10407207a005020b50b58054a0440c400c1c0e9940300018140c0d80c0444111198aa00401e1002c081c0500e43c001e4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 50761928 1250 50760678 50760719
    0x210c03180a050a05010618090510050903040305060a02090a0806090a0308130f0b0402042301030807020a0302030601061d0a1412010615020703110901050102030703080604020702040207150c02060c04 87
    0x150700540a03030325810f142950012003501c19955413901444140d200901440302c400404505010f1702c01130790f0350300b55200101054040c043e613031840405c0b210030b000e104803002075401000301c4a41d41400c6403000029030040320800d00c505401b0000140901000c5082481900100007602201d41140c41c195000c8800503c3c400721b00c280c1404c020001514030402c010154091f4100c0c4480d46058810f100880c2d281e01101c103030442c100917007945055100304100d81966840351410f0f0310f60005101081402116800096141c010a0000300b01c060f441640b10602e004070003111214555010f0030b0005e41c4000703002d00c0041040344c0120542d00c0c140702c40c070081c000c8158000040c1d042c1d69012003452482070441c1000060704590420000d0129078030a01044d0803007124000141d500d4075001075074078804c0c58002414081220001910b03070b61343c3c0d03040e2240280c01900942d50307810359243c04809a144484800051880d14116480c424800116180305000c0d42109a18190900d42262200403c01480 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 50763178 1250 50761928 50761933
    0x6050a06051203030a0c0504120809121f0b04060302060909040c091805070e0106080f090705030706031407090e06040b040209040e1507020a12032f210c0318 69
    0x24090b19541584500d00038580c01440c0c03a41400040d990640d081c200c2841c0820000b800184015030942c409100c3c415484928281da640c0604046403101c8007464501800d40564682d48500e20301c2c1901140b503480141200704901d245030030410044686900010f1340100b414400032030340781040105260001d0140d110101d03204c2d6102c207607009680701410941d903401c011007511030803c5001c01400c0c024002c41001c4035103940c1001002050940000e100110302010700010480020f01440500082c2402409640c0180d40701e01c8060090304440d0148800c0ea58000001204c0d07520500000c03042d50061081d91019031200801c01c400b030000b41041c030368041d60030000c4014580e9280705082c0e520b0a104090420150840d160036510b540003424902550071480302c64001030440c0c03400e00c440c07000600300000c0090500d02800940d100501030000100000581d03829680141009030071016010180f203000130071850146c0142450660b1100c05001003480841c83e0400895006514166a03404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 50764428 1250 50763178 50763191
    0xf05090d06090b0c040f0b03010e0412110601060504061d030705040b040b03010f05010e07050717030703061503060305060a021e03042a030308060609010507030e030c030a06151a040306050a 83
    0x1d815241540540301600644e10000d403c000c01034101200100412054440030b045602d404442840c0000c002c000a181c01034015214014500542e03d01e4001c80b020b1080352511768446901501c140d00500400f8013013042858807c1d40d844d81003004052586c030140c040d000581ca064280300160803c00442503003e41c039210a00f44079142449100d02c2d05480d07800119195142c100440c1440340081c15450030050100711007004100005010800d03010300c412299075a0303461071021401004640c1100b82d0342c4107c2201181c80a5140d00540d041d030703003d103056605c50748a00500108a2041d460260b40500c05035000c2800e056007500610b602900032004005007000c18404107504030040e1a035003450080c95001442850327400400d2540c080000e80c1c2e1285005203020020700715003c0c02400030b00308035600380085580e4405119000742c3c00c5014040300c500078290301d00800a0a81450f45a0070f0309071171200003c8030080621080071401d145118546014115150b410113048020a001c041a840e0007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 50765678 1250 50764428 50764433
    0x405031f1b030207210203071e0c03030c021008220606090e0f0106080106030c05060901110d030c030b18010e0c090303040605030a0c080105030316050f0a0b04120f05090d0609 77
    0xd01040da5551036034006a0351401403a0001e80c0c14524554818542141c3d4017030100b07503030000103c400311500309000030030403840d040301d283d012000140000d084100b0200000105a0400b0b6503c0c0105d100700d40c040303005022504103d41601c4201d500c116018160111041e07800c0c00c02c110164114010100418129141c02218050318060414182c05030b1050031000c1480c0d2082c0301e8280034006002c028801c9030325549450011745a2070054a108a40c000340158852303005100c4000380d6050f00064441007800203501a000340107208401000c2400c1c0300810006142242c0049060100002000307005c0e42002001e102c0748000a2600b451007008001008441d603003040500300400b42944c0301d0755a86440c181c40c000b5110140c1c0d0306403e000d81e04006101c3c0780d90102c10b4441034a191110815886a28104540303058001182550603010b42055070041c86040b401c030a20035402026002d8018000a00c21190207808003501c00008009012800c602e24001c0c511000b1140520004240c00c1c1c2180c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 50766928 1250 50765678 50765711
    0x80106110304030c120309090b010509060901121109030705010206010e0406020a141603121803030510090e031e0c1506360903040803030604020f070b0f060906060405031f 75
    0x170741003012405291032440c0100b640c841558070141580100174002c400d04040060290b0080d000b03024410000440e003100700f0307407245039104403024030381206000f00d4950f042c00f1101c0d07500c085043c902034010b46001042230b50001440604a072400346400d0010b950702d4071028002c1d000702500004001040319401d0f102c4044401805a2088140400010a00074a0090001c0001040b42d07084c071030a000c0d003100d0000c140c02920901e160141400310302a500d040300d403003c00c6025000207103c02e217440b0320300100401c000041d1500118420b50307031a000820045003591030103030150b2010940d21040b03207552001d140940d21900220050b0400c3e50440a9655070350911190089000d40c20b81c001c61043da004030b44900c440c0c1c000d16541c2c065454181423001da140c480c80010080c0303004640000308031540140b0a004c880000d90404d407100d17000e041c10a1240600e80e03040d18106c0c800d120709000300d1410f00d050300c112011500010000c207002d2001244181c40308592100405215541e42e01180110310304 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 50768178 1250 50766928 50766953
    0x90503030f10050d030e0907020102090d061508010204030f14030717030a050606030c07031b0203010c05040608060f060d09051606020705030709050705040b1806120604180308010611030403 83
    0x1071407128042072914800301d020209060340024421514130080c040401c0e04a400e80c14496130955101c401541c800000f680680f14040c034040d001030b0459103e03001d00c2042d51021075401f4000024a031000e988064543c281c0c02070b404068070700c030f90f1091080000748d40b06c40220750f00030b044010760741000155107580440e00c60a070b03082e56500307000004000038201c45104503680300c503003116550305609010800d409140034417a001820b01c4030900c2082044080c0005419038240d0040003032290f001c00c11402016a046845401d01143c0c1d184081101803800c8500d88440b0300c0e000d450b8074248100300b441c90f0b0141944090640f124000c40c802140f0001d40000002d02810158008042c414600010f062030f00d119940b045038040d1038071050181d0264041c0459044400c02c440c41622600544c9015074419400d400c91640050700045100b5509042e100f05c5100303901c00c490411224200c207800c40d62100c00b03ca8014002141900180400b500983e1161107190844084a0400741c40790340b0515050b11 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 50769428 1250 50768178 50768191
    0x12120a180b040620120910090e0109060312020105090c101704141005060d06050702030c01020a030f0c020307020114030a0b06040e06030f07081f0f0c030905160311060c0109050303 79
    0x34104844c600d00c40140e035500b16100c002001044000002e1022110740d0003000c0484e4802c1d8640c1c0303007451420344a900340e00702410144511541715603603030300050000e08051000b15845400000340c60180c0f030042c0704151085401b01c01410030620f2140400071410501d103021000d100410b0009200c261061b1010740c4201d1183c0000c1d0300884040c081289000c442101c24141e05007083c0406c1039a8568aa055000c030754007280c04529912030b01c00a0381940642c4401205561010035544006549504411860500d4040c100014600041c5c02c90f12442242d40290200d0345144800c00e41c1c860300401181c2c090408000005c0f0b4107007480000c0c2940d40181c0c094035450200c0d805001c1945000e000c00162400000000c00c400c510300001c09840350640c0e603840404016409101018031045d400084074182004420001401030a030044c00401c4480c0003a2110301c280300210390415a07424000003502d4106142d00203a020b484100640c07540b00b1400d8070125500c580b05400055410400b0b14021407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 50770678 1250 50769428 50769437
    0x30501170616170406200708040306090501180803010302090601050c0a03080603010e0102041701110310090c020a0b01030b041403030106090b1e0403032303130b0619080a0212120a180b0406 83
    0x6d0040d00d40110b540b1903106201c01044200034400008003044110380899078803881c00b0940036a14100380f401001c0c0c030b140b030301c03000c44e50041e4240030020500001d41c143c0c2d100315035a01454541d14011100d5006110b41441c8a40c4a1141400460302898402d540940010004600e01c40e0005c2c1c7d2509a030415441a1000d506060113030410480a00403003005d140c680820504510f00001140c030792810b54800c04500c04c0e591140d05070803038801c1c000421500d403c0030b44034500396540d14052100c840c0c00c41e0f05907000300c0888880c1400c071001000700d03030484951359254219182014121011640700d20f002c80d5550580803090004081d0b00800740c401940691184a00c080031300d84071040e00b1441250702d0079081b00800401c002101e1000d120120f40c5e421010614659980c5400700e0812204203540c00403d10049400003100c020000d0040f034464800d44014a040c00e8184506560f186a801e210012410602441d100c071482071341c2c42d1030100260400d940c0c0040c0d0390300107a003403a40141c20100004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 50771928 1250 50770678 50770691
    0xf030709060603061e1710110c0c10050a030b0102030904060801140a0e0a20040e010204080c0319260a0801150819020904020405090c070201030501170616170406 71
    0x690f09031141900078013840d10011031444281d1413402e01c00c85980219170080104120300e8002040401042d145040380301c500700080700c84179842c1c0e04c8641040d00441c500344a900782c803002e603041054503441080c1042d110a8180030606006401a282c0c0a103024110b2200307204030f0300c2e55542c600500c2d00601355a00001299100070b65a0a1004002011058454202800d584010400143c01e01400c0d821892941c60800344009087d0141d80810009612174101110382d042910190300510440d060306c022208100802c800745a110b1030300c4030002490308c0c0390f03100d000d000c601100e4155a80130031814090f00410000b00f0700140c1a0014090540011001001032003044903482c102c0021401504004070685402e0000c1d0b03080ca408800d00d40042500840c480310a9161501030307c000c0c28004060716a6860700c0c44598080c2d030002d600c280d0000303082400009442d08489880d40c144c0015801a02c0e56540c1c40361070300d024511400103038040105407a118410100b1075603500d8080c9110b40c20200c0c05 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 50773178 1250 50771928 50771939
    0x5040b01081c050406140d02180301050a0605060301030206030c0708030a23040b0a09061805031305040209010503010603020a021c0e0406090605010207060c05071d0907090c080402040b0f03070906 86
    0x521460b80300b070060285805050315030540d000000c0d07400300c501c24079004024000b86081d00304580605210342000c04d0010510603c0c850f55000c5099a801007070b0000c02c1269280c45c01901503486074890640c0010042005101504016000350303408002c6006c070b40e1130b0900c182d494036040c5d84116140482c4d296a1003d441721283e41300b01034005105005541042da08080e10f8058010401405464065540b004202c0400220f40c0100742c48205010520050f51001d00b48541c8950007200c2c0700301400043c14020a2602d001d1094852010041c0e44590a581c01c0080640007540b00184400030b502c2490203030810445000c240004007015548c030300001458200500042e62a903400c81d100c580d04000c0140b02c144d0380056003001b00c1d5414500098483d840341000360230555190403c00b1540c070350b9011802c1006075000c0c0c0c94001e5601c00304a48a0395a02c500010440b65402401800038404002003001352074a0b400100540c10000d1526201c60a0140001d01c5c4c00078580c000f000840d1900010081e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 50774428 1250 50773178 50773183
    0x12010204120c03140610090513020619030b0607050a020d0807020604060306051002070602191b060504081b09280c030c02070e160f02070906060915170f06060c0105040b0108 76
    0x540e04c440c2e009091038142035201042e94609400381c225116034920000343c030b00c900300d541c000c2c0454000d010150303603c000e411441d121140700003000f00442d060414640a070f051900850346910b801c180a072005003400e500304420309440c0d440a54040005118402c0980e48400c0108000c2089440008060b450101031024140c47c026400040d50041c0c503003084440c0d00802c80070105068038112020440041c50100b404480d06002c1d190010b07030140000c1440760701700b401001550707030350703012545840c44002000261611807826140c11005a9012440a801d210301e000d1000388201c000d2800c0c0b1045c12401d10880300308602010000761100c441e00d9034660140413140280c40031495141062070800790b0b02980207034003041d000401004644e2002d2700703071090088001600c0310003c00d009042d038807000204551618000c1ca19034803003052201d41c1060091488070081020140401c60558854168401c10500140050b4020208200814180c04280f0425214a104800301009941001942c51 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 50775678 1250 50774428 50774453
    0x2190305011202131d060a0504031407110402070305090d050a020109080309150d14090601030c060906021c02010204080114090d0903021305060301062417010b04030212010204120c03 80
    0x150b01e41c00d80c0b0a90000d603d4180d0944041c00c001c003008076400b608443d0058188205001400c402c0c0907180601c03020034900e402060045000341e50303030050141d200c8540b002c1ea2140c2c0c00000d03c44440d081e89d40006040c2030f005040d1441c002c1c2417480c1040102c1000c50001202904111055000316092404560b0841d030018081d11641c8001c606004120022440300444c824016080c82008580e810071040305400c002c07a21800c0b200303d100c66090405581e42d96440a01080f2821203a0f0300b80032851500c14101302c4100c842c1c560003801c1c968800004140381c50780403421182195000c1101142a842c24000c420058018036192400c034070b001c407030190914401c2c89410007003000c988420030142e9103544041503260040702001689446040000b0b004224a900a92580000c440500420805400b048580f4809030b11241d0124101240001e86a4424019144248400d100c20710160500f14180306000003254001440c1c907444181055000c00391003400c46030381440c04014000c0042141010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 50776928 1250 50775678 50775689
    0x31709030406120203131208040b09030909040f0f2f1002060609091c0f021e0709020f13270612060e010902040c090518011208030907090219030501 65
    0x11401e107410108000c01c0d2800d8070004500c101c1d0080003152000d2036800001d00060303032141040e119040d2058001e8982c0d0b07000c95082d2446141071001414982c0c012080782c0c40480010a084016555070791180041071840b9000e44d50b40300305601840029240669402241e000c900b4a41c1f55000c0e044080c404000309281d800703000302031000c2d05107101a000210550400c030304603040d200c181d4651000c00e1501041100f003218112050300c40d40c004d180c1103094482076400383d41c2580c007080385030410091030450a5100361030f00e5110b940108040d20440d4007400c510304902d09064507042d814903840d6402c21850b04903089005940301e2405805101e14141e10301180f80318002c1c05001e29010300c1c000169007807400680502d86030207010400d072038294004228154000d20400608140d504004c4c092140360141e640640281030f50b030410024840c070316504840a001402020400360350b41c0702c0e42d54001426841080c4100d207400301d0040c6d211f00242061840781c1807065140c40d5190002400e84d032041e40030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 50778178 1250 50776928 50776933
    0x80c1204061d0f060609041a011511010b010206010b03070c050a050606010f081003080703090b0a110105060312070206090a15050c19030e0d1106070b06090603060c0403110607020a03031709 83
    0x3076615500d40407a110b0f0b40017008a414060740e03a21810b0510002210000d40b41a5100d81800030600f03140144e2200d40b400c00c145e03180d0700c050444200f05801c0310303100d02940380075900280c01000b400c40c81c7c038000d41d84540280380c4410005600da40d0140b41402514045842d5003061003008400d507400310b02410081d0f05454014054117100c0250807641240b400060501000040c0d000d09260007002444014030301c49000658401040d88010240c2d48a480e00a019508110105e541840e0008031100d03106401c10215183c001d6a40c03c0040c7d0b40e0081c0c0c4899000000310800080300840189000444007954170f6483c0e90b003015414190410684c03030648100950140744000129900880d00101007005888bd82245e5035281441004184180c142590280001640030104298860420302804065410b4001034994008244c1c44043c100d40049012900703000400100e60201c092896128028000c680b9000640d00414100c110a400503070200326192000052008107014483d4044c0040d0301 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 50779428 1250 50778178 50778193
    0x9030f0705150310060507170a0305180102130e04020a0905011212080408030105010c030e1507020103060b36130b3102090609040f050403080a020c030406080c1204061d 74
    0x4d4a021240e40b0340215804c200340403a5200403c5000c039105489050202512030b21402042d4000b806054102e40d090f4280c1012625214040c0301402510480c48000303002800e400d0400d1004803508400030410ba030b02c83c0072800b001804641c01d2103414064250000c1e02d400d44034141c04d1800349020954410020030403001e0402021900017425641907880918246103000b1150504445000c2520403a1f0380c0a0001040300c8401d4040400510701b581c0b007030300d06000f072954840c52007000c0d0264004506c045440c0d4403651410320140004841e00ea8401143c039034010b0401c0e400704a40692240322601e131155101c000001500d061031210300a0342041500d9011040150302c179115041b03582034880c16143c0c01140d11100d079035406054070700182000d0000c0041310414031404010308400c1e1402d03404180c9080120300d0411450003282d500100800055107080d00c1c041d011240c40724004e2405070841d00c14460060f501003a0441c6074000c40c0071341c10100e40344043c0041c200e140040386608002c954007800c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 50780678 1250 50779428 50779441
    0x70c0806010f0302010e010203070c240311030a0b01090305120306040506060702010e04050915040507060806031b0907030204090e010b013005040f050a1505010b0a080f04020609030f07051503 84
    0x2801d2400741c80d0f080c41c6c1121000000c0d40180d01c3d5015101008101c0c03c03c3c41c034080340350205039495112900c410301c1020f99a0107145030550032251000d2140d220140e003080090010926500004001ba1040c5090600d0076500d07150281840103da00041802c4030001c180201485c20f406401c0d0045421a2002c0c0741003041e90000c2c12400203040445d00594442c40001d81241d8240010400222040b08000007460507180450f00d4408901408000c80c0041c00407a086003000624099005000640e03002850140740402044003c024122410140c0800005c20451414082c48100075090300c004588950791400141400802011129803000600341801500c044542e413030030f03050241600040c0d1070700c9904040482d9810503070085c0080c03003542c1c0c0010411040030401848020300c05130820285e41ca85003058240d210303d4007400005842a008102400303e9260a26000784c40180528503019030100460b060103030500c401001508048020003035802c1001d150040540f560032010300d5407424a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 50781928 1250 50780678 50780699
    0x3060e0402010c170c03030610090b0409050a15060302070209060102122502210d1701030803070201060503100902040b06041d09030d0603110f0102160909150501060203070c080601 79
    0x14006810424103080f2442400710140380d0404a030310111015a0b903440c80040e0039520351045c1c072600c2c040c40148051401175441420500243e601240c0200c0ca441e2400503204013034880540301e0310603507903580720101e0000b000454480080400c2c1d240076840d050140100000640300410a0f4155001500381c3c40107031054108550f80c00001002910009600d0011a081806540c000a42180800d41d501b04170040d409020010382007507004440300000340a800301c480c003000103412030007000100018000102040080c55102070544000a5500c1e6a40c00181c030b0500c0100c101001c81c4c0d51010764070705508090180c1c48205400707441c61860286401d00c5842c0e41e17010b00d00e00300400d075107a5012414030300013401200e040e80b03024401071088544a0803c0204214017401d51445445659440c901950001c100303800c15600f07072040d03940c1e40c038503000402015015400c4104d8645143e90011b0505924a2049501800c0f02c2ea006589503c450300c2d0800440e60140c0100c0390643c4184010020445503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 50783178 1250 50781928 50781931
    0x70e16030c0e0607060905010903090f15050a08070309050a0b090106060c020a0b09010918050a0b030d0e010810030c3f0602130503010513030e01050403020f210303010806040303060603060e 83
    0x40e20100c0d0385a00714101700d0010120f800f8020125400d00a8035002c0c50380c400e500600784c40440c0154100c042c3e40c0d00424031070544038184000414410f00400020340d00458402c1e6002d60306040110b40803400ea0f4481c0d050141c0008100c039100d4180c070038401e0b500c80c2480750038058105420600800c29803a000102001c5080c031986000e003400181000c0943d10500d6201e00030039821200131240109001e44c1c80c05040c044994010baa454500f0f800e489140005480e640d101c80750f1109500703041200011540c00000400e00103050b40300c0003000000034600081302008040c0c910f0118829403000d440800d0075004046074021440e4400400c41d410344000340c190182d280d0140d0016034614500392401c14401181d80200c2c2d05528007010031420700401c180d03a14a980c820703515002c0c0c6c08401c6005407054081d40c0406034001003405425142400c10160107840f2b20615000c0c42a42d11384c00004c00e240d030b40240c20190b1250005400c1c130040540500a10300135082d01c1c01c0c103110300c3d4201005c4101100d070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 50784428 1250 50783178 50783207
    0xa0e010e151303020111030406060603050c09011e0504080307030509040b09040c090203070c0f080c01050c0301080c0f030102070602160302100c0f08061203180f0d0b04140f070e16030c 81
    0x20b41c100e1080405000b540a140d480000d0300046480c0d04d401d040a10003032074588038000c040383c00c1030300017003081c4048801c8981582058681c40c08880c2400c1c09180d244504a0300c00c001d100d810440412004000c0010f082d4551207542c805a881c0200c03c1803000707541850841e24000c5030480c00f8440010020078207802600e898420040c0c480d590058120703041850104082d0024440c0300c034003010301580b43c0052130005201d0000b0310881d19129460b01440c4024403401e4103035005000313003074100d240c0250a4554884000c00141c24116587c45400072a404003028507942001d800e90071040513014040aa00807120070b408000010340740c1c1018010543d42c1c8840400c014051000592035620b6640d482c43d0700301600302303c5e611011003004141440c10b204a05a1103004600c0419900f072802010700000c10b948403a410049445583c2c0e401151400180c0308101c60180800d03c10340e60b41c003004410003e140300e0f203000086060208131201c0e0031000545c80010507040100410045402094420b11180d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 50785678 1250 50784428 50784451
    0x806070c0302120d020316021c03090c1805090d0c2001110d0e03070f0b0a050f12090c0f010519120906020d0501060e010203040807050f04020408060a0e010e15 70
    0x80c25180032030400c8030301c000c981d00300a00407a4104000d4501c1d8050b41c0b0070750b0703031036003e40004212240a0383d9460400a051243c2c4171031151401c400c900ca900314600c024440c507d40c48803661166082c5100484070040b10400c50342c0c0e60100000f06000304000e0350780d00c0880c02c003403101980580300d04480c071084442061250b1000c6030ba505441e403180150341c1e004145881580e14805503500d00602c1d03001c984040d14030030701c100f5102040c209050716400d021201103c3c60f4602e0010302480a440d0350708400d20242110070240032440c0540030b80c4100c240300750b11481c060102c21a18104110000b8110009241041428405907506210400920400c6ca035241400f110159440c0c07080e5001c0c3c8242031004004600102d4013185880103a00034a05840c242e8a6503c141042e40c001240d0303a005078481e4408130362100208215a0911031200c0b2150072000d0805441c003501c5081e024940ba200361000500c0301d90b41d61400c1b00250007846a960741e140c0303000150604644902c200c1310001001392980091f038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 50786928 1250 50785678 50785697
    0x1b090109050301050906040b0106090e010e060307081203090d090b0909091002120411030a080f0f09060c0309010914010207060305090102070605041b0e0c07030c03030603020604091d010501080607 86
    0x240e010310100001010000c00a0086140403011282c030780005a80c00c0300e802180b2000860f1050140134400b0540d40c43c09034005590780303810320701009070501410458142c022400701180002d003e2100494000e00220340c10b03a02d0070600501440d203801000c21104004030341030f081c0640c0c0c2e07002d030403507050785000c5642901c0c9498650340141048410038169001500c0000d15212610100d501d051050740520f81607882c060442051684480400074020b1000c2410440040080d90440192912440b06001e01d41031800d80380c04107080f0390060b0328801407940701003110401586e20a0501e0701500500e1004040c549110340042d54503a0360740030354000e02d40c40e503000500394842541940c2003290031007020b120a00380740c1000c21f00e01c0105e00c1c0550480114000c08a0940503501c807803070040c03910301241d9290940a8a003142c8076088280c0841c02c0644400300000540d549001a02c0541402400041c07014078080e4091302c44c070300b0144202d81a90405d0b00400c4000c03000b2680ba44d00c2500341c144500361 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 50788178 1250 50786928 50786947
    0xc11010518101403010f0609080a02091303020a1211101a101107030303050106080c03040f080313051c030e010612020d020a09060902070605010914010603020d020c011805070e1b 78
    0x3901501850a0440f1501200000c1d03d200c0d40c009000c02c441c407036150282c400740c6550b4910b40b59040200007a4000707400038040340c881603a01c0585100c1a00a106540c00f8524030744d0b5180c04188140c0c02080014151482c280c4400c500307020310a8071703011100c001c029071360079a080e0b00d121000800190b803040e100c0f03043d14409640220700c40c1c003081da00e10381503035a041c5c0c0300e1034090000c0000b03018800c005401100040c1c04103030100120380c0501d800c1144440d44000c1c568401246500050000e03c81a03a606602070000314100031254100d01700c00e5242080d04140a001030072602c2e88110129a0b03810840c0800054040405900b5102d030155120100028140045150347c100c40c1c1c40315116900e0802e00045040c5180e029009440c400c2c1410300050f41e03501948001e4821900d9241c440e40034440041000340c1c020381c000c040a400d40d18002d401c0c414405881402c45100396807034142c42841d0b6420341c3c04c00400340100800303400e01c1c41200c800c600f0105246584040f07500191100b11a00241c40d460b03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 50789428 1250 50788178 50788187
    0x10813030503060a0f0905070305060108090a021c05100912020d0e120a0503030405070614070b0a0e25090509030a020717010603080315041a030a020108060f0904030c1101051810 78
    0x1400006403409240ca07035401241b001014201c1d403000000c0d00e808082901c56100c0d840c034601a00910b401032002103a16020880d2004c1c4070081c810101840d5082140026814425800c0005400700006014030250510b5080003243c4c0c0105011074004006034030b85650001805104031a041d9605103e42c803846a0749407410f407141c2e4000d8480e201c00700420042080018101d0196031195070740b14007104102c955101c40780100d00300201030141020000300c000060394000150315a60204882044440c0c500280d10200c50042001180a55000030310400d0b005004141d0040c1c0d40c03000170740c40c11056a07402901c07401e01d1702403801c241400d00030a001c030000940100010756081901c0b60f5490074a0000c8500d070024000c0c6c2c1901032803d1a403030612000400440c0c91140c4006030240100040f0340d4011280310304010701d082c0c2d1105411484100301d481d61030a462096200340c484400100003030401d0003110001c44902410001c040101d144030006031400301034604000c3e110b01120a41c8541c007900c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 50790678 1250 50789428 50789449
    0xb0102071e0f081e010c05030a0209150f070b060a0e0106080903040306060b0d0e0601060207120f0605041101121a041a030a05012301030c0e04080c0d0203030a0b01081303050306 78
    0x1901c2081108010031580b83c0800c6840300c540301126a400103140d00c02002d400d88084030b5146020600600004014400c1a0010710754044010651005500d90983c1d840d4244c00c2289052407484010034070000b000b001c0c8000d50f030802e10441e0103181c034900d80000d4181c0540d0502400c0304109818010440450341001510702446d4404018068140c030ba000c2891903401c410304a006490420801034070b10030011034043d06036881c0d46c1c0131381400c3d0704164241040310007801e400c07980c611281a02e4800b144140c45518011031080b04a18a09801c1c000014452071601c480c030b84460346400502d1385414a2940c06d41c200d600d051b070300820283c0c0e59a1006840d400440d05981d058010121901e080003019884035441c003074070355100f40071201001300c0c01803800403d01000b0803540c00d110080c40b102c0380d254105603200d0701c50300d40c075440d180b8185949814507a4035884200540d10100500c000c00c1c0d8030380039003618a1000c0c42c12140a1501c0707003510340030211107240603081c00320020101e080d503184e81c0c6109 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 50791928 1250 50790678 50790689
    0xf060313020d081206010e040519020306030316060c080c030f0a18020907090602160f051e060a0c06060b03040305070308040c050a0807080f16091802090405010903030606030b0102071e 81
    0x80e0344443c40c20804d104244c01c121402800103c1e811612105490588951400b84001c0310014541d242034080e940000c2d4409407c4941c94070051003440310400080d100701301098071031100810402007440001d0400ca60280c08500042414403c000c055070914280740e521924000001c940c1d0541e4400c50b03240ea0391000d00207500a42e800042000751600030180c0e004941d000d41c200d03a9204d1101c0f070206810903040c002c4201e1880001c90400642c58200d04c005401741d001c102c0d900e10040100001500b40c1d02414000340456050805001404002d00c5890300600345800d41514610706030303034010200d03c00c8102c01014408140007003014403a480460401400015150302d44068850200c555100c2c0f0920130180e00744900520645c60316070115080c81d280e0760800d40449017030b0410450030050f20381c20200d8014004250903100150350345106c0e01e40aa401140000707440310443c1001005c2e2003c58010342e0034103041180400070b13a607000840c1012220a03c07800c01c1006944035030f003000c07648140d100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 50793178 1250 50791928 50791943
    0x40e0705071b0308070210020705030c01050309010609060f14030601030b070516050d030207050c030706020303063a02040e0106140d06090819090e060307090c020f0a03020d0e0f060313020d 83
    0x11080080e04002050345e0381c000c80f807114016482c04c5089948010750300071503415070080440c0381e01f03550013040070f103070411844070012a5058503003201c10100d803610f91120107148e0b003044c41000aa110224603d800344420f6001d000c0d00e40c115203031115400030251460080000000780e503c0b801100d2002c05480580c0141a5115a00c02c640d0080113500500c0050303489001d600082541441e001960408071000c03071700a1401c50b55040104a0385044105a0070860309884188130310420074048a4200000200700e9110800458010712044031403598200c81d03140e160400610041c2c044001652000c0c4003141c1507800404949070030300c06404086001005807c0c01b19621480c01c1e0f03918804000d078030080e41c2c0c81000f1651015402c59011080e01d5568140e08220014801c20340107400020900d8810f004598100304e480c240e2500e010490a410390040e00100040c040340f40d40300300001c110110884802c10f00000510000f185484040c0005101c0d40e08070012030f04540b10318940c4e0300d083d03800111 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 50794428 1250 50793178 50793233
    0x303090a060306060e1c030302090a080d09150f02280507030602040e2d0a1103180609010204031106030703090c08010b100309201f020304081002040e070507 69
    0x40c0c081d10190003131201043c0100800404c50421040076500e510001460310f02900094405400a503c040e50322504070000100104442c00208800b10441060b6a40e880349a4070700540031801e07001e0402c210b000c00c110007001c16090f51b40010403400791210440004144118078515070982000c081d4002d2180c094444004203108a0358007400440d10207a40e046102d580d15407480c41c6902c2e070107d80b0761148142c50508080700c6944910b20f80d000d011600c0008503030182c1040340c4090f40003202e10f01c401c0049140700c0b51024105100e10703504049000025804c00e42580d5a0700174202a4241c410b00481e800720000c0c00f514802d42240d2002038109141c880b1103030703c5d2190756000e000c1e4600054082e000f0140760b003400760311038420000100d802410403440c0704500e0005510747d9041c4c0c0d00080d40506507030110007050b000c54419000d0060150002e40e50746142110450414400207000203e0a105010400044403c600320507444003041c944517a64860781d05d032940c01442c1c40808160825240c94 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 50795678 1250 50794428 50794439
    0xd0e0111100608010f050c0703110c06030406020306130b030d0c06140405030705070b180402030a0b100201060501080c07230304080a06050708061f140d23071812020303090a 76
    0x144028191490742d0020705c401310b0781080201c1558000c2d1a0703003100b01010055540864454075180100a9552040d03031a00d103011400103216401c00d44080e64030303903400418007656151901d070f1104101d81c50b50040c07001488900c0040d84881020390b00c081441030340031113141000700d10381c030899143e00a04042c0515080034200140d90342c0017008101c1c2c0902c1241401b049494a12090b2002d00880404401d400e244020512020b50400307030032000c00b40c1d100c0b842080c0598034007484109040c1641d00000300249094001080c0501c0a0301c0c82341050780802070b10010032f40d0344100b00034001d00741c0d40c03005008c4ca0301008a45180b20701c1e4030000290154400e10000c0010350b82040b4091003039030780c90007443d031103070303402c00c05504424419210244418158074041c0f0340a40a140394500b04c0c2c411143c1044210009482590742141d80080d5400c4100202d1100d20092451aa009100343c03804900380c165165010301441d4a42c000c03003091049480f070710781c119942003080700c410b048041c0c0b0643c0a9503541 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 50796928 1250 50795678 50795681
    0xa03150f06110303010b03160e0405010308030a0605010e0d0609050f0a0602040f0e06011215052106070810030209040819180602010e0601030b06010306030c06090e0c0307020d0e011110 81
    0x60188900140801071004200b400001c01c4c0d80c141c882030f656651a42e15a0400ca00c000e00002d03d400c81808a024001a4a07580f03612584d4025400380d280380b6903a00d480c1e2130150441d01207420480c144401c84c4200199902d48103136211140742c4c000000506174145040051030131900c401b000707403075115014000c000c110f20354001e0012104030415145095444141ca64814002142c0c20b0780000e5110203480b0418040c3e410481000c0b0404070403000341c0c0d840710007240d4040c02c0d144800d003002034054104c4442001c2000401e620845504d032501060400030350384420300400b4800179120780c0700301d000304081c0002002120318541001140c45442c2e840084d02030715440c580000100d00f40d0111400043c01d50060007007000100ca0100946103680c00c50b2349413102e10002408132410196129808000180c0800b4090040c11080d155004010b02e000407040c0014002480d218410100340700703001180d500003a155405907000e052030414280b00d1001260041e1564030809030700c0c801c0d108101d00d41c0626 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 50798178 1250 50796928 50796959
    0x2190602030d0b0909150c0f0d0207020a09090c03080307052107020d0e03030406050f040302120f19020d060b010c02130b090a0203040b01060c031206091415030c060a0315 75
    0x1a11814482e6191900400c102040c0071160208182c118009001d824582540c410340d0213242007640d1f50601d000d068130011540c10013280400000e0b40041e544041d8900100380d0401000d03519001d0018401945e640c0c40706445600c002043e034078022010510325401002554000d8080360510a8048040be694900a0000781c1d485005801900d9402ca0241d1203080320380c90406000d802140703007500c2c1c00d03001c03074207544140c0184403030300700501c000f01c016541e142c8106007921320200240650030080c1d4010307040000d421580051220802c1101c0c0068442281854109800c10700028076a24581c00503141401c1c21000251b018049005c1c5401140d03865000701d0f03080f84180c42d054102d54808881c903040348000e6a0150100500200422446204804001105200e45000c110f8245410030f80c000340c41d01c41d00081101c075102c0d25160300105024507416400300b00c0491448501c0c5542d8003090b164414600c505010b072500041e802c00035802a0880e1110303e0001d1402100c5136aa2248030300c41444 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 50799428 1250 50798178 50798197
    0x309060313060f0b030d0c0201110d031b0809070302040b04090f0c082e0903120501030506010509071e0302092101050601020c060a1d010c050f0d14040e130219060203 73
    0xd00703061500c045119116244c1c1c08200913001b001a02c49092003501e802e546080d08038100400042c41790040310081c001d010810303015890100e2150100c02c03045c0b110790251640041044a40c800b005a003000016842085a8041c0c6000400802120119028025441d0301600c40c6078400d0b4200704110320030490608035424007003134520013808007144d035100740c910404240419040510b2449118400c1c1e010700c802c18420709008583c480840108001c0d01d0099109480903001140100441e045c107020303e6a00422034130b00a40502d00350300944040c041820115420190302084000c003540703030701602d101c2c64581c511407480318021144496020705022500c160060140703601c00030080c01c0c24010b89071520016114030484690003610300800c03510200f041410496145010307404120306110304042d840188002d41381d01c128442000c0c040d41c0219400746035040e010001001100000c01d101c640007030b0000f41c10010000140006a500320048113030403520035952100040964000008001140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 50800678 1250 50799428 50799431
    0x60919180501060b0a0c02061b0a05010903021c0816020705060c160504020913020306030a0821072a08040b0a0f110a031b02030a0b180714031e030906031306 69
    0x1511243e0009090141d0303105d0501003016402d81000600c0c002c0302514020b1b069190200a400c1407902051502030740c00010b4419965600301c040a140c0d0500c01c0128039070408410404070328001c140100003450041148803030f03188014414088900c01d100c41401010003c007166201e00b484800701d03445015800840102e00d00f00000051181014000e43e8030311a002810480307031241540180d80650700c02001c09a0500441045500103603d1034060200c1d030392800340e1803025000b010060007403104041d02c3c0c40c0a21015200405c9100620034146c461600201c0040109828615084880f805590442007800c41d02180701d4440c0d0b80e00417040024844c1540d1a01400c1c450201000e072180707485000030740001d4448008110b42c03908412115242c61014040302d404111a403100a2940030a40e0b030010003903150b0079210709010040009001506007031265034510394402000980c3c503200759000c0d00050070700c2246152040014420340303248800140c021a920700d052110302c41c4403404200100c5009 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 50801928 1250 50800678 50800691
    0x5090a02121e0118030c08091305010305150c0306011b080408061f03020306060603130c0308030106020f01060e0106080c0d050c091e03071404021315020105090a0b060919180501 78
    0x342c07414007600d1501110382c1c0c00000d48002d00e403000c17910003118480544500c01c1c00c100c2510181c0342e0000000c01210104070004079941945403290411060780030170b8100c90410028410a50b85400c122a000f05007400d203004403800b4140794094218061a01800c010400f290000301000049800d512520b403c001110710f008800c000e41154507030900029400d5072003500010b4940c148007000390b4000c5140c40e804015010966142c0c07a00307018030703001151440404001044050380410a00a043d554000244402c50400d114400c00f00014070907502041b034241e0100380700740108170445046040f4184107000070b20340a603001c00f0a60080546c2da008200341152050101124240069510001409080703c1490300700400c0c0140e103810b0072558025420402803c0984209807210018a14a503072007042150201c401307030850f2001810039140e030304040486c4c00002c00c40700c804d56000c1c0085403031380780940302d20b06090300340d40c11812058603082c500030080c1c0500d1001e00360380b12854400c200a0148 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 50803178 1250 50801928 50801983
    0x927021908011a040905130501090302010902041508120d0905100b211c11011a04050a02031003080a0203090405010617090309011b0602300a0c0c0605090a0212 70
    0x20f00e0b911244145950710901c8280100c044640100380c010702c44c05d0310790080ba000d41e01c0d0710b400c5071141001200580e544065003400c5003054041c1c81c0742160181000c6824914101046403510208144141d030200c3c0010845002c0410340d1000f40d09942002c1142c001e00c03000b8050500400324208100d01c2282d0040180d218900c00e03200903105000c9100c013421204c021783c00540142000c0403000b03030038000c181070380c450002801d20a46000c101600d0060380206191401d1108840000e84030b9000c040c01001000b0ae80300110b50818211b9910581a680c1d503e03900c17104a0644c022410002d502504207030000a2160344208841e80865544c0c511b8007158540d0f0200319600d104141c0d00d980030902c5004100c201349003c85039981228010000545421082c4500d0060207640e803411910307240e20703583c01a400308480c034583c2d039202c20805801c1201c7c4840150145c6140283c800c020102074a6000140007800148803582200764054050b400d0710060a040c15112580c58480000220200b80511030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 50804428 1250 50803178 50803199
    0x1060b09010516020117070f090909020312030a09080a0504030201120506030613062003010f0902070b0402060309190803061e0603010b0f04210c080a0201092702190801 74
    0x2900201611003600e4205102d0034a80f000e01c0740c19081e4107120454000c01940c0c8804500580b003020242c0c1e80c940610b4141c4405081242d0b50707040350b40f48038540b400c4140161000500342c4407050300f101c00ea541300d031340b03c401e170402900614000a2500101040d42401c06400901400075a4802d803280b00800701c5006035101103503001c6030b11039450703803080c0049900d05013a1809000c1d21405603d001c07800440c903401c0184c10180403038130480c0700a8000010443c4914480301c2c2400303460101c4066241000c583c941c0501c0d9078010b40040d1140b04000041070720400200800403401c0740381e60881412a09a09144809800844a080c007618030102201c86191260f105070010bd2001400a800c0d81d08005940089800008800c071550310304110204280c542c522040301003001038401d1040010701490500c0714070a01c1e502556041e4030101003100127038ac00042d600262800100c0080075801440b101d07690081d041e0710720400d914400145420119182c0c182d1041d09082610380350b4403039990b09030304007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 50805678 1250 50804428 50804437
    0xc120b01140a0302011d03010204080d11070602031912090605060f0a030c030f02030a0209090a0501060b09060714190c080c010c120e03010b090a020309010c1805040f180507060201060b 81
    0x10b030b004a0344142400198011300408900d03191041103c0e0502048001007404c9921603040803409900100d0380700c8800b64000240345801980c080a00000307840c1c0003020390b80340516540058080d503c40225103410f40300d10305050b204400d15a050007402d0407424800c0c010001a1010340c000c62078100740c0c440c1410301000c10003c41c0d506c2401c1c14141c51540d01d60541c1000c403000c04036403500036074400d0009661a840c50728050300d0003c02911a03031840d4a0010708543c9180d10034114a001030083c1d00c00c1e81c0d110302c10354501503006008280d0150718143c0c2241401e2030a006440d82400782e1103041e052203c840914001d4441c500100c0d060300b00000015103140811400003022004002a1140d06910642d41c565007000068008031f401e080d2000003031009041114007890b030300e40c04810001089824010044000d47c603041001602c25000071404440009004007802261136401904420042c4e038072100c110400d0000742d200b1340d841071a01b680c888200b40714000c010340c20002c0200d0020305000855 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 50806928 1250 50805678 50805719
    0x2010c0207270e150a0510030c0b030402030f0105010909060b0303031006140705030304030f0f0e060904090809040606030902030d08100e0c0c0d030506011d1008090a0c120b01 77
    0xa412160000c26201840c09060501428598442002a501020070098134020305200a16400c1915000c00300c50115030000700040c1c02601401c030304001007840032003464250f68116121554035520350003c01d00d81070813401c451495600e0180000b42d0700b112503000d00c180340d118403418449807103044201680d901060b980b084000e80888802c000b41030040d06403c0305800354001403800c041d259103c40f03007107801c211010303004501c01d036541003000c41d44590185072004040c1070071000700c2e50180c01700e5841d0281803030304e5019940d18503448082c8001107042d00d001550041083c4480e98941c0d600130301134089c15104078020700c1100703424410a8003901c00e0901ca1508611180c00c410b250003030340701042e20058250031601c80c0421488801200c00c0c8a03035583c1e60307183e072070114a038203040c000102008541c2c8400742105404684000440d946e0f0000b51100d40741c18035100041d51202241c0e41e081044070034004081e03104000d0001903502075244114030050140800c0161aa60360801c48020003512250 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 50808178 1250 50806928 50806949
    0x5040b0409020a020708061501030509031303020603091905030d0606020d0c0204090804050616020f0301020a02030313050c0307060801060e0a03021c0302010f141605090319030e090703020a02010c0207 88
    0xe00c401110703980079110f20f0043e48110742170940c2e94502d6504140d001d07140840380300400701c0180070650b00360145035007100e404002545064452a0400301100035400001c2c8203a000102181001701d04120f00d40c4420b150f101001c081d14142e1406680d658040317400e461620781019030004103a400414412900e00c410380b16010107082c903500308801407401d943c044610240600010801d600c0e81c4003d00038940c004c00203500c0304126401009146001000054800d2b0b004021020141e6808420b980d00014100d04103010300d0f0300c61500509000c030030701c8030603014407541c0c07000a10140d110179598120750b0303507845000d208494242404404c80c6e80d400b020790042e8003200da500701c5081890081e8001402803000292205481c64440c090320340001c000942c081010040c0000710210802c0c1c3c400306844e90800030300d051190070101e80c0b01c280103c0071525002501000500f490f02941c1c0205040000400003111450940340280080d0040300c9034000540c605a00240164000122901642c0e03901c0c40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 50809428 1250 50808178 50808187
    0x105030607080912040608040204150b070b040c0515031005090103030504060537020c0a0501140d0f020d06030506060f1e01120f0b03101a1003090b0a05060f0105040b 73
    0x99607031800c0a441c1c000f051190110100c58442010068800340086070b0b07442205082030300401c01544c1c4110354a0900c00b0708500200260f02d00401103078290b80c0d000d50b5881c015900d50800d0001d200f015072100380c001d0509440f0516240c8080000c5100300d45000702c01311500d8441d81804040c9809020043c00f091080009221050051010b407032510b80c0759408075080e41e410321810010f0042204480d050f09000510040d0640c0c040c0b09000700d082060314010742e01072501d40020206080c200c448441c1144c0050445c1e4490500e400294a510001100f55a60034038107070381030700516032448203980038054000407400702d140c00c1311049145c1c81d004104000300c4050200e0104404a44403059060243c0a15401083c5141d0b009510170301003008800624040c1c08030501d410a091004c91070800e52801c1c285400d407880e440d1444a0010003030310100c4490340c01c5041900149010310000e040c01247e0020480ca01d0b13000e4001314490305042d00c0c0c140c80e02d5030210054503540640c1c080c4560301d410510 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 50810678 1250 50809428 50809441
    0x9010e0103090206090a1e0602120301120201090e0f040c05030a12030f1805030c0c060a0f03050c091806010e030102070507030b040503041503020301050301061205030d090201050d020d0e0c010801050306 89
    0xb0401c00700580001c14441c9064480000120082400d0b0f11041245040307910080a5110644500000740310a00241150b000215200301c42c0703100c140245031071444607001d2802503911440c01f000142c200d9030032000e410b0801d041000c1c1642c1046404488135406140302103074501f070100d107040074a6400741c80c115203001044000d402400191b400c1d00003940e0340d010754403100168070400b00880c601030400b841d500d80b800e50f515030408c603100302c0650046804002800a09910042101e8a230107503140020301a25040804113443c41180d00084e442110750344694885c015620450303008402c00d03225000085e40110625091340120701015000d17400880c0c0820100b00f4480b50150300c140b20f40d003524541502c5100d0100d0b4402c61845e5500042d5000c070040c00582070034031484001d0640003d0b0100c400c003484d51a0350b0341e8802c596070030303505a071121140b20031640103d05491403074408200540d11201031000100042404801c110004e119218441c900c0d035000c0c1c40d8a82c141c4030050064840d595400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 50811928 1250 50810678 50810681
    0x150420010516061e1b080105030a030c06151503050109050c180d02030a03050a02010501050603010f14010320070204140c0a051b010203072106060e010f18080102090a0b09010e0103 79
    0x41c0c2c4280c800310344564071003500c203008211040d8610700100000070a4000112181300c10026445044244404a00140203d560006180d0f0145602d4501070804038031521f0000060420403804944000404c800802e0014502400c0b0b0300b0214150750030012a0b0f0707143c00300f2054800a0b14078494041c0d0402094001400c2400101464040501103960300516680403c2c0f03800d145100940c009800442c000030765035420f0142c0d50040c10708941090441d410540005c101c40b126105588104000c2110a40b00e070340203810018215080040a2103030000b44802e03031185a0010804a1140d8500030702780e480900d41006160007183c1d64200706040c01101c09095070540d101804001c1034008800024007050001d00046101340b030103a0724444508600640310311501d00071081200b6680c241b0f0424403005602400c0100100c0007482c120368070204508e026260b04044d0221070048402d039910103d0755400540041c01240410355010b500c140e95900744100368081c4010780340c00559140100c161a620a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 50813178 1250 50811928 50811967
    0x9010c1e030b060a1106010b071203020c0a0c0303120f05010b0a0c020a1e060305010e040f0b070e030a052104060c110f0402030f01141009051009081504200105 70
    0x1507080000b100d001d0640059000d8126100380e04c002000c1d0341800c0c03201c0300300f07215081c010318004c1c1083d410501c150741e501d09620b80540c0080201540401c1428403c00100314640c002c40d0040d01c010b40060b142d080040640030034450000f4480e0418408034003aa103144903190480720703000c40c0c0c1410480608004c59600c003846000b40d03404541d00c1ca010031041c100c2c04054261000015110707510601c3d20101400f5154140e1200c4982c607a00030400000c034243c820b0b513180e4560302401003502d659503442d0640c2c16616100d20340da014401c0254010820000052020750000c2c81d5003a80c0401c44c0360262601d0604c41c0c0d005030800680c02016400004010322030030158020300811905c02e0301d10703900c0802d0803600111012036403030700301000401000c2400301ca804401207050f202c8a880300d4208101600c0070f482841124040d141d203450170454503118207041000ba059500a0f1004c5000b081040d0070880002d45060f100060101800d0404a110605143c400c02041c0c59540c10141034a0320900420034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 50814428 1250 50813178 50813237
    0x60e150712080601030b03151f0f09020403020907050f07060905120a030e010e0a031205060102030d020a080a05060103060518251701050105120f04020307181a04050405061801090b0408030f09010c 86
    0x4400350049040e20b60f42b11240090280500d005860304c0c6180100004420060125414480100b00110030480184121203800d50000c070301040100007403910500d0f12840034400c0c0d080380408612480d580c0c1d45608141080006c58000303005c00c2c0d41c10920705495a1b0340140003030100c0c0da00d01c0048210710194003c15070040050040d07e05020344500e000040c0d9002c0c4400400084021041000ca200c0a10629400607801c0c41c0800245007450082401c5040e861118082190000c0007e20940000c00c10011103400d68814000c0074403a00e000038050341c40303c1d0000c01d039000c8031200105455208005030b071480040012402c6150301c1e420121041c80303602030816078150184080200310b10300b20161408941c9903080c00015201a0502c0d04404e0390443e2102a101300c1c240b509120100c0d00c0000d000b074005510f50986003c16800b11a907900401c0004402444031046400300000d21200d613014511800703a4214004607655070500c0d0328226035a030b690880224400d41010104d40c2e03203800f5600f00010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 50815678 1250 50814428 50814481
    0x181d030a0c02210601031208180d11070f030f0b0a020c03030403030e030c0d0e10050702030615010c0510050604050c0703080103150204080f0105010618060e150712080601030b0315 79
    0x83d1181601410f0080c02d0b042618444040050b541d603455010304010391285661400c07400d10219a4045a11140440204810000746103112000c00005003c400004e202e4401d00064a42d9640380181481143d1203050b603074111050000b400e2224540222203202190708061450351b0f0310390303130709400815111402c1700080c44207003c900702882c0d08120060b2080c0141d15840d528806034030400c1880c3c40b0021840003048014030160700103031000903100b0f42006864450142544c01900125140c010303400002e4900c2c03060004042c07000d01d03c0d501a50251405031000d210981e1081d103d8134007031094000050000700c2c4030300100085500e40e6407489008152a03805454940c0d512100f92601d0852800044240d5480b00100700c51500100e040c54418041d210208403646046005003681200b084e1050140101d401c14070b8450409604442040d07900121480ca41900500c00900c810703401c13605140407074074100c91040c00b4540000c1070907070100e03100c1d074101c0f495031104e040d400310301e0400401d810b004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 50816928 1250 50815678 50815729
    0x602030a06050301140901050c0703020307080a0219060213060914040902060918090f07060503070f0903020d08030f0a060803040603021c0e03031603060509041b181d030a0c02 77
    0x395401c1c0180203484003146074000d21410316950140c01c648c1c0250510065020030404100002d80110070f5a80041e003204200da10b80c84005070603410003003148603800c6000013184020041000e103502400398240d0b5050303002105034a482c000d0781c6210040c00f550401c0160b54101560034030780354200303001562005c2d08880c01c0a14a80101d1820400300081c081009000b804002080d442006014039000b080d90060003403d2503c2070243c00c03440082d065108110510300c010800301e018004000003150302038a252403420007810b0004564209655032a000d401c0c410103c2e03c00303815401104140e82580e00035501d001e150107400c0e8000d40c000503950700e803000703da41180c0240040384070340750101c586180919903910b06110680100f4807042400c10034103140060a100d6900c80e0703a10198800d501ca4104a41100e5040d40300412642d564044003940090500d225200121500201210180384811900c503244070001207449004020202c400204008100809890851183e12030303848200c010713800d00b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 50818178 1250 50816928 50816939
    0x60906050112021309031b050c03031206040f200a0e09010902040315021201030b09100e07051905090c070c0b0d0219020f060c03070512090a02030105060603130602030a06 75
    0x2a10000d030700070b040240ca203072004015410502c41101284881d00c0f800c018851240d40d001e480c070959098020000188400510100a010031072120700342c200030300b1240c0300c000311b446003504d001d41107503101d000ba03050043c111040e035414004d240c0c407a4280c40d240503168018099542c030541292a6034002c020703c04c0214083c0d034440c104044e020304403081c00940d507136003507041c00404140e9503100a502c00d44104044800003140989690541c1d030b0002e20b001181d1208080a0301c2c044943c91a03039211468165060f615107400200c0000716007060b078441c61401040099074070441201d00c41c1c50b0b0080841000103250782c0c90355000b0244280f1485400c04ca9584800381503d140e0421040480c0071a1700040a4528a040c0d01c09101c86809900c02041c180a050316104d8807040050000e000320000400807401e40b5000300269620082082c040103c1443c041211741c0d9156241502a0f02a510341400b1038041d08004048078480e0301d00405c01c002489a0350343c1d0000940c00200444138940e660040481c030b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 50819428 1250 50818178 50818181
    0x50c09041401030506010506070803010303031d0d020a110103090302060109050703020708030c030618010302010e0d05030d0e0303010f06091505161e0b09071404230c070c0504020304031209060906 86
    0x510310800749468031640c107600d000c42c90603a044e00054445d5806100d8040000d00e000d0449056035418900842e046084c81040118081c0d40c10980f03c01d4080e10f8400302c10740358006141902c0314003170300c02c1200d07055200c00154201c0b0940a005030040c0c10480c010f11010344180c001e03680200c058a0010320309001502c44078010382060302ca600501c0400002d100d80d070315281c01c010b603511030b00f4807600409502d03584c000703000b40d05c01200d40c0b40104c2400300540103000c01031059a985820440081c00b680440c4059035880742d000b40102403a102c4a5040072469900c60041c004c151030f42d03d03800310710800380004240c030f080d00f0180b004140c4240100c0e04100044a0900403950f52000c903080c2c45c031041e06072610340100c2c28001d203500381c207a00540c0100002c6000147e120003200056500043c1e2005d075810590140c04403032080c1e0b50f01e202c07003000d1000b0100018010180c01e4010b80901c21030b291101c08100903840280c0f806000507800d0080c2d0807200e4080e1748000b012910031400010b0a14a0b90360307600 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 50820678 1250 50819428 50819441
    0x60906070b0108010c180504050601030f0f0606030f05011202010809010e0d0302030103051b2b0501050403020303070801120803161803110a050102061003080903071806060e0303120a050c0904 84
    0x658942481d0010032540009001d015803401150800800c0c0300c02c01d15941c41c6071060f500c925032145480d80e0100c1c481d030f400b9500c007100c400e040d00070906c004084494000c025084500c940c1001074075000340c030b20000e0940d20800c3c2c1a564558000c20a26415800450b0820030241c060803047d582c40c0d018004100040100441480e01d0b52005a01ca42c51400d203d0f041458090b424800c402c4c0e82d0046070155500c04621000040f240d0801c1105201d006c0d5810340c4180200c40001d04943c42c040601c414990000080d620417a005c1d5264000b03a86c884445800860f210380000340f03003250600128040d031782d01025240e8051410701c0d02003070b4811440c011a8140301c0640c415207014102d24080030a50070101150000b41c40c0c20f0006113140c2c1400e518100e9610707071728480940317444008240448940d0341406600001d0640c0b26100c00000700441781080100380b14400c2c000441d115500d50b000f2420040b0507286009045151000c440d514624890098000144140c1000d4020030001100d65074030711401c0c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 50821928 1250 50820678 50820683
    0x1b020603040b0403260402011419030203070302130f03020f0307080303041e021f0f03060b0d15030b0a020409060f1d060102010612030206090601060203090307090b040f061202040518150606090607 86
    0x144030501b800e000260414006072040c0c580c480c0100140758420078182141c0d50a40118500140d896550040480003401010740552012108501c00195008403040c1309003601d00071210000b0b03500c2c1c40402c25130b560000b4130406285810600008006c03490200e455882805184400400552540c2c0091301094010400494034808140d99200a550042c2010300c91100c0c0e0504010a03800c1210030320703180c054403890b0071659465846244500c10990750b000000c41d4007841449081c2450080e030f0b0080e42050054074031140c94000d0004140c0000108007040325403210b031042c91500c5003a00c43c082e8100091000d4107545d01c4510000fa0001109117808200d0b01079400f0302541d0920505042c1041d0041e80803c0441d8000e020344000d5a50105507502141c4214000084c1ca090000c04240584810b1228010070b91030b140740000c6001100d2840800c0324070880b0304100301c0d520350140d01e00044003152005481da006050050108101e0b901d001d4114500504460401e40104d0010704aa030151004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 50823178 1250 50821928 50821997
    0xc1506030302010f27020f04020706150303020d02010b06030103022701090c02100905031c1517010f05010f15090b030702030a0212030103020306041e0204060603020a1b020603040b0403 81
    0x4040c03c10034541701e08000c00098a81c91900010031000500c542c1c00c40d410083d1103050130488244080d502d0303034100c4201d1a8004030500602d1201108091480a0341c441603000d80940160310070f0b901c3c81071103072101c101001050303c0e0640c4d003150284001c40c241a610118001c20148284a40b02d001d540c07210300900380300341c0c081001503038030380c00a08140b0000008601c070383c1010f980000107080032094605e10300080d10310080804421001001800141c040044840c01908000c1008420a103000e040028004024008480c03903945017001c89034248100404014482c100380b0034901c44504c140540051854a41030f002d40707408044107203a009a070308001580c4002098140316405000c00ea0140313a05508150039985543c0101c2d4403440300400090110365502e4140c113900f5004801c055903070780c0151080001d1901c6803409402548003804400108030f03040300003d00c000140071041d01c200c0d80506040d04545596070381c64801e5002a000320144200c03040c201120100c585107590500888841 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 50824428 1250 50823178 50823191
    0x90607060f02041403030c030d0504020a0e0702060105101d060c01021e04031b0b071b080d09080c0d030207030206090607081c0f020a05030f1f03060203010503010b0a0f03030c150603030201 83
    0x1c0c80e5582c2e80e03030b03200c4d07a40650030921a16000750004001d0740c100c1c44802c00041480d54503840011040001034115080f030301245c105000e286035001035114103868090758078401d94030070003000382d03090b450191040c0d00c100c20104141c080c0b410480d000c2d00003d20210300160070144401079440c0d00445214030b000842002250410074007010880000c0b40c9030423400040281420a481104030340f01e03925018001d180c1ea04c121002c0340d43c280c0b000c60001c00004096a8030410f210f0f800030420061403040030f2403413140f285020b0461910594070001c841d4160010a413251039036081c0501034100114181d4411801d1001c00c01150116004144206818039410f03110300d2940307161002c44280e0019a800c40d03106004404d05c0725084011240c0201d814018190903584581c1c16a507075a000b40106890f0031900240002040740c1c0303401440c1a508102c0080c0180310f5540203000201c1d001e80b003802600320480c1c4003000424020b0a0341644a1b010380000440e030340500d4840e8041c1c41c41d0307500840041c1e549a5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 50825678 1250 50824428 50824439
    0x603010f05010503100203100e13110306060609011202040b030c1b01050f060607020310110405041a010903080d060f0e090607031505101205042d05060c090607060f0204 74
    0x40361040408088508022075410080400e50380c06820381c00200c00d0798000f01007540d5948489220000700b401e920240f1142c40c0c0030041118400380c85900721940d000364602d20b1010316000c9582481904003410441c14030302424011140ba140039440580c00360307420800403440000c10b400640c85035020380e011580d02d940141e120003041820b400040702591524051041c0501113440c10380d0407000c2229551b84038a00c0c1e000007401c00d4032800040c0c0d40180ba00380b69030041c00e502c0e409001103030422078003005541c5000c0c1041d0703801038041e1029400110f50700c01c240300298550340542541410103c3c00206a51039101040b000b802c0c503003110203902800c001300300c1a01c0c0c040000c56484442d514081c4191a00c3d82c80c00c91411415008203481404640b040306409842070144d650160041c5100b44214145810600061611000b019200301e01e808204604041c2180c00380c0c1095610200808507a84c81074502d81071a00710038003807a40588200b00c1c00300818054002c4450038075162400503034491421 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 50826928 1250 50825678 50825681
    0x603060c020f0d020106080712031b0c080d020a0203030306270f100504180b0702030d0207060209100c030207050103110403060c0e0a060903030504030b1503030403050601060f0306050d02010c1b060503060301 91
    0x10300c1803c0441e0305015082c040d03518003184201c12524030011601c0071002610301030715904d01d40c03c1820380c9245503101c03100a100704c00c1c0403c000c032005401a500300d1500044202d0b11200e90350300113034141e481000410341904040600070030503200c0c0d418203601c0e910702c00350212034000292070003030070242c51409014400021f55260401000100c80c1044070650024078007118071002d0001071f1000c01300100249040f40244210fa4029034000011555000386140000094001300d011600802640c4040c4880c28003401032000600c0e01030700203011a84c903000045025180310003c50601c2070090100200040d100d00920352070000c26218004040d200c5000c6c0200c00ca05507004a04002c4640f10130004280c0000488064030380180321026566584401c1d00095441034a1003505880001000000d1140c0820210305075049961041d0540d5124001201904c6c000d009050380491032018240056000c0c4007071030001440707120990303107030f180e40c0d1003124400b0090b603c0807010a10000811107580342c20b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 50828178 1250 50826928 50826943
    0x809010e04050121050f0109050f070605040506160602070821060619231c0b040213090509100c11071719060b040906021b01091709040603060c020f 65
    0x2501c0c10450b56260414100c81651107a540c1d42013011402c542c001840700500c858840c0c4140140284686131175894440c2c0c0c1c44004001e107400300e0140f07600210342944124110b9007180c8000b054503082c812a22003d102c40702e00c0090444600341e003000b1200005400801400a1503d8002e0056040c10b80c041d0806d41310360010300b264400d940800111010401d40d07441605183c03c40e14000400e05060000c542400788071400c641940c000c0070444030301c109500b404d401c0d1180302404040c0705014245003444107074018a41c2088290000c0074052108001d80e0f84100c1c0c0c054088000c40b8010170764242e80004a4120070030000020f240201c8030b21949a00300008002400000406002011f142070100d88800c0d640ca40f41041c55031984d224170602c442504800d401c9040204100070b80503452804100940c00080d90f8400340c007007141c0304440f2075818820403d540f070304040240b003400321100102a050384811101e80e409a03581c400840455110f104070f034400317002074008181c0c02c104581c0712480c1044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 50829428 1250 50828178 50828207
    0x60605040e370902060f070507060807020c0904080909010806061002030304080415020a05010e0c0405090a03020a060b04090f0605041a010f180e03030709141206150d0f080901 77
    0x50070500c00200c44180c03508010804000340000c12214a844810090500c21030045d500031000b141c106080b0700c0741c90003804602e200d039080340d424554804050361041401c464075005604040383e14031f07003400d216042c1580b040c81100100d02d0119600001500b6107820b030488541903022800704402810300040c0c20801c024540000c505520f4030f51340744015807245001e00c100c41040b140c03d00d40c101d07000b000b42d100f01c5680400207005000700d201c0e02940d507a00f0403440c9440343c2d0914002c910f410001049400d00701d034065000d080000e0907074813640e002d021140d200341c0d0001d07910000003003c0b91000300d650307403103a00c10364001c00c0605040c1001013038800780c801c20902c074050030b0b0010006080b0180c0d07443c04880210708580d030b059402460450051901c0411403809000001c200154294414500300c2076906103000713000b1404005062102c00c0300d040c008046294850700110b800b0b1031154040c031200b014001c001200c2e07020075a031112040f4110300800c480f200340c04102e04c3d11560300058804000d68 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 50830678 1250 50829428 50829451
    0x3100603150207020a031e0614040b0403140c010e03040513110414030c0a080a03080901020f0a031e0606050403030801050301050f06060a020115060e031501050a0303051c060605040e 80
    0x5055444041c0c0341100e10140d032180c16030001c1d16104540759404490011600030380c400c0b0200140b035070346102a0200c0141200d00502e00366940721000401d1102601030b40d0444118000e41c0d44558041d94120201080e50309022030038002110040000d005401c0d49000400c00355858625210a20a40f0304c5800320510f95541001d0034212010011000c1c1d0303084450465104442080f40004641010402188c035a0002400180400c03032600c00600e0110b1035100381d442000c15030322805150300300d001c0d10b4110300e0081810084440440e00c40c0e04480c0850300030300814201080480307060402ca50b0700d40d1080c408a0800300b0108140358212448030300402c0c09900920107450001103511721560001c0c81c50b4468100820b4a110851003507100398100e82404444002c0942c85000c098070f0b181140c2d8169210f44a81034140d03042c030040c0c0d01683d049607030103081c14010341e08540c1c2c2516185c12001620591703207042607081e0798000050150100800e4240c070741c280c0e65401e054164a01d0070004015440340d5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 50831928 1250 50830678 50830691
    0x31c02070f02090406090f11010e090f070e010905060403060b01110d020709090305070b090f0f0313051212040f0317070201020a110a0503030c010c0305070c030c150209031b0310 78
    0x40c4200001c4061254100c405088568a6251a000400e05940c0190001d00740b00710f90010410740c801601005502600c03550125a03000e0200903241108407003629445c01c0010100e09041d00490b844025444141003155043c1c2e100c40118070716409c02d0b4001d88200d40c8841c030003803555030042520142040b0010182405060008000e07640c3d65061041c1d1b0341c83c5568080c9041810300c2402503c1c0b07060340c0300714140c41504040d81042d40d0313191591a00d402600904103034441848002048401451030101c420303000b1846e2000700b041601070b203049040d10380190b5040900361041d01000304050107800780201541811410002c8102d42141d410b81c0212508006501c00360f80c0000b00003060550101d401d000442c140e502241901d0003c1d844035416120105840d14144010b400200c404c14440d03030304000b15611800c04483c1d0002c15500030300810803020000b4049030760014148800c000d0000b0140c9081c2104000c03d10300a21070304c0c0c14040e41078000c840c15140ca424002e80034118a01c640602c400e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 50833178 1250 50831928 50831933
    0x120a0b040b0d051b040b040c0201060905070309020d0224030a0507020c090403050d050406020c0709090611040e010e10030c08060603010e01020405010e010c0f050a0b01030c150507020f010207030b09031c0207 91
    0x85031040c04640701406819150342001740d949410a4a03650006007041c03009000c1c24a0182c0039003840d010b5040380c00d01b0a40004e0840380f0030312442e070620390028440c4074040855028084840340210900b580c001541c1c0c85606840e020400840c01525940d400045910342500000d0038042d42d099110b118102460501c00400c5e442000c2e5200241640e00c00103440e259451724030700038802c0c0c06007503049016043c8001109191540315180641c0070b06014045161304211a45443c03241e0300489030707251000e40052241c0c902e144000f5522a0981c000308a900d5125280e240c0b182c080c5510550480d41701208005a9090a00484d0b09031000c0c40020360815092100180542200f046104d04008516a40d00144059031010100302c0d0303080b0040c1c40c00700c0658142034007030070024002038403075000c56040011004c018a034000c081e0b0985507a1242000d400750300300240304150000b40790440c800c0c0080440800e00003410540100405001180d665042c00c040620620440b4101c48113070380b05000d600b01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 50834428 1250 50833178 50833183
    0x306010c120c0212030a09050604030201050f03041e0c06030b010c050615030312010602010c0f0c050c120309090c0309010b0a0509010509090f010510030b090604150209010203120a0b040b0d05 84
    0x108290300080e07100404440c40800c8444a00701c003000b0f50b2041800290500c0204080000c2462100c0307996010710598407101444910b11851000030f0028400b0480d824089034542c0196820030320403607800484070b40700007004040742c8416006a03100022500c04000701501445042c810b00f101382400c801601c269100d041e26075078001c0c0161310b0201c040822400c255018003c40c1c6020307047d8400141556140c010003402042140c10b40008181142a0740d000b0a0254076001c581550150043c230f2644940014400201026000c3c1e192074030040c0300440070380c0d80301da08a91080400c1e004c86912840c015054500f903642280025008150540382407107242c07601032200d41954002e0b00d1602345a250701c020540751a0840003c1003031548cc01003400781041d2550404801c580c0580f060261984440c600580c840c0c4e000d8400a2450821b07010840b103901e0f030380d00903054492050040d030b8246210b012030031b00108011504540044d80e9004148018603242c402c1d0360a000059071549514440ca5070b0f000da = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 50835678 1250 50834428 50834447
    0x1a07030b030c01120b04020301090501030b090609032203020405072a05060a090305090909070501030606030203060d061a03070f03060509060f07050c0a210f050c1b060d050103080a03060b030601 85
    0x60403c0401d40b0a01410130719034005e98540340f0083c00440da070b0360f9954140e00c01403401f804111900c05000000c0f60700c01c40b00040040c024145040614035000040d100454111181e00340c039014503400c40c000001590320391059601c03c00a0f40c541e900742492105010622003819051504514400c0c0000130105400081e0543e21414100c0000f491040301d0500783c2c1ca501904c0e1b00142d022401400301700c594200810f050041760340a8906104458540200350207038042141c1075038125041d1001480805c0d05c54009100e500444080090860308a0002c241802d160390007501c088401c0c03400410401501c0d100d03031a40700b911480a0406420810010782840300c3c05080d400402c5004102c40003816800d10036964002d42c811403644003206420041000b06600c40c040354040703410304540c42d4405000c3c90481d0741243c04c55014000340c04c0d250a010030319039020704071160001401e0011402d100141e00c1501d000e140105a103503100c80c4170240c028190346042c4c001c1300c01078500744140440c0e66084226903 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 50836928 1250 50835678 50835703
    0xc06010501030c0903110402070b0709030501051003020d1203090605010b1b03030709050904290415060e010b0d060803030a06030213090809040203040303020d1a04140f1f030f1a07030b03 82
    0xb400d40c0f0500090023070300448502410003c00c1c2410303c4070041d00401e03800b040340c0c0308000900c8543e03a0300c04100c804142c0c0c0d00c000382d00504030740c0243e0000341100304420b03458012820001140007041c1ca5200840302c01340c103c0c0460007000581c00103620b032902c030750002501c030321401140b075490120401000740e00d00d803090b10b000303109140c0494200010500c0304031800d102100b202c100a0307400360b071a0340c0701c18060750b041d03589030320036026a503a0102601a00c400d4448008010742c1c40e03407900d207403a906036000c0000c15002542d03902c07002c02c11070410b00045000d441034030408200c243c203500401c142c0c0382e105240607900c5440e240c6c90b54002460031096400c1548101c9005880e03a54605066003c0c2c400c441c041d00c4080c1c6402c83c1048000107441507807502c0da41c00c1e00c0400046602e05040040c43e04140d442120040461002401c1c0402125980c0e521200559a01e01555604d07030b40e81c1220503900c8011252062111500490010f40301440f590003800c174601402a0016039001c6601c41c00a070006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 50838178 1250 50836928 50836943
    0x10180e090708160920030703060509060916121d0307020111071a071e06050f071407020609010c120c150c0e090405030906040f18020a051219020703050c06010501030c0903 75
    0x8010240300710040c0482c0f4100600d026921f1907da40c4c000c0041000e4020b1a100f03440c50b5000c07540394245240c0341c9110b012a442e61440303000e00c0346815034000c1039280c0039055184e1908850f0704d20101c440c50140c11103600710001c645030403a03880054101e03140171001d0101a40f007210104550016880185940c120240007140c3c1c8403241c3c14035030a09400380104404812128140c0c0702007281039400144a001c001030400358645540400715007810b0a00502c103c514424081d00002d4504a0700800c8031000c1410204d030b0b95a01642c4070b6040308100c446010200e007040401e942800503000b804130310310300c0e410000c221179850024050505a0070341c20b01401030700c01d48002030400c68108211010740000038000c0b600d45548a840036540800343c040c1c46c0c11340035200725805801c8100e000752016801d044c1c54160410b89021403c04210600800c8110340340001c03030164041c1b00051004044550180c0d071001e544407001101180f0703085040e4003013030425280500c54000207600c0140d540641e680f0840 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 50839428 1250 50838178 50838191
    0x10c080f07050f040b07060f0b010c0602300a0f050f13170f0a1101021206060a020703060203100e090c031e070305100c02121810180e0907081609 64
    0xb20341c640900d04011840c901d00060124481c807440d00030705800391040e1014008407454004103000c0e43c40d5403800310701003501c5c20030b15000a1900d40107000001604400c803010856454182e1448042e65040d4848820300b10003030106000c40e42c000c0030721603402d90a00307004a0910108481600d9001030900000001c01c151901c01c00c044200c915450814440300e10b07403070790b12001d5000d00c0ca5005c20200c030f002c174480c0c01c4003420f003503c1030080e6140b05404011405842e81c80c0414800554002c0d5585011405030442c080700144051015500640b069002005198188450b000034240c0290100d14541e00c9a2782021165400241848040c0080700003540c0c22220084818035000841e080100640500c0e0900904010168043e00003100142e00312009002d0813100e540b603d00c02c082d102035019141c0d0f81d2071a01401c0203610342c0c1801d0070521f40748014034070a01052200c05560b4000420314490364080c060440010085180501302010142c0b80c4400c21410852400080e841004804c544031b15 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 50840678 1250 50839428 50839441
    0x10603030c03141b06011d0f07050f07050102030a02030115030219031503080319060b03010807140114070b0702060105030c03060411010e0d030f0216030203060a11040f0b071103010c080f 82
    0x205031480c1130010000716420141814aa82d21003401b4014441c42011a0301c409056912407007140b80100b1030f901741e4140c941c550007400c80f0940c1c004aa10002044204801c0b07002a50900c0214031807400340c0c50050300ca506200407010709400c1c0c01c40000405006111541d4041c854076820340d0ba542150400040317541d03000203440805601c81e40060b20815020003007086800300b0210001404103144001c0281c01d85610320000d15000a0003044859440300c28244490003007810344006050f01414404241606c0301c4040906600c80c900454800307044070103120301c41d034041103010301400d8210060101c00c903403a80429910324008101a003000c0e4500304202059000381480c1d1000c2102800340d42642c0b16609015024084000400780103100d00e020440104921020742c10a8941c010701500d61612100103140150010b0300c4626101c0f00d040100040c81ca4420740740324010008140000d40703410550800020b0070b00140a454066414144640040e5034851011580b160040e40d0707811a50719442d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 50841928 1250 50840678 50840717
    0x10f1103060909011b0309020901122a0b0c010f0b2205040f02040e070305070806011802030703110c010606170405070302060708090907110606100f050d14040c0302010809010603030c03 81
    0x500855900510168405c01c800e5264112049541c0242c40862480c0d036203880c44032900074110340103005508404801242d000440c0710390100c1c000e05400c07200c0e0302a294211a80a5030180c2c0c42e080160307541d074411a80102c2d003800f80e0880f41404a0300d009008012001c0605100da04800c0c2c0031040d5681c070009000c00440200e941e20f051f030040c00401c170000d00760712110341d1208103000c07e81d86c034800e440d800100f2400000340790b8140d500d5108107a907101c0021540001940000d04001c041c1500e501e6600c2090500c01c001d802004003200002c20664a08200a440e41e0800c500c00e40d40b425004040101260b000950b8004880c0e040d900325a41d400c143c10b0440c0d0307501030b1210341d50b448041ca00900402550000c003019010284005560365522640204070072100c4a07440000442c14034000107403214040d201805100407902e1000c145444115040d61050078211030403103030010940028401e55034030060644c2c0c03040c881402001060709544001d40790b44102c0d4401005c002907811a1641c80044 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 50843178 1250 50841928 50841941
    0x1505040803030408040e0c160b06010c14070915051005070203030d0f05040605090a0302072102030a080a0e010c1e060902040f0903080a180b04020402121305010f110306090901 77
    0x300c9041e292641480d1412a400364000d119000c100c01d0b1490114a11001040459200001d8403524200b40d01081d82d0b032401c200c7d0300030029818091030baa61100828064000c00c1c40d020028000341c0349550604800d08100c0317a910100c0c0c103800c1440c050a20184d100c80803040107401050a18035203650061000a00e144241d04d00d440840381054021191402d00760403507802103200e01710038401540c03410915640d401301d011002e001039208038020400d80074a40030460b4020b20b50b880981e042411074000c2460411311003012101440002120015254001c404100300002441c150014080545503240690391041440d0002c1c081d2064990410141c0d9220284170755024000340014441c85d4000c2000744080c7c00290040380f400c40c0041c40540481c811841800da020314040180d8000380c5664040403c010001c0340c1003a405c0180b01102c090f0502d015205000444036007140401c1c80c17070180d003902c5108030000a40e03400c240c0c955a0321550401a6640104180c1d180c4440340d0300d07040b036103000d46070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 50844428 1250 50843178 50843189
    0x6040b1f03151b02030903070501031a0f010318051606080c030c0c07170604050105060405010b0414030f0304031209080105040b01061101090204060b070201080f0714031801050106050c16080601150504 88
    0x28408580d20343d43d00800901040d48080b003d4a4070b0b20358820054050b540c2d662000881e01018a405682a1805400b003060b060810b150008001c3300d400100e01035415101c800760b6441d8003402e00401c50392000100a0080d1040e40340464450034a980080360754000500601e00314800070030b9a41c00308200300580341c002c000f0604030b03111040c0180d00c000d4075a41b0544082c0c54070b508280004a0718109405a24101e5141d0034005142c2882d00c0316803602464110714981d81070140000000c0c070110200f0250000e14002c0c520720790076480320a0082c200380c0fa103901c1003001d039041c6401c000124940402181c11100707142403000b803180d990030055004118405009500ca45098000724000d200c66002d06801d6100303803075080254a4800145006440448000c40012852030304c2a190384040300140d034001c100c91030354000d220200c07102c0a0964601760400000940701240b003000da01c90411140c3d240c4070780751000e03103207081c240103180b0344440d814000c15424002103045486501d1145080703400406 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 50845678 1250 50844428 50844461
    0xd09080406030606030b01030504120e010504090203010b030f070c0210030902061b0d09060c0c060c14060703050411041808030613060906050f0105031501030902060c0f06040b1f0315 80
    0x58440d9070290042645026a40c00030b032410300c0d8000c20794040c0c89082c0c00303650448020400c44c2c1c207802e01261003408030310301141046024000054825103500245000c0c05154882503140c2c64081511038420707000a10751403c01c8001443c110240c2c07505151501c2c100c4103468040766440710b45c0003007800b5200d03c290050f20703000e03407415410040c000030420141c030140c6035444400f11607980004445000b4901e4020b004100032000410240e03010300803207440544105003440068100321400360903e80100d88040102c0d0f11842040200241e000440349030450444040010341da0001000d58502010300004000c0440040401d07856900d0110076188549000810720041e030b201c42d8220b000d000584601d40c0503a6030354003036002543c000c1043d248103d005041c0f80d00f902d0070705401180a0010840140d0b0072103020000103d2502c41449221405400340380249001d04051034040900e07030004041500b02054110f21a841400c43c00441003101d4202c00301564918110b500c0c07038010940109406100e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 50846928 1250 50845678 50845687
    0x3110d050f01290102070b030703060305070b040618030515090c121b0904120f03020d1103070915090905060307050d030210060b090603010510020a0c0603020d0e210d0908 75
    0x40ca0305400016003070300d42d03030680ca00842e4100020760303c140c02001401d0240e00300300400c0c06240344904c013440e400740c01c900e00400c0c0c407a40c9468107424400c10782c020b1700741c0c00000901800580e4024090180c41c07403c03000c0c10341d41289181c4640d600c07201c0c041c107000501e0b20044c0120351406400c00c5115407901000b840b034102e500313500c5a0300381c1c1e17003040200300b20030090481070700d9140d4178064010510503500301702440e5841d54010707000c582e907151041e00318051541c2480200e000114505c140300200300d01a4200d80e0780d050006010303101850603407100b40459507004040050581c050710401c21582041000f0480391100d0000900340380e820b80000f0f801048940c280801d140d8006801040c243c0502803c04c11542c40d258140d045110710f28819800c8201040108894106540c0d080300c0c9181c1407050b50504086942c45c5170049036554400d00000b500421080b03000c0c0e515108400604c001d0303270004c1402c0080f45004001c20301c14480381c95a1040701140045220115400400302d260b48900d40c150b45 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 50848178 1250 50846928 50846953
    0x9060a210603060b06030702060601080916060e0102012d0f06170309091005010206040201050c010207061a0f041506110307080d050a18020306010b1e070501020c0d0503040c03110d05 80
    0x51000784410f843c003d052030300c600030b603040085c1124080c2070607501424680d56a6001915150001360040c580340c8074030040c90504bd000c1e0203452000d41443c0c0e40e00500c2564180009080d0f07000307008681e41ca12102c0143c105c1c00380401d00480202009810085048900d0845103401000c0c0c85c0e00036183c00b800300c0e094000b81c1901100070300c8050800c4481820f591181d90441c05100e055016050260b40300002107005907004e40050135444100034005464150280e9891040c5e600724100f181002800c0b0700c100f071445c5000d40f10300142010030740c1c00f080f0f107104580d00030740545503d110350020b220524440315880d40c0b0600441e05031503003003040c1c90382d9400b801189800800c0111a00d00380c00e840c03c40b940c845125120381105002d038004006000f164241030442165078000d0407120b503034030541c00b82c4181890200c0050000b03a4040e8000617103403800380e045181080407600400b0200201002003100252101d00800c003529042000b0b030386240389820102d030000c4405800507009100d6000c107400b9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 50849428 1250 50848178 50848181
    0x40204030503130906210b040204110a031a1014090a0503070e0105090604020f0901031104051207091505010f0c0503070206030a02130f050105070602130f080706020d0f0509060a21 79
    0x316000808100403545d918126911b940140583c450345c1e0364090114100440e1900140f2034220340003c00c00941400000076000050703218401400110740c45040f0030503080041c110705251080e058a1100703026100400041c001d540c100e1410032840404500c074412a110040320001400c0054115000b249c0c440b800308918101c00d00c9800d104444110005000d0304080c02901c00306241e1511041c108141300f40150060420003070802c0041000744800501c5940d906508185240c0440141c0b615500b001c411b0400c1e82e9130365030400130440c158501040680d90025418007070b5003039803030000d030141064031b003031811446007401c060343c0000080140b24100c1401d0f4001e000e43c10000c60b1a90b1420b0341c4054900c4503007514495a404250240b1000f8046403480e002015054082c4441e24815611035200e07000d103001a410001040d480000e0900c4240d80401150b1070326022800d0a0f04a0049071034020700500c160001140a0103012545005090103201c4140850b0118901e055058202da0038000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 50850678 1250 50849428 50849467
    0x603040510050601020a080d0c0e0312070501230f0c040816061b0305030c0c0f01020301030501020a0f030902030d11010b12160b030c0d0e0325060b06090a03060b040204030503 77
    0x352140c40d01e00860f03020341c0005003800d03156038020000da041602c131041c403400601215030038505020448000d520700d41d8003481840801000400ea954595980342819421035690081c0310001e0f100c00c0841c0b0f5410150030403410740c041a825081881e55440804d80308650003a9800315030503214840c03411103034608004000095072069902c0000032040108030085201d41c1002c0039010401c2003000c02c02d41080440100315120007041200c848103000c841050899000341e1080d2041c0e54081040c03500720380d00c4004000ba40754540703010f001801003130700000d80312103c0700002d8007030060030407518002c09020341140401080081107080d010340c0301c1000e02d440d10101c0e41101c2d03c4103103c1901251004109050303900500b41e023034225042081c5007200701c0007040661061541880306002c1c11945c00780c03101d24021100c844008024203400c036480c0000645140b2a690342c410007080c000380100340ca031404108101c0750003140105808000e0301c04038000744102e0700090114040000d00c100c0c075000418510 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 50851928 1250 50850678 50850703
    0x60a0f20070f1a06100203072a05181e0f060103020d090b040b06030f01020a0206180a050607030605030606040614010e0a050604090905060f070c1b0f0e06030609060c07140c06030405 80
    0x450701710000f14100d840344111a0002c10402c41c0c0c0504081d041060b491003520303c1c440340c0010849940b82d00019140400c0f03c2e0000c0c1190752801c04000d5001d19003100d20100200d140e81ca51f120b401d01e048019070000d8021300603030406502040c0998411040d410103068540c000c0360304103503801c190038180880c800403240f1034003d124020011142d03000c140300701c0e80945800c1d8081d2086481c2c2c1140000d5410040c0005a040d10a81d1480c80c0414818024075015004075100002c2c141c1c40c1c00b050606215008100390720a030b10b40b50082005155002030103541d0407092030f107000003455a00001d8a00079550704590b411010200300030504e42410f42c416212540079204550540da40d822000d00440c03000c0f82e414000031822150003000a000401d0140140e80e0701c542200d41c551210f16040ba040c1e00d50b4400c01c000c02039142400070700d0a042c0072035a0000030000145c1854501280e0510242c420400b008004580ca83c9a059021b10180900301503440000c00e099500d04203410714030340e511203003101c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 50853178 1250 50851928 50851939
    0x5070c05010e030315090a0e160305010c03061505030a06031509200109030803090f06100e060906010915050912010e120406021b01030914060a0f20070f1a06 69
    0x440c0d460ba400042600d2145044504c00800f1700c08035410b0040025001d00003c0f46907441d10501d4034a4802800001107050300d2291a0004a140d03007001c40c04e407001c1403040b80034140380c0002400040f401c5400c00b0441c1d241414a9560fa40341d200d170754030091090740e001900328a00c0c50481103260b41c1540003103021074091151035040d48201440b4200d50701615242c0750100791501001c20000d160040a5548034000714159282d01c1207142e0102c2c01c201d8111a13411420800c60000d008140102d610140c2212003595820510300d010070001c0c00c003210074001c1e0200d4003035502d07030b00019034450400c0f00e5900f40064805403030254103441d05400f03049449200d000314091000740d03059401011303040d00c1c2242c12a0f40181702d07181002040c040d010804d010824101074588a42c0c60200d1000041003600c0c28a0100508161031702e1900a800c03542d0301103034040300a04010250f03003090000d040c0f5440940c0440c1070359a850f08240380850f03528a8010006003001c641810083c0b803c1f02c04580d69204010a460 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 50854428 1250 50853178 50853191
    0x51b01030609020f0403020108191103040209070206070c0219031502090307050108040503031306090503131502071404020a05070b0a0b27070e01050c0106080106090b0a0e0406091505070c0501 84
    0x440c0b10580c040c0d18a0010406000d1004202540c45260130940019126034018402008001190103075035031488407101e000000402e010842c28011000c55002c05984050181824010f00040c1148100c40b8068816090b02e00c2800440c0a0050303028001c40d030101d9040721743d0700c0103500748000c4d40011034010f00c64007a24200003850750061020070b100d107602102031440d6507500b000860b0b0503007036010280c4d6110359400c480d01c0010010401450780c582c03103800144019292009844180c281d5080300d00441d00200800c1000d03040c0b0300c0b08441e00720001c0b5405a01c0d4103c25408444074042c800000e059078000d2824007506a4596110340c0c0c15940940f9860001215143d20418134040e00405503070007104600010000b80c8201010880460140340062400000454184c207580054001d89032a9560ba102088031040e40e20665108281c1030705c00c117560602e0801c1d01110100d001b000581034a4903859203e040110018081e117241c81d00c03800420482c100340d07400500d03045d8100c00c11038143d842d122 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 50855678 1250 50854428 50854439
    0x506040e061b0d020706061403070609080304270903091d04020f220e0309030705030a050607080a060f030605010501080f06130b0103020903071413020f0406030207050a051b010306 79
    0x8505110301180881c44070090240d42c0700080c103601501e4191002076007800f0040000c0ca40c0d0060070010030b08d0505681b030116101007014207045144c6d00200c00c0c4032800c4002c21009401109460480b00807500103c3e625008050510410301c1c190000d4001c0352130581c00380205604075000806440f054488000070504d00b1a81505100c01070b580a944038101c00041406031501342d40c6281c06c0340703041c202401a080440400f0041d20309021001d41c2503000030800c41070508080080c480200003c4004010641e072f00e1711415124078016119604201002c0005000110203810800c000c243c510000c02e0b2940e0f89052800040c44280145070004090602081811002ea401a405400010003403010071a1010700c140080c40114086410302d602803241c0700c041c0e94103000e1a00103084c005902516038160b40104000341c2440341148120507c14024541d10b881e141050750140c0f5100c0c18016580d01160520500e800f074501e41c0140548250012090030364540000b29038104000c0c0c0f401c2c040151200f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 50856928 1250 50855678 50855683
    0x90d030203060a090c050c0d030e0c0405220f05030304060207030e0108061806010201090b0f061002060f010303031a03010222050d03020309040f06080304080318060721031104090506040e 82
    0x40e070318541e00c4101c4000511100300ea07a80711704d81e1805a800c00e5482c00c415004001d040ca054803030090007090756005a091044030600c054500c03c2c80441c0e0070821880d04002c410000e50318541c210115948404071201041048020314021981050880787c80386402c0c42e1400286d882100c040700018107090303440c82c69500804003503005510003004440500c00003c1101c1182e40c005240350704645d00e603c400300c04204954080342c0240d400081049961411005001002c03041d91521401c5501900c100407030740d501e41c428141034a5040c03030042409e820340f180f00011a041d00704019815440010b07514071094084012100c2592101c0d283d0520079a50310811898030f00e448405000b50f001002903030720f1460964861b06810700c141800088a9450300310407841c682207900407590a42c000200441a20b00d004885610b14504855103840d101c07059a5540755002c06400d00010300130780c140b0b1070000900a4012140039030410f0712160304c071a650401c0390082c00051741d5031401949060000c03800c001e0003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 50858178 1250 50856928 50856931
    0x705090105090402010c05160602010b1002070e0f0403020a0206030a02030703140c071e0c0305060a2406030504050a0803070e0108090708060c030405070e04060504030e030106081902040e15090d030203 88
    0x42074480759035030f01d40045d80c240510324030842d298001c2c50401c251049003408140f02518099000090f84500e100070f1100140b0118103e03015035100e140e0401c500001c10303514580c030110942c4c0640c99529149016460001c0e17111000b0762002000c400c000700296141d001d144540004d5a041c0003005100403400040d6206454a0300705032410404407011410010400140501f000038141c1c0032885c68841c2803100390103410445007900707e40140602c2d12140d008079440c41070000006c94082d0940055106803044d40d1049105060311400000e080c82000d001c03810350b07690040d00059580c41c05140050080c181c01e6181070100f181a40807644140001030002d0a454040c0c006000a0315001d10002141e00000d20072961885000c0e000b050080641c21001d014502c905008903040c01c2c039140142c83c50180c42c084e640aa07140820401500c5000541410b011200700030a030203080c00d5001180103001094903409403441000c00701028602d520406600ca656450166a420b0040f1503040701603220 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 50859428 1250 50858178 50858189
    0x1e0e151603020c0f12120c03150f060d06080106061101020c07031b0f09020a030518070e1902120601110d02060c09010c12020d0f0311070b060a0308030103050a0507050901 75
    0x310348110029503802640149101001c0720100c07444074600107460740c078016000503031200c038034400b00307203a40d1244d900b14030030b81c00400221001d400d614080c480a081550b250182c14411542c443d92801d42d522100300301c3d034018090030001c1c0900c589480320940601007612589001840c1c271020920789060600c2681c0c4403030001d601802d0118507546500240d076806034a100507072240c900c40081c11102c900c401d0802840034000141c0c6601c802500a011183c0040c050078041510360440b10f5800c20110f141d0082e60303d0b417244c28005841c7c420303030110b0030340a401c1000c00c000d10020f4024203111500840ca0710410003607842c00f0079050900e40c0181c480c06540d04100169000f5004510441b140002600c3c038401c1c18501050114095118010201e800400c9400540c00140c551150280e004445003941c40b1035042c20b216960b2010500da0306d0703100710310010380a2400c5001041650395060128801150010000742d140d585074180305443e0a038960048910744618840010141003a40c600d030304035030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 50860678 1250 50859428 50859451
    0x50f03030406052d030906070212030105030604060507020106090e0f0111040f030f11060d090302060a061505030a150e10080c0105120a0608010c0e151801050d1e0e15 73
    0x44d0410034010080940007040b4024020549183ca00120524055407180504000901c581d0814101c040d0031f200c0c0a1044074200d9104100502850318000780031500300c3ea22080005a03992001c0e0124014440d03a040a0500d50820b060070104140000700764001000c07007002000440c40e40340e4505024417884c07051100b8030030744c00001c10108001e40300b0328000501401d1180600328000c400104c3c1079001e034003601034440da105480024035504000d50b07540904807100402c200c509001d503030041019100c00d000100704c0b001001441098880d040950aa144984d031a9402521a1242240500111501c0c400240c0c0c60ba800030741481c00050b2070314080d0041e101e051802c4070300310060b2040000100046030b00354a0b02c0002075a1402449403001528243c0c1d9442c100c982000108200d81d03181280d020b0380f59500740030040340e00401c02d9220000d50801d0800c0c40c4c1e10082c031003544000d4200210301c00074902c8600810412012030740c01841d8880f401c035090311041c40c400c2c41c25a00303400d000d40e04000c40c0c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 50861928 1250 50860678 50860687
    0x50405070c12020111270f01020c04180b3c040803072102030a0c111c0c0605010603060303090603090308061509120f0706020a080910050c01090507050f0303040605 72
    0xd0400b03815240b581d03190310002c600c0c0d030103d505a100030782c82800394040c0d0b040f40b00d01021840a510007649100b280031910403503130454480000b035850103403003061407065076203420b04501181c0190032034075525400209245a031a0a0f81c0300c85004481010804d140c05440d800d000c4109130300345c103d15a5a002d414004070340d46594030f643c11a500002c091000340710f801415030b821343d04900c07680942c2c01200840541d0b00c2c03031700442c1c400c00d9881e010382d160180410015032303444262010400640d080800903160011500c1440200c801c4008c1000c00380409141800115426915401180c15680a511021550b40d81e4000072070440703250707480141c005070007940420382e2841c02e00705407213020400207502030420114100045008400d401d481c074551b4408180286001c009020b070310700410181c009003107a43c1c55500e42042c2480352081c032078030a08101842c1288580a081036400e503405500080041d010507150060343c60403540034951085840080042203442d000040350260781055403500e081c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 50863178 1250 50861928 50861933
    0x20c060708180a1806050102010c1812020103090c0e0105150703051b010609110424050d050702031204030c060f050601050a050d0603060c051914180a030b011e050405070c 75
    0x81e080e1000d10b5641c840c42500d00010b4280010a5001070b83c8054180000c0192401002a08440b48810080240b0020401701800c40d58041024021a445001d00c801c5c07031800ca00c0124024550800014026030709803030003041d6508108003482c1a40c00944172202081c1083c0c1c101c18040c090540000d000075010441c050300b24940404810080094000102c0d959440d000c2050130344404580c844540c0001041c20403071a403040302002a810305601110036403501d0140010014426041000402c0d9200c2d800300e040a803080041314048000b884d60010396040a140040840b034034000c00303031982400c1c030068208086e0188112130080b081611034a1802e290f110342500c9580090104010707035a50340c03000102198040c000d54ad0160340d0740d5503ca03035a5207000c9100d2040c003169501c020400512002d450403200d019821a41088021340030506600d090100140c0401c403241c10013085403d001000185030690301d0340b82c41d5031504510814203c140c81c1c50a100450b6802c40300c910024002031340902c00b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 50864428 1250 50863178 50863207
    0x110319030b010c05030309100b040e0604030c030c080307120510050306060d03020a06050903040501140c03040e09010e01090303020a0e0f0306040f0309080615040501050405060109091d100903020c060708 89
    0x880071010b040400d0804040e441d4079040d600200e445200ba0742180320710307000800a034441c00c20b0001c8119000c000c41c0003c8004d43c2d5881000a00003418009004401c00c140341c01043c1c0602c8013648550540c2c1d032440c10120003040301285c035041d210300c2410034020503507900b100c909040580b48040c00800882d66500c0070070440e0f043e40407042d02035010b4494200301180c00350049030b20030a0742e98002c6a4a40c03070311000400d0350f40117121183c2e6008060000181110700401128100c0e04040c148400e9130321800007a030300500443c401c08000b07602c0c0070104002c01d5010f40140c02200450307150201c9150280c02401001d002040b040c5503d600900001800a408296494000d5000b4030b85160308684445075203180c181d0a0350f032024070250080b5000380c00e20b052702071035000d00340c295024092030502c400082d0110f45980941e11082e0340b0b400980070801d00d0650030003101a45241202c0826043c160031200130301080030254014041c410b040342c1203080100407a09416840a40903103840d104222031031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 50865678 1250 50864428 50864441
    0x512010b210c130e04020307120506010506070206090303161506080303040605100f0807050a09060b0304030c021302040605031008010204120b130803040506150f0f060706060b03090a0311031903 85
    0xb90120030620030f55103103450a2030f0080140011521481481c10503004141c901038031584000081d0032101c2d1070030f00254001c034500341140d4003607400a403294040d100041c02c0b8002e854840e03416103c080707130501c281076640b9100ea0955000d00410b52100e040e21660000b81d521500440c4a035034010004100040ca0f50fa000710f901c1908000300d40c5600e070302d8001810142c0056480340c00f05074080317103041c0464600080c4140c000c04088504018a52400a0003000e03808000c2000d400d1152458418080d500c3e082e440001908009800315602c030344404000e0020303041070f15084038070444118042410b08051084605803a00000c0d070041e03404c0190b55404051100825001c0d4005028681d0800201118003031070159220320003074011840c00d0f06403580c1020790100840e00c5403400c2c024a1660b6250080000c3d03c080083c0d40c2d807a511013490401c1009000c142d071103141d84100010411400e003c0108040350303010b120b543c9860f02c1151820319103540b030007065007041e03044000301001031000313009070b1180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 50866928 1250 50865678 50865691
    0x2915040b03190f050601030b04030f02010c0903020607020a0b030c04090e0309010206010b0c03090901120302061501050a030c021c02070302030d050403080301050f030a02030604080406020d021606080c0d06060512010b21 96
    0x18000e2150995513641401c00c282d00c202c400040d00700c1800700305904100340020080451000b00085242c484000380058054400a80921000543c3f2015903c8150140303018040d008813007507407402c0820744441d0682c014402c2010551070880c0c0204001e50200460b0040141607009115590800c640000c82e44d00580f00031100d031104001144c299103d101e151802005400c0740700000c41a1405c010b400d1580040603ea00242d100110320a140e0300071080e1041d070780e0146030005030b58100c020160710f403810b50144601c0d540e50068102c2e50305070b800900201600c0c406c0e41500d40041e505201130300c0354015400300401d402018001800f8504009107050041070300101250326560752034000c00c2c20204c0603a030544001c10006014040a50108440040c0c0c4400d03200501203489880c88d01d001c00e60050196034208030b20000401c2c02e0a8200c801d0f01c20124a0754010041140c0e41e90014046600003034110f106880c101000003904580710040e544c180f00c07041c014040d4003021a4170101c5420000f02007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 50868178 1250 50866928 50866943
    0x9100513060504030906120209100e030f01060b07031808071e27050705040303020a02041503051510060309020303072604030804090e060c0a0c2915040b0319 69
    0x400300414402e00410740194007944400341c0c450f0600030002d2240c0090704081c10a00e004000024443e11a42c0421320305401030310b440c80d80410b50700d00107404c20407405400c03034035903003800800301d00b001c8510001c080340c91180d140d580e1020180c14100c280012144503100e800d8000600c10010381c05d4002e4001c0903400b800d50700d10f500e1754403615890101811200d01c1001804610b00c0524080c010b8843d19030090040d0908500b401c0c51072340c00035074850039007000900840d201c000b1980300f685419a107030040c41e840700903556901514800c8a00005081b40e52500c14040188001652406440342d0111150050091450540c039a111560711401d496541006000c20009640070103031032030041c10195100d105010b90f2185004000d4040c0e401e14103680900c1d1b004042807019007589802210421041c504005000d41c03ca4100003007400d4200003070100104040a00060500c41070040710703c00d40c0d040c0000c4403002039010500003111508030070a501644102e6801c45588015103040064034400d000e0f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 50869428 1250 50868178 50868211
    0x31e15040506040b0c07060f05090106140f0f0307090509030705250b0a090e010906091406010c120c0f060e0f0601030b070509190b0316050304050c1e1905010207050306091005 77
    0xc500023201e01020220503919551010300205c40e1081c0605401040c0f4202100406240c038400a050a400740200901c02c226800d04048107480500150b8000c0480200802c504d14041c408552030742c2c00107100300c5680c000c0410036001c8c030021210350f04422102909160807141002c41c0641c180d40000f1801060144081000880455000e11240038049188022030007078070708490002500c0e46086036161003d100703020401c481e40d001da0350303040290b044864443d402c040c5400560307030050620006000b1410030545d04050204a80101d00441040c604540030120b21202081e101e0100780001001c0c40b130b112011600044c840c10240c09000d50090842c00d803040416240e00540b0029030005055100100c1041400100582d484a1300c441d03e04046242d45002d0f0742d1a40c5500302c5003010391081503013401c000000c1500343c03c02003d82c20040c09a2010450b5010f8424154030180b20f002d0040c400c0000214003803c010592078052a031100081032070740140210640500002072201d141c0c626400c3c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 50870678 1250 50869428 50869433
    0x307031d0705150c03090613030605070315060c020f01050307031103040b090f070807090207060207020d060f0f0207021c020f060409051006030603080a0c0c05031e15040506040b0c07 80
    0x40600d4552080300041c034840b807a05041c00649441d0894011a01c81c080c4405001c0701d0b000300880b5207811003140c0c200d656001c031400301c01c1d1700b111581015001c645400b040002c040d4040c4c0c0f00702040f0070001d05040d0100e6581780100da00f1307030340207900940103030010500c50007550040e406103410101a050115019450a820524507001140c096643e00d0100702480720081c000d1040d1113140ea240c40c05403490a050001d165950462403240c2040c05a00040c40f0040c0807481d415151103543c02060302c803010900c0d040140290030080e403284902d602c1d102108403152010302c00c07580140d0f4054000407844900192800c3e00c00c40c42c071420780c0c1000403046065403642d00c11000700040c2000c20300c002a00e080040f40108451800c0c2c02644c00d0605e00300090001c80d49910544d403043c4c1084c501465822402d103880d030500c0000e94000d41c0c061182185e082c0044502c800000c045441c4a41116039560f0105014000c0310700945010380542c0042d8007082c041030418036102d40c8440b1490718249080a540d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 50871928 1250 50870678 50870711
    0xb0639030703021b09040512071104020c030a030b03012d0e0a0c03060b060412061503020301060f06020c090c041203050c030315121c05090f040c02031e041802030703 73
    0x102080b001a00442d09448050307007010071114900070203403a1143c01d45400d0360707441d5a5a014015088444c0c03004100101005000c08482c104603102810954541040c852070555030340240d448100403c1c24082c18085c3c900341407140d03917100c548040058000301500d41c90507003801c00c00c1040c0d860719901c0341041c40940a04100104596110350521180245182410310403a4100248140305450410080002c007144222080d40c0c29000000040c2c001d00400c900703206428103500094040d401d02000151448032003000b0703400c6034816003e0b10100d2003241c1c01c101c180c3c0310490310700310303011070510090000c01040c41c41810064442e0501d50f140081c9500c6c2d02d850b40d0800c8541846c92a01540a5942410301500107084050300c10010013900030681c0802546c0148010341000b0487c0c007142c0c800b0300c1d903a00310882d00360740310140080114030844035000751a607004200c2c440c40c11180c01c0702e171199a100d00046508803040074200030500c03000521354034040d600151084040689401040c2802000e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 50873178 1250 50871928 50871937
    0xd110309100e18040b0613140109061401180308031909120f08040c051012050f010e010f080607050315061801021605012a0b07020d030b063903 63
    0x161196281c01c0160b00c10007182d40107511034000e100d403070302040c840000c140c100c1103a00038108844041144c1c1100d41c90000408211601950f1900408000989601a9031204003542c42200d06414000c1c085401980c003508a240320805009202100f000400c0e1000c1c00703550800480009001e0182c1c0b1f081d00c80041e1840758400b036403403650380110816500c0d0000000c422031845c5042c41c2071285031030f80b129030101c80c103481030501550004401303c40852241019000026048a0410990074040d1941c0c0c00e4201c01d019650100f602c10002040c52003501c0c2906080341c45200082c0000d5135080f8084502d41c1020f40402c290fa648070383d00c070302c2c1030390360070058050071080380c00c03c000d402640c800080c50b00c014070341c5024003090100800d10959074030031070160301e40b04003c00c404140029002c00305181c071204c40f005401d4030076110500c2a10342e400705020282280643c0c0c28491403440d0001c210081c8155046e0b68941302c410440088031b0010444088012280043c2642d08001085517107400c6910 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 50874428 1250 50873178 50873209
    0x60f040e01090b04061a030a09030302090d03090e0105010c050601090e070308070f03090501030b0a032003030c060103030e09010f05040504050f0706020d1404050f060f2101050108070305090d110309 87
    0x1c407140140d0f0b582c140f038490040201001864641c003250300042207180d600c00908100c1d02540c442451b13105050181d0115103400328040d009407059166800c1c0100400f0007402414429a880400062a588100700380c0f41150b8000015141ca079103009180c00c0101000701c4400b5072030181318400400b09208102414407540200340e40c44481c080c81c540100b51070301da07411481c10f141c80c0c81154070341512059100300c2504d911a03d04000c445140c2c0302d501c024000303100c50541c9448000384208000310041400703412070307209483e940c0e2800f80000411a210b4424000c9603030700213101c001000343e45456081950024001c4085c0c0c0c4152808070b0b569800d03c0155003040f005030f404500380a512a07403008000d0800d16a05480e01c4c200b600707210001e101050300d00c0c01c0c01e106840214441c1d0a805100c0100c0310100342a102010703d00304511429400241309100351404100c8078030001c2d604c07501074010310f8441c3e0b1128010300000d032165682596810f100101402403071200348086042c3c2d0301c0e403030b20000c41d00a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 50875678 1250 50874428 50874431
    0x2503110a05121e1807050a0611151902090f1504080d080c160f050d020f07090b0907050f0408010501261912030e01020c0703120c080403020108130203060f04020111011a060f040e0109 80
    0x410300085443c010700c07080c0342b00304041c81204004000310400d4424411414900c07000da5600c00150018108a0400c070115a011184001404039621030740000c0c0111080d20087c1c49594100f00d4007511200011a4414400c0a08008490b040f021030f400306800d191080201440c240d545880321481c010260344c20402603484a0f03015240c409041000c640280718980060243c2501c440c04621b101c4c01c017811400c240100417941d504042140c00694029210100082280b0360355495440b5800d0249240d000100040803200100c410340480c010b01c0203440c3c07020301c0f4201200380c1d5640d03d241c1c415165020030181d030752901c0a03e1090030300041c200c00000b031000740740080c1036003444001081e80308041c0060202c0c0c0403504000800300d80954040b2602402c00c1c008903520240031800d4035109030802075150003004108402000f0052a0300e008900030798581004075030404100d4201d900340d00030900b0280c207a40c08010180b400400070404680300003c51410582e40701102e001021081c4c1000e8a4507 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 50876928 1250 50875678 50875697
    0x60308210108120414030c0d050703021c02030d0e0f061b0708070e0106050a0512040803070e030609070e130f0305030405060a02032503110a05121e1807050a06 70
    0x21006030624003406a80700034080100c580c2c1042c1c000340c03140f4410320000303030411001c6010703950301032004a203060310140241c245c180c10303440e0030364840d40507003c201c5c4110382143e04450590f6886030b41c080407a9010b801411203401080d005c2d9481d000716003400d5440072140c92002d420b500c43d4800341002e5074041901e12801448181c04909001c22500b01c2403c50707102000403c40d0070348248500e0b04603651400c0281e0360300d070f0b821003c035514452203104a4402e88100c05110802c1060402144203200c40e07610384804c0c510003070815071107510542c0d481c00300ea4051041030040040c0c00480c1608105c0442110100c049103640f0104075407200c94082d008510040100010b00405100e59580040303c002d08600d90702c1c0c006089114810a0808e804201c2c018102a94042d40241e1100b451448031442d1a915a0303480f61000f8002c0d8440b4548034100b0380301d41c0120741c0e1000e80b00355496001030f510001405a070717030310b902d4110040300b2000b80c0205803040e000001003607180d0b5840d52010300071603956620745 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 50878178 1250 50876928 50876977
    0xf03090221010c090b0f1b120301030c050310060f062010050103031d03060c0f0724060603020304020310090206130e1006080f06060315150403030207080a0b010e0a060308 75
    0x113580c030ba41c090148000200410052030614504540c2a400480b01e0042200c070300304401480d0a148500000c09183c00200101c14001040d91801c05c81d501103045404581803d1070b14800d5920034805c1c42c24541c0010070901490f8051500348414404038003001780c400b40315907140391609031409040700c0c034541da40300180203155001d803000d4001d40b0f0104c0d443c0844007164000c280e403090024926201401d01048009098a6800450b04c0c52500325910442d2500c4400c80d031031540c0428545040f0652400360000350450003070080d60b101e00e800901804032a8860000040503101200c0226801a020000c2c2c201d56000000804050070f600318411950f031800c1500040c1028990300800c2c14031103600200403250010290856000e5130989140c0d4407a00ca1402100d000428441040ea00400000081035104101005030040300d009508941c1a290380c0c0c030303c031602c82c5008000503241d2100c500c014820780310311144594208012001c00960340e0b699458100d425080f01d0402403400c1c81d100c501d92103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 50879428 1250 50878178 50878187
    0xf0602011107050d0f0c05010207050619060e0105040c1403010f060e0603060f010c030e0423070509010203030c0906040509040803061002031c0b031c0f0914010f03090221010c 77
    0x890384401c1c0c41949851941c2d00d42c0c0742d0302c0c0d035104035040422400f01e400340e1440b8402c603001710040d41d01200941d216400c40c0b801a890b48400c60345841028820144801d20124602802c0201d8031341d21a030100d80c0e420801404047c04082e50500c1c2401a02040d280161184000450007411400740d020290341c10301d44020200410354820600c03800d014814412143e60342c080362070040318242481d48420003185800d9800340c0d0407a0010744d200e0f2402c13414600ea10404010b0071440303e0b6400103500142d4414070284c4190041580c40d80c016030041c40081d4031050998000c000e041c0c0006d05580c00e05a5807c00031b041114101c4084681900c003200f4804141840c151440300120b090002e94100700c0c04a11200c504030f8400c0c5081c001c580c881600e80c600b0348083c8103c0c031101c2103800407150305c2d1404000c0640400072114600c0c0000e030050b5000140e02c000759501104960f0140d42d0b08101d40b1114004030007410300400182c3e4000c0c5802041c0c034403644896248941d0200460002c1021158101c0150 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 50880678 1250 50879428 50879441
    0x304080607030e120a030207060905010e100e03040806060d050703120e040b040b09060f150a02010c0f0c030e01081f140307090504020603011a1603030f05070507050706030209040207020301060f060201 88
    0x403070380c0700702c45560502006805580d0545121b250058480c081c0d0708000d000740c41e0344030018225519049003000c680c0008a0f0501030a130280000b4454500070144090b540c0c800c6104043c1e560304450b01080c80744c588142e114800c039000e4002c40ba6040d40b00e498424131405426042404584003d081e100340d41001d00617114a0b0408480800050302c07000c01051140000600c802d01ca4104480300524a0381ca500d42c02e2695041c1c0d905442d00c0303d6081d14068002c250004d03110001c02c010342940e001c440c0c4a01390109825505542c1c10740c241c10b5040c019111840d0107030004140e01c41400000541c00c6814186400400d0000e00a19001c608402030500740000d0f500203800b6035080404000240c0c0b24002124115491041900e1099051031080070081c0a1441c055041c0d025102841041c1541078000d60300c1c400e52640100321079207940708160b9035445010700c02000c64000f0701c006c001e1113000b80c1c050055070310045e01c00762605000e40d00007030071600590003440100c01c09020a02c6499824480c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 50881928 1250 50880678 50880701
    0x170a020c060117030c031303020f03030403050a021005070f030f0906050903070315060308040f050301050f22031b03080103120203040b04030803090c0d0602091e0f040b060705030408060703 83
    0x210325103110301440e2500c9000502440c0000004000c4070701866100b08105c504012000c03040e81d460780c1d606003408129003001d1100303030300c070324640d8010042c949804801c450031030341d002000380308904880d03091010400a0651030000c1c8202404203a001c1400804010021403090f80c03040443c8200501c00340c105000c941007041080001c0c02101415140003480e042074940140d00038880d400e104c0f004801030442a00000c218010201c3e00040764030009102c107058078011002030106035901d41a80c2c0248100304c0c2c03d80700109903000c101c9045502c103e90400014024944500032224000c10084480382d0791030206c0005210750010410300401c403402080c0c0680300c0c0302440c98285041e504500f2f5010328007001c1d000100003c003080c113605042100490955020300401c95505642c00e041c0b0003900156030b25030150004000d0700e0015880c1c071401c50307440c1c1c2d0000c00010382009a14103100040020242d220b40101040020f0000f150041028000404000c0020304840c649000024150759540b13082 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 50883178 1250 50881928 50881931
    0x60f03060c091a03272e0c050a020f0109020f0d021203030c0d0f050403050f13090501030c18060e1603020702180402190302060a03050a0b0409051b0f0a0306020f07050706170a 77
    0x6217655400b00d000ea50000c140c02588003217008034264401049003010386240501d00e00000d07503001c81e03008130140003080c5850b020344c1c603d502802d05003030a94104540083d8016450341502c1680c1c0391009451a9460000d403010031b030128250002451503109548151840001040070070301e054050249800d2860b148000707108908140e60003501314046c503005030b50388100225460764007900c80c0540c0340040480100074400ea59480c20414440300c1c43e401100c000030b5004603038081540312402490201c501c5101c61419603510781020344600b91180b02920209502004000c001d6a50140481d0828203c041d81366900e060901c1000030a03085103804403a0400e0740300007000903a5035402a20308421303490402141031343d10fa1030031030002c082000c01c4e01c0d4420318200f101c41c00c1c00400219a9a403080603078000e400c07941e50400308204210682c0e40107901101c8403405100043c0c45402803c0401244800c0070b00300300c203582d00e40e030408900d90044000034545000d03002500041c844410b030410102e000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 50884428 1250 50883178 50883241
    0xe16050609090a0203130c03030c020109080c01120209030a05010f060906061e200f0a1b0515090607020604090c0801090c0e151903050f0703060f03060c091a03 70
    0x8542c000c400104036503501c40c3d010002848030483e41314050840c590044282e061544c5901d40a0110804803006a0019240100101e80d20100150f4044d10190503100e1141001c1c880c0741c000040d42c0890308040c3c043c00307458900070010350f00f4003500305507039007020020030001e082c0000c0800b00c443c3c560241b01003080140c075803040f641481e4148040120b15140c00218035200300e4001401000d031400c815514402e40c240b0407642c210121340910001d20440d00000c200100302007032400c0a0040c0281507000180980c1c00d0783c410035120040c1400e0300094101d9007041070a4000505a4200d68442e440403500d034207048040316030002a50380501044003013000144008000180030041c0c0c50700e01c42c0181c4001702041ca02e040d0031401e41d01e006500b46810210a0260300004011b0001174580b644180b40ca003020880031030280c090b0400b41c42c16100c007a001c103880c5031a018050140030102000b17000c40c42a02149520400131444084002004595507a040040c083c50101040d00c40341803072100d4110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 50885678 1250 50884428 50884447
    0x5012301180605101202040e0702010e01060f0b1b010b06030705070c050306010b0d0b010c020411040317030c1c0b06120402090a09050705010e130516020d03110d050a0f0e160506 78
    0x32401c0d800c48854540039190345d0b40c4001400003441503402c001c1100000004002c4400d41c1500075203805103800c03009205050780c0b4001d4000b40c81080c000d80071a14030501a0b14104901103106202d00f0321307008000300b100140f490203c1c0c4d00e980160b4000f0700040c800510f810620601e005e81d080140310542c003c107881c2d0314103541e040d0307030380202c05050000648802d1a06001e078403d030860091990010001c012403910b101003820180c3c8203110880b0262410501c41ca00480708030140ca00c10806a40c20a1810f44940c220ba2040f00c003064020340250f03a10054541c194031b421000d4500180700403440b82c9181098010883e0300d420040c081c0a0f601d04014241c0c00040e80420100100e91017801c002c0140b549034400240c0d0040c40c81e5a100350304e0316040810891502c20019a02c8007056902039403080b8100c02c0048040c2d0348010300040c2491010007008100c200540d10040e03001c40308080c00185100c411110400359109444900d00da40c0c40684141e21903c40100401d005100c2260340c10329240144 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 50886928 1250 50885678 50885689
    0x1081204030201030b041b03050a110304080a1b080d060f3302070515030f070228020609060c060601021204030201140706090b010303050403050c01050c0606090405012301180605 78
    0x1d000003410140c84000201558440c0d82008140c3c071440708440101c8400400d00900a100c121a41496181405032024506400d281240c0c0220780007040140b800c0c0007a03400341c130b110443d200c03100a003010382c030482c03000b00391000042d000310081a02d000c00c28514252400ca94515070b41c100251054000c0c0c000d0300255280c0300d903441400d141c1c0c00110741907500d001c4113909220641c3d105903000308940d24605494080074004500c103456996403040315484880c8101e039114004040000c100c1c10596102d6599031075408041c2c003c510003003840749025444004104190030420310045a076000805011480d078042c000e03942c2c10050140110304251850b000240410101e4038980200e810002e4a1028800d00740c0160010b0381c0c1201d805070741560740c1d14005045a10501c402d850760b0095040e80307009984624112562518100d005114644940301008109000a0003c9900d5903075003004808440c0104c0702c0011082400450f06240d40c540ba602c64900340240cbc01140718a86000c00a000320340d00d5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 50888178 1250 50886928 50886937
    0xf060803070303050a0e03161b29160b0f010e100306020906071205030f0c070b040605070c0b070306050102060c2a0a020a090506040e010b03030901030f0f090507060206010812 77
    0x40c43c0c041140e07183c44010300001c0807510a608524000050084861400441c0070300c40e89200322510140c3c1c500340010b600c01001603020f21140c0b000c0d81020220740004029a050a2580e15444070746800113075000e00c1611128510704842c0c0202c1c0b035040118003c2442003da0041c284144612000d160890a004211005000040459501250007101600e13020103640205030f026000e00c44a9010300c0c03000c0c109800031900c028241e454000010482d95204003074030242c0d64013032040d041d83d40384d42e070303810010301402130400042100d02688840071036107007003a01d8081e0300c40c1d40300010204e007044002410030400804000c0326a504102180b03880c1269801e003180740f40b08108255240031069030441c14070328910342c00383d40101c0001e004a0b252503e5032244c0d0040c1d00441e1304105280325044e01c90b00360340840005c02e078142c1081c040c0101c1940286c0005524115030500010490a604424012904864002d44050788078400a00c5415010003605024240d600003e12020400b403204a50a115 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 50889428 1250 50888178 50888183
    0x301090b0a02180303030c030f01080a030f140715050a0b04090b0105010804140303090309040c020c1e040212010f05040c050c190206190c03031d060f090a05060703020d0f06080307 79
    0x140003810b0f00c01140001c9902c40c00c4003000f82683c1c0d40b8100042c0700000f43e041600c000084000b0180000f1341c110380043c00307009040c3d1540740c10000140701c1d0019107581d4071061210301915001c004000c00901d00d80c42c003030100b01d9500800211820850f5000d0f08840404800a004925001140005c100c0000c00c182c1107a03001d20b08035900e5551880c0c03443d03010700d070300b500d03842c00d440080103006e03940002101034035280c0e0054a0801c110180340c002242e540f00c1661901c2d0304500414207440c1d0b84010070401500504014002520780700000a00f89024a0300745e0050288103181c038000c0c0154035050180c0001d641d0303e89411403c1054540603035488081c542c2c6100c819440040320103046454090640300102101c0200c4101365440c150042c0041a0700070013100082d150000c114025203540b80307140c0c2c3c04d0180c08010301d0680c0e981c00341d520001c40080c06190862141401840000f0020410b2501c14000c99a0168551181510803002c0c2c8e00213401c1c200c0320303500b825010701c004000003094410658 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 50890678 1250 50889428 50889431
    0x90a020903010204080f070302031606050d0b0a120803040501050106051e03090a0204050405010b0310020a020327060406050a11061509070c0501150515130b0a0302040806040f02030c0301090b0a 85
    0x4814002802885245d02c02d07243da0242e14042d50401038041000801c590082c2e00392900e20b40100180034060b2402d001c6c00b008100144404540511203502441400e43c0213400c0c0b203031b070325103c0d120003513079005010003107070390450000411003003040a0154a0061040d810100d062080080c41c029039080503200b6004450070110003c1c14070001000402070954005e00100701600382810300c60b0103405440d000a0091050804501202d02c291080f10380542035a405541041e85900140c070701041540340109180403c0d030758004082c1e0307400300280010030050700e440c0d5640c521310070081d2400001110f141c2e04c03a0080020001d4410001c103c090040301d00316040c220640d110001500c4410a403074014015611340300040305c4a60030080c80c2c50a903182141c1c000d0005076a920f2610f1036105050b40380001e019043d8080000840c24805809854024140517042c01d0312060002d28020007105e040d41c1c5020312203c1e103025400d0600150795010420b070002d20501241e611180040b850150000e1000d6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 50891928 1250 50890678 50890687
    0x32405090a111306030b03060c18270f070c020d110d170d0b030a020a1401050409152c0106180f08030a0f0c030806011d060d0c020d0201060302090a02 66
    0x1ca0040d484082101019035000b0340b94030310050701e84a400558050040420f250001c245114640001e1613403060740b5001c81180b415070b4184500750b4401481d03450755001030340d0007804111400d2503a90304003158086400311416103000a1441c4e02078101400800c14006019524005a2941540109801d4220044044407a12000070645500300c07a01c01400002e001d856207109071403214010940c0c182031000c18824003050b031080503112008044029444002c1600400c0b212920b040301e901c0f141c8050500e83d0070659a0300000c8290f841151246055240040052208181c5148210043c3c040d50f228141d40ba0900c0d0070703002007100103001d60410310402030542da4a18100b40e030540c003d85910204d501c9200d076607400d00c6581c0c2d00f0045071413000c212171541d1400c1c0d00348a84c212003989601035813900c8540d11140c00555549204140346041040b00314080314954550100034224428082000a58003011050083c01c01141400e0101107904006041000da81c03180b8000c0d801030444200160398 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 50893178 1250 50891928 50891941
    0x70f0302161208011806080c1c02060c2104081e0f0d12050c030601090905040602160f0c081906020c0c0a0303051803010219050304020307170a0303240509 68
    0x303490000c440107002c10305200700481c480b035200c10502e040700c02818103210343d900c407403d40f1400e50321907000d540010317070101c880c030041481c1c0804103081548805000554008880d00420300340d42c8001030309401c540c8101d02003580ca0b048000c500c0d2501c18120002c030704003030070030b0340040d03d40c00801034207851960b0130185161704440600203a9402100c0d50102e032142e80500b80040c20b201801c000308807219103000300140d480100c000440f44101016555540c520b070600050b1002840040d0096484503400d01c40320f400b1a50b800702821400e40a541852a908001d16201c0d081c000a0342042400e50000b44108402200045148203a140d1025025846804405001d4500000c07414016030100903030b5000428190400005d100542092264901510740300050509034420422080214000c408405041d240306202841d0400d05c02020366002c0360342c031803000c0d2000c040c0714070903125500b0550482007010380620645d810b40340c5451058800b500104c4000c19580483e10a0500450070980000c1a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 50894428 1250 50893178 50893207
    0x510090f0c080903070206072402210a0b0102120f07060f240503060f040f02030601060519020601080613030908070801140a1406040f1d0c0117070f0302 67
    0x5444084400c228004a004006015008265100002c40c2010010480408011040f60b80058000e45206d01d000b03103d40d200c152190403428a4121120b10103045c01c03c0c280140020098070040c1c1e100048800701000d1601d44549028101d28036091401042103c40e980105201c2d00b56018580c0e081e40f9075408a0191040b4411200010400c0303107041d0a500d18038034603900040760441640c1d01000881c15051300c2005041b203e000700e40d410360000000600d15414107a0240d8010b01c195524007a00740d135503011034603000c000e801203008210041000300c003660500e0741241194909200620055140460158076000040c0c4800c0307903c1500f8205100703240c0075082e94001010b001c01210042640e510a8a008001e5800e400d502a02c1341000308083c8002805901e840501c510704008494a4190408c00145503007200248400d0b141c904101c02ea1100752810044e070340e454400380c0305010742000010440310404101550074001103060101055100c008800d1002d521f0400590310701ca070010a90 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 50895678 1250 50894428 50894461
    0xf0103060b19090e0606101b060b03030a030b120a020a030602130512030d05010b030f070c0203100207140c0301021207050a1407050a0615080307021c0c030b0f06060702060a0305 78
    0x62010b01c0070721000501d1002907129602c8610b091090b84d929448840801c850141d1980c490400078075550460380d0200c10000b105120507200360f4001451610800200f03003190089188440803940d03484082805041620f0000b4201c01201c0c0603185c40c0100e40e00041c44000715000c060300c407039070105140c1d1108051070454406417500815480c0140321140c4019502d5000ea0031105440d428038000040c0f100b43c210a5901807060885812444d507140d40c0100c6649014000580e4107218030519113021658a1004141c4207008000181c195250003106510300050805075502036072040009090701e16041500e0303900503116141443d80d07000345130002c80d0106681c03200c00d03440100000e522003c01c00e000841481880c0705090901c92045004108001c1c0c601d18401c1e83d6041e00100100001031610360502c130310f4007132070201540d000c003c44d80350301202400075001201c011081c0010712440000400010380c3c407640c01c071075031403138a2000e60200719580078015001c02030584a002045051042400c100d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 50896928 1250 50895678 50895709
    0x120411030102030c0304050f06061834020f0a0302120706060905010e1510080703020c0709020a090f08030a0504180e12030105040605010c051c12060303090e01050402030f0103060b 79
    0xb50344901300b44d15041055401940c0071559446100c0b00c0414410010034506c0c8280310007400082c260380760000c1d0800203000103004100300d02d0f9110703480c040d100c5102d0344111190414080710800b100040806440d10750b4950325040550b014003030400020780d00280c200030100d284140d0740d8071500075103040c00c003400c3c0d15081010b507641440c002003507104c0d802080600c1801c0742108040700c0d2400d0740070301c1852584c044070b41c00081c80c1c00000510960184c0c00070260f50000b5801c440c4501d40c0d45088034101c0c2c00244512001442c03602e02001944991502080034220b0781000d1031038401d008502a1952041c0d1050182c25410740000340d14440e6140e000e030401184440980710000d840b00c0d445c1c00319610902902d8402c03407615401051552080e001e88110680c46002004180e00c1d500e8042c20b1010007441440802074141c4502c41c00c130045000d04001523100e912003203001824054521000d200c1604500c0c00360384184100140355150000b0780e0304403038201c4000030300320114101050350390700640c030710 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 50898178 1250 50896928 50896931
    0x105060c0a050f0c0f040c0e1e0405011701050705040b1801050c010f090209100e0a02031018050114010e10080709090626011b081f090c090611031204110301 69
    0x60b01400940820110108072045540c04105c49500c0100412505040e03400300010300001c0040b0340c503080c8010010005500c5180075000c5e503100308002025100242c2043c1c0c070240050344220f8040c40240550b94001c241410300c40c1c10320b0304045181400b8003c01003602665000c4030b0300c2c4405130b4000c5007200c1d004200d1030000d002201441000c140a070880c0c0304104c0c0203224640c00104010190000201a40d880b02117240303168582c03000d050080d400240042d96a9400301000041c44070941c1c0c1d921540500d1807501050310340c5070400c80d15070701a05021107418041100700000c460398444030005800000d600b010109611281400c5800200681002e085903182420100701c04d00703607281a0340c0032041000040031884494031a542624840e0130b00641318600d00d0b1160074414019110180d105035201081a5040803058000d0544421580110681d0307540e143d8180e2070b551b1040f00d00000e040242454148070040d404d045a980c442c0241180d1548000e0010800b001b010780707040e02860100800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 50899284 1106 50898178 50898193
    0x605010c030c02030705122a0108040201030c02070503060c1b0a020a0302130f02070b01080d090e070e0409020310020c101a06070501090c030b060a050d0b0105060c0a05 74
    0x201e07454040c284001c502925110001c0038000c81b050020042102d001864481c04800c0ca103411b280d0422044e0381c21809d07600a2074090b0050350a1a00007070715180c8078012814403005400c816810701554040c00b540344101d001a024240d22010403139062507480c110b0559441030303900d009410426482041016284c88a071030900601d8482010811000501002049034072454003241e101c143c080060022031010020050780001c0c90400500140c280348800d00000d6004200c81c4c00c02c01030701001041501c445c0c00c035030a0b055024003182e844c10a00c503062000b94008a6103041248191044d6140c4507405000727480c100e030328009500302480c40d1242800095400440c05950705c0d9245c14200c40011303550280c240003035000c5e00c14880c0300d040c40420488415aa54000ca00c1242034809941c04142074640c0c2c503046880885125540709000400d40e402c080070244d01401034000c664 = true := by decide +kernel

theorem cover : BRFrame.Cov 50719428 50899284 := by
  have h0 := BRFrame.cov_init 50719428
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50719428 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 50719428 ≤ n) (h2 : n < 50899284) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
