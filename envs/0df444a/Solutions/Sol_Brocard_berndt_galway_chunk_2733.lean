-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2733
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:35:01.259137+00:00
-- url     : https://prove2.me/submissions/f0308a12-6bcf-442d-a9c2-b50fc8a93375

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 491366906 ≤ n < 491546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 491368156 1250 491366906 491366933
    0x506030c0405101e0503070902040f0b0901020120072006070b25050408010b060304120807030902040c03060602070b04032f0406060c02010809150c0f0909010f060207090209010912 79
    0xa13080c13555021056814081c2c4030201198000c5044500c003d460b1880401207201780c0c490508004030390f1008001c1d10702100007424115005000014a00720703035124800c0c0e000c1020600058031070780000c00c2c000704803800c165145402821007038243c41c4248400811707c2486408070140014050000146030036040248941101c0310350781403550103000c803d2000c1c0168101c1d0060054039420400011040c2c200720099038800c5820885e041da80d00d00e110b00c01c0d42c0e0b120000d03210b8020143c48915160140e00c42e07000d402012042c81ea00002c40d00d10f00034000b402c107100c80c0c00094406000300410008075000d128000d000480b040c618810342010303a0450301490700c0d100c1a0300d03005810898005915034014030540c41c0300d8001e80b1484080c0ea075030240c40341c807405010300c140000d0a03c500800c100200d940007806c81d505145528074503002b804000101c001c9826444800c02c10800c0406000941d0b050040308000c20311850158180404000080c2005140340207500c070603c4084004418030058624411 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 491369406 1250 491368156 491368169
    0x22060902100201090507080a200402090d0c05030708010207080732011a01110703061a0d0606061b03080601050d230709060903030206040204021803070603020a02010b040506030c040510 81
    0x41c14101d40d03810103806042601c0054032140a001c1002501c00d0700410502d810b10762040105400c014440c284030742d100c0344a150070f0780140c0c2c00d0109120940313510750303120b000b18001e03140c20820030b282008040c40c052071900255400d90040c0802d8001490000c152142503070712551055200c20302241c0c1019010000b02001041d0130f005030240e4501030198042446584000111545a4820401510325900401010205602544c010004620680c0c840d503121202c058003070426045c001b000070565a000b140c11780707210b550f50301d007041005d8026050312000084500c000641c050181c90141c2040e02c001d0049052103000903440300518510f81c40014240d0144151000343c009041004131000412140340d008a003121034046892360045e03004a080360343c180d006105540e21a42444040e40100181c0c9003003140c11001c490140e50305100400181040b0383e801038844200d21030003130130344180443e001e004a20380000d00601da140032812080340d60054070b003c20561502d900c01080300b0f02990045 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 491370656 1250 491369406 491369419
    0x50d21091103060a020a180501050d1505030727110a050f0d05091b0109080d0509041103070c06060e0c030403030b01022a0111010b0d03180b04171522060902 69
    0x300c0d13008250342c017034004006160b079820341c10a00141154840070040c080c0c90b0201d001448800c0036000c503070308024659030000c030341d04614540d03800100c0c0c50302e025500800388090203101c1407070740e222052174540380345d8508203414480c507000069420040c2c46541e07851820880d00041c0d080e440b103807a004540030320341600401c00041c43c00b400c4003525002640c0141111502e20900501d03258404c04004003078541c0c840c06010301340301005003520164040320180e900315490310038841d0703c04490b00c0a9445060b0588440704c2c4030186141000403500349401c120988400c80040c060040210000e0380d62040d4582400a280100c180060f803419a0f001c0002111162031440c910807001210301c148003a10080c0c0300c41c501c1718179051215007640c640411082d00702d0074400c08400802e201d285881e42101411900b0240d0075115032040764113901c01d4010040c81d5000e6040121480010013480f82180c103940c4095220b4100325402c1070342120181002c6c4610520261100c0c02d110855020301a21503005210 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 491371906 1250 491370656 491370661
    0x41505072a1d04080306220204170f03040e01060305060d05100209120f150403090306052406030f01031112030d0f0507080906040f030921050d2109110306 68
    0x1076486500c0380b802046a00701c00180c21207104090a44081d01440d8008102d82c1141d4070700c0140010b2034807070107c0030110030420029101c642e11510040002c0c1000d003040070081b01403140600d00d4012608105011580100410040800400001170550b000c0f86000b050540764940010000600c40030080c1c200e000c0e0280c49200090180e0003050320550a6418414002c0031120040e00c0750300321203200c40c01c1d410507190300040003001e03034043e03034054800d0070f2050b411502c80d21100304482c0100d5010000d03c010700a00151401d400301308070310414040710201e286161981544100c00c0c41848010504959844d0100340c5940d100c0c003a103c03120ba039808030707500e5805040400303014250f0805104041c03485e020104100da803050080c20b2194181400034090307600c0e155501c5442846001041d0200050281c02098581e281143e1001c03589201401c550003541074104a07003081d04004c04041881040165200100c001c401c04041c0440c1441300020a01c00600304520b210440740c0b640c1e40d25000300f904 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 491373156 1250 491371906 491371973
    0x13030807031e06030302011d1b040e030c0601140907021c0522090b0d0f030c03052506140105030703060209030f07030b040611160f0c0314010903020105060604150507 73
    0x4410f003164080e50090040c0c03a4410300c0c02170070010010018100786c124035125122024034011031480800058800a141c1030041662411600403003501c20041d00944010440c0b20451000004601012100c4000324140220b019654111104007250b1140e42c642e90784030060301130030649481c85a1044201414520180c00140e1005580190590b492512254504500b070841c401d42d00c803580003a269201c981581c80580c0c100403551000c804108041100404090b10351807080600f80042c20014003c00700d9280035410b480075190900102107001d4010800c55400141d54030480b81c10800042e0b0750327840034007c24101207100126510501c5503580000030005030244840c8114001d9000f0000c4005482c41400a4481d5000001000e150582000046500b801758260f03414801e244c40c8a03070304c0da40d0f0740f030b00c10b075034201c07a84408580d5403148200c00349038082c005d0550168046940328079041c10000f0440c3c0107480000d1182c100319010500c942004005102c5924200ea070400541d800240306c503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 491374406 1250 491373156 491373161
    0x1707080706021612020603130f02040911010e0405040b0105131508160e040f170d0501180b010903080d0c21020a1101021c1a040f02090a05010813030807031e 69
    0x15120807448020000140c0c1020340074460f200c0b6a00030400791440e1a450001c0c09440b070980d406a40c0d2702c108107660f80040c0e94500c61400c0a501c10419009911015000035000c0080700d410300b406141868200000100c1c90910745040d03640490b018200d40300784011003c01048000d840618140c8070b120042584c910018100740c8804542003007036a480e48030f442c800c0342c0c28002d5500804421181502c1340c000341c1c1c0c14054018050895101d14100b05041c1da8072000c1d11004e902c030111603110388111141940250040700603940d401c1c24003210300d51441d81c1c0e070115840391303181c03503464140e0b202c803000109803007040c0000306000148240040407440403800030003580701039803030360114480040304084840d06009484494000003201040c03036611080303c802814955a0210710402007400403a881e954600c15105008902c5c5801a1110b4164040c49070716074041c1c0220341480400341c20000320602440c0600c882d07076490b1400d41c08a4540d08000d0b0090828500030360304d454480910f251410034960f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 491375656 1250 491374406 491374423
    0x12020c06010f0f0f05010806010e040c080406050c070f0b150a0e060405011421070b0a0903020913020616020f09130c0b090a060e030c04060314010f020a0504170708070602 75
    0x50b07408050039956500c101d0038404107220b030450340000841308114540c0a03d0b5819400390060501001758400d05001070100c0c0d6101400b100840c0c03210b0180018411140711f41c561024800441500d002200d80301d400c880308007101c00508404400c4000b485040c0c0003143c410507003101804d0040b902d92207201011041c0c004031201030007149003a00024102c801c0b425101e0466001034411400d1080b901c16040749032030008603e2a00d40b04402d40008c00b0303580080104401c00300c654400d586141184100720b2140405131070b43d01000004001030300036a89010884c1c01c40b04405403485003042d15440480d190504041866074480c24031420403243d00c90750104407043c1c91007100420076603501c0d55420146401641f2501e90014803240f0144685800383c1040c0201780c100504440c1c1070f0ba170143c000b1302502c11079017003191015103281441c4601d910034019100180d188500550a00001500090141c000c40c400c420b1205000f41c66042c0003041030101c0d0010f4400c00c03080d181031382e40359000a9903c5801 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 491376906 1250 491375656 491375669
    0x20f030f070e10080603010908040f0303030b1002121612120507021f0905010e0303040804030515011d2a04060207051807111207030e040501050418080a12020c0601 72
    0x305002801061140e01d28668040c00202034000b4030540e0041141c0c0f440e8000d101d10341640da40d44544011aa12034090401050440f030030307035508d905614004050301c3c02492205c1c09030703898a02c0c0d00f00554010070401224400245a039440309440c2c1c40da041010304014014284000c00c0b207621079110340c0021000081c10441a062080e901c0e81c1e0b808a94178000460107031007140c001c140400301200d842c0c008100e081c0c0910008a034a080900c02241158030a840480748210006010000c015044c000c00980b200d035001c10100350340c034003910b00c0c851130b608103900704141c5105800103600e1408460080d10401c410000c117004c2500340083d01070a0391080c002c9401602c80e0201c00038080c0b42c000d0f088015820602c1c10030310b207611400307015140c0007003031000741160380030b0084140003059028025182144c00382d134035140064948000d2000b226810b81103103005509116030342c0110107404881c081080d41c00848181c1e0b408140b0070894421100c82150b03600b4074000126401004000030700d20781078994 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 491378156 1250 491376906 491376931
    0x4031403010b03011706040b0c0c07210b0106080c07020d060212040b060406050402070305121806040308150103020c030a080c1c0204030b0915150303040b120a05010906060903110a09020f03 83
    0x1449001b030740c0341401c82c2c00501c0c1c02c00c0b4100044090104001030042103215004660889850301e042d107a4003905d4061602282241c0e184030001c0c85175802550340104124240b012140c180001c0cd5816440ba907030380a4055040c610b0340c8000c00109078100c600800c0c0060b25450b044c00c2c0703498080e03000c3e1004c3d07441c40d1003141090710108c0e032480c3c548212541f00768181c44a81c5450300c41d00b01c0301e65031400103003c11030000000b01e5200e040581488071602c00d0303100b80e44410861418810203200030304903194103810544180401080c00034000101c0d510901c041c109040140e41d000700540c01d5128801c00e00c0076503032102013410103104194000d44107992144120218580c2d40c0080a5581c21004007546681501803003c124240050f05480400030300150039245410b031529410503441d400b49040c0c40d504240ca00c10002c00d5041480b54a014000462003844940e10702040180500301303901020301240003200d403115141c4c0e074013583d041c02440b80502c03e540f039160061039030074240c00c11140e8100c801c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 491379406 1250 491378156 491378189
    0x60706021c0f060b04030308040f05010e0d08010806010605041e05031204030212030307170426030f1602120c0106091a1c02090106050a0c061d070609150804031403010b0301 76
    0x41c01c0d4003c403029141d50544083c102883c5403001c5440410140060307070721820600000021880c28000e10562090400c0104240c0c500c00740000c00d40e201c160701510301504110300500c440c6a20108480403901d404415007510480c4118880b40719200d5404980c1c54804d80c1c0c504900343d80208043d100316402103e4105080c031003140c0c569142d110480d0380e18002054800851074030141078050319002405200f040d84032701c0ca69041131005080f620f41b20240c2c002c0100c10030500041c10030b00c0541c84070320304003568152480e0b031201030b50b40d100070780c081e120054001c01d8201c20b01600358404801012600703018003035800000546144403607020080381c002d1810640c030001c2d2401d2081c0c039001302513000e4003a00d4980c0c070b400c10840b459001182c042040003481b0b80010042000c601848410700600071b401a01d09002d200b400745445440d034403a00070300610340c60800004107a0040002a4162410440a030340e030f1301c0c0b404642002401000c03040c80034021001168080c02c07140558180c80102107030103105c9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 491380656 1250 491379406 491379431
    0x5190e0313090c02120a090e060d12030e2107060c020609070b0a09030803090606041b0509190806070e0a120f1b0b0c0c040c050324060706021c 63
    0x81c4514008420800745800c82044903403400c1c1d2040380c880e05a841a1041c0750804141003502d503201d07005520024241c81418040b41001240250b04804103e806032507000c0140d0703c1e104035880852503c4c0c1856640e40e042d00745001d00b40310000c82e008410b001410050f0508200d17001c030713801c406001e40b0316500d1f280103c1102400000c0c07043c050a64040106941490051a010f60b50b00c6414a001040305c40600080001d1034140914018016000940441e191560511040f81d4007140400a40c00d01c050301a19540d40200484905070401c2e14200d1682d528202c0e5285040429400800306100b407404000007280c1c0032000e4403164004450255a2940e2128003a0728203010301c038040c1c2825010411900000c03c0e020304c08130801c4914800140490351014a444a80c100492602c0c01d078101040d011004d00c1c0500c18260b6244082c10802e080d41044514509605800556403c121500305080d1586507644015501480d41c007050641da988203040810b81d901130004000e200307041c01c1900703141e0f00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 491381906 1250 491380656 491380663
    0x150e010305101e0204081c2328020d0305010503060609150415060e0103061d0c1c180201020c0337060f05010314010207020f060901030b030105190e 65
    0x100ca03002002007280c0307103442e142c18005185591003281016030405070b030491200d05001910040c520704026040303000022034112206c010307011820703080216684401303000016043c0a0f0007060010010142c4814110412481c0004610500c116410303040d000da00c9860350000303401d00c0c094180d540910580e40e8031814584c1d070b107c007500e1481d4450000320014503103007410300246c00d5a00001784041201e10124006019003130041c0c2154001402e01440c1044650301402003e0041034800001d80f5070300b00410700505030080c00b918a01010390000f0380c48440f8601e4105110444440034410802c06034100103110801c459800100d007d8091004251080e107004201000f080c030500d409099050003084021009034a1035004510b80c800d03c003001000304085100d1180f892114003800074455045003800000b842c1e14030002c000c40d038010040000161151003180800040070b45116441e03e1503100140c01500101c9400303500756203000304109410100d80c1401d20346000180080101c40080d0313448907103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 491383156 1250 491381906 491381909
    0xe0f1506060a180602071a030c0a030203040c031a0103140a03080a0c020312090c0f03030c120d1b02010b100201020403030914010507150207030e09090c0f030102090406030303150e01 80
    0x18444140002446a0a1000090074481c1e554601101a08450903a10707074415800c0d0003030710040c2d1111009001210348105880d64421841c4090380c1545000d00d440343e090b1003426003d00800d60048049400c10010320038613400340d0ba2205a004e0f116036010310000d981e08091109840d0300d4400594081e0030480420358903025038155480da02d146d518004400b01514050b00c0c5002103200402441401820200d2080d0061000002a2503150007500421040103080d14411303102e40c000300900d203d41c03a00000d50800d850790707044260f80c80d0181c08401304003e0100a41c0701c6108400d1004a500c81076040d801440c0b100c00441d200070b180040340707200b03c1c00c0340191301000b008280c64032003e001d200d01300030310405502c10514046150043e2b41d40ca00c8501140d6081e541501c6401241c10020190401c00046401d401500c4c65401450803000aa9884560b41c0003a80601c203e100a040149c8080d01100d0156a0181040c054142d9038138008005018042c111320b0303e041c3c2a000403c082080c051440d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 491384406 1250 491383156 491383183
    0x70519060f2003160509100801090c0215011701060314030d06060806030705010302070f05030a0f020609150f07090503070f0f080604020d24060303080f0f09030409110d06090e0f 78
    0x1411943c84011004441c09404c0100045c480c06210a00c41c07962100508207025a0380e030742d04012945884091015910384101030019508a8038942c1c0c4800c8040600ca411101c0140243d40b000b064a141c8a0052800d5080074114014419000c0d405a078004020036049416000401c001603403040100c1d00145e0666000e40c0c540c1100c0300070040b45d0321a4001d480842d004490f1035002d081659500352550b840031003504081004030119510180c0c0522140d644503000402901c03030030144409480780174030000e02d5184081441c002280700c0c1c9126070440005400080c040740c1c00b95450f00b10b9400c2c50800e901c1040c0c9084a03080c8041062203004c62a18044c0d64058603005000a044c0d0300c640501b440700610200750030420340082100c0d1000d019082c0258080d4450700c07640e041c40100c15050000c000c05482e445210a000d106940c0300000031102226205040011080d440181152091041010f1390707004908242c00071500344030703640c0b000001922410482d0150313042c81142544880d02c111080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 491385656 1250 491384406 491384471
    0x11100501150f051b0c1e030613020a030b1302030f01022a15041e061a040212040b07090308030109020301090c0807020c010315080616020c0f1302070519060f 69
    0xe08020204007440c8a4041090a1701c5c0308011680200708842860111907520b00c0e00c0c1d49600303400e03007400c5c421203400640d58404030070000d60320b40128810550071702c002080b0b0807448000680142d2600c18100c4465070050650b0641c10110040038040c0d00002110030350401d454104100010040040e00c11b1040560b014000c903840c50b900c45c0c4541240288207403118002c0318941e0301c0c84420f0142c1c21f800507120310070000c1c3e540c01c00320031328407029008140c80e80500c0c410001102842450082c90354469400303c010002e983e150241211a502d440d40010108a00400003161100d0303160080c6041e6101c90004116904640038102d41d40309040ea01240540c00c026600010355100c0c5c1c0003410035487e204c1c01e40d25200d5842c0d101ca0702d00a801c0ba100407510fa03030036016185603035040c0000c25146004842241640030740400040043c1c1e01001d031412140c0d8002410000c000d0107001d05521030301155281081101c040c10154043c1c204c0900082c1d0244c030303180420400111402d445200c1c08099202c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 491386906 1250 491385656 491385667
    0x6010e0f0d0b07140f0307021207051e0102090402040f08061b030a0902030304050d05010b010806030105160804020a0305010606020715141c0f0f09111203030f0711100501150f05 78
    0x8264002c00090100d90821000120700740d0307203401900040c500f0084404189981c1c0c0741c0316000078207080300eaa00740d0342c542c03004110a20100c6e0000941480d030150755800700408c01540b103812130080c480c9914080c1c00c01c2c004500080c6006a0341d0480b8212000c90040d10b003103690700768440d184224454010340c0c0d022800d0001c034441d13032250352007003208520140489250603181c0e00092000c0e0280c0c42e044689a444c1c1c104c2c1100c40d42d020441d03d0700144160002d101c14280640c0504030060003410443c00c000d00e20001406554403161044004d680241c002c1200d90b40710709000752518224000e40c090040003040c4034484501ca14400001d03480407440260030619901c003598060604504101c5201e6102c440d100700100b0349200750301802800b0403000610680c20700d44902d4030342a440e40284146644038050108a0011045a500420082c2c814080d584d030030f041929580400750040e00e46120300c02c46445014a90b0780300c2816a900030300c8a00030a0240c0408561801042a41c40c0c001002840f0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 491388156 1250 491386906 491386913
    0x203060303032a0f0d0c0306060909090204020d02032a070f020f04020c100509011a09150303040902070818040c17100e0405070306140f0112060b04090b06010e0f0d 72
    0x12500f2a125403403241ca04030b0550740250b842580040784102d4051000080180041d4000d01c41c290b000641410b05015903880c00001901c8001544581e404058880b4041e504542d0345a044031400d0020a03001c540ba03082c5a101509003000c2c200072480c0c41c01c069000c0354010039910707060701c08540e0311001d15038624440e94217024019401e00040ca400a8082c0a02e4106417420300c07401c2440b41c85920000b031281f420190380c5080d6600b48500c40c0b20f815803000384103141e840702c0c4003403540040e900340c0214070700c04007402280c514456a880304505502c0841e4040030410700d04020151040002540c440e40410581040100c6491b4a102804180141c035001040c00c0c00d02d004039400800107c40c400310380c0d40c03100e010703101280486003150f40e604600700038801c00426215030000403e0740e0f402c800035413070203000350f07103a541041c082d114016800d02e404404102c07007a046428046400342c0b0a000012940c81c01803110141910094003088030641c40d050300f41480361000b241c000c002019007065000c2c0e41c8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 491389406 1250 491388156 491388181
    0x7021e060105130f05150306061e1903080a0201091b081e0c0a03050705090f0610230d05040204050702010e030f03060a0f060809120a120e250612020306030303 70
    0x746074032115260301340c0440010403403140c0c9209410066a00551605500c1050b0900e400101610f12490540c1519504244807460603000f80c00d0960340410b050140184850070111640c0c0000e004c048001003c04285906410256115104405c40803020100004a03012141d2601809100342e102c1c11148111101c0d550302d81d242c00000000b9181c0760816400841c0d02c8074502d4009503045c1c3d0150301d0800c0b0506180c203036907030301c0b41d04802c0c07640d51030500ca40021440307202600f102c2c0c104010302c9510f400c00c4a810700300702c8006070403c001e01c0c0d83e101640e5807032003d0310044030b09903c941c1c81d040019003801d0040c01844207035080740019515250003d0002c0c15180c00240010b07800500c07503440441d44e1913030074075400040d001e40d403540e06991425049a070300d0240c03100e485020003c1d05104181c20980c00c8100d20300c0141c40307618046401a00030790060301e07249200040040e481030301c02e91a012454218040700030780700700740da45940c5090181c0c03906d07041e0301c01561003a400da4020000aa00c800076030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 491390656 1250 491389406 491389429
    0x20708030a0506010e090a1409070302100f092102010f090f06110a060c03020705060907060806010503090c151305010309230f0109030906030b01020d02151005060d0507021e060105 79
    0x1414001c01d00c00340017012903240241160301806c0d10ba9203004049240b030318000341d00d911908410041480508550128030b4541c1080c0916080c40f800070008030880c1c3c003c1d480c0102a010141c0c9160800d400310507940c08900300484113902054610348030040c5503100c0d140305010380703246140d803c811901d003135011180c40d500d112603030180c1c0c002c170052280012114012201e88880715500541c07140c0d101d05003682403d00180910300b1a501088007000100c0e001248603520900909003140c880da00d003445035081000d5080e541e03078046a05c040012078520000d001d002010003010103d44095244d00040d011143c20081c041c2c060880c50ba043c00c01c001962030011a4042d40d42d00392011a14401d03129401c0d500d0488d4200c001c555403080500c45540c1c54403948041540034402400f81400180010751503641c0b5900c490840d05a060000780000d2185030102d006060103440e81d5a900795421404008041c183e9200006000c0c5070303820074001c159070019044091005000e42226441d1070700b00407001c00ba0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 491391906 1250 491390656 491390659
    0x180c020705060f1210090e030a0c0f081b0d0f0201060503190501061806081002120a05070e03030a0504080c090910020a1b06021e0f0a0c0c0302030f0706030e01020708030a0506 77
    0x400015010038144d03102d160040c108203100090079814140d6070000e40e0030200c1003580a42c001e0164203150303039000454040c1c030398100040034080308071400e11540622074148000700c5100200c001408101c0c000031200060909a50389408042c004c1000b00c1c260765481c4036071580741e030020742003045000705240309001c003600c50f0000040310307036551045281d100d0024032003500840d40d5040070004000107110981800e04032003021407800b001d965146e00000c2000d040c40442e56620000900030724040d02840940b90b03802000c40f9110080380e1401441580036002e613002a000e4000d05011505100d0b014a010347e9643d400382c0301c0c07040040c1081c0029006001540b04206000d050312405100d910f41101c60507000b6a80580d440040c610b45e2200f10b00400014800751500f000743c580401c200c8002d40307811000e00c3ca00840410f1043c00c01074501900c0d500042d515025000040294041c0010301008a4805071014849042d08000003401c070300454501030a070382410000500c28119560101d90300280 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 491393156 1250 491391906 491391937
    0x501062a06061509080d140309010e0106090b0a120507030308071209031d09060109050d030203040b0c030a08090304050904080c010e0a03050903150c0f071e0c180c02070506 76
    0xc6911103000755a0154444841c16200301410340d035083d03012503031030003501012000b014040009580102640312801c8008030078040800800c003408000c1d088502c811003464028082c5585a12155006140c040c0059114042110001400e44840040d003a41e0030b4100015050710761560314142c4000e0030007000c01c07040203140f0810140044d40b40c46660702e1640607a03203842c000c02043c0080301858140c9200c0701d110780d00744400c004e140d030b91000c4082c05481c82541c07a8640b8200f00c2c60241c1c13460245401082544d4804645007942d03a1002001e00420300c001e0707803500d4854481486c01c54a81c8600e005203600704007a40300050105004000418810f0010303400080c44030503841001d42000380903e011800a0710005104649180410450607000c08410228841741840715010040c0c0c032600b403161549a9000c9080d02c180000912544070102c0f18801c484030b80340403441c16810080c014001c1c0d01040407010410286040d07140306031000610150000d000e00307030400342040f12503000a281900a4a03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 491394406 1250 491393156 491393237
    0x7051305060a150e0414060a0306020901110601090b0a0e0114012d110111180d060209060301031505010b0f031f12031107050d05030703080705130b0913050106 70
    0x360b120140c103103c0e02c1540c0c544481c000e030a0104400d0318410500f408402c5202e03828072080d83d54031491641203e41c0084010f990705214001a500ca81c6220760b2180e00d80a0300e00001403111040d000000b0080044520440c19a04c44140c0d42c0108420f001d46102c10040290035405035004201c20520b0410266810208502241c04108902d0900d00c00c600064240d22070303030568020901a100440303c4440009040002c5056039160850748004071900c5000794031144421300151743c0c12144040e101901c516500e44e142c0c281090043c00344d4240654551410000048035074001c8291203440280514407891a01d42c100c0404610041544e10b020400181c400086c8243d4941405560701303100e41c0310340e522281200d0b80181004615030145015404035080100020004812540010b074582131007141503c50540440d102c1c0a40c90b40d2510918401e100803030619802406010008000c81d05168480c204000827022760382c081c42944d0105075a10301041d00c045c811100055085001c6140f0300c1e03083c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 491395656 1250 491394406 491394419
    0xc031515070809130506030c0d0c0918050708010606120207050717011a03070305210c1504060c1d0f0609100906120608120705030c06010b0406030e07051305060a 71
    0xd5000710300860b00080001000c22075400c05042c0c01c0c4034032008900801a030720b000e0002c83e45800c0d40301d034114410043c4c6808442080b0320100300c0809042501420016260511010840584800006d56543c450031900042403817050040ac01510019542c82c41c46940010002c40a5005a00200c4907401349200104a8100410b12421140004000411106507800c1ca01640400610140b4000d0300302d64010310214a002a000c0072070030080c06224001c4102e4406c0720003074000c4105081c020b015011482d06100c0700c54402e58061030240f901007080110800381643c0020301e0101e14011104650040c40c200e151030407222004800103024540342c09029000510203141990344440494001c003001e00040340d000900080c50b120140b01000300b941058181382ea501580400003071825400a4581d00f04a0103005031124802ea0b17030100d0310b165031100e01100164006014410002e40341254051800c500048c081c001c0301e0b006080a46002041c2010401a11000b00100e800802c81c03c00054603 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 491396906 1250 491395656 491395699
    0x50105070801090e0a052518140c0a0e010809030f03010f0f12080702041109090a06240503040807020a0e0403032004081506010216080c03150c0315 65
    0x5180c940e40e01103042d81010980701c101d8803800001071003a880702030010001080082d000091032241117081e46000300e44d200b1000e07031800507001030400007210148a9001e400c0340c2c019407541d40141d1158042956000f030b00504c1e03030192081000c0012031107101404d0365401b6024064004181806507442c14091440ca20301c00d60081c3c1c4200d0308070ba802c45081002e83c541c0b10642c4090896401c000042c0032141e04d0b86052405042000b9200d03a9035110703c020034404070022188020805040782c045480c0c812441001800140328800120007107560400300e180c2c140c440700c0c01c100101e882d0181513413201e40703030406150027008080340c200401c2000890714403035005000b44118803990700842c030b04070440740007910400402d64042a00d0014001403100e07240c08240c86400084240381c41c1003d503110700c0101c0c40c20320303141804902452b20500210f01c000f4045141171f58980280c04031922081c1104040380317401c108540d54140900b050011030a5040c1c80454803450340001000c43c00d1440c92034003204035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 491398156 1250 491396906 491396911
    0x180705040207050a02240706051003021f020606090709060e04020906042c01050f091e011412070f05150c0d0c02090a0c0f030f060f080f0709051501050f07050105 71
    0x92613407180441004610340060070508030704002c02281c03695080c1c2d1019600c5400791400080540f91038200040c40300744861001c400a40d002085548030740d08c0d036800c55505840545041005014003400500f450030114070b540e02480c52a0340300c030b0201d0300d4140100c80720010005040d5016030204507108065840d90050005452200314100311080024401c00c40d52200c551b403100000d140d5001040145c0c0c644c4501c015180054900c2d4881d03582e45110003032880030a0990705c959035036903000031070514000303031a141103810181c0d075110281d001c0300d05044d901c409510501e20007480440c020b00907030905402c220440c450f03034140c3c28281280ca06e402810801c02c408420300080c2401140c505500c1d12003c000d03081100c51200300007280354020010100302101c0d001d001410b4803410091406003595206030010545500f6840f00ca80d00d4010140d107070101c0b03446d80d1030706200304400400d44c11980d104144c05510410101c2c0400e20142e001540d298122242c518034891050140301c010035002c0c05201d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 491399406 1250 491398156 491398163
    0x110303070f090602010c0c060b011709010501050102070b030408030105041e02280c33020c151f03030c08210702010f0e1f06050d05010c0207050d0b180705040207 71
    0x40755a092220003015000581e11403011681452078030401941c00103400090716800c42d40c0444c6501c08100140d86065180f02c0101c0a02840020003c01c4081036020f281a10000d0f800e840d0017030b583c1e0452802a00050b60040c155200c01c000402c0385152950041c01c1340340c1c619130100030b071100b0303059031804076002200021441906190b401342403082002c081c0040c00340c541446404124991284010901c83c1012039260f8100c02d40c00200101c039620b11604242c1010340c095544120712201c1d030303440d540f00140041c21041c904006c5000810174035042032802c40c0d2582c10050003441d50f1021a6a070034002025552844208a40308410761032201c0c21ba5910743c44403040c4424144090001d086030016145085014a0200a2000c1580201c0d61101b10004100d98428584c00300746800020300d40b5a10140c6d010355080090000c100d4103400510807450035400340e40181307035034005001c4003d0f2036160080c01040d000d0001381c3c20b46503c11841c0c0e15007182d04c00310f919254451001c60201e0b84a55800d6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 491400656 1250 491399406 491399417
    0x60315060a03140705030f0f0916030311150603101a040603050c0109050102031908090f151005041107080c21040e0a02280e060403210305040b1611030307 68
    0x980b100300080da4181c001e460b0b464080e103146022507d6a508410140100303403080300c0180401c011030300030050b44011400440003890341c99628038001c3c044051814846225010340f440440c02022503804282c8140005006410f103001621800300007084010300713801d8404821081d681540e100c80c850503000c0c501c17501c000c0181203040c000141101c2040d6200700d0456004014250020084480600100403542402040307030319040c10340f03420408003003000c442a1080a810030480010f407041c0c640103800124aa01e00642c48000340815951400350380184a0000c00c110340c006486840180110104c87c401d0712050000e40c0075441b03403501590408801300b40041014803d803820303040a50341000640b04110b2070500580102c81c09401a0410f56100108d480080904c0c1c9005800301d41d42071a00420f0180e5030340d143d281407003460050140304a451241049018501800b80c4182c6000c3c039000940e40c11140d0300c00c6c40011038242c085d0a9041040745034510450800360400c040c501030034040d00c51 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 491401906 1250 491400656 491400671
    0x315110313030305060d050d030905030906190f05040b07080d1508070510020114070509030708120403061413020f04060b030c030402042304150e03070614090a020609060315060a03 79
    0x201034a401405c058418a00f0017044000030b400010020250100d0b4100868100e40303c0c103005080d40a8249200d1b0000e40c0016611140201402940c201ca041a1110a201050b090b4204c6140c0a02e000305005400704001c184045001517000d40780842c1c4420001c110034021800c00105208160b00c011440d50026105206514016030003043ca0080c910080104503889017864a101c0406440e09060010000d010042910b041c040c7c0c0c3c02600101c012102880060348001d001603000d8441681e40c00d02d065250b47d542241c00008900404011030944410380503238080005072403081034002e50182e0340d491b0014000c00c031030001e180b00303219040036640c40f4641801800103071044128a1150000341c2d1282d00c40f078484581d50980c004da04001010b02c100c6925103000000d0128030305000c12840007040034410003006070445504100c0300c124407a03ca8440c525802d9030349038148002940908140408551400c281e0090f40e44800c1c42d130000d68114020308081150b030342c060708070540041d13100c813103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 491403156 1250 491401906 491401913
    0x7030302160204021c29100e1e0f0d050c04050705190306090f050402281a0304020102100b0f1c060501030f111509040e0703151a0f0a0315110313 64
    0x169104007103c01403201128141c0b412103200b46c81c20000c24a01c01c040d40c15840031514800c61a6800c0200c02803c03000d04a0454040314003040d080d0030742d017807040300300c480c90700c07081d02344103c00030f200030791140040000344485001c100140030700402c001c04012061100c01c5400d03ca030380803818540c8207520001240c50408103c2000c1d1500100490000c0e801c03c401c7c0001030321080045000e00303807803090f0070210400c0c44041d1711240342c0302c1d1f0007869959900003050142130950b44c0194040e030710076001ca95100b040c8000034010307114021541580040d0b092009812400c0c4521180302d010070720a403c1149041d55070310740d41111302c2a0026914440f180c8504010855504e0b03a08410783c8040302c0030307650012485644010740c440c2e0540640510703200e0585501c588400c0192801855110b02c4d0038400140001002d00104002195081815580700c00c9028504080040c00540c0c24040d00c0300031a0780c01d54481502c88241101c500403030301d9440c4800040c9a03054406580034145420b299100c0340c0071420b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 491404406 1250 491403156 491403161
    0x210060f08010b0f010519050c071701140907123002150f040f061407120b1206040b0c0c071d1522020c0111090411030403020307030302160204021c 65
    0x102c0c03240c09141c1e5180d0f4400160307041b03025a40400035515117001d01d0480545c0454050140300b4207125288141301001c40c80007029107460000448100082040c09a08030089603a28012388080d041303500020014400c0355140c0c8058005280104050f0a9049031b13034800b9407000c0100c680c11148142c1841032030481d50744c14403005036403041d103015001e454280050484007180e0701030300003000d50840741c50030380401c111904110303076a040c11450300d1f14500d0300710307806801d40b2580460f2141d030f0307880d088412038145404042e0b1812000400001d080540c1d45642d800303a52440580944000d000a100c4030800c1d8400704020350240c0040c0d0100c951100d2281901c20345140b0280030100d4040d501114000992500054068500d009440805903c0e8410301c2c010001c0c400c26450280a5082024042c2d0f00c100c01c070010701c005001624200088150a5070340003650005840040050b08204082c0004c288660060300040348014282424030390560b0029040781d11048002038407001c0034000403142034191 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 491405656 1250 491404406 491404421
    0x3160c0503030301150c060905030c07090e0712020d03020c1009150305010506190e061204140303040302060f060f060d0504150501050f01110709090f120e180402010210060f0801 78
    0xd0307000714199410019400c600304005041c20302000340604180040c4406608402c50898020341641d13074801070802075644a8106011b00649035040c17103001840c091b4001041e0080390f4462104120000b0f2582c00c07c11307121241207084d13007107108072110481c02d0340c1d5440c0d03001503d046030f80b20300c6070061401c4104004620340c00c04c003100b41071401d4010030032604c0307900480b84c42d8403031070000c81500040c941083c0d8144032907080c240d0b08000c0116440c8244807040c40500d010718003c0100340e5059032004030b1644c3d01d00c81200c0040041e0401d202181090010106460300150000c2200d0f506040140101d03015411110400152980305e10500050080031551a581d01c1134007001401550b0501001c18807002010342c1c0c4904112801c001d581c000903040c07240c00080c1a02c80828000c440c60b80c10f1050645e200d5860981e12044200510f00300c1a00070062002c0d90310010f0016518822150280c5840c240028003c0e81540602071004094a4480c86468007031b14504185040b41c5042941542c01c41314003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 491406906 1250 491405656 491405659
    0x2c0709090506192105030c0d02070b130e090c1806040c030c090b072f01120603030e06030a02070501111908062803080d0903030f1505010e06070503160c05 68
    0x501e01c04076004901e40340b00d01035508905126100b049070380c900803c10304426501a089000104100b9003501000c1340010140b1062750885d04455154510f001c0a0b1241c510302c6481c59403154000c20010034680c03a0503501c80c419005440b10030007180c01059107134000c04040c1e0b0558940c902000700d40d01d400d1051006025407031404000c000d0b01194040c00c0d0754031602521030341c06408a4284e0030042039041d014501c1c904215815050424510f0344080300703403a005041d020030400c8000329500c01952052004582c0c041c0d42e00344100009400b448a10f500183c616501c154007080010003007402400380c006141c5201821580e185018031201c00d4000701110b510b02040101ca050185a648501490b4010915505114420b4948901d5607498107245e900081803030001207082000910603500c801c02160280d14144208448840c40d04207c500c4410348210310503844070180040e500c42c2c41031101ca6034001e01004d1800046e40c681901c0c1d604020361001c400840d240b031103020403000d40a0b60004050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 491408156 1250 491406906 491406919
    0xb09010905060d270b010b12221a09071a071407120812160c03030b030705040f0b030f030f040e070c0c030308071808072c0709090506 59
    0x1501000030004a9103115040c030440700450b2002001001d81d0207882c00750b00720444000805000c0e207110604810f09001541c00310140000065890021011240c2203410354a24140f6071390f560000c0130300801070f52940c103408080c911000d80001c001680c00c2071400c0c20344008081600c0d02040d407514010080e00703c1d603d540e0701d007000c045035920a6402d0310482980403000800c01c9116110561134507006601000780c603c0c9000c03014090142d03800c0200849080b0f805403282aa9964403040c007964880c1900342c00007000c444900d00070070301c01e50181c3e035400002402d8501c600d81c1c0b01c0c0024144e4491200020381e03140d03110341400c2a413604012800d1866101000385040070000c0300f2030b03c410b0185106482d0001208000684428071a0518101c4e03141e0202d6445a01c0780c030f03030500500c410000c4445001248441c8661001100b0140610b8200c551101c02000b01f20304110b00002c0401201181c02c80101c00d00155a01e8003400c0c1191381c3c4510490358071745410758580640d40b0705448019000358010107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 491409406 1250 491408156 491408167
    0x50609131b03151a03010b031e0a021807020d0f0807030e1c030b01020708011512030306090c09080114010b0f0f1b0c131401050d14010f2004080d0e03070909060f060b 73
    0x3c40101c1c0500c02052743c0444860b41c00941c01900741001c0046200a51005000700d440c0040a400c8082e9802040365600b120326121840100750340d100045454100841c039110000340026120360801034906101600381e41701e42907016080d07000b03115103005110109442c0c1050030a95681000700f20020000f8034024440940c074241740c400e05c81500d000308000c1c280001c600806160181c0c001c04011300200c4020003c1da909500000c006415601500640f5420501c0120419030b000b10824141c94000083c03500d0143c801203200c049034880380032460101d4091044400e941810780444088480c20005403030114268002c0140ca00c051000055055107490f038016220360903000300c203040d0382b0305881d20590001366040042d540d0300310385444803280d82055440c1810780c8840d0000c07860300804c000301019040240000c02c3c3c16005a008501980c0d010500004545214050009082d8406410b0ba480680c69001c0c420543d0400c040684020761200c00884003010079100d80c20080222a500d1030500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 491410656 1250 491409406 491409409
    0xd080c0405060c070b04031104051302010806060d09230f06070504060e010314090a03080105010c0201020c040b12030a0504050f0607021309080903011806050609131b03151a03010b 79
    0x5000e9801258054400400c105450000400500014280643c80d240e11240e4915011284442c848a128001c500f41808515080f0044004d41d0b04c055050f114400c16a49441c10700219070080c41000203015194440034000c500c3d0001498241c0c014500e41031461910154100e240c9404419400a2944204204203860342d1050980c0e0507541d261030035405141c0e40c2d200417405040011700d12504403500e0018031000b00c0001510b0711440c0d11035111030040d81c4c1d1b00c40054540c50120740c4064003582000d1400c42b002e02e4244d100340010310000340320224a45481201c580f442d0065508034010400000e814015403402800000755018100c806510700b12143e4040341001d0800e0a4564800d0b807100790501c2040101000d560b0840310280003040300d00aa51070400060031100420b071143c502e0700b008280107042001d0400c1c400c071100c1810302d0601c0d52945c1c411a400d1201c011b05c41030400201c601000168070a242d8800c16244404e0214407a00c888903480440e030100c40f1214420ba02d01541d103c20b5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 491411906 1250 491410656 491410681
    0x5060403030302030a0f020301061d01050901121107170c0601080c0a06030b01020a021f090e100b07030e0418020111010c0f0c1a01080a0b1303020309040b0105070c06110d08 76
    0xc0d00d0341490090784940780c0454134409070410450700d641e01e43c00400003041003076125071100100301034400d0400e00c4450030401503840d41300c6d41c18070074001035880c2007850a0340029004034102a02409030146442c0882e21544220344036030038030350040350002900384500201004024054075021000d45165036150001075a42d1540e48118002d145d03c0c0c0d020251503071700038807004414640180041e000d584152140018040301041c0c1030303021810f2000c0c04200201e84584d040e1142d0120075211849a05214018407a0382024500b10304115401118075101d0b2140c1c05070101902407a015007410403400d1001500d492840850200d2603032601c64144011035010400c0b10081c8003904204809406034140150036541107071803d014055840000100c0150004026003003074000c3ea06110207844e040144140e07801005c5014005a0040c0100e045602e0a54230070800340005040c29880c0c40ca442d901e90328642e500d0f501004c0840c1c800007140150200c18450820340700c1451070460f2030380c9410b1203080ca0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 491413156 1250 491411906 491411909
    0xd0c231c06050d1202010b130203011503020c030906220803030a06080102030603070e060a1e060206090f0a08090607050604260909040b040804030803090604030215061c02041e020d050f01050604 85
    0x2980e4801c0d1358050a034000c0d803041d252010041c00d0400c414121944003030284d4400c1c800c01c028540700a01c1004031134807900c02d48081d010034901440c40c1528083c10040d45800c0b4041c81e8012003d400100c18540100d42e03018030091030b40b003024603281c3c500003202c0000c0750140e5100c0c4040e6401082048147e98010650030181c940b5020700b6412074494101050a0302540e270052090b165013034044001011009082000701c95060b4201d80320390b6552600151503019034500020b0650111210f04001740704030004d44035961001e480d180c01d01c0003945401e4034104041d20140e070441000e180307010381540b00201149008564004061400ca400000300e890314000800141045091300041400c20000c5130403500116080b15480341c0702e00740010011749030201941c1c201d016120740c85002c1002a25900c1c4984a0350b002030640d40d00058407803031b690301c24400250888e80075554481c0d44183c1000781e0150000c6544282005032684044e6514070115603000e0f1402c41404030704001004940d031400c08940 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 491414406 1250 491413156 491413163
    0x3060a1103061207213e010e10030b13051303030e03190f0206010806071e110d020c012003030c21070519030b060d0c231c06050d 57
    0x30184454000850400318103401031440f40c400d12000002ca00c09615010101c68001c1d400180c1d806444e100d44034040c90174001000e10005454120540785a0300c4001210f15401030400c100c1d5042088e0000720740c40350006010003c01d5a8100c0500c8a0400402e0f81601161a1b0020410f505000c1050184403490382001020580c8940c622a80540c080c0140c42e10007082240c3c920f02442502c6000c0c0c0044007003c450030042c860304000091525001607900e0041d01c4070744892545e028000c0d00003c0c0080c5132480d2400b44015007c600300c2214040040f502c00480e00e90284c8028640140010710030803010508080181f141030100496900c0407044903080ba13004888142c0d076568003500c1024100210388191010213420082040b41a00a40140b9580c0007400d19044407940c908000c1d0102d402020380c0d5500b100c0280000d001301480790348031550240807410b09003c2400302c1011006401e094500004501001044104010001030082c0d40703006200c0d90144480d600785404510000003004c40036 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 491415656 1250 491414406 491414419
    0x30c0c030e1c0f0b07080c1306030c170a270c060507021c06020301050f03010504030801151218110306040b0408070c1502011b020a05030403020d0c12050c03060a110306 74
    0xa41c034114410b40342e100b0140c0d000581880160141c18134000c240c2c0c0803907000c00410160800104c02c8014801101c2c00401048d1034075a00500701030303040b0001d00742c1a8281c1d0900038070b25071076018444180c94061003405858004100549404000000385051507a03c03c0301c812401401c800054800001c0c8060341d40525100c5e460b0001400000d12858408a100c6985049202800240000f580086068a9003034412008400b00d40040c123080b10021540900021a4003005101303000311201e0098029066142640c600d031004d0581c802120b4181c9000004000401c81d140100220b902e824054540118003900252806440b1451917000082004100c5900010514204108048504094408908070811154041c2c6010f4000c0608807401002c2c2110300c4440c0e049544000399034003205031720101643c02c280c0703154288a00d229010000301c4d681c1d20608000314178909124000f5000034040c00080c0700d0181510b06150030110007804c5031032814106000940c49881c00802c80b0341080b02502c24 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 491416906 1250 491415656 491415679
    0x16030b1605160503071101050f0a0806040e070e04020f09090607050c01060e091525110c030105190c0201050115051b031602041a0d030c0c0e1303030c0c030e 69
    0x80300e40e8401c50070a144240d11030b10324401440b0f400006070842c01d100d0410201c0007101c0400545190154550301c510f919001c22140004c548114903458004d0000341020400b0003581c007520307041c54101e0308012001c40341c160422095140c01c0c17091a0382c1c00001e458048250400c01d9502da16141e00400020034008001a503c6000200354071150041881c4126030b0000e0030099100c548800d042c2c1d01c3c10518911500100c0c100c0d156a180141904410085c03052000244002c01d49402c11a0601d804460003040050001a1400e01400b0b129840398a40b2220440d68070344000c00f00c40111002004680c5444014014521400b01400c90300c3c2c56030800c90744821000081900c3c0c0c0d18a543c048505000125910360b04901c60010700440078402c0b5005e100c090031100b02d415160000b41002580002e59810b101d01090040b07100003d880d015a480c07a5201740c41e40c0c00480f44410640300d42d00c07802011410ce0050551501c03482a00d600140b904480290340d5840040c02076071074030070152048854190 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 491418156 1250 491416906 491416951
    0x60c1201210606090204230f01180e0c0c1501030201080403111015050406060c0503070201030e0312090d11010506090601110f0f0a060e0a150b040b0d0b040516030b 72
    0x9007202558081410300100e615851124043c0d04248a10840175041c00e203200c0740a882d103000340e00c0500c00603001554906180c0e0045070402c3c01200003a207981c5407441e011500c044a448132601c12503e0300201503076035086030311440c038200341d001e01060120f82590040c00140ea1252034203401c40e400d46445100090302501040c00c010303c49099121941c03030002104c129440c560014021100100e504120b0f0655034402a5407181001c40001c00340e40003040050015030281c1c0c0650750010302c7d40c0444c4d04000c145501444986800c1d5a1a00f09030303c444640c5448980c0710482d6280050000d000340541d041900100d1560034020389060306011a0b441d03d4000c14100304650140d0443d07440403140ca40b0340007100c41340c440052000aa0b10b4504002a070800c0480000d01080c490354480c46500100d483d0403c420024226039030103e40c041e44815030160076a0740c5c043c01d902103600034003110300903091910f0701928040d04da106210f881c940040c0c1c1080816508030859501620004074014078485542 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 491419406 1250 491418156 491418209
    0xc050f010809151b0304140609120d0e120d0519020703020c040b190e0f0108030c0601090f0b10200c010f050c0a0206070f0b0a02070c0519030b01080c03060c1201 71
    0xe18007120301c9408000c01c800d07c12105440c82c8280626015034410741c4400746900d844e100b01c0484440310010070020311200c01002c0e07000700f0350b0403d68401e5844c2c1d0790f050290110f00d64003480e82d1081d010b89031401e00217100b03c2090422602c4011010031483e150003550041d449000a0444900c2150b03103986012aa481e0149014007032901d48441000007602c4000b018200380c01500c0700702c0c0d1500020300101300440000115403000c5261001032000f0382c42d104e191009400200c500389880354540301c040c8510b13150300c480d0010840c2a0f803a02c2d500d0704420b003c19403038104028079880c51070740114030403031159810100c00c0490382070915041e95149c10680501b46800e03210a0003d41100340001d240f000e0081100008a40a101c0c00307160340c0b25150001c01c1c0007030740210500035080c0c0e810b070784c001c020618003c190380500341c00345e9644140183d40c0c0d44910300c54000c240d008c25802e4000507240d0381d891406004442c6d010f49900201d03810300030700080c1c0a4002605024102030801001c0b006d24a24078090f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 491420656 1250 491419406 491419441
    0xf0e07140406020106080f010209010813060e1207121403190216080a0f030501540623090403050c011109010e060918070315030c050f01080915 63
    0x21445641d201e5803600004e0003060a0b102c2c002c203c1c02505c0c0110700e5a1418001c55000e501c0c1650b850740c1903207680300c5018081c10340749012a80035030781d400903101000741440b680c440007854440d40c0341c950990f818100002e550804031402042060400a2000460102502d400108440140c000075400184d444001e10811072011500c040041645040200c41801000407251550720094411741c0c1c11015026201c082c083c0d003000b51074450b80da0220240d210021800840c44240320b0203140260504074802c1d01400c5001c401d02d002e04d44000d1200340c03150040d00000c015501c420302d1000d0000039102c540340794541c00c1c6446240404086400e0600c00d400785d0310101c07003100080105000c02d00c1121404d41c03141c407800c1e0124a07864200701c11480c010b419110500343c0909030061301c000703ca20f440040d40c00145846d0500d07550741c3d0315000303070200b9054ec000518461540b01e0300135400c100410a5050075100000d04000103003042080c80440424860001c0b510044560714544400d81406800842c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 491421906 1250 491420656 491420687
    0x1080f2a04050a090c0e03070b0304060f0209100c03090b0c1c1103030f0619051e030106180603050705040b010210020a032d0c02010e0d0c110603010b0c0c0103060f0e07 74
    0x4031400404c682401390b1200d0401140b070f03203072096802c40001c00e16450f96242d204580954409000040209109401c5594081030070400103280c200c03e41d0005604048506070503002988861500d800c0603002040b610140020302c03103940c1071003040d07640a41d43c0c20a612015030645540000000e095014110f1000440291070a981d1245031514812540742c1d0b084030201c0c42741703018583d0b041035001210742d590103449014105851314498010500d44a0310f0840c203140d01907594500004800304c8800380b04280214900e004a0220715500348186800c070b503034000520807841e1403040380c000e0380c001506680005006e4030140c0c8884140340140c00410030079a65120445071b00400c02da6560f0030441044001c0d0f1402c0081101c892500c01c12822165614200e2585a200d11525400d4901410140520a10407002c03560f0b048900070101d100c60700207074441c1489a01c08504000d603450f007407212110003902880c0c06c12505142c55094041402d413481009100d00750507010408040c0f02c3c00c10881c141d82c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 491423156 1250 491421906 491421919
    0xf0c030714031e0f070b04050901120c210b0109050601170406110a03062102210c03030d050f161d060d060e06013c1e030b01080f2a0405 60
    0x341e580d00c0350348980c07070020007113640c0c0100c078000b0070200182001e6809440c00030707146503d01e03030800020103045000d2600030385030348030340610001304c01c401c40c80c84c1da085504000c940f46c42c50496207055001c145042c1c1003d0b10142c2080c040080c00d90b131000701c00061629410020b4030303079269810000c00401611860b514100c1001803680d0711b85405400a00485052550015412460381c00001080340f030020025844502110170740003020b11200d80007106c1c0c0c1607a058070f00c42142c25000902d164030020308240060b4464040000c216840403100747c4c06000c0e0303400095408940c40c001084080c580620140e20700c5020749940c030300d45070041595420701590b041004000c3d01e4030072484000e4002c650702c0740080c400d1115480d41d503e003052101c031128842c01342c0c5140407407000703401c15142001002171410000801880585070594455880c1003400130703200041c0c5110034400052628200400c1e81c881c50140714148110311031035103c15002d01c036014250307011000f0026610034481c0300e280d000590058 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 491424406 1250 491423156 491423203
    0xd0b1e0408131502060402041505030304030605041b08030a0813050303070909110c1b0420070c06030504230c03010f05090c0d031209020f0d080c0f0c03071403 70
    0x248200400c1451103151880b00c1059544440b02d004101c3d0f89080e0300140c02001c04500141800e030440050942c0c0c589075000c03519120f42c042451504117910a4030a25111380030b0005210350181c50070035850080c00c1c040002c1e420419400d90305e100c0d001c3e1031020400f00000066540003028800340410742d108054a0b600c5c207007802c0c01001904240914040d4929040c03c107407001d5400d074100da09a00b071190107820446440e01c0c3c12280080540c060742d030041d03100c00441000c205100f03070350814404402001c540ba410507040160b01d0b0388454005d00140340ca40024000414070799045040e0112070040d01b16001c0005201c1d0364103150301003e82c113801d5806d01070700c4014044950800f5104e00090000c41c0c8642d50824200001c10395909005000320b144085010080446600400c9c540ca0000c3c040c06081c3c550a00803c00c440300b003800c1a2031030300c00400d840d00065420712401c203981e414400200318100c03242c03000a0b2246a1441032584805460000d46030720b450902c50100c074141c00408103249107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 491425656 1250 491424406 491424413
    0x22110c010203061912080c0c090c070b22020f0d0b090a0b060d170f070c0303080403020c090f0601120b060406180603050403020c12010209040e0706120203060d0b1e04 73
    0xb500300760f0704039108000405000c0003070070600f1503000072140d46030440301024030280c43d13490141d0300502070010280100c4940f00d54030b485080401d400f480040520306d945d841981003071820742d00f020b00380c03c00420044011441c00b0440f140c0c03803100340c4c1d01110150540481880010241e90f51140010814404042002003088020403052481406442d44c1040380c4d407070404002100000c650024100c40c0090701e4a98590960800380241000024030b05160170a59140c072800380e09645d00840000e400b007401c120401d81e0602c5100d00d01401500d402c2e09a007068240e4260182000388500e040043c8100710301c0d15001079400c880200c883c0940b1003a5129100ea60081080d1051208110702480c01c8100242c030300d22034440d03d40b103580c056000e8140079002d441003028000d0312507040c90b155074091118241c19a41d901c640c01006405c03800802d0030502c2d024010788500741d0008a00c80c801d2051040103806e803034050a1021403540302c0340c0348c40740340e80b0f8551341c2d00d03c800e052103040080b001060410041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 491426906 1250 491425656 491425661
    0x2010f02100c1805010825110307120909020306030a03050a03061205100b010f02060609041a070e0a060c08070b0606040b0f18120c0906210309150922110c01 69
    0xc0a5200c2c40803c00e07a440d00b0040d42ca00005541030403100d1981080b4400400358805201204803042c50440703401140c940041e850b6030480c0000381c2d00324400c5103002c590544c120340c65400421464071300303500f14a040e07000a078940340d41d201d0185c180040021503401843c0f00341c1c000b0001e0110101c240c06114100d0074901e588010058226522070b28000000c10b41e17601410368150744180c2d590043c141a6602c1050100d444405401166983c040100140900b04416110b92046c8416942d00f044002d201c004c11580c1e440a601071001d002103c03950030081402e500444070540d81050381c0c122580c4504006c0750a0303206590143c0310800d40882d51100241004004042115085040b649503d09507810000040408009401190320042c150702c0d0b030381040b42040d580200e00420b80b11015011080e803a00240a00b04009081d41000415100628210403001d4905032030711401410a0b4240012031801c034020a440340b400340c0413a54082408885410001c2410140100c540c1c40b4400462210301 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 491428156 1250 491426906 491426927
    0x1205090a170d03060e15031914070e3913030606051915030f02041e150f08040501020d020d020403021f050301060c050a060617070803030606040302010f02100c 70
    0x103801920700742c0360036070310030b02410b4281c941520081906480e29000101c20030f0058884c01c1e014041d540741008040d42e0608051400b82c0074403891242400c900b4811410503400da00500b098203907403c1071090110700036072031465110381002d1505290801a804040030804074900c2ca1600ca00051155003044218140600302c0c0d02c81c0c036060209544031000c005030100001145020b250303200f1000c0100e650800c058110001181c01c0000d4021406050700c002d0313a109801c0f884458408140104c0d07108070144900cfc000700fa42804201000002c00f000801c0d8201c01e084207005c100702c03a40800c1c1401001c0d812220040e681d004219a42e80007501307520065007213480117902c00c0800b0300b507100e240030b43c0000343c040c0d4259568402d85180e003440e60035600c004999405640324800c05000d00001400ca02c074400181032039190a0601e08000b0305854505a12600142c041c0e810070b10134032071652100380c10395064a0342400c148010000300c2070101d240c40d45282c114030a181c00c14100d00d449a401000c0c240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 491429406 1250 491428156 491428199
    0x901090903090e04080f0a0315080c010e1507030806130c0e0405070c11190504051314071202011214070306051011030403020d0206090a06021510030f1205090a 70
    0x70b4110f0b0380d800910100040c01c890103055040b0822607481807548120081590b9101c605000032700c08141540b072401050203030040d507030715401040c005840350b0300400f02175090b030b03401c49000c400540c984912882c68001c0d244002c06010103140400c481360790fa00d133400c004001c8000208081040904001c1a0b403d0a240307030b9000e07505d02030119400c203205a82d0540003d8014280d0b0700701d80b2008042c00518801d0152819020261400102c3d096407940500390080100d410f11502089131401e05042c00444460040c0707107079010b070744200005222528009020342d02400c3c440501c901d6080400042d0024103282815a0314110820241c1c03600345d44080161403065034031855070716200300c0503940c40300c1003503101e0410340c4103000800040c5801220315000905c042c1216003003d40c04800705140d00303400c5d001900540c001840560201081075142071740720501a171282000b6246885071300c128100c03914086e0640f0341034108809110301030f41c21500d5400002e800007810702d07543c02032001440340d1840e041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 491430656 1250 491429406 491429417
    0xa020d120c08220f030b18071e03110406080601181d01140a051b16020d030c110d02100518221109010e010f030b03030412021207031205070f020901090903 68
    0x41813407400340c0420f4080d66406810b940054465881300d81d45800300d040c1c00482440784178030224110707541744442d13418940b40c4c4444510751400c6242400d2140188030ba080d0166240c44810069944005455811524000048040180d4224207480548030000c4a03602080914114030400081540300303445d154810b400d000c40ca521221001002d595042e1091851102182c03e007044402010300200040445184100354640140e4040f444110085c031082d070100301a0110102070041611049000c1c110454800d0724011855000031200b13181c904004c7c00308030f00440c0d40c0d0780d010900c403205c00d81204000c0c10741c0322415540d541e2800701c00030f0040807080d070741c105a842d01e190103070768060ba102c2c903805850b41d540c040b103180700442d002c400040c0d0349801c1584030300380c55105803414402000030304090842042c55641034014040030700a41081c0702003c1d40250410808203c278032658840e114030b00d14102d65505600d0428540ea4070421901950082d4010000100055641e00440c4080d1203501c44 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 491431906 1250 491430656 491430659
    0x316060f02030f04110f01021b06070b0411011b0503120601030e430b03101503020301150c02030717030408030301080606090105031506010f091e050109080a020d120c0822 75
    0x740600f06c4202c0c81860b01683c080248041031045584500d8010304015211a08200700c070b848500d40414199400e03a001d200506031443c0030350748145101001c4880292101d4403907640c0d503c03180d41e40b00d0140100784191a60010608903031281c1c000500e1030402c0000c40d0b00c0000f040c00092200030040c52190f04090943c0207a2054010700345000c0d49903502840c0c4011181d02e8600300703000700d0b44010318079402e00d8510000414549140d02c0c4421700602d1565005840b5814210304003110302084544c0014008070200c1c420060b90700080744020780d80010030050f0300c4040c000d14189580a03a0b00094a1400040004100e02e4000070f040744c03065104031921001c1e81d07a1441850349803050403d40e1004000c640f000500e895018a50503420284c01d842d15804207991030303034103002400450800b880303480045d00c01000150707400307060380e8007600d910005090041d800b40e0010308145035001000301a15003810390443c01c03500804044a4064020710f0f80c0b60b03212681030810603080c2042e0744081641030031880 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 491433156 1250 491431906 491431909
    0x12020a030e0118050c060703020a0b01030309080c06030f061509060c031c05070504140d0210080a0c110d0c1109130507080a03140928030c14030316060f02030f0411 72
    0x210806072031300100903103980110780d0b00780045a8000c40050f0103600c00c1d1810000000d0b0f44c5000e941c004d601aa841501c000d00780341445090048450109104020610902c444441c00e0324030650084000c075401c682c0481e420f0312052050140c40501a401000400e41881c82c40c8044000e0041e4030031211598590105101804100c0d18141c5d20040022402c2c0f10520212510190581c02410000c14001c07190116600103000c8828800071000018400320501105032400c1c003130f010795411b0070308100c1c0b00d13132481d4180a50b6800c2010050390402c070a9090210078031003004c6003520021000b9021192074a040a481803083c1d0060404a91900c103113080064445400700d117140720940d1541d12000b4a210b0800081001c1d0440040160322514021607107507040120b00c00b08000e40c462000141c061403541c102007001c3c11a41e484480c0d4486071038440b0b8600d6601000300c40e8141000c0e0b5480300c09241d5030070014020309414401000d03151001080c403030042088140345200b14820401154448440ca0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 491434406 1250 491433156 491433191
    0x12060b040f0b182e21060e070f1205090109020a0902030108071206140103050c010201060f050607170c1f0605030a0f0611090d120306080a0804030303050712020a030e01 74
    0x2410780509861103002c1c940c140c079018540c800c0d6201608801000100745100d8003003000003041040c03000c107282c07400c0325112070b0080380c0b84500012142d204009880c9404001f00303464000400103000c120b0000700d0803030114000c15201d080d140010f10300704580d00e403100240d8004d05a8007410b0f442000b82e4000090303651401d00032217050303d200401901445240c4140111880c0354410708407076554035490799950307806410059a000354011070003400d00c940f404001a0844503503402c80f00007c181c5600a00241c0c40d094225880d5035404100c0c01711180103062484114064010b11701c010b40202580c0d40105850000c1d042c20000d00f0b1f0700300700310729a45d4204050b5a051182c4008161510410f5400c02103459a070281a0444800c50b86030f14107200400015110917000740111040312400340100e500540c148544405480c0c0c1c54003c14049101d5126100c0354000c42c4002800c0540721000204240d00c51404002c480000060a6484900c0d00030050090002c905030007003a503180c500e40610401441 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 491435656 1250 491434406 491434417
    0xf060906091009020f040302030a470c1e030105012d0e031014090606030f120a210e1b01120906142502061e0712060b040f0b 55
    0x440c4500b407100c0c40c10b54103001940111560360300010080c400000584c605210b40c241840c4561454003007804e10b6800744000f4500000d48006440381510b6a182e4078082441c8005103200e44601403546030782c0c2810280701031041e0000701111091031216040400d41c124040d60503207000340c9400c2c00d01c1c54131900c2d01400040100c82c1d11905040000303112109405803404014002018050b100840c600c68411001e450741d1031040103680c2d0f4221700304080104244aa40e4000c03100314043e1084051020a8591b1030b102d603040c2054203180010030500103400390320400d94004c8680c42420004c1952104107005000c03030000c0f21018003070240341c4440c05030784001416003210705031070390810104040102c40003000305144c2258000d59070350f0a04500001102d130b1511543c040380380d0741d00f211038040184060920654140301558020b0040c04110301003c0300359401c0034003a4007007075010794504100300c880c11310300c070884141146001c0700070514001a40042c41541c100c0c803201300788556101d041c4c048920a0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 491436906 1250 491435656 491435671
    0xc08090609062403010f020a09030501140108070308160c0e041b06050318010b0a0f0303020d18090b0d020d03030b010f020316080c120c010614040b0a03170f030f06090609 75
    0x340400c0e0500d00b80403401010000f00b0207400001c1030030f008100a8120b900505c803c0001c91021101001000f100340170701c44180c0e02c02c9046213215454602e006950f44168080142088004601d100310401190741603e04150001c40a280342a55404003400420303090360181e400c2c0c181659500f1010800c2d4190700300320b8959640c0c40785181e03680034011281c04100f05181d0001c0d5210844103503507544a800c207038081c00c603407641004114510f00c0d0181c54810080c4d1840c0500c03402001081a007031042640408a611100000ca00000c0600004e0050300030590029806111100e1281c01c2c187c0c15405904646001e8a4081140d044060b00b60381d2400750b00d01e1181682c041c0e60109002130300d650f002e010303020006c3c42101d03103141c04550005500d0f0011850304145a41d900c50822051048000202000805480410020650b1004100007500714000070345040c0038058918440320044c400c071030000c0c5020944c0740d100d0410b01800140b903002035802501c46c1038040c010a1040c5440711000b401001d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 491438156 1250 491436906 491436931
    0x8010506071a18070e0708070801060504030f0602070203010507092102030c040e0109080f0a0f0903050d030903050405061303020f040e190206040b04080d08250503100302040c0809060906 82
    0x658641000c1103540050040f8480c807a0000901090101041050040c01181803040d04c02e261446004086d510000d20407010007444000400c4065003060071641034035081040440c00d181c9505050000c1d00c01c00600a401d50728090811040310341c048103100070b40d449800d0061104c9014162060980c040c80c00c040d42c160400880300b642440c09074000c89011030300c034002041c40c40715511641c0c1950031050b00401446000240e10751015400079800c02080c40500b0300800f51802d41d1101030783c0d01070300001d54080c19a90401d600c1418026001d940050500410041d500d200d20508250952020300c0200d0061060020401d0986418028028901e00b80d200034000d4140c1803615000078000362405030f80280b0108408240d00441e400200080d290701c80013403100c0104840001c002c802c00900480303c0003061608a600c855420919000c0701d030075480d20a880e44c03034914010040105c9540300a510601d00300144100c0780d04000d50620038402c42007510300d0355580f1000a903c3d10406c80d09840100d4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 491439406 1250 491438156 491438183
    0x2030d0e0115050621040f0309060309030804141203092505150f09030303070302030105010f0f050a0f1b050a0c090204030b0a021b0709051801061406070f05011b0801050607 76
    0x10001e014228550307001c90302e0404103810710710090014400356003e42e240f0101d83c002c7c1d400d254202c680b035001000d003840c00304403c0640d61002080864040c00c01071240320500c8031510180740401c00c2660010300601455500e06020383c5c06079881041e100d102c4036403020048010881c130030b900300d60011030700c0c0a04106107180300b0b0700400d6800c2d800861829400b80c81403100c8003117600c007000074600c6074440b5200140d4075410600050b02c0056460121003c01083c0c012501c0c1d8180e205003500e1000040741046010007110300c03001d90b50f100722800c00c002002100710141060110000e04040f2503400f40f0f58140b00c039034a5070701d028141d115500001d085101540045408402103900a20303000c9031100c00310543c0101c807038205003460220790140685c207031990103022402c91640c4040300080803c00080164a1421100c40c0c00d9100380c4c80d20911641020580c0c1c1d02b440341d200d144840c0c02c2da0140082200188004040c03948084074141007002501000001c1000d0420348122194107802c21403070400a03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 491440656 1250 491439406 491439409
    0x609101e1e03020919061205060d050a062f0d111905070206091305010303020c030d0e090403090b0f120a0207030c060b0a150809010f1401030b06030a080a02030d0e011505 75
    0x82d80030950304d03a089003079200c480c42094201e501a81c040c1501e5524542c0380c190f13211030f910580b04041e150f02e22aa00e4280084c0c00510300069018a00e41c0c0204003188140200248480c07001821100d920b40005190b613000301c146c070010040c4a5803201c0c0b182001091355259900005024142c0b13980c03624522011515621030041c806484451b1004120034981000e020104545181580140c6201500c4100501c10540c06100c400c5101d14207400034050750198003001055841240c00180c043d40d85480030405061191072424098610400e0302c5036100ca1b6801441d030998003d040341a0700140180214400b0001402200d0781f503034055417031010012140d202c0304000c003115103240d54440c0741074000064400c500340041e20368007044e88aa400034034090340d5060075030303640d0944210039620305503a031581f9000c010840c0e03040d6600000280007039a076050100b443c10400b0b643c041e1400c0c50106911281d240c1c004000d00c074082c00c102e4281b00303501d082002c80d400c0c4c800024240341c502c501c502091059 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 491441906 1250 491440656 491440661
    0x30d03090203070e090313080a020f0306131106120c031006140a030e0f0f010603060f02070c0303120f020d06060f08040506060402090f0402040312080f070f0e0609101e1e03 76
    0xb02444007a2407510714840e143d10008010791740142342d16008200d03010294604008081600042907020300340c00e181041e0400c0404080320740040000d003011b8880b00d180d440d03030000d440c221140d00c100c40d4154180584d00c43c00d540c0041728507001600400f080460301500c00c2c410005040340c00c84400d801c02c20600404c1e00034002682034104070303100d0184030002d144010018141c000750302400000d01075003141404410f54a401031075a00f0b0b50300400131400081d065800e002c080325050300e84003410703514114a801c00340c550101e46030715aa0022549440b056425401a412a100c6032160025980d02e88410395080c01d044801610700e802c860001601401c042d0010078801e14010594403842c915803000a0898000f604180d0b240e2248400720040990002a5160008080e903910085841c0c14070005007100c00d0314890340b080110759240903503503407504402d903100e05400400031360790180b0701400100b0040750000c0c0300395014089001d03404110300515850b024a144056001801112079900303801 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 491443156 1250 491441906 491441911
    0x50324090a0e151006030605150f0901180311090a0504021f140309030306150c03090103150306020d0f0f0204062f0d12060608010b07060b0609030318030d03090203070e 74
    0x55402081d82159500d4040c0390814826440d84013000f2603141040d8000b41113503110742045c0d000d1440d1f881c0f1000d00000300016180904400c0195030b82d00c007482401228010101c0c01d0044414108840c00f20822000e00701c1c00d41029025a101000355841d50089000d8400590703001e50080d55890f10609907070742c00e00d40e21010043c281400d16275002204038101d6254412a002c8500350400720501142d498441801d026440700405001e00302059421103a440e441110b0009040c180c1c0c0e41586d11141c8001c40d07040000750740207001103403105512081503016003800038000c50b8181c0350800740d100380441803094505607059503407154402030f00309009030110741d01e080c0401555031000481c8150000c0c2048032000300d090590300d548509031407a11b20425184680c10840501480c032006000b161003480940b44020b400c17240c040360aa1404002c504070f4407800c00104c3c5c05000004842c00c84024404000707410f0350003a0111401035120f281c0841c1280c8400c02c00035032540001400300115601c1c0e103400703074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 491444406 1250 491443156 491443181
    0xe130504030207121b0b030f0f07020106270c110309042304031112180108041b0803040509150a1505040518010e09070f0501051c0507050324090a 64
    0x190200d894004492407204c1e281401c80c2c860283c020302100d00040141020010488000304600b1410010762400c0c1144d002054a12240040030001c1c170344501c00d40015000342401040400c680e01741e00110036449100c2c10b580da061070b0901405c01843d42c0f00d00800d01c04102d450000d140bc01a8480c2040098070391440300302010b090720394040908042e0000300500440c440d0f10303491240c1100c0c8000713074102146680d40000c2d00c1d00512055081201c180e11500d00c0a4007481e100001d42d0b81c0e881c011070100a001c0c0700d10b442d005101c0002c03c04801c000000c0007034680403110808c241d070720806d841309240003022000343c00940f072002c100450041c0e8450500d03082d056091032814951260b021500e031005460045050000407401040b0f84204407042035002003040d0701402d0300b282020800a040b00700d900c10f5a0411800103181851114071600f030031110f00103050280005d0070300c2c2c0c000500c540c0058030044148490351441c00e0440044000c58141d42201403c8400c140e601d907a5401c000740a044c0c2000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 491445656 1250 491444406 491444413
    0x317100b16061e05040c0b0901021c0c0f050d1d03030a050901140c0102030117060930130f08060403080105010e130e0a0c06030e070314030c030c0f0606010e1305040302 74
    0x80f111800030b1803215203425219103001402d45818200900710400075449905403500802501c0400c1c0d030f020404015525450071244652451420100e90315a18600094522080c5446c3d440800c0301c0412490341a18680c0d0319645030441496040a10302040f0300c0c1954140d0040001d4250b0b0b034018005019000c4050600d559803c603100c0c00002d140d8030540f50b403440d41e540040148030241685035425040c4990070010601031400e02d180598420204481859065035420802c032084c600340d81c0b02600e5110080200d884603440400740c5030ba4001030285090881402d1004519500d0010700c4621581d015a00e8005a920b41401510f03004800d6803d10b410504110140300111501d0265007000085640100310241c017900340585003160603007254041504050140000d1100064094156600858040400309002c0c43e100d2961044002c465590301000c04c400d0b01460020a4500f644056401a210155694001150f00b001c240180303e50249440c00b00422002c0154402c5d03901c1880b90044 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 491446906 1250 491445656 491445671
    0x1e0e01090e0708070b0301030501111206010804061506030902030d110d080702010f05090a030801080f0705120a020a0e0a05010b03280f0f020405030f0c2209020d0317100b1606 77
    0x1c1c3d420a2225080700000640000040082003000d01c12595001114030180741071400e03800307a01ea01d11001a00041c10010b0140210b02400742562256481c07a021891145046070b4a07240600506920385040e407190180c5807089811b01c1c02800411a40e80030f01c4050095084490b00550f510140035000034110340d40c80d402040b4441540c403425004100c8440240011201460000d0074540142c210090640095650031100c03800010100203483e01146d26800d60184184120314021650070044d6020807001000207142c0c6014030134500894403a1420300a0340c0e01d992100e55a844161035203802c0c521041d0015050108038400400031021000003c180b08084d40c03407030b006a0300b51101c1c4100c030310717070010301040b81d468100328000130a03180d18090040220203a00051002243c030f80807100c403885086980350307054003d901050314680d00400242400c4550300713008084c10415140d60f0030020034030000c43d0501c0340d01004031088401c901c1440c1d103004100c1c8a145d2900711b01c549c1c2160b080d82c84500c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 491448156 1250 491446906 491446919
    0xf0c020d06020c0c010e060316031b1115040c060509131103010f0621050612011e061403060c0c010f1d01050f040b01122301061e0e01090e07 62
    0xc503184101d000390005070f02c0f0360b000c858842c100840010003505100c14010082d100781c82d240103070795000c0c4105c51440c9140b080030308143c2c064402c0345950281c0c0b02c00010380c11440c43e00b250100041404020031620050101c414030700750040d05441c080d02c00340e08840200301840c0300e500100101d400c0507100001d00d40201c41c0c90300580710440d1000c0d100b10004801803250b0b1218468010040c0302a20300350320308000602c4055280e40070400e250054070740303990004d40c854403054502c507840c8000034000c03c00101e181c0300703003508404585498054142000c00009002c00c0341d407544501004000e024040b2078580780840e4076141d208514914203952540c614134688012440780040c3d2030b481d0f1006501240c2d5081d1104e003100c9004040d00c80d80c1a00390140400318002d86002c60548031107600b4000381c04010700b089000c0300c9543d2142ea1000303c0746070004d0f413990010b400c0700c0e00b00c84000b20380c410582483c0c013503403044580358050222040c440350300401150104e50000c0e050182c00c00705480d011a1aa0b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 491449406 1250 491448156 491448169
    0x230304140d020609060a06030c0b0304060204030c06020a0606090b1f02011d0c032811010e0d11090721200301060c0b1005060403060c030605040203090a1a090a030f0c02 74
    0x554800168103e44100118040244140380d0704c008612000c100c12070840d0346a481132020390255000312080400000c0030405160304860107580c102403000075017582e80100a5841e8002c0b80200c0b007941c00c10500041001e494004c24030003038001400002664101c1c0d803595070410202c03214904664942185000c0c000c60754100210308403560014190389041d0800340342c86c014508402c070b4010144810fa40c024414070381c040456580d0711200180e40200ca10740104c2d0b00d151101101c82c0d2000f5014005070401030402c10039101030000752964829907440c070405441181c0c4410300180590401c0c00e0601568609034400982022000200c1c11074005580245040d60000d03089030b00440d44044030701060240c4059203c1d4001c0344920700e41915424980072819030700451000429580d03c804c424409240660461400781002400c21511703850200e50590f50f81c20310700f209803500e9601d9261000301049000c2c8051103646100300401c0c901ca4141e40c05c8414180c940750510401c1040ca01d9200141d07250f0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 491450656 1250 491449406 491449423
    0x408010c1107030308041205120a0603060e0c09011a0706111c0c050904020a05160309060e09010b0412021203030a0f27030e040b0312040f0623030414 66
    0x1000002084280c64802404065200d0704030116540040e01c20000280d2201c46960f025a1044080024042c1c52006481d1802401941c0c00512078030810030082038001e501c040c007228010340d400d0203514901d2030036580ba108840b0005030424441b100610001301c00230342d4102400500710105103840042c0e00c40100715a6081c1c032500d0007840000350520703040c1c42c0c650351700007403104110b0800800b03c00c0200a0000e00c81c5101440c061754002c1601d44400d801541a075a0302c1c140c1d102e040850501c5803174014801d0005006d8580810038409800902d0f0800d90180c0b81a0381c10321140038502400c2c040003695107000c10f0812030340080b5810303809100140520156005103800e502c00b10300d181103140d44006569100c400b070034602c0140c54002e51042000101120442d42500b071840180b03c0c1038000c43c0280450451454141c4280c012100d08550468010411500141d04101c101901c03004110740c11184d4203c441060480307120140c81822204008503002440f4460342428028003403402801c4c400030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 491451906 1250 491450656 491450669
    0x1507060204050a170309041e09050f0106140d14010209100314070309030807080604060f0e0103050105100506070303050c0405040603080c0f0d1b05030d05010b0a020c0609010f05031b04 81
    0x1050801141c1401100680540313004448000902031601e03207565a80942c40a0710700c103d4840025180441511300c0742c1800810210041c03040c0052810b18543e83c40c1b0320302200819610308800000c0e140c0d810003010500c40b400422016400c400303601d604011141074001e02180f95420003840c1d86668401104003404800e0f034401244c80c0030505801c80039040001c0c0158185403d00c1780800000c1e0740081c045904c20b025040c12121030710341402040060189070040f0300c03003071885c540100c1d4800364a0b44060480c0c4c411002441107541d00a50144c00022610419801c024103000020000f40250410b035849840043c031a4101690b400005058494603031080c0d031141c0e00080c80780c8907030350107104480c1c5541000005100b40700c0071050050801155402228020314805c030101d041013401d00840380380f841681000e102c0c1d941c50300ca4024155000c02003501c054801c1840c00009800e041e001d0f9001c03050305840c1c0985042841ccc4003507445600040c803030322443c0c001ea40e00c000d00400003405400900301 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 491453156 1250 491451906 491451911
    0x50603100f15030c0e0f010815040c020a020405060d05120703120c03020c010e06010302010e04020a1715030d02120304031b0614011e0b0414180109090c170d030b150706 74
    0x82c03140103000ca4082e492030703408001d40e00d099082d06460301e5140c103a90403404c0c038242005541d0400d0702c074030004031100055806802c1180c4001d006134002072502546008a800700240d0b01c40c0d00400200440c102d8005029400150409000c00c0c003c502070702020b0f000741062403507004440c0d804403c80f03180c0d00b4180c01182d80030403103140b540400d21545110511050003000d26504603000a00b480c40003080851043e27030000b03000c01c4c07428862803e003d5918011800012107051221007480c84a5031008a18007a00c14040c5e03d6901e90320000f2414502105c0c00c0383c2d20301d1501c031901d00b100c4000d1800c0080c2080982d072482c000c005030142c401c41440c40302d000810842c5504121611901c1005100c10501c043c0152074144446184102240d0840e58002005174400c440c080100d6404820031048000e020782220000407194040e410080e02140302d96a15070045444213030a40c3c490310010200312496024010700700c503250003580920341d20f80005000035400d0300401201e040980c010031049924a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 491454406 1250 491453156 491453189
    0x5070312080108030913180f08030402030c0306010311040b3d0302040b0418110d021c090302101e02040306021b01090f080d021c0203040209060105040807050603100f 73
    0x1d074407040301800f52042d00c01031480c06030701100080f89600300d1210f01a805a44070140400c840d0364043e0200d1141d4130074281e000020203803d1410340c94004031403e178003d008003400c5628500d404148203060300d0380075030728601c42c1c440da0b01070000804003601b03c0c680014110746170384050200501d01c03007010790100c5e00c507000d040100c0549176100b00b0869941814540184010701151802c0000e54094800300c40000d420072082c4000310b400f5006100380c114260b90001417480310030703030690000d001c02800d1081c00802000007000ba90103c940c80317000580184c0060301ca20307407070850a40141c0281c6da00c0c6036104c0b1515604102c000300700da000d0342c001c580f419800100c000c150450411116209503108008101c01c03003081d1a1007440e100c050710f0003000c074440000d842c510418998107440740d0ba26040403114141d101d059402c80254401d4030141e01c90881c01c8001040382d840b49048505443d180700140400c0c61422052204903040904007100200c200c040c04100c4010001c009402018450390120803030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 491455656 1250 491454406 491454443
    0x1902061b0d030e010b011b05030d151a0306090a02030703060e0c0a0e060f1b070308120105010e1f0507050f06040b19020c1b120a030206010f08060609040305090d050703 74
    0x101c0c0d483c080210700341d0400c910a40f040c1c2c0c2201d144500c01160b07800c104404045890300b14118070803074041440e810b00c1c00e114036020b00383c0b1580200c01d0300c003c0e04c61002081084060101240803c480d03655103c00300304000703400b01031075070061504101e084c240030451a40301c244013841031308210742d41c44103000041041c141455002e20001401300c07041d203246181c5002d1500401c01e82c82240009002d6914403080c024101e0310400c5103200070740c0c010740507a40b140842b0419480c600801c0c410b1600041600008114624049083d517810a00703e0b1124101540c141d81e040d50035030841d110564060240301e0901c100c10300c05001c0d880c45280b084003031441901d403100120300c00b030b6061162040c0d1703d0320510105803400300002c0c1088842c0d058816840034058011300142111352151001d200d00d001d290010710402d034002072480d05880d07503c4c810741492038440540c0da07943d20003200d0480d4018005c3c808200402d0150008054980014001d00b107081003685400d2b11305406980121000026040081d81302d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 491456906 1250 491455656 491455661
    0x3051204110a09200a0c0507030302030409051f03140723010f02120d15082a031b0d030507050a0b01090b01050c0c0906030f19020a05040c021902061b0d03 68
    0x686103c1000b00040911080c00ba01c500d0420040242c103c103001407400c191502449410300582e42c400101e501c12516460002d4903500940300b0540c200703080c4000f080721200080a210b980d0313140304100040303052464880d280114850b4007140d80c240510b20001c182e0b2803c00d040062128881601541070f910044001089107240381c1c540421900030354654480414984201c3e8a800c004200100307110381c41068016000d1510350008400d4850006181d0201e0000500c0d08210200003010700441003465081c151509420103503142e43d40164803c515540c40c0c51011014064041c1c0340c010300b001c2140da100c0c2c1c80c22400205c10b81d10300d600c007001004261141c3c051007005070310a28041d8204144071007829901c0c07450a031428462405840024090345042200480900c02102103c26181c02180021040c04078040d0503402403045503004900c0d801c02d0300030011407003140e50081c00600d82e4204000308918200c4003c03640030004010000441e6003004100a00c6005000600040001258041d04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 491458156 1250 491456906 491456909
    0x1b0f030507030e120714030702130b0334050a05010c1704030203161a040b04030303050402012c120703050606010518270a06030209221a010303170c0307030903051204110a 75
    0x400da004008c40c1d0016240d03080001c480c1440d000020960745031800009013002090305400a103103500070200050b198052140c8401c4260300314940541c940c5880500941c034000303002d01070205546008901c0040c5007444a0f074011950a04103506098407640001e05010360a01c1d08045018500c000740070752044042440380540103120310500c0c243c0341c5220004580981e200c09400d0543e200c001505590298120f4440031880d6602034040d580e0668102d02091000f80c030282c002d03041149110604840010300390152a0094028101c0c2d45d98200110740580c070081c10146e9002079010030040c0d0751039200740040c15041c1c8500924070405400c81c013601943c3c00501200361203042c02070410168442c4c1d04d200c1c2c0c1002c3c200700840074101c81061500548103414000401c00c450303004803160565482d0407100d040c1d83c401e03941c25542d102414121108150147c4d0504804d45082000c01c16146c0640c0c021303915507203c1c2c2403a509007a40049000014802103c00760348034681d2400c841020310f0905d06100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 491459406 1250 491458156 491458193
    0x13140702010b0a03020616022d0906061207021c02070504050a02070b01060e0a0e090a051c0807230a020c0a0614070204020702031603080a031b0f030507030e1207 71
    0x220301851030001e030a01c103c512000e4040d40d400034004c281001600030b002c0e42940c015002d44001007491384c4c813070841100d581625050306c0c2a401008201d00d0300740341042c0940801010b040c14000f11090084481002078841015841404000d4801210303940180c0300885c5250040d02890f45000148403c4e6000201540e900d180b0402002c4000354080078154155040c920704444110300d00c0c2c02103544404181c100c140c00d506040108250381d8000940c84400c20b1048080c5c6040385140100b00c4902045400c2d068080b81d00040010109442907110703070a04000c0b4a00801c1ca01a1801e418549a00074456000141c100c24604000c9042800d101c01c010849840c140c5c1d070202400540015074003854400a115640014140e415940c0421801088500050600c0c0d1556a40c0c608420241d1081c1444400b190415112507420708540300c4021011850703858044841034034400071001098010b00b40801d15642d020001c280c0403040100c221881030100d00c1303980d91001d03806d2000c0c10b0005550b691 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 491460656 1250 491459406 491459411
    0x3170714012f220504020403240501030209070e0d0206030f091e0c011d0307060503070e090c030c03060d0512040306150b19170709090e010903020616030b1314070201 73
    0xb40003141c1d100858101d00c04008404441e291000703100140c500f010760002d0750260000c54040140b00c0b000d2085140c0070142002c4000d0718076070b20f01c4842503407424440a980f140c0301074001004640901d0998904540003401c1c0182c1080942c00900c3c10b81003600d511680f0802d50742048103e44041151a03c00c207a050f480101160b914105a0b54a81c02d5140090401c50341500309454a40384071406507642c1d82c000c0544400540361800100140c00c03c4489500180c0c04404c52007580c18a00d038080d02880000c112a465980c07406c8100d459684043c3c100c50300409208100d10100d4004e02c500c1c410040607987c0c090b561455811300c042034543d280c0d004082485106020001c03d002c682c100c902500c2004480140a21905404e40b45002689690324000401108000715194026100030584265400030400c2001c1009058200e46800c58010091f070302c001e0100748440c802070248074100c02689000300d484081480890814000d59400c680c40545641d0f0b11440300c003a240403194010300501c001c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 491461906 1250 491460656 491460731
    0x27080406050c0c2e2f0723010815010c0204050c090406080105150915100c1208011a1801050c030403060609051e07020a0303020d0f0207050c0405100b040317071401 72
    0x400300a841d40c01c4482110102c03000b8030302d000380d0180120001000c0054442c0a40343d1407c403000040031405450b14009021000001c0c41401031181d9800c603034030181e4802c90403041941c00d1000406001d84000c0000c81c3c140700103100d95481b0f004a401900c401000400c990401000300081c40d10040201c91080242100304110b050041c0010080c540080713a041048822107442541c52284203540030703000580d80710b40503003c59000203c041c100d82c4104c1c584611059004003080041c002c0c03001c5150035040740e004503096503104001904181d030307034107003076a151680c4c90340e402c0222001d56001d0242c4c3ea8640d402c125550b607000400c16981d08441c504032485280c00c070300003034580100c00c000400741903000c90028225101c40e03021006500303d40b10115581d005030f00309030743c6d02e13564884e42c03e21960500380010700042022951104940b0321801e401d040c5030a41d0366070300080c04005290710800d80248450742c00700b00080410303643d44841d28000101000c03495201220310401071000b0002d520716504 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 491463156 1250 491461906 491461937
    0x50d150c110a0b1e09010c08010906061b06020c07080109060e1212100e150910182f070b010501050f030705070c03051027080406050c0c2e 61
    0xc800c440240d2140c0201500d6544c0384100000303007813080c0c2240240c1282d5003000324107170055000c1c0c00c9882c96a100c400741a82e90b44031401c2070314294059080000d291007800c8854032041c14024200074428400942080c01151505213040321540c40501c00d17a44600041003844086d2084100e4401d5180c090440307401c11000303190482c45a4034120240d1462500042c210713445940f404406001e020413120345c14240a800199080d85c0d00b00510300c51a640404109000c203c2e40100084030010046400c0008c9400b00c9000103150903024010324003850240b0055100405100b800e41c02002140d50340c84000c0350403c685d40d004141c0086043c800c0c100060380d0a54007a000340c0b07a0107451841d281741e40e9010f0345418415881240e0006101e0301c90b1040c1c0207a1b5a22580040705009840901c603030b1074026440d060340c11418080c5000d0206a01000f050080501c5038004003403a03185842181c0c0b1483c114400700c0c00040d072484808140c8000012410703c149068203643c0740c5c0d60402d15040040c0014100b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 491464406 1250 491463156 491463163
    0x3050604080a03060806040605091c0906180b0a05220509060d110904050102220b090907090806042f1e0a1205100b01230d0204050d150c11 61
    0x180003501100780451099449032083c0c0101010300541c000f13a4140d03041c1441c040f4040c0200341d0751075101b03005840003e50a00841080101d80300225aa01c000391031815206440140c4c0d4100e029603290f0302d140d13001c00e140707842100800e100001070b41e405688048249a081003d90314075030b140ca00c0007110208101c1560b81380d9601da00070f44203e0f150040c03500b16180c610341c03c070041c03030741c40d60400c55079410002840019800b500603008680424010251984000f40350a002d82c0203407100b0b408107000160076030610401d0f155016015041400100b516503100300d242c281d080700c0484e00841008242100f00b044200e00421040e524440c3c2c642e00079a900001e5501d03030014580c4250000c644180c10a0381d92030581c00e000600444102400d1400c1608046071a01500c040404885042c00b6040b00d80b544203291900701501d40c1c13182044840107440300d92406a000c2c00d6a54460b5070240008189030750751101c0c010318684900c3e10a4400200d201c404010f682c02d4144074418480d440504181044022 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 491465656 1250 491464406 491464411
    0x90c0a080c01080603120a03380405010503010c211d100c17060d05012903010b0a030812040201140406080403030506010207080a03050918180114070914030a150f15030506 75
    0x14100422004440016082d814564124a49003480307501484000c1d400d01489c60300d00100180c4061103640c1c1c85000b49800c3e40c5d82560103c0c0000c4501404010707074200e400d2255692541c050700411213180504010045604014030380f02281c0000304464040300c0e0b10b102e40680381009042010800c502a940d900c2b10423002403459004e01c03003d00c0c0b001d040000a40c0940400b4600c5071a21400418042400d0086000c000240340250700e4501045110701d406004082220303480310b04a86800300c1c1d0b0030000c0c198807001c1d0089041c4941c5c00400c004801c11706014002814140e40e95410514003410000c1c1030ba02c02420315030554000542c140300041c008940400d90340d40606100f80d8440309603021440800300109990041d510903814450580741c00e0120b4107040010100a000f491558403011071440016502980410301e500410003080142c482031011000700107054031000f24650b00c5640c205907039500781c0152155a81100400300245104a540f0b0b68200c08108525034115036a03a071ba03d8001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 491466906 1250 491465656 491465677
    0x515070f170a031404240e01050c040801061415130503100b0907030903080604020c0c03011b18061707020c1824090106080c0706060f060f0503100e090c0a080c0108060312 75
    0x15040b10710601c1551f504450030966a1000801c190b18101c58400700c1504580034405a55082400005030304002909541c50901c00a080c01c100002002c03803072000d03510005000502030304000c000a41076400f0b210442266100c1800899007261080412a02543c000c10360000d0526103504030300401c2c0d00c031420b164172040a03103005076260a0210102c0ca445044d000b00c42d85907007001050401c0d00010b0605641611a07500e48000014601c1458000740b80c0d80d000c2c400000705400d420104421000c245030760826a10b0051f140395003228004036581c0c172100704040e0300d010030b01c005021321450402c00f814a16040ca01c1c1e44c2d244949642e0000d10031034418426070f0100001f81d070100f00c040907890b080300c010742c5e4001401c00400740c0e1004146901000c5209580c041003645410705c00302e5000f001164414905d80719090340143c28808031b14880840980140d00a100340c14001c00107442d100d0580c006403010100034650100043d000400801d001440c19020303070080c1551a138405015819135400d13200307 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 491468156 1250 491466906 491466953
    0x3110306042a0e090703060e07060507020103020a0c0f030914120303060f15040f030615060509040c0504051909060b0703020a140a060f02030f07090515070f170a031404 74
    0x12000010300c8010083d0010740e8005400c0f4107010400d00005102421030b4803400082c0148034602c04030030384440251290201003101000800010761095004051080150404003121100e03034813041a012000c040031000710b01040307818071600501d07240420039280200d48038000064421041307616170001030125806600c02140300740480c0c0d0350400fa9101180b4280b482e0f902e4903540d02041c2c0441200f40f205036101c0f172070046000c000c0c2640f02e184000b070b01d401c2e44030b11749800484801d000060030452400400c0000c00e01c0007103680c0c2e503113002c9082884407403028060703001c0c20f04514000319451917002109042c02001040002600400c0307901d81950020040009070303201c00c06503800d03da05c0d5800140610310300000000000f040b0f50182d8003458107000700070004c1e500d005050741c080e034442c011560f000010880443c00342240c0401882110b110700300742813040856a480d141c0341e40401e00030340400341000c01d1519800754036100701207082080d207a104096046c25180c0365640e0200700c421045c034a0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 491469406 1250 491468156 491468213
    0xb0a0804060b03030a0206180c0603060105030403020c0a0605090a050f0f100e090a060602060708040b0c09060904180b0f0c1801050c0d02010501080c0307150f120c0203040311030604 80
    0x36180d105044042d0007606807566031003c800002d440c2d41080742c2c080b645c0c5901c43c00803550740c60005920a1201e8025100501e0b58454000661762500020b000301d0841c4110049090740e921514a50700043c64941c40d11502c40d0755480c200038034840700741c120030b004039080c8049406070303611610442030701001650300c216901c81d8144202c6290031b5020481e030b0007000d440240109140142e0002c011a40b40703900340e0348291a0704030100c1e00c3c04130903640a0050f034402400300d003928507164014207140304010162480e02c0c601401150550b0f8a0039801c102d00c0745460644c0301407240109000da8091801c403036036503007441c1070100c80500380264804120010884201100c10364014001c5880006501c0708881d02668000f5009028207400d0045141e24064205507080c642000202c22040c1c2d44013256036981010542402c8604010343c61040c030801c06070a0741e030710481045120328002c081e050743c00340d42d50300e0550401e07000c2c0c1c02a191010380203512910030040851100b8100c04407a5040580480401c0e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 491470656 1250 491469406 491469413
    0x114011214012a110c01030203100519090b0a080d05072f040c02012702010509120624312307030905191a0a0b040f060b0a0804 56
    0x50607a110003401d03035881c2103141110031601030103444181c40603040395800d5481c0c44000f00c80c0c00c1082681070000c0d034442000c1c00010360081d006036520a411900c2e0203201c035590000200b110554100890003941400c0052120b41120f00541d0301c11141030b0307070640c1d15502c0c01c40c1040e50344180c0c101074420414042414020030000d03c45142185000f840d041c020805440c01142403202030380c07001d03441a80380a1030001076134018041c81c1800c0560700003044003a20181c000d41000ba01c8103c040341044010880c0029982da040c801c5820320140c480186400e140070310101c4a20841c48540364044680b010201140d030361380f004080c0c2a00011140b042d80080801400290000d0780f4031480031b81410807000700c20341d902c18035820708a0404c00e4040e44460300d80d0542a004c45403c1c84c0c0107003907070708401074410f80ca006205800c425a40300d01c1c00201c2e540408095144003c20554070462040c4e1246140f040c54901401741018110305540108402c0d86007e41d006024854280c5020500c220f050010301030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 491471906 1250 491470656 491470673
    0xe13060e101d0406090c050d1202160b0403062f0307091a0d0b0111100b0109050d0b06100203070804090504050607110601141503150a12020108130203010b0406062001140112 76
    0x800c03005d003007110500f035580b034100c9c100d91464055800602c50130510120303400b401c00c100411a44100442886c1c1801c42e01c2e14000362468000404c8259194558890301d80c0040404002240f40f50075155200d08200c075004001c2c070f00990240701e00c006100100798500000348200e402d512100c210000d02c0801c243c0058401c0200310813148194000d03580c60b688062900d400035180e40e4800da0f107000495454600708945030005040c003a00c81c401e601c000801900f0712040300d000300c0003d40112400c1000a07520408140e02a4000303058607500e50080c070041100c2041510382140700c509141c0741c0c841d001d0790503650310f000521405280182d9000a4003c42c0c488076200c429010302c480003540d07640307071850b0180c9646940715909800fa08540600045081c04050380c0320700e41c0d6059540c2c9400b13171200840e403502c203800000c06030f9055503291066042aa100e114101c02007406864412801e50482c002c50001e030104074044074a80d041c00010b80501a00140381030543d8580010fa40303881a10b414604130 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 491473156 1250 491471906 491471909
    0x308061921260d0605040e0a0305030606122401050a020604110d0501020f03090601060903050d0302090f030a06090501050915060909010207140303040c0506040b07030e13060e101d0406090c 83
    0x40c1d140040c281e142040902c10000e2500b40e2415000b48812950ba00501080b01d02035948200150041551100080d100350700440d005400100120b051400c071040c444946841078420a000c615190800c992002c0352003009144007009090a40c1895001000070f0b45400004000404903880322428850a0380c515116203c41a04000215241d01c001c03810214181e01c2622007041c507200d10000010a1841145402c013a254000081c112482d0180015070194100d0a40141c5c071211042e252801a00c00700080246140254404964445581441030840304040c123009140c0d002b07051503c80141003000301a0704600305480da000c2e582d0342c0182e158020b01903010000d00a00c1e0813028503600200c0000510300072801401c100b00c0c03c6543d80b0403c1540d108a10581c0039022017801b16030301281c001e07888401c41d00b20140c1a85e214101a00c2c4800031551039401030782c11018000d09000084000c1842031015040ca2404410a060010083d8505140040006000d16150600703017042007400d800400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 491474406 1250 491473156 491473193
    0x2010909020d051f0501170c16120e01080c0a1407050303130c080102070b19060f0b040e0105090121030e040510060314160309050111070308061921 65
    0x42d12078460500000240400f6501032448262804c19601c406500403a05000c86405869094401e150005600c4544000030040650305900348424010300881c01c84040041e4440d2008101090301c2e400b000d03041c081281c1400e81003016036000c0100d05010070381125540303103003403c000c1901c1e80c0b070785480c4141703114440008150340004000d00c40f02c40c420b0808207000340e2050721000e0340551180c225030300301c0c0142030b07014140390350103004207a0b21000f502d02204a028484400304440c0d171110b80f07a00b2030003040e0307200070b083e190000380c10402c900489114a000d44421502001f070780d4903014000121045120400700d0200c942400396040500520407852686800743c07040c402454000216001601c40d4840c0302c0c082400d0107200c143c404078003c0003510401000400001c0301c040301001702c005091101089603950758400c880c103001c02080300a403007402d22994502c1c0711440c000081c8030b24150403004000e0b45804004082c002e2449540003c082d0880089109002085908103400c08168860044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 491475656 1250 491474406 491474411
    0xe0f06100e040612080c060106050c03042709050303061003020c10051012060506100507020a171f05090f060103051b061603030e0d0f05030610090e0108010204091401060c0b0402010909 81
    0x741084441c0d4040c1042c0e1b809607007954107130307039031032006070f034a4071404c110082c071170300100000e01c103855241500070413501d140d00740100d80300f601d500e82004690040c042542c4950010007000b003079140c1034141d030b642d40c40d191a0650408810080030b0340c3c0c450100d41809503541c1c17034000017151110000034580080c90f1402025542c41106d0074040020001912054001c640c20080000c03201c0c0680c0866082c00d901a20303e06800d80b0b048401203101103544800001805282a5240549410040449250140d080028030360030220f82240c500031100b01021120381007d401000824804207205100d441c584c0d107458140d0540c0d5000686034810040d250515540450f035030340505030326501403860281120112154120702010942e52804540d8403070002070000c1000071205e041150f2400000c00842c2001c0f11200d0300c03000e035204860303403d030894403542e980403c0810600c0d10038041d801d10002c2686c40020654102040201100104807000d02010241c2011800f164070844030100180ba01070801c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 491476906 1250 491475656 491475689
    0xa0209340e030c01030608060402120115030c0e0702070f0905100509130b0c0c0a142d06010f1a1b01020f0c07050a080c010c050a050a0c0e0f06100e0406 67
    0x3404500120320701c54040d11400c00320081d154044c0c4140c0c1d0680c0d9400000701600d5135240e003080348404180074061000d540b031711015044c11070b40c004510090761060b508041c02c581000e030200000d41c0c0091a100455000000800c0b0700b600c110102d1042c1c600600010070740b47d445100c0910400c0e40c1360f2040d0f41100650040100250140d1422401c0503c5102d200c0f20070b44032407003880100e0007415101d4201c3e070080d0520341e00180c2c200c803d507202d681c1c80000b038900081c40400d180501080c003485a00407213462510032003007024180841805011314a00c0c180a060511400910544075014900020000001c4d0610380c032484c428641c0c0007840301c0009640d039000020f2142c0c0540c0100510f000948036a410101c0c440c070709a070601040e141c40e00010328a08860400444400c02d00c10740c1501c03103004160505020136020b01908280714001c1c900800c10f945480311f505000c0c2001406c203c459510402480b2030b07640d80781c604010309121840c11449a40d0740d140010001e080581c030054860156000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 491478156 1250 491476906 491477011
    0x31b120103140f012d0b061209060c0a09031727010906050c2e02031626061002030f07050c0f0306040c03081606021c05090a0209 57
    0x1591079020241524002e0307604600f01400e075155200b200142e4912020520903030400c5d01c04580100b041004c0200d03407800c031100860300366441402007524000d840001c00065820400400e034020001e41c4a0030710300019104006d100c0002c5020040c03243c103042c0c5912514600da2010303603200d02003048100c07075a05914191112503100008402e40403e80c040c0d00000d1150080c000c4e42c40b42d009200181c0990f0380003190701c8030110088020060125881c4520070350b400790078401b442c031401d0001c9401c000b41c80c04004c0503000031484c0d00b0400224400c11028100503a8002000da0402c00a46d5050361104030480264114010000d0030700c03040a0115815003441400182c041010340141c919204520171901416140c000490f07003d090690a003a040001441e04d000401944061900c2c80c801d00c465a9181820fa034007000c040c07509040488085000903807684640ba4100385070000804110000b0f034082032186a00038403120060721010900e111142c0c60312107450301b04448010030b40040340b8502 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 491479406 1250 491478156 491478173
    0x60402040209130f051518010b0a02030c16030308060409030f0305060a090e070e0c0901050a11031306050c0106150e01081305070f0e07020a030c02090a0b120a020310020f031b120103 80
    0x105c1c600a84d103945400c06c00389003415943e507078031003071451040341143e800d0110300c3d1025481194000118441000905221741d801d011160070300d903e80c03040c0100a499414002c001e444041c08452159103403442020020746c1100392000f2880321801c3c00300e204e03640d50002a01042051303225400040c2411654440c07030380301050780025200a449204001d80b50f01d41081614003d01078024003180040003110016030207582d2210b004030051044a1400c0c0c003d4030031050b030380c1c0c40f80c1c044808550b0214a01840d0310003030080002a10120070802d14208a2240007005540010201030621100c0030100b100400c050307503c007401036002070031240455030b1809501c1a10085203e0040450130020101d0003851012400000c05a010341d2a4850442c05400f0002504000381643d0522135a41116040b90740311081401c2402140f180a0301d20041540149403c100010802c18000c034410030206e8000d40740002520707007003a142049041c10442040c468402c40c0708120307a240540070800000002c104180c2c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 491480656 1250 491479406 491479411
    0x20d06110d021b0607020a23100f0e0a150209040b0d051e0601080706030c0219030f032003010915090f060501031d0709020c030d06080a0c0501050705060402040209130f05 75
    0x1e03550740f00f000e28124200741c442805860150060700601100c0000c00c200c40403401030042045030007800c5401110b40185030074081e141e41000182c441c400c0c280c08041c00d1045500c860541c038003805603070308d0aa90701031303001d0043d1048040c684ea010607146c905488652004000c84400b50100c0108041803c00071b07034803040c4409005600c0c03034410907114080004120b15040381c01880c018540300e030500310264058000e00d00b0100861044100c040114151001a21039850090b190701051a80400000302510490419115402c25a802340c450031320700c1004407130440e0218240007501e00e0441d14901c0801d0321941c4600c1c045820b0102504170305a1650103002156001d0320104400d43d50504010340c5111541d0000404e60008102007124600c41d0b0014a01c1011740c1d029685000c07030b864454800c5400903042010f17140e201b002000108200108840b01500d42400d205051040703e40d038460341e61030000c01c02405142c002c9028401ca4480c0c0880c1c00441c58002c00a1201a503903d6141c4020b0008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 491481906 1250 491480656 491480677
    0x203010e0c150c0c2b1a0133180608060907030506012111040b03150d080a030e03041d070914011704020a0506070b0709091404020d06110d02 62
    0x80302540782030b40041110b543d000c2c0340d406003482400c2c03203003040031403100c0c01c1140b01d80012218040f50140c074101684c00c4071510401050300340016803003800b290700c4416000841c1000d04400d1181e01d91000c0540e2625640390079041054a14880008031102c0c0300c4000030a900b02d101d02000b04505402070344851040364160b07000d1440d0b0b43c2d00d0108a00307886007521480c1c046241c001e2001c00c100055203211001300490800411103400010488030740754001e500410311104040180100d92540c505000340c46070003210407816603182c644071101a03118500100080c5a51007060000600050007a90b00070070701c01039000300c9030341c41c09102842800c0849260740042c8009801040c400e5000500328804541a990319000d041c0c84081000e850801a20a0780c1c04601c12400080c3da81d1080d00400125100f40c610441d14148400c1c0605a01013503040354101c1801c203c0302109a444a1608950085d01228546103017142c1d4180700d0f0040c64a8049001001400507100c83d8011050300140041c516 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 491483156 1250 491481906 491481919
    0x1107290f1801050301050904060911030d0e010219020f19210501051b040b16060e010b01021603020303030f130c03060204081011090402031801050f100608070f0f0203070203010e0c 79
    0x210740300119150721090107040d522116510210300419542d0b072001c07280f02c3c807912202041580020009242c421036204000c0021081c02c0d80e03c07841c1d603052044a2040005039a01c02c2c00c00c04c03aa000980b01282039100a0007243d9502001e421172240c0c0d00240b00400b03000c1c1d8458500c90f00c1d80700d51000340002a40c2503e5560a18000c5001031403003400b8284240030f280c1c4002d0405040200b5800765030703ca146c828035150f940ea0041d00114185d8810309035040010000060040b4000307001a090500c424007581362035012003001c00150b00c0200c116988100c607441400c800360b0300c4032003c101006c0e2540000e0078089140300003100700403481e80200261a681000c0355019400311002d0010350b40b8010344014011001d0042007983c2c14580c0155400010050402c2125000000000d086620031140d842d0307450400d905000d03203c03d0062030080903040074900320b101443c0851001d4000e003907014140c81000801c050482e0143d02c24070684030740702d41c0100280181202000c01135a00c058044040f881100c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 491484406 1250 491483156 491483197
    0x18030c0e09060735010b04090c050a020309040921030c18050f04050403090302061603260403230c060f0c0901090e040602130608161107290f 62
    0x241c0002c03907a1082540740e9802070200d8480307420415025145816600514041100100e1420402c403164042d2090110081d02d8500e8402e1030015143c40106101c140035040080d0100d2a80c04404c440340b020f01910302050032903103861300014200c0104002048511300e00b008000c10350749600300f180114a99619524901c5040f5503c5411341d03001d100c1c0b5035020301001c181040604194200c2940070f4040e007004401c940c2e036034003ca40c841d4040d1303000100125002c0749003003c064021130240f03030205a0701441d08802003054a000340700000030f0009401d012402c040d01806100c0040450003002500030015150140d00d00c4007179403060259160b0a807511404002040e0414104c15aa0a4501691030b2680285440854100c0c01c801800c1556040d40030030503840e0100c1e100c0000c80c02040141d84034562480d040412100800300c2e11a03100800214441c180c00794800000c0b01419aa04000303101d501034040101b02c4007c01d602010914089404181c0307040001c1d880001d0030203c6500701c1c40744683c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 491485656 1250 491484406 491484421
    0x50115020d030506010e0d110303030c0415050a1209050a02030f07050a0e04050706121518050a09050c10050d06032603042f03070e010f080303010b0d0c18030c0e 71
    0x320404c44002c1e0008246102416051a02d0350754042664064022640007241c402d000c00e0655008070380324000200002810044001342008160704800303945000781c04c1000c54a40284145411002d260b5019291300480303041c010180801191958010101c2d07803160100120a501c0d4459032003000e225888130a400202131100791455807061354090003800199080050566034143c11070514200c0c0c1e075a0b405482500284540250003402140000140e03104449040313901303072072000b0110847c07541032580c1040041d100040c400c404078401c540f10398000756424421603940c05a4000042c219042c03603c00000d212504402c1e03d003102000441c04401212800003030380d94070060b0fa0041c41d4550078140020f4124002001103900c100b044030000d0810620000640b5100c810b0304845148107215004101e0505088003400050a0120155080d9031518078103490358050310070141716854a4082804009229038070301c40d580c510440f644020740c0e8132410f000001e03143c540294040d0320310600100f081c6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 491486906 1250 491485656 491485661
    0x6030303060504060e091917030406060314160303122306150315010c0c0b0d0e010f110301090b0604050901030503030f0a29060f12150d031d060409050115020d03 71
    0x4620b5030000b00708441c05031f9004241d031080a04260b4581020fa943c074520b100510300214040d9025803030120b0a01d00310308106c4000c60450007a804c0c19481020207040000051450f842281c3d01401c01040d504020f054503c050054400b0282d0081205801c110151402d05801405400309840b5441c0061040e03601854905c8156040c1c0100855100021400c4d886203d144150070311600c042540c699840002d1551a08125103c25032181c89441c81144103000744903028110060800902a0050941e0007031030070321041c01641c00c40c584580e0144003a13240c40741258000e10000c0d0509143e0361f07407420016143d4000752100c400010042002c00c0100110340202d030f01101c54014500c58080d200c00380903401c004003004083d00b1020038002c0e80921840c0f0000b4020303480341200348401a10780317981e005902d0240c8031072680c89441070200706001f00790701c505840b60601d0720300f00e1103142c5140e640c00075041e406a544513000c610305110011502e0b8444601400d045c0009800b10751180740382c01c038180c05 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 491488156 1250 491486906 491486911
    0x5040b030a020a020a0b0a050a11093f070e060a03020a172a0a090908040e1005060a05091306271506170c120703020a110106030303060504060e 63
    0x80510050001c58240841503000b40300307115090045498400443d607031081d4810b0116480f0714060350f00d10800c084140c0d6030113040e5000e03060a171070510f450040e80000c0c44a000ba1003501c5404c101c0350074020300076200f00e0200000961100448040880700b043d5041c0d40e01e0b41805083c41e2010308c0e41c040f40060410300352100907a0b13401030061500728146400e8451a8081c0c4903050810f03c02e0310303210780c51501314140d80400c243d0b0340804055001c52000a100460351135a200440c10741c0341003642070118034104250b030191941d44450409a46600502e078800d42c0c0140c000c4c0b5401500002c1103603950744c03c6801015500000c3e03c94104902c1c0440703507001100e0003846031f01400f480c0320742079209818101100d145030351030309500007641e400c05010120000310541c10210200b60400e913500b8460f04524449a400b54510a41d1780c40c0141d41c1d004103000c00c074080c090380240354010400c85000c3d80a95440e81d440050b140080000b03681d01e00b0010041c1c0654414240540e103000d02c0480d1114055030001e1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 491489406 1250 491488156 491488169
    0x9030304140328051c1506020c0609040b031e07050a060c2103090b010e01300305030a0608030d0f0b060a02120904090b0103050f0c0d050c040903030216050a05010c0504 74
    0x15403c02d030310f00341441a0111560044100041088140000d03401e041035502c41d003808010010384011903210700c0300d200300c00c0e400143c04d540c030408001d40c41d982c1d9201121007621007514045602d02810000c689801e11481c814449080b641401000d030200001d01c000c11240c044801d0721113a9611901a0b03050040380d07c0152404242400114038520000c02023162200d80e8a4000b81011803600d6180141200382c0140300030070761800c0100301c00c1440001c85c0b006c42e08bd0064031501029103d02d800030b168100c2e04010217000c0007000103034000c60f40b0b504c00d0340103041c1b010980c6c2d03072401400b22035001000100e200300e203500c0c80c00c0b50a0040c1c1c00c10806980724042250000c00310041b6085a080e081c1c2c02c4500c445a110351201190310000700c000b05000d0085211740001c080b00040b01d4070302030038110034405c8603002e49018a0710201064000805100382001664002a0041c640c01c046010340704100d5184140d070f83c48000401041780004079040c2d0140144001c000920700f00408840f988902d22810 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 491490656 1250 491489406 491489437
    0x71a03040605070509030106060306230607111305150a060f0e041d0106060804150b09010303200d0203040f08070e01270f0207060c080105030d0e0d0209090303041403 73
    0x1400288036039100700c3e004046401c00d01c2c10f00400c8400282546c590390400d0002035200c400800c80596101041080b05030a490040c0f40c00007400041138041c0100c042c0030346071030480d0301034401c1601c9055044124800d81d00041c0301914018400c0c0356031603400e024860096400080c0013820900c40c0c3d00c42041c0500f5a40d450b04800e00e40d404000103441602c0080040200c2010b0710045500300b485000d0007408543c0350000c0e107240c1428480e88081078095440350242c10320030740700d40750741d0703114000c82c150381d45030404480b00d5000b04a20440c02450700d0940815220f2600d600700700540008c09042180c4004c3c6a0031303003640c0c03034049080d00c8803014030484d80c00060b080014001c140b0b41c444005d01c02c019041024904a00120b281000d9660307220080c658554000303408011300c6000d008104003040141444000e83d4500b0000ca6a10040801410300700420039401713084564070451030707020382034000717020a6507420100380c81c588030f034800e880444da00c000c5c245a11596000c0030082c4ca03001115000d8a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 491491906 1250 491490656 491490661
    0xc05060f0c1b03100e070b12010f0909030f0302070303020c0f031e0403020307030222151a03070e040b2e0314011805070e030a051608151f0b0304050a05071a03 70
    0x801c40030b0440042020540d00403950085441e44d1f421004e860149a1240701d1695545801d980b158015481c0d0803002d0b620f170a0507481404603030410740701c548010013031a0050350340c260390400720000c1c00307018400c0d0301c18012207a00203182d41000028001040c94810041610962084000118032a520001790160801401040903180400000d4203681107240d2140d50a448441d401c822039070b4481c15002c240700c50f900240718910f80c1c8030408040c1e0301d858006034594140008054540d8007443c0401e44160340b507801222140e240c103507101043d0b6500d40c07a2403d01d12048400080c00c607801c1001c2000092420100302100001904480d04841c040b440c05103024408004500140500521201c2840840540b0b0710458808100c0b0710385003409040038164140c200c41030034100a605501c14001c40d800a1140f8401120303007241550481980400c05c3d52288070203450520002103070b8820b4070402400f108001c1800000318203901b10520030415a84c0668803a094905c0c24552040c905c064410240b00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 491493156 1250 491491906 491491933
    0x120705070e15063403081501140705070e0f0708071d1203031b18040b1c0b0a140403050306010c06090209070c0b06030a030e0d0c05060f0c1b03 63
    0x3115003041021250b0b20503540703850081001680100840e0001d1144801c0b07594854030002d078402c07140484c001041c025940d464030000e1003100003806031081c1a01459041781e15070f0050002018080c03004600945980081c180503881d400c1620606940715101c200066000c480200c00510440135500c5501d41354842040032200e02c2c1c1c114084440800d1500848003007a45d50003031100c00c40105c48019a503170f20b40350302201032000024000004400c001c0c80880180040010030715040102610001810680c490026500044050115003100420715100050041c0c3c0c4415521403008040140040c0a203040c10303600f0010120b40250003e241031020a850f51311907164982c0060044101003005070840c2c0000c1c00c2c1c1c2d1015a8108081180c840c0d0100070040301841031944a4011806001c0401d415100034143d2840008100d1084581984010400c43ca81e0646d001510b8050800c81e202c150410300009180c2c07003c0c40a01c1c0e1841032101541da00a2807140000030103074090b0280218419512 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 491494406 1250 491493156 491493179
    0x60f061209051501090c1e0f120c0e03070f03020105120603030904050a05072604030503180f030901032405040c2003030403030612030c0308151206060312070507 71
    0x8101046646400700d06021940400c4090b21200400b0b880b041c1d25454110814115401030b54030758140aa0320480d4000d16010071003180420f1118203050300000c0b2007480032901070303907900540c1004030301d03081400ea507141c0d228030708101031a021b500f10342c121504c41010342800c01c140d110003400610204801250326030801e500325080500901100e05040040c0c00160640d002120000409135889081204441e071041084108544401d030f5041d42e087c40301010303030001c0c10050001e000c0c05000408079041d080000507040310780d41c82000b0340380c4044143c04800d4481d40300c062030034000ba0070680c2c000205010303014003180348204540f2800e4201d01d040c040c4000752200903003520a0001c420403000c10700110b505500b44541424001d1640c1c0d1915260103030480e070003a04285d44c0c0d240c1803400c180c002070b00200d02e1a1295010700381080d49590304012042e1960ba81058544c0080d40711012610195000824a029090480c15600000200da10380fa240e17015400c03014196600c02c1e80f042185a8100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 491495656 1250 491494406 491494427
    0xe0607110304050409140a11041503030e0402070828030f0e0d0f030b1c061a0618190608100510050702010e0612090303040302060a05100608071106010b090a0801060f06 74
    0x560b07600c0f11368602503000c47c3c10010400c00036581d801007070015024500c0d051248010041c075107010780000c24110b0718001d14402000c10503500869001903c4030512100c00e0555040c11411980c0100c02c0718992000c07500d035005558484003007030074004c40130001c01e1a4001d0f65201c4592200400100c580c030b00044034440303220300e4903e0074107a0751076000803552120007400780c1c0082e24000d05080107142c1c0c03900c81c0485080f02c0f0010000440107190b00042d80d0340300c08481c004100f504214105082c444000303a00e0f400c078102140312040400c3c0000898540122406114401095908034015601c605004016440b034101000141081012100640c080da00c0c10402c3c60b4040c01e414102180d090004001901c1074441036150b13030012041108150f8100920f41d0310440c54501841141000310344100d00e0700301c17402401d050200c5100001c40303250ac1f5003600321070450f9403400c42e0081d5070740d172103500160760150348064000c0418040210340c28105016400440b4402c01e00c811000d841c0c560704840d40e1100c0e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 491496906 1250 491495656 491495663
    0xe0f0109150905010e060301030503070f17181f120c1701081c17040204020c01020c010f02130b0712050f070f0302010b100e09040201120b0d060e0607110304050409 72
    0x11040c0c04100000400c08030310a10354581c03542d0401ca4101000981403002d210744040c404c040410040c8001400841915030199100d51f02990351078440c0f40c003107009070400040c00015480440d00c280c3c41d0113585461b1005500c103561145059101c0342400c03580c4480262401c012600e400d520b811010207541c0050900f110fa803402d00c41140801d00c07098500b9400f13034080b001e0340d4044480001c0725452403110f55448042c0d81020381860b2040c11103845030740300090019200e1071780441d01100c00d00c0d080d01120004c0705c010000b0000703112203402e440006d4020303aa1841c031000688402061a0804808079a10550400c3c41c038116290040c000b211a5813041c560300980840500c94480007991900f0501c1c240e9120381c001240107124101848461840344511004001040c2c14844440e128081c3c4284c0084e02841d28070018965140b080c80688109100282c10041642c3d00c40d082c458260f00c516596001c803030a80304140c8501030304a51075146a03661102c0e64104110400262400c0da00000541d4070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 491498156 1250 491496906 491496917
    0x4121407050d050903072102090915011514071b050409050a1e0506160314011202010806040b190e0c090a061d060a0201330e0a0605040c021014070e0f01 67
    0x31900304047c90080c166160094200f8252060b0b011860501c400c03c2d032105815005050000e40031112051700c18040c0704201a41c20441d9408031151b10407613043e0a0001d040039816035912003850004a0000b03815100311b07a90741300503808143d62502e80a101d901681000051500d481261982d880c08000d2005d400600c40225035001300003401480f25510560f07400d0202c0013211440c010150907285050400030301d20b842880103006229200c00f061000540a00e003118260342c40802150040005e812801d03803200380e00030494180448001c280003a50a030b480d801507252218028031b84c441c02882c800070b1303118500c0e51041c41041d10035050f9681d0000a4041010b03030302024004980d56a01200d0003000607511403000c01d8195106200302220a8001e0b800302d01c40d036481c00b401d05150041c40c059414580560800b10309a400140c00c13583c081c0100400c10003100000b41c9020759030347e180054401003070341000c9000282c0680301c14101d118843e0390311070b01407162555003004020f0a021064034107000303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 491499406 1250 491498156 491498159
    0x3020f0f030a150605040b0a0b2101090c03060e0708180a08030c0304051e21040f0905060114030606070204020f19090f170712020a0e04121407050d05090307 69
    0x280c0400c00c002c15540141140e0030703140800c054440a80d06250095801766042c0b80210071240c6425594030102c2e0b003240c61094848070440e00300c81002d074100d25000d100d61213140020903074840c103912613401c0c04402d4408001c0c088e6945a01300f584201143c140e001f0444e1100007948181c5139a15290000c0e101c1000d039943c42c41656035030040341d0001d452034121290080308010820a00300444400410402da420080d5000b1032074195603601e040668140d00d0a0861410107180c00c031505070780260402070722120400ea140c1881c68000c1500703c40b02d41c000760003601813503410f0044404890103070001070030441c500311070341d002d00c0080d40c080050702c0c0048a0401c11441020b000e40315100032040d0980d20f1100b0107141800d05a10600035420450704881411001c00c00000002110800c40301131041130991450a800000c003000d5442d0710101200b0301a0041104103c0e2005004d56018501d40350310700014051202a5994011803c0042203980511880500e05002d4000790880e2400103044a440d10f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 491500656 1250 491499406 491499409
    0x1308040324050708162f0a110904030f0c020a031b0e0c090612100b0712090f150309061b030506030d0305040f08070204110a050a120209030703020f0f 66
    0x2046070500070700c1c50039001c4a200314807492801500d0300480c0300d1030b20401d00d0500100c0307044504201d00d000b0041c080560303121100054582d840d440b14a079030500d054800441d102080c2d40350841100100e401407003c0f07000c091149010768403076000e180c05603121018411041019038210702004800e981c04083c1b41c00002c00110801c0c081c6081c46412000115442e117044170714000200091300950803407100b40b002000c1c0340c4428060303030b070182450b841811050b281ca0490b50500802a045140403541c0000c140040c04032080d5101c00c0301129580d070700e011550314a00c503480d41c4085d0041081c82009003d0784900720348241c02040d4604d010b460000b80c0c9810314001042441001100000070031746079020031403075113002c0c00b070030f400702e011410300340420316180e6500e030b40c0140102802444400082000e0085d5113503581f12031440f90b18004469981c1d0f000350006020394100900b00000102d84200c10740011065000740c8400c0070b0003a000b400702d20705550030803e43c15151002c0a4102d036140c959480b06 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 491501906 1250 491500656 491500673
    0x7060926070b07050f060601021207060f02040504090305040f050a060c0b07020c030f1005010905040b01230303030403030b09091b0d020102240105010801170d053001080f011413080403 81
    0x1481d10070001400303003200f501700e61814213038003d090301c0c10354209000c14156401c0403001c0302d540a900c1403000801c5070111480500a01494000b281c1240c504103010b0201f640150003407090f181e803d031000c500199070300100450700c0214015500085e1a4a62510009220f00c41d00e58208140c1e0054032405410b110200740750601643c0800c0155002e24400c0054550354030826000d040c002d20148070b07510341621685001034062003088102c000450210b04e0041600c0c0c070b01c03409018024241c81d40c83c200fa0800401800079540310300c0c41044c0350000b04029a500080c0c0244c000100a80f0401c410505c900700100e0911049040c1d040d0b00030041503141580c01540403800880003000d6404a0354100000100703410416041422a024919069640c0480c009402c0c01d040d9034070300c2e04030391714001c890a05102400c40142c16203c00e07280c03407003800c0c451050a10030341a50308410890f08060550012036090b601c665541c41384123a40c500119600d50f82d05021602102e0060b69544c0c82d050f0f1340e64a4450 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 491503156 1250 491501906 491501917
    0x131a090a0f0303050115020111161b1509080114041b0b120114220c0306030f050d1103041a0c030c06010801020405041505010516060b0a09020c07060926070b 69
    0xf0b43e03944014061032080c1e040c0620f4010962000b008003a1124241c0c904501c646000983c10b01d0780981e0110401c803001b52891000e2a0403108403410f143d4401c040714900111003200c4c40459003080021072070020510600c0d158043d0000e0015141d00c558032072604000364482c00c0c46004450240c00718a40301110018031240c401f40031246010340c545540110404d1540051501c14408403a5000390504011082c008025480800250104000d5030035001800c4d580e01c0180f80c901c031a017840c2c00303010300400c0d9514002415103501d01010540f4420341c1d201c2c8a18043d6001802d9100c01c01e20b460130351074002c0c14a074180c1c00c040324600890310300501d1409409030700c161066900042d0a00040c00d2500460945003207540e20440784070300704000a8468001e41102c080b21b401007a10f5041405229049150804401b400383c01c4500e441d40300b5203000c0d5000082c0d01e4403d106030800001d94070312603800001152442c0240d0006111110150000403007461032110f501d1040510100352031000d10014076 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 491504406 1250 491503156 491503163
    0xe040b010302160c090b030303070909051f0b07030e06040810050415090b011d0c030c0d06030b070c0b1302011709100507051c0623010332131a090a0f 66
    0xc4139440d090841050b9000000ca40b80240c109206015890381c101010609440c007100d804949a81c0e4090400c03080c0380710507140f90805855460000e604038800008000d11402581c480c506405400c0621000d84620310543c0056030003184031041c00c00b083e5006c1e40d00b1500c980d8440400d001d06103140c5058889060040d14603004440042101c401d20b414900d208e62000b510a0065227403400c608112804001e01c5030340f404000150110400405501880c0515400242d82c0e00300d050110006142d038081490845407448524040390841101ca030002d400d55905960b0504010704402100c1d00841e00a801059184a00c41000750b4189140c06124030440c0c0c29600e45450300100d2400030b02c020307a02005d12001d545008402d112007040c40c0700400c420801c50306d1407001001003000407401400f03149800100c10880d5000030564510061080c6490384002281d11420b4070354030030b0b082441c201c0c0300f001001c009101c520344000c024000045503010501c00d0640340d10003529140e001c40034040c00c6046 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 491505656 1250 491504406 491504423
    0xc1e030c0d0f080402012006190c0504050d020607030c0b010b0901030518070308090d150911090c120c07060c17070306060905090a020f0c030403020307050f010e040b01030216 77
    0x12111440401240300302910600c0c0044202c00401009800d50320081e0000e07041094043d140f40c07801c14548040c00d41021107004a42080c41d02d10700401c10510901c2200c6055070902d024050082c0c4204151000d480c0010b114100da0085c81c1d00f0040c6ca5403022300100e0601040c0d6412402080c8102c2e2058000c0c29440c3c0511754454504000500702d400c010011817403540c4c85260380351131800008000045d2a0f00c924a130b1394408080300010801300c0701c4100109004055480752400b903a154100b81c0c2e0fa640300b84188013068180f2000c01600901c1202d00c0056014280404441a4414030600343c100d042a40100d203010056159401950700c00912007020460200c072081c080d9032010300c016840310342071604010f01b07810010300805032000b038450a441054070a0200b00950550f60403950003c03c101c42640d0783c0c1040f050440d489070041c1c8000da219000300c0c5400134950400c1e540401c1c104405948140b0400d20300c00401009003400304002d41019803d00003d2441f25045e604c4001990080044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 491506906 1250 491505656 491505667
    0xd0b0f130b0a051507140f0a0c1a031b0d0b06030405010207021806030309040f02040504090c030524010b0a2f0111190516020303030406020a08060a060f050c1e03 71
    0x103100020042d5481240941040d04905091403014000e582c0e2055200c04807203d44c034810a40303e0300d032a4201c030014140d805601d040004010301e42d001003084460340c1d081030144004041900b1400d02003103401c00e1910104d0074031024801d01d6000204140c1c64620800500c03212401e0108020b40c0084400302e9081c3e500048800551411000110381c0002c038002150040c60087c003c40c1c0c9900800300300034015034859000211902c25a0103690182001030420840ba0040c2e04000050003ca8030043d60540280c52081000114000014840421446280681da440c242c20030317100780c0c0401d140034100142c402c1d5251280c9c000050025401c010744012041015040201600b100c030303030714980c54100608010100f202425400761a107032100030b0421341e803944540c01e0140c90300d5503540d034003d42c540000001c210030489940d002c0e10f00c0b000140d0b20301c18980d41c0c0c01c0504c4041c2525000f00004280e044031600c1501d48684014004500d1140c01e031003107030073318101520882021002c40c50694001054 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 491508156 1250 491506906 491506909
    0xf0906080c03071a1b0105040303051f05100507022403150a0e04060b1305010b0703081303080103060f020d090606080c030a0b062e0c0c05010903080d0b0f130b 70
    0x200c512507070300c12805081c0d91407520a15101821405095240a50340820800c100d805200c1c9808662007106000744035625007460001c0040c20101c8001c0794280c00c020700900360750701c1500d644064400151502250403412a4250344507040380034100e0348844080110034401d106d2a1310b00c0014030401c14229100d0911021417408403082c00503031406494464030400184182c4503c0503040740c5c010000203140591840410360380c2c00241184509207050600005844000d100181415800703955030712655101c1d44c1070040885106603026000405110044c80810711030380c021483d03218100001882c01d80d08110b020152100c01c2c81c00da4025a4841040141580502c02c10345900c108034007400035062540d0f101c08040380d01815607030043c240f82c000030710005150510b00f8900021103030b00e845000100313080149460141d94048400c40190240000e8a501400c10441983d60140d41d86003001c0840c92820001d083c0302d443d941d400b005058000c030043d01d50301a031001510400d080803560022480 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 491509406 1250 491508156 491508163
    0x807140d08070f0801090e03040806010b0a09170c13020405220c020601053601090e0c0109120f02040b06070f06060803030c04151413031a09030909040c0f090608 71
    0x14a607800f40b1a0002c00d180340954803107a42415100442000909800f01490341c914501694007c1c000c1807151000100b14001c291000e040c2c0c120941da01d01100c0ba80311150901d505020310300d505000d03482118041c1e003501c2e0941800c0c9040c84220340060805603a1000116020950704030b040d50034100102c1401a0340b01c40c003c1c0003039040240001c042c00e501d440301107601404458440707100c50303aa01aa2513040304c150100c0030f060807442d101404040d6158549131000300140c060841e49031191990002c100d50240d40030004454501494408441c8141ca030400d038a811000100e0340103a035104884120307507480020345140c40c01624000c000c0300551034003004545142d0401c50322035105201300540810740c00c00f210305859007513600c40c5990b101c4107001e0701c207400c2c0704810300c205060116001d00320032400122403045034055100f44a40c907060002003a052901501ca4010769042000345585600f054008250090310500c0c05005250703851084690740701130354000c2c0d00015103031002000050001c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 491510656 1250 491509406 491509411
    0x106050a1b0203070e040303110f1c1104170a0807060b0102070807030503042d031506050603040c15090b070606031703100e090f0715081b07030c0807140d08 69
    0x402074000da030070540000c0d9807070060f0321802c103441511600250405119422504503100c10f002c0850321405031f880d40c10101e0300300c282064880001e80b410b0200c0864140103c140340006500900e140904016031408222035501c42401d00d0b03c10283c80300d0003c0c1b50207005214540c05010001000741090b00024200025075104040c42d42c400403062000c18004011501150031056940c1c5480840913805d1030b040d030381e44e072a442440154990000500c9607000003807500d10b401c4201040600c0c3c50f403041082502043e540a0807105038031005220380e0a0052450308128100e0078840d90865031400651001d9003c94400c658090710b0305410010050320048524000d108481c00a0852400503422442c202d0b1522486440101311008614102010302c000c0b59280c500000f950b00654486030364442064003143c1c0b80000039000b10004244e04800302081d1107000081981c507250880d13548085030007030320003042501d01290070044a400244400000000d03c0b004801405100202c65405010359000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 491511906 1250 491510656 491510687
    0x1502210118151d040201030e060906101e031104110a0903020a0905060f090403091d090708010e0a0b0726060f03030c030a1b3e060a0e13050106050a 65
    0x14140144402c403e5049540301c40501800752150603036031400102c010b0801c884001540f0f000b4601400900e1ba03000c00c5a512413a42c0d44c1c01c01c1c0645030340f190510243c014178110785451410800b002d100040030369002c040411401007001c0f03403900e2150001d039200d611800f2940c0100781204020011400e205040000419015804100501c0c0a00c04203298004080b9002d10a040c880009010103008443ca440641210071603020b2124289414111488080d6100e6000341300b01c1200144401d414003810000c01c01840240080040c2541c81004d00039020f4907000c203000d00c0244c424aa010b45559091460003000382c8010541000801d01441c40c0420314041e000741c104000160504c0c1e00081106d508900e5440c0c980c0c4551031a450302160300580d840d0051090001001c9030600ca14a6021014410504480421600b8900080800000709140b92641014003442032241c92409804244007811010706008003031280d17607298008840090300224041070300807407402c6a0552241484120f11074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 491513156 1250 491511906 491511941
    0xa05010609060e0a09060e030408010b01090e01052805060a03140901111602030a1a04170702221e1b030b18061f0c1106071502210118 59
    0xd0016000c583e0100926030001a078480a040c4c1c2008155446407115000720010380303881d40d40300d1100a001c0c00381c1c411814002640000085034485580118a0403104000c004920540e01c2d203858510070120f5000100080721050400145a19008004e140d034817503e513000030b0f06014824a945107a030020b418a000d5030714044400d29040c01c000100c902d21036030500ea00480c1451880000d26000140400a0141c401800c1d84d501c1012946015070055210301075041611081c030512201034040e244020350322030b018440714000002032900c02101809000700101d142003660101950710b0385001000c0c3c090a0307640070071010810700c018a290400403185070601803500a030f00000d0a0b038806282030f08490131040f000c280281d440c078070021043c81c08e1405040c1c0d074400003140a80783c0d12002400f40d500b8034201040c0700c00c500e04402121001c030f504c110700503000c8491b40000c01c003d40042e00c13849101d98801c1090340b084103a4020503402005024590300d02060900d0130101034a452440c114851706 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 491514406 1250 491513156 491513159
    0x8030a0f0c0c03050c120d0207140f0613032a12090303090b0906072003150f0f04050c0402041e060912060c0512090a110303090f091e0106020a0501060906 68
    0x5a004a00944035501807030800d4032011041d00c07207030503d032403501d00101e07011b0005400c207000345954001d058003501802a0420801d44d90001d244c485103002d01c6070b220b6400c2040007a41d042d10302e10a0039a036900038940394100c00c0780030b00780d2011220529214124541e01003600e00400056007240104d03007100c0d190544403036146a030064003980190044900785100841e0390b0125450308401c0d1002160004d05565040010322507640e448102103201034003d00941a0400300602080c2e00240036101c0b22070104a580c0e114010a101d1100141045035a80120381d101111aa95070020b003020707100c0e1440e42d02c2038801c60710580000704682d502034010300c5002001040041d07500600207541c60303000400070880340422842240d80d44140300000c85070b450b9038410f1049071503001810040709807042019011202100301003540c3c0f80600440305501c062020714104c00c0d0704005481030782001b00300c0c40d100b1004403840c0b603214102100b60032110041c0d2000f02c0260a0117001d00605000700340303903007003005401d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 491515656 1250 491514406 491514431
    0x705011806050d0e0303010609031202030412110a0b0a11011d0d110c0316050112050402240702031903091a0a0302091c0c090e0c0d020f06040f0308030a0f 68
    0x1000c40c458681072160100c0c00d403c455260f500140c141c1003501003034940d03030341c1c50711405404505a0300003580c0c1c0921035480e24121600000490b415101a040c0d101145602e0350744400c100100404221303084980703a6400580e116010028100140c41d5440d50340c046034000c411031b03007100c0e09000010400f0002c3c81900164200104d0070348803540b107515015005001c444a000c0c9070004007a1029010f2240a80140308e191a084014081e200c09030f0710107001141681064090f1078060320007940c02070200c103004815040001d200303c201040b02c02d0003424416140c002905000c0d8820542800310810400c000415620801f4103000d0601260000400c1c0643d80015105000e2500c150f814994002010042503030794400c07420851440f8502c00215414520708510b0b802d907a031007101e11041c00d000e055440c995000c0758500314000050b0101c000c115007a020030052340d458001e84c80c0c101104000219140d507699003081d01440c05070b441d4907034034100b0300c2c048402c0b500c160175195a42480c1a80490b4030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 491516906 1250 491515656 491515697
    0x30605040b041a06030714070308040303050106020f0c0f0f0901120606060f020d030b060c0d120507030209010516020a05030a060e2406010c03032c070509091917120603070501 77
    0x43c0043d140741c0d460740d4882000f0750385041241ca800d010120080340010805520410302071007940300740d40a100d180d0b03852001340d1b5660002c0a003110203410030f01c10203100342008070b84600359040003005040844610030102d501c031b4200303030405182007042d0028038061020324044ca1006040c10302d41f81300303000c507290002500c6144100c000c200f0180c440075811800d40d948400c4e214801040030a031020204074070030203071111b0003000068002d01d003010b0014040e64040c2c402c2d01c15940068650034903005800036080e001e0f0040d03103822a80b02416075008607040c2c4041201000c414420700300000c50040303144400d0301c0c02001c1091f02280c1030203404107100b000005404507030001400e003400341c00400249000c1d4050280360b5502001c400740c01c6a03440c20340d441191100710442c84031007034a50345500d4006014000c003081358890110380c0240400440c00401c0c14034580c090f8000c81201c0107060a40308182c007143c0c0100300390300c2c8c40340009003440401c1c602400800c008103000d00700440d003502c001201991 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 491518156 1250 491516906 491516951
    0x1812050f19081209010207150e0d0f140d090f0308090610050a030305070203010e101515050909070e100906031a01350c1b011808070f02030607030605040b04 69
    0x803c0d000038000700312021000d406482d29a54040000480150303100c5034140100391310850800720b131140140c03500c3c103940611a00c2243c04825075401c00e403d4141d20344454254480c0c0e9091103695076412003900403030a00000300c19035034481e07a40c8030072500f0010070342407412801030546811003400030030800666455500d44000c60740c0c1814999118a80b5000207070061416065001d5280601c601010010710268464003000050714600e00b2069240d11907507511000c064507041c007007a8200040034607454050034943e8441c0003440d00d08005c07207032080071030a000c48110b02c11000c52000705080c085581c1501803103600c401d5510b00c2907020f103007006c0020200f41031004a4600301030980da04080011a8804440815101c1e042010b45800c10007050030b4194000101c002114464150321080c540d018014101d4040d0544140c040c446ea1b69186c8000c10b501c20001201c5200d16150440016242403200070b00c202426100001d1440c41c2c54140429030700419180c5108070305d05481c401500100055008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 491519406 1250 491518156 491518177
    0x30c10060518040204090c030b011a03060307090902240405010305011205100c050d090b071e0207050f011710030c090c051204020f12010902010219121812050f1908 72
    0x2c807162a6400420018000184080c2450441c000003100b4040040074140c101c1d1510308000314125411002d07214140015a01990305030040030041200c40180c0e0800781c001c900090200c1c186241d487c0e90420101034040c01c40c1944040810200069a01881264010668620b05200f0b4210940c0c9007500c80c4403440111443c0f0ba900c140380c1c04858850402d031520500317031100c100031016581c2089022040d0854040000072030200407004034103d0580c01c4040c2403029001401d03041d04000c2042103210680140ca81042084a428010f0181460100307000b60041c030b0012081c0350550518aa0032541c90304034403003a9080c042c1a00c1c200d6401021907480503951410000c542e2128130001d4034001280004a512442c458110040e080040d4460a0494070036001c0340e80d8244a85800700f010203955002130001c3d01c9050031124034901421041c844032540d001440321716500e80c042808007a010302419150b50340624050100f9141c10031410785410704041c055450110039039901011886104c1148 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 491520656 1250 491519406 491519449
    0x51606020a17040503010e03030a0b04150e1308120708070801062a050303010806070e030705090a0b040605040c0504080f06010b0a0c0c051e0907110606061605060405030c100605 78
    0x80b4007048001c0107032005464000c0c0284203007014985515902c1d00141e07800c07890103244c81c079840b540f858644a40c44c1d10025124200404a1030f040061182c004020411a2070341c03243c54410b80056801001400950301e96043c08801d4180020000d128010003040b00c42030100c080018460541c0190000c0d01781c034400750341064440301129120140c440200c0380100541700110021440034000b1812600c580c5150342c0d10602c014a00080507521030b000d2107060380200c40480800e40801040e00304200d41e401c0075001041d0940d40e04041001c841d448a184c00010b1000300b014001c641040c000f03207006802c590006c040c55414200300800c103100304207e060601218a401c0301c1045402034640e4020f1000074060411403905411409191008851141c440c521060004541c0c86c0110482c040f19100c642c01011140d80300000e100e415400b6042095403078074040000b0b40040c1042098038415441207020f142c07220404d01c45189003136140b540020015060801c107000c507403105041c1051101100280 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 491521906 1250 491520656 491520683
    0xd05091524030708030319060b0702060f0723190b270f0a120c0b0c0c03040e010306020705070e0408160c0801051810110702240304050a051606020a 65
    0xc1080c80d090a040e035542500440c000011124408170240d072007070350003054003210b038080c044041080719524090100040b4040c400003001d41040d0002c0c000300107191191500d06412600c0340011508004011149a4420856940081018401e259074071503002d0b02d18040f05040c0e6222421401c2c02021104154500300301c0311130380d041c4094070f50a03840c601000c0d14204c0f20054602910780b900000181c0d4584114070ba00b40c80f591242d20b402c0f9400e03400c0416a41d01d40c844075180e5141360300c001701c0c0f01d62910080c0000b07e0104e054114082c021845180300580e141c20501c2d026091541541c443c03071881810000f0400490a104c1c2190100c0107441c0b500543c40308a072820000510075500020720542c079040400a40c175a03107091a020302c0d0001c004803400e0b9070008004200781c4002c03800300c0000303034001d00560005041055240e032006400303089040e095280e102d50035810b40c1040758103560951100317190800b800018413031480c1c1a00b0100340c0014403400c00c0000381d0317922640c2d00028440c00700c2c1c580c1d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 491523156 1250 491521906 491521951
    0x5060312090d170702092d0915040516090609060905090717031611090c090a14040b280b0306220b12010f0630051609020d050915 57
    0x1204c44540e40103160341d40c3c074209241e8240301c2040320b2081c0d12100c480081e40c1c2424501a035001480307010007100520408280c0800058800d802800407035507440f1f03484483c0f004821038103402c0c020302120b0900088052600f4213000076030b901ca60003080d00364a41024080031840200320030701641c0214981c9030300c82400542d02451842100c011450104802440070b00300f26001c0b68101102d40100d80412040d1035003004009503102e00e01d1800e034800540501001180911940b4a408040c01480060309812000224a004107813031a04c0c41901c4051402914642d0100300b80005084a04040c2d4110314000b00800c03080c3d80003010710080c001001d6181c2a402c0c00c9a0400400385c0b00192007142c05a0b2000d00450190403c0d00f113000480e03050180120701204042c4080c86000da4041c001c1043c00210701c044d4110f04803284080c2ea5600811281d110569140764040006000100c40181c0c0c80b0147c1c010355080301c0011703100c076805801000081c4001c1126204254000307200700c00c2e41280400204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 491524406 1250 491523156 491523203
    0x180c03120e060d0c03050603011a130f0f05100605090603010b0d0f0905030a090602011802010c0c0e0c0405100806010c1101362c18010f05060312090d 66
    0x7039800d503015400242c40604182c4a030080342020b01c89450a00258640204160983e080001c010300c1c449501118900b2502d401131040b54400c1c40b00a00140106094814000751030150000c400500d0b201c06c18488400c00345c00041c401801315160080c2848511000113000744010300c2620030f620030109101c4103045060f4000b0b5441405c5d9030080194040601c0c0841d1a904082042707004203551742d070001803090060192140c03544c070400c01d10008400c1036005482007011802e0540700c40d1032031103001c144d0310704421a03070340141c40180100303845510340010404201c1c6440414030400c542c0c1401d2029030390708011003041d5a40e1020b91008107081d0100121002041100c60201031a4403201c01c050700c10301700401615141c1c000403141060340d00e40310701d416401110426580c44c2011090035120f440a14284a504079416490b050484140e6064450940d60002040441541d480c014802c1d1403804020021007039081842540c1005020000200350f415030b064041c0505c186c002d0180310703002818 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 491525656 1250 491524406 491524427
    0x2040b040c0c11030307050307120c050d050d0c1103161b030804030b060402270a0e0a15150215090304050d080c010c18051e10030f180c0312 62
    0x14000304404405000010035141c0d0018043e601d10000722620806400c01000b100c3e42e5940040003145400e6a0b65149284030001041006c1001102c07045600041c03400c1c070a1000b80c0e000b9544454813521500350700001c54548501e03a034103000c403500c00341040c00c2020045e991106c2c030000c0c5808540410f0300b0103d9a402e01c28400030340940b0f0920011042051190241095a00580c1210681d40d920740500040b40304090290911214400c4000721000445a5400c1d60380300181030414810355520141a2441044c0c807503c400e1502c07080f24800c480c0035070380004001d20054000710b441042e071b00c00c040d465158050310000c444140da0000340ca407003010030495008000287c00160702000340c0c140484c658206c1100d090f42542401d103a5811148144400343c90326038100f519071550b51401c0d00b04042d0f5100394200c400c502010701244203403a0790b05803200c0348a41481d2404540107200401c103508554055402c50134044240c60000c021440080601040d01d0b444034540d01107451505041e03070721003101e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 491526906 1250 491525656 491525659
    0x2f09011707120e03040815010b07020d050309060313050f060606030a09031b060b010f080705031501020138031615020f2424240c010b030606060406050904020702040b 73
    0x2030407100c1220f40f1000000b4400c4800100950b40880009114034001113802e2240c1c1074828000d00c0a2405850030803001c440e602e20440032a450283c118003c544103030822a031031052176400c80c008d4420b00c2428000c59910021350300180c2150b10380700e00060903901014001090342a6a9140d080415005141c40c031400c00b05011149030040e410328002e0040c200b600c0b019030006040e8010840c80c5409010305500600c3c45272191400c640e01d80c03030041c2c840c02841c1d0550f411992a440c0c010000c01c41202d00501c101d10504864a5002c0e0110078140c1d040d0000a1450095102168282e52108402d0750740007620007880c04031840785400d2204a1a0280402e0740c00d00c0c0c0d0181c004e2084002c4d03019003e401d038040c24010494207a64902400004100f4000c9101c03801d002c41004904041c80e100b100000a401e1400c90041d5100980c9030300040c41d02322440e80c0805a54507a0541401d103020071240c0c0c1d0005003150110325090030010f0007486070081c0c411203030041b03801003003102c1150b13126013214240d41b80 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 491528156 1250 491526906 491526911
    0x170c070b01060f23041706160e150a2c0f1314070c050705060a0203220f031401050a050903071b050d05030d050c090d0f02040f2f0901170712 62
    0x204d2015142240c4c01031082080000790340c0003420038a038000c52082e119a03450388119541d106502400c0c2ea6442d8030300c0b640b5501624500c010b0309043d1549000d010310701300c4c0e0303070316500000101000301e50408615180048c07002168520814a5540c0040030784101000303845080c800c412110481d0050100003805418019020f0308011200d0352000c0b4047d81035000c2d0702240c2980d43d8641c1401590300c981c00c2c0b0400141c2080050400c0704d0104400c0c0c0f101094014041d0b00034130307a210941e11038044180c20031141055600c44900c03000e002401040d400103010f032020403203410081c07807095072072003002002800250000c0308407400e04160303922603000f0140a0110000841e04d13207444ea4595004400e000c105130314240114000324161804d6940b03c42024002813400016a203510b800700300d00d00c1d401c03680551501c80b4440307101e009024125a0104140070500f80840b96400689901c005255888030414240302c1d6803480da07030001c11551903003030740c041050b12a00e804008403030034085e035208185881d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 491529406 1250 491528156 491528207
    0xb1203040e07121404062d020405090a0510050907090503100203060118030302030d11071505040309060c0f020906041506200a1703060d0c0303170c070b01060f 70
    0x401244010300c01d00b402d5480c407114400b5858240110351540c0d03001c080143c070000026000510503441b0b01450004c0c00c405041a1881c0600101c140214001c03810640390082420402c82c140148400c2c0c100c0d192820a106500d00079041e920302c1010303842590310404411000c659200e001d0f000f588090400542522000500b241d0008082d520541e802400602e042c103076401100c0c011070300201aa2741c107501071490040300304400006080c0e02d06030040c1014041040340b00055031410341740e010300e181c00f00c049064505400e0203020285107074050300a019110040c0d200140568084205180c1d040350203078102c0d100c80c0c3c00b0900400c154181407280302c1002c0408030320503420801d44450f86103c01c00342d00d1806801220681c89159000c0b0003002c003559200d11000e0b500316140030316030215000d406c46d02001e02c01d84807032292400c107500035000310b03007250081c18010000b411a20750219141844914181450342d44105050052090701c1c200b0074a01104801944182032002c040e0302560040c00d4003c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 491530656 1250 491529406 491529419
    0x14040b1201030b16020d0f030b120609010507050c07030f110628050c0316050f07090c0905041a0103150b040902040513091a060310020406030b040c08190b120304 71
    0x100800c2c0016502c00d0605400514000020542a05101d10700d038054040b02c2d003c100c0c00d41e0022207a800d24014151114001462601c401d014180b185800f2801414241020240642150300140419040210030002e107940c510000550b01f08a0341c2c45125500420b0b04e07400c000510f003680c0c02d800ca13400701c0700046030000c42e10301061100c1d808507021407140095000074400e0b03899218018030078905030014030100740a01c00500d000440c160080043d500c1c102c400c41c0080781440d04540003ca0626514507480c42043d40c41615074018002c252810000105401d581416600115280302e04040c0c90300751000411410a202800520f08008030a40707558031544410081d4005001d010f0003103040b12102040404d181c006c19170100c3d00100707000c8091070311440b0104c82c80c100602c3c01d901071044131f03001c00f030402c0144000d000a20031640c00090842c0100d0800c016180c181070350004214030003051001b00e010042c50f48203403000001c4e0005162001d40301013101c202d0003401300d04c0d1a00010400041d174 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 491531906 1250 491530656 491530687
    0x9141924020d1a040203070c080d0b03010e10150608010b1b010c0e1503010308030f2206050105030c090403080109020a1806180b070b0f06010e120c0117090c0114040b 73
    0x405102480f6034032968680341448101e0200321a100005580041d140d00400d13000e000030900000d040c00041072a0075958003090940d842002e001c15690300010350020503e2071845800000040440c16030381c6649420402084560107000b070924001d000282c00502c900108881082412004024132000859032009024425130040300380c081c0c0c168240c03071402601c000c1304490607031f640715600b80d045444103d5002c112000c0144800c50046500045041141340c00401c001420320400c400704d100c0d8104418541050072443d01903015241c10300030300001941000c0c0d80c41c1035400d01d0a00580300d005a02e81103c50b240c0300300305c90200ca0442c21000c51429800319103c0b07004e1005d42d030780040342c681d11a5203e685110b500005020541000041861111745c1c2c07400343d412410514040016040a04c0002e80150141e4800c1c0141d51008805a50b90350b0018164000c800e80c200c0312250519141c140c045d101d0030070084c014100b0150302540c41d080003100d01924084d1040b209126200c520810f001042c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 491533156 1250 491531906 491531921
    0x14011d100503090d0c020a150210020c0304051c15051f08030301050a0f0b030c0708091201050105090c07031d04110406030903230a030b030106081009141924020d 71
    0x6203405214821807106010303c102041580d4084c07c140c1010786814413911015001c0c0013a0021401103a50407994649107001400d044440341c40030b036a030760741b800c4108034502880072812100d04407155039540100e40d1526107010054035034034001c1000d1307031001900d154040b001d582544a8249007007020400c2803000024505070390041d520011641d848074100c40611900384030340800504204002a4201003180c0541a1700b0301c603000150614400100094084460300c3d16070040f40c0d1366030010016413800400007600001c0003008a4540403c41c3c50003081155a409180d018185c9000701552075100d80d8440140325084201e481c2d29543c0721440100903100400055001030600340500071005509550158208112440d0030f251000c88802640608440102258155038035900012070842c1449000840d14400c500010804804c1c41d225a00c1516011340e00d5465100c1d1315004803036281007c3c3d060070301d6008800c010081c0f0302601c64064140a100c184402103002003181c2640709210380082c00c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 491534406 1250 491533156 491533171
    0x3090c12032c100f03050f22020f120a062301060f0e0612040506280504020d0209041a060105030f070c170d1d060610140705070f05040f0507020d1407060501061709010614011d100503 80
    0x7250802c90080e00b002c60403842192041012003b004200103801502c101610440d94100055524112400100706420541c0149404c20707180c41000300f001018014240d1200311008002040341c0014541c1c07692250300d5503001e8445584501013410b41d51594102da5400f58003e20f500c0c40c510701441c2100e001018440d50704600e4480d80d021400543c000d8090701d22a4552484040340f80c0c4c2c407200c04407550307002900c1c03d0301c5200502c1588080e50150100078000e103450302402207000c5c0c010290a40451108280d814252b400c2a01400120b58510000f440c4542c0c0380e251803c141c06000c2d121400c03d04c50103900504501c6600d00001b0320b40700030b01c0d20504681c021101004442d804d0030201064820480307031031006811405001c40c5981c0140c41c000910000304100904190342941c49800300c030b03070070780024000c0307054945e5810300c001114000301d40c0f08190740001c0c1715072490640e007115044640400310b0f0510245500500070341d210300c2d0710300d510403200400399051504080409000d80d4010303103180307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 491535656 1250 491534406 491534411
    0x1101180510350f0601080a11070c0303020304051005130b1309060801050a050a02090a06050307090803040b070501060602070f030807020d0f0303090c12032c100f03050f22020f120a06 80
    0x8a40301400f0b030b806445101c042c0c40c2e42045681f00c51904c002446180911044a0006c0c0080703004a00040d0303001c0c000c1c0d8407070f40003141da542c00d04040041d40e68044564400b004400c00a42682201f103181e00300448805003401c5841e02e0460a450b11821040e81054031024a4102e0000300110150080c0c0d01501300f0003800c010603210750895005901c110241d10f5009088103030208100c42c8110010b45d03003c2da075440c5c10700d00305440300d80c0103040d0380c03050b40900c1c44000085a1203090000070f2013000014001400209a61807501c44404040052484050505107010a070002592140c001c191301325540080d01d4603602d0340070700d806801407425032800d1b25404103c110109003c0791124580030455050b46072111003911081c0008644070b000e19895204000d07468920007240c5a15030044a000000e4803400100780000000608844000307021125400414041c0659041c401041810510b14005400d0640140f1b0000c58001806010416000b80300e05100314854000810301d00341051081205 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 491536906 1250 491535656 491535661
    0x5181b01030f06050d0b0703021b01060f082d0c040509241005040203090c040603050703030201110307050d0207020d051914030a050a18050a030f110118051035 70
    0x2e90080710042e000d00d68201040b507100c1000304001e5640c669001c4007610740945408400c41c4d8010500c0b03a040c03100c41090f911441c050206080490703125000e04466402007607070000390440ca5400c1c149406050089465145229030003582c248140310724450050710500230340c00e2201286071b4819420000302221040f1040103810038020088290003000c03806500308116040c07204000c000d604c00340c00d2a059202d01032181a03640c8460003904015401440541492465800d01a0a443c186510001c0e000030400030000c802c2d421105882004e00b42c2040143c41303c4a0340301081246c0c846010244c402d00c0741c0055402c140b071504104600746d500c1074100070302841c0c00382d110a41d2400703244005004100240700007404144140e000c4224105034032402c02d459555500031900100340b907001034a0300070419484905120b032107100444415000c0c40c001001101405070034032881c1c01c6020b943e201d100315400f10515580300d490f03086807100007000f030110000e0015045200c1c908014580d80340780c1d61300380c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 491538156 1250 491536906 491536931
    0xb0a0b03070303080601050d0e1506100822050307060f1d0703020303030a0509071502010b0901051c240e010b010315061b0305040b0304030806040e0c1305181b0103 72
    0x11071404990341a1a802c455071030384030054a00c3c1d04a240c031140c03507650710503d9040d24401004000308a1a0944121549044c00c8042c01692039000c1c1d01c6105004068007844841110480f8801c40f1040c9100502c94000ba01c0c58a02d007148100e41e00a0051414910050480021a4080032406a103440c0800340449500c06071510750b02c143c400a540740d0410b200143c01d40c100e6070886588140024142c0d03086030346030746d1440403900c11712000b080141e55a442103646c50801466040c05800c0c2204c0d4691408903104002c0b142c0c0150303c0300240b0b1f0540c0ca25000c214a040317049180e000e41038802c801d00c4442d174602d1409008210410704c860019007010340070030071100d00e641c40c44159111a030301d03006280040005c0a442e2405810100d04201080000040303685204010b1801a4800d40e524025402d0603020802907490b580e1440d50329400840c0e42070300640d504100d441007255091804141581d40c800286d02c100c1c00129503250f2030256801076100e180a0300030101e01403800341c07010001c0114014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 491539406 1250 491538156 491538163
    0x7031e020c0724020c04051b040906231309060638030105060409020a17150306010b040b090d05011b0809101e0207060902120a0204062408090f0105040b0a0b03 70
    0x6101202517040307101c80b00c80d541816006035074481d41c588101e04048000040c4002154030543c000342c10665280c1040c82200e0540e030701011002c2c40301e801c1e60030006a038400141c05107122204041400d0b541c000b00020089150041401000c1190048403803000300d01002803000300c0034240c8120300600d00c1d614070b0203440072070a0b03a06070b0360701500f19410582062001c43c020340c0036040c6901880441807094801910b900180b81c0b0454203852804200c000030020b05144c1841a0030900441d2400d1006000c407681d2501550764041c01203400700e182c0c1c2c0345418401d006001c04d2a0400d02d001d4002c100d5440725411a44241c09074400504841c050760842714494210780000c41c0d400070f601c2d00c0c04107961841006c0c3c1c01901599000d034030700280744c564690001c0d4069144200a1032142c02618449040d0301e02032140c0380003028001c030002318241c4011600709903401c40c1e04116061214500102c1c5c0345880401211400c0c481410080140f42402d0030017040844044680740c01e0f1071304011850781c0300d05010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 491540656 1250 491539406 491539469
    0x30506090d020c120f06010605090f01020604030f050d02040f0303030507081302030606060307050c010c0221031306020c030c0a0602191e05090310110304050105060a0b0307031e020c07 81
    0x20342c00b81200c1000201001084000403074039419a00c42c0c1c0034810005030050040c0e46c000c0802d40c4400c1e0f0b41e508020240f1090008070391507a81550040810040481d0b0426107030442e16216151a0341e40741e010040c0c08009005e250800341201d02014008070400d5016400a4041d054a48038001c869a03108280e03031100780d5a1800940513041035011400720304014010b1341c2c000d40c1754103100f030030880f0b440710f890308603065a840c91b40160300c40039540080c585180c0c800c80074180b02e490308600d1884c0c201490300b00807210300c6000f03000e5603000407030008005042c070548518120034015584001910304116010b50007114903401d0710700ea0350504a13040c0307000b020103000300015850070440c1f400400c441611242c10500b001074260107010f1003820914000e200324480405030a0205031a4241803d2650840f40001c00141c064042c140083c003208503808152a4095180c2c40c02140b2010100b800043d002c4403920b40301344450020600002c0c180c030200c0c0100644040040200440200b40d0480da04000e20 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 491541906 1250 491540656 491540683
    0x5070306031703340c08090438030c060706021606060f0e0906152101020301170a0c0e1308070f030e040b1806031c05040f06031e020304060b1903050609 67
    0x90b44c00030340c1e95015018400c06076000d5801142405c494001040030303103010f80340b02c5015900c1040001c048a110040702d501c449021191032040324041c4010035a200031001a036031143d0000704042d0104031081d012250210724035100321503030580902d81800035001e0342c01a40201000c40344042000400200b0891040c0f60741401800381c5c2d1030341c0003505c0c1c0c40c0807080301c07943d00b018a0842c00a181c056511004403a001d45200040c0d4070740c5000d43c00c1070052a49001c2c543c55800400d0700d0b1001ca4825103000065503207548940c44181c58012448040b10a50340006140c0c540116000c02804002291110124001d03120510515860400c101c00c850401060550180903006c4080410004030750407030f0701c03020250841c0c9104030101410384ea4110051182c0e00003540000d000c5c402d182071081c40302c008200c14141442840089181c181c0305240f019000034030f041e4088002418001d141c1c000c80b4100c800602250b030700321543d038407000241c0c1113400191454468207002c113184010000781402d07503091 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 491543156 1250 491541906 491541991
    0x2d1905030a0b01030c0e090a0f0203070e0102070504140103080a051c0e06100302090c0c01020f0d022703150c070c03030206010f170714010c06140615130905070306031703 75
    0x43e04000c940f41c2c0283c20b00d40a20fa54514127402c8201520055003e28070715101c01c035044259038002460301c402ca4000d64001c42c18600c011000018984a0505590b440b0f40d100f50dc1d1107296104403454007035110100ca801e110315100741035003c4c080e440075030382900400603142503a80740315484003040076604c40250040901c800149590341c802e0058401c4031118000545020016a0455100c1d00005187e240c129400500703610240d00180d400407284004d400c10840518441c0c5c0000d4542400328510341241d208600001e000202180403982d42036444142c13480095240d0400a5850f0024042e028009411480104042030b030803a6101e00080360000410b0190300700718884961500d8141c0540c180640c0f041080c000412501481c2140c588040054900e444c0c00f000700450f9010050000154040400c000d00020039060f444c5016210800350105080d00c80707090880003413031164005041040300b40c05500380c1400050080d0f0007036106542c03402d80700210b074601c005000e244140740d428412 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 491544406 1250 491543156 491543177
    0x8060102120915030f180a080d05060d02190905060102030c0705060705010b0a0308070201030606050c0d030b01110f0c03070b0f0d092904172d1905030a0b01030c 71
    0x11502402440c0090b400f410304420441049000320b204d81040c1c60b101e5660000344100110b018044400044035140c0c0700080000c2074141d140c0802601c202801c410314991180001507850701c402d202c110400d0303405404c0590b22100c0640147c2e0500c018000e0383c0c0d03010b00b44804261550320000c142c80a2000d000702400c0080e1a1000300446035100031f404603032a5480312442e02607035607807610b090700450080002641d80c00172440014100c440f6500854280007061055880000c0001a812840f5009050000b130645100c8010b94040c034621042c2080380c41341303691417460568013140d641048007082c1c04950101ea21685040c0e0140910070902060355402d100d0203078110001e4004001c1d0b83d01410040c5015885005038011148410b20a40407210413003062104020030706a111a0401556041e94104410b0390b0b01294400700e40385040303461050303405200244203504400c44100b9482d841420642090341280034245410885400e41d5041c988081c2e5803595002c0c1c080c8007a9504543d41c2d80c1043c6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 491545656 1250 491544406 491544433
    0x1f060815040f0b04050709080c0402070b010509190e070e010e1b03072a03180e01050d060b0315010f080f0c010f0203090d05010633081807141008060102 67
    0xb44400c4402d255220788079140d4504545451061a00a0200c1e99456801c00e041699051030001b14022480c000c0344100400400b188030920100c2c10340d41d00b1200c48010340c0ba8085200f90200e80030488196841c5403941e448035401d000a40001190300021044405a03038403005c00c4090142110b0782d034140303004200300c40c440c00b840c1e8000b140c0c002840e0030800f5503035684400d1071406185220303036000103103030508100c014160800820500f22100010507001d450801c1c0046141c0c880c10f2082d5800b408240c40d1100800c840f9800c00d104504020b4129504003500501509003000f0a10075003080c0042010302040d824808240809210150070091280e07007880d000448413517400d09013860450000b486801030507034805241c030300842d005000200d07280d420700f02e101d64408a0319074404840303801503080c502540300c82d0255010b003c000741480b209641e00e41c0c00b000340008018451454900820320003044100f200495028114010345910b8110001c0c0c0c5000c3c0d0740f000041d40c0c140c1c0035a000032980a403c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 491546762 1106 491545656 491545661
    0x3061e0905070b090a090213050a06020a03020303010312050d092d0b01050f010c14030c0606042702010207080d120c03020a0f0e181f06081504 63
    0x1110703640ca650b0344803144035002400f02e001c075910203542e654030185402400300d00000c1d55030b00d03001450054941c502d17000381c6120b2403540c000410010b100144641c015540b40c0c000b1403070f42c3d08544910302c400ea00e20b0820420401c04000b03010030400702d4060300060920903c3d4441c4140400401420320100003030313081214006102001c4040751952101e58110b91060754401038404040b170040321000b035084005030010122000c050704000c0c001000341040d042000560300a41c9450013088151200340799142c0240c030a5005d00510045007034400e0002e02d20500495910701d80e580019420100c112038a04041840b414040c0f41440d4a40184c4044607940d02e0110301c1c0411041d4040c00c0001c600f00302c03108102c1c000001c18202c0c3c55011400401032000075a190301442c2c888041c8402307007102c114510a041e100140050307902c0c01080c42600900003c0050640e201d9144e003803000 = true := by decide +kernel

theorem cover : BRFrame.Cov 491366906 491546762 := by
  have h0 := BRFrame.cov_init 491366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 491366906 ≤ n) (h2 : n < 491546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
