-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0392
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:35:05.681375+00:00
-- url     : https://prove2.me/submissions/b6d3fea7-5a74-427b-bcf6-76beba75df92

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 70323743 ≤ n < 70503599 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 70324993 1250 70323743 70323751
    0x409050303012409030b1b09120c040b150d05070e120303010305010f05010b0a0c030e060d090c0501050301030f110a0513090b0903040803040311130e1c031505211e06 73
    0x1300410401c1071000c1140400c917160b000d040b0342c9641680d91040d1011810a00030145240c2d00460264804100e5003004180381c450104140c030100210b0403072100f04104902c0000010361001307000c020741ba0580b00250031442d400381c40d5080412006801c01d02083c0c0060324102070001a400210052007040420700482140c4603844205107c15414000e240c0c10030700c03d915051007800340326010074040501501c10f06042c01401000c1c55100d82d00300701c1e5040902100c07681107600c901e24000100b8958066030a89042c1d035040a20380b0b81418140da01e880a082505c880c0652280c40c060300082d9543d2610101640d1040384e5001083c4102e0a213000c03000c03048041e00d003a5040e08144802d000301d00c0700000307690440350403020703010b04003e0305400f24100a040c4041d550ba418141040c0250040300003d044218905080240550190381102101240c00141610751119540701d0b04010b20301d00010528100c0b1410003805042c0303040070000300d01d80b4902c031010319038045c2d101d500f03444602c000b400460b42c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 70326243 1250 70324993 70324997
    0x60c070609171516231b0a0305040b030406110304120809010e030a0f210b01020f0105040c030206090f040504050f1203010e04060e030403050703050705040f09021e04090503030124 79
    0x600c910003044075480e50009000404d012003480804080c00c0c850482404030350000035508980c10300c2640b05014a500c00700211160750030840000c0840c69002440300f001641607a10300b070515040000707485a960000c0c001f658050340300c500811140812100a40c002c520600c07040a5084912030080c2100c14000c11050142e45081c06840c2000340210454084070020710b03100d01d500c88000020703140211441100e800030301441c4000c5042e40c4a83c2c4c000001410b0907002c8a1080180b070301ca4500340c13002160002c00980c03003a09c0030001400c01401030011410004c0070148200081c40c04107040781da0481d03040d40e0542c0420700300841c0303030401d010b94031000e92401201c1d4a1136042048950718510081c00040042e86d03a00c0c801907140d9001e1040c1c40c00303140d00006481c3d860756030b4186117a0b0707100540a01803103a0b20b0240207890030034203442110030030350380607007400d050514075403501c1545013556848640040d168241f040001380c05100841c040c10003901c1007050340705480780c4002000008100102 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 70327493 1250 70326243 70326253
    0x308190215070509210d030b0a0e0412080c04060f0309060612110f030a0206070803250906020606090402030c090714070803010f0503061909050c060a0f020c1005090f060c07060917 79
    0x41460340200f400080040303035047c04582c01c081c00c800b0800038140c0707606ca000400c0d480c00c28041080841d6840300e40c1e200140c1c3e0780341d00741d88805440000a01c507600c569400320700310343c1c0c18400c1c1324000c0d04900141401100c00190443d035901703102041d440900011100000d03030210a050a14080d01c04944800d403d40c01440850100e40c04540c4500ca000030103083c0d004d01000094840b85201001400c0780030141c1c1641c1312048941e005003aa0010b4010710b000360203841d0008400b814403210303080c8510b070001c0081005582420501c01e5810024082100b003040300000039104550080080820031b11800da095542e614210840321075603041c2e08403034460342010060004e0514442e0000045040c07100e00091044124a0030b00d24003000001015002480030513500002c81d0403030f620718400c2c040381d001d0b2860a0001c004129828600240e924040f9038103001b03c0034142450240003010903c0a04002d00d0401d6000c1d000e840e0140b20781c010700005240d64010300c00d0a55020b010107005034004000c00e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 70328743 1250 70327493 70327549
    0x6021209010c18080d1d04021209060f070c06091a16090801020307050f030c0c0a08040305010c0801030302100e0703020d0f020112050402030c0d060f15060906090308190215070509 79
    0x140d00c500360341c179204040101c1c1031544d4102803402d490a40c0c0e00840248110742d16180e01d10400c041e150304070341e0300001c6d01504002078503444c145070030640315419541d0341081c0884607030368010017000c0340001607441400b4840001007204070000c1480c080d540042138003075101172101000f801490140c100d02c840c1d0340188244a0065003241c2030341c140020031718484d0389956414004110f10302035120400220300c141e41c040c2060020540040040d640104002c1c000c1e40301c170003000c0e6038050085c80002d0040c0d024606c000710214081d4000354080c082403040c1c40c011a580c1c0c0010311454401e0324203480440c0d040243d40e0444d81c104041100415210409005502d495000030380c0703e5601400c120b0003070618000c5107081120a81c400c034695141000f08114001c020707040f410403103100d07001d06404106071000205009029411100c100d95100d17a400c0d1511112984160800003250500ca095210351034008500d80700060009101d80390503a20715840e6040322081141c00c003000c8802c901e101d10011180 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 70329993 1250 70328743 70328759
    0x4090f020f0a030e0f070905010e07020307030e0405070c050a08030901050f0115231204020f01020f0a110a080618100b011b0809030d03090605150a060c06021209010c18 74
    0x501c0e0250b07507500700054508003d20005042420310701841c0081c0c01203a070003007403000c0b141e0b10071416211100c03a9502c0960f541501a6500d20403884050003041640c0d0882c0305c03510703150300001d900c201d0740d00c0e117040ca4420700c7d41c42520305407000da4121848040401080822002441140e6000c44180c1d01c2052951524440101151001503048108080a040700b00b86400f5010394450940780301c041a651600051080d507402ca100759001c9100b07642640c28009558400941d80d91350100220140c408550180e540806104240905a8015a00f04000074203800140f1186101c1c240b48414500c02106909502d420a40610790000303015203012440074230359034815a02c80c80b641d52410204254106070401c00080e00034014115031500c0780740011080e2541c5034206648140c0700718000e0003a03131540c1800c18007008080101d290802c40711002008080d01c110100c892244c0070765001460440c1503801010110b00c00c4502055a0b91251000e80240303901c1142d0751320810003411003032421424a040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 70331243 1250 70329993 70329997
    0x30f0304061b050a12062d0806060f04020d0f0e03040602330a090c06030b0301050105060c0d08040f0506070e01020c030706120903110604120801120201080109020f13080304090f020f 80
    0xb07400104001684103440c03c200d90341c1b1070409010250390091880748100d10104c0781034a12691001003030500302e000224240002252401000018546e40581441c00c00307020094114207004103609803900c1050300464040d1041030840035502c0e01555a80e410504040c1c0f6000701001040040110105075990f82001c01d0520b004004100f00c1c51101a00d032842c3c0d11000e0080c007480a01418401d540c00a50300c0d40541c40310740603039025802440345a0b40c90040200300d008400d50030314190003440c1d0807403003a48100c1d4841d50082c441c03101c8a031100013a4031030038a0724608803990808560030080d03100d000e40e010802040d6402d41100201000d5007008801401030382c464000428950f164118101003600039200703036a402c0e0006003141c1161921741000400100780791404000308000c0000420b5008241000b9001150103071074404040e4640261100254000c00c449081072000344840030070300300c0302241c2c040184031304001140c4646c101003620084501d40200c4224041c41049103001d1251190b00b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 70332493 1250 70331243 70331257
    0x91503050f071e050a021e010c0f08040f030804050a0c0e040209060402210c0d05040606090b0d03020d0f0c060e0708011d0a020d020406030819090501050301050d0f1103030f0304061b05 81
    0x98480d4440c1e40708071046c0d180420900c581200317054001d01c0703002c0d12901544956040015641d442003400403841050b5042d0105035000b070000786107800c40802080c0220b801c15045441a000c48524441c140c4883c94401d400b604000c80c1186010b05100551030644c0305150004c5089808503d015402048401403000518960b0310700a5030308005487c600a50080e0390042417013307414001458649400e600a0040d806030f030440364034003400c00d0300ea81001d070030f66002907a154000f00034060505105950080c00464203508210101c9412000030b0b407580209684660f04070010001d007810210a2801d442d90000217680c042c1c510120459003e4001500c244280e8064558204100070f60001c03d0207050300c0c0c2c002901c10b28000411085004604880003482d02e141ea98070b9901a484900444641c0b02c280f0905500c80c11182543e4003040d2581107200640d0702c0b510380200c00603201c0c4042410340c0c108043c0e007656010040200400d0107854000d030040800040c02c002620310301e203600607040f809017034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 70333743 1250 70332493 70332497
    0x90c01080136020c011e150b0d020d09330e03070209090a0519050d030501060f0e0f1306090b030703050319030204030f0c0303110606030c0402070201091503050f071e 73
    0x907800004807407180e048480c1c13408080c000380400c0d0503400000380c5450080d20308000d818a0440445504000115400c09607025035551918210392880003002030341051a001c0300107940e07150103000140c19018070301400e03100440d0302d4101d0200c0851145117100030400c0710424505102481c900040b01208850a26074121103005e0681c4175040729034507280014100410318844c041d0303072001200d2000c482d43e6506101e03008840a014600b501101074580a208074408125001580600a8050884441e4550029120440c41ea2070440040c03680608420340002d896601e00d030500c4140441d00880c40d015606030b00500c41149150384156030b078842e00707602240b00d50a02d001c603542c0781d20035011a00159080800c5070700c2005582044005443c1910044020800313000544107006004039655110704001406030042110100a000280d07009500403810405889404580d158440030f0346035401e003480d030300001c0a160031a0f0220101d03002602034004e000100745440d520707818074890008110350700c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 70334993 1250 70333743 70333829
    0x1180e060c09100e1908060901020a02060103020d020609190501030f11030a09150f062d0b0904020f180102010b0105070c0302060904090f030e010201051807030206070804050603090c010801 83
    0x1080c3c00c580d0300d4201081c0310ba00a008408024142005d45001c0041e20f81640c10b45070681c585807103940c200c1c4118038035400540c00071801003016140c0758040121040c00504030f14980b00c1c0c80c50025040c1d40d800c0d0086000c807514044140003550741031040040940640d40304010111000aa409150200922100201c1d8071080c000007008101c1f2007040d142094050f041c4109402d41145202810300c0d8010b0240708481c40840104a01265032240b103000c0b19180c201c0101d50502503000d405912284603140c00c01d40800840da868403a1030004e280c82000c2503003003102030554000082c02c2da00e0403130407141040300a00c9150f000c20f0f1020890400c4a40c1240c102d650380000c080820041c2036020380260210100c00201001c1c15000243c108008a09a008201e10380e00c13403207040c00ba0140b280c0c1c1e0300d40540c842201072006082800040c80100e0052030140e040580d00d00001d42661700c1101d5500c8203400c020200c01055800c45110f9024000d009150207101007820b03984295460b5102d0f01c00000400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 70336243 1250 70334993 70335019
    0xf132c180705030a0303050103060f0b10030506010e0d03091703030c0a0f090509090303071103030108030f16020301180c0e0f060d030c08031302032808030403030e0601180e060c09 79
    0xc000e181c0040c68043d081c0e40c80c01d581410090b0052200748001d4504e80d003400b880c1101c2e001c161003400302d8850002c10200c0d6440311a1411001440c0040c100750501840c4490b030041c0383d4a5448004400b07100381d4401c0d5072281800c20701c206403c04641080b50b654014418010500440340c2940c050848500c1c000c9a240544a01110702103c00d038000c903000303866401880040074000c0000d501c00c01258481090711801450120380d28402403003000400d400501c81d4a982c0c0741040000c1601070928545900c201e0b610381c0000b800c5500100c088240c0203d505001d41c204030307170b00001d14010400d2035074800280c907116001d0100814000e11051041c080c1c80455001c05004104501117907801c146d0071a186d1618041600108c5107141c03007684a44280c074000d14101840340300040e01d0020940030f02c183c0148540e204107854001501c00c409141d111013030001c1c12801000402e00a00e084540c00c00c910141c1c0d40c41408640c001502004180c010340c082010001c881400c880c080442680c402990000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 70337493 1250 70336243 70336291
    0x326040b090d150905070b070c1e1d0f1003020f0402070f020402030a090b0c07020d0b090109050708060105040b0405090d050f1204050a12030b0f01080c040b030a02090118290f132c 79
    0x8031076008905c5006035014030b51240030784204bc00b0303c95003c141e80d0302c9081e00e840765428018029803000940c001c200c240359801500703017500580701c0d891084800044a151560002e0260b8000b19402400d85541e5074035001071200c280c03812500b1961100140d454140760380c000c20440c1c0c000c00c00180038200c0034000b0402181c000d40c41505a140c1182c156400140c480c0020340e1200400c0c4101c9204509003c1c140d010307854184201805000c00500410400d0701c045015507043d000f010b500e52403040c040c005450304080c4408401d114521582c0a4003042d459840c1030304440300b0b00c59501007050b02e0905503038115280c050360082a4242420144a607958078542c0781d569106a80200b04c0c0c00e02c02205010118415030043c104c1c450090f2501c44956a1501e84d020b2003404612540c07600448040d503c020107991071424030b50441c6809030751450003141c1e0391074910690140465034000001c4840400c0080080c81e01602c0a0b00820199551018400d080d010928400b8010b1450100aa01c04480c1c0c03803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 70338743 1250 70337493 70337549
    0xa0f140907140706050f0901022805040305070b030f0a06060509010c05031b0a060c050c030304080706020f0a0c12020c10030f0b03060108070326040b090d150905070b070c 75
    0x40c20382c03811554852092620034050401030307400c0044070103034201040e003001d018006e07160182d0820341d10041c200d8070038070742d00002c40241800741d090200030000403000c80d00922941001d0700000d00c00315981d051841603020900d030000c0c0b140301c1061901c00107000c100d520800300c802c2c26000f4138226249404900b0054110301c101112141d204075041034020071500081661010680501c00401c000040b400c002d0301c10b40b0404210318099001000000e00081295001e4288540200001410301000c01a009540d41c000d00509e0003046c0540c031900e0802c42080400c8074000308500c003820000e11030030b000c01d480b1403000b0404410316844400311044101298007440c1501320081c2100c2c03003541d5030740c000e9855401c940800d440101600081d1401060604203448240c1c1c11001110b14140c6403035845401a0001451154030015490b078401c0420801000d44400c0102514000fa006240c0d1821500c1d000c0d40c0e41c010300d0f0702c030800d01003000455940400d41c0c0440310701012440d150001450111004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 70339993 1250 70338743 70338767
    0x6120a15080703020f180403080405100606030f0c09030221010905010c05090111070609031202010e0d0216120215070f08030f0a0b03031309150b0403050c0a0f140907 73
    0x1149400001d0507680011040112070083d1900c804000142080c0207040d0361180f0f00fa406485050080b0f00020b00c03e029281d030046c0107070140e41041050303210700c038181c072626030203003002035214600c1100021092040030404c2202c0d04240c01c005240d580440d1019035292640d650301108141889025007084d008010b07400d5020000300003101101c640503089801a60085d40054a1116200030781c09002a2200503a9242e40310318030183e2640c0c1d14201f402e540031502008654a5030702552880d0b1007007141e50102d031456000b0f0301c802d01d0040c07014400351030346602000a081c0d29003c04000341e2140c11403006ca405582a070559600a07909066500201e05003005243c45800030421861009210003c0e004090900302400141c68800c1056903078020aa1b2140e140504031004100c521582c3e801400b078010950440c0076059618214410250080e41c002e440c1a000740c0c0e000f04040c0781104000000e09000004c0110080c20250a1a80211072003411400388040001003010b10303002d20815661 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 70341243 1250 70339993 70340021
    0xc03030a0204031b0f0e1909050c150a09030f11030a06050603010612021e0a050a23150703030207031b050a0201030e030f070201080c1620040b06120a 66
    0x680d003040c540c18030003903000e403106440350540118803641450008541e80d0444031680c1034840260b040603c00781494401034400b41440c6a12000200c1d400741a00810300001d0080c40a48407404100040c4a0110000341001051041c1005032500e100e070080011001d680e000701c1300340705000c224074081e2100906011102d1741407185003980410004150450b51049105400030700c05180c1e20859100c102c0300452000703621210412081e411f041c1045071302003220300014000704c070482d900d1002c5900301d292034118110030284140c0c40c0102030f200c044907184092042e18800000d00700c01c0020000c9006004d0001c041540020b640410b26205510007140a045034050045001040c1f510700e03664036940804902080c20102900c40f012004003c2d241d86000b20058107241c1011a8011242c00b5001003c07040c2c480c009125003000c040c0d5038241c0010447c071544c4094000402d401140400200d06c03404107119034180344002442d500c03400d080e40c001511014030f245c0c09845082060010b00001c80d40154 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 70342493 1250 70341243 70341247
    0x90105150705031e030415050403080420041a01080114061e0c030a09090e0c01080105040c14070506010302010206100b0a03052502160b1608070f05030a03060e0601020a03080604110c03 81
    0x31305400e00300c000354007480c412482c2c0c41c42c0010403220030017911400c0b200134001ca0f80690026012615104214400c40c0e0a00300c03102c01100c242d00050200d8988405915035604100011203d0f960840f610b903005d4250403600807001c4034410700082c141e10484994800300007005c11110038000034074003a595001d203654145c0340c5500d0340e840c0081c406c4405102c2c0c1c088007410504405c041490200b0300c11341420701030b500c1800e03681c200400d001c090701c442650b2600b0803a4046c0034182d850007001c094030503984140b0152209500d140002450544081d080c220500140c0701e003084414054021203921400c98100071a880c0d4444859001c0a0f007099001d11146071001c1d01d600e1510b60115416451031048018200f400d038862850302064096800e4000c00303e43c5d51035220300800c503001c0240444900c58cc000d00301c1502c2d25551682141c002d4069000842d072508030134010920f90301c050300c0d4044002c0c03000380800300203034400820b6540302034202d9000741c0c1e48408201c010b0024030100d590080a0300c007129 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 70343743 1250 70342493 70342537
    0x50f0d0b130308010605120406020c030c06040b01030c0f0b07060b120f0a0c060315051201091709010801090c200715080f060604180b06040302040612030e09010515070503 75
    0x700042903070410840010700c43d6000030820364022800d07100c03100b0613541608407139511642c0d890300079801a0103a80040c841031105215141d0f0401480d44124801c1c8490b8045500d03601d09407a003d10150454140c05000e40002e200c400310040a03245150f4104c0c03070100d5440300c200d000c0f0304d85004084210080d07014a5610302c0359003000003030f9406214410442d8002160761401c01301c08403929180c044000855407002001b0718500103400218440600340002a002140c0d5200c0c0042c0d072040c0c014002503600841d031400250f0f0890b140c80d004042840e4140044082c2503401089094100c40360410480140c12000b40b4800030400140230300364444005200341d00d0908060f28203c011240d000031070348200c000032094107285080e242207039240c01120701078030304110711035001d4440b007007801c0e400150902000000d41d80d0750180304000e01c0c280d0030303000407083d00d810014821071a960340c0a0107615203000400c03894807010003000f02040341118054641d8120b2074203608510a10020140c1e0013a02c40c410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 70344993 1250 70343743 70343761
    0x12040303050f090105090a0305030406020903031c0b0405040f0b0a060509100801051005031e16060306030615030c06050903030c07061106010816170f060a0c030e030c0601050f0d0b 79
    0x105001c0d414003030a02d150790b81c981c00e0035400e880044401c4980e58200d80a00400240031b08051508280b18a8015080012120100c1e00d503800003e43e500480c0e80c01000d0b0410507410707100344d15030050b041c0c2c4c1c140328a19180c0c6070003680c4500c0280081101101c6400a000e1000c290301040207001e00424801460505c0d8040c02e0358070720380e80140012541f9210124100d41104040c800403114081c01508108102c4004c032801c52420151404aa01800e00c90710701e221552620000a40059100041d4180c158145441207800c844070840c1c10400a59051010070141240c810451b5254540183ea4840380000b01c5e00314017a50400d59500d200da4030021859075044020740081d80700c1502100e842da03a80f060160f42c0c41c0e2000c4402103414550500506c4624041c11b001c245130301c030110886030b041a0304142e00785461011a51580c20650320104101c0103549401170000d0744120800560910310207900160316001e042c45800d11600c19020900c6054942c20440c0ca40305422007035a6103146001201 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 70346243 1250 70344993 70345001
    0x10c0f060e011505030c01020604021008040317090a0308010605090d080a030204030c0311011e1b030504050306070216050612060f040e0f060106020c06040e070c080d020d091101050309060a050c12040303 89
    0x107054446d014510481d0b401d17510002e80240f10f180c00030710f046060b409409065483d0700c070142003a010881e0408800207042c00314400140241e94007030080945030003a09008014140680003041003010800c00700346241d0f03400f8404070031141c0012404c2d0343d40300358143c19002803007180c3c40181001d4055400105003d080155140482c8007a01c80500900300301110b0861840031402d02c0c404540c4000804a4403072a90240c019030502c40e0030841e01d00358583d40044c3c6002e00482d40e100040e40494030000c02e074501d070041d40c0c3c005c0000f90b80c01c1d410300e103110110445400000b0101d41c0590079012050b0003a035513070741001a900d06001d0549103800b809103880b9458903824010781026108108280d81c01e400d201084400710b407164034002d00d540d00d444104680c00c130307500c07441507410050900c08460740c911b03644010521041d042c14000b405000c145010406c003030f54410180c1c103009040c01007129604011030020340c07213840b81c00d00003950b03503e100344c00b40e83e070144c02c0d00c052640503248100000c041d010f80c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 70347493 1250 70346243 70346249
    0x3110c0312220609180906020d02090102010b0a05010210053c07080c03010905070c230712030f080c070501020a0e0910060212090d0501050403020618010209010c0f060e0115 76
    0x4403503141034003108442001140521030400062001c13030301080070442e80c5140c00b8090481e140c2c00b0030710051680340c0c481070360040601d4200c8590300040c20aa15a0240315910364000f0581d06281d20340e140100103525240008a0402959251340c002082e4100340c4ca600281140304403092512810407801901e140508265006484034210000c104100c0c05170000720f1248000c00c8600d4038582c20440080041d1401904080074811404520700002e400a029501c0d034040c050034440d1b0708113000420a242c44074980c01030111665100d82500880d5100109641000c21030600d01a41c1c1c90f980c0040849100790b80e0003600e954401305001d03441690004241c000c12000300c51034482602c1c3c1c86408050301041e8030503000581d20943c05044540e00c071001a040b84078008203201c85107030164540ca8256182100c040380142c000400f004880002d814650152442c1903000b1820f1a4100c00003801c06a1141070182c417001310100d2190400c244e03604a841ca0761450002406210f076090382005111000e80 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 70348743 1250 70347493 70347517
    0x40303020601090b0d0807020f0a0e060a0e0c07030e130603060605010e190e100b07050102071406011a09130c030501081207020607110613080622050a03110c0312 71
    0x84000a4014110302504462500c028860005841c0550b40c085842c7d0010b5012a0003100d100d00f161030507a590340b000c5e8014582d4a5800e50349260a0041059021031900000c460584c0c01c414440b90080f21005d540e031495250411084000100002840f00020381d41b20030007280c2030002c0802007008503004070040310300a8a5001c0002411400c02c0603507140340e000c03004141c1c15010100821000100c165030440061b044410b542921012008070039405601d099505079000946102002142c04141465031070101c00307803605d541000b0401c203400341034455010304820080b4045182d0f40c0c4201e508144074682d150704110084511402401803c000d12682c0c0481c01030b129004c1008002e8000c650a1b1540208458a4240c8580e034016101d0b8a102415070001e2052142c56001d00305802d0705000f078507200004010380d00d402d40b00038420304282d1344c445c0c40a03c000841c0b540041c00008680e040380303038181400703007038108117541c2c2a24003000140c80e00d0b494443c600d1044400d005150091072007941071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 70349993 1250 70348743 70348753
    0x3020d050c090303180a05150c16050306070825020c1302030106120e0102090402070803150406050d110d050601060549090605040309090b042d0b0d0302010204030302 73
    0x401c18031070706405400506500b41c2c00410a141e800b003000c46041a80c150002c003c041e606031940d000c202c05c28200e00c44d00c048460001282c25a00504120b8440250140190007013509d0414001c213440303a402500c41020f0011420100341c81e42c00e241d244440d450496401d1403400031503100000d6035400055142e9009007100950381d0050b44282c000c5070305030780b00c64881c00c0766849155030004c0180001038042009540c24482a1015540ca00081420070300926204d9103904141d0411030b844460400c1c40f0744114600201000700b0b8803070100318822103410049000c80e108910f00418114800040001c0c6240244d20022034500d070448041c11201c2c0c01112a445c1b0894030143c080070000741c6408124681e4800c0802d510317084031103014a000740c10041c4010400100382d42d43d807416168292400c40c00318101c149d040c01001d1091007805103506044500740f25004000e0380c810b0351540c449540300041101c4040c13245d001c481982000108440152601c249076200b0300b0300a000b5001400110018050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 70351243 1250 70349993 70350001
    0x308070803040201170403021e0a0506040b0118020408060402090a02090409120e01020313031b0306020301060f0e03151515034201030207111e040c050f040b07140d03020d05 76
    0x8010641c031b1081e0f92540040c80f490050003a40e010f024142c0005401030f1140c40413050000b101800b00502841c85100c11600035418800e0080c42c008940313803c0d220551042c88200181c010010700306800c0380e010795200b8410741b9900400b40191060040d415001800c0ca0070010030000c412411408141d92a03480340502407643c0c3c0126128803921004010741c2c0c040c01e0090002c5005c000121200400bc0c041c0d0455180d0369903651003d90300b00f60700010104582001d940d00c603540044480d00301542c03c80140595901040042c0200304001d040c3c03240594900760200001d1711208004412204403259294582c60444041e11500c000e526102040c6003140742d1100c0e06010106290000010a5280c00075000b00140110001d400a410544240f440e002406600d0b450300252080d0704104c0c66880010304090409001c20348548003201420014104021298040c01809850640340354035259a0b0b1100d1908242003101c400650200c80c0d400703200140d4100f40e03051342c024192800025418045070352 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 70352493 1250 70351243 70351277
    0x609060305060f06010302090a060c02360901060f0807050406051210020d0b04140609070503130f110a0b1801020304060f03020702010201150b1803030906070206130308070803040201 80
    0x11844020702690007100450115031408090760b611100c18940141050042800140410b01076070100c404111000550310a41c1414a0b40c0e000c0e04110481952038000020702e26581c0c20015050b59005d0462600825030429081d0407450003032202043c03086140d501c03402481d4a600280c801c2c580300f6403801100146c14141042040081466500038003901c00040100401a40c00381034a004143e03599021b06200c1d0381c030341c407c495022100034041401860494140080103070090007940a110703050003040380030140100b001c01b0b1146e11084182070701d102443c0c2401c00d15010660b8561240344246c0204411400c000a002c03040412641c41041f5034292005903240d2156002c2c080004401e45e43d2964128003940040580c10701c103100000c2c0d94a0882e40190500b21280c01020105400040881c0900008000b20003540402c401039403810081d00006100b40c403483d00002d000751404510000c0a0aa84003034134002c1d50080040c030703901c4c0c00d1071411010684c4120341c04ca01065500340110084a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 70353743 1250 70352493 70352501
    0xe070305030a081005040606050a02251a25030f030203010b0d0203190c051801020f0606150c0105090a1403030402130e03040305031c0501080303090a030f030209060c0f010609 77
    0xa4215001d140307403074550201210310309030003042546001c552050015140c0c851344038400041181d5030b04d0503111107000f20001c1c20001014091000b07008040c2c1c2070480750852255280458807050907103401c8241c4003010269034000d024a01a41008034240b85421000c540904402d10f4400d80da012030903207417000305404900083c0500401110240000700303c09107580c1c011a041122084003401c01c9581102920035100301428540c0052b4001c10803031400c0e040d1074003115104030240060f011410a03512090781d581030040690340700325011206030713000c030300e20808490120100200a2100c1e140c480c0486548100900c8121170004241c03110560005011007960b01844e4010400215008045058806890741200501860004000000011f04204024a8951400e90340b886a8002e40c104020890703034143c0c0a01015001001040000c02d4042850b55042da41420044c1782d130041310500700e0090050700181340d080500000c0003070701204001208005010a03000903c141900c440b9684c00351 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 70354993 1250 70353743 70353749
    0xf1406030c031216030302040320010801050a060806091f0308030405061b16050304180e12040605030a020c011d01140105030f0c041a04060b0706060b0307050301140109050604090e010e07 82
    0x500e07024404813015101c0000c40d048800d020740b80c003500341a126154000307000d60550398030b64540020300d80804c6035600304140303a004003011644d0f400314502d80a009415014001c0c5040d10640850000840000350b120340040135003501c240e0100d00075100c2c5800090b0380c0c026107080e240c40c0303e0a80001c2c5100080e0101030003000080329074904026030b440702c0400c800400301003160300d1b00060101103642c50f000300b80030b81c007a00e070000c0100d1f081d0314101569040c49040000e010030107100300824448290418216a041951040b00507075645400001a005060070803101203000c070036060715480c00070150400026002c60302040d94141e40d0711010507580305800b40310b0405540010001c0d034114030f05507001d82c001c0115204022801d10f28480001c04a500301e03003005001110124210302440710034070480010386080100c0e10b14504051310f02810078001440380b600b03a401042501c48041c0d105619143c0108405020203840c2c0b600d8041e114085d04030781c12402c015618080910300c050000181700011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 70356243 1250 70354993 70355023
    0xe0306010f0e06030f0316110f03030a050c070e07030c030f0c080106050c030f04030f05071a04050d0305071505070e01020c060f09011115040b06010e0306060103050a0f1406030c03 79
    0x15070720b084110044480000c0c070f0aa850700901000c2030010703106000510b24a80c0e05003ca48650716946001010078420980d007030f0090420303100b080141c0d280081250012a61414010340700c1c0580140c051804582e80c0202403048080310074048440d4143d013249245c9009030304c0600c10f1080c00c81d011003c50302c182040b40f00003141c0000412459000b000200011705090054a00d000d5892a40c40d1240c0d0080d80108c0d40c1d40f110305100028040180810b00244c0b9402c80d040703900d10140d40d5a2200ea008034040c191203000c01100390300030540200115100c46602107501009034074000a800010003040711804040703500141101c01941c8042002c1644001c018041c50801c031091120b07450581100d07084c1414000412404411401304100c180780d0b01c500d80c4442425403502e07150005c03129038040c080303c0c14449002e1180a1076500851025031140080c40d000500e42e480c52211710241085200038440710386001110700d201d44483c21150f01c038003000c0d41198000b41035041850b948141c1088140340c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 70357493 1250 70356243 70356269
    0x50a050309330901020a050105010e060102060714090f040626010608010c1b0201030b030303010308030106030b0409081c060b070b0a0b01140d050601021509011e0c020a020402090a0906080a030e030601 88
    0x3a0302c98074000d0050342c0c00610440750215040d030359050071200280c01405a4281c0c20b4100441c0d582c2c100034055010305a85010384000342c0020a15071036000c0c18600900c203207a8108441c0042c1c0321503000500901d15030301040c092400110700c0c5503641043c034001d41c0745542001d4001c01d60100c1402112401005503550f64a2181645102440078260f103400300d0400d600c40720003d000f694204050750285000e140101d5481d450080c010342280c46101c0014003590428602c030307000c29000780a640444c1c280c14410b04150340103018120050025030041c0341c141001103100300c2840a0010030702e1040240307000030865a01120015031714241204944101ca480410024072191040e412241c0c0001043c0110f900442d11091900d142c45412911940c0d00d07076440410161a0103907000240050040b86000c1205103800880203480d60310808019010355000a0f18007144c2c0c44140005008186103c002c01030b0350344569030551522504c1d041a8001075003c540c5428610700410380303604030350034020001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 70358743 1250 70357493 70357579
    0x15040503070905040f0822080a120503040c08070602010606020114010e0105120709090308041211071e030c03080c2b0305130c08010c121104060e0607050a050309 71
    0x200039050050040362903040b0010413000217090900580720300107e00b0b141e00c210144c3e0301c80c501594122640300a105030710122080012079a418070740c1e050b0201c23900d8065607a0340c032800c00a9031a225a40700e0900d07441a0900081c45580c107511180c1514141d5000740008040c201c46150f6016083c082c46c0740212540f0010400d81ca05030b11082240103c85c025140746640e9180000b044921111041d8040784400e4100410000ca0410600402c925070800c55101c0700801241a901d201602802040841c000203e10602c000c141e0f60400540d0b00400b0001000d80700d2400b1000b07a08040b0702c50901e441220322204204000e0716800c101c0c15080c104404204100e00c1046010744009448001d800074003000d11000b08001d80222000780c42c480d8008035800c100680020300321344c0281e40c12207102d03140080c408907100300da000b1903080310550b150500300e108481001880610804a00a059128507039024040200210192403580401ca4506190745140c402c5880203085420000b10000c1026800d8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 70359993 1250 70358743 70358759
    0xb0906041403070305061017060f0403030b0102070b03090102130b07050a02090c0d0912020f010b0a0e0403021504050f010f0b03210f0f0702040b030d0212091302181504050307 77
    0xc22041d20000d080b0b814080c2c0e40c0e260281000070944041d5042081c4403001d101d09005c4555410b03e803224000280854078220110f4050301101030300007800c2540780c1441c0e4505a20810101000c3d1910003141c60f501d08050300c07424000c4d4001303801c0e01c0c00c444440070000350641901080c0c40050390010094081c1e60007650820556000080c1100c04504d024428142803c11b64450706800d58407070035401d0306c18908040040d2905101e0401501d880e0704026203c0d03a2902e441500e0002c99410b0300e62040c064880f0f190a0f41481031b10b08a00c1015040c6500f0403042c4030300050320400410000d4001c1009500034004031054660610345980c05030b0040c48204604000c071803440001c0901c2d803281c1070400240c3e810382a025130140c0100041414041503100a40c9458032421000d0b0704110000c01000e907240a001c0d4441a40030f0342c81c00c1861000c03c9401c0c00b034aa031144200c0d03a40700054115a103000003045041001440031080d0f0041c00c1d044007512483c1d200313038100c600340d500040040151a07e08101 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 70361243 1250 70359993 70360019
    0x910050a110a030e072321010c09150203040b030103031101060b0d0e06011d2a030a0504030e0108090c0d030c080403080a170103080f030601020109050a110a0b090604 73
    0x441200954400c40d448088601c03101400691030103a602140200014020134945030030350700000d1404000b910b01c681e03c0f0552190f4002c08900503561100400c40d107200c032450040d010200e1000a500301400554a1640003d00e45c1c2a20701060098102400300ea004990f02e0155006620700840c0c10001840400d0140d00510440c0c0d01c09800407451a451320900c890540002c400018a203448240c035040540090001c0c07070141108416012600e28000121252400044c00039000002d400c4044560b00c28012000710100340142071aa5403070410508103801040110b07030a40001e042504401a2580314042460250f01498024581a003041c020020b0380d130204441107040c400c052041000190150014000030750181030a19210f00c1e103030380058182c0c0d9003007041ca01c007152428014800100103000350f0360032004040c031917502c1e5030701c10005034010310030614081c0c041d22a0624480400c404400c4520b0302c04020340d0311440490351540142c02c18020301c0300d05980500d052006004026807071070703 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 70362493 1250 70361243 70361251
    0x501060212030621030d060b070c0b3001051e010c03270806060418031205040c0306090b04020114120c030901090b090d020c060403020d060b0613060507020f0108091005 74
    0x80401c0900c00100c41d00c1c0000a896a80d04d0940d400208040c5912502e5104402c0101040485140f40000d11341d10a0b0094031107020700106110b000c40d01d440d69503800d0005401448a089619007116040401c0480c081c0d024032406200f81c0c150705109990f1001380001c03149071441a100c107140c45d03a0a5805503901d080380900d4010042c407000b00000e00d030810b0b0881c50003c0040c1d102401590410005000945408140307000b50700d0034019010002131341c80344854540201c0000009415180ca191a440f1103200c0d600240140d810921a80d05010300159014000d5100b6218006400e2642c3c11460203401038561001060031414000f833000300e4600029580801ca01000060074981036482e480300f00420341d0002c0c5154001d883c190a070580402103a0903808003181c4260a16195a00203803403908441b40081649890b10b02d85101030f101c180950b503d4101e400200c03c0c10783e885013001004c540220209034883c0040504021665008180b082d000d185218090942404d5204525000e1310000e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 70363743 1250 70362493 70362499
    0x91303020f01020f18031609020903030d020d02030702010c08010807052214070e1f050a02100c050703031508280227090615120106080d050301031505010602120306 72
    0x8184001c10090078801071441e8624072506544407101240805140e03070b0441c4025004e5880001d40700038503540344440e48105c031048000940c0e40c000c07600210341180109800c0807581400450b20b60740840d40358020b503101d1240c0d64000c021403040e1a1048a0b142005e1142c0d41150704441c4040c81a13042504001c0d0050a075446000c8030b1118410220040715000b07000002e2051080017805066503006951803030108084844034030700c0c60b1100b40c1c8106590710155040500900094454085000f806500780348101048200b10800070b001c0094140c0d03005c89002c03000203240200390341c1455402600e290070366240c2401000840041000500202d210f030495003105036031100d42000607581c10600c44c5000041205d03040b403441d01c208070312403010b9016241c4421034004404101d95040c0d07040721502558022588000d4844078008bc1c03600604064225040c24043c1c800d0000710150401300450480b03200796406003200780c1c0e204840b02290000c2c000c3d4070058110010310160504504095a0021002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 70364993 1250 70363743 70363753
    0x118050603120d27050106060809010b0303090405130f05100b040905030f030403110105090c01030e010917030a0f110910090b030f042906040c0c030e04020c010b031b030606010504030209130302 85
    0x2800c40c1100c0e8030b40f00c04c0229110781d1125002d0000a50081c2040d8215240c031000b0f0014002d5040065128050041c1c1c3c0e5001d19507403400512110900081c154515820080e244040540781c188161100030641d45030b6109030914407040b03800c2c01c0c1440f8501702681c00c8070145041090703200b154942d960020f030068041002225440c421031000784100c80c0911210130040418003110390024013502e07040e81d24403030240d16140c0d460005c40d440000040700e41d2043c820007170741d9950301590803004103401440b108805180905103591400183c00a000b07540040321010111040d00b00100c410840c00e0007002c15840003800840c1c040000d5600043c0c115102c0c00101c5058000312140000d14800b5110358508209180b040c410359051600c280580c865003071810400581c4151406044002044841809503600203100d2a500714203512640742c8002c024195154030740c3c620000c00b8202c50041180d80309000d04000701e2801d6010303104a5040b17a0703001c1e141003490f9442084001c28240e21700d130b040d0203500903 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 70366243 1250 70364993 70365041
    0x30313031b08030a05040e070c11090402011e0804021903030f0c030309140309191a0f07020d080a08090106060e01031a040f09140106030308061c0206030118050603120d 74
    0x400c0c009007800c1195580d0711744d121361038281c00301801c1c04084c010f00706200a00d5151408500651049802c9041c03e07a142182e0740c989100494080c28071955040461342944034400126600003000c0f4051802110301200349244907010300b80b00c1003644001008142c0c000e2210b2001401096985121406401c0011700c1954549a60b0840554460300d00e02070f42000071002d03018900b40383c150031000e4002c68001c01d01402c2080b141c0e122200440f072101a1500442d801522804190484540780d0b8007510807400b95200317207884c01c1180c00a40410300801c540c0300c0012000f68052207101d0444000b0358640366031700728603001500107000400922481c800100ca00410304d4845005142246040721800a01c01555081000000c10441001e100c40d906261003000442e0307000c006150005002c0f01d0400c0c00c1d0204020b016180880d48a00941110b03002c0300000782781d45040b01c45e0310004641d20041c0002e036907800815856070000da01e4181c20301424000e48280303040560041c0b22506000980001144c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 70367493 1250 70366243 70366259
    0x206011505040302060a050426100207060605030109080307140315010c02060c0601080d090906030206120c0c0f030d0c0806090106030c030204080304090c0f022107080702130b040506030313031b 85
    0x40010040d00111f00d0000d410015403940c10070404001941d0f031a22800a107400c23030199200d80707070380d58104205500800c00c0c6060084070340c004002428014020070041c1120314204403d03400c219100000308604240e072912441c032a03070449120320b00c074044c610480e00c1c20800544503524124000c2e0303001070301444420200300b030170048940a030407044000d02207500e007003400422101160700005000760801e5130820050b16018140e0744100c0c0343c80500402942c0d0240c0070096406591518a5144142c0780459500c1801000400002080176030500c9070710148a003d8038400c0065540c1a00b24410100401250b40301e40d10090030990180303005031810b40d580341c40e01c3c65608144c001e01e010079541c903800c00c680e5405c03d039014680016070011300941c2c1e05000c064041026074000164034800300080010801000308100c8007000c0e401440d5494a07020b08c0c55440003800d604407094011460800498920700c0c0000569414040e42c001d083d82c00380c155591804100081e0700380300a00540c0c9000416804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 70368743 1250 70367493 70367497
    0x91009051020032a1201030c120b010b030a1b0c1104050601050a03091e03050409050a11040b07020301060302060a1107140f131407110d0507080d091104050903040303140307020601150504030206 85
    0x120405c0c00c4049541141004070703034034801d98003e00c2d02d82c1b41c5010710340c005581d102c0c51a044a44500f9641e4880d41c40301c2816001c0c00d00c50b010020341807400c1c4400707000c2d260000501d85040303008081d52803031900c102080c00100d920507100680880c0c0305014407051540720703811101d11540300705030006003081d640c40c248400000d190021408140046418002480c0901c109544401100014030508460030360700c1400b032041e030007680c03408100001e4150954409400c410000e56015142960710101404001c1c40c110060801c87c07100d01801d200020580c1040d0348059810f240100100d41142c40038003000b40440041120130440380e00c901e11104030340c1e2442032a074801c201c1502d44a001001e110750160505040c120fa40c0300b400300034880306010601603002d40c2c881d0b80844400284802c1d01d81450740e8500400040070b50702034141010813030003a034080082c10482c1d200b605c54040b02c4101c01e14100c2180000c60380300d001130380080010410150905c000100280103414024a0706449401080080d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 70369993 1250 70368743 70368757
    0x15030e060109201201120303060305070905091c09060c050c04060303050307170f04021210050114011805060304170705030a0e090c070317091009051020032a 69
    0x40b0b5580c500904183c5a11400c100100100f59102d61a01c1d00710081101c01041c1030159007600140000d02c441014000e030700c00740140d034001c1c3c01c80e40700c1c65075000c5400140004803001f0045008040034250b41c0413030b104211000340040e0b11510482424090300310344c4407400d904180c50324821603014041546951007020302450103660780a940f8a406e980180c802c19410b2032607605240004204281c03c100c030032016801550488000800125502c01c40749800340824481140c18070303000c0001500d04200d40d5084490600b80c03507a030602c860500d183d00d100480d511410303801000410000d00000c0c94400304500300020f1801c1e00e410a040ca8a440d407940c2c20841c903c80c0030518560707520100f441c04c074184a6000c0381c0ca21403580703048410758008201141c0b801c2404540c000050214000200520605003810fa242004004046e024140103a503100700c40f0600700490325200001d0307070459440f415003c152001310703602440d50315840c2e181400700780c020345d400c0384c05055258025101d4182e18010560 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 70371243 1250 70369993 70370009
    0xb010e180a0b09070f050a0507050114070f030b010503041205041206060f05040504050a0f050c0310090b0f04030207060e0a030611090108090309032505090412030e011515030e0601 79
    0x8a071500c0900e007412114a04112482101004100100c031a072007a1552281d00403440c050b0f440705006003007a86d060103205c000400c0765003082516070013181d9041809200e10510395410325124250742080d411507c0c00614107000800c00c00c001400704e804c04107042007008c824904145419914103081c0042c181c8904215281d5448003c10446100a406c208014040071a800c0000d82442d40c0d070f03e5039815031004014800d10202010805000050120007185000581500c40056043c502d90005000c3d00c44100c40318007d8030f02203074060400f144160f1049030305800803d90b0b03d090400640f1091301c4000e180303034807425640380800007400c1400344041004c9140b02a80e12880b40c28005010904001c120315400d070b01c1888200e071103643c002094800c15445e003802450300603804050003000302250304062b0304403051030b06203c1000303582c0202c00e400d42020354003000404403200102d400c2c2c5900040038400c00044102c1407101e194065041c100d510114240010790290a43c00c8504006003603014000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 70372493 1250 70371243 70371289
    0x1419091407030e0c0f010e03010603081b07080706090302220609060503061f090e01090812010e0f01061205060303070c0306020429030103080a0c0b01030b041202010c120b010e 77
    0x10101c1e0b00750040e240e80341004000341c030002e116100410b20825600c04444c1c104040d404d80701025490a5100c20040d6030002200c1c0d80d1008181c07500c143d85e1800d001e5000310351040da100003400e0b20004c9502c40907940b00d540d0300850705d880c44d0200701c45814900f480300c00001280074407560171035551007400001c007202000801c5591802c1e0406080850052440d17144489412407562a111099640c0b0240c0e01e1402000403220720562805005014444005045400014026070b81c8040003405074100c40e142c50220020b540c0d0071141010040007840f8440c00300b00c0c080340d00707920000c0d41d400240e84028080c04680c1480241e482c1e0324601c1ca002d074416038000b036001030103014814611001912240708414a500000040550301049100c14072000c1c00c2044081100303170519202d558032140b15a0045400b10f80795031a418413114180d4140c03004c0303400c81822180e4545442c0180140b00e90704060351038600e0000816881400a00080300c00f040c10008080d07181011030761142d0220032002000c1c1083c0e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 70373743 1250 70372493 70372501
    0xb0402012f1501080331030209041a160806010e010c020d0b04051218040e1203040507150807081303050f12010504050109021315050f070303020702040b040614190914 73
    0x41c070701c2001a042140c090700100300045d5030403113042c42c6da6002c1580340c15458296090703500080001d502500020750004da08002d220501403144a43e090034164094111000d40701c8403c00d400390031071f001964003c207030807000180e85907004203021400e100e0181001d160340c0d0210b0340011490201414111000d07495007003030000307028003000505412001c201449182c14070113281c60113000442c0032414803a64940020002c1c5840c140031401c041161000d10b0740e1030341841d02e00551109000d00558802018012102c01524031608082d401809252036942841e12484540126031040803010340500c50100190f0304041110340003000e005030700c6000b868203035042008110944506a01c5112000c0c018010140d079034408005800844164240e441c1d002140e120341542c2038002c02e200e403c00010301240281c140342d01074000b001001d108503010060142607034200011200580284840e10310780e080b03032140e80d09045d251121318450a0210800300341e0344002d03e001782c0d0079850b40c200c055042c000c140 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 70374993 1250 70373743 70373773
    0xe0f0403020705040b01020a020d1e0804140303030609010e04050106030516030501060b0708030c160602130612050c04150314012403020a120b1305072a0b0402012f 72
    0xa4005000101c0b0148036143c1080300023541ca038160b48010744142141400c2c0000c110949004005c0b0070b80703c0345944000401c50600150700d030010b1090a051003c810010005d910300842143c0c4513072402019113030306900b000d911843c0744d17400901c100d40540d40c680001c0045802048842400303864202120322280c21450071a003511030b1940800b900174014010440054410000e5070742c420801038805403100314244035003480e0b10309104050881c910019032003400c4c070004009030060741c0450301e0b40c884c90b010010080c070071900202c078408000d01c0c0522040c4040005000f60340004040d40ca404070386140c200d002004544020f1748944000c0c0003000c600780c2c00500305000340140100c5814110f0404410706405082540002c0305040059a45d8116005030f5a13883c59400060942030400c001c00c2c5080314010301013104001c001400c0d07070b40b03281480040c0c040c3c0008a01300c25600249120030342d101c990054641e130008c0c004884118840c1244188010b01020590304400d05040c01043c500000b03d441c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 70376243 1250 70374993 70375003
    0xd0606051002210c1f02030f06030a020d08090402071509050d0f0507060b0d06020318061005060414060c0d050304061b0e010c030915020105090d0305011512060e0f040302 75
    0x401950440503143d09501c0885443c01d007503040d40d41040e03960351400344520f4104603410000c2d95450b0411100e45501880f280d019604c1500444000c4da0302d0380b600d00800d991a441d40c1c1c0020b40c0454200d150100050048015068400000e0305c05402c00342c3c0f41d9600703485010703c241142e1400d503480a00c40e0510000b005400c0d920600784c14001c128503040d02008099201c1e00002404c4540c0b00c02c046401610381615113080c45400c14800c43d280d0400c0c103140c40800b001c841d081403131445003c2c00716240c1c00490b03030504119200100000d26061410950440300d210009582d40d008400b440b000b03500402c188003007404541690b60312030b500d142a107000d001710b9001c0d1a800035910301000240640300d802c00c124588064090806440c0a155490100c072111a00e0304071000e4042e03078034000740c1001d0701500f049000e1044541a640041d000d91011412654240b24800c08071003003e040f00d842a015000b4400c14500b01100420015200c01070a401000e0940342504202c400c142003209050f81480 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 70377493 1250 70376243 70376269
    0xd0c08010903050d0c090e010b07081605010c09240305090c060712030c17060f030f0d0903020a08010c090501050703030605270618011401030902180f0f011503090302010b0d060605 79
    0x205494040d0030851100034030007050007907043c01d52780016502c00744008d4809030f40e500c0c03006d403484581950702c520b0624003038003a009601c000700e1000d80000c90781181810450242000c0d0903c002085040a1012006400b0243c0800d1450003240e43c1d00c0466111900140000350080815061341007214030000c0c201c1d802c080705c900c1088002e0306202c0b90804141c0c5059000700f4121200c0007480b1041c00028106a0140c0c00758140344207103c0c50003207854202d5000d0301101d000300c0e5000c040c981c2d50119542640c2c1ca201c11440044c070324039403d1011390300907000307800054020f2030002100c03611500403810030320b5102c0c01c0380c44074000240081c00600c1441c0d01131f540180159070f00f05a240c00e1000e07160700c80806009207010380300703400b01e0b641040c1d00c40da12081328183c00800b040411400000c0803242420306031244403110954900080c110180951880d040328071a44900b4492246420210010024900c003107085540305c000f910080d03903888001e520f405029800c00a45140b5180030401407000c1d40b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 70378743 1250 70377493 70377497
    0x302030c0709020304050703030f020c0409110a080604020a0924090204170a0b010b0a03020904150302040c0c050d08040201050c0318011d09150d05030408030c0d0c020306060d0c08010903050d0c 85
    0x10170400001c2000c00d0303880032654981805682158000c070b041e41024100b00d90b0700d4100c3c2c0342048a50602c481e82a000305c803944161501c10035240c0b41c034181926580c0455010b9000341d00602c00300401196507101c027030355118a081e003032517580c40c0f15010030880200343e0200e401650081014890125005184640008840300614400803181c1c4ea98201400502c50410342038004030710b21043c40d000e030701220641d07100140200890440d140580e0085252400240d028070328080f105000640910a0042d801e40c101d401000700350102d080884007510b00800c00c070304000007441545040741c010806000c2c484d0030351800c0d07800520300100040c440880100700c00c1e280d40b2002d01d01c003141d403510740303a031604a1300e110200d600c41a41000800c103520601da2000b01244400280051001d1340480603010000c5038600781d4140c10304840d0110f481d0080e440300a0b5040e00400003084a62600c45c0b02201214882e5012418280c0d8840c9190308441368041d0079408a80c0015151154031658490750300c0405040c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 70379993 1250 70378743 70378747
    0xa1a130210091a071a060105090301090f060c080405070b090d0b010312020d391a01031407181d0607090305060a05010e01050d03050c0a0804081501030809040b040e0a0302030c070902 80
    0x9a05c981c00813520300701002182d1004100410441c0c1d10a00803a0303a01302c00a8000d0084495900c0c02090302001a84252003030352034a039011010b00e105a4801d07018030342040c0240401d5041100c044202c3e409407420030303888001d03652480b00040c0d080380aa4003e501803161441c00585a81000c2c0c01c0944100c58402040400300310000d41d01ca12001150002c2981200600400e0204000c0411800302079806443c003442d00150045984044402c1816207102e011a0348080e4a00d003074240d5102e049001e89a11110006c0d5501031103100350b44502d0b1146e244200e002010360382c0da000d280c1051030640d007040c0060059042071050010030040b840e048015550300700320740d62601c00094401c0300107006280c45801291140c0d81854480c0003610100c11042d4285c80b40380490340303082004c81d80703c1e126182c03686c00ac800d520b0302c0d20304602d0061070407244c0040d03240d4645800c110400005203000f410184e805642e079159503c610604002541c1c1c072a03c0f0360011070703035500b1015445140c900c042d4081c10703981e401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 70381243 1250 70379993 70380007
    0x18121206171c0f1404091a01120b0604051005070b091e030306030a0308040c030b01060c0309051e01110703080315120604050d03020a050f0c010605010f020a1a130210091a 75
    0x200542e080c28102d503a02d018244e01428440508443c0702c0c03940f01501280c00e06018405c00011500200100328090700e50510302070300500310800340c031081c801c550b40c0704a051008201a09182c2a50510a2080d2030161319200990351041c0e210442035a03241100d030b0000c0c1c48029078451007801c04085d146048011421890402700080e030b61541140014100f00b03182001c9010008031008444c0a140e02800740212036031100f20050458107248001e0300003d40310f00d80000d41c2d0030a074001030740b241180d2402c001003290200c010340300c55072101d010801500c60f25400102042003030300591301882504000310300e012412001c12103840c074100c00408050700300c2400e000c0010381c001014404602107080161319002204025107050107101304459100d240041e42071905d88040d0300031420303104262034620040302402001c9943c0c8001e40d01c0180410b00c5041c003034101421085038660f00484500140c0e80840381540031501442e54840b614012840c1040c0501640400d41e44852003200811318460030104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 70382493 1250 70381243 70381247
    0x308040b0a11030412050c060a140a090305191206140405011403070e04030306050a0b0d060602030910050c12040e221e05211305030118121206171c 65
    0x1202804c0205680301c05005100c040d0b028506036a0743d41c00c034009460117490305007840c1024026501d1105000100040050301d000103521501c599560036030354442c18420485800001c04103d002c5001c01d12410f90018404800c007409001c024060250707001160104040a02058560607004106041c1740d0038281c1c0c00c0d5850009031201101d5401c903030024540c0300ca0405600a04442e005140c1002d06c280c804116100a10700508008500c01c00c10400b0650b10340007207849015015166910200e42ca590440807445200513142c0d050502003640c540c44020b030b041000640c0075038006500424406c0401086400c040540301714100c00d2130404000607120307965440011690400d10500080600450091000c03c01521100114804203500e00302c1d01c800c02d410241d00004810540c40c6002e68010400e41010302a01c0c1340d02c03c0c00104080461066030340e039140c03103400003400c801708099080c110100c0000c6006040080c04100c91545c60310020940e0541008080e0300c914508091026140f58059 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 70383743 1250 70382493 70382497
    0x11104031106030c0c0601090507270506070201110304090902030f031201030308130204050703050a0c0c1e05210a0f05070f14030c0109120e010216060513030f0308040b0a11 76
    0x1c0880d120707a965900e00c0f92540380c03030184040c801d00318440c400000c2501c00b51a48100d0003000c06480d020000030391880d5643c80c5001c3e0003038405024085020802c120b003041c0c1c0180c0700d000c0c414106082200001840d080c510380242d400301e8015a21105100b081d801c3c14000d52215440020295140c00c801c102c40d0040218188001810807a05000180e04140c4c03551321320000550042c000e1082d41806200240941416078502c0d142c6440c145403d40c607103000d0510309842650018807a6450003c0b901d401d0704079120808107840078020842c140602d0703d1081c89099400c1c200f0300030a91182d01840000b000044000040e40904c2010070064011402102c0c2e000482c6a0000d01d1401c211100b00206082d4000d0281202e41582005504230800060044000380c0301d0240c2d441131442c002c1c250049a07150f8101003c1c1c80b491003c441c0911400384a080200740c40b260011441120980d255918088030200c100140e000413139080c140f008015041850f142c01105075078040c840c0300608014040c0034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 70384993 1250 70383743 70383773
    0x80709140112230109050907050d060c0e1005030412030b031c0905040c030b0301051509040308040c030212150603010c050406050304060f02040f090b0d0809090916080c0301110403 79
    0x4841203070a0549040c2c282d802ca00c1184102d065441401994010b8a01a201c001e018003070345242404001800440002031800407070700014040e050007000740d15000010f1282810301e50400c20f555004031455201c0e02040d0208203265541c40343e82c0d150500301303c4400e8611041c910201410850810040e40e0300052040e00014803900340341d100703210302d202074404d0035841d484141c21504201c0c3c03040710240c06034010851200c05030024041907542001140c0303107401160109600c45081e9000c280030030302c228203450b03025104880c000c008945076000250010f1000346c2c1c10141c2d1748040c4100d09000e000f50455a040700c8203400038420059004000b40c518001d5014100810002100180c1401401e401405800320768800441d0b441c0d4032070021144c9540b041c003615400c40d043c01051200c5040200c01c001d455a01b04003110705103070b0901c0401c1841072000d0500219445520500c42d0130211040858005100040003050544540301c00e00d82503420820301e090030b003041400100042102c4480c81500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 70386243 1250 70384993 70384997
    0xe0a0504020a0303110114090714060309060f040804050409120f030504080306281409070203120604020306010c14031306090b1e040918020a0509160302030c12040609030807091401 79
    0x80800422074a0051400c403408045d480c00a07c2802510400450340000356820800c00340c12113484c1c8014031581c3d00c01500d00d8015607101c0301c001140c5182c50b15125800a100304c5400b40f80965640002e0143c1e000180309903407000301158540c01342034011310182400d81c1e10f8102401a460a600c505400e4080109102d0140c000541c560003241a48030040e10512000b28000d9041d685808020410a80b8001020300442c02c220226415a0000007500d0031b1064410b903513201642c602080c0700182d0030281c01203043c890311100d183d0008000d480c0075034507900707000010b507120303812526180c8242a403540301a0034420550750601008070742e0b2040302c1da1b150040c1569000b6074004142c0c1e110798403c680c0302103005858107030011090038110003110452402126011b405a40750802c00291840941d00603840010445a0f1807c4c1750113a0040c40d80030025859a0303003801d400b0419945450001c4034211340180e0395070701002c101500f142d0707101c1d004210303441d00039003181c00e04130b00002c100c030480b0002e41 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 70387493 1250 70386243 70386257
    0x90f08061b130e010311011119060c030e01050a09020a05040603081801110f060f060105030126100911040f02070c0e0c1c021206060f04061b0b040503040e0a0504020a0303 75
    0x42c2d524481045000906004010001540c1c0d6070418224202c040380115002414140444c544a0000144d031030f44a20042c2e58641c41d051303140c1d94071000304042c207241005d25071034080816070a8020b104142c403d41003100b002c075014200b44100101c80030690170207403141d440c095090021540040aa616a50300903d51180030101070340141e4100c5030700e4075008403912541540103481080495501d0044241301e0000049031184001901e5a0009008141581c0e0300341e14a440c0e000340382c10000035200700e080b054802d80c5440314544820340740950016504503588211412141c10203110343c4001118110045042c54644c1da100185c07440d09205440c407840403000441c039481c40000c00c44d0701a40d0740440101c092885c10305004d0103500410065090420f0300c0c2c00140c12400d16008480034010420b1714586018240481903a08841020007244600c100c0844600001ca4401c0d8403401540100011910746242442a88014000901c2022100d0404044c400143c0304d06c920507080e00d0b0305041c145 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 70388743 1250 70387493 70387507
    0x30703050c03070209190515090406020a0e030f0708070503060f04020d050304050d060527060115020c06040303180f0503030a05030c070203070f05010f02011104050f060c0d090f08061b 81
    0x2910307500401e400070317500c004410b040c8004440d0600600d243c2d031544003010702480d0b4600380078115810b804403c280d080980100014001612540103100300b400328181011920300c1d002c00310f85461303440e44215050741d10000381403180c803404103e0030005140032401482d8624041d00440c010900241000780260f020048920070040240180c5001d84000317414a030242050307090030b5000d002e01350390303103060304210301c02c40426945d081428280320200c94000384500d91070140c030034140e0b4240354109411400b031586a60703c03964444006100035400f9660b03c103610030920304d0300d00d01428964003902607030905645c1006035440c0842030700c5010f8040d090503a02c0f0303554618101214401c1407402549400f03075a03004510703802d0683c4000b050b99400c1e1b07614000b16009003400e07400c0701c0c8030040b800c0d484141400100002c3c60492185043d40201604803410101011049880c200004205401050142d0300a1000e990340f0072450008000d02c90042c803050418000c0c0c001003400d40001050030810000d004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 70389993 1250 70388743 70388767
    0xb0a03120c06020d060e01061707050a020c09090f010b010f020c04020a09090e0105090111071a09070503030f09011b030e0409110d031d010804051903020a0812150301020c03070305 79
    0x161030568000b4029540d42d00340015050040c99503015840311100e1510002c22000e100d801045886600030f80d228045844588003074402e508101d03003050452040c6602044640c80320315480340203000090082c1408006211000e0075500341500d500e0402002d41d200b500c1030340e0f00082c855244d01e0195401130795440c41d07000459003040c981d006440590300f44801e1504c04030381540f2252080301010020804401d510742111207a00c5020805070086507482a81c081c14515011200d801403e100d003195101552100400d0540d0003001c00580c042c1400f003102e498958100c86031400303045500c0c05000074000182e501030b01c4ca18242100d10701486d5203180f20f02c104900f200c00ca0318035020040c010b070844042450000c052406a82c002d0f8030b4074104590a42d003039401076606d18007696200e4003821014145008040d01440411005e408511807043c21901240c40540140840000c811001c49103203041c90884000b2001d4082c003500aa2040010002c4480007005450309207601d8503203140e55410070602 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 70391243 1250 70389993 70390007
    0x309070504020f07021e1e120a050601090b030321060102010e01060b0c15010e0103140c04020409050105010206090708030d0207030203070c27060303020601120501140c0c0f010b0a0312 81
    0x480e070054800250091150560780240242c1407003110588110004810400040044000300c250024a0255003c4003000010300001540b50060810528010f44070035440c90030f807880e20301751100d8020100602419890340104c0c0c0e0000f0003500203500d808081c07611101019102201c04d00b060450750f01103262a8800c0d0050114108084005c4c4449601c0c0c1d031031092943d20091f858103c0c0e01c2801403444104042100681c1203561140104949070701c0c0d62210400d841e10401c000081d4062584c9640980da1644042d0010744219840040ea560500d800685401c601074148030050f400508104808100001110b000e600c00c0000540c0710344851805900c0d600504c003004244003010000410154106181c0e503980e040032031110340300207a0780d804a07001c4482c540070103030050f08000014402480b0031411012001e04c140c0000418a00808034414410405d58101d0041040000d1340d500020b02002004003020b803c9001700b0078141a01d000407403c00003448014401c0282e0007002d1003107401819 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 70392493 1250 70391243 70391249
    0x402060d0218090f072d030b030304030b13110d0b0106180b0f0d060b1306080c0409020310030201030c020102091e0301020712050408010c140703121b020a0210180b030907 75
    0x1003e1040e06000d142154914021500240001d08850500400d00382256001c03040c0b512420000c1030000c6401411030283c110402d82c16010b200404c40000000e40b404085442a03441105040b00d4001601e0311030030400030450700c1c1c0c0c481c1000200400101c1d000d128000e0440790182414400101c582c1850904683c641e40030648094000c0740425012170404000c26240c00e002404001894131214010031710301500740341c8a10300b503000c442404028003483e01a03400101d000355160800d5a6030b09007200f6079200303d40d800900712003080b0800440d41c0501803c0402c1d41280005e6041403095000b1a031501c0d900480041c102038020340084542c0c03400e60440e04600e8100240303d841c014506000303009544244100d00480d0b282c400c140003054481c070810b052031900d41840303610748000f80c3c60845401c58800c0031040d60a40e1070b041e03070741c100f04543d82d488840c001c0c07500030b031054002c14010000d004a00ca54000103100e00c410a5030303d00c40c1020401000c0d50321446d0308940760b07200c61703820925043ca160 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 70393743 1250 70392493 70392499
    0x50621030c01110a0807030c09030f050307020906090c070303091406010602060405150403090509060415140109090204030f0b0910090f150605060405060d0b0a0b0915030402060d0218 80
    0xa1625a240902200520000d00035400a100c59000c04403205103e108410b0040c001603e2040400c0c1c44922942111a00c4195450301c0807410303440f40c8803080345000a50045510364070028000b411401c040c00710f0340e031101080340e8000075894001315011852094400060401d5501c504050401542c2000c00c0c0c011b40100d000c40e03001e03603104c5801030754685c802e490a4502e0301c5851010302c0103242c0070001d64895641030317458a440030720744801e011140d40c014242070740c041e0f101c005408000300c07000e0214008080c41402240103407080000076090200503000382500d40c2c01000148003040e60302c4408051698424542181da50f142440b860510b010303900628485814a00170070144101c1c00500a00b0700c3c001d90001c00020403207980755088511501c10b0325041b807000e0004004500c1d18502412002c48805000b10329071102a0010b44401616042803802c600d0109502d9418140b290310051654002c1c440c82e03241d4106500068068010441c1c412151900051107650b4110343d5218219800005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 70394993 1250 70393743 70393789
    0x20a0803040c0503060a0c0e09060d0210030b120a1a190c120b03030306010215060607080c0a031e2717060702010e01180f1b0f06080c040e0a0506 64
    0x5252440207840b15110b501c4c481c0c8038580100340500994890031040f032601c1c1c0c5501d00c07940c051000740300710f400004000c1503100c0384650341080903031200c500c1c4980952103950005150410700040040b903003041240701daa032341d128841110000381901526400c0004481c160301c17041d6500c00800400725034119030a0031050814451003402d54014020800840301920180241c0310150141907403400100e030030a0059000751081d00d210362001410a4100101811040c5020003949421000d58420006841243d00c060300d10403c1c540e0051012480c00d14540c50b80b180240f500c1c000810040191095481000c01ca00c81048050285440403008207230030248050564022003100b034070762034201d4a5501550800e100340c159008184150742005c041c80b03990300c464400b40c1d1262813201d03c0c26001101c3d6855911003580000311062a41c42c0101200c11031004078500b00b80c0010a041070203041c2c0244550240001d1100070645c195040d0711501c0392000003440e584a40c001010a01e458480303125243c41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 70396243 1250 70394993 70395001
    0xa0b0a0e0103020a06031a0d030e040903090e07090323031c090212030307050f090402130f09060803120a090201020a0204050c090316080316050c03030f0c0c0a0501050415020a0803 79
    0x1a012024100e0f4021150410116982c18090302626500410712a5030a490142201140307071906404c038a0900134504285048425004681190707105141640400c00d24401000608640301c1f2450f40321066140000b0a075285580c2c2805400c03001078005052014000007400f10300c020030135181c40e41040c00500d00c01100c182c40d1b001c0101104c403400e900a00c0070498140d9800400402c80380100700070303500d1510300081c0007180c0e0001e4104414460f4000c0d001c010b040c2e01c003004050f0007800b41c0380c5840f0100c2e50a20344203002080f60101d0b4007010b5207030010300000c00003003904c1e40982e9005124001c086004043d03840100c0c00c0000458000394031614020030b1001c40100440a80052402030f8200c407003030f07032085100700d1503102948078142856001301304c0f112400c140021248001440b400880726100718000020b410754015981420140d080407850800c1e421003040020f0b21400203440f1005030f6404e00c030008100342714030b02942450200103452403003031a00c00c001c0b460a50b608502e00c16200c1c14 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 70397493 1250 70396243 70396259
    0x70b010e0609060a05090c0d060b0c070608100503060106051b10020c0c0a03050a0204180602040905060405060405040201020604030f0908120901080f01621906050a0b0a 74
    0x3809a030503a004608600008009003080d107164030549a0040c01482a955010740c558095400030040b03140d200d072150400103000c0791490242075080f00d100041c0400c503040040007409064000d0148c001504503000800254402042e801e0554805160036641d802c140d5802880701c20b41e108450940b480b420300208207112040e800b800441090f4001d0310940d0640c803040081d103110700e0002504031b4029511a800600e00381d0301c20400c2c900300c60280c0203400c1da251030f070404917001070340084041c2e0b44420030401a4600791180e10750020301218100158200b94000070342c2c40000400c028103003c00c0764007580c03007240a610355800818104044a03004038840b41000e8098101c01301003400700e0f003030f02c001c03032a00d0202d16003c03816070f29050340c1c0b91007441400310401c5084880b0f6154584080741c0b03410341441003548006107110444c02402c0728052847d42c103511150100c620680c900550020160300305c4803054007010602c0795421040c08130340b80d101c80100b0401040d01c00005680911442000a1425 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 70398743 1250 70397493 70397519
    0xb0d090f050a061d1f0216050601030309030b0109050405061605091012050109020c12070305090d030503090601060e01020a0602030a0e031204030212090d020d03020c04150f120804150203070b01 85
    0x42da03600000307601d02c0c0e4a0811992180040f505c01041c8159045aa9024440d94050b1100040c04c20368101e103246c8985866040240c280c00c02c4e03000070051141071007441401419503005052809080020341390540300c454582c8009408915400c40b1085550780e40391086003943c0000c800201164900903140001a18940701218080000c07810080002002207107482a0380c81d59101c0c401800c030060900300420940c0d40400c1c4100c0900c0811b00004215850384034a03000b845200b0340314941d6034146500c2052809005a1144c0100710110b0304001031a40e020400d8000190301c1600940c4903100c406500b8041c1000140300306c1035120208041d61003100c0c42264a0103980139409540310a480201031103680c1c810107030043d4000c460403070f0460043c03c1044510700000e00a10669041c90110790000b41035071803088091200300094082031083d100c2c5031039540000d024818250011090903070303c0c80342d140510f200714814501e19a0105903528020f00c1148c02c580c2d40b10b03000b98819038642c0211007000f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 70399993 1250 70398743 70398761
    0x6020a0c0204110c0a080a09090507031a150405040e01020904020a02030334050a02011e0209040e060f15010c0b0709060905060702010815040617060103030807090b0d090f050a06 78
    0xd1401d050b100d010f803400d8030080740c0d40062008060407000700700c1d4a03050b405500424581c2c0403c64101d60000742141c0c0c4c0c0c82018011002540c01048003130b1030f1a0180600c01d203880400b841500c903041c002c001441e41008071811240300f920041244511400400d0080c01202c103403e4006000140c09060b280e03000c801148120f000f2804464511001c800e80c44014101141001c00da01040100052041c044c4e405080d2225240c800401c0042800464400102c44820180002c50f004180e4090741d2406019040030591100f004180f10f1030050f442150211002d072400c2410032240340d0707260450340b00303207000e614841d0020880303112828003550041440100d4441e44001900c1020017045c58903104040b200078507016990800345407141e24050000007811300a01c7c0c0c2c010b40d650340c00074001d11a410648040761188018001d1503165080282101e1801001e110801500b25003c0c4503c1d1140c000f6162001200b00f40090b098505142000404c1c1c1c210380050300510a81c008003040101da600050b41c9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 70401243 1250 70399993 70399999
    0x305060f0d0516120309030807110d030e030d0e0d141207030503040209100b09040e070f06080f060d0210140912010207021e01200c06040b0307020f030703140703090306020a0c02 78
    0x7016910844c20030210020707a001000107002000030008250480090b26103240240c4a41141c20000d100103400c4091808044010403401c886071480340c5024084039002e0340c1e5500703019014210207030000d40e103003c24210051065568018a00e5004000c005015003170b07840820044e40d075442401d0142064104840407441060f0203800150400d41c40102e1600321450b40722101d04200c240740801c006050300c030304140c50a1003080350001e0a0100360800700c004103030359200c180c11410803000140d0b02c0c0300700612090040009066800041e2507a0f00b0301c0040150f20707d8403104803240d80300c0a00452040e260a1030307100c15010501d0506203819801815194401c450001040481c50b10020708800d000d2106408116407005201c0d01d508240440b0a013408100d060b5803c1c1f00ba2840042c445070001e401c0707428040400701c00c0104907501040035010201d203440045040c880d031030380e0042c01c0456025a503034406030042103a60030180581035400140d980500c00b55262102044024107801e914003040c5d03c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 70402493 1250 70401243 70401283
    0x80105071101060506160602070f0203010f0f050609090706110f06010314060702010b0112021b06041a0f06030a12030b12010c021b1005070201120501060815030105070806010305060f0d05 82
    0x55586810821905943c2e031040310004840301b1900d0b41f0700207410040e0b090b90203580e038035982c0b80140e03000c0c0b04011421101d801c000400341c60200d0300108036a402401603008286d041e09010040d1000100001190300500e040c00c03042c404400054100210100c481000f442040300100400000e5031046617a40945000c40310103503180a8200d09a501902c0c0480c04100d108400c0028400107070014002c0b10324400c0c49440d90200740f010240ba020303080741c098503050000d0503406100c000d140b4906411603401050176a60b030070507100290f00c8148020b4000c2980c0d06059043c9603460182d004004d500c0c0004105800c0c3e2095004400d01801141002c0700044c092203056050301c1c804e1b11108509c80c88050141c0400040132841907545ea4404001a8180032900500c844a460315004450290034103a0707503030200307040c40d08405401c0001804441e1082e4104003c002a09600c1058260700072424070b4081480d03200c0a01203040d1000d00309609030002c0301350b83c198061000000f88442110500c00c0620 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 70403743 1250 70402493 70402499
    0x606020c011205160e0102010e030d02030f010605030c0d020d0603050f0105070f02070812070302120f04060215040308040209060a08030403200102010c08010315061d0a11041d040c08010507110106 86
    0x401c44204685800311060f80c0340c2c444c91418410301c04d200c60316006000004900380d8400b40c480c990381240728016401e580000800041880718181c490040c80f1f10b0600e01e0071401c10b40f010031401d0080d5200c01100c01d03030104842c50b030408a0703000399004503004004e60359081e10900c0c5d0b2034040d010858144c008103025031340c10f0240e180b00144101c1101c800e42e002d44400891600c00c00342c294030a84054003140b04903040c04031301412040080450110500721582e68030300d0200f0280c100741e1304101c40054140010208030203c2d420114141e8020303411a8004441d076207402c00122054055088107041e84800300d404800c00004110984d03030300d0783c00d4a801d4078020303000e0012400c0e5800b030300c0d40a0005900000410000e0340740000002800c1e00c812002c285140c83d4012281c02d200d103c020541002d82d800180301c0080756903c1081c0711106001e10441c6400d013410340c445075601c4c009210312003080030580040c0c24029a11450805003d03035200900107030800c07180c001d048210f00c01d900100717940791503000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 70404993 1250 70403743 70403777
    0xf1005090406051005040905180f03120105060a0507080703021c020a0203011103012603040504150e10030203060c2107020105190603030f0e040e0a051f05011a030711010606020c01 79
    0x68268413681d6903403d1401c0c0c286a410006820040c00d480c5442c01e0368807030400c4040003844000d2728885210300441d160041c03001460300c07602040c1d0209001e024100905462564014200c8843d19003110301d207591070b2042d142c102e00c0c00c00c12540c209800b03c4030105121007280c0c049201e040d000d000310300030710613500f50300d60140c8648401c0c4100d180c12400107600035469041a01c102c121900c49030192801e15035603030003184c2560114071801010300c0f0211301c20700c4100b00480d1810b40216900b280c40900700e0565000c6079403584007510346040001e0114800103007408410b81c03000d172600700c1c4a0b2031106090081e070190103000261007502130300440030760410209000740300d032000f02c0760540e0340e1458440d0321603402c1e1038078220401025080781c1c843d4184484044100080400c00d482140100700701d20b081014105032040455803020f0090928004200e201c039050022140e03000d003104420b669407921481510805032142003500703a0350804c18002130941d00880c40300c4510400380c859960514040d012 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 70406243 1250 70404993 70405009
    0x10e0a0e0303190e120d150909020a0b0f040f0305010e0114071211090603190f0b0f0f040207050a0602070201030b010309020d0b091204080102031008030702100c020f100509040605 79
    0x2c5500c14280d080b042401e150004c0d080761403009884002d65030700144008080420343e2058140032401074950b03100985039104404408014a00d6030030030400250184c0c005400c01c0c4403845422510440800d409000103185402c1310002d00300b0045044185a89180c41d40c068030301c45a8404a6502e000321001036600d0310308115100c0c0c00380c4e03614090b52601544200c0020038640008183d04030b0248031041903034850100031030007001740c91001c1010206142010303041c0c03405040040001400c101002600e51108450315050101c01ca03280360500d46841e0102d0024000c2640c054010f114215090086c0620b643c02030084a000b030f40d0500072003640000540540d00c0099000350040d1b010054000401c515090070341e00700e0128020754080c40040c1583d6012600240c00c080d045075400028810181d0b402c100900c024030301c020207107091800b00d0b0002142d007102075500c24140300503800581704558803605080d150702002881c040804294050090080c0c000004040c0500c0c40d1180c085010700e4a042 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 70407493 1250 70406243 70406251
    0x70915050108010501051b010902100e0307060509031218030a031211040b030402060306150301060e0118080c0d0501061d01050f0307031509020604030506040b04020907050a0207061d09010e0a0e0303 87
    0x549620300030f441a2100d5042e4101c0c07e40c0d441c1035607142c20803001030340c41c030301c4149514115644000c15804080101410100c4640c0140300740304080000403850b890114038a0542101c4035402501e400040da10311064910242c41c0ca58140a01e0b03c5140415800121420b100d120040701040348580e0702d0b5400d612480790340a508514541800010014a4045e000f15440780007e0101803451500814010030345c0c2003070f00312101040d000b403650304040d40d01c060302180c0c107007039901c401003e286040c1c5416180c11b5800c2005000c0d02101ca0f812040c4582500840020904810b00c0741e42158180f5504c0c8607542d0078011075102e5001c100c00e5114a00c1c3c0002c518080d65040410300402200000c0503000401650004030b80002e821302001001c68402e021291055001e4942200c440ca040d104001c03010000409070802e2120511145000550000d581d03020384200742042d81c0751038801d050804001c0c048100701a400358a00c40040790701d01900503464003403a640034081c080b10356950030146e102d0000b01c07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 70408743 1250 70407493 70407497
    0x130b0406091a1309020d0f050c030a090201020304031415070c050c0906010c0204110a1b0c03170403060c03090501060504020a0507020906120307050a03021e0a14030c070915050108010501 82
    0xc003060165601c07880341d84003640124010b5030300d014070305418003501007019404400120341c04200c4500840c0075005daa420f48414050800061502002810b298040940640344488c0d940800400b16402002181c0103140c0009522202c4440039888940d44c86604004807041448240414003c0d8020880c2d458055400030117410100310404c1844000f40d0001c0001d410820741d00801c0d405a103452260300081482e140c0d000340d0f00c01036030902a0070500d241c4545035607045410340010105005c4001901500d900c517544040ca06c01401401c105400789400207001c02c2e240030494960700303401d540011003040c4680c009220499958040104038001c044005002c10000c01a240041c034203201c00b1540000d0091000d003003040a1241d01d4915000903c040f0351940c000c0a9030010325804000e0b41c0c000501c902c084d442030600f050700c2140c0f1038460182c010989192004240790103207086c02510680601c0400303c4039001e0351802148041e08000d400000d950a9010300816030754410f10030141601c0042e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 70409993 1250 70408743 70408757
    0x15060e060703181e090510050d0605090a080309060601080604020414270108100f1b05090406051002160902031612020706020d0914060103020f010c061503030302130b0406 75
    0x603403000c0e208403c440482000700701810301c001c81c1801c0000710103001c40d01c220101102132420480980200d48010b04030840b0380c07040017010401030782d942d550602e940b0341c072401c040703001c1e15442c01c0c441c0781142e5150010301c01840402000b0441c40c0000f54544512001d0b030b1040090b8903058207100480c070850150f4410003248a054682d982440e0010b003070101d10080c140c0000c0d16008801c0141d504007a00206a00d800c65440e03050542e0791030041c0c2030003115007a42006850740411507040f180c8205442c0f80c00748103000c10048070669495011400070701010788480100d03012044000e48a000b640c0d070500b41da854074a408601c0150900c2602e1082194213030410f206d2a030040c0035203204c2c40400951260036020042480082d0550002c1c04c8003118090020440110619100380751f40341884605d020307a80b00d41c0040001d81d5850400c00e402c51f40031300f4070700713103000d150305006025041142e0007440b40c0e44410700000405a0507402840c0d03c900002c4002000764031450603403214401c5100360300c000360700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 70411243 1250 70409993 70410007
    0xe071211181c030e10090e01140103090501050405061603020c0c0d050703060609020d0b03011a0402130914090d09060522050d150b060f18060f03040615060e06 70
    0x1403051515100760000784240b4000d072044924080000e9880c02c1100015031420b1081401c1c01c088040c1d142031011810704000c0c01e400c1400d001400b002c1445200b110300c0c410f00800e07110f42d01992140203c507410800a002034540350070070766625007050303640c42940d01c2d00000d240c80da1842403003950b060944900251205240004c1000300c00d4203504410b0f01e5030300034004000001a5207115075402030448036400350700c41080d03070f02460031203110a0005000ba4140b10014032211000c1c5502c5000207811071700140c903010030601d240407411068000e80d0035645400115900c0c1d0b88411404c52080381401c0c00c0b248900d90704031088903502075900c03410021442c14800d00d6080340e20819081c0d4103040500148090703035540c0d00080e450944150080d941d86101c500601400710140c065030354013800c00c0d1001458001e4015810145219008482d680041480350b80e181981d00c41d0100d031107103004010041cae101c0c06c181c10010300508103816800120817000c40002421402241c9072100044000c200604142c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 70412493 1250 70411243 70411267
    0x1a030601031113140a060e010f0210060b0904060504092004180807050105010f0803040603020c0f0106030308151e0103090620070308011a041a04030803010e071211 72
    0xa8981414076490702401c2000d0b00c42440505081c00740705051012840c0340840b04680455004040c1d809901044c10520a0341d402102c007408541c028a0100300f81d4010344c2c0300300d080031038a643e0039040500f00b04000074820354220190440680490b000c0000550700c508000c1212520b0000a0041c0d10107100f080d485003d100481e20305450281011448004055418900803900310003107411201c04525942403090905c100c41c05032601c0211a020340303040003401980c0340181d2044404142d00001c210071041d005008035055004800000c0c403044d5140e15010303125074000c6403403c074004640c01e0245445d240c5404140640c00d8940c8864004220303200044000c1c0000c100251482e030346425628000400c271070f00b402d40d600c14200c0a6604c8410a150081c80c0b8174040c0d1021404c0c0341c40b485110401c0700d481c421142161528840910460496080c1712024040e9600140c5580004000020b449012801140c424403c541e0f40c80b102e42c004002c1201154490782511401080c240203040d4580 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 70413743 1250 70412493 70412497
    0x17120909040f06060f0b0d0b030a0209060f061e0c0d05040e0402041a0315070f2f10020708040303090504021201090507030e060406060e010608090607080a0603081207020709061a 78
    0x40c0203050120711130b80c0b07420007110382c00e61a5100c400280c40004191440c0c1c80548100c0300011000c81c0070303001d864550780001c2d1011070081e0600c1c0c03080000c0a44002d0302e036115800c80c1d0740c0b4505101c05404110b140d1801c540702d6007042003040c1042c010300d006086082c2c81501103c0a98480304d160a2503601e542c2c0a200040141184c0205030480d101c2140d0007039941044a1011070420140d0704110f46050040100281038519102092040c440d14081d25005d40d042c0e00703a0504d5458030070b0613094034003a20003407800c0684003801050314400a260170034000604010020703a80030f503e0304c200169440342888120f00c02c81c560700390142500d40051001e41803c4d0081c5401851902e0701180c2480b6090b419400c1420650b012680c0b03a6039003600304818002c04421900500003810300e1941c074a403046c00d243d1981c000234440c004100b11180040c8100b00c059015401035a044800152100944084280c0801082c0c4000d40940724042d800641e8a40d640200002c1d6110fa417a1108040d070b100080140359 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 70414993 1250 70413743 70413773
    0x40305030a031e02070b0411100504051201021b060a050f070813020111010212100902070b13051c020f0f0106080c040b04022503030e06040b06010c0c08071712090904 73
    0x90f50a001007a2006803030020304040c80c0a1480002c2909051030141044802c82403800e00440c108058600c000c0c2d0004250f40032038009449254402c00382c5040940244540858101d03811041042092040300002d901880303801d41d10410045900c1d818420020200d04441c081300048100001544804811440d610510b106040100d404140c00c0700b280e007640c210600003007c03010080100071240880303000450007409200b200314a40785440e198000c50a400620105181c0141e84120701005410000103505009803000000c11070855000203488070403409161669101d00c1601000182062003079804031034440006003c07100886052001078890043d409902644c240305004512000d5001d058002084506c80b810702e0f40507103030250455035030084d0310b1001d601000030040003e4003480c805420030000d082083d00104249081c08004910750043c85c402d02900c18001903600c0e2444421681c008940d00b03403841f441d80ca0a00502074007074400f265510480c15000703e00803600d110008030352 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 70416243 1250 70414993 70415021
    0x30b0919090b01090915060317031b070317061e120f100b0909010203040206090418060e01060f060215040602030606040f030803240307030303020309010b040f060608010b040305030a03 81
    0x18aa40d02e4481d052100e8099110780003d58544040d5000c025400c866150840344040e8100145400c5403690031400700c00d146001d80b8003200102040d1922000380c644040100d00d031031515601c1c142072030000c0c02010b0001000340301401d0000461046e103420404403050f0b01c0a0281400c41407010b408101840c000302021040758051903206690110081c0004041400305440100f5006c00c44401d22104c2c50009101d0390321a44140203002c01680c0b42c804440c11503d0403540450300c0714440705241c401552007a0028075480c0f070840c11410411043d0030601c100c40030b004088075803075641e07a410383e2200c980180340c07640040802c002800180955004c3d6400500150501d42002d481d80b029480300700581d04207960151010040046005030810501000391160510240360070003030001c41da483c683c0f400001d080c541c0120010b03c0368042540461502c42000700240558140d03104900020440750150302c001810307440001c541c0520f0401202c003101c0e41308000310304c1e002c0140c0080340100083c0c804084 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 70417493 1250 70416243 70416251
    0x12030f0518090c120106021203040204092f0a0801090302031606090210020a050c011b02220212150409050a0308090304030212030c10060503030d090606030507080d02010507030b0919 80
    0x10a42e119945618400c0f022426010756850320a10a00801401640400700f10b610a10391446c04151007400d0382e070043d9040da004a6018114506031168810b41c01804034407440c080c0c454110a100211072140c0707010240d03210500a5100d0800501380c940c44103000d00540d00400c141020b400d82208482081c6002e004005541045c81c0d001034015201c1c0e00c941c400581c4415040400e0040c24840103059a0003400c100c0f901c4602401c110001c00031428010340306003400030750702440c640382006440f41540004000c544d51800e8404811b000807040e124248407003120081074205003060700c83e21401542203401000082c505640440c1c4946d00103000a1039400705000000041e1200880d101c03401103101302940d21020344440e0746180450402c00b103c0414108038040115031000300454402ca004c207000803c8075805401c013640508030940c40100144039040c000100c020b8007080b40040036205900900c0680c55010046003610f2000e40800e41c40480000807580d0380400c070f4600882000c0400000c0307 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 70418743 1250 70417493 70417537
    0x2010e0603010f030b0c040314030d05150d02010f030f020310030507050405040308040803090307080714010b0907090b0901090b0a020706090e10050d03030902040603050c030f01020c070e07140304060603030912030f05 95
    0xa80d4189c4510901e6150340c808511822040003601920383d120103006890340b8480358100019801c1241c07100c0290611807071864104107036100703805c0944019817401d415592420000c0900352000120302c42034849004414012440b460140640c60003150180c0c1c0c0d00045d0303140e90700c41511a90000c1c0c65002075110411061000a001d500680302060142e500d44803006d5140b101d81c0d081d03940c8003981a2007907600d44104581160000c4240c4141d4030143c0340360740c50b150013000699024590360091000c04c0e00102c4c0d090145580020740b01e0586240e13680e00c1401d81d40e00c1d407410400ca08280e80f1620040044003051100e800d01c0846061510702a14000c41c0701c0d0300980105003229400c0c1c0040c1e0302e07030b00078030007200c42424100030303500890040d80001c5240101d04201151500d516000703e4004111450204421502c0f42444134108071014a142e40c2c3c03410300746420f000414840c4400c8011415902c00060b101c00880389035240d407074054888200050414000301c1d1a940b20580e204c0c5209045000700c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 70419993 1250 70418743 70418753
    0x50a0513030303150e0403021002090111070e090c010203040b04030f1505091b0315010512150711070504060b0319061a0d050f131403071e02010e0603010f030b0c0403 73
    0x18a0046000f0340b8002130108004604c031040d5010743e080940d045801c00140800680c0c00111041600340c00000103844401007001251100d9012030700100382d1080750f80100341840311204032800307401c0c00401c990248540c4001a84c030f0340110310501900400c00e01040020651824000101e00d01c18400e091002580e10401000c0341d00070781e182d00d205d92088906c1c01c40b108864042e58402901240201180800600306203032100f014002c590241d130340d006145a042da000c100c141006685542030142c1c6151400f4020100c013000406148148181d600010b00d034201441400d00352405443c0e441e10b1540c80c01070043c0ca41078002c103481c064568841c800600d41c207400c0d100c0d029107111040b403da502c4040074006429503101034000292584907000340030401714003200095181e640300020a00548241071414214014250080c0c20365407010115020840b00d00900e42e4014402d88844403154100030601c02c03540800d002e41c0200f058110014004100c2c00080194003459036440e151801e41c40b82e50b4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 70421243 1250 70419993 70420027
    0x50f0d020f0a0507020f010302041a0705070e040f0605010509010509072106180506040510060c0615090507020f0f0d0c020409060c0c0311060c0a0503090a020904030e1201110406050a05 81
    0xc200141011030101c0031446e102d0340030314441c182444c080d800d190038204441805030a0f02a80d09824500180004c1081000d00040c00242054005039403d4039042c2001c812400c0b40e01800c8440380d103450004203003031070411031850581e0f802500c01440b95851181c00c0e9280e1240d502c0071188494101070140403950140680405418490074618560740700c03a01c49800c0d2907018010a204608040c01c202145403051000c0c4102e403d035103880560000c050400c1e600078034481c64070700340540c0002c502090114881c3c003c103008076200e50865140754810b03504070740c6502c2c10300c00381500b50b04101d00c04800a03100d0041400c1c22400240006800c0c0c907030f941c0311400c44022000d2040803400540c00c5e0b509058000032001800d00030341010304400c0ca0807507456002845215140e170148078000c00030038002542007181d0807100d6806041d02c0f0084c1498180034001e80c161100440c42005060072016210206005012098180702c0c4100d0405040803020342e070a401c500041c50402c20284400040b03d0420f642d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 70422493 1250 70421243 70421257
    0x60f060d0507030606081902100806130501090203010e0112030e01030b061b0601080f1504060507090819050d0507031403072c190e070c05010e0703030e03010f0507050f0d020f 77
    0x800098032444c0842160a0220140c040314851f80170542c200c026850b098142c0c410007150346409020b50b5a044006019070080100c040b42251038a40080358801407079004505803880c1c800080c04582e42c1d00b15120000075aa0b4000300000c280b1b02c044651035000342c002842c90f0000400907810320002c041c0c070846206107014041081d91044004005045003401090580c0c0200806052110080100ca40180c2005400145580d81d6000001c070501d200c0c3d005203018013410b4044e503c12110b40c000030b0012201049007a0b6160103103c0858039414000e8003214140ca0307040d02e5104a2000c409206192600001d0405060000704c100b100d1440e0000015108082c40c089403020081c00a8001d000e1200c0c00c80c034503900b41c0c5c00c020f40103020030103460301801c0d80710080d8074000d0781410541c5062400360028000b48481c605c6012000b1041680088104e0074861044d402048110803829000060390b00a46130782000c80c0080014100e048611001040c15440a80002d49400602400c0b842e150b40215 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 70423743 1250 70422493 70422503
    0x16210623061801030b03010f0b09060a050607080a0905060406030c030b010e03070902030a02090a060f0f032304020a080f10140402090711010e0a08070201180e0a0213051504080607090305060f060d050703 89
    0x4844400344c0c6400012603410bd101910880f400e103080c0004184240301d000c4020b00500b6000c60564500c03172254914002030300014201d00c0c2c443c4d0b03a800c00130740903250071041140030a00b4a1001c1e461940b00f945c00b040a804028020003040e880e100320340c4003d500203403220807250b40030080c200d07064545940301402844130b40c0d124110700180b500f004120310800380d240020141840f002d500c600425000b490f00403004164900348545461001640540c080c0c0c2c068001c42c090010102210309002c6000390172004280c2e414441000745081c44030b0340c224204c600a504ca142c2001107105144214182c01000781c26000001e00c0c0c1c205641e07564030f8100e031114100d4032400300182100465a1080d80d10508101801549040d14109000320044140c02071460001c542d022502c03620302844030307005200030301000d812030112603600000007146501034050451284030781c00110785443d102d040301208a0342c103d000303801c0548919018000014014000e194010490070017403003c1441070112000540c4a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 70424993 1250 70423743 70423751
    0x6040804170a0b18210711060706110d0608010603020a090207031103030411010e010305060906010807020a080409091101020613022205090616021516210623061801030b03010f 77
    0x1d142140c50050090058186140005d407000c4002c0e00303110035141076a6020b16642003030142d440200d40103005618000e010142440090502100000300401e40c8a2240384c0c14491251190b10141c04d0f254144402900002c80d00010092946154050101c0700d100780740401034119259546403454000759000d40324a00c1c0c102e030800c040c1d81c0007840c50403901402e0905205034a080000100c2401000f44035a05105245000481e014400d003c0e1060081c0d0083c01d007600d071501c810344d280041c8030503103044035040381d2000d04082540c00010464400c1d21529440c0d80d02480c0c603828042007208480c081c88828450340120201c0085900806204034161402000e01e490590200c551811403e86d2141c255049118090112080400d015070f12050a28118030444849407044030754080341c644481c46207540ca40c502900b0717001078004a045800520700c0d00d0b004000222014114040481c0203584020200184d61403482d2100c40e000003178205040000380c2c41e62a502003801c0d100a2941400e0550751 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 70426243 1250 70424993 70425031
    0x60c090f030503130504090503180112090501060302030609061b090a05090a050703050a06060e09060d050a0b01030516051f0306030b1e0a050601140c01091506061106040804170a0b 79
    0x13034421200e0003000101c8062001d00c0164586548074495080c1d10b80d0160003e01d00c443c01039000f14a089136001c41300c2410882c201c01818424000c1405000072442070060b9808100070340b000203519400380d80100a50112014204450750050340300d160b080303800084450f40091143d40e4074203080e00c1810900d10204081c90103a1000f4200c0d034004110106a5144c10000d0003856030103c010380b0001c205949149050f00e40d003002a48880107094020a6886603c80300c408201650304240c0c126031003601190340201c5c61a500300828105401103a410046500b401d80b85034000804815200406040000300710761245c030740c4071501c40d0884100000c650324070003118008641011055021148040400150605200090404009110385851030301c0105403150305850a5011207002036100c1d00c28140001503062610280c0b84034030810001c151707090a0156450404201680b160ba44009694680740c01c0400d283c1c280fa00c10004e0034220b1040e101c0703110000f10720800c41c03406944001195072200d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 70427493 1250 70426243 70426267
    0x15090902030711013e0c01060906150f0206070c060e06090106060906050c0604080c10020a120501081f0f020903070b0904060b04030b0406020702130213030b0114090103060c090f030503 81
    0x1117a900e600001c40717004150940c0240d403e440d004045c9004140f1260702c40c3c0c40c41445850141440303c0741d16529000b40003414140c194050710490312180d610941e07070203201d40156a0040e686031b6682c0541c0002001900491003490340108151043c03000140040007100d205250100c02c48140f051303690b54000074401581c0000260b0000d044e0307480c00c3c0b843c2a20086082da210200500020324081c40820001c0110300180900c1402108600c000c540b14240b420000b0841e9120860500c42c0516010010440d0840490002810055800c140f01c804040303910792002804401d40c3c00f28155420300c21844503030f4083c8141001019100c1103140c40d4445401001304403505980089000a020441003001030351000c20143c0c02074000c80c005031134170b03600d002103107582c0300c04050f120701a8070000d107000f03911050148040989010b603010001c0f980e00c40c9245000c0e040340781311031544820142c00401c00220175412035003440446141c42441c0517a0380c2d4840200143d40d40044405402c04a450380d03907030b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 70428743 1250 70427493 70427501
    0x3061e0213180c05040b07052b14030103110f01031b180e010620030d0501060503040b0703020a050715060f120b0702060105010f0f030902120d020f0309010503011509090203071101 79
    0x2040d44200f041030340840103015009100b9440348103004900824140d0520206001c07001c0c00c0d00710030a050610000700c4108022201114960202080b1913801e0420302a0350b41098a069940c42418408085d2444c810000c2c00c05c0890f01060415071154420310207130406400c40090840d4076292030030b480d806d03840c880e60881c01d079400c209104800071004101082c0d2190f684130108040001444600d03080d0b40f801810340c4202c8003c041e015050000000c0d4242d800401544540c1c022010f0241c1902e41c0d000072003d82c070600312010006401030100b4004216100811900020030071400900d0310b03a03603c6130b41910403090380700d840100443d45000c4244510b040207113038490071a05c0034006541c1010700103800781404162100411540700d502e52181e500a6021104080d0010316699a01e201d000d5510358030000c0300380b54401801115041c105908001058034039104050311402c1c1140e0820316030349451200c0c2002581041106900024451748920081d4000c064558515542c05c034a14038003429a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 70429993 1250 70428743 70428779
    0x13031707020f01080c250302010c090303050307030209030316060203070f020a2402090a171902060910091502070f060c0203060c0c01060302190806010f03050703061e0213 75
    0x549010000c140041c0d41d086012544003909080c940760540b24440c550a0350f00071150509400e40c0106111030181500c62103690312184240e00901062445010840741d1496500c4000d003c06e0050000c40c00a0b0300035005000b0b40305000d01100d0034048410100700f1114002e001c261511a4000203010744503030b12940c10b040c000000e00060452200350350710a0512000380c100d8214000c00c0d810318003400080741d0129500403100a014502c01920703270341840865050f00c60007401912845130002030352080b54000d0021140c0081016081c240840d090001c0c620281b5901c10402100c070901003085820b1030b0980f0400011030707005016580c10915243d10001640e044030b41441440391300304006960006126501160465031640c4520490728043d000d4200354000a50044005210455013038230b034071010301256101411070b0582d903130781e09160500d1740c0140406016034100c0c0c5c41c00e02c081075864001c0c00182c0036894030030703211000d0000600107d0b00803401465192510500410800503207401d12405 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 70431243 1250 70429993 70430033
    0x60b060f0307081509090c1314130f0807030c1b05030318120706030e07050f010f08070207090501090b03010609050c041413091208010f05090403231303 67
    0x508800441580303040d0200030107040c100b248540002d00c401c80c80e0845000003440140000b4107078104148416107074106600340c280a108022883c0815000e01c4c0101c490a41141c041d612850701d90070040e060b80d003e000002d84102c141480c041002412420040ca80c142c020765070386011080c3c6150046190100f0000c052986050283c1405542d401008803035155400414101d1042801c001085081003031092020107800b490748000b0300940c151704101d91020a480035214100d4a40040100409540f02c2c1107001860030322200001d24044d0503d030b5004409070040b1803401c2e81d1100c00800383d40c401d802c8070110640710712554095003024012a0054005200c041c4146c0c64a004803e500b40220301c500c01007803a100c0240885511100d0748064201d4400c00140502c04450a003000e600700e1002c0d5401c0002c0c543e400002d075400701e8106050546200501402007038456890445460342c401001c104461601000c441c83c070140d51004203030340032240f0b105d020441d02d541131080c0e900000c1400000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 70432493 1250 70431243 70431247
    0x90b040203100501050315041a01020106080d170a0f0513050c0904031407030507080304030503060312040b04090e0c030109050708010b040506100309050f010e06011505070308070e062104060b06 85
    0x1140b07600301030b80c2a02d00a00c2d00d0342c0c40b90b4406c11341012840d400704965030403515140315101761301c60b42100e50400300701c21b070001d00481e60b40b19001070b9035102e07138001800054420a0300d10a01c866405078030785c00c498400008074200c049414801304030354040e50600c142c0104081d610040080501c2000d048000441c0e20b00300502d0300fa28050014103202c0082140401c0000d0072404041c0100d003900c52075034201c5c00443d100d140a00e0058120b9005503102442403092444403c9100c040b0b0341110b06403402e1b07040890130b0514000c04040600342254202c8014040d9104420054509103e00d10780b15005800401c10940750018650031900c1400300c031070085081808218581d1600781d032810741ca14981c54006000710b401e0a00509060b15165501419403c1118014107000d0001b1241d05880c000c18900c00710010030b4000703540314410325000501080010340050b8203280900e002d150030000c09040a0728000948107404000d070782c0e04c010b40301d001584000303010900240f07106821844801307540c02c2e4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 70433743 1250 70432493 70432501
    0x5010e0601020a020f120102040b0304111012090f1202010c0306050604060903020d0507031505091905101109040c1e050705060114010c0605010b07021207050a03080c01020c030a0504090b040203 85
    0x303445003803228001e4054081d1445d03a1440c0d440319035010460003002c000071500c0781d842d441403206941c0113603019a120a884090219940b400300101c4a0260050701d4000d40c0718001c000140250282c03000507a030f0041ca600000000c07501003120704142d40d003130f640005010311254401500300c407459001240035480c1440148509500b295521043d02d804880c4108010030380d103403851070062603410092120f0005c0096000155460f0003103030141e498401500c50512040d07035100040800d00d0000340150740602d44031110101ca651011210380110000140342c80d400401003000e6544c07180c000f60001e400c400380010641c4000b0000ca4040a0b28030b080c52516500c1d40300c4a5030b540040c0200040f000320050b84100681c00743c4000c40c0301d00d61245080c00a5a95020b001b0385d5500084c2082e030203984040c01040d00700e0808190182510801400c0106950564a90501c82e411401c4070031003942d4200903140b03408108001a001c7d918017aa1811340c0c0385d00740013540080da040788001501030390044c0140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 70434993 1250 70433743 70433747
    0x40b150d02010309080408030f121b03010e061f0504060305010506040e070807020c030d0f030f0b03030f0a0e03030c07030201020f12030106030c02031603030b0f031b04050705120c0a0305010e0601 86
    0xc40c51903502480c2c081103500c042e00b405d070481e04c2250700042e1140300c00103581551030048809450b80305400341c4e01d5052640c7e10301601000c2031a0480000214500300010301c520382e02c81005035080342000e00444464400c02d0202842c078158100480d01140006ca0304001c66035050048034050081540d00c20b0920b4a0070f0f0005040ca14042e1050052151410009240d00e2003000741c031061140040866480010401d005007101c41e1071092400080d081540072588100c46004012404034080c00951400f10100f0310f24410b81c0100f866541040b60203e000c000d5680c04101030322800590002400d0714a10710720002e481c161880c508114140c00640c10084519005030030b1360304442103820b011400381e400d070a040707003580316261540d9105851f0310904410b00d68141d00400c5004800c1d00c0340030204011b1400c169580b074a00850318845907024035103021030308241d003100b0342183c0b00c0e05142e0308041a81d804440d114504580c0018104000329085c00c84a138580509401400100140c8110342400e43c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 70436243 1250 70434993 70435009
    0x50115020f0a140a1a0f0a02071a0705040b1209070806090c09060a05060d0b01081012060f0219030504030e060703081f0b040816080303070518030106050405040605040b15 75
    0x7002d080300f0316120300e0090059041c8190003400e9402a210206044007441692000d102500d0340b42c105008940010045a030b184200d40708290410401e0840c1c400081c0d1030311584000030b10240400000303100c0040c071900101d000e01740c0c46103407a6006801e031829100040c58440e01c0d600002940d844003042c8000a01d000c104410111010345070a1282c0da2800045a442c070740c1548059000500051540a040c00310340c4102c01059003640c61200c0e070748031a075007454006160f000d61548210002c0c0c8030800145581d003d8141449001c0740035003000c41d840450001e0130708102a40020a842d04108000c0551004c3c41006c0b000c0304031a03407070904c002c50310010f045010041440483d641c458908814040740f50090900030000c900055548035141e03824141c0742c0850040c0340040001c4c1c0740002c10100c10220590303114600603550103091020080c2000300511040d00c20325010356848074003098030745403400342078801e5005020204107814941743c1b08003412001007140141410b4080001e52503550010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 70437493 1250 70436243 70436263
    0xb040606050417010b100206040b070801260f12130f03200f03030a0201090201090902041410050702030105041a0a06050102030405010c0c2c1e0a0e01090c09050115020f 74
    0x1003088118024400d4850041466680e200c0d400741080106c1d501e0700340d0008645124500c512070300703c203a45800c50141e40c03e1800b030054030440b00c40c4a0b4152404414000540140d0800c0400c4620703081006c016a03040a0400c00364014100000549040180450603010000c003807091a1844191a58545688009a40302d01c07a80084c50f800e010090740e42e80c1c0130220387d98080203040d80c1d0b480d182544080d000309403c00c0200e01050b00b0610005102403180300b035074200e82d007113408101020501801c0219458032980010280401030080030056102449110f100343c0c4100f070580107104240030341c00e00d00ea10044c420305901d41410824022039038044191021100203003008600c002c054901160000700c03e40003401180a10201941c0410104081840360425451185c0c4039807078880701d114490560071440c030040702814020480481e0300340e21120700500c80500000f0020381594460080003000c0c0d201828480d2540010320011034640c60700c85c3d0728007041c0010284c0560300c0c40d845860f100c1240b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 70438743 1250 70437493 70437509
    0x6041707050307151a0609090103020d03090305060c1206122a09040606030b06031903050904020d020a030608010b0609012708030c0109200303120c09190302040b0406060504 76
    0x108208003040300410640f0481c81c1c1c06030090035103c07040e8070000c000300414003080e09a0b035070458070000c4a041c0441102e000100113840001c1130fa082da002c0c08000c0080c80300450400480e90700000101d24180315142c00782080d4002107658498032070310320040b51b40c06481988109101c101c07490300503078005098845000034072282c200d04590340c24080e041d180c41c10800c5400040a404010070442c00798004415a8802d4041c0300058451105041d500c059240140c1a1410b92552200110740544050300b1440001130000d031400f0354803c4070310180c4c0c100c034101d40086078540a081c02a004203014100b02a070040c1c0e5030030b0601c064000020484c003858100d40302c681c04030034041040d442c1c1c01c3c94140090302e045812a542c0e03d500c0503540d8020015800305035111000003a40d80310000710b04050b01034640c402002542012084c14043c131a00c040500704003d407500c104120280c0d40c0714445503225507400982400350b020b107140144130a81d04041c40a610940ca031003014408190004d06580030340f0414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 70439993 1250 70438743 70438747
    0x40608070e0a0803040b04080d140703030e01020d02042304021e0304050c0d05031308030403020d02060306010e12030901170f041209091104260606010f0314090f0708060417 76
    0x2100801c42c1074100f9000341e030080c000003030301150300d00182000f0800c4680703050485184c140c80100c11039414130b81600032180e1403020401440881d02c65080804071216110005107070030005114078080381e01a91020b010403041d114180c5071707130541881000364544169815803810b044401100007615000d60703100b017214004004101800000c0000403140700000d0600b4101268a04042d0358036044a003c4101d8541440e1001c070340000f000c0309035011030340d02401d8501d26580560820410740c100412a40c10031117001c0f0989201d81d1000d00c0c014404940e14040d60f0b55440a03c0010080341ca100708100d840d80079682400318442c079000d90541d10581244011001040e0008121782911041d41301c2c1d0356880c10310704500304003441440140111012180c00d02c02031002c9c4440640f405075401e2282e0141d80261001400a5000341034041c1407003418a000900b500b10382c1e8500c81382090648400ea090390001849180362541008188050078440c1e0080805141650f15007c444400c400808012580 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 70441243 1250 70439993 70440017
    0x15030d0c0b011a070c1e060203090a0303050714120c0d0915081e0109020d0e150106030f0204030c08060a0c0903170f09030118020103050a0c05030a0b06040b030f100b04060807 77
    0xc81c0003680e400381d40c0f014017800300d00d6443c070744000148a11542d1020000c03d1080c0007610b540000100d41500501614800c0881d1a544099410340c000f8902a0b9003034144662000c000003051103922031405058806580b1021501001860940400d44c1f100601c00505000e100680c45225014142046843c10055a41d504081041e0301c64030003544010787c0082d54000314248211f5006031070383c150580c01c10890920f04800b00f0382e5415000b99030081e00c0390020014401039101c4e4221101415084001501c1e2968a94404001c10180d9000c4d00c1d00741c2100b004d04c5009241c038040c01d5040c200c5d5150554807a411520344001c9010170300d0450540100c0010607800c08880103041c2c070a0901c004000300301d4024079800d040008220100201d0001c1d02d0040041c2107410345e4410100030311101d98500e801c40d5104549440100240d0182da41d000c18140400108544805c00035031148480107a00303409810081c8102510120781e41203000c06407014041030003000d500c045000e5029000340350440c18502 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 70442493 1250 70441243 70441289
    0x80c0d050c040e2401031104020307080f0405030f0c0303150301050105130207020102010f0606021e0d0507030c0204021909030b0708060f091302030304120506010b040b040b031e15030d0c0b01 84
    0x258952000a40c0441000c6640c40d4000c100501d04980c042d40c00c0e00040305141c2c7c1040101d01c030850f04500410509000702c0e04072906400c0b1180d00900c5401164600104402005c02c6c03500074560620b09036100000b001138001e2010b0200400c0542a0024407240d41404006241118501210020680e000c00c4072015603100b500811001050140e0400404d5140c03c8000d45621b0ba8401c17160019082c200d02c018003010000b0600d80c01130030351380d640342402e030265001c80e143c0018420aa034400d80a0041030b00b00e42200404000b00348031521043e681038910b02d42240c540301d004001b6020f102030300d81040200c1c2c41c0c200c2d0f80303200c0d0902154121042e0352504440d07100b45c0990600070b50144004140803408080c1c058a00b4180c40c0500229846a03a9803003450600d8032950041403036002090004008801c1180080d41c0c00c6a6400042849541d54503501d80d00c0d60300444c0d010101742e45900781d60880741000e116040100e42c09107806c0340038000c02d49a003d1185030601c03525554110920410507044 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 70443743 1250 70442493 70442503
    0x150e0f0c0d021c02060304030801030203190b070e04090602040801060314060c0301030b0a09050109060213050909030a0c05070b2b090b060909010f140a0506010206240f030a0606080c0d050c040e 85
    0x144d00030072045c0c40b818607050003440000c09000881c000d2041805079500003445440100225501c51900d003c1545d9141c0101e1b00341c3c0300020741c03540007500c07070038041c000600398000b42020f44000400000c1c100d1650422aa14220310f0309104003e4201c882400351507100d2404403030641c4c3d00a82c05e2440d940316400c03060001d151600b030140080d46051030100800c0700c1c5800920355030301d120401055281d2141c2c10804034005c01d8a1030103683c0d10410aa0240724040d880e100080d900075010380305104c2d03a88a00c1090341d07100c01c400700300c903c002003120031100c2504407066240c200102801c210a2003079903100d000f52203000e000c103441626000f0019031200002d420082c100103005405100d4000342d4404403a1041003982c00c080380e2401c000025401c1d503c00900c45114180c14600441c015903141d400d83c1100ca0740581503504500c60302e01c040c82c01e0301c041242c031501910032980000c1440c0b8058041d81814500340045204161005800c000b15400050401d520707030085400282d04d07940c03020741d18a04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 70444993 1250 70443743 70443799
    0xb0307080c0f120a0c090503010c0503010e041b030c060305070e030d0c2a03050708030702030d050a030908040e0f16050703050d0204030f0b07091d180a150e0f0c0d02 73
    0x41d5000c0f4100600300402da0816288401070340c50301e012513911030003014262200c10750010700240003030004220001c0c01900f6203401a0040455160340da02000030064560020f41090301c6550684030200f2205515102d81580041c003850450f500c014000c00003501c43c801940244104229040c0d104140207281c9442050b00c2d0740c2040725442104c484048403600c6100344403d82e40750058090005e90b04801000301c130318a50f4000c0141030004080707c1c1c10345440d0008031846e000c041d47c41600400003038459000300044c1c0b91511b8a1041c92030b01100b14480340d00700618420070114550510b82155421400759500c5c3c60341401c0494507a0b10944c18880280510f83c8082c041d43c096080b0313202400030452036240524800d40c2c039002140d80f1502a010044c800b459110500b040f848001009501c2c01410070b00d40c000f8403401c6d40d130b000c02e4a0f194180c0d002c0b05083c80801055031004d1940e0542800c1009624210b0481c4c0504500c0381c0c05000140710401d5084040d0240881c040c10000340440100001ca103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 70446243 1250 70444993 70445017
    0x1090807060201060303020f01050106050a050d020f0426010b01050a0507060e120909010f030803010b0d020c1e0c0a0b03151c0302061506130315020d0204080c0306010b0307080c0f 79
    0x200a81e03401c0d00a0183c001c500c800c1d405405980d0184081c0c007410b00a26040c1c0d28213031a0a0320303003141003804071090343c00310b00a100c000382d0912000c00300713a018200074002404a440200d02d2030444000c8003180b9114001e11070851b038500a944a8980d0700b0400380c0341c01483d00c1c02c020b074407900ca43c2422000b4008000d4614075900030501e111018003c18400f40105101c06e99640d589031380c840456001c20100c03070001034204203092004000c2101000000c055034407440401608080c0401842494210850601819019488212200c0b2442003200d0a5038040440c1d104090302c2c80c00f00d800503180700c0901180100d8407583c40c0b207452a00c901c2500c200403200c038000390000b104103041c001e48070b02c002e40b887c503c0581d800b200c0d15494503001007a2211010090361840c0050b14540d101505159803000c0d50f155960240940b00400700c072807000d0030007040d8020181c00341782250b408240c104001600150707460001881401022540b02d0541c40e0720240a80e2420758034010f43d040c595081c0142318815007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 70447493 1250 70446243 70446253
    0xf04030f050d020d08150409060b100306090e010c080f1e040507030302070e070f0305061302070b0412030e030735090102010c03020918040c030f120f0503100e06010908 74
    0x400c0040c0001d0036200e0711890f82c203541c40c040c020501103804c000190340f80016012803507640100e500d89a030154030340900c100400075044505001040103a2601e100301400710382c0d22038041080d0240d5000b108140d25060f0020048044000000f41446501400440b840e0582c4400500e6022084001481100780d251160102c1c2c0361038940703140c0d500414082100107002d03511000442c2d529043d00c1364000c04040e00c5d0500d8004108004030020f200c02007a00d54003c101c0c0d0b60070910448913100a240d4203000d07000d000300c285014200b4042164003040f86104151401d803000b902013802105607201164480d14421400c43c00c1c141c19041c802c40030b08600d80c18004d03030080034000c085000c0204503600081c1c00a2000c41841c1009604902881c540290080301c2d403521150410a2407041d50b45c401c0c458809504180d45079240c03c2c40d225031958040303031110f003505005041035030400001064500c103031400d039103507280240300300030040c196102d40d45000101c0004103116078041d150034000740c4000401c6030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 70448743 1250 70447493 70447523
    0x603051506031906050301060e0406092a030201093005030405100804110907050f09010513030b09061305070501050304060b03101545060f03020f030d0905060f0403 72
    0x3c00050720300d0140c501c0c4620700800001d4134203040c011501121489880c910080e41d403a02ca03900501000e1a041301c82030180c031508154610108540c8030802e809190342c4061504500c00582030302e9241d00b103038608030407224100d4142400d001c0000202d4000d02a00a803048051400310314502507500318590110a0506102c25942d000d43c1040c441e600414000c940b00701c80e20309010319000182c070341100090341000b02c215030011103801054407840601d499880c0c03e188d001c1101c40c3c030030244c0080314000c08003400e01c4825002001150b80004d0300030444032503201310b551810b135500715511405050000100c0041e0034031803950302800f005403002d8150390325070121b03080380c41c0146403605042c5414480c3d100f022a802088400300c0402e005d2685480d85405461042003244003590282d001020030b04452064180103280208001010140c02d419000c038110b10404c51042c0701110800d01903400300300d421200c1f95004204c80c040f10030544105564100012090103e42b1a80e0000707030854144004079 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 70449993 1250 70448743 70448761
    0x70b0a030f06060c050604060203070c02060301080724051215120f0105180c040e0a240c0c0b06041e020f0324091914160f02060907060305150603 64
    0x505100c041c1e02100704106521000191100030f00510003800940c403910029000171131a500458122005041a400703040042c1c0c00179000d42e009030403041480d00000010084141c0020190080708000c03403c507204070034600350040450190801e00c0b03c403002c81c0d00100b00406403403501940842805010200003040b0f1402403075907108200c9909100350303c0c2c40001400d45024403000190300300e0f40406008245000d00030800036102403038003032500d4026121040e0000c0c011007a8004580030400080109100741e006080850700b41120307000c240081000300030000342524a10079072005086070005036010502100c030f40744200b06440c0503060303407000885140e442c1d0010042c1d0b01c202c5030034801d0380404c01070a2010b00300541c512105d5800035901404a44821701210841c21802940d5200085030140c80e000011405019540b4010307545800800c0d8128582c40326540d0440c00c200d00041145080280c603a45e600c0c1258400c8a04059a0320301107000c01d0882c40110380c42c10001170280e51603081c03051302 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 70451243 1250 70449993 70450001
    0x304030e0d03020c1815060306030c0315070311070c060809010f0e0c0901050402120c0d02190f11011e0b06070210050310090501050105040e070203070b04030206240d0212070b0a03 79
    0x2401d1051061207000205e000c02042540c0c45072100035102005c00b000d58040c0320b003581001e0f000c150303d8000c11601458544041200403031786030040d00300e40d2850800f51009821030300b501a80c02484030007007203103402207512480b120003240c08628002c0b0242d0b40b500d022a0041c8000886e1540b054200080080441d10008443d168107a04441e801740a90b030b85d204210403441281d88074035481803420005140190200302500b0301008407030300545480c00649100400f002013801c0000403a010b51060f520b6158850080011102644020007103003090201901e615868651440f46040c2c03110714024103900c9403815203000d5540a40080201c4d071181c0c0d409130141e002212090310002016800140b001603038000c0c0e904841c010307100c441ca000c0c14400000010708004041d0802d501c020890f205c0003403003401c0c0c0070b441507000307601521047c00c0004000741030084401c49010048040119507140381d480c9019002415811038801700c0d05014402250701701040365020402000000c0b80801d181901070304 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 70452493 1250 70451243 70451263
    0xf03090213020307090503011b0e0a032901090b0d170405060d061502120909070905091512030a021f11040e070e0a0303020d0e03010b1302120105030a080f0304030e0d0302 75
    0x15802d2905440d407045c5400c84901c0d0301c601480308850707001c42700ca050280c4803a00003520054041306a95860b030303d81c51082c08a2070840e030424103042d40e10302e0654840f006030314090145114180002c043c4000091441000894081c0000300c00c144807141c0d4103102400c81c1c008280c054443c50301c072034954400e8002400700f48500e50422402c0aa42091a031010803484081d40185111a080541001c14040d84031401011402407040f51803001c100d990324107154510802c1c03030981d490500c090000a02191401e480328902c4164024014000707001c0d004a16141c0046031844000381080300207100074064030340f00135041d00c84000000d01064840e140c101691280e5a00d40b40c110800746450140410b0750306d54800500140c000311984580c052044100b0714101c0e10003000071039a80c408100148412251001000e1860b03400980c50480d44c0301e43e110940188412409070215411946030740510f8411085514030001000001030201400360018141516028105c00310a220740e24010307568500c124 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 70453743 1250 70452493 70452497
    0x10050408060106050301060f05090a03060e06070e0411040911090d0f03110706080c070c0302030106081f060303020303070c050709060b070317100603110c01050705121501020d0f03090213020307 85
    0x18001081081c004c03c1280d04860742692060300d12080c5031000c80d015080311b0b44040d4805d0003401d001000c00d0560080680704680b0030058001c0d41840030015001c51440c034001d134022403d01c0d6025011454074000d480884100c21800b1400640c1102c0501841c400c402c9840c0e4000d14062000080c050b000c01610459442a16000740580410000c0f0341c1e954140d10031100010907a0340010074898034080945846807003521400400c039200e900080c252520340e00103c2441d40020004c240d90078070b40c94070789a80ba0f0204410411241503407002500c0344401402e80b4140031654445c442000405c01c4482d006001013902041300980b641041e410701d5101c20800d90020741403801403030410082010fa24040c2e035009000c000407914281081e4013610104505000d41c071800d000b40b0740d0820b42070182c9c91042500b9624141c1c0d90500c400400769225003d801c0003032046241e100d02145903000104a50080c0143c24404000c4c810070702c00b10b014001032540250045076030408050400c0c91500514002e01e069 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 70454993 1250 70453743 70453753
    0x50103020114090f040903022a040b06040b030f0408040906060504090b010e0901050f03160b0d0e030c030706180f0b040302190308011203020309090106020a17120a0b060910050408 79
    0x30071140b6003240141040301e503020460741051a581d240a42c0701c40e074841d2290041d02e04411420000101a00e0040f101c07103000c00f11414160114900340c4100480c1000480e961401e15081010358291400005c02c031240c03c00e810804a8144078180c41034900038854503000740481e68464800402e1074000d403288080c001d041911402240d0300405818410003405003140a043c1e1802003040102c0d2030040e00e00e0f0700340c02a40412a00314219900d4013010b800703212001541c903922500c11200f160450440c0c100076400c01d00c00940706c1c1c003001c070403240210f4011501041320581c94455002c08080000020005000144c80c403040200210700c041c400c2c4c0c0280c080c5e824603000060403108850180c20002d000440310801804562042050f01c00150300a00c11242449000c03004200e40803000e801c03803000759110008034010800c6018026651100d900181030503d0403040c1007202000015004ca503504d5201e0708c40c524903403100c4041e00e5240307400800c50040b0500300344002d0704941c09400b07000513034069 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 70456243 1250 70454993 70455017
    0x70602010c0923130b130905100509030406050703020106050a030f060f110a14040e0403080a0f02120109091a180105100303020309090403230c0d0e010915120e010501030201 76
    0x2030040600da07400071408400e241c0500080000608180c0e003822901175841e041119241c58010400013500103042000480c1500c3d070134090b1802d01d20a40720401309040c042000340f20f010100a45044038120308040303444204a103400c4c1e01500e80f42d08187e03001580e2460000600510000300880e00e805040b041200052404401c4241c03200007441854541c0c0402101d06454400c4035400f0200100001840c00c15459070110030751000d0948041d00020800d4080c06034110480c803030710b20040170001c000c61501c1d41d210048920080144500e02e40302d40d55060803001d0088c00c4d000c0001101600140030864904040d035030071a4061401c8810f541c0d0b2034100020000c0c001c404004040c0c82e090340081d0708004c4403004001044100420480801900031910551a10f411400d502c0181c440d2411540380d100c00b915540c58480b03940348110420245244018003640c008a4120995030004640030300d1080022003902d00b41042310709118110303c0c1041c2c000d000c10040d400307035060700d200340d03a58086248 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 70457493 1250 70456243 70456259
    0x2070b01091a0f130e07030302010b03151308030601030e06090303180c09060d080c06071d0102010b1003050705270108062e030905030304062c061603020408070602010c09 75
    0x5001a00b0607000400000e81e11100d103450321080383c46a01201010038038144070f141603814400c040c0d0040b00942e44034120000b492505002d802e00c10301c501e4492000500d046c44100c0c05180d1001c00203007200d040040400c1c0c50f07900c681c200700d01c2c0b446803101311026801c250340030326a2948120351860074002048428200b1200102e00c8505242005000701e000b52030700c41c10030013007007601442254901e0003041101107825003400194441c0d450f03929070301c81400200306c064400740031919040b811a450b001c040b06499461143c1c1d010100c84074540050f20740c0d03c1e1001503e507882058002d20782d004048407442c2d00c40005004081000c9001c0c0d07510b940c0e6032034030002c5c04101a03401c0c0d4100b0303c0381d540030402d916010707260407509400c003403d03d07010803603c221343c403003500f0755006032800c0d291030392124405003010000100d4030f0900c850b184001c481c94660081e00c00e4680d01c01408200f0010341c55181e01c44100d10030b030143e034082c01040c4242da000d15640e1001a0080100214802c041081e14400103003182c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 70458743 1250 70457493 70457531
    0x15140a06020c0f060c0f1b0604060c03110c0301060e040210021c03020f1e07051c1b1a0f010e01081b0405060a0b0409060f080d020307120c0602070b0109 67
    0xd52036001840902d0320b030030800000d608020160760300601c1c2405900c1c07945c1d0040111078000c5d40c140014090500c4845814089207401d1120300b80590801c000400c50142c2c0701151103540d5070580341c02d6100443c22040b250a00c0039540703c00c0e501d5800c150001c00c560120840283c003441c42250b03042c0d00b20464107002e0361120944c0d080000f504c03910381120721800e4000e0f001820001d42c0145c40c14917100083c0440e800030b03035461580801122000ca007000811508000740541001603078003018078040040001000381507000c1c2c02c84001c0c0501c0c000d000801084030325141c40130086c440086558035011500c00c417010400d22510703031110310002c000210710401050071000f040c54a04250005800f510130300c006030102510564220706040c100159025120001c1c1016003d4124003282503403038a40920715828168008011a400540070658480e40000403984083c2d0311480366802400e040c807040e00c4414080d08044c08a13800041c0b200104900c407030300340e070607226412002c104403803190301d00070068 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 70459993 1250 70458743 70458749
    0x60806030d091707090f1b0804080405041a040e0604031b0209040807050c040c0f02010b0105040f150c120c0c0e0f01060305060307180504110d080406030f0f15140a 72
    0x1140d41c0b030506105540121164150000450701101c44240c3d68166841c216019a0f24132001555180c140700758841c55010b01321954100ca01c0d0407021070030103031660100c910441c0300399440303182d448040d001038a40404070340e52148001407040080c10040c00d01e261b12000f0843d42200050304181014030304035412400030300840d07000b41074a15603130b07034540e501c2c80551b010000c207407400e1049681d4401d5a98480c025605501b11a94880031050000714004c2d0035100e1301d140c0b02e41030040522061250320a1082400c040740c80d89040009035201510041c1c0e01c0d60110301000e000400c9600d04c1c1c007444c54002c0001d0181501c144010b4802680e00c02d48900c03064003e640d8a00b402e1241380040001a110f500040d822038802030030343d400565910002c00c43c0801c0d1080e9104002e8640e010007052214000681400e88400d503540034056445507252610380c4aa030065100b81a6101c0c23421551600e0340d4000c0f0b0741c48224041c01c102d250402c901000f0b00c1c0d0703103510a1510907002686107801c5818161009811 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 70461243 1250 70459993 70459997
    0x14031603061401150e06090406050d0f0c09020405031009021216050a0b030408190323040605010b16080315090103081e0c03120405160b040e060102120a0c0303091407060806030d 78
    0x208803e40403c0106c01c0d8801c0700d94560150301d0304404140780d0b4855814090b4188555090f0903a5402c44c513124400307030b095074003115210744140403c200648011802c00304d0905110b030005102c42d4030317200203048001001004101c61088c4440e8946a003241081d0000f600c00460700141125500e81c00c1040380e1008840c0103000e5070042c0104141e01d450070741600c10400c21070030f000c00c94500ca08111401c1141503c42440246c6107034080c0800d20a8070b104141c0076100b1001300d5031402e04000300b17124190300003c500400007107001000420340c0c2d40d401c20041490100809001c0c195a490500500315040001c1c001005248280310003c000040c0e0226880d14080f000907600704032000314100300c41d0030700078016a004c0c0540e20544a01c145102003000c0501221900591a10705085c554201460000d04041c10766010301c0750540b48808080030385501001a20300450001a14a02200a03003100078000f03200602ca04200c0d0f5075503802180800c165074582c0d8407059a691070204240d6a40150310300c1d040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 70462493 1250 70461243 70461257
    0x106031104051339170702060711030c03030a0606120b150f0f070c0e0108061b090105090d03110d03050610050c120408060f0a14011403160306140115 66
    0xa09041150030460307907210050020104c0f0761500300c41c2c3d140020782d1941d10300d0b02c2c0118401016800d420005e108185e0280e20440d061615055101035a00e02001c0c0c0f80d0800d0000b01c80f85111036450410440e81c480e2902c50650343c40341041251080649128041c40e070102d0842c84500e04012054454100aa40300904624143c1e000d00e40102080e8852070b40024206410401411086028001440000d11814110305003914101d000384003900306801c108210341001d000e100040743c071814100c0c100c03143e9504031550740341c1440c0181da16100d5040041d4004400c01d082c03406150304401610017190001043d10789800300420304408941080745c0e419840a000e1031305221181c4540080d010364400b483c1201d000710b0b0085039404850300254400c80c45640b0140c104a58082e600702c2c041e400c00c3d9404000d001d0840541d40000c545081406480495004801d12242a950030820b0307c003a0030100101d00c00d45a02c0307042031000381c288800802401e410740000001c0c0040e01a1103076001c5500d680e41c8603 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 70463743 1250 70462493 70462519
    0x4031a06130c2a02040926040305030d0b0d0519060501080a050a0f020f180402030111090d0b061507080910051c0504020105042301080603061003080904020408010c08010603110405 79
    0x181070f03440035004890300d20001c0b440c902c01a1214032034020203074007414070056200b440c405144600b0884a20000d42c40500788810800120000700303541600e1008140030654607400c401048400c03052190143c2107200783c149891206011a10100266005090030b12040e80c0382c0c0700f0742da51b9130349692004265a000c00c87d8040407a12049172510002e01c0200225001c001c1900002c4119292000c200c040c544914140421032600f40715280c2a031100d409210f06222442c40000c00045903403002400788001e090018503299503040138182a003a400180341c1d2103400700d0504881c00e800032400c01e80100001850781103828080d40940d9501c0002c2503507194040380e240e2000300980de015100b00d051007007c1c80003007132100d040010105501e028071381c100201d458a000040409401400b000e000f60803002c140038a21700d041d25440252900034000a64880e51400403c0091290b41c1c01041c895103010b030584151a03005980d40c0c106c455907038052104070029203013140c86101d2840b07a5544640740c58660 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 70464993 1250 70463743 70463777
    0x40f0204020904020712200c04020f040911040608070201050106080f090c060f04030204050f04020a1a070c061713081b12160209070201111207051b060601030f0213051504031a06130c 80
    0x1010152070440005080c28dc1d1804440b0640c0c40702c0a001e0f84114001c901840310590200000d0761010491009211651510303401400b207040c0640030b03141c0e8409050014a0440d03080000000c0c206001e07141690310f0010800003000d42c1c002e030004070700c20350828011481052300c3c252000e020b260000c0c280020baa1501e074080810300ca2800c54854007650510001c0085047d0011000082080707482e4002c0c2d021140800c0310308540f0040a04901200e811a842d0108881c041520041060f0404181c80e8007064a0001d281c910b1003405480700c034034009407646543c0e240000c82c110980c42071b510304c1d0300b503281c9000a0b0700360380b4400d0050700104010b101e030070701e81d454500b140b50b04254503040c12442c14185950b070b440743c0081203041c041c0a81c0b01805020195902d4030640c0a0b010040f43c08500300351480b003c21032008076070b1151501c01c3c030045800300040240c5808a50045520680008502d402c1c9550034030201c00c12104144251003a0200d403031036a08a02910981c0b101c2503407581c030000505521 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 70466243 1250 70464993 70464997
    0x30708060a0b0307030507090e160302090f09010305010b12030a020606011d18010509090309060904020a031e09120306030327080d02060a0c030603030503040f0204020904020712200c0402 82
    0x1640d603104a00301d0300000c403421120000e60081c41143d0740401c8a10380f800002e01041c800340e0020503024402030030406000c206403414a000710701d81c0350241c1da076011a40003a07040000540c90592083d091000001006015448540c0c3e403a002c1d03403154984801e1800054807402640243c0300580c20110008040c0d40c490890701c1c1d400651b603202c5c07049007d981c070041000f1100f1000780c880032016007801400540f81244502d41d000c29900e000310714295444d00071564500a5420706405940c000c0383d0031910038080c1c0c1010880c500c49040c000411107200c031500000c2c10f604d860903140281ca440020301c41c0e6100b80176440549426449540103c220001d480d14104604400002c0b00c9044000125013840709010b543c8208105500400c2c403800c010320068102c40000d9500d105040c9801c0c01080029005419240d1041d00150450121103075030000c00c0c007a101c2d06000c5a400b9100040780b82c00c010225200114000440e66000d1010710080210111001e00c00e0f8118020361195158555a14041e00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 70467493 1250 70466243 70466251
    0x506030a320906090304080a1b17070906050103060e04030e030f010f0e10020307021c050706050705040611060c0301120c030606060203040602100c0c0303090203150109050105040f050408030708 85
    0x75925801c604800d018038a180200c021000c076200e107100307000603036000f04111600b0070b0ba000e020b0762910f03141001c051340d034545200307009004200d4601000756641c0c2c1c00030584001e10400c8a46038040c9240240c490322220f15005203041c403072610074080b850354401e202c0d000c2640e070f10701040310098445440a58011441e030241a601d441240316110400800703002e41201021400342c0410b44100e0f1064803030410680d5143c6596031031040c810071810590010baa407040702200c4a564440028a48088560b4410044094034460400087c0b005965000c0c0051084031255a40c0341c01d00110b01290742e403106401d5032210410328050005100400c0525040c8044c2c51040d401959200e0f45c076640c1409844c659884980541c00210b000c00c0400d40510200c41042038110040241c031030203079005020b2b42e109080181c1016a5481c15008646040007001200804c0d0741c0312005c1d0791303907500c105000b4210900030386004504040780c0c1480308559020301805960320048640c00c6076610f840464000750014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 70468743 1250 70467493 70467521
    0x90111041404090f0c090e01090c0905090f0a11010801061107060e0604051206011d040f0807020117090105060301061502060606030402150708070507050901051f0302040f0906090c090506030a 84
    0x2d5000000a071010071410100f0b03125680440c85c042c500354484084894103402e901705079042100d13080028a01d00b81c4141a46d42c1c500c0d0001365038540e440e086151118519405445108600b0340d041071020860210810020903a50880c03681e8903084d04a0302c025a800380c50031030380e00c41c17141408014001d00c501c0d07661403009000340323040070390b10710005001c20200c1e110b0032070580090340140006580c003d80c0f0301d40fa103803c00d0300560381d003050f60301c24683c40050200903060303000100b030100840e0300c0b8039005440c000f140440c881050404503001e600a00e404d40e116403103503103000000664100c0c0b141591103502c4103500580f0541d903981003804119800113100b00da02848000016902542d84009001d00e2405004071a44881041c40c00c18604020341d001a4883d040c2440100010b03510b4401e5920f00e00aa5200ca091851161400360060f000741d8000100c290035000300490714a080d540000300301c0c1c29642081c010aa182c0c18140c1c0d0861072801440d400050800c00201c2c00b01d80c682114100c04000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 70469993 1250 70468743 70468751
    0x2090c1603031d0307060b09060f0a0603020717030a1b0206010f05040b03150903031b070c05040906090501051612050c090105070305130609150305010e070c0507050a09090b090111041404 82
    0x2408040c15640b005c0002c55150b44d0300c00e504001c031b09103182c4860340100180ea003590400c0742c0d81c000540c950210320074441003607000a207040820405502c50b01c48002e056800b15168109011075a01030070900f4640886001480780d0705052038400290036040300d400c40c95000040e8203180c00d0101030050440b645415100342440e0b00892206000c0c040d00c10181c54001e10780300d00b8140c003140300000043c0fa01c00b02c400c000740700c2140800c02811091044410841c8c0000d0420b0a41c904840541418103014140c0c3d440c1c030081040000c1000c01041411605941300c102d498800801c003400c88000340c0b11449a024107100010203540180b00400341c0031b000382851401d00c4189a020040130080c1d03000400011400c04017040802c4c40440c240c42d0405450030140165030610300c12844241008000408004a01e41d1420a00c0418007640300908005014100440d48030041e1001414401a04580199407000003904200d0706210b0000203d401c55069803505140c0114074954144d5990025405552 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 70471243 1250 70469993 70470041
    0x3020303030a0c18050609012a080301090c030e0c01050903030d05010807030c09020702010804061a03010f021306020607090302040519020706150807030f080304140604080702090c160303 82
    0x3000610311071085004041103040d641e0000402d50b40c0882c18440e110001a01c0030b1003545e07907400c240ca030040303420b29040030081c1c040c001300c94002a4268480b4070341031140c0c1c80c25003480f007400000c3d4142e9040304024082c10342d50410807011110114403202454205031440452580314900416240e24002c1c00c880c1045562190901111020b91121342c8541c82200100200040442c0001c02811084021420444640c002130211031008000810659a0365680504588a44112030000402a0080100e0303000c0c00122402940401d92420360180d11b0080005c02ca84001140743c4a075015a4850707001915507070a103c042c060107850141e0100f104ca02d41c418201551014118140c01250080f44001050540085400582d00312a48907080241d0900200b4040421076003215445402c4950fa959542045000c59008000310728803400340d5410301061044480c040c09507240201d520f403556486440c0120301038071070303103010482210348171a041004c00c0c0258040c03056054642121016808 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 70472493 1250 70471243 70471249
    0xa0b0c090a06030b030c011d0904020301110409050402090a060302061209100e0303180105010b1b160308070b01050103021603030c02010e030c010c021005040f02061806040b0705010b090408090f0a0302 88
    0x1c0a8002030002507031040034400c149000c12074102d9441c000c0c01c00814614580760540395504440100074002d000900c0410f0864a00758040c804810056007525215525034803210003601081d01c00340c0c40b44080c4030201d40384003114032071581200ea0040903607140440003100f8107130380c800c0104010064041e071032046051a045025031230400c2d01aa006e56641d00d00703e105d0704ca509031118828038250303162100610103c0c5010048803241401030401417110b4142503031462030490070300b801c006518100c00000040240c000e008d00340240c400c80c3c0c01c100316038031040110100e001d088501850300c0810001140031034002c3d48100c0a4000a03c0003140701d00780e40300024610b50000700c00c000942e46d17600c9078081030743c3d052009007980709240c1ea041c041414661241400d90410341d0010340b15503c000b5040341d032560600c20311401c40002814084d01c1e241d6544030000321341c0042400b03551070350030b140c410800c52408060884c41a540a0f124504005002003840000302e08503901710340041c00802d0100250b5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 70473743 1250 70472493 70472509
    0x2070506070c0302240c07061d06042102060601110a0203010614010306081603060c050c060a0207030f08041a090a0602271507110f041416050c0a0b0c09 67
    0x700301520381d90741d442101e2800a1811481c12400501415845003084010000901c07554101010364000ca4660b080d0317081c02002044000b69034004907500c4159001010745c0070400740e108074000e006c1e90b2442c2c041280941c43d041c0008100c940140c0011000074001d60150f80608055603481084039070018003540800c0c00c40b00e040d0001107a10844440e60301243d03a05000d4100541141c9024000c044145240c00c0b109013420b00000f0f01e1a42c4544192100c01d11031400d841f0307042d04881c00c8401e103040c5806650001d501584003603001031000c0302c402a500c0c0c02a156140078982c0000a650024100700d2025950070b4081c180035424010a41c20380c010503010300207400c1f2400120512107550740310a0140548100420b101c500914800c1110b40c070280c80351041c0c4101e6900a41104407003c42c40c00001c1101d0014645580e004d868041001010070740740e40358500c120b5084412000c1c8100746030050703500f03001e250411005503100c039000400048030280c030b26801c0241c0c0c11542e414002c2c0c2c071001507149 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 70474993 1250 70473743 70473751
    0x30204050a050a050c04050303030c030619060905011d0102100c0e15041e03051504050106031e0c0f05150f040b03130c050405040206033d0e0c09030d0c030302070506 73
    0x4984401c00e03c01048480d00c16280c0141c1064041490145003102280d220f001c020206011118040001042ca8441c0214200d0001d034204855508030303215070010b044141e5a001e01800913185030040806818583c541100c2020160000c0c4000340c0c0c0104264040c10804001790300f049542d945002054445860131401040081e4442e52190b0400003c2000494032940c0301500030440c000401c0410f00220780f10005000e141c4003012a60303250300b0082e0241030103600c02031180d1403c55090345205040f13444c40520900c40c6500001c495603d41000f28406010f00a481c1d0191240c0c4610700620201401015441440300300d407400c09903a0484a415030f0011039060300d5082c11001003504200030420004068881180c04000324180742e00842c2503804010402c11203421040660030b1101604003030b00b20811800c0310100d85212880c044141c40203840d1061b400903506c0340c00807400c03445e142419109183c10141c01400b2040101c1d804a03902d05aa00e0144c09066003040441d000c41d0062012501c6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 70476243 1250 70474993 70475011
    0x10e010c0509010e0306130209220602071208010b041811030a090b160507060b03011803030b030c0306040512090604031401020322020f0402030901021b010c110d02070b03070903020405 81
    0x1500b8003000054403482210503190711070f810203400c2205401c4015180c1d5074194069403000c5d899a20144141250080c01c1c0d1042c115145a580880402403180c005082040c0725000f161401c00100200b80c3d6095401c3c001c0524002d010b02040c0301c580032480128240c606401c0000c40e040e04001f640f101c41c1da009903042600c181d107074801a01480101d00c10742d600051800d035102400c00b00c0342c2004003103001d000001464240c40b810b00e914940e50035040740031125406111045003808a1601900030402d203c2582d01030300580d0702960403441e020035020302c11340d0003c016101590f0040703d5058940c1c04040c80075803080c002d100c0400407038090000308411800da9800183c4d07a0030002d00c2e442840d5050f4041c008060303103030380800b40162280089011100303800e079009a1251074a200f50340c0a40101c01c40700d16040c55020030700003501c005422508070b00419032030710806940c0c01c41e40c440d220388104103e0300c0035a1049408101040c4c0000045503c05114980701c44403503160303030001e41034a00035074003003c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 70477493 1250 70476243 70476247
    0x307030210030902090415200d090c03060c0c110103140c030601020708030d060608010506070201050703080c0d1a21031215090702060709050a05010906031d15010305060901020403170c010e010c05 86
    0x4c0d40b1400e80325001c4e010400b460005102003601e201423405201e8045040e06082e166165501000a500c1c40000955880b0400b1301105c03018a02c010301b101d41100f4240c4540c200d9259808840d4080c1c801c0d0724103d400c12103804690b0340c920004a24942c00a00b0300c504500c02d89130700068240051001e055100d84a500110301c481c68900006c001040c10b80082d48503c2003000441c005070b03040030807241c20581c1030900b001556a400508500d60142030b80928001d0b080040301000c520030b01d0350003801c100f41241c0558881c0003030baa100c401441e00500c0c92a881e4020000150700300e00c82a40d0b2948090002c0340c440c03c0d4404d41001c00d14010701a2608009a03011070244011150002919406450b00365840c81c5072a00c4e000000f05180c0e0300b0321910050540e07030300180c0c10a5a0b800002900c140c05002200c0b101581c040344112090424030003542e80d4054400820018070060080394100d0b600305500c1c50300d00760b0124107245240d00440030030020350758400b624a481d1200b03004c0e01080301c240d0b131150743e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 70478743 1250 70477493 70477523
    0x80906071403030a05150d020928150f21141606031b0206010603020c03040503030a050a090e09060c09041514010e01110303010b0715020408010c09120203070302100309020904 77
    0x21745101526900303132603c0c00642000e480e1210900c5551140d0112201840e0340ca603030b000e580790076100b200c4134454000680085030180c400d0f500302c210380f8121060b080e0602513680c00c52a900b0600c600549246120450808140300340e0403084076403150290481884009000342c1d00f0b40b078a45004458040c08513402c0741008066018400c072402c00c011610404141c07000c505000352140014000c0720103246d40400d030348403040410002d0310301030440234040b40d5072208d0018000d08a50070180003440050401e9101055012011640500900340c040081c42c0390340f01c0c0426495280c1040000ea50065917800b801450a036403484008020800c0c1d00701080c001d10b4200004290005210700c06050001f1200700f07018a010020481c0d0449964099554a9099030300e03011410340d907050b00d2480030300d00129010810a4042d8850108036072141c0390160304550b1180c114859035490000658103800c15031040025081407016581100418680022182c80a07400a1307002c0342c00391002e0720000c40d204004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 70479993 1250 70478743 70478761
    0x21c0e0405010e040f03050a09030203030408100e030406120b06071a04030f030c12051003021203040918020619050c070303081608130f0f140f011d03040308090607140303 75
    0x250141c100f080289400e8a02074481c410180388102d401010032100181101c03106210740c0b2404c000e950b0050a6139903d40c1c0d02c110781960b134070030714103003a04151800700e50392240c0800108407000c850b12a2200007000c00b4110310300004108c064000c90300700d1000c11030345000601c068078000e1000c05000101809080606009000080500da548149860400d4000c691900400c1c0c200c0d10494003d0089001d666010500d529142d540e40020340250101c4640c5010900110280c0182c0710f0b0071200f00319110480c4c54010313020610920194010a01b00040032140400151814022442d805c0103450160600821481d00c20140e100368000b07003055007400b400035403c049160000d42c6078504051a170415082c40b142052088200600c1e80702d01002c000708100c413200e1581540781c1c11803103020710141d00002c01c0740c0f2520b140706800115464861054010441e482e410b8a1106c1000020350500b800c0d0b58804826a0142c91030782c0d0300580c01d01c09600050106042c0c3c40701c0303c69103406107031282411040c2c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 70481243 1250 70479993 70480001
    0x70b06010509010c0b0a18050304060212130320190302040f050603071203020a050703030306060807140a120212070c021207050d0b040212060f010501090806010e070f021c0e04 77
    0x2490401404000300720690b0780c0031400e000002d4200c00ca0002544910544e20024400c00e0050101068401721401c240311002c409030045501540aa684002c029007a925603881a040030b090352007401e250a101007856080900c2c00840f03c01ca030305074030480344400100d0b0700070400900e80044480640902c118182400b40c01a9072851078014085410f21307100080d103c0d071040c003850341e5103520100714006041c4204000d15249801c0401e40e410300c0c0d180d05004025182c43e00a0030b020802e1a00461011403080703030503c0407140c4403e6030600b0300038255400c4a1191043d43d83c1d001e015000d0098101410002c4220ce00501840c0c45640b414a81c0b4414844c4280c80800c8020042e00410410486074481c00300005a07180d000c117a0364090398035440094110082042071034050720460080000200892240c181610002d8031030200d1144d80714055556800c0074002ca1071200e0743c001c08503d1050041c0d02c01030444007140140c81c0950140b09242e5503511885040c01d0008113010300c030380418109445 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 70482493 1250 70481243 70481251
    0xe0f011506030204031e080d050103080d0c0203090d030806030c0307080105100b040614090109080a030e031b0312070309031a0118020a230409020423010315090c02031b03070b 77
    0xb41507080905d541c561000324422400e100383d500c0700305500c40f000c010b10001258190302d105a02007065584905001006420506c04001c00c64a4202190002400041a2462280f005000c07071352036a002d030360440314030354040c0c08190588201000900550b50610818004d00f0100000240034030b84240c1a0000e40c0255100581010782000b00380038265205518149000d80032802c03e584420840040b00da0400c0c41d4040c02041c001c003a60740040581c07158890407590301c1102100c0d07443c601c8012010301d110266800b203504d640008070004410151101404005019041020242d0b0390f1341c940d0700d800c030002e180040424407040010b02c507151010703881201c00440c409086040c058103030f001900d240d281004410011151410992800e80000200c80107085904802d54440740d6584403a04500d0040d00d00c00955040385400040c1540b00f440740902d8075a4082101d40710620303180e01e15008110080b150320860208214a0803010300303c0340d60320a0b059140e07000f555100180d05002e10740580c094 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 70483743 1250 70482493 70482497
    0x312010605031b0a050708040608090c06040b04120203100212040519110f21030d0e030901020d080415050c030702100605031c030e01051e07020703021302030a0e0f011506 75
    0x320a011400e43e0080f107a41c1010004846941e544003030350410303103050080d41401060648002000300b0355952142c281e86c020000c040c00c0700d1070400c85d441001040d0050307014010502500340810001c500002501c116200d0002d800e07030f01e0a01d100c005210a91740041c5404007c240c4581c14081004402c2007071003000c3c41f2071200d68503691090780d5411180e03804e8650403403013100c3c0b940c0b003001d1590302c160007030304c2d401080440c15144002125180c1d40340d03004081c10880c042d140642d0f042e6111700100172a09003402c143d000d050a018410400c0e5918070014006135008d0303841091000b034681252103054000c88010121a446e032400e5140289050303500c540900c41641000c2007000941c80015200e01c05082e0640c208605050001044000b000c428080c54a19804d0030301b4080c881c982e82c2c041500200c120403d00a280c0d0320380300141da80390058030000350018007aa00c001081015079003d0b42d0099464203001c81e00114403000f191610b40d55400d40d4103e41d40d9050031500d145081a03985000f403400d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 70484993 1250 70483743 70483747
    0x30f060916050a1d040606031a01030218010c0f05030c0c040f14011712030a0606090b041206020304020d0210030506031e031209010b06030703020c07050105070f0f060204090e0312010605 82
    0x41ca00100305002e0320410b1024000001050800e80382c907144140d02070280031700f0400c1219a1084024081c0014054020403100d030108000384a500ca8021511120000c0b92900c064070b503c58011201c00075180829a44070424007103400028400740014a40005080002c180107103400040008940c0c0004101a95620300080207084150b0811038604640d04644403401e030180c00071a060078095100c2d1031aa20460000400008107240d03400300c01030f0748260b51980031b242e440e01c240d030450f4803880c0600c4c0540107590081400103007264008503131062024007000ac000282d5400704054000394504500440e865204201d11801c0802c604c10b8462103441185c0c0c00300000824958070b03807050401080c5d903280004000b50180b40250080c00400402420547d5245001140180290056034a1401c2d5001d00e00c800a000d611030f10954035241d030410002c0341c196003580c0e20300c0b4102400040c02c4a025030280800180800184104c0d043c241c0c0c01c0000e10390300c0c2014103081007030000580104040c0442 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 70486243 1250 70484993 70485031
    0x106030e0a0b0402060d06030b1005220903050f0a0215160c02010503041a1602070b0906180a03060f020405040608030c0303060108070c0f080a0314010b0d0c03060308030f0609 77
    0x40021810080c0b50415000d400644850000c103407144203a02c3d07180c1c81141402e00c00010000d2081180e482511801110400300e6141c100b0000b10301400c1006111b94010783c10a00310f4200d0a5114440c164407908045180c00034160f04c80303510380c0090640002680194502035400c0e4410001c440c4d0000680700c0c110f231600c60420025011588258010741004400710001c1c04111140185040d01c42800800351307290b2130142e0030504c200700c0c2e840f00c4074010b02881d82d00045262010341658200100249410308000c54007983c03190001d00003080941c070031481c8900002040380b85c4200d0001983c649000342e0344034280414841943d03075a504c43c01c4d00354030400220114001c040140c03508203c0034a0300b001c0c1381c5c0310300408079070500440d600503200110f400c226000f04602c090043c807840e060340e10180010009209149150324091003240b08424040003016401400c641c04082da40754a401d0000c0ca00340c403070312000101c1e0402c440d04846c42428200b03000d20351404103905503100358030b17145c5c01220102d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 70487493 1250 70486243 70486271
    0x20708070902070303020d0609061508101502100c02010e010605060301050a03061508031602180f0412110a050c01030e0a0f06021e0a02061f050d1103071509030308010603 75
    0x24a4480e196009a011503500308061007501143d080390003280040c400c003034480ca49c000052103203105422600c0c40701d00181c00090701400391075111300303100e04211602a00e8020605040c2610030700c10700c00c5003d04505040040b90030b12880c580a18558000182c0301c049013015801c41b41e40d500054030550f4240010040c80c1d03501413881094980c884030108807011650078a8411041076008131001d4000456800b0450700300d440d41d01c0d642c0f03008540345641301040800d1200303040c50945e02081804994400a00441c4d00160340041610385454100701c0420407040d07881c00c154141d40d00b240ca85d0480020f103940c5d9030785030040442c2d113050440030b886441c501e6501e80c42402040c0800404598000ca40560b844403015214941c4040107900030baa54485d5800c02500c60b1811504082c045c5030240042689000042c0e110060314405082140352003801e0725140b0b400c690000060351b040c03003a02c1c404141800c100c4d072200128410794440350a4142189000350024505803c08000c1503d402142e0386414 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 70488743 1250 70487493 70487503
    0x41110021c020304180e0114010914010e070c03030e03040f0803191103040303140403080a05030603010606090b07060504050a020a03050a050c01080c070b060d1b03050606100c02100e03060f1501020708 88
    0x4403000000085213030004105602508501c9901d42a4281c1c8d1400010a9030140e0040749110059122940c95aa243c11410301011000d680100c0003c0345041c40c440042c0c0694414160280c4000803241080e540d00840000e000c601e42040c0d45a400124403581d0f41c0907403811081070b0700e20905240c90744d84800e2542a54900a510014080016200d840c0d840418404101e40145800c1042e446c0d0341c2c0314461001d45a6401603410034000d40c40d00174002262885060900191120382000e2407a00c002030329400081d100250040d00e147c000c4846c0140165207461400d00194400d1016211060980c10300303d003001d070720103042d905200e490410011079040c01400ca803e1030750b0240d14010b181c1c07104408184c04101c2c98a00a0184801c801003c0c51020145c1718103049911841c1169a191b41d1f1009018510007000710300340120702440b101000614000841d80d24001040c507000b030355407110300000380c41c100d010707074002280c0d2251b8401c1c03040b03021281c890034001c1c44080c0021f1616900e080c0384190f5403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 70489993 1250 70488743 70488779
    0x10020606060a03020c0106090204170a0c06050706020909070c0c060807050901030c02160f08010e0c0619020a060903030207021005030f040605100b04080c0117010803030a05041110021c020304 84
    0x1411000403480b04140c000e50590700241c20b103000801501e030301d481d600d00095225010382100c01000322101d0f0060440041c00d800362a0348500c1030a05246482d009947d25006180d04940e92602408203c01035100d40061a2064540b541c42c402860796038101100310b5203468025801f000518410014016000400c640e4405028640010700717a8a65504030b00b040318030365240d0030031504001d0004007003855180341c1c400e13070b5149402007185c02d544840480d511012032030788a820010610018102c1d03d4220302da12001080c90056640210656940c0720844030071600031004658089600800c1d414039184000c840c41850910038998200003024160250740188000c0c1500d03111000140040210300c0b078840140310202603561a581c65102180c4c440034001c2c8034074001510601800f4030b8020203e40c885c1200da51001440ca56200c00d50503c0250030002c7c400e54104001d40540545612644203410451110344e010705a1000461003582030101c000c1c1e016001c640c4280400c2c8079680501c2e85800e01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 70491243 1250 70489993 70489999
    0x3040308090103240501090602030408100b0414040602070605071b02131d0a05100c14090409020604030602090112022104020a030501050c12130803011413020307020705090610020606 80
    0x84441c0580100c015003241c4c040004c003500d5907078124260941100c04c403000c0e40c07000d032244030016031505000c07650f0780914405d100141d40304528458512456034407054084901400c00310b0b01c40000626288260000d8804550060b800501101440410b00c10260000554605824000c840010310200407a1444000c0e00c900c0340d010b10f110080030103a010740203500034801c00450ac44a02e80070991641c41e9040300342c60070f009441e10814103003850712034a039840c40d82e030f03e402c122810700d428204030710b400000301180c000740e5401c07490000da500c01004d44021032007020007507907801c0207074001004a522105880340003801804460b01491643e27013886002c020007501c442c3c69583d50300004d07551580075800038129518101c1440340e0043c681c0014039602c00041c140d01c2140e161403c038000100d00c1d1900141440006200622251044c2024000404030052500340d603480e01c01078602c101e90042e06c0c100003682c000c2008010500f88800792550140e422140c00408201c0a0006511464002d0000384 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 70492493 1250 70491243 70491247
    0x8070503100302030712031b1e03050f04090204090b1806040e010f0f0c09060206070c03140903120309010b0f0f041e0612030e04050714130509040b01030b0108030c03040308 76
    0x52000c1c00038100d0030085400030120341d8291740e20f45160284000508007900040c0301d0a40781040500c40400e024074103603120382043c1c41c1c0f404c2448103032500c1b407018100700c04211040052a40c681c10800c040c001a08480b24016070382d40c07800402c0340172515501091800340220500011468060304044c0e50312180036100403400c1219507061500402007160844446403500880ea1385441d0036501c00261400c081e100c2101300380d103c0500b80e03640d0f9400c890510014441030300340342c00a80308035003101580c5c400202c0707103040020200004e42025904188070110600100030418a164240212821443c0035100031021181c40c80109448218801d4407d00490b02c4003219100c01d441c071002a00746040203202088565100d003009980600181010f03030008039401d903090003d01d402e114581c001c0780b4507203c07000440701802284043d9001b040310840b207020341040c0083c81d9116417528610603441001240c0f00d41d815854211070190b81030300842e14541c82841540d100b41c1c1c00008440a4a0b000303039450b5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 70493743 1250 70492493 70492501
    0x10501030f060e0a020301030501110412030f0c0f1a13150209180903090907080c0702010c02010e04020f121302030303010b07020406030c0b120609071d06070503030c0403060b06070308070503 84
    0x141c40c2640c0700403d10303d88402040041005940954141c9210750000e000d20f15240c40320a039607008500030280001420a880320002e400f507102d000b1203801608100d0316160603038886000c141d4001c40c0c00e0744d9481ea8103e1010080c1042030300b69500a80c1c902944881c0d24158030360202d0f6120081da5811911743c0006c50703c186594001c01c071f03d5030485200d00680245400c00ca550b032240c200d05c02203800b42c04150301007003001d40600500c52040400540e42824903030b09400448003048032120903818003450b514840b20741d032100d0004094011f540b181103a99080003010301e4030340d450300070702c440380511a007002d400050b580801102d04540700c402205464041d1400010f004007007a5000500341a100c0d08000f508071100c001501c1c0c1030300a0010f00c00321399140000d000b8422804c45401e8006040125031441210190902e049018070103081030307051985503071f50146994800e4420810040010a08104001c000d0140031140e0205913030341410181c155501410040e0041c01030414440c1c048002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 70494993 1250 70493743 70493771
    0x80405010b06160506070305040b06060a110313050108100515130b0d0b0306061909020a0201020906070605010519060f0f1e051b0304030f082505032a0601050103 71
    0x1d9080200420040c0d0725000c210b80c042441070050402c0720980207040019610070b00a00c41c00703100e580c000984500c81e550b62802c0054a40c0f141040c2d8052220a08242101caa0100046d04909080021002a032810580003401c00e0b50000c0008880d0100350394184041e407500c92580021080c5104116151080700051141c44d4036683c100710710340d000114464052807801e821407541e01e50103030103503107142d03c2d014140480750100c20041b50414a45080400026945500801500c41284001401c1c5107010000618641c0f21001c02d40703420791103c005102c2840e011490110804c081108440c00c02e2070b044000d0489030341c1e03062046c14092407910b81e20340603001c2e0708120300510700c17280c8044000242c04805000390b0002c0540c05c401d011107100329104801c0000031201601c0d00036281b420041e0309950345e1001e0368805817080c91000803820203054560f01443c44036948500c02c3c00910380320310f1169443c20650031021000207800c0c4851030341242c071440215442d81510000c0c80d01091032275800d840 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 70496243 1250 70494993 70495001
    0x150403091505030106030c03091110120204030c050f062106010507020301020c100507030c120b01030e2b030c0c1502041d01031a0103021302030402030a080412050708010501080304030308040501 85
    0x103220341c00c650020464040e0742c09801541a29203e480400144003001001c07421034a040c00001c00d2103000304010280e9282c2280344c00348414407494181c045900741c1a146080e600540d01c119500240c0c500d0a000c039140002100380c4080c8103640b00303401c0030742103d041440f07504030029020005604201041d01381c2d04c9001241c952580140007559a0040d1010701c1d592451044260391030b50f403607c0f01040e0b140388a8018540031100c2560f844684a034501482c000030300100301d00605150380e40807481c4111906201d0090302e0505180038044030211a0103494100151031101c00070103240400400203140c214903100386044d0440109852507903004841c1009209640200314502c90b8100b003054544081c00c6100c5c140c0f80304142e60620040750310050003182c102800020342c4920010441c2c2a291415400f0b103901c140003c08580110240d901c0d038803d0f507802500041003c800d41d285030003d0220810203840281a1b01f4020841980f4206040b80c9900990000808108007000881d00780700303003508 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 70497493 1250 70496243 70496249
    0x90c14180c030601030e1618060f0e1009110406110a05030301080a0201020f0d0e09150406090b0405060f01020c0f031509030415080906060d0f0506010603020306030f060103020315040309 82
    0xa400d05000381c140c9003a400854001c1d000034100458030301c9001c4042800d058030918088818412800c2400b226841c108000c80a15000c1e80c842c1d0002d0413202c08840507004050a0412207030905110030a00300d0325515400ca009514103045141180c41c14680455040350000c1c5090150075854640090429400a1014059100202c0081903201000c54007400c0b040c803d03002c0300d11001c440b02d92191150070280307201c008a81b948070080c2460800c800c44541c40f0400060021120039101c000a01312440c54010080c4c03180d6901e40c41505080501ca2550065021554200700540c00350001b55204501c82015000d138407210340318211610b040051079014450103c01d4404c6241260200b81d50350024404d1301c1d68000c14071001012035004407006802140040c01801d01569940140005d0b0281404103c40007504100c403000031650510031240a000180d4006d41c1d241000c01c1054507203c0942c40140840e00041c0c010001641c000840d2802e403651030311040c03910350351810191000c1c0e07a258 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 70498743 1250 70497493 70497529
    0x312021b030d06060201050903161707030201060603060b09030601030201050a03090606090c171b030712020d060824180c100c02010815061c02040810020c01050a090c14 74
    0x150303004a580001c805007124000000c802c10003141c1e1042d0403400d8660030780d1621082e406c20003000c030b0b18a04480d18000d03a41d01400c4013a1940c8003420540e0740c9540888400c0e40140d44d2a901801038690502480c40101009114203042041d49000240c030340c0c0c2e06100081c1170020000d40d4801d02030003038100c4540c1d160000b00c204070396690340f0042c10150030500450070001c1c03924003031003090300c000740350031801060300c8859600c01161401e01065543c1c0045e1001051103502c0d024403102c1d5000b800102012000e0341d20101d902807900c26032929100f11283d44020515076162015190017081c00305e9035115040c1501035807440d0302c03020074034206000c9091301a0030084a050b000c5029800411031810a80300307a07900791040d940c03c22582962450030030b6280c3d201404020410544200c907070740110040d5240e80051500750345030042454844a070009400c0c40350003040501d400c035001e204080c0d0041001c1c00510403044030b40c3c0c602c68922500e001d000d4041d8010b612036007864a0312050b036084100c1c21 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 70499993 1250 70498743 70498777
    0xa0e040f0204031a010605070503030c030406090b0901090c05060319051f080a1502090907030c2d03050f01080304031b03080d1a041b030b180a0c0f0305060d031202 72
    0x1071304019000d464140491a0100440400013034158810030031200c143d50850003640c10f5403100d002d92400740c0d01c007910036504140c4500d5450089027407411707114004c26402000145641d44ca00d84210510b0560b030020f07109400c1030080002680803030000c1d481c1707500310400000f46581d800da514400034090601280000c903c0c0000401d02c3c440000d00c1c2503080c2e000d8210644920588100340b4141c3c46003812245c0c0010200001c110b045010b5005890780c8101820100038031070038039449002c024a030274039243d0034203e241104c00501c0e0f0180300c1e15030044d0070745548500c5036042005560b601c3c0700b20f1200410a10700003082c003c42813449101c600142d03911007142e0350345d104400f4229001e4800454020561842c0c100d02d113446142c1032140c0010400994a5116502a0400c080d0001c000290f407890b04a2440c400c4850040303601c0d450f0501c03800600e500064102c21071080100360415428007070b021705191800b882103a9580200c03c1c0c41c856410b10f043c00e8184040b100d034001030b00521041058002034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 70501243 1250 70499993 70499999
    0x3110a03030203250504060305070c050a0503190503010509070e03030403080301080109060e03090904060f0e010203090a110a0305060105100e0613150e090117011e020408010501060905060a0e040f0204 88
    0x105800444c003c02d04814560440c1c0114881c142d01c900304420304001041c02040100311003402508465840200c50030705015194558503241d0401c2034144049400b41c10004840c2117004c004d04580e40410100c8c5046411903050002040c400781c0003070000c03410b00001c040154101d03a81001182d000d1584824001e4695a407070030400d010b00780d2800300700e520500349400d80c4090000001510030b105001800280c2c246c899032900340080200d43d400a41c0940c5074100482c00440900055000e54006001003004100d10308080c900c80c0d148108092003511410b03030400114a0010f8114191041115140500703142d1100540e8115022032403240c000b500440d0faa4084110310081104441e03e481c1c40310001c2c0a03031001140c0000072181da584c0c2c4559024014012003210200210b00000d01000008000343c043c032441401c0e581c103030500076030550000f170305000c001c1c000c1c060680185000d00b000d040c41da0800c0005046070244040e410204210310f543c180440d51035412044071034000c1c5104644e1552 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 70502493 1250 70501243 70501247
    0x120f0a0c06020606010507210302190c0c0504141503070e040311061513020d0e15010f0605090f010503150a120611070507060518040f05090c03120d0903110a03 70
    0x5407140501600404000a565502940031076510b80c0c0d01503030083da15410b480d05101c2c0500c140080740704040c0c1c00d00c494850200100035a44410715141c035000b183e11014500a1501001a0089800349003015860304031189002409034001c1400741100074044403040101c1d1400c40280c2c00b8000402142d01800141a00009910140c00b190803d9a040d5075481c02480c1c40c0c803074000311180e0014103044090041007402c2e4003400c201c804d00c0743c012440203004d07001546010a00411480c201404a00401c0701810918600004201d542881410907040200159030030760040348490501c080000050070301d407105180031341e010400524080c81c094540415500001581b40110303500c1e407500c00d5031200300755000142c80c910b0794041c0c010011075003003034002c40e1581c11146404044101e880c0660591f6602c0d401100100042840d00043c2c0b441c0a00d4107528050b005a441c0b4002c1d002107a05420703070080e480480701c001c0300060012901c90128a0f080b58650b500310f0200c03079240200030305201015 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 70503599 1106 70502493 70502513
    0x3020d05160c091d0c010903020d060f0507020d200304090e1903020c010e09071d010c0503120f06100c1e08191202070203060402120f0a 60
    0x82d81ca02c2203901c401e030815002c0e16282d54440454140101194409403d201c0c0241400029000080e102942da0b00019020f00c2400544d8014408290881c40d05d0281c9035008200b00d10341050000c0d1503107540380c0d07007100050070245440301c0c1600000021452140c11009145014504940c540c002c00d00031041100038000d003e410703071603c1c0111502010a03400794000c0c2840020b84c40005101043c11543d991042e0442000d20808030b510001d041a004a07400482f40102c1c103100040c3d564123400c0c10002c029120000710303c070303604090803030b000e0181c400691040c000b52510410407110301c1d010051171300011a48000c56010541a0868030701c881c15440960070031181c86c0e1281c170059030042d40c6542050201c800345044055000c040c080040d040c0706800c40c20089251300003512520054800b0388601921115100681024011407821090074400c80c0d444118510b003101d00b03c = true := by decide +kernel

theorem cover : BRFrame.Cov 70323743 70503599 := by
  have h0 := BRFrame.cov_init 70323743
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70323743 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 70323743 ≤ n) (h2 : n < 70503599) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
