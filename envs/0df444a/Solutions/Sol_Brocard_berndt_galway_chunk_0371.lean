-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0371
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:28:11.815265+00:00
-- url     : https://prove2.me/submissions/e17b136c-0c04-419a-aed3-13c82046bc83

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 66546765 ≤ n < 66726621 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 66548015 1250 66546765 66546769
    0x1b020a050307081c09140c0f011b02040e06010608070207050f010f0804080f0a0804120219080a05040e0c070c0603060b090402180418060c0807081909051009022701050603040f02 78
    0x2502640c81100c1011900904441b05a030030014018416010388a40c4c0140d140d01d40013821030020346204003c4100000014800c44d211600400f03c44d00b4100c00321441541c4410007d005080111031020042c4122503001600f850405400b25003440c3c1a1200c6a00e8000d43c0c00480e17117000020304c01e0710b4840c01000300b1903824801c1c1000f0701d00c59043c0c0e0340c1c941540c2024642060501741c0584032104541c06450700c5218003c0769006190140e038403500859440788242d0041d40e0714015603200030004007007241040000c0e10200000c2a0a82c0700d18a000c80a44c3c440c83c2c103804548881c00b8286824030180300400190429500420705800b01034100445440c41e0400903040e190402e00c901140e950340c8072001304100c020b004503110b050300c0e41003c1906182c503080c01058203400070201800108004003600e90445960712007080c940c0c0113402c1e41d003140007203a0314002415100303600324083c2c403580346a80c8c26010403504003140c810080100300056486e12003000b00f82d80000d401900c0c807a0911103008016 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 66549265 1250 66548015 66548021
    0x9020a030203030f04260d0f090801090c0503100c050307030b0a0b070305090316050609040c18271109060c25050a060503070207030615080604061b020a050307081c 72
    0x15130051320b44659501e0414038600b00311000c942090307009080c0c4807010b141019020420040c4030160b45840410320040b088119101c01c003d50141444e54601540b000c1440511904501680e20a604035440020185540030860300b5018075000054821320200307085511a40000f40e8080000b0507034101c050704e855412010307500192007180030074400202e0100b03500307040c0701100099000000301d481b03071480d1001095051140f81e401b01d100700e1f80e5420f444103045c0117810b8060030a50011414403450b40b00d44490100d1189214081e2a8048046110102c0407850181c010420400314019040901e2041407043c55006121903030054058071440b10826801c4c280003500c4661703000c0141c409149400c00344502c03915030703400c0070301086010800c03c141113400003942000c4982c01030001840b00001e8a00784120b900359001056103025850030301c0240726a0f42c2042c0b01c801c0c481300c01d01d080074080d2002641d0b9021180001009034100b88102c1c8080b42d8000003910b0007a111070400000c62400036464022 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 66550515 1250 66549265 66549277
    0x10030207080c070603141005240c1e010b0a030f061118100806091602010f0c050403060e2b020c0a1806050f150c0f03070b150a0e010909020a03020303 66
    0x340e4003000381001910380c0b42c0648501e0700178200b0411b1030381c01d18802c0304524030a54040d190150a000d60003901c0400404034030011401c9103001203450b50f52801c1a070307440d10ba07944c801c0001021703010f08030207181006124012240030300414904e5501c1c55980d0351603000412490641e5640d95800d600891030802034001c003024007082d0200603003a8000e408100c1c18801c040540020080e0040800c51180c40303480d07010740c001403860210f251404014008030701500d42040f00c00c64146c144240600e00c95080720103001034070700c12081031210510490303100396120000801941542c040c00d000c04900055120f07600b186044c0b40c4192034000d0288800f18040d6495607010300a0f40d20215403103034030b0468910540d4041d0000f16162940c001039200020041c02ca0019084051b080006494025010410803400840120f909690721450340d418030240c5204121180071b00f02c82c450282504620b05061440c050740d0541c40781d03103566428000743c2c030010100d030141203070003902c0d039400440960380c2007014280f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 66551765 1250 66550515 66550537
    0x7050d030f030507021606051b011d01050108010209030a08030417070b0103061503030e040c230901090e0408031816080c0a09020408070b070206070b0a02120c03060a051003020708 79
    0xa281007206a0080464600409080442d00102c2440c1c00c8001c601041e9001c035481c40c900035071076054112826000c004820307075048041d842c1035136500b01c0b40c401845a4501d680803100030485d030780e0785078200350030f0340700c0c0076407190703068105002040002d83c00b94051074000b400350103458107044000031417048079400884203a40001c0b40e0001041007000c14042c0109600e0828040c4460381d1a40d130f000362462301c00c500010b00c5503407a5600c000380a1300c5400c0c1102000c407450b83c0b810b244907105682d908503621062340b407070016040181c085001c0074002c034a54050740e40204814a11340d0f135040003d00c41c404103039a41c0c0142c040c40c16041c06c295002c030181009459078a014010004090040200f00b0782e02c3d9200d1303000940144410480c24402180031422508501d0509544c0d056500c0042c440303106084004090002840031f020092440354094980c26580c1c00c50800ca80d1100001c42503a404201d400c141d1010a1803418401804c0504410143c5449403c0c09400d1420541d5030b40003917041000f40354 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 66553015 1250 66551765 66551777
    0x30a0206070f0b01080313090c08010303050a21061e0f0902090a03050a03080906070906080c03060a0b0a03020a03111614030d02160510050405030a050c070b030406090c0509060d02040e07050d03 85
    0x104021f404403005d840103214031203040001c000c8480029203190014030010b8240078010510010040c040c07a602e05000d4040b04000541701208041c100c028001070191040c012051060502c8507031540507000240c40c00b00843d006d2091610b04100007035407200404981000d00c0d00300000015030f0420071052511720039107410b4502d203004c200303103450008010329041c1003000b1b10604026450b00000c0054001d01c0403007880b952965494049803580c1c4507a0302034814050f0009104420300d40c1a8090b1030000c3e110380c0d0138006140b03003e0200c001c50050b0520304141c0b4041c10001800581c3e030003a0190480d010508ce28280401e19034850101d030861a007a002d180c508010700303402c1190a00115500300245001044a4101601c44517a40c0c06255801030600c81c0016071088008010000800100341d40851300b0341c3d920b070502d001c8010f440d1180b0101d034440d0030880041103514085444a100e91800b418084030320170f00e602000090505210590b9080c00350440120b030a4541040140040b13001740c441c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 66554265 1250 66553015 66553027
    0x11811040f0b0c120f0a08060f031903020714130903120e0106090b03060c04060c0c0803070309090c1103091003020403020414040302100203061005030916060f0e090402030a0206070f0b010803 84
    0x30f64184080c48403100f0180d4000c0040d0703407064105070281c0300310030514a8018120780d1080003168018000b41d5940d03915100c1c0604d140b260b001c12a045080c01440381d420303580361a80e541c0c0c0114032080d40c4089103a10070300f42c00c14a900c0f020343c1d074012180640a841c1c55950030310080203210880700d40201c51089651580b4003800400040d0140c1081240709900914881c82c06070505020b42c001d9000e140200a904500902804015000703a0040c00f079401c140c90351420325107405480c000480c8103031101d490a10403410f500a01400611601841e07040180d440c00c00080d00b001500c1000701801c009040d402d02010000d62120310480c01d641c0100c41e226072040c00c2909005e803800142620280e9090b00410400946840303049034001d040c00c25003001d9480351110f002490900c21703003145000e800c8851401c0050710991000102083c1d030f6490b1200c12542d42c402c014400b107000103c401a405911120707119005007031480080041e42d00a5110003c0502a80e40e1100908002c2e0f2204a2560000c110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 66555515 1250 66554265 66554287
    0xd0e07090c090f0b090307091e05011d152e0207211203020904050a1508121204060612030e091003120809031b0a060c0305011811040f0b 60
    0x500a400d64071410115409403424402c42d08000c82401001d200a601180e00541514100151406812038000901c1180002e4844001440c801d240312140740c0d0512000203180341801c6200d031034241c42006803c0b01030791200b1001078000449103d540c0c014100341c1111145481080b02034050391018002112204000b0a009260880c66084003201010b0311800700002000d03060b080820f540d0044010a0712f295854098000380500030406400900745801c0003c0400664800d5800c0c0c6a44455200c4c80d0f070720780802640d100e80350100d80042c01c50801c441864607440380c9075260f10603c079040110760700352615400081078814080450204964203c00b101500d46080705641c0710600702c5100310900c3c65a280c0656500c0c440701120103000c5a1008103044400038000c039141482c0c5084082d24107001041e00795622912100195120ba24003400c0b480154806e0280354121150704011105103880307d401c590080004800403078100c04100b000090404042d02c9043c018500d0380d60f05516043c174108 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 66556765 1250 66555515 66555521
    0x60519020f0307050a120801060903060b0316030f0203150606070b040c0f030c14030312040204020315030105011d0c03040210050f1c020306011b020112020c0f0604050a02010f1701030201080403050d0e0709 90
    0x3c540d1b080c4614640140b04071a8004001411650030210200d0036026074008a810007a6419001009030b410240100510551440b60340c4840e2083d011210500e504405182950009070b65440c0d10410401021012440030108150460f0060742842102503582c3c00088010042d54000c031448102ea0500f0032842400a2001c0b000480940141d4a0410520078a510222004000a00c503c2d80400890102461001034010907075000d0000c00c01c55071100403d500c2d012a04103011002c034a214005a884c1c0c10200580703000d294058100400b00c80441c0341a201c580144106c0302c41c010082c8224840f0b0181106404c504d5655003c0050790f0381802c5000500c111036004da038080c280a0702c100140180d82c030003003003050b41e0114180103855110020409080c010414240c00c541e10134281440103002011500d295090f100341c07200400754507540c03420f84000c1901b200101d1952101401003001d0b50054454503880391080c60704619196408204108640040a01c038040e54408402401000e0b003c1c8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 66558015 1250 66556765 66556793
    0xf0506091308030403030c050723010b01090807151b030c0b0106180e0c0403140d030e06090a0609110d03080412020f06010b0a090b0d050613020301060519020f0307050a 74
    0x600381c40c0368416912080703180d100181c0001c0802d541c585801813420b1048046c0c4050300d6000441170700c0200c440040800311605d800355625554602170b1a00708a41c0a59012004c40d43e010001c0c2070003624201e4000c981e00388600c4c604041c49440c4a401785a02000c0121202d450b100f6121003100e51701c03c1c00c180710505816081281400800c0d0000c15242d508600e0700d0341102c000c1d00001613150303201c100743c0c070003809503610060800d291000075500c290004501c000789031540c0e950401003484080030203542ca40085c0c0340341c3c5058002d0303a110000301340f240e08084021405205403a403002426404281155500e18040d00010401c0c0180130411041034103010100c001031004090110569420945482040c450b00712411000240c1c94140c40c002c4c03281800400014071015200c02c52500e030440a000225491072140024920000c0c5803000c0d442034a060310340940c0c0c0da40c207204420040c240821b080c2d00c040710540c03041c1c00c11038514000800c0140252807041001e440e446180e46003000440d5880 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 66559265 1250 66558015 66558031
    0x11d0304060e04090809040c11010903050903010506040209010f0e19030821010614070203070801020a0f0f0306030f020d111f0314010506090904030e061603020c04090b13060204090f050609 83
    0x4c440306012030400d00550340000b904641c00140d51441040030384031600d120350101815403c1c14070540500d42c1002c090310303444c401580203203c50703501e110800c8120b22a4610aa01044408800b008041c0c812891034909207005030580c610308183c00c5240036401950b40c01143d03049400200700208510000621841c20750f84412403140303504008010f003400d0703a04441d10940003404103100095580400c1440001d1400000071580c03010401c070010412500003d0040100342215603503007060303200c0d10641040340c0d08400401141c0940ba401c10600c0e0501c0c040940c0c0140d0f400088206a40e140b41205403800300078a0055681840e11030081d06540b070014501d400f01e20074900401c1951150811124020300c100c90550091b5540e19051b070345130300340341015a00803801040301d15400c0c0a2600c00034402d4042d408a0f440030a00404000543c0c0b03000300018619001a004179900036602c00c0552040c610600000d0304258071020803e00702c1b05050740c0c3d9054951184140501400c00020304c0d5049094 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 66560515 1250 66559265 66559271
    0xb1305100c0206090402090f061306020f0601080c01050702060705120a030b090f0f0603070909080307090819080c21030f06030607020a2010021f0b03120c011d0304060e04 75
    0x6640010f0098090032094501076034001801c0191541ca4450a090045004180d147c941110544039a5606040e02460340548245580400001c81c0061075504849404c00140300002030304004585d16000710100300c1e00034009100041c002202440b009000e50303100000c80d500c1d00a800301c018140c44044160b18050404030f01408000d481c10a407996002011182005180e04d481c0046482e01c5070b0b5a000d0680b140c500700043c42044403090042d03000e0319003580d80b042542d03103d848050311540520700901c4030035101c040b000300054111000d8030307400c2d10690558502c002030419440b910000e4800c99100544000100704801c00d20104803a002403003940246401c1c940410041d64890b84101702a200d01401c00d50003a4179800040000314990028000805200c22040042e40c0c4507540d803c8040340e400c070b441c52210008c0c0e082c401c0520044008000b0815950811b003031001641c046104540a1b540742e0402502a6041c100034400443d041e00c011a5598513001c401400007580c06099407203a81 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 66561765 1250 66560515 66560537
    0x120b061302070b130305130b0d140115210c0c050f0705010503150301020d090501050720030d020c070902030108030a020d02060105010c140703140c010206060d020904080a0203040b130510 82
    0x26000320f95000304155010a49040d041c1000d03103040c043c1c0a18a00c030307a4200980400c2c1c2c0c07142c010252004070141c05007400b00c0e101c060040700d8260401d0290380940391900c0c03400740c8550700c01c4003030709880c58201c0c0d00034031000d14070b414000c2136445090213000410440b41d542420030030204940c08030b0000c200058032a00e810440005c00520018084024003900b01840070341d503036030a40c129520346005003010881c8416900e40a07000e0b010469074280810a50b00b01411000034240200009031200c03c007071480c003040a060344000350004401d000d000d00c2010008500360840b071000710b0103411107800a51312814244e400030300d400204c1e1402403c64200c04c00410690340c010381200c62407540140000011035000c0c503460300d014038607400540300e0407405c010640c1e003100c04102d402005001381e090790403594401c401e00034091003800009401001840004021800c241c001e4400025684140c03807806a890a030002e142e001034a02c1c2403400c205030010003507131400282c030240701c80c42070600d000524 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 66563015 1250 66561765 66561773
    0x152d01020c03160b0328050402010e090108030d020d0b030d180603060503060103140a0c14040f0209090402011b050d080708060909071413020c0105040c170303061504120b06130207 79
    0x581e52050161307101c008800715404078010301c3c040c0c0c04129028001038200344030482110180000b910241e010a0384120706880e141015950310341030754440c2d0025440c045004403200002c0d4000c42c00b5004e81650754000020b150741c14004070a1265155940c0c181000c941445c10a91a18035400360040c5440d00e9410482d9850104503141102d400031030f80325459000801c0301d0b080000742100141450b070160004669200140b45c22003100a05407010414044009005403c83c4142169a40d111650800060045d0701c280710540d526440c540742030a03040b241d80d40305407424110030906004904c083c0c0800c0305040d0301c030818640c008001c489085c1c460800c0007041ea26040f003809061011030450074504081d44840101003d8064800c04c21550f60f6071001100d070080000341d9080b50401410000083c0e02201e503200e45010005071b00c091403860721140100804001c0c40c0c0004108500c0a10002030f2038242c007010301000900581001c5242d140c00020000b001e00032030076041e060741c03062000ca0042 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 66564265 1250 66563015 66563053
    0x203070c0509040c0b0a0c14120d09050c120604020103140103031e110a11030606190b030604110d050402010206010b03100905100504181b0509152d01020c03 69
    0x128000c0c0e40200c8203448500700300302e013036026070440300700f41e54000303580b001c00f6601c6102400c0b51070240c03490032103c21740c0111540d10740800001d604d460250600070500d003450160701200c140c0740f01d60b04641030410781e0400700f50f41c0c120298006103039411043c100029560107000e0403040240447d0741c001c00398150703503000c1c0070110f440c0d2245070386009151403035501c42d01424030401980846000c1718810301d51880d10b06480404030000c03500074085c101c007041440c1400c0b40c44082d461140828031000703d060802c7c004413600010609503110351100a03a0a000305100b00504034200f21500100301860180000f902d8000103a000513a8290f00700304018a036103881c0030b0b44043d5580701c2c00c0801c4944505912102d01c40060308240d502a01d00220407087d00100601250340520500c00801c100b211200b402c0c01d04030300351082c103810241d144001204000380c1c3c00321049141000303041c4066500030724030700071020b020400454500030642c1049035081d030b01009080503428048005000c0f542d0310f241a140c0d2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 66565515 1250 66564265 66564269
    0x906010f0b090109170f071814070e0112060905010306060e0f01050603070e0103091202010207050f01020405030a06050a090b1906140f0f0109171b040b031c050f280203070c 76
    0x10b00340c01c505d040d03500f1100c00d0014103013490001084803070090303c0d540c0017001d11050f5100311030260b16021440409407400c15581d4400e4119488070202600c0a40064407076808001304100c4c80350381c5d050046000e034500d00c02d050103940503101c001101420b042c2d10380c00ba414060000010515140010030450b601d000490380d003c81c07586070401120003800c006801808400340010081409400c036038000540c150701030050103005404848900603030b844010700300c1c1700e24003c02c1d40507041740d403180010070384942045c3e800c900f0710200090005d05035242c3c06002a0309644035180c1c0c0c1000d0081d18100c802c10b0007904068005001100819040400025010480c01884c540201c800c0949400c00f0f03030090b580380c0c0042a100c51a00c2c07240c0003c1000c1c0b91200506201900c4019141d031042e04035040520800200b008040d0041100c82c0c602400da08001c1840e840403003c120003007120240780d1100c04090044101e0031090001c02d1811003d51901d444040d00c0103408550062000c4404601c5407051070341 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 66566765 1250 66565515 66565529
    0xa0b0103021c02060711030106170d03110d090302070302010e0319020d06020702060a1101052805100b210f090303041104110307020f0c010306081f060504050906010f0b090109 77
    0x1941e400c000140000b405010001950155000c52603000b44800c42c509107034058030032402080f0312511031f0040030854440c025550600d42c0018160000760313000b54403250f18903440041c140d007008140b0b65a5800e0301d122540c100d006802001c7d08004650b04180d003000c10910460142c080803600c15910490440840e40180c400c01c0e00c405490184000ba60444003042d4000d00309075a910300300c4030090030100e28a1641c031034540c03038080080e40300c00071b500802d0201c074100480820b04039949074000c00170700f0018014124058440200081c0500001d008000651280c200c1d03030100d001c0c5107680842c1c0f880041c0b400c1200b146107010402c4140021040340c0c0e2269008410181c2c41032223001080040c000040007500481d000424404490380005c0c2c138021454581c0112160386e81d0200046041ea51540314064813540682603200102c1f0402808000f1000c0070200059416580c000003801d80b601034504408907009030005200d002014400400070700200b5a083d490316900d0780000300310311460300c00e40e4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 66568015 1250 66566765 66566779
    0x50d0f1b120e21130e0103170702010e040b01020106080706090303031b020d05070318090906051f150507020303030c04050909010c0807030b060c010609020c010b0405040c0608100e010f03030e01020a0b010302 91
    0x414001e401105942c820020071021442442d221014111a44404e00080d07035a00c07114500c090008c44180222a206d0f68182e41e00484000e5250902c40a040c0b202e0442e4155500c0d020b011600078420032a0500400d01c80e620b0140c1d8a2640c06d02030200c8081842c00350090300b20314800314606400040c50444034840307141c00d036900c07079960408440081100e00440199901d2405c00140e40356103800500b640c5000d07450030451521a21580b241b03890943ca00c1c41d40c6a00c03440e10030000321303e40f003085002d80714190400e94a00046580000e040d03500071a10b40c1403090021409000505207a00815072120185000300000d01d0601c00251201c50014030200805071210a138001d29100e00742540d450315046002408965150000e0034007070b411a13429526158038100362086c6038500b9000c7c56000307c2e0410000000c841c1001001c588081c001480c2d07401a0409080c00240c080c2140c0c20382d0b00924100b0f50803040e0900350328004103000440c2c45104d0456000f41000401300c0c030340b60103240c1140d6048402c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 66569265 1250 66568015 66568063
    0x2606090112031106040305270906040c02101508120309031c0e0a0501050103030e0109030c030210020123040b1003110d06061505040504050907080607050d0f1b120e 72
    0x3280d0f480300c800d058004500564090008150304030029185050030014260201c01e850050312651892900703050394080c00c10408641b15080a50000e50000c9162060760300d030200090001040c0c0d049071422400b4086008802c002d100c0d001e12444030a11548030800e4030307504182e03c0151780d9014515501c000016804444444083d40d94420401540380d00141d810320106030a2a600a00702440140d000c50807005818001c0d61241070410145c0303901100000c10541183c091216115103019a802990750b10350003546182c0c424042080d030b00707035901088181403401c0d141c024018003000c1d12150b254885207905200258030340e4406107451805503812403842e860f0b818100c0152500d41e0000e0000c0c05400000205550701200410540c1c1064805004603212101030694034030342c41c8141145a000b07100820380c0180305e00020f11510081102c007043c0c48090b110b0800c1201c010940ba1068651040d0001c00d80c0303600403811a4041480d441c00300192010301130102c0d00e500b9200f403404555001c41c6a6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 66570515 1250 66569265 66569267
    0x20301150f0c0209040f060b0303030c04030b0a0213030b0907080c1f0216060504061b0305070206031308120a0c0f2a050102040608061302090a06050c0f0d260609011203 74
    0x10107440c840d0001d058904c0741c281307420200b178404082c80c01691918105180c0b010b550400104682c002e105004600c3c3c0f425140d92214070220402a024880b96a001c0000c82c00203542c10746c00c0005503000d00540f60680c108107040d0307072810215521198176600802005100f9603a507180b03604072003042c1d0180c154841c0150604a0074041070340c611a00d1a01b014a0200340b13039038004054401d8407131035185c61481d003a0003411070b0011456090700800103a41003050340c0041c10a81c014640045035002815130312800c0c1d80c0d0f43ca0384e642103025202e00300c0610000b00141d00c0e070580103003100030b8610f08003050702c084228002031140e540035100030300c1d840b044900300000628800c490070441c0e8020f0000c54881e074441c0c0005210050980b01d030381c46103000350303515006c3c00114400c40d12020001030400b0201450141c09488a40020044806502540c004440c10303080a010031188c0c1310140e901e2100c0f4200000b00e4041c2c0c48040e006c8c0d000e44100c000104000d80e102c82035598151890340b08001c0c0b8114092074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 66571765 1250 66570515 66570527
    0x30604020d0b030f0102190e031209060f07050a020108010605071709030307150b030607050a0512040204020c010c0206040c080d08010e04080c0d05030f0f070503070c021c110f0301020301150f 84
    0x502ca030741502ca110300340c12482c88198060007400c060000c40100040083d041101c003000c01004480e41a0440c031042e0b00e4102e00b58005000d0500c000d0b042c4c504004502204900e550800d045c00e0340c03150802040c0504541c0d0000e0b00ca03001d8409070802d181800c034103464006860084050384036892000040d005c200741e80400540701401d9004900d031004114114500300130384550901d4038001d105040103c0c0300c550080c001e8807003090746503543c00d0070300c000040340c03445540c0007910681c1c10a43c2080a0300034114203008029001145400421990038103280c10b02c7c2006069104411640044d031400c80082e5011010781d04513084c1783c101c07031029156400c1030f681a118240e410107803403107400303512401d50342c00038003840c0314644084c1c4070380b03890b6100490401500000c4509400046042001815003401500c0603005140041c1044914992006002c02e803c08008015910803003c1c3c17280702c529113480c01d08244020015002541075524040480c1005101e128544c0140543c0c0b03001a100c09100746 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 66573015 1250 66571765 66571781
    0xb040914070507110a090612021201050c250b040501020c2a06030a11030103030804031106010e04080a1101020c03090415050a170109060f0207062a0f09090e010605090912030604020d 80
    0x4004207c81640c442007034060060042c003c034002c1c089001c10202c0a00c0610607140320b010303400045480c05081e09040c101d6140010a51011610607440260101c0c0b40f50a03003e104a00c52400160344100b40d00d122403030600712102940501d161448942e06160740d140b42c11000c071806580d40d5031607807102d100c0b000107420842502a0306041c040300001c10306500006150140d80607842e24200401c171011b155480d04003d0266090440500010400084500004007144040b03468000381151030300001c02d099a02492070028254030115000c1ea0a2400f841765985181402031030103601440c0c5000b00d022008284510001100040b40c41c005102003034001640c250340c0461300708a09009480424000c1d009070f2401c1d18518501040e5442200c04290080d900501d0b0400c00c90702040098812110b80c100c46c5214010048681400101e07010b05e03009074042c0822800000c9a900e04120034400000c400414000042c0d000c90100910032500704120394212100390340159441700101300610240c9641 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 66574265 1250 66573015 66573029
    0x21011030c0d05091302070803040201050a02100f0519060305120f0d0c02030703201e1006170d08010b0901030c05040b0d0501080618060a090c0305070b040914070507110a 75
    0x46224001800c0d40a401429000802c175010450095030305000c2d002c90099100080c02100e042010038090740c0140c02506468442c0d02c120b404203000b000c02081550f055070404400545ca038014031056481003d074540c0c00810584040000e18910707100c2da540e50742c10518060380d03580006200800c0c10b51141c201e4810300381d80b9006000c05405030b4402503599004160540c0001c0d5511021105c0f240e002541080d580c5410303009001d04103400b580e0000400f2013405081003841500381c41c41c0aa00f282c01041c00074410108006050802c00c6190f90400268550181c208500c1500500400000000303440c140c0f04280b900052040302440f0503142ca12440d0800d0014810200d4028001c0c1c0c229003001d41070f1001c00d010b8480b552541814445000301c4140d0045041c1c0094001a6207420f00740d010b402130501440c2da800000d581c0352925800d26045401c0300541d1400001c003809250704034056210f9906c0760340b02d040d00c6440e00803001000c0c0d00803800c0081101c044a030007000183e51b0610640098010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 66575515 1250 66574265 66574273
    0x30f0c0e150112060b122e03050d0504060206010e0702150a09030f0e1318020612070806010207150c0501060509071d0d0b040f0f06090605010501080f04021011030c 72
    0x100c012500d020421001078180001c104811142c40395186000714005c5400c1a00b10500b41aa03c4030900d0543c84020302c0d40c0c0c2003448801480c00d48000354100b800c020441605030f80e2100d415804c0042c107040c03540c01c0c80410b00808001c00c00c030aa50028000e130442c0c04860000e2115152510120704100010321003000401c501d500b48480e002041d0f004460442c40303604d4981e483c44220308141c40540007425000d91016010400030080e01e04d5801200c1111041032084c28680451f6000945607045402152a40c182d9a81008080c0d170304498241d8004c04d00b4002400e950b86000c0780e0500124010300307501c080141d140124000c02500350800c6001d0640100385036564a00303541c00610026844524102205c7c5000081c0d940c1c0c1480e203010403145400c0b550001c5590b4031074441c0829000f088504070b90b0401e0002c00381c0b01069051044640080c852003000c1031079490480018074028015002540c5107080f01d0522005a0307421405191030446414203040700f00100b004242180a072800304102402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 66576765 1250 66575515 66575521
    0x50a121e030905031c0509060a0c05070305160e0603031801030b1f030f060503070623070308040606060e21070b04031a090703030906231902060106110601030f0c0e 72
    0x90446400c0b400d42d14194111800c80d6050195070707600e5542184401c0216404008400307060a06074020818404a810442030715407460b03a4240c44d002031a40b0a0783c05402440c0f8010807000984000d030700410014480c0429401c3c00c4001075103d01c12040500344144030000300000ea42d00075048000d1305a0000d01f902110103800d110f1400c005020340b900c5000910b01824103560b80b24038802e900941d100500104403242c10050140e82003010400c00386507210360328548042a42d0008014000d1901c6941c50200ca8101403514009581c0650001070a12507001040c0001d900d03503a17000c0c41000c01410310f0320a4110071108035810110141c0260000880c0010b0100c2401300e81c406015034400200c002c52900d035190202180c03901000e00004000507250f01c400c02145201d070b060030002e4600d610045000c9081043c40d8801c6600091480828000b01c5500c0100503805003d864014031107030625014080721120b0460b111601400010301d0380c01400609030510100d14200d5000e040c03902c4040003981 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 66578015 1250 66576765 66576767
    0x30c0503030a06031b0320010203130603020405010f0503040b1302120708010209030c0306040201050f030c0d09030e03060c0a0e090c0f0c03220510120e100204140406050a121e03 78
    0x10000f4001624850282100000e503c1d041004550407247c105858001135141c48840c801c88080c04140c05045100500c02c101807101c080240c2d4000b8022070b1401a900c038903010024085030031140c03403241030040c24810407000c06c5500f000c1b503500550701d101c910710a140742d1000a5002911051802592003026000710327500c02c0c150300130280f010044007141c00d10040c1d0b0040590b54007003220004e0004909001f40c00b0241d5004001e10713003085038151110b007010109280c42c4100c0b01640380c1980043c0d00303c052004241418460581c00403d4a41154130303107114100050300c104c2c1120003007802150340c1000030b801c080300c510582e5042d16440400680c1c50103e070020684c0c035000408421211850b041306508509588020442161400703807800e0000030743c86030180e4503c810610302454807903c90b140340040d42c07010300202e01070094491005032a2820030030f02c042e05503241d14206010300d181c8402400142e0b00d41684904880d0041a0300c2c400d240c5514004c2c81440d070b4803d0340861440354044500c201 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 66579265 1250 66578015 66578021
    0x6060902123402010f1418062203020a0203060c0702090106020303060108040602180910060210020309150601120603080d0c08100603050907050d0803061504030c0b07030c0503030a 79
    0x80300781d1129a945404040489034200c4910a07180216080c80704010140403000c02c208032140303800002200d18040e8401010f90f01080010443c56507200c0401150010203000b148403042124003c241619021901e091aa0380703910800025000345516082018802c10203034145c10b0f40a8103a034550705001d04c00711819045804220301c5003200400201c1d41c94400801e413407240b00140d403640e149403074a445140081d4099010109a40800f2940041d90b40b66010760f00c0c007800c089840c3d100642c1c07501a0007400c0201141d009802d8034010400d000042500085a6180751480c5581500b41d8454400680b065003d1317640c0ea520090601e035001050242c80e01c064261290004010301c1904603150080700c440c1022034680546282201c81401070130720035800254810b40710021100120384800008080381128035046444020000400c4035900702401102c1069619a18160815081d0340d1000d180e45c40d18040c18442400c0461000c082c5440380d01c030400950f07000390503241c0e00d00702115140d010b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 66580515 1250 66579265 66579277
    0x51209030f01020c0303061005210c09031f0e0a020a03080c0114040f0b10030f170c0f0601051905030d030c0203091206070e0616060b0d06050906010e090d0f030e01060306060902 78
    0x81102042c130030803071460040740ac9441d10f042c086030f10a00c0c40386a00640e212002e0143c070300c181c0c40000303000d2007803d518208982c4034a56103e0601082d14034a8050000170b5821072440c800c8a034110003505401a203038011103c0640b43d05c0305840d40c452061504280c0141927803481020704d01000800d010a0102c0500c0d4014841e004817500b041c1e640d9400302d0310700b211804c0d20005040144002004010075101c0207040104c140800c25136103440544001a40740c0080207114041c0341d01b2020040015261800b80b48400c04404003039600300e03529240c0000d0722103101104031000e05031200c4407020f1092003031045607034079080100001c8004c0b4805006a940303010407038481d408207204000050040c075040040da03480840c22a10902034003e0b95640001500388583d0441d0403103106184040003807901d014051090660354020401980b50072110007003400054098442134202c1c1e0381e00f40c0b040754404081380300040d20382008991110515465401011141e02c0645420f2402c04041904170194004041d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 66581765 1250 66580515 66580519
    0x1060804050f030a0e120a05070f0e01120f0b090f070e010602010507090b220504050f040b0c030c090411070c060509010e0139050d0305010e070c051209030f01020c030306 75
    0x2402c1510600c0b030640e07a100f0781d0035180204444071090ba420789002e600500c0262010801d40307c280004c1d95030b4a103048259007142055000c440780500c1507100248800b80100900c0313224420369452a2201130500e0b01c05100500403545100c001040c61004214409540742000216514565100c2020b040340000307000d078070019401c0c040030940340c0b03100c0e840c1c880c00c5d02d082000302c41c0341102800b000b443c804482e400c030f8951550441d01c000b40c5540c8600ca40c0b48904259107100300d1500c1e1520f0030407440c0030001c002a032110b005000f84204184c68805581e0910010743c0c0001c0c00c445001c1c910f00749400384890041400180e40d10101e2515400406821910801e890307048041d403145005454105900c00108180c00c00500002c0c05886000c4940313a41c01403c1c854451074800c289c543c903051408030707a120404662500e00400502410f0500d003035002e80507107088501003496035152500c4111003101c0200f90040421081c8560b5401d1000100109000c0001c5656540135041c158403074000b200d04038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 66583015 1250 66581765 66581773
    0xf0305011b0206061f110f0304060f17010909020a050910060e03030c03120c160501020415030209131d030705060108060105040207051207060207061406090105040e03070b0a02120106080405 83
    0x30007000d00016000e4080c42009125006610003c0e41050041901c059800c0800c0b480c1d0321400d04440c0c0500092440c1e20310340018641d00c90030f01001030032403034841c1b81c043e04010451195001c00c40060140906603280044042199000c1d800050b00c2004d0700d420260f40003030500140100100d450004404496058541e50f202204d200201500c0b0f016995240c0c003150001c0080b603412104800c141c581c0714540034481ca00380515510343c48000d001d500b01c21511a0f600150620401031401d9000000d51003500d829071a0500200c041082013180e0080626000e41300d4010071300400845100450111401040326102e641504000e03555900a00c0b9840c020701540002044a0429008032203860b50468010210928400444010b50b8085802640d2950713090003c800001c805014034220361000c0c110070f0b03046052103000c2200b22072041e1321041c0b249281c8844207224000120130f49a60940040e421066039540c501030001920031400c1c000041d5814400126015402c0303000c6034025030240c4112 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 66584265 1250 66583015 66583061
    0x81b0d020c0d0201080402030703120504081002040b0d0203070909230a0e0706200d0e03010c020d02060105041e06060801030312060f0b0319060e01091109090a05060a0f030501 77
    0x590700d81c0c0904036a1a000308024144a015500410700560401d10240490b5100c50b40d0f51a042081e0074600500f200003440010200718000c0100110141c140406204610707203032400d17540b85003900c58031020b50100354000c400225221702032140d810082464540c2030102c401900c100480c1488003a001d24005004480459844542072080b82580000360340148955410b1250a0314045401c0c40c4d6001c841e0b40900403491062424030084021758800e44411105108500805081d90b590003948821503121488486d511580010707042d04403042a500020b11603002d181e140d90000808a80000b114241000019019130120585048902a5981c190011040c04180c015141188101e0404465618043c080808070000071604001c613200d0488440903007000030350540b03550345d1016200e140c90200400c0013042d1802007201000318440c84514040f440b900040c0035440251441c00700a40e00c43c0002c0080d120309a1240c0501429a2120340c22907407031800d14040c00426480010340d1800c1084 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 66585515 1250 66584265 66584267
    0x50a06020c131e020703121107020102100c141605060f0c0304030e010e130b100201150902071406090601060e12031b010f0c080109050912030c0a0c081b0d 68
    0x21000304241c00900c403810100040c0044800391000001503200702c0c4400f80c038500c105032903100810006200340c03102e00040a07a006030302c080340c001041d4000e600c101042401c0060ba0301081c10605d201c10260001340c0100d04000464503c000125071072119040040c00541c1421207000c82d1614034801c8088468954a0300c07400043c2160995010100712400d1020a00090040709041c0c0304a8042c5415110150340d0300004101d8408074400d103200c83e03610718150b0300070f060402d81c0c5c100020090000384042000f0392315101c1b4902042c0301d4152041d501045d9402040300c80420b00d001580360408690007410008111a15450284941004902c103564a980e0078281000ba80c030301450300801075824039a03040c031054901d0000407100f000c03555030303032a102d01c00100601c580b209a0015030b03111403056050000079070031200c0c0a09442030550000003814402d1034000304480c0c0c444d4045250584408a51009551001d208100101746680c08640e0340740307210f4407071555140c410804c0d003103800c201c0c610f042c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 66586765 1250 66585515 66585523
    0x1e050406180905010b0a1401030b04020306060405011d060c1c0309020904020d0c05060a020109020102011503020d030f02030f180f0a05011202070f0c12030801090c050307080a0209040f06050a0602 86
    0x41501c640c0d44900c1c659406020301a03010744200d80c0540004503009118400080f03500c04203410450f01c0710203030741d003880c000d503414401d240c3d55030001d031021459420084000346990040b4411281002107480e04082c2c6203222810a1342e08034800f4100c591a02c3c2c43c11850b40d100c42d115421071140703e01060744085d541e4441d02445848507005000b1410980752034080c0494ad03442a602942c1540614500290b540ca07080e00030080c2c20980e60001824501a10009003990700c043c0410140340c010f0402440503a071008600c031010b6506d0b081821000368110000da0943c01002e0548440460101d0890041a113841c62200c0c82002101e4030203101121404200d550501c90140ba0b00140d0481140d154039101c40d03004103012401400101c3c020041303591405510030254018145590310202c02c0000c254001c1e54041c0074049220f81444802002d050060540c00b00038149020011440041150b0144903412034a00d81c00150040c80341e1034801d040c100c040c040910a07107018600f04140003400e144081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 66588015 1250 66586765 66586769
    0x30c0304200603010e07110d0203040501020c0a050303030106031d160f050904050606210106030602130b0301060e0f010c0b16020d090f09110405091306060905010e0a09110303041e050406 82
    0x2d210500b10303420300c4050a00c031070000b0801024001000801c00402030200150134803a030782d66000303641e501d080c500028140b400d00030105024031310018092080343c0d80801030724156551413800142412010700b00e401242d00c403007003650741809211180510303000c1eaa4510000d0381c041040e00051250765109202148008403400750085d040040400c00b24941094049010301550b6000791010802c803140a00716502c552045507030550004241c0e44100d4501084401440429040c50075585010405425140c02d6000035200300506a500f4241d43e001d46a02d501c2260005071890041c6010284061503403c0b02120300003620807000b100100340c0c03280c580360003503e5001d481150030a250840342006080d01100200403400244804552501d030315041500c11000f840c0300300c030b80024034200380c0c080f1441b54005008440c03c010060004040650782e01d6008910040c0015030100b440c00c040c041541d1240c56680c0c107000002d000601c0b491902c480215122084031000075843d40c4404000031505ca074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 66589265 1250 66588015 66588019
    0x40b06060304052d0709050a0608030f0d0b0103110c0105060f060306030a081c1514040504030e090a0617030901080a140619050a06030e0d030501060806060c030f030c030420 76
    0x80c1e180c3d2481e1041484c15980c1c00c0325101800300c04580f0040440d040078242e070800c541295035241000348555030790240500030321070351025610b0040c81d038404e004070b4400e0081480302644c554000c21120391207940804141042242c20b25114040711102e20f028110584d4042d22071140c40d01b0400305031403e04102ca0003482e004000b416000c2190303a81121580021015800e80c07403420a00e40703e82c800038044d401a03070060713a5440015a0526030441a09402400958025403401041100007500101c0c000e0b00e9a0302190390382c009558520401e4043c1085030401600001304668800e03502c4400005040680c1d800d899002d00365a459213494200c2c0c01c0e0114082680501d05e01080c105c0c208100d007154640f5070a0341040c0c119803101c0103d5003901303c03603002400080c1d443c2211514032005000e9984c0c007a1651600344003651410300020034844000d00860b11901c0001082042414104100c0c5d904003d04c0c011681c40307251440240b0f0064104031410344040180e10740991100c1c81070744034500341c4080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 66590515 1250 66589265 66589273
    0x21309020f1f030903020a06140f010b0403050303060108150d110a050909030a0c0309030c0e07110f0c040c03271b03080711010905091008010f0c021002090f0604030506040b0606030405 81
    0x8003100031005001c13183c0c4268250b000312001c50011582c1405410858044840880914103005880c8443c0800590001c0741c1100f05100c00d100061000c0204d0340c00800900c0c00c450551901101009400103401480341e0207252605c481c0200003042181200c00802190003c5040765038506000c0b058408940031412070f08100800704110b402595a586014028a441e010b910b84030f0b03840d5130311008030f50400c8408040c00402c00c020142d202c0781c18203007805010302502441d40070a040a1750340a03640c030701754401c1d80c031040c03040c005070f200340c1c42001e24400881003100e194400a0200c00000354042c800d482140d400d110200c00102d074105c001c03045035400781e2501d20700845ca4030340c980088a80076000d8104140e810001800d50b44485005000b01c0e00c48128419203403800102074215400074192070019800c145084d0055a000b04145940c9081c801005da50b48140e1400100c11a2441d260190700000220b004810f100000071070a1045102c0d041c50600380d112001080f805010440c1c0040140e80 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 66591765 1250 66590515 66590569
    0x512100b0f030307321f020703020606090a1b030501051f09090f06030206030903030907061e080901021e1e040b0301120204110f091f080121021309020f 67
    0x7044d80d480f048407076035101840366001c0f038107005d03014821001440c40903501440510810006100d030b404420382c014401107281101c035503406500c400d40285102e110b011200000b94040c5103d81000310b0400040d070302c8003040152590090000c02d403c3c010030b801404d08800e200140031805e80d0117401d0308915100e0302d800c1c91800c480c180151480800411099440e04030000c0140c803a00c0207140101ba4080c0503689a00d0400e00c0d041c07820300603901c640c007005194110b00c0c17011003080188018400c25841d02150380d9a401a41c940644903031000158021040b481a884070810b020150584481c4800450842c074010800000d080c040e5015400580f40e00f000100481030403254690090b41c4060b001286880507001c40c03c00da6000883d0a0290510025000560f40b038074a43c00c15018102c9a091400c481b0700080040c84490705008900729010021648200f14100c08a02c0300c44c103074020320b010501203a01415001803e0445000c0303001c0d00d0020070121041c503021015403020301f040302003500e841c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 66593015 1250 66591765 66591773
    0xf0403020a0209010f0512011a060702030c100c020109061e030902120601030c14010813141603030f03050c190f091208070b1303020604110a0512100b0f030307 70
    0x1510440a40c070a8940d464016154004840d00030540030580e0600742e072411081c44050402c0000359100d23a450075815400004060207041020801075500e03940b511410b102291a0465015078a94070080d030700f030f91104076503001c501c45200c58804c0e0380c1e0748000d035a0744409079a0300c03450511100006588400b0301d03038038600c260302c450794003030000f401c1804207005410520304280f020b820075580148150401d1055030303c441c1507062220300a1070f181c601e40c03424900031a150040031400602c48914604120f510f40820030250842c3d0b0000a460240c090b920b01d400b80094011140410100c0e04040c0014600110a820341d904042041e402d071400741c5210300204c403d05040e48035281413080c0a4004039002c00a41c0c10800c0b11840b82401c103070394a800f81014101c800000b00003120390b0307c0c40070071400000c2c1c2c04200f4179007081d40700004007041d024101c005145446541c00440c0c014405200c4924400000600d00a000d0803024007041150b45100510a0780b02030000e503103425901c01c00040c0001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 66594265 1250 66593015 66593041
    0x1701061704080f03070c03021b031f02090306010b120114010c03030507020304091a09010b0a05070807050102040b0d0203040605060306010506070b0603010603050d02060910061d0403020c0604061107080d08 90
    0x144100c2c4228602900988a148582c0017940c0e00300025034164107982c1055010001408001c6003400d8814226000500090341d0b0307400e000b054680c0c1d580d207882c50000b1030001e4058401041c001800c1d9034040d07858640a03481c5402c4040d00380e0039041d07104000580c03040141101030f501d80b810fa480e06101c83c090b48095010703100c040e01800440c8420000010f03000790600c0341e454251401200b5111549606003005410041038203e150b0284c010442018426000421501b5140e0b004c082552603c079141845402030289901c68214003900141d4610f5004440d4003c501c1148aa842042152119014981e4441090107010b40141c0204000000700788005101a80500001d0000c1450794481d0380340c2c0d041018070081040940c1c845030074880209400d018603221150900c1007045854075041e1b061580141440c0c400448400000125040c5882808040074400b0060810b5070f45035518140108501c240030b80100060081603030105d20224041030f0000000c8450359402123940301d2076422444 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 66595515 1250 66594265 66594271
    0x8040c240305070e1f02100c08070c08070204020d0b0301050a110307111f05040c0905040206090f0103021201030b010f0e06032e0c090501030c0e0306240301060e040317010617 77
    0x344034a8007440607890362458949013000d400d17440c00404840e06a04083c2c80c000f06001c50350401401d003680002d43d10707803103d1950f178841b58615282c101c06a20341030000c01c6214426000c0c0d006030001074883d5510005402441d40c041c030070b800803c2690fa0703090103601220300300045650003243c1040480d03034152007081c000c0c0321501d02e402a44e9210011900c1c8040c038504801c56184103c1d15401040305000080d50123030018144110140640d14059001414612800306503a00c1045c1d40030228071180d200b40d040d202003004110110300e0f217507140d0808034140007091207440c04000502c00003046201c0849441c0f03005900c041c004124521100c0d00c15844852080c000c60180402011040c2c064521030060701c0c1c1030f003101d0311030345242c0341000e000409403003a001c00c10b414000c5030781c180901514000784a0354090480c80c10b00030b080c0b51080358081100705000790198550f0800300e002c940051103031000b42c0a10b209454020080c60f00304034032544510248070390070203d10202516030704040074071109a8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 66596765 1250 66595515 66595517
    0x70c06080f010939081008150406060803130311030c060403020409020402070f060203150a03050a110103020c030409060519030203060a050402060702060301060c03140322061b08040c24030507 84
    0x1414440181c1c3d40f5691448030504134002d501080c640742582c1e422080b030350340100101e43c4102440d0701308a07802c1c0c0e5410640902c040d07085034410000b814440c05500c840c003e000c24000b6244e42c2c140340000100d1196560000380d40741c80680e95250010700d800a41140d5030f10000d0030300c6007003920395001c201c000c2c5662101660007940030001c030400540110b00305803005110300d00c016240e08000c002111096410b0900314011055a2020700c049100010424070703803a4051a092103407a80c51004038043d00a141400501e03220108010811004542280c02a1203080d214400d20200c0040142c203000e505210194042d0046004121001231039044958042d0002d0002890028254042500c6501c240d0050300080c0b4070309810020964000003107041d1080808a0714118281034400e0800392040c0e0720403501440002c80003c04002c800d802186460801071115003c1c0b0744a0701001c0c0281c003080b10300300c40100340407134003055030007083d40102d4401c0d4643c5510021803840c5007040d0020f007009030800d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 66598015 1250 66596765 66596801
    0x108120c0f01020417150403050306060904060e01090614060a050a1101060308070807051009200d02060705070e0702030f0304120e030f01020409180506040b0403050f03070203070c06080f0109 84
    0x78200380000d0004000424010f100705842d41d910500a030f08091010103000f080001310010700c00401c5e4440c007a43e0300004200c54695a480940d000903004181c613620000c008a482400060720641c103a00620483c1ca44212001242d480001086910b210301100c2801089003070044e580d00510524030f000c4158100c0f0000101e03180c403038951441541200b08221034014000600e40d0070030034144004041c0c202c1341d000030f0002d00ca0b5561030b40072068610240400c00710030b80e046188241d4031524015051900074200550f104240d0820b10f8031190b86001c1d03010380000c0034001c1401e03107100104940c0d00d9490881103d00b1510386a45400e1305400000c803c0d410002d10907002d40803650140300020340a10038600069803245482d042d00e081d1000c1204000d44078145001e4100412404200b041d4043e41c40244a0f0aa80e114541941d0f00c1c012107101082c10500401000000f0f5000002041441d00503c03940301025a42c510450345113a048405000030b0250100400861a42e5080381c04c06a060400d48 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 66599265 1250 66598015 66598033
    0x201020a031505060403081b03040906030c060c170c07050d060c030b0a060c030509060d020d06140609180a0207150b0a05040903020c0f01030e01020f04090501050a0303080c0d0617060a140108120c 86
    0x1072749903401940007490702950f2042c04008003d104070400004001c00e0801009a45103070b294a035600e5140d900d90a24000005028030010b40144484030140c800140600080c0032541132540051142e02005004a807600100c0c406d41d25040d90b00d00202c03811b50340c40d440205020394044445800019020760030000c2881703001e0310050640082c22a8040300c0500184480c0343c064014510071001895030b020308020456100c0d00e48a041e480500f082b22241c694100e915518034101c003c1c450b01c5c83c0503080c00c01c00440031040300800d401c420483c20041781c4122880c0d44943c1040116485000300401603446810103400b58102002941001d1030141000a00380106c6601142640d000e143d0010302e10600103400d1250342d02510541b4050002510424681030440e903000d05185000b82c811110f00c1c0340400c4141100c40e003a04040041c1c410311021509220315000c809a440c0d0080c2c1d41c0344030460901c28210040d04c0b15101da01d0403039110000914454003518214401d41d807041d0418641c83c040e40f440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 66600515 1250 66599265 66599317
    0xa141603090c121506140f060315040905150603150403030c090b0d0b0a140603012304060e060102010e0604030212070804080d0908150609010303030b06090301050103030201020a03150506040308 85
    0x1440b080240548040d0804c10b084140140c00c40d801600850b0207109160b044101944503141c0310300a20790180c4072107560392105540302d10f4484400790341d00c0c0c1c1700342089009800c008021900c00b03c4240d140f8072108031a0ac03480b0400d5120450740745c45c12202c0c2c074160002404a8800e030006012004942001d50003940c441c26089910f600104004081c1038595003c6820b50030300c00ba42c0801010071240c2441080032540000d41d8621062141d0070001c2c403042e00510f0401c041503401711640034010420804242c0c0e0b1190442c000e0011501207000d5403078a00c3c1c440c140031000c2015807046034140d0103041401d520b600381078001d0704401010340e00c2240030301c00401e081904228502403403000d074861032415480c16104515040840d03900600004400d0284003080c0c81d1300b41518107481c1c2c103080200c1c0d0144070601140c918013904c580d16505600703043c0000103054040d80109540314085d5020b00c00100e44841c20841040a80308240c0c0041d4100400c00100b203001c00905104006108441c40b00300413401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 66601765 1250 66600515 66600539
    0x7030902040f02031006020303090304032607050a06060e04150f0e03032401020703030f050d020c06040b0a110a02030909040303020909010e012301020303070f02011b080a141603090c 80
    0x28841a10b0380d80041031059120304005008014982880118914a0042c1c506a01c0307000d01d01c001030800805a804c003440c90b40c00e038440151a045074543c1c5480740d04c1400c05a903a07140221054038050700d003d101050403080d00d13442602c1941c00400080320482ca240d400001490b50858540038999681481d0a50010a00040d406181d0845050425400010251082c2e61080d1070f0745056500c1241c00b000000d030814001c0c204a44181800c5440380c800481c000d020303224403c0213110600400c420042002140c3c50390034041d0040300010055101d68120b00712080c8100350054001da4001e00110b2080c0c68540e40326503002e07100e8900542007031070030b502090910f0070a0b0030840c490043c0700010f0120600c1c0e480320414031000003c10744e007050392900000c2c1d00c034400601700900300810b0340c002c00f41560007500111400006108d8040c0c2e40e550861001701482d00c21303910390481c1401c00e8910146174204074082e902030b06000c446006800e5007030b4010381c010441500c0c22618404215000202184100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 66603015 1250 66601765 66601781
    0xf0f0a0b090901050402160b0601020a02040905010c0e010f0504030b060a0314030a0f2f01140703021b03070803010509090a050319020c01080c0313150c210605010c0b0703090204 78
    0x88015031103401c03450411510010503007056002d00d1040c0040a101010385001c0000150060030100b540d80b90080102d09100c4d0514020b07400c20b0503d0317901401c0103015400204694000c0d07580d003100a014078011590090055052400202e00340014400315400ea019036801060050800d100c655996403a03414542000c1e610813241d40010a08107905900041c0003c2242441e26140c00680c1c4104e00d103103454614540e1200c95455140d448250004096005820664013140c00614901e041d030401006544000105d4003055851010300100c034000209030384c0701c250701101150441e0301300700c03c0c481d50301801002641d01e40714050030400881c1061009020180790095410402030401c0e1000e440c0c1910f4003040c2d81004455410804c1b001e1954059a800648192100350107500714142070b810070300007640c4242d0309450800601555600100300c10005188031212000c07903030800005008840f824071a65001c540300e005814000380305010611303403115080c01c000889072a20b0300884c00b2100c0c0c030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 66604265 1250 66603015 66603029
    0x32509230f0316060224041205070b040605070908010501081c02070b03100303090b1e0903010209030610030201020618030412030302040306051806090a030507020603060a0b070b01030b070c050c0f0f0a 88
    0x40c0c003401205c0c3c1c18410340030000740d00100e110f10317002c000303200d0110107100420207441240b401e0482d0000da0303c80e0080303451440d081000c0c0c000a00b06810502c008000640d801c2010820070603001860700743c10b0250318103c41d00840039005881c00c0d0401000c3c001e16400f108001c60282074400714000d401e100c06140100c28010701110200d09501c2d0250000d41950020480850140010b00d02c0f8984290546140c10390340b03a58586440b40100804d000e40901034a45d81c1c94000c1f04200030340d5442c545110002c4038000d83c2114115214502c101d2005045402d842201b07802c104000e000451581d600911003510903e001464190b680d1a4802141c000307407031a021403088020040c075080e03810003180d03400c040a40c01900440c40d0b903640181061042080081c0204408800030381d0687d541e0200c81c1c010105c851070b0741d9607480613181ca044401800d000485480c1c82c80c10215400d0340c442c1d03400164080e40300c40100000102c0104014a60303002e46081d80c0d101c41d4080b51187e00c2c4d1280b24840000f0615 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 66605515 1250 66604265 66604303
    0xa03090b181c0804110a08030307121a24040f0303080603061003020306010e061f1d010f09050d0c03060606020a05010608070e13170a090f0902030402090610090902032509230f03 78
    0x12f884801070580d46406d000318a600504101a4210b5407816600c01c92000c68540c0a00d282e08140101c1c0c03410300465000f01d4461040c000000300381030b000004284200f40840540b9940e50310503c03030300050380460001a41540c00580140b0106290341c800a81002d00140b80d8a01c1c0e446e2000c12007030300c1c2d000c03505020000e05a6581005d0382d2600500d441d80031042400e24401c884501103004041404511a29209004692102c0284001584500041d581184042c00141d880f810007950790250803104407000c1d0301e40940020041c101040f488261840040148003076141c96000d140046245441a00c03012014450b01080080450052641810b00d40741c8a06141c039100d010480d504043e842580c61a004200300300050b6200c2004903070101003115900803c0062031400c80380c3ca00d1940250464078400014040010301946201082604032020400319100701c0c80102d800d08690710807024090342d4004005100c6400322095800c0081c00780c0280405c0c500c1c01c1c0002d01e03000c50012020303c403000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 66606765 1250 66605515 66605537
    0x9040c0515280f08010e0601051c05010308120114060301050906040b0a06020c04060602070b031b0418020702091e04020111150a02040905060a030f080a03090b181c0804110a08030307 80
    0x90403c2d61080300080c542003030a11503140c8402224802030090149041140001c1c0c002042c00c404884200240f007000d604105643e120714103001241e2001d500f040905888000015210500070081440d402010b0129819a46450240101d061000d043c5035849502c859018949842d080800e00080216a0040464907a080140000c40c2c0d03003134100c0400c40d00038842c00e01030700d02d9400407203401c080f60400702d00e0041130301d0300e07000040d004641003030190350b40008000080010680180c006030f402141c0600301600d411500880c180b428020b6950740c0e91591b0009005507000f60b03c0800350f5034090058404140c44140d804003141821901c0304200c6a001c1420300c203940c5944071f810743c040703000c0c0e441e81107160540d156940404480c00d4000c00c10071001405541040c8244c1140055581c03025500b2074900301001041080791800b5420b4000b40b2a007000d00c000140007804c049034040340d44d128515162281c4d29036196201c8640300300358006110b02800180100204002c602c0ba1107580d0f10300316100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 66608015 1250 66606765 66606767
    0x61306030c0203040302090115090e0c0c0106090203010501081f17011d0a0507030b071206030302010b090c030723040305030705070602190b01140307090c0e090609040c051528 77
    0x24500880722011076200b8070003407006132202030b49a8191220302440c0460b04c40d00c801700b101d800e40550414040c51000300d091225075144100a44448001c1000134000c4645aa8400741240000d00c100c900203802d01022402460220800113482d803881e00300310440035244c8c10b40c4008044003884c003100d00d039558108440007504070700c01e4130164460234000d411660a03684616941320401d0001030481c00d9020040394940d40211004091074600f0141402003959030b09010740204400700310039010780050000144158106802c0381d1140950741c070781140c0d000141c1c600540b10921381d50b03139441861040101201046c402c10240034050311490042442d40c1c01e01d030b0001e090000d02000e098010002c0c4a05400041403141c3e1141510481d580181d04280342e10700003440c101311b683c043c0e5012071030402e17000002079000303004d41e050380c409440079800e54844000344402084111805010794100d241c0a01603454120a03038900445081d01e0142400003420200e03004070001c0184e8803001c0c030400c2c0c2000c185 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 66609265 1250 66608015 66608021
    0x9010e03300103020307031202030d1104081606090909030315030b19020307020303060d02221b09030203030d020a050f130302100302070c050909030c0111090901121203050a0b06130603 81
    0x64004180401c595245038040380e40c07030102e800000d010440c010310841c000c0e40f0800642d0880e83c260305040c000981b044094150316440b0f4060721450b0701884d454480100303104007080c000c075032807582d030b00200710702d00b410100c01040c650004501f0152200c01d40488281e0b807480a0b806540034203602041414401c00140100e607c00904020281c0140100040c8680201c00d40b68050b00507038030082d2450700c40c40010400343d0000c8492001000c541d6454070f000901354402c3c0f480e1062922128908031018000b6143c800e81407000031f501d84d008112404030080c6603001b400e00300c59207040982c03e084000c0c208020b2504428002100c0da03d0112082040d40340c08034000304e99100c0c504086180a0a507180e0000c6a801c501400380503990444c0032507922074042007140c030000c25180c000c100c0c000720400300d95030aa205001983c454000b920004c00d0182c1055805a02140c0c083e01e020720010800c40309030003510b80141381010082d40e6802c0b50419441c0d0358014450003910703001c0302c640503050540203822 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 66610515 1250 66609265 66609337
    0xd0c14030c0d12080402061204030c020103050105010e1f020c09010303050c060c0301050d0b10080d0201060e070908030a030c0905120312070824060702060a020a050f1f020309010e03 80
    0x842c0920040d110b000c43c41c204416581c510300c40c40c0003241555a8004035529100303d40c00c00c090362a07110208010706512015840c170b0340d0b100760303014040c99a84400448030f071440c3c150404c0e405140d005420000b4101260004046007941c016600c0030581e28000a0142030242d000703074040340c8006200107101c182807001c070781d2007086480c54500359410103002c1403042040700c1c0001c2961b900c420108014440d07a10007000207203a642c00321540300c484640024068a0a449000650701c00f00c004120740d1406200401c0584068000070750500400540440240010284910622000d1140030519407102c22000403030039410340c01150348090f4041201c00c0c400e130080100041200c101c00384104010326001d025005409070608400040a40700010070511907101d00075881072001513480b02083e004145000e00501510691b80c841c441c01d0142521410080551b10410000140c0b03041200310990103141c003c050800000303000116100c00c2c0346503900c10040240394901030220326200307100809400f00c4c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 66611765 1250 66610515 66610519
    0x30f160c060207030c1d07030b0a0905010b180303070201020c06071403030a0c020607030501060207060e030c06030a0501050a081c030e0316030e0411040f29070f0201140a08010b090d0c14030c 84
    0x986c404080240d151220806422042019119440c501250380d410b14080042d250190041100c1e581d86e072174a803815400002442c000b10345c12100c0b1b801500e0040252541c054040e0054510604a6000c11486a0103680c080340c0f95074080c958000c8440d0304001440c840c000582d000201e50300142c40180c60503a009091504050800006100d2107501003075000840e13132141001c000420f48840000c4c281504003484c40d4001d50084104403500c94107801690480380181c1d0314040d442d071074856107910b40b01c80304072a03000341c0c01102c0000040c0d40709078840c6e4000403040b02541c0c2009040c074a03640e00345c03c51031000d600181c20002031030598035043c410480041c2d5030090b110b2030700745400003002d041022403082450810701f200d40f00703603100c4403454045003100000e003609565103114070744010b1001c1d111a003640050802e0f10481a0a1072030011142c0c02100ba0301e8150490b8a002c500012030340c44480d4040e04503202d0b1000360001200c141045014096101182002d05c240c1030030f142c40c1c030b0030a1030b2080c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 66613015 1250 66611765 66611789
    0x403081302030c0909031e040302010f08130b07030e01180c0b0909010e07050705070308030f011703090d02031e0606030d0201051b090d15020a031104050102030f160c060207030c 78
    0x90010b96002800f41c2d40d100f0140e801405540c1c07020f05843c1140500a5a440580e2454110b00100c000d4100104240c030b00c00d072a10561000d0800080702d00720300496100c940180d03414000000700d40c903075010300c1c0d00449030320300402d008441441d0142543e85031040c0f4241401c01440107010890325080781030180c400c0c052141d042801400008040403410701c210200c02c000b54001c140d115100341c04507131166402c41c04030785000780d481c640180684e0044980301d0300400b800d00007044102c24030360750000d205001001141007140c0b040c10007524880d141300c103d91610035071000414001000c1038003a001c18296001c0c01041c5400c0090505000c103940c185401c69240c5020003003000414200c02d116150601103a5864050010110310f000c00300744000f030003401e00b60000e0108900e4680007803102e41200d03036085c0500300032030a0304440c50007640a164091303081488146d00e4004004090419103042a01102c809440b03a1164140c60f18a03800100060300000c41c14014085429040d1000b040048140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 66614265 1250 66613015 66613051
    0x22709070519050d090b010308070501050c09060d0507030b130e01140402010f1b0213020408160b030112031806170c0304030207151e09090c090302090606070f0b0708040308 76
    0x403040e00d01d002d851600c107000000c40e01c12001042c540c03090044940c0040566055610f90400b00700940206e641152598240800604524800b0091760000c55001e001c1e1030600000044802c081c0000505542c20559a0b04141d1001d1f520030121241c00740401000180e04040005128250b451000d44545140745100500c80183d9005230740e8000080240f030440050105a0b02e0b03d10350410400010b5030003264400380d90041c25099000740103c03081c1b00c08860b1210980b11444d01146014400c3c5040b004040c401007052003500c00c180d4080c2032103443c14080d034040305d2550f1400c0481581114000501e41c5003003007002805994802d410091260300e2900b146401d0f40c0080d0f88400c40d0140400d11004c0800001c0b0040c080c085081d501080d5107400d1142c4040c0d010f00400f04521440b60007842030414944081441c081c3c10160184d0744c020f080d542e81540e601c820702482e5442803900301c0340042100d11443c040740801003414024a941d594403041405c080c14010000000500100130301116011a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 66615515 1250 66614265 66614287
    0x120f0301050405041401020f03060103050114030a11060d060905010302010e011d0105090111100c0f03090308180703140303010509060901210c080f1006060f0f0c05010227090705 78
    0x192411103400321008501581c43d031078031030180003000110804542c0081410380284864001543c46400b003a601005541e9885141d40c0c04050700c44610340d0560030140d4030340003041100b891405220005421285000f00c5c030707001c1c0e0046451540c450124980c0c3c0318014000c640c0d0150780364010410074038040d03c1c0c9210f0b0038a49440040d0700306803181403207400216030000d6405440c2681c0134120b070400361480c41300000d0041c0c01500c1d4070100000010b0b10b5100c1d440003c0c0c044d21070700c1c1e100c41d019a9004041d0b41d500160086068050300b6002c02849540c000100040f00e00216044042000d8041d61300c83d4904000c0c4401a07101800301031103003900314010711200201800420354408001c00020101c84a41008103414010750403614480c01131071810300780e40c0c0340080d00305401c520303842d000c04c00160790b030000f200c0549801c0076010009040307660f4124124842d0480d129482c0c0200001460280036540b00208518113203410721098112100580702407401d00d26081e880000d905043d807500440c004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 66616765 1250 66615515 66615517
    0x10b0625021903060603053d0902040e03030a0506060a020a06150308030705040f060903080f030406060504061d06091005010f14030703240b0a20010e0f06090f07030213020d0606050903120f 83
    0x300382302e10441120000c418038460340c00c000c074401c0d00a0010083d031400d60b0381588e00c035802103030188001c50407c40404d0050038402c046400c1d17210142d014201804440d07841f00064008486000c0040304207500110100d00540c0065015002617142d41c2e90b59440c11a44240c1000740b41d02400911402c00b038100007240070501103d50b03622801c10031a94a40e41c0e403810341e00901036500900e401038070b400310218028202004060741d0742c407587c01c0b0200382e948000c10440040e6085070f4140170782244000030003183d40038150a8003000080d0422900c5a80f418901716900c0e08100d6111002a4490160401140c2d940d5404005445010711740392082d0700300342100a1754403c120f4070408000112000202c0d0070325003038524038106074030002030040c62640002256a0102d44d00311030514003d00001c00c41420b0000b030142d1200c101c9030b02501c00940755400b0045400c0440c0c2002400e65020440501064450f201b48800350045855141d103039203118040c149016080d11520001e580200004840b029181e8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 66618015 1250 66616765 66616843
    0x10602060c0f0c0a120801140f030316020312130302010809030304050705060a0e04020c1e190303051e0702060a20070807050f0307060608010b062502190306060305 72
    0x240146560780c00d460500e0f80b41410449018014442000e062444c02d98850b10203412103200b488e403090110180000c2150f0314030341b0300301345a05500400c0621400c0903984042c03054a8001400e80c0c02c0e401300130080c0e030700c56803141242e108080e8501009004560b0410b0103141c128032284c00640c25460969103541d60f59185005051150380c01180070300c041032181c4c0002e0180c410141055450301600c0d20341582e201d4249080f940703140c040d01c4507148060000104050242407010300b9414080554800303400420018010160002d00342480801e000b01c013500403400380c0580d038018a80c41c03402605550454603800340030350410300a1070083c0380c19458001a940099000b0b440550355242600d4094504000242c20f040c4c03900000c169402404003a038440750882e00c0400003809803507403d10811005114414282c240420090258004860780c0080448140d10203001800700081e00409454072400c581e0040700c80e103848803c00e1007000410300201400083d03e40b0440308420281d401c00c065000d4030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 66619265 1250 66618015 66618037
    0xf05030405060f040212030c010b040e01090c060503041a01060c0b07020c0d1401020c060c030103110d031209051005181b0105120a1103040809040b0f06040909050c090c0909010602060c 81
    0x1501c081410346d07848900c0503514108030b404980d074a1802c0c0010901a04410640394401c5140a1622200f0711040c0104a005035012044201c9207040c00320696607500094000e0380d91954a21240700c65030310380b10703d01e40030b0180c580300d02610448500d0484c40d2050000d000c582103422485450303d8035121400580142c2d07078070003110071a00d81c03042400c90090180c041541024800c007401d206510f2403090045050320f0103030005030401c081031000d00440d40c600e0040180012031014040380714410341d522a072401b61140c0203a0303004d910211200c00c15140c05640c60030302103c5200400d02e00101c02c0101d05811708224241c0b28011030304100290060107000681e1001e0315486001603207100c0c403039200b50800c5402944039501c9047c21b0615111580103080132031300032803a103400c3c000e0320700d030540800c080b81b50000d155510741401c0a1841c009040d00070022a1144218007000380795035510000d00344504030303035214161624402c1382000401c00041c0e01800540d0000310510682c2080001255086001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 66620515 1250 66619265 66619291
    0x10506070f061401030203060c030c0d020c1c180f0e070f02030408190209010806160302090d0c090506030c0a08030d20070302160b0a17070306030b090d0f0503040506 73
    0xd0400040340c0110140007440a483d0251901e4600d4024203c24142c0b4001c1c0c040b01c0b078540d40c240310840d00744800da0303080e065140c040c0548040c40c2d801d5001050351540c01c400765801c04514103450001241150840c0c8041519a403840449440c240045402420b401000d030351518039007200d4092410000d880d00b400c01000d401d51010890080048031f00924401c0203c61081070010304030180c0c2c503c00042280324030082c00c00016a8600020b030030307010390b40000d04250781070300c0c40f0030aa009501c003002c1ca036003003000031a180b404200e102011000810003000c010480303292034410541046e40e0400824883e2107036450501040f40004180d444040d441340e4002000030400310203005034408003032450000c00740000c000c01010b50106501c1c43c101d86000175400c0c401d07152503c2d5071321802071000400c00901100031040e99003120110b0f80b60006a0342c20002041030301c0c2c0d114448070200459404907280e000c0001c54403200d5209502107200340140c90004c0c02d5040a83d5150b0312030f200a8804840ca0350 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 66621765 1250 66620515 66620527
    0xc0e0d060b011b030f080601030c0f0e0103152408070207170106090504030e100306050f090a060801020721050307121a060a0905010225031e06020f070b06011106010506 74
    0x402201030f8030100441d4005920765010358980186451000c0076140c0001d900c02c0042000d55000b40101c86c680d81c0c182d122001d41e41760462048a500601e9400030307040640350030411054140144501c000f4015203a4010066003003c0103801e005003201181c4401c10009004000306c00368041420f034103841c2d451340150120b0280c030218a000d00015003040c0911032400050004040c1c00c42c24491310558243d0b8002d48a100c052411340c1101c0c041d1203540c2e0070581c6014100c07924904080825800040d6000c0001c1c2d107a107803455182241c00c200002c5490440d51080b60341d030050501c0c60800201c0140c41c0480c41d52a0101000b450b86900341100c460480d29242d00300d07600c070140c100d52103000c1401303420036494600020000740040c40030b01c2400c0c094000c8101f00d044c60100c400030008046002403220b105c0603c1d69440700c80c00c402e0480031010801131001500c00050142c0009c2041080c1c000809031101d0807410403203400744010b440383d414000c0120f2017117030300d0002140c03240c119401221001d071644 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 66623015 1250 66621765 66621767
    0x9070303021207030903050601060c061404030e040207080c06070c0311011a040f0902031f0c0302030c070b06031e07090b030102030702120c0106180207030305070512040605130b0907090c0e0d060b01 87
    0x45c440d0001022401000b0003c076415900c084107040d100d01502040c02006801568007200702c105860107800501000311140c028217098000b85400c91107460090324024200d2030840c103080b0266003400c001410070b02c5500c140341d841450111250603150080000514214044080c0064129150301031a200d14100d64100203030b41c0724100464000c0c0540d40d98803c03401d4032450040003c1d14100005162020242d05c607032192003682e1045640346501071414a55460307001882d4002050a58188901705002e18102050700d807004841c80a20000c00d40c850808031030300305680314a002d0b0390103030b031040c010001c5466001510300445001012215508d80d1014800c030302618040e0409a8540d1500c003000322018500e43c0205601030080d40e080041e03460700c00007225644109100d043c0303001c154001240104000d6032200c0c0e00700d50003409131000c41c7c00300e03035603000007403402c60304408150407560040006428601070811450094a001010108010005640350a91030000740400d84d80d42940001d503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 66624265 1250 66623015 66623027
    0x3130f030915111c02070323070b03040203010506121005041106130509060d02060f130e0406140906060102030d020d06210618110919020318060907030302120703 71
    0x40c21110740a4000d854940c20003503c1040c2100c0200d0140c40744141011244400c01c0c01c2c3ca03441500ca902405015140d0b488968130846d0285183c80d8034402d031400d00034001c0b020404c11008204d0300740400d81364901801018210341c0c0061075580143d40140040171281d0011403200104080110000307050b442c0e6082c10182032007690040b640009000440f0080c1080e05003880b02102d04c100c541c0503a540d01d000600c0a80c1040240003908001c092042c00c4040301c400024050042000324105079031590b4000081684206903003e0710120b0703480d80301c1c01d4060103071440560300c042c59070b0041846080220000b95a40701e4182c240c2515540450b6024000700c26420800080000c248918074080c54010511604003894008685003840c3c0b40842c810428000352611506030000c8084290b01c0205040c40710302d240042c042244080c0440f02c68a00c0340c0284040e50003a001c2d10842c007451041e98084a00c0c00001038803114465008503000c2002a0b80003565086106814138400e80341d1580b0301d829104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 66625515 1250 66624265 66624269
    0xe090a05061005030f070b040315020903030301030c150201060b0307120b100f0f14091003091b080c03031801030c02120304060c1d0102060402100c0b04050d02010b0603130f0309 78
    0x6640541014000d00700c0c849122001510811800c1d1120a00c10301702c01640c0c2c0410344101601103809000401c0030500c4900f40c40421501380b00003519008412000900b142c1c0260422503000310100e10a003d0b020f191401c5400c001070b140000c00150742404540b9403c2d000060006003040840d0741c000e1031248064020406950015002b00c5080d14201e03c082c0c0461721000c02c1c1d20001d42e04111242d0070a224000215030320040d91802480d0031400c00c14800c41d80c0c44550010180350722900001300048401491b410801030aa1600d640e890900c11150705101c070038121507200c1e82c001e1000d1643c0241841d20072030051001d007000500c0b003c004500303a090104030450b004154078040100001e0041c0c60300001a510b030b0b03d80d50090184266585081e1850a0700c3e907050060b40700300001401420943e0750181e1a103207909180b140c1c1802aa80e844211030100c40881c2c468000846050a0507024000c854a1220448000d82580b400c0b030b013440034140d80c0901c05000d40a1040e280400e0602602d44500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 66626765 1250 66625515 66625523
    0x180b011701060807300c050108250309050601080c060306040b0d0f050307060c05040b12070219050a0606050402030105060f07062304021809030a03020903070906080601140402130e090a 81
    0x150b041d0f0302e4095641240904040030035002035813255a0007003101c642045c070265030000d400c0c80710604000044907919070043c8640c507081000e000504001c1d010074951303603019015550101d40d8008610b043c07030402006a100c0d04051740240350545407036403120142c03940044140d5001032003150640000b40d0042a0010241042080e00320382d07402d102010004055040c062041406022807101c02200c8500c01c510400e0402d0009010403002c01c41030030006500824070744110340340d401d62466018450946e04104454035400f80b05807404200c4e0a00409000b4141210b04600350740c0750001203500c1d07128804420080b94000103420041041c181c1c081c501a80b07050303100b802c0710500190742850140702a68241d110300300d02118104002c08042109100387c2100c409107050071030010058001c0d400103061150306000d12900400c805045124202c01450814002c00c0c20354504a4a405030b80c0c0340b0018540034500401c000007002183c9100729048800141602d459950380b25a00c0c0c0c00c042c0d152400038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 66628015 1250 66626765 66626773
    0xd0203010f06170115030b040f1b0602010c08060306010f0510170103060204060201050a0b0a12020f190e100320040207050708030301210b0f041b080a06180b0117010608 74
    0xc80c11901901c20407500752120300013048a111170400b680e81110b80c40c40000d10148007a000100021a0301e04200999485a00c144200c007a041000c121060525041030340140e43d80c80e840242154004401038108109030040c25081d4117044090341039142c0340c00340d1405501c1c0390002a201c0c1d8072030042c1a903180442d14078080e003540c4034a040b030060f40c000d10500e001903003020081030040e1040c0c411120030040013072801c81010314200620580703403071820050340d010b45a12102c0c04540c82c4c2c1070108042c2400f110351400150300f407094003440c0040160291340145c20180c410f10014840f40c440c079000102410210a03503507464030015020b8800c96000030014020000e0009175040c0000c055410b0350207260707400c0d0b401c200c002188211000b203c14090032180750100818904140c40c0d20380e2350054041c101031f101c84040c0c1d5112451101c0540e006041d190312142002080c8200c1c3d1080c403490980042c4400b080140ea82c035401e003181e5040c01038010005e0001d19108580200f5882030b402000da42c1d040d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 66629265 1250 66628015 66628019
    0xf050609190801183f0306090212091216030318080706150504150315180f05060a0911130f060308120a060302060d0b03010f09050c0315060f0d0203010f06 68
    0xc01e000790001d560466030103d040d6031101c503590364101e2911200610350302c215111702c450800c01c0b0107618032800640525035200008034881100b400181024041002c0d00d60381401c8c200f901e10310303000112041d0601800180880b40b040044200d420352166094a401b154090541010901c006004030b4000c102c003000003024410003056400c5440801440ca10410003190780300140030994000000e0300d60740c100340700c00c2800011383d903001c4003009503095100083d10803040c01c000041c03296984020303a14506403481c1c0b41c04014007040051342c07003013000d0b8090164400e6070713445025030401c1001140c4140d4034010200031840300c6a216801410402106100e0310b035403410f1807084e56010400c0540c0000b40800000d84484d800e000f01421240d01510488c54850707403404180050100f040000e601d5506d6000030100340369503003d0b403000c45024030043c200c00c002762801c05180c916619911074418413041c040011650728403003030080250064426003a42103140c400a8018443c54002c111890310f0b00c2c0700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 66630515 1250 66629265 66629291
    0x106050a03050a0b010614071e061112011208030f1e0705090a0b09030c090414030301090209040c0320070501060321020f0106030503031902120415060f050609190801 73
    0x107010541809284e00d646a80d0f00c6810441e00300201d010184e0b00550100710607070002d888103a04001d1540d6442405070380300000d07035403a02902c21190110950700c0001c940c050302e04407a1100d590040202c1544406000140d50b0340504d1404010100c0b854801303074000189400158030f0074030701c8401d5200ca10b1071443c9441800603100303400102a00d400f0700104103000c980c010b008000ca45902000400408600702c0c3c1008210328114000c1040715581040c0140040029040014501070071440c2005038403240000c2c140400c4860400c2c002040600b440000c6010240740045440340c84040c40c07440e540e0b66843d040c10b502401e02c55000401c0b0280d01c1c42c030071a480f0101c80940ca4030040c2da44c2a11a07121601a4135400d030791031070001602075041040414811340100402280700c0784041d5000d400c19901c1c1c02c00010b00041200c09035030291500358030107003080365032084d5009440c081021400f150b09010211314a4001c40f1111801900d0031030710091b03520b03190483c00001384000700003070040c1c50011031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 66631765 1250 66630515 66630523
    0xc06040303021305030316060c020f0d020c1e0904120c02030304120c0b0304031b0f020909060411040204030b0609090c090403020c0a0f06050304030e011209110306060406051305090106050a0305 85
    0x10b19960f040c4400400890702d480c1c007104031108801c0a2036280503621003038039124000c290500c880825803003070307402c20b2404550501c0384642007107640d000741140c48211020300040d0030407103411040c0e503091079914440540e0b0380c840694101d038100707003811200051028150f61801c480396020f5854030010500003902c1030115800318641e4443d0b561513039690707529487c1c90341c140801e41c0c0003008a845601941e090103040c03903086151600076503000c154004142c011401044003500c415030a03400c00d074100000d01c095400700b0101040280c800f140303091b28580b2801c1060f180540542d1003240301e000411651401007140c180c1480005007060310300d05042c07070042c3d502c10750245010b0185014030400101c40d002e441403134045034690346855145507a103540455603e6002d050013814000c425a0341c1c9074090310b5228120354688503200c41a100c005030800c01d46041801020795220710700300786040c015615002459254103074840e030041111748072042c41c540500072a400c00354111185480000600030005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 66633015 1250 66631765 66631777
    0x503160c0f0b040f15020d030c0c0209010e0907050105040f030605100302180906070c02090103020603071202160201030f05060a0314010603120e040c02010b0a27020f04080f0a020a1403030c0604030302 88
    0x11080c00d109175958000c00001c20442544400541c00c01c24646212901a811401040d0a03510b450207604000b5030000d80c41d0b980030b8100b0b10310304510300100000150200031000140c002400d00d68109498a4807400000885000040c4815100d501040302080c0c11b035a41805954001d124946a00300410310a400c154211002d1015125441c003040704280106402a02c1c44e4024000c05642ea0942d004c1c84890390000e003100e000c004610100581d07155051001c0c0c1095030361012030348958a0705000060940300803901c40050180303040188441c039501d05000c2d1003281c0e40302c490180714100e0803401c140189a240d1001d005c014084400011599225071003c1640e401103408104010003070000702e00303c4001c00c0b411a0003a10480c028403140b28078000300c3d035070f52410041131003000102d4031f06401a60050004503402d040040b809200d2454240008222601590018524148035070001802ca040c6446200314401d603401120020347c9080c42194000c4001a00f10750250034140b40040003907000c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 66634265 1250 66633015 66633029
    0x709050601120905060c030702030c06040506160302120a0b1203030a0204063b040609060e04030201060b0a0c080a090915080d0504050112150f060207030516030503160c0f0b04 77
    0xc441d4412030b450700c2a0303440c941d0010010440381c0d861003400055588081d0801302544414480b00b00b1107101001a113103d40e01c034601070407007070a0101c0890b11004503081da200134035006205501c038000100607095400440d1001c0410407820300408074082030500c1c40d15200310300000003080360540e8582c006204480546c0da624000741100c0028100d80e0000601071644c403503c0e580ca07280c141c04030601d0465108001800000d5047c2d90340b1034102220790325071001515810480800c0103140c0c082c400c820003000303100e180d28900300e1b52803002045081102801080340340003284841400d4400da181a01802818500f0000c6407090b0940e200030320414441c501003403060780b0074591030b81e00c01c105031400c561040e128441440c2c054013501c070181c500f0803143e00d02c07500d100c000050006a0040750b68001c200540152580600f103040150520b035964858955501c1c4c0c8403400c00008a0000403680c0e80303600340001481030302442c60084400d0055500286056180b02c0002c100c1c05c0071880144100c40030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 66635515 1250 66634265 66634277
    0x503040f0c050307030606180c0e040b0609040c080108011103040302120d0908030109090606090b0f061c060303051c061805150a140102060a05070e060c120f0408010b0102120a200709050601 83
    0x23514401c0d500f0348002d0034031507001600d00391210142d800d19811926141c140185283d04259910303001c101150308224880d00090300960040201c824280315545070369000c2003480b8a1440c1c135032400780d83e600d400840e811000100140c01e1b02100c5065002044586d8404809680c03940d5a80341d54016189402040d41c0c0b46180400000380c00740d452055601806c80a0121b50945841c0410004103801c440146404a101d0100c1d015a103510b51041101542c840d807203060302ca0200507002013400081486213003c0d180b42103020f0180c3c0081d149040f0180c90009030205440da120100d00038000c45003501282c20400c09540407540c0d091700004105445001c2c0c3c01c561003940c0e0a004013090f66003e949110120303011210f52059402d01000500c114008902221121000e060b002e0701903510080404000030070108040c0000e032001e000e85010f4070424402482029452004442948103c003010420721050120600505600900c0b42c0c14004040c02a222030075035a03020000540001c84d00ba80c00500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 66636765 1250 66635515 66635549
    0x7050a0b04032006070c02010e0301050f100909030210020708070c06051b061003021504120b01140301140c030603010e030f07140303010b040b2118010e010b010503040f0c050307030606 81
    0x2101c0d54486503c4204000142500d49401c1015544103000340d40070ba0400c44030714180d0f526520309004140c0078486860140c0c82a2508a082004200c40307034000d85041800c00403404c002c00d0340012034958109000200598a9443e0305c0e000c0020300c00c0c59001032000e4154100080c1042d040340140004c60140041c8a00c81421002003544496040300c8030490080b04405c10300160400a40c1c01c0b80350141004c0640c134043e10340041d1034200b040360408603850449600140480780ca00c030100001403c0580c000d00c4200d80043d00b040000000400d0f031b400001c1c001c070000701c0c03695003500046008410181602d60799400e040d242c256642c031a41d401c0c3d03844081c0143c1c948a038800003084034100d404000d10281814101803000016a000d51002d5200001c1030f06410303002e4407a07031240d0b40144031002e040e254507001101c001c2c2c20346d6420000b8211917494002003101b04c0e6004001c0301c0e40a54814074030a6031070454034184035004000d0300025014030a01380007100b0004540e001320180c800003d16485010b0b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 66638015 1250 66636765 66636797
    0xc030203010e070e010e0c040806010806010f1212120b0607050a05070e0f0408030406060e09010b09010e010609140a0b122202062a0f010c03060e090c0d050307050a0b0403 75
    0xf458441d21044140d503600412114141908050300030304130114241c0b60076501d440113031400e03000307810204854000720010818041203121107401020400742e81024644c19484e014a008404c61181050100c055030710b203107017100c2d940101146c050041500e51904110305240b83c1d5803011034001c541d507119100c40843c080502c001d42ca84070304441c0c000040c840c2e071603584040f030304c0c6c00290003200e60071b80752000071890408505105200d4a12040002a01c95001c03040000182069100c00c0314481d4503001032002caa0320501942c181c8010080c1580c405d1060808a9403c8846500a410b15000410040300903200f4a4038540226001da82007090740b044010259500030300580000e40c403510070810301007038030102c1e404540c070344d01c180340c040481540e0030700a18100005c0130031a03c2181d5450054050164161280001403d05101c100c1d01c1c074500320b411a5521b500c00d070500d5101e004010f86180c01c12000700102c84a25600c0300a882d220400d62501c1d041c40351041d20210041168aa1007000e94 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 66639265 1250 66638015 66638023
    0x606090504081b0a0c12210e060c030408060c030906010b040e180a020a090c1403100b07021309080901030b100c060b010c020306010308190f0804060f0212040c030203010e 75
    0x20340d41002c540ca00d021a010450310903400e5504400307185008400080700030450603248080141503401c01c0b8450400070703240108882c010fa03402e00111400f200070040e441343e8084240c0040c1d04041d034421760b4892410014078550302540d80001c07414455041041074040e80000690f0160007103204840c01c9903202c3c103010f00a030040b4041c1816605041000584400744d03103403d440341e00320010584a0034901500032812103036a54002010301030301e0b00814141e595001d00300f624061114060941541807100702c100c14202c00b4820f41a034260f01095042c00d41d595010130315102401c010041100040d03a1800c49011f400c0110355501203480c0508403035441c1030141c440d000c40c2d040c80d61915041e0605544100040140c210043e0410409051010043c1c404000031406140900c0c1c2c09520f8002910394503445000325003904081241e02800b0045064029902c96049980100301280701d00c0359030020002401070b00350884040d003d80080c001800455043d210a4a0080c4c0081c014181c41000303850766 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 66640515 1250 66639265 66639271
    0x1e0c03110315041d0a0302060402030c010201140a020708040f1401090b0405090a090c080d05040f080a020a0e1504142a0a030905010b0603040c0602071a12040204150602010906060905 80
    0x1416500345440b110342e2070980c4c41035640c02c081440992480c000e07504180c0c0780c0b801c03150701100580d00c04e1084c4402d5113410800b030b020441d001d1000b03009480101214408680003d48541c03d000d4010038048c04000e044420349016101c1e44040040071581c0b2300030b6041e50251000d81601055a071803020841c8d42c540700885007524000b5180c2021500c415040300000c1580540c1511100f00020740441c042d20240554515126560b4401d41c0b241d040642038030114045034042905580204094030040c0c61399080001102c2c00800345440903aa0031403002c141041515025500500d452020001c034060000101d019211800c1407840d40302600e09401751914520326403141880e030070b01c14220460f01c00e80080f00d426214000216145403200003103003094005036821914081c051b01d042c48070f240d04000f084001d01c0500c0c5c109045420301c5904003007a114031040f400d10b958400e00018155151904100c001c1d95a060704000c2b5141c2d5041c0083c02016030040444a00d804c20000040100c524025180 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 66641765 1250 66640515 66640531
    0x5010c120f140c0c01110307090f0803040317130b03040803011502060103170d0204050402040e0603060a020f04050d1103070602010203070f05071e0c0e010b03070e10020c10031e0c031103 82
    0x2c0039803240480d14540d6080100d90400641d01e80c80b0503006101d41401441c012001a250000310904040000e4460f050942041041d5807040c04208081080c44400e500c040b136010354810b640e440d058101035004c00040d0000110607c00009100401c007408000b14100d03200c51701040c40240c009502240c41e408284130142048204010300c410031552823000b002e200d05512401842c095895011905a8101d640b02d0103e40e0310550401003542024000150b0000c4000800c41c0b510000102051180c010360042900a0769410540700401160000540030808010b04aa46103950388800030301039842100e407000006c41021621003541d016100390b80a050b4801c3c0c04c0c5120b0042040c102c2c11300f802507001620f001581407000901900041422800780001d002e07140e9803441c2045002c0c00150308095140d006105940100c002940d012030a00d080c071008903515084007000e0a001c8002e080f06003903010310801c1c0540c2c40083d0b0089540a034400490ba40c406000c40340709c0c1441811107001c2112901 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 66643015 1250 66641765 66641801
    0x10b0712032f090a0815070c0305031513021815040503030d0b0316060c021009050f040b040f1404021f0807080705041203030207020112060807030b1305010c120f 71
    0x71181004500300d85108a6420b62003424841c4110018190313181c103512241c0315400404040c02c00480542100ea0312040da42052001007203d80d900500d03a01c0000d150020b403158103400f6110715038030900001c080490855095449080031442a807101034400300e034520801d221034040030406080c6080e5001c86c0c8004002c1d5040440c60325030385020300000c11440f5803500134102030140102c90701d000500604100c0c0d030b039080084280d2060140011000c50030100340040036038104040d946011024501c1c0741c0c107030707400b003030082c0c80c0004140502080141d0384900780c2800204503042c0340d06650184503600841d5940c101c0a0b00541c001c81c8951485049070006200d40c000501280c094400d07190400356602e40103180c1981c40c004a0a0341c07440700d40450000390001424829580c4c0256680d288001440c0f04001080c5400d80c840c2c2d50f011188801800c82a0100004941840d000f80d120804c1d03400400070321070a89107810046c00c203800d80d15144440d902c0c0c01041600f6040d07500c42e43c20f00c800c00c11a12 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 66644265 1250 66643015 66643061
    0x3060907051e04090f0309170109020a060c32010b0d2303070203030f0a110d020601060e010302040b030a091202010c020c010c150c0207080d030e070e040c0905010b071203 75
    0x4800d9402d0020245820584481c0507900003803c0d400c07019295070099070380070310403030820005400b0010418188a016030410a400001d641c07a11282e2045031a281001403a0002628224107515554041b00141840998101c80104280302c0340e00d06c6002d07950020050344903118104070405425a002030001e603c1e000c044c00b8040300d104c140280520138202200d0a065181d030000b481d41e031007400d01070300d01403003c01c00440050300300641c02d00e83d00202e80601001c81068900035520b07501441020204090450040c0f0182d010382d040b10080c01d80e49404076034070b1410f4076420000c3e20513034101300c07071401554407005030840c418440d0002d00c00c2a81c0c09001a600c0200045030640b02d0b01d04195501d46e4090403e84240e900d5100784003281104d600a481e001d45440c29072424110007100e41c10905080c003291540c1c0d203001040c61002d8500801040c0125152410050324407811a00131040c46031a01c400481c0490148001d03001042c41201068600c10610034110155111401c4a100340c42d130481403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 66645515 1250 66644265 66644299
    0x110a0602210c100c090321020d0302090f0d1101020c0a0e0c0a050d05100e061212070303060f0e100b04050108070c05010e0d05040509010e070c080a030603060c05090306090705 77
    0x10b045519000c1d003100c000c03074003a94660088031111103604011030306100b820000c06c05810343c8600038081c0c000581240e03211500b00a92549000c03180542010b034001102c013610307501c01d00b59070b00d86c20313000c0d00e2140c00118030f1078403a00303d100c080c0e002070142c81a00385214042c80c015004600365441d020f09507100d0344503011400d03081d030440c401070b10030b001c0203000c095645040313071040a1291401d40031440341d1078640000d203822800080d01c018018074110880c1590810001818440c1c503a6032400b00303995a2441c103041f00140704030b41280c1300151006c000081c3e80d500031420780b030007144080707850a02c0c035640d02207070210b40c81148102804598148001040180600e5004030790500031000418042200c4081d2800c00000040c0880880c10100303042c4940e08244a44501400c2d1000d02042d00b400d003804090300d00700103100000d000302030000300741155038829003142c230003180c2c007000603c940c1c800500d0103171003904551b40c15400bd10800300010307114180001d40404848018141030309880c51011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 66646765 1250 66645515 66645517
    0x120302032205100c0c0b07080a08010603022109070305030a020f010b0409020f0f010c080316031103010807051908070b0301140a03111c02090a020c060a0903050d02070302011503110a060221 83
    0x340e0751031407170755000105e80038540001c140040c4100b02d45a582c141070b400140c0b4a00d01a0840d030b00b01441480000e201c80221881e0307501c2c40c40c510300801059603074030740518034201e401d8000030b249020101c1c500000c2900098015400e040d0107009101100e80101032004481c1d40100203503100b0070000020b009410940800c0546110614100c1000c1c15203440e1415076a000340c6010ba00c0a0003400c1c15910168184141094030b8001c800092441d4901000641d03280400d004062140c072101c2807030b034078001104400000a00b0321b08242e40c0c5540d600c4008146d190800d211744500340a40003c2c8410a185c0b40e20035005aa6114100e02e9203840070505100711502c20202c21509500c81401d80e40160ba00d50340045d200300da03a020f002d03a8900407541d41504180001d0030745850141016845000203801405807000c1840b4034500580300d54a03403e049000d003030b00c44d042170503c0315039004c04001d0101031400d05039004001e5483c888402d56459040782d9880140442c0050b0488026001041d481d00038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 66648015 1250 66646765 66646787
    0x120903070e07111218040b0612060d050604030306050109090509120f04051504091808030601050a09120c0e01150903020409030e03031b0606061206040b030712030203220510 76
    0x1180000f421421201c0305890038444980140d880070b00403540e085035206030b0480c00401401550b050000d000c81c038020443c3c2c0c0c00f80a5020b101303e0030310b100240f81e07601c5e4211540c1100d90400c1c00c079690760030f00342000f030300605040c080d07180001c02c13644001c60380d0341c1d00e8018680103505450061841c0745259401c4411034001c0d030070003140440200000074040d580c045100c810000ca05c83d0080c0c0d90781c641603101080381c880310f10065440e41c41c0140b98011454070810340f0b41c4240c0a0030720396500c8032010012036070085a80c0103186001d0a1035500028415002c03200d00643d010300c1c88081c2c0a98840d03121003030942500c94110000b41d00040e061005081580000015030b100b400c040e000f004003140041c2c1150001104001c2c409940b1000a05404d0200030701c5030844421ba64082c82d20349410a1040d599100410460085031280d11f400055242044000002c01040a620714042001c0c030f002922a8054100002c40005400028002c401451208030841d900141003403000003095070190b030f07845945 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 66649265 1250 66648015 66648017
    0xa02030c0901031e06030308150102010606050403110d1e050d0e0a060e04110f0a090603020a0801141302030c0702010210060f031205120c07060f0b0a090e01021902010608120903070e07 81
    0x5074120081c0d03c4c0c0b590140310080c6100c0d03100c200300c506d40141c01125a1600e9414541160304150081080750380000450301940d40040310030202c015281c1c0810700000004000030804103c4000c1e00d52031080e41030105c1200d92040040d2400b40030050000c840e413001d02031320603502c5503060380100b00c054000c01c1101d0782d0300701c0a000824400fa101242080f581c12200b4004103001001a00b030800d5980b00c0c695102070300181c1800c60401c03c12020007401d44005000701e089400b06400440d01d5980e40c2c244124494000b60820356603864011702d10249500320080490161250700781581da80086801601c044d1080000d01321896480d40d11800d40d400c1400d20040103000c1c1c100300710786145020400031482843e8400440381e96603801d10300241101d05201d000c2000500d488002c1c0305503a1840300c1002220303e44000802c440c0f5949800c0740c02441100c5102c80500010181404000e0f01034000e00c0840c1c10031001d40b803409080d100c2456491003400f50791a8190800d045c00c0c0120380c640b041136a00403030b607 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 66650515 1250 66649265 66649301
    0x3131e12031a0a05032802040c0c051509030d0b040f0f02130b040e07030222060e0111150403180503100b18070e060310050d05060906060d0c14040b0a03060902090a02030c090103 78
    0x1d50082811104040c0b944270028000ca480c107070601c007082003000c020240d44400a0a83d00d0200c50b03164581c020294449696a1140116a155501d0303400100d100e0031001c03000c1140200c90320303011000358845000000c405005d0315001031086006030650302110181450a0b00e15522200110002e6209108031000f01d08240582c00500412000d1840600059222403400380d003458009040c0fa00150340c0a040340d441b11509003440d80462403600c2d081680740c1006a000178a03c0c00602030300b007094100c503402d446044d07a4400000c1c4141c006090500e0142c94240b80d2040e0f00c2c2d100b02c0d000c80e0441e0500f000c61003070542038645003401802583e00c8008080140407080d16400054095408072009560540c001c030b0500a440078240161070b0049400c03070303a4a116040713596850105120750310465485030b042e00980e08581e204c2d5084040b9000e80144100d801540300c3c5007840080600c0ba60980c010821080022034415841c42224002c10610a4403401c140500d0011005001015900c03051100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 66651765 1250 66650515 66650593
    0x170402011404090204050316030f02120f030d05040606120302030f0304060f02030403110f430f08010c02010c050f0d090203011803080c03131e12031a0a0503 69
    0x7032840040c101401030b052004d13070390310310f80b0040519100a100c094084179846010410000c0e1002c2e16024005d07a0694008030003040c0500000d060a404242d04111030000085440315096a580040d1007a440b50008001103a00d40c1c40a641e0a0040030000300135030320802801081a150001550740940b10320310100d1440d441001c1131741660000e4404401190100384035082c1d90800384140148005a1030003005030f0720342618818101c121790780d0083c0750300101845403560405c0f036106000a00c145049070715003003640c0e40c1c501401c01c0140e10903c00c4035480c1a8015140a10600540762008502d6030b0f01810407815407404c0929a00c10031390f15000650300c41400006031420b005140c901c000c5800c8096110b003840c00d000c1c084500040452a424504004203c0280c260724004808550019680c0c40c0e285035410103a0030821805002420b4181100c143e42611a41a0800e0608040241c1130312400304159061214028145c068554103400600f0076038559802086040c03481c00c80c103961404800d03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 66653015 1250 66651765 66651797
    0xa0302070608042105030406050610140c01020c010903050301082803030e0a0605040b06030d08011a3004140f0c0906040f020f0306010905030a0f0215040503060a050916050117040201 80
    0x1140c2013a500020030000710070030040c8040c910032107900c038005907081c0c0031240c2300c50700003805036150400e01100c075840410080105c01e000d40c10b54490580e098004c200b41c20003424007612507002403160404901c14035440790040c1c0006500d02180c442c40305403803d03410310565802c0c1e015008480245015103d10303141c2c1c4011403042e00070b45015600030002c082c00350030108181401c280d8405588000c0c05010300040001014106040a000c1c800e16031103038070b070840d000b018206420020310032021b05614024480e1800107140300d850042d0b214002c1c0e9550110030700031068480710110382c40300c000d82000c01004001d0800c4464280e212342d00400c0014100100c15124040f80c1012807401c49409011042100d2542c1100911010346821001000011036542c0c0700c5014841c1040002e004241d07074000740440040c4038058401400c0000d003178030580d10705802c100c001018112840080c500c02c0c032204910700c480040020050300c006039500e00000ca00014a200b064002610403410402c140e40740f51410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 66654265 1250 66653015 66653063
    0x311060a06090c03060501020304030b04080403050a030f02060f040b040201030518030a1805040605130e01140405010c090b0c0304060503060a05030304060c060b010815130f0203090c120a030207060804 88
    0x1400040800040742410010700c201182c0c040b03411902410710b024018002aa000000e45044940c400c0f10000c50359964517140e5003600503540002c081d0712038140c0d40410113802c40100c2ca0410303c1d50782250416a1450071081c0c0c6048245c4001e0301c1c526404003c0b4000d940700380c1000342d01004409040300d514410306116882e40e8050012500042c03220401c0481105845010310700a15003103030144241410900000e088200d04910507020540c0e610108103050f1080d08241110488154013074404d14142c01d00d80d002e00154243d02f00014600d403004240080d102040e06c1050007904015418107042540a0f0f440764009410550302c0359000b81c1c00201039070200001d101800ca5607981039625900ea2502c0002d81d101c00d207905041c88412420001001004a0444809081110114100000400c0324801000554490b000701400041008802c0000203140c1035012000d0301c1d040026105090866180d070302280008005030000c2008000030ba01c00c40d0284c2d009030154110814000840320480c640c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 66655515 1250 66654265 66654271
    0xb06041803111e030409060e0609010b1804020301180507020f0606010c02010c0203100c0207300303020d0f0c0e010c020a1502100207030810090b030a0206030a112107020d0219031106 80
    0x100d500005086c0040101800340301d000b0a20f0320401410750901c80002156070805014122401501080d80340701e000c1d52200608401c03101400031075036940c50b03880348120000280d00c0c0d411040c7c141404608110310024a11000a0400c405821591100c000444464072800b000343d0404c4814034955000d2307a400d0004415620405500040403640380070080d003807460030303401103800007500f00340006c0246154445240c07011000d056105a01e84501d0260f00900440c1c0707034450350030714124405080c400207500104050b0722507104c1344154600300004591007021501c0081d00324200c200d08110080e041e520250f0003680c3d80c01540c0104000072041012a000164107070300044c2c860303060004003c00081c440300585070021050002003100404666102c05031a0000d018050000005040f54095805800c000c00104e0300d4565034149010502000a9a00c071007040c141800310201e8034180c000503c8840111103900940006018041c000810300060442035083c49548120400f000d2401c1c894188 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 66656765 1250 66655515 66655573
    0x402030c09041d06040201031d06100305011808040909020409141b0a03030507110105090d08030a0c08060901060e040b0405040f120311040b03190204030308040b0604180311 76
    0x80ca0307003102020030080e148503c04488452401d54001c81c1c100c000807601380d502071740a08022503a40c0d01100250640c2d810708050840f5401038600744816101003c1d491310072a800750b8000d104800c10805110328100c403022000f48007001c100020001d1f80125040130000030f0006200040c0203459803180c40008010340c02002041e000218203006603007084d20180c242d07803010746071150300e00e0950350301504a100741034004d001c50402442040c0305a100714100c40c5a0100078100701800009031a00c0082ca41050701c0d0703039940b64140041034803e5849207a4982c41108000c4c68010107034a070000503601c554246046a0308240c0f10003100106844600449019601c12000031528051600b130203440d264000c0c10360f00405080030258100040d11206580a0301c8041401a03501c0e1550010301d00c0e140003440c15034241c9400070600006254224144a110701e000f1240248265110002c01040715204030000d00000c500c9001ea42c0440d10601e014130482d07102c0c10444140e21315034841043d603944007000f118 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 66658015 1250 66656765 66656767
    0xc060e0a0b10090509122712010911030c01020a140a02041e0b120705120a1502090a0b0f0403030e04020909010f15020102031003030507020307030c090207110108042f0402030c 77
    0x901a051013150f0303103c4190005444003040380c1c51078181b1032007050034918000e505201800441001d10064a5508800034007030281e031548044841d020385000c0c00c00780c0d038050603440c1c650100e04001c146030b50707a003805030701410200a4642e41c0c01142075110450b00058441d005050300180c440f48203030301034100d1550030310b611170099002d25010703501d031b074950700340100305450340700d034014200003000820303990111000e26800b10b46800c0149401e51040300a400800702407020000b141840d8003d124000d003d80c1d24189680c1c580c0d40000642c0301c2e000003814111010001080801c0c0304182100070881e0051001d0315140b51000060007551083e005064150b541c0a401c00c034440440b1100c0c011b070b0030240002d609601d0040174500b8100031501c40a0300340640003402d2800c554003401030f8400340d9400501c0c03c220390f0711118103000a4100c0c21045800c07a041d0f5925640940c001e0380103610071a80001c6050004080c80c49821f0301c1d19081040b02c49100041c140030609a4850000e144a006141086 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 66659265 1250 66658015 66658019
    0x50f0c160f081b13021614060601050703021005060616140d1b02060c01090c03030e090703050c1804020c010e0102090a05040902060307030908120702030720010c060e0a0b10 76
    0x121200e640c540d1040d9078a034004004a0b45070448018440780521049821180c4c0e1808050584013a11070b511036541e012001701000410401ca4848502c0302074103450450340c10380c0c0c9007401500d2600c0f5422000d009684005080074400314542c0041c0d41c05080545a03a0501000626236090b0a03c05801121801c1d0010100d12070011308010f2604d54900700d04c0d002040c01c80110040909442d1410042c1c09840000340c1900b82c0d0034250048059a5801042c4c11800766407410000d041c0303481c501c0e01c2c603c240074900105001c540301e4040ca0780624440304c00c03240740108020b03542410004820503a600503800780101038401d032003171040b84503a444840001d03965407218030800049100a0300001c1c032a51030600c001d0050303102c69040e00d500003070a00700010b0704901824066100d006010711804000520390401c030305035501201a0511511521100200428000c4c0248810059008150002d8a1000c80070702041c515044808031030f050900b90b41050130b441e212945440001c4032920a942611481 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 66660515 1250 66659265 66659279
    0xb07030b010302030105060904020d060e04050609010b0d02010905090414010f020406021006210303060f060306060e030105070f350402030f0708030901030209041407030c0219080a050f0c16 83
    0x404003601824a4110320310340c1460000780b1240141240603014541c080340c1812070910b1fa501c400c003d41600110003074903140c249403d603554031041310440f40703039428068400a1420700513001101103034140c60344c00c0d45c9400c22040c0084e00000400689010030013050444c0200030038410821075200140303015a486042a4020b4640017041001c1492207117411390800c40003d12003079540703c011800d007a0101c0b804c07003410100d004c0c10303650f000300c1405542e000c070028115030160300901c202d8085071907003111054000201400c03514112444000328034028030a0042c548100980300307081040c0041100145018031100301c844404035040325031855000140000d526040002c0c0e4031101507440105402824454419205d020341200e5505142e00861041c0903035176a600200c9418490001180140c5070582e4010f000e00246200d013805800740010680c440f02c10036100900d200d0708801c040d481c18a03159030484080d804107400100808041c001d800ca60441030015000120030790000744039440c20468 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 66661765 1250 66660515 66660521
    0x907020c0103060e042001050d02040e100501030218011407050304090603050c0a0f05100311070302060a15030c12110319031412041205090d060501090f200705190b0703 74
    0x20130940e01039420104000100c001a0008000410141d1541080c0360100140c405016400e03040300910f0002ca4041407840030503407928030400c1d010060001d2541c2e41e400650480c0302d400940c2c003400060b455001c04a501a4880601d4610003040b02e5141c8810780d2030b51404c60304150003401400d03445003030070001d0010400828810f002c3c2241d10881403841c0911100b041030151155074091001c40c40d0030110b00f130180c1d000640950711401c41c41c0c0e0342d030f8262400a4403100c0480d2441a094078111200800702d8100e160241620ba0002074500318a00b015105001c01409660444035484030381c0d415541c40d1418041c10b80b1122601d000e840300c140041c030f4058010076001415111401052245102c841145080203030001d802c080c0c1c0309000401407004035071600c640420b07640c1162000c1e0421080100c1c5034002c0e8121040101e04014130b602d50713410081542ca04100001110803160715511100d2a508005e040152040003210915800260350710050310b0f0b104816140c2c0d444000822590b150140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 66663015 1250 66661765 66661769
    0x5030405041508010c020d05030f3402100c0c0b04020a080d050c061e01140a030b0c0a1106090d11010f0c03050601080609060303160c0803070c0305121e070807020907020c010306 78
    0xb0028042c2c087c451280107020b800300401d00d10076080000080b800380c0345442c403484c0c0780283e588003c0e07000c14524030003103d60b0045101e80100610860354030310b20000591007403103108a490b236540e20400304ca644828900f008081c005907070040014038000780202080003c00c400041640f0348a4544076541c509600300000108048075845034002c1d04203500aa05800d00c0c10756050050580109501c00c01082142032903800042000d1005c0060082020040c00a41103410030359454569070b6030759514403a10348a003540c02103401e82c403240411020b140906000c40c084c103001800000c1d403c540d02c1d080d0060322401011040403070307980d206000665a01c0000c1c6644604203a070500c2c01401c0040c0841d590b031090742da400c901422800001820040480c02c1600200290411a5103a010500703140540c0415448119400e10416100d031807103510000c2503400208070105990401c4603400611900c560101c23500f10744c0180d04103c3d9a0040c0e880c1d200550088a40c0d81c001c00320100401c0014080794079036 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 66664265 1250 66663015 66663017
    0xf11040e07121404060203040303090c030c0807060504150e0105120f04030305010803190e0105070212070e0115080105010c170a030504020a120f020d23061b160f05030405041508010c 80
    0x2542c00034090f0100403258000394498801030f900d40d5681803c0740101510700300141142140c42001050203c444007010075604900c02f682c0348113590301d005441d07603c5a48a030f802d8120300c42030b9480c0030030301030b0702050300c0154181003d5150050456402d1105034041390261001e1003031005100c24150725104182c0506241001913150040310401814549015007034002000a03000440300c0d664403031015104020b40c007404c00b90740c40c90342462844d02c4d048076000d2801000071003800048c2c52021640304100402c03941d19111071036424000110b8988004003015520034000e05600340004541d44000e000c121116507001545040601c10040b0b040c4c0d003940008840c180c1001c4020100b6103803d07441c0c220950480e480418210a840c00f40100c1e221459100b0442c500344085007101c41002c03c003144525420603141c3c4c1501959603030001c8a006611003126040040190340002482585032b1002c103501034411039044c541d481c030000c0c0030348206070400d0741c407407090070b0007046041c42c02d004080b480411 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 66665515 1250 66664265 66664271
    0x90a06060f0c1110030605030708060105090601020105130b0903070803010e070f0302030601050405040905010e0105010b0310050109030c170c060a03091401200304030903020303030709031209060203030106030f11040e0712 97
    0x3503450782c68102c0f8450454910400e0b42c60403400a4501a0388100d0081c40080e003501d404a9070b413640541c640d00d003481418050f044090006801d903106210716072043d485402024151502d588030b400e0100c0000b00b44020a21080008c1030100310f03030303101860003012490031035106482e09910080c50f095004111209040c018000c0c40860313a0400c0584040c1d400580740020500355904005c0d000d4041809521125441c150020608101d2400254490603012084025440d541d00c01111540a40c1c070001e04030034031140090002d001710364110703a02e40b0042c00898446c0e031a100005202580401c0c02e10000c01c0c0d80d0090346080141c001c0004100c0c0324801d00811240c54200106881c601401502c41e00c000c0000001408160003011180c018540107401c490320791410b54800b520404003800140d400c000c00c0312075100c81c030344070701741e5403007075a00c1503024504507442d08605a020300080b50079a41443d0722841d20140020844020748000d050382d129501880c00c040801501c5039420410021250b03003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 66666765 1250 66665515 66665537
    0x30605060111060f0109090f08070506011e0501140c031902030405130501080a0201030b06070804060e041d120d0603020d0501021909030c120609080c0d0801080c0916050702090a06060f 81
    0x804c50f0541180d01440001c150712103d03103840b1020140c1d218004003101d002090010a00c140058440d05032400100259441d0000603081004c006607841814006521040e100010170329480c050041c00311024120380c2002080040000009104d13656400103a10100d41004145031031500108040801041003146505060350a41c84007c0000c1c060306047d00c1f034100d000d19841d0001159201c0c2c1c1c21040040c1c680352941c000074078101541400c0c903c5a402c4c1100703024138120440c5680888504c4030001c1610400074400380c0c0b2140c22804814000c207985010000150f110034404c030020611800005944030b100002000445030310507442010011449418000103512241003003e854140304101110855498620094822480018272501c804994a06c00e01c070f00003811000c0510580340c1034641c1ea25101c00c641d0b96510155081d0b40a03400d5000300d4100c0e6003103131400885000305c5c6002c0b440c4c010190089889580c05032854501e443e0384480c10000e595001c440c00c032800c03442d8502000204 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 66668015 1250 66666765 66666781
    0x504082e0b011b030203070c15030c080610110c04020a03150819080d021603020d0806030c011d040b040903082215020903010e010e0705011b051203040510050103060506011106 77
    0x141d4101c83c0304004a9040810405260082080d1545585c0c0051151041900d443c250055003d8452200b400300381403c1c00300d120305002e640d90600ca00d80107030001142402600080325071281c589040d100034040c6500074107041e100c0e4001404c00d14215103000c2203203500b01c0041204000035030306c09030581c4c00480f0074820718081030354542c2100e41c1000e40b41c0d840f0a002007140c1c000344a07415511000304003681034481015000308402c15003000940b140d8105541e03680525880c6c0c001010b1b01c1c0c2c00100008030407100c01082c071008990741030b40903000203880741890000c541140c0580105402190005040200103110103404040c840240248a68140040c2d0b46015401e00c42d8801c0303034940c540100c0c2084080c2c40941c804242c401c3c980780203101e203254408111b81c94070001e01906001500803000ea2000e40c003c8841288404da002c4018012598000740c0c0560390b8102a004840c40d008544002d8007030310781400741601850184000007040d04003038001620b4000c682318521000d4200004110a00b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 66669265 1250 66668015 66668027
    0x110d030e060315090f0403020f01060f120302120a0504080d05070f0809032407090803160609171201140f03072105011104050306130b04060c0504082e0b01 68
    0x411041d07070391507100d455106040540300b0282688540002c0304400308280002e0001d502c0d40a54040d400361458020030b02d01440c20303144c07680281c0380c0c124480002007108003010425010310f64000e00c1510300001181d46c0c0d1248030761001f500c040004001250605c011901481058000560b50501500d40348551307407601c201c00c17a0f40c10041c1200902041341100c1c1d4a0034040310801490160b00c0d14030702120034040028180091f154000040e60100d404500c2900000031141c0040b2510003003001200283c1d642c00160a05070310031101d5641011031407000300440c2c006010443c02c03402c1d581d41150306194110030400c2850058074030400341035648590b2500c000c104042aa900b00003507a500504902c00c00c2d030a03030b10f00940140950b28000f07138900a001c0071030241059407400c80c01e0340d0007625900c0071380403d68070321a4040e001d61b50150219001a220360301c40e074041c0d801828158201a170340c0211504060000f654811000801c0c0c413400071500300d80c48101800000082c0c03c0180d018140002014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 66670515 1250 66669265 66669287
    0x3080d0e1c090e18060a2f04031401021b010c0f050412120207080a08071208010807150306180207050105060a12200406030507060206100b03070806040603021309110d03 74
    0x31403140b00e01140b01c485003d1a5030890139502411070380e075030500d10381c0240203290031000c241c02180c141400c17601d204005540030f2005500d803159503040ca800c54950742000c0080050001c210365081008401003c0d42c101c05040e0010002d00000f01d10000d100040c002d922240c00700800c00030b0030002804040c0d003544540144c4c1d5001440d0064018500000741d00c0c10f07c02da00040014810580d1510401c01c62600411a003840703180c004d50050b01850055500301000e000300c1289030031441c0c1c140036150f51801b0f110344d03030051031502040459030b40c055005181029a180c5881e140c00283e1203040c09402d025580e042a000e40b40452aa840c02d15500200340340140020178802501d4078902041800104c0c500c4e00342c000500801200b80c0e00d180c0b195885009116400c0507000c0c1c5800102d8103c4100300c42021a6400c004441c91640e85603001c651030743c4004c0c1400d030b126646140100240c0c80b50341800c065103070760000004001920381085004c40840e0001c89100c1c00d80c0d0600a00001e0784821003001c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 66671765 1250 66670515 66670529
    0x2010b090a150308030a0e01060905060603041b1503060806060d021302090409060203010e01081c05120711010e030301090b0f0a0504050c19030b040b06090f01050904020403080d0e1c09 81
    0x148003800b0388080740d210300d942d03002819502010042c081d141c0c402d68030903080c90310280004c102d015030780e1070f0981c00d03510103e8455500440c180300143c086030385040d50390280580621a00390040e200d141c10502445007443d0352000960b110030500260b141000740c5901705504070307070880350104264005000400003c5034101003e0b0045803058954071203400641156a01c040255125038403400900f108043c24803c1340118801c82001101b05160b448007801000c1555491910f070411030b404200c194a800f810140805c088201842c964041c288120a0944000d0300555641d5141448400585482d054040e101d0071030030f255940e5a43e50800d604041f0b50701600c0c0031a1036507a44011400a010344441c0401805188940140c9030740e060b032040e500307850121340130084000c5280030f0101c1c600a8800c031a803c60203103070b80e1280703d41c050809054501802417000d4a01600c0b655000b007182c04c0301100028142e210f04008403001803e21103420802280241040c0120f9603c000403caa007592203904 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 66673015 1250 66671765 66671771
    0x21010e0f0708040c03081e030a02070c052b030519030504030e013b030307030801030201020d0e100342050909031603021204180506060307020a02040b0a0518010306050702010b090a 79
    0x908110f09120040c4403c7c1c00c40d0281512132a280120901941c820301c411200e81e00e50300400f0401c0c0c601000c032220011900d0186001d01810402c483e14041d120410980c28000c050140c200f020310003041c4000ca03441d099030041032904261170084c1195200d0080035060010f11546841050610700b2200240c481d8044000c091074144001409034803070203881e0503003601000841d1ba05060300003c94a048900c00c0c2d00701d80380c9007001c044c101c130180b842e08501603000e1701c49900c1d44001c1c1e02c81d81107002c4480b0282a10900d84490541c08141c410703004111020b4800241d07103503041750340781c0a50400140004d45502c2c00910381035079038a85a12484041c8403440c403a211055051600c00c21010300c0080700c0d44645951039841c0d844168643c503c20003910611414000001c1807800d100c42901c2c080e00b6140c004103002e1180f81d0802015285915016401c81d0189a0005180e40c0b061118000400101003c544a504508040050b2100280800305580c14031b580c00c000754541c0381d1020341c4580d800c8000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 66674265 1250 66673015 66673027
    0x1050702011b0203030a20030a0530090706030b09090c1207050603070306090e120f0d090f030306030312050108060103020906030a152408030f21010e0f0708040c0308 73
    0x503100b2949041070103501803201003040340e00660428421785000b0003114050701c480c00c010100541ea4810086010000340382803040d010032001c44250800044040e8226401c01d028500001031100e00c111004001580310030000c00042d50940714607003205030151815034407440d0000c155582c4904d03100e01c203401803404206040560005000160145c000107003107035a2070400c420010040e142502131500c2c02c0d490012040440d603000184007003001c0d5614901401e24190404500e91030b080002140110340c7c0301c0100d0741c0000c1c803074400e03043e2242c402c2d180080d1250650078009c08401034800c04000e060716010040c41080e2001418904403541141c00c54103a07170714003010030f003000d961202c0200300031031a101c0d52581040c00d4204c10601004100e5902441031408401c0047c206d182c8194041c9400420900128084140003000c844240f1104002119071440180c02003031026070046810847c0741e0180007064808800c01900003a0522301445541400c2d2180ca405a1083c030008105d1a40000c039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 66675515 1250 66674265 66674297
    0x304140d0203070905100e130b0106030203070c140708070611031804020f0705070e1303120522080904050c07211e0809070e090a030302071106040303030e100b0105070201 75
    0x30fa0000b6080c90401400030703040c0041c101c40d09004a010b400600d485400004001c48a40c2d040c0c0b170703490390b000000d4001c0d81c0d203016000d41c000d6001615003003c001a1102d05004030340200c2144100705245002048900e190021032402e002654205104101c071108205410030000000c0e2a42640301d403c800d44090207480c0020001c0c800c0a11a0288a00c0407400005000001c0750170003c07a00c40c4426080150780308041a000410801c4004003ca00031000454185040d9440340b94822000d50030b080c0c181c569010311a8026814020480c1c00b03250006640b43c041c00c0c031b80140340e041041c000d0194201030003a6500200381c6080e0200341c99810502101c46980d40c840c1451821421f05004c11581100014400410225085407084400e01c51418000394102c94550b00320710a21011001d000880c441d03550403006540659010741c1c0c01403031123807080080d580700307002440294401d8031b00042c01020703251042c2c140800b044000100600d0714a4200d0b03640d070082c1c22206c0081c1d0901c0c242c6045004248 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 66676765 1250 66675515 66675523
    0x5010e19020a0e1e0114160f020307080f0303100b09010804060c20030d1407080c0703020304090c0e13050106020607050903010e0703240507020a0f03020c09090313080304140d0203 79
    0x240f92a400465900502000700c01011440368800003039071110b504480262601129105440c108407030107000d62040301c082030705900e01e040320506c01070070f0711040741e681c2c81801d145c401e600c0344003400740e000007041c81070810703400d070451006010440f049c40c100a071940019210f44402030001d0a49510381008407000c0e44110340150f030407400399014021110b070507201d10341c0e06c1e0820025010070328604121038000c42c081120a0388070305040e80c1d0f001c2640e96642c40c81c2c4d0103504a80411000d501c4107210126420202e800741002d0f481c030039501d0400d403048001c01c2024508102c0c020420052900005008140d03000c50034542c00304550038a269100107000110b80103149114000041c3e00601c203004c41000312055200b440c0241844112020105c400d41e2041107480507110980985c1c400c1180400052074140046540c5000b0f005988280c0407410108400000444070001036400024003124500609070802c002382030120000c505150902c1007442c403a0319140c1030a44900070300ca11603811503800b04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 66678015 1250 66676765 66676787
    0x8010302130f1d30030a0b06070c0602060f060d03120b0303040e0109020405040e06100e04020402040909050a02130c02100e0102070816050c1008040b1005060c0a0605010e19020a 78
    0x1901203826070f40b4024181d51983e00c03203414607401c08100822803154119803003144800b0400c03114010724689a146528000704400c2080541141e030905c64131004c50702011010009182075005810300f0b10740841c075801100b00040409205082200208004c664020391003c20b09040090003e40c0ca0b1007940000c1c40c50003580c1c00004000b000300000314803040141c001d00301f00c0307200341d40902c2894100d11685440b50302c200c1d01d490364103c01c00300c01c10518004440b256081400503000510f081d407a0740860302074031100e40080d2160b0f0301408518003141409010401881e40045080108003400c4d2002074850003185400001203440d04075201e954882035040700c1c1030550000400380d0f60b00c036051030980b0f00c0140000a44060060b180cac80a0340d414485001145002150f840001c0c3d50380e11b550315101000041c065030704051071b4517404101d5844d900000e028655043d00200602d40c003d241050079268143c0004214000300420702044c04800c21901d03000c41c01c482070141e01c5069114044480885034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 66679265 1250 66678015 66678041
    0x40210090b0f0d05010b0415030b0105070803040b04020f0102010209180a0219180f0509010303080a06050a170f0d050703050304150515100c031b050c06030403030b01090608010302130f 81
    0x800c001c1c0000442d0007072410400d403403014440d43e80d892406500301e0051348030340540c0e03202c540c4001f40300038425484050f01a41c141841814412251240c2c0c1058001329011202e074040842404203500d04009030f000c4405c024802580381243c0400800d000c0c081402c0c04843c1c2d01c140b0700101c0c6602c0465010740d40440c00d100b50790118034500e500c0041400100101903040c150050300040f81c0d50302000200d0b004d455014110120603465541c00b1160400000c1c07400c543c280e604c40c000b090a5940d1411080140544040d030369904004150960820440c2031074503541e540980e00400c00d4a42000c16078a0705e0342c160508035100e035601e041c5142c810305030048080c03866141c00100b000e01100300e00f03c1d1840c0c01c07090b0303a840384408140000707503645c1d0200c41c805400f1840b40e150300f0038160090395080300d4103440754050710b40c25117180c40890040c1c2c1080d982140800d4441840000130759010400784000c10403450000990351464000c0b030303645107100301505a0a51100d1085a40f02c0d41034020220032846 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 66680515 1250 66679265 66679267
    0x1b060403030b150f04060509030102070b07020706110a0b010e18010c02060f0703050907031203090605010e0105030f1f0203070908150a050907080309060915030408070c050409030206040210090b 85
    0x4a440c006000b0320b011040144039080100852040001000544008911102c0d03920300e0142003400607101d580000e070186900d50b4080101100080009009034082d0080b83c006244450510703034041c200540108601100358072424061000c03480780301c1801e04465803000321103920303100d13920000b6018080c0300040c00c156091680c1c00f55000c0d0b000030150721501c581c14207614140c0703442600300c4c1520300590f0380380c05940c06040c003407003ca5101061000b810569040009500c0b80542d6643c007580c800740e110b501c1e0094050010099410140840504584401c014100e010039405032009021031608004c19415800310004e48218010304080001d0840d0300101d6011a114180000e1b402030200ca40480940c1040c021400301039000455000b540c2602000d1810f101e150428403090360081c40806500c003198500f1840c01400c1c0300020350003180500707112592030384035052014140b60b456000c2d600842c90031402002095003c2551600594110b52003641151030400459002d030544c4c00002880700 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 66681765 1250 66680515 66680521
    0xf03070807051f0c020111031e07060b03030a1d0409060e030702031507020c1e0a03050d080603060103080d020903010b04150303030e15041707080403030309020130021b06 75
    0xe000441d03108491040702c209010014036107126040c040e803e41464049100c6000d213400560154070381d21201c101140860b81040301b58288000c10300f0a010407071485010028101007402280e00581e00003070415002945400d11510b00204442807031600b52150306c0d10006d140c00207681d203410101d4115084401800144c0042200c0c0d0b44a03409040300324428890600814200188480c115214034403d40260803c0c0c8001418480010060500180c1994a41c10a5106590341d01e000f4009540901e004180750b0803d01c1c405012103102030420b034403d900080040000608010403902c001c029200c01584412542b00485d014004100c407182d4080e042c158110000f0300444612400c6a02980d014001c03908005a03480e15440d5081e501e4000e140018000390220300c9101c81d01405d034042c0c804040ca0401c003625180a03076080340d00210000703a100d0849600355a44200802c03000c0d540d0b43e2000003520b07103041700c1041103588400c5e10200703284c0200b0906e460400003914421003100740c0c02924136510b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 66683015 1250 66681765 66681779
    0x4080d08100504020f0901120605010e0105070201030b040e03070b07080c04060e01020f010f0509071d060405100e0405030720010915180801050403030e120a0305100b070c06120207051203060f0307 86
    0x1800820000c1d00064010201d80390101449c007910080740c4060711002c0b0b140d4446001103e1503480700030180c5c14541c0f907028070f000540301c2d8441c0e004162000e83c051902d4101910304000c0300c06000d0940030400110805000045c5007003002c0f14121800e50402ea54031101807070042c3e0401c0d5248511344000d5183c114050040195034110510521402d42640c1c503150f181c02940f03411104045d074100c40805d148000501c07904140d40480e42100901c21200d0700c069031458082200d00c0c04075422500d9402c0402d075130080046100d021402c3c21080c01c40081d07803280c40360000b0301000c980c1c0300e48a44501c1039241080c0702e41c054003c241c95002890184d88105881c1c1c810240a02015202100040e10301100c0465040c40031860014603102d44d8242490071004044c201c010700380242c141081150743c242c0004031180e07414010820340740305030a003100c4245022805002d03400d0140ca000c80e000d00400602e400910003040307032000085042852500c84d10781d2400f103180e03100e52a011139054410000d001c1034031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 66684265 1250 66683015 66683017
    0x2a0818030307021c0306060507020904080c03040602030c0705040504020907080a0e030a030608071a030c0702030c060c0109060b0a0501090b1b120711060909070318021906080a0204080d08100504020f 87
    0x4c3c03c062520045003004108100c0403542d25220b0b0740300140060011000525040d0a190b40240c045c2c8801400d2000440a09055500c550b1000c0b025a000280c0c0c0c080281c0107005040082c0401c4608101c00e2030960040303000d4034030090139402000303910000200c0ba55403682c041d254440c468001c0382e46411522a001c0c006003181d0007000c250b880b03200000038040c3c0f440c4607807011170084106011b0a68841000303032051500304840890703042c0291694031880c2e4442001500030190010000300e1780d0400d6040000440d844918040d028007400d150600032a40c128040a08903001100d00035501e60360310481c02c454540d120107000080c0a00d29a8503c441880400b03050154020080740c405000140f041010901c1061000e0b500303c2d00103400501c00700d02a5002d9110b800f400e800c4201e40390003e40c009040c02c0c2400151960200610b17409000b440d1b80001c0b410ba11882440c0110718181c2889c0d1030a60300d0902c4402c142c20099a44001564007844213072041c005c101c068402d41d20344250411400d91 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 66685515 1250 66684265 66684283
    0x30b2d0301060f0605041206020412030305010e070c0215090f0d03170f010515090105130305030c0c0102030c0606150d0603031d03190618081308012a081803030702 72
    0x12070342c01c000d03020500c61a4152003030b00b100d10b162103c0c2d1500c1e01c2e04440341d01b4841d0b100300030781d00b940d424440040e1240b204045000c00b41d110341e0f00042e00c0d40c100300000d80e820501030701510400c08681d0350500140c0b41d9114004201410b24182c0c3d0b21101c8210010301d645640c1540d6070b41219060029034101500400111141c40f01200e401e01180d45103c001080400240328081d0710080d40700c081c50184110314014a91090f040c5070041c90040030204d0b2000c4801c1640c811078923607200042c00c0031100014000b000714150b00740b010398940300000c64801e41c4c51a0240030284500091800600348820b4442103500400d448003040c44042d03980e040140c00c42c1c5c0282a8501e89010b000300005c0ca0380703008140c083e0000c601c1182030045802d5615000c000f01015555503c10840322040c08001c600848047c3c175440d80c0030f8075030558007420403c6007070940c1d03440700031140c00042c191854500c00444804107404101e503481c140b01e10342c2e1048029035160031041041d440310f010010038884a980d001c18902d00e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 66686765 1250 66685515 66685519
    0x1202030a0210320711060c0706020304030302270906031617010605120706030b01050307050d051902070609020a12050703030503070201090b09011a09010f12050304030803070914031c030b2d 83
    0x84140801105c2030701c400c0112240400c3c4801004650300040030350380a982c0150091070014103118000d2902052a010000170110219000811062902e0042c0d5070943c00a0300b50050401001034140c10b0080b8116801040d00c122030f0b482400030032400c00d6000c10000d220050680241c015091010384e1124414010800041e091102034002e55001d8001c42c3c2c0240000da540700d20300280605444d00802c40503001034070107102c0b008580007095040c00a411624021400042c0194141c41000148034081e0b00c0302c5413056103104007102060000c2018400c0341e4050030510740d25030301c4450890051981c140004c1c038405070320701403000c0c1000561106600c0b03280c0c480203203000d0906404000c0811400d200308031100c003401c9030a110488083c4050442c06100b94101c0b0f0800b0f4680d0740f4a603440d013084648100054481008006080c2c580500e2080101d06902414a140d00c0d51030300c02c2c2480c0c0700303280d00c414952912841005521140e07440c2881e04017208a07070740c510040081c00890082d1040082d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 66688015 1250 66686765 66686777
    0x80c010506010201020405090403030c0306030b100e01080c0604030308070c06020f0702130e0c0f030c031524030604030503150405010b09030d0302030f01030f080403150204031202030a02103207 85
    0x14210b94014400c0300e003582c900800d10501d603900d03681c0c2140605810794002c810903482d5000040000c1080180c20b0184181c0e144540304981807003402844084164007a41f11580a64003a560300c0e04c546007118256601483d00091603034030034405550414006130700900c014030009002440154200280c0502c83c0300300e4a0070f00c400c40c0d81100c40f0966085582e90b59464102c00a01e03000ba00d0702d23004070502c00c0400307002d0300c109500f440002030411140d480d803800300c0004801001505090100b904011018102011038004803400c04283d0b80c1e00700030002000d01c5000000300300c0d01c0ca0301d104041d0210a00400c14080c030741c6c4595449603e5001011924000d208070764544103050300900070ba0703100324080001c0b1001caa00c0c50710307880c0c40c1c16103800003500c00345820000880410845020f24200030110301d03015940394514079101c008081088a800c0442d0018407018414540c00710344071201c05404100403c8152003107071404194060201a511580075030500b0258811b49121080e1041005032604 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 66689265 1250 66688015 66688021
    0x9090e010207110405060103060b0d0f050f09030d0b04021b0f0d110a020f040209060d0b1302030114010e01020c040f0906060b030705040902030c120903031603020f070f020303070f080c0105 83
    0x2040c242e0103101c400501c0c00e09000c1440366581400d50003a54481c0051401145441d551000c0e00081e40c40441c1c14207415499480c07d030ba50032098004d468114520403401c007282d1030000b151941b01d0103880e08485100307840e543d40701c2d040c0da9160160307450024464407080c201441d46110580d142650080c507140b0307000b0340d50f01c1180240141100c030144081840900701005071542000303904a1003002d01944a5401d10139480c4a03103d24024207044c418026000901f03e460030104100419034143c0030b21031500400060240800703010303138140c030802e0a0034019110f444000060307007001014850b640d042490302040c404900010342180320000d001341ea0802445495400340f101601c001c550000101700c0c204820401c4c1e04140d401942c2c09a01002d00504290722009900d5103200b09a8014200e58404418014100d0030320043c45100c07034075030800714902a00442d02680c68010a0409000354800d04080f40c02d64606000b12080640d004848554000741c0d0b1800c800503803c420680400396103080c0c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 66690515 1250 66689265 66689291
    0x152706030d0207031e020d0c06110f0606060d11070c150e09070f08090a0602030901140a0204080d0f090f0609030308060f0307050d170f0a020d0206060904082505100b040501150c050f0d0909 83
    0x40e25000d0dc0010b00b00519102000b15120f000c0c1142040c0c0c0c2d00c3c2d81d001004600c012401c0412114003500021714021403007414000000c02c6102d040501e079219a00d110244005903030000b00d144452892030500328603036614000306904041905070003030206030001040180d900010740c42581a0f00446400e5485a1203030b101030001c0740503c0c000c03048140c1c0070025418600f8040e098035014110549007958030103440302021892400340381d00c500c001c50052281441015007284080d0b900407800e54862180c400300b100029a10422482070a001f805c014120720700b07020b10440c2e85030207440318141140c0d0398000f810b0f041460358419100c41c1c0c0140641c0c9852034270346101041440c0944c04c020007a401c0da49a41d1120100c41e40420361102c00c640081c042e0640022406405001c032600460142003c4040003031098141c419003182140308030328200060240d00100010b4011090942c50450700364444e92600928142d40c42d0020034081c4502e011029400b580860384c182074816900c270920200840c000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 66691765 1250 66690515 66690523
    0x30507020d0c0812060312070b06090c070209040201030f0f0603050d020c030d020606010318021003150f0602060103060f090c08060709090c08152706030d0207031e020d0c06110f 78
    0x10002c201200821003060f940661a5813a07030005801019994224030b19103070000f0940c080d0300101c81d006104010010b00b4940a61816409260401818940181603000960b1482700400c004e06042d52000036111290b01a40024045200a02c04119003900c3e030408996a8460005010042c400e0b210684403034200455084001030303030b54004004a44524006401030408440c2902c12050291080c6004d031343c446c00c5110140d46170780c400040d05c0a590120305010352998203c696801d4400c18200003d5500040c03850449401180000d1a04c5901c015100a1b21003a4800342001c040144003003203540c1c0c00300f0b100b40540585d484d800c58413940e0b4500402503070034804506010488020000d4200d880c2c10a54100a40c00101a22200c0c038a01d1340d030f100f00314074580c00484c8200c1c20314100040c07418108000b423490034990009015040c50b56441c41028071a01201206d55981110040119122640078038022680401c0c608413168881c84c0081c06000541d040c1c018510602541101b070b25400700d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 66693015 1250 66691765 66691787
    0x90a08100506041521022101051f0e13080304080d0f150302010503060a0806070201020903070b0c1207151b0e0a0609050d0c05040606020c03100204180e031603030507020d 75
    0x3000305411600c0c1c1003100c2d103c3c0082c94071784040250840880170050b80c0e07880d01c01d145001407151188035103010306d50300750843d9402070410580c40b0000814140d010303508401c000c00c940c50803051100030b60301c03250100740b909082c500081180b44040203110410240c540548107802103214100f0882b15400c00340f03415510940b403007144404840c00f090003d544150000c45c1d2002001e04200b022660310b290251410800300c46070700060b5030104500c442884d080c8003280040092211090a08100c0c601c2c29032600080891080e0100b000074103641004918800c04000080d41e85c010084240a40d1804100c00230701003012000940e80c0174040c603d40340070750345542a42c80598580c04828140f00032f11001c1240c80304280c40a074100040014207a0380c3c1d0207042d011b0070095003d05100814201031502c0c01c1c610312406900e480c01800140a45c10b0f1814451090800041d008140c1c0e4040401107401d51084951070059400800f180e003041c15051741000c0d011311440c4c5e084580e00905000c084464204007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 66694265 1250 66693015 66693041
    0x91109070302250624050a0f030c0e180303010e0a0608061302010305090109050f07050406080f0604080a0309080a180501020712021011030a0c0506010e0408091005090a0810050604 79
    0x540c00d6440043d4111021000758821000003d00d13440c108490012400d07150410011040c814000f40001e04045188900070100f160012880a00b503542e2264401010f0044500c80900000007846600d420000c5189002929003034a640f5615003101074030f0508221245890103051810002e007003400090b085108050b0b0071428003207110990b0044000d4007000c3c140c2400396403140d100002042d0148403007460700003039500400d149031910050000ba20451340c0160702e160400d8000c40700f0014041960380c0d110342d0011a0b25903403a2040415801000c01440c040e206d400003041d034031103441c0c01c40b41080e1604040c40c003800340365075940012030f0b070340905000d07a888040034180600014100142e2003904034207075007001c2203040c550f034030654a150416002007000510303a02e681810706c541885000e02410701112f031402c20785042d40303910800388076541c1594042c510090a41030b806105806491103948010a40003810b651040525503c08070b08030051040f900e4940031981d140303001e11a02c0e040d40e0003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 66695515 1250 66694265 66694297
    0x1005040501020c0d2f10050301080618070b09150a08060102010f06060c0204050a0e03211b030708070e0307090e0c0a03030c080a1407210801030302070b09040e01091109070302 77
    0x341250002903403603920604101c111555005c940d40e0240746120300c00103981e84980382c0d0702d04020f080c5801c01c003900507081920f84850b0200c0c50704020034107206a4102810301ca955406010100b950303180e41c1e03d00d4500010340404d5480c00d140c0d1100d84d01d030050100b640240860a20340c4901c41c00c0300d020344120700100d4900c1e580c00e001402c01d900004e900000244001400c1401c0b00310f01e42c06d5501030000c0030f141240075901280c0f20b4120201d103d82259250315454440180700564070036520001d0014401c0c0a00c4000040c0300c1481a904130301005006010380f100d06079581c41e80c4010702030b0740440b00224003400c100c11205003480381e902d800312034141e61070640b10480758681c60780c10341c00880300500704003403002c12025015402c0c00518209104566800001e980d4031324003070418650003500004c1010710401000483e90001380d1000755008100045d6507013002c8030018000f4215200700c01125420b0810000034000e031007008020103a81034480d010345582e680c90480c1203100b100e140c7c03808496 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 66696765 1250 66695515 66695543
    0x6070c1707081e07080a030207050a0f0b07060203060f03152a040302150d020313020f01050307120c0e030f031b0a120507030c08070b010305010605040b010c060b010e1005040501020c0d 81
    0x4044048050604041c1a54401d548070117041e8104203030740390300f6009603102010400160030f0103088400203241c00440f1016050401900e10194881ca043c050314154020010604aa0f500c40010540f81001402c07a0507400b804410140c0a4100b112820350b44500c10319901c040700e010034050382d0400e40d01640c030b40c030b85400c640c01c00440700100144002140d1060017004801002c500c01507020b000c043d0901540442a44101318254114107030081c100320b804e20130b00140302d4101101003c0d110b00c03414003050280b80c891048885c001d0300c0c0314965152058030074554500c40c001c0028010791404c10304c803801c02d100d0b8030511580d42003660002040c401000400703501e110301c0f500181283e50300c80e1034200401c1c00b031601d50701029041404181c604113403210042041003070911440d4005c0c00242c40030301c0210300003070000e402c00b1455000a00b2464079079101c208240e1081c1943c1420a41c0101128039000c5211401445600309001d01c074090301c00c42c02e0740c54503490024080081154402848401c5070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 66698015 1250 66696765 66696793
    0x12071a03040614070e0a090e06040204050c091c0c050301060503120c120c03090a0602070b07080310080303040b0f010803030112111201060603091505090703020d1106070c170708 78
    0x40d10051081e15819030328042e000101e000a040c150141c1d00c0e40e036581e40c4401ca09030070000e0500240c1e1002102034074082e642081400c0204145500580440c2c00260740d9440054032082c6108001480c0d50111405e511012406000b01301001d00b94022a070b0303031071131325200c600b414200c0b50345001c4c090f815400311004150080040c4020281380c1d6180d8161189141c1005402c0350b160861009a190b80e0408640320345c07a1b0030454291001010300707100030003000745858500f961a02c50710502500d00c100000015a11402c0100c10500801c5420100d1390740b8030b030506000042c00b10070351300d148070000f418000080448001098038141c0b90100c615a41130205a91002103030340c601803500b600010f032030f070800380420000e00c2400d005000b1501c011402403114607015414805105001c41c40302c3c605000d0009c4a80c00241c094280d0352b06840a241c4401c941c00d12503503c0765141c40e5039911110010b058400c018403807420004483c0c3c140002074034031340300914480c0c99200340d00561440e0341c042c0c0300d0340507a2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 66699265 1250 66698015 66698017
    0x1050606070f0804030203070b04090c0201060e0a18050a0b190209031e0c0a060807021002040f0501030c02030d0f0615020c01020c0f0607060609270f1104020f0d0b12071a 75
    0x80d071083c00600c1c501a942da01090400c020381d803001d22481c4000c0303800c03c85d600d0f05008040002c0d03403e10003002203a0600144400032240648203140240ea181c11581c0d040c801e4448684000b0340040845000c0101450301015551044039019150100a94519900030311030081e1080721400402a01c10700903100500310001c1c801002002041c0701e00400c4404507200c82140502a01e01583d400866207800c100103485d25100d2018111014810401000704503c083d407010290303542460049824000c0800884c6540503019501e1081e030310340807800071207440a52005040380c04088d418801040e050a09a8561003071300411405a04098418840d40c0b428000c00c10b031030745004001605140107601e5010072114540c10101540d5a92032407030307544c031b8400805031005200010401c0d1160005e40e43d804486034407002e005208044007017161401c1e5559405841d0001c07003050740e440d22001d4805031a00074141c81c15004d4020702c2c20070301442211501244140036125000c180120034541110f00e000d43d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 66700515 1250 66699265 66699293
    0x7050103090215030406050603011802030705060309210406080c1c150b0c100b090402330a030906050a0608030a050306030309030d0f080f10180e2d0105060607 70
    0x80705040f20100541c8201400156000314014080020a441c3c01e505042c21100211080d4040005004031400140d90004141c0b082d294281c5820340caa84806c036416281c0400c0c0d20b1440e80104000125600003160500508100da0040d40c40c66425280c9400c0000d00e44540020391414a110766402c00710190350b80c120200342c06014256030805540c1d622244c0440c1c20035601c002c0d4580100c03400c0702c401542402051041602100d07aa586420b03d41d00050750f0100c042c0030441603078a805200f02f00820070042405440fa000c40400c0e558030040b20006009051380c1e68111101407030b06001c14061640d5103e2142610710b4800210301d0158074410550320b5130001410550b041c4010010700007280c400b8000344403401801c0d11400018480c4101c003802100c80209400000e42d001c0080020400300341c52810200c0d0419012988020038042c0d03044042c10b60200c4d1200d003440382c1021501c6400e0908019410164244c40c0125180031003000b060980c0d070705460386a0701000c10301a6502262640d664112 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 66701765 1250 66700515 66700519
    0x4050f12100c0e130507020606010c0501060e130311060c0f2b02030103150218101205010609090c02030f120c07060905031b03070b19020c0111041a0c070501030902 72
    0x41c100350307809016a1005880100021490f0003902440c3c01d011144c4c14075603803469014000340c50250740095407010001c214504000141e2120020b0041c20340c030040181640032020303d424a443c034000503128200b40301c22000141c0b000460f500030080801d07428000c1d09651404c41c9440700300c03034041100c0d411080a0400450950070614440d407444190f100c01c1c0c11810b0005030b129032560811841c295401e410030000c070b0340100101300f81c1a980b2944000c03060760894114809211441c0125041e034217045005a02500d00000455910340143d03151040300c450301000e001210f4446004c0384c50780915025680f48010074000c0000c00d0003603101807a40080d0085115003031904a032109001e85120303550585284c1c000142d031621072002e1091590071011144015460005a83e9541c400240300519084001c50300310742800e540c6e5681d404450803805100002d0215800300c1038441c4603507000e84625610000d00d5001100085250000d4450320307003141000c1d000491400c8015009040b480030101c1e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 66703015 1250 66701765 66701773
    0xf0a020d0e01090c17030403030909091104180c0f06050304060203061930020603060d05031b0f0c0301090305030106121b0f08010e160c0c050d0b090105010b04050f12 73
    0x740c0c0201c02445580101c0e0701809004035204e10305800b040c400e040f0020346035003d8100304403d00c0071030740007a4508200c1d1001d000020b8440903500f0a034402124000040d90300030b06101d2811a400380f0b0180c0f0b62403080c0282c084582d0a5514030f01c0d03078144040c1d4810340300851800c3c00040e000c941d480c4d01440d4403190107041400e0f0402101500c02581c9031300e40141c0a18101c1d19960000088031070200444068400341c041c1614250750000b030024000144058800d0800c1480382080203400d03c04c0c2c40c41380400b0100d0b11041c41c42945a01d0721044400c40303000541c1302e10180200c2c07907e0140907618115400d512034070319603401c0032421200a441030503200140c60722190070a1038040035000c02c07c440c000a42d1040e8a444e81c0003801068104181d010302c0044c5070307000034003d00308107000e560900b42800c0c0c1444039924a051030003600013641d03544900d5200c89950075500500c083e01c2c010310300c22850040200056038890201100500550040c40d4001c0c1d01d00210402d40d003040c201c44441914550116 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 66704265 1250 66703015 66703031
    0xa0809150406050d05060303040302181b180102010f0213030b070509130b040507020115090c0e030703030201060305100903020d051b0601060905040c030e0c04051008010203090a0201080f0f0a020d 86
    0x51030554440d9019200040b800150075503803104610600d40c00c031000310065450a89103400242110540c0b0034410070405401c004104510700d0f1006d911b40c2000944500750b10b521588100404d81c1004e40503c41c095401d2400c0080c40310401c2c0301726286620003200d5502e80f03a040d5101ca0480c160001c048074180182040841c24070356400d0070404400e0031540340401d0742000b030310501c01074650250042e03007503a062101182e0b20b0018061710601361182c0c0c90300050240c0030040101c0300480302c00c0d1415098010072f01c0110a240d0306400640580e80a9400c60b460001000c445c04116003117044043d0068208440c05a041403003180142000114107100546540d4040b014908100003a40814040b4081440401103800c29014483c60524142410080303c00300301c04841d118040c511150b44159a02d03400101007100700e604020203060044001c40d100c2c42c040f42075039514980014264046009100001c0e450b4500010803480f44240f106104016203401000c00040d40105c40303c000d265855200b5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 66705515 1250 66704265 66704299
    0x708030a090204060e07020703030f23031f0b042102060d0b010e03010e100507030e120a0e0a0302030c1e03010c0806190b071509060f09060c0806030a0809 68
    0x165018030314014001440c0c008520420045800c107503c150319a181c000c0820010f9500429800c003100d4050a1560340e0010324101261070100108030300015020002c1103210107450000a148074582d0700701030700d4191030080c80b0081d003009580b08010110404200c1070141c03604181409540308005140300d0a000b003141d0004500780c00c1294440445540c8400d505130540e0b1081e01c280b001413065000f00f0100b001c40526544648001d0840501030b0345640102d4040b0380309510180f155018a402d90310608613000341400306034026498040015a260450592440c208840700202d03540100103020030740007401840b002c100c07042040701d0003071020451a01103031030a019a02c1d820f0b01ca80d8402c50145403500400810340d45800328901111101d880510190000c2800c0352249034102003400d0714445031003902c001411403910f00074010f43c14185a00c01d01003054004051583c401c40082c08401d8804004a40014007180c2d460380c5980042030301c0c0c0104080800900c200e400140600c1104494019 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 66706765 1250 66705515 66705517
    0xa06120605120f060106050a0c0b090c04020a170a0204060e01030f0e031912020705070302120a1203050a0b01020c03190f0f030206060306011703040e0a1d030a02070f0e0f0403050708 80
    0x1000b101a40c00000640c01062010320603607014110509049003840194140103240355034100d0000c0800c0c0b01900820f2400004009920000400510a554405032110001c000f80040801880e1020080010540c00d11160081c1d034141d034440e0b655107002c040c40c980110050a0180350980d101a6290702c4400e0b500d0050000300040c07850b14102a03007620744c10b4801494080a80c803820074071441445003800061000c14030204403501258003001c4004407c5559007000403500004100c0701c4940309101c05c05030035401c4180b056882c40340c10001c0419040040e40c40b58000c034451903250300314083c8155880e000744603c0380440e003c0c0802052034822035803000009403900c1e0f4150050b81c41102041610300c1e0800815014140080c010945007080c4071105a880c003c60090154012906000480041c81c560040700d18403081e18850507983d01002450303440764010380343c14005004001000c1440a1914140f0048890040090300160340340170703403c0790540006c4c1c0100d0030010f080142d440841d000740 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 66708015 1250 66706765 66706789
    0xa0c080d020903070f05010e120d0c02060f1201061202190809030c010509010f0b0a0b040303050a030209031b03060a02090102061b040503102304020303160314040b0403200a06120605 80
    0x1060002e86901b000b001500300314952002502c02c0c9969000c81015010124034000c6110a82c10841c0c00c41405e071000034824058424455581d0300701040b442d1f1408508950030f070413100d0b180c42d60040c0340c41004291059201d00c01e10844032504071000c100700719124148003540203c1c24421f0303134100941b804d082402e464055030313490b156a4403580456140040f81c030500168810450b404980c0c0c40c5042010a69400b49120207010312501007402c451040c06038040784c6000d04020240c408a10041d008070252402003401d40e4002e210b2400041c0a075105403003150a03d400580003060150382d18256409598024555023028820a001c00500c0d42c1303007040030507000054a14003142142c20544075100b03020150110000050b1108240000340c3c8021040780d008075074507400342842500604050341c11140a520118000300e0024001455002e0721f070140040c1c038480c0c030b030a14003c44961070b610f89140d086482c20340d008007601c6080143c01c4c029042c0511248081c4808140596520006840b01d0021 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 66709265 1250 66708015 66708029
    0x6150310090809090916090203060a1203031b030204060e0f03010e0609030a0f09140603060f06030108030702040b0a080718060b0f0406020d030501060912080d0c0e030d050a0c080d02090307 83
    0x201d03065400740380100c41c4c90b6009410600030b140314411440d80c00030f2031001d482085002940000490200e4503043c40e0b0102510040c840041850480c1c90010020701c094000045010f03036001c00c4a000743d11a000305c400701d55240d40d801400081c0f9108000801c0200070341c1c140c0c99940c6041540300c408091081c2c1e0306c9140000050354541d188200080c2c07111400c3d400c0c0c1c0c1b04029501c032060202c00080d0307005020314003066544a0b200e55841d80424418001c68001941c0803001200000706002c00000520103a44251402d01c110442c41d424811214028040c018498028410500c00c1c46194451021100d40403880400c3e10341d030b00c0e50346c2d40055101d4580307421035480010301441150780410091210f1400b5140c1000958075000c002084180705004003686000000c0c05401406030440690b4001490070500700980030210801a01e440c40c8651020300a0141162180700c403070065054404500b100e44885414184650b1021b0701a407001111250f215800d1260100c036840802200000d0603030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 66710515 1250 66709265 66709267
    0x20c0d0f17040804091a0306270102070314030604020d090510061d060d080d15060306080c0a090f06050310090c05011403070e0111160e100612050408041802070204060512061503100908 81
    0x4659550307088c0209d01003545443d03030041147c540029072040c400c41110011007001031b103039102c3e600001c0c003902c540000301c1d08981c01c10000b002809008907103d84080070355035082040503a00d8810310840c0858460201145000c41c00043c818100345105240c0d00388250291460042c01c0c4400070100ca0031120b46c801c00d051100740502985416100b5807000d042c5e05001000305202540000e1040442802001880e0751100000c4051403a16040708001d00002000d58181c0740c5101100d80040c08164801c1c4c442542004000566500802c0000101148200741905c1c6984480c0180d408070110200941044051524911000c400b40969850351820020010005c0d24100c141a4114405060724105115064040141503000f841e2414a05017503200030035196228100580d26024035804090801c00301d0350307040d4101c40154014458076208540c10001151602c05105258403204514030a0341d01802c046890426040100218104000e0803034a554000360034040980e100c0c400111070080c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 66711765 1250 66710515 66710551
    0x1030203060705090916142d0304030906030209031608010e07050103050c070f0602040506030c0409140103020913050f1204080105090f030307080703020c0d0f17040804091a0306 78
    0x502030020790342144042c40e1850500840c04005102c50a0192076071070085e49486200c2070882c0240300e0404581c185030707041e54558000e00c42c590b020140083e82004108211560042c03171007412000e4a0240c1e4140e600c0110440c28010709078000e41c00354a130140d141c49111380003a90b201c10030081c1e2015218080000ca50040705040d80d0703242c8001c0790011410326080008104c0030481c40816141210b40183c031a0041c0d440a08185c030083c4150703040b8540040c1c0c0081000041280c54008008440110340c0412a9240300103d0f660001401e0100951161241c80440d6445a001c0700030360106004200303851603160a00001c6140c484403d03007410141c8004242000401403e1041c01d90088050000e410304840b5038003c941c41e444014041e100b0701c4403080204104902c40e81c1a9864a5081c07811102241048140a421203200c2c005400010305030400c0450b0004410020070b000b41c0d0303c441c01c141803e0600760307454050b10703400a10f00b1018000f82844a6655420407160340154440101842001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 66713015 1250 66711765 66711769
    0x3090d110f0406050f0103020a09080105100e09070501020a030309060e07030c050316051c230304090c0507032012041202040509060403020c04200a09080f0d0207050d0c05030312010302 81
    0xc804100502c5107240220410003a1039240da420a0100b0900c2c0060396800b0300310080d00d03034001c990051120b80d80f910f0100282c3c42001380c004002e485070150900d94994510481c15901c1e01640903007801078010016034800a0b0290700046101e500c50580450203180b5145a41d1034025079610549070751510b500108600e040500001c12510910281d21010310708000100301004c40500391840602903044442060009003000d040c1c5810740000b041d01c1d90180000e2403541e07a0007500402503050310346500854203600410886d0b07a11030741031320781da0804211a413403e03029000450600740701c2d0080041846500707070000d0007000504210304c1640c030490000d005001c121100140284140c0d40a0001d0001094001030820045001200c02144001c420082015181c02142020f072a50001103184408590840526820b6469100c01c072290307901080007142c0d40300b045030a2030b40580c00155081c0402e0804041d482081c6016428010f4190b554101003403440d4040c034429030814064100500440c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 66714265 1250 66713015 66713029
    0x5040608010b0303041202150d0203040218010501020a03080c040b070503040e06060427091e06051b07080309030f0a020d0806010302030f061c0501050717160e1203090d11 75
    0x584032000082050000030404240d13a0b1045006546071040101c442ca0115901c42031081588420021503036154101724000d88041e40050307030704034414211014101550b10050405a040701c1c016401002c0b40ca804da10241c40c134103030181010000310410080468103000d403400411042d0303c6030008541d228900f00d03081c110800c0152213180b28040400040210741032042c555001c8021400d00c0001d6100100b0340e600082400c0385000b0451220380c80e41c5030b00c02010718a03d180e4107019040c01c0c0030380e540e5503a00045100810051840840d000c0c07000c540450200c20141d41c0c45010982180e180200c945040350b81c60300803488580c01640404101010154050b9a680d0803190030308055041d401c00c202d440b0105000141110b00413220325894081546290302c03120313480c49d00300c0020465403c0c000c000821100414560f808a0300c0b407000481c4005c90300035518051312b40e003039a6005080e1143c20400c503550040440c40da078039101c14001d201c03490340c800c01c3d2228410312461100003010381100038003400e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 66715515 1250 66714265 66714269
    0xc050d0f02030f0c0a051210030b1501142d0a0f020f0c01030f090b0a05012903010501111e100605010201180611040f030501020903151b16080310050406 67
    0x10990051040c0300f000310420f07484540148071a11510345072000e0f814121424010103e00e0104a4541e200744414210748141e0036080e0b81c05031801e201c1e01c4e540c202a00c4483d680442e1981e001459540e55202d1101d02000680740503d010781c0300d200b42c2004080166644179134140d09d200c0e1030000041441c00d098109101c0324804449001420007284403d1200c0d1300d40040d0401681815150603864a07020714590040095a030b12034014010307400d225100b440100740c02d000700513400246002c040d1001c4003d400d0a10b02c040c005d0f80c814a10307030a24004451112400707901c200c1500c40d00214030845a01031070000d00c00c803100b00043c02410062003124050b01c005034882c81c1564985205900e88145e0b2940800301150004008141116502011300451040d94003030056110180307004010400d0640041803d404101c048a07403198120740007114403038051b9070780303e03000e030b455030106c01381141c92000340c4085050048800d81c0440c840e01c5010103a030089800f001c1c00c2c0115881848640f41511030b13440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 66716765 1250 66715515 66715541
    0x18070f0206010e0604022503030603060605010306050a0b1e07052a030303072f0714090105090121080403120206160212030a150608070e06070305070f0c0503010c050d 73
    0x70140d4900b1164844403c00a0422400f40f03800189803c00f43d0708400000d52044951101807110400505006000300654001210014205203002070590710078000c00b8140c420082020000a161030000781e210ba100903048164031011140d52614461003002810031207026501800180081481c01d9501445075001d50b1124131040130802045c0e01c0000550b90320008038103000861101200301102c0b949254161030403018a2002c050350040f0020890314211020b440340a030a00d00701c0d004001c4180004d00440383c101504c01d00400c90a145d8194440262207018000e0904820a4651080990181d00140c849101c0100014280d070340c1040810f07407202440203004146552401d00944400103507200c08076500d00403000c1030900c0308940c0007491804c10840555010b9581c1c09000c0d2007241e08840340c40c0443c00700d00103a041800c0100841d4907459250ba24145001c1040d5105000d4030700702d540c1521821002c000c00701d00e40d00c00340310b01e111291140d29000e4803501141c00040503640600c81801d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 66718015 1250 66716765 66716773
    0x40204060c1406220c08060108010c02010b030a080f0307052802150405100c17090c010212120f150406030303020309010b0613060f0c0615090b090906150303040518070f02 75
    0x803403a0341c2c00c410711085001d011204e00d40d860106080c40160410190860410350045100000703240405620200d900426900240100b160f10307002c050310303036903402c41c0034000040800c50080054400070007145d210b1228100113090416592401010f039105240d00c1c00030007a03006104121903010130a0755141e0141a030032002603c1c05988850319000100e80c1d0f0512183c480c0b000896860003020245080d500a00722004180703008440950354205449249001d409066200d916284100d002c49034405109a0401c08035210402c2403040c0c1341c4010f0292602501ca000011900d603514010740c1e00540c000d82c5d0250b11f90a000400f607017100d161200751445084100820b00c01001c4811040040741c85506110003002d0a1802c290780720104071038000e080e2458410712480003801240d101041c1d4051080c01c1000c04d030404c0a00c08010026100d0005c244e022900041f0705550213082e0020b80340000d410369041582d02d001141101144a41c1da411320910b48007004103081d4401c041c61100b0030148001c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 66719265 1250 66718015 66718021
    0x609020406090c090521030c0705120d080c0f040801021308120403210509130c0e06070b06040b040e0d0503041401020310060c0f0f080702030d050c030d09050c040204060c1406 77
    0x90081031051280ea806004141044140003081032641c40444006e075081d40d035a41c8070f907442c2d00d8541940340944d42c803481ca00e035601031700c0c1c00c0d0004180140340c2c260307290710030640c5580d00c400c4215041141c006035002d20400010406010038000751041180015940b0140c80c246210103040120030715191050103020720081000c100104a503061600c64a026105404000c9504030360b00e01c19070038040c0c1c011030050030180408002d0340c4810446041c81d030342c52011060180800406100311800900451610710100e072072442c20303900c528040c090007000060b001407200849400c01d20580350794404140f000c01080f050000c001044510450804001c6207541b5040c7ca41e0110079689002da001041007601740c010801031070751000900160010761400c0140c0062a225008d079011031800ca0003030188143d0401c209001d4400d845000807080040d40c14099884103c10062800303080907111403180d6248070740c003600d40d44028406001669922240c400941c1000703c0025203030b04010300c42e68010010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 66720515 1250 66719265 66719267
    0x60307051332031f0207020a0302041d0c061305270702030405010801140102070e0a020706140108100504020f010528030912050705122101060302031e13030f1b0609020406090c 77
    0x8200410b8601300c0c0162903c015001159444105403c001d41107031800d00000c1013603031700881c583e91000040084800742080d110034070046000320540c0010303100c0d14000c288101d02d0004070170070743c601a042e0086881e800a20280c107064100386d444902580000030b040c452943d00c0326480303014201a002411415840c640002d41c0c0e4070051207124410441c8034041614606150100c038a1640c00c03c0050010f00c5400d4140303001c4907000e119890180c810881110107109840c0100ca01c95500100040640c0940c0801501c21b5070200744594640326110a0342c20750b10306100c50006040d801c0d40d9000074104d105181502d1501c401913124800c0c044217001000019a0001d8401c19601c80d443e0403c0c0c41e9100441180522004e1243c6144030701d003075400100e2450342c9136010750700c554400070006402000009503602c419038191504654140554100b2001c240030b0b00c5401c2000c9150310b02500842c00048540e0709235580840100c44103511124500c00303500d41406404090180d00104000031003505030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 66721765 1250 66720515 66720553
    0x80303010603020901021204090209040c03050f040809030109080c0d090b0c060118020c062a040f030b06010519120c0f0c0f0245040206030705133203 66
    0x40740070205500000c0443e6180d00c00d0102014840d01400c000c0e44803034540801c02c0c0030390411603480c0d00840c42c284444900078400d024690080319800d0031101c0c5525940c558200581c445850385400d0b6488042110005038000020488014460060300354400700310320050011002d5031018400340030500503108480c0f804512941110403104c081c94a400034611550040d01400800315214040d6400700500220903000c20b4a1040106136142502020b500b0004840d01032030107046800c0e01039850074000249010010347d0480c03414101079082aa442c0000701242060039210000030b00d05202884094020f8000d4035440c1d01d00d42001404140f4802c00101280b070880400b0b0403500c0d2403001801517480c2c2510107054200003030110050702e0982e45588011a2211142d8840400c03500c00440a03070015850183c0255401041180f540e1600c400c2129250024200c101d1807142c18080090030401134443d4442412218400a00075080300003240b111269150005011707410a000c000e070300c1b2003d29 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 66723015 1250 66721765 66721769
    0x506100c02010c08030a020a02010f02040b090d080903060403110c0301140c0a14181201020705030703110106050a0306270b0a0903030b0603070512010602010603030e0409030e130c09050a08030301 86
    0xc54000145030141c001240c129044a00180c01c1d480c0000a0214503842c42e0010308000b03006d174000b48030121041c1082003c0f4481c1d4828604060001e010107622850024100c658260141c9070160404107214002802c001c0e050310f00311f0206121030881c090240043c007007d03c80401c100d008114501c0c0f104d01a200502d001001c85000c03000001707103201501e00540c8040c09a250011000d6110302440c0007510030844030a441d60711039010804083d0a0150500032100803a81c080301450401e070090360160b038a40c0c05582140403554030b440c0003042640faa0b0301800025030180d1800700307607000358113002189a10b0381d620868001480d80d400780b010038201c109160708035050060004c1d482440d0304084000f8502001c1c1d50380d04c15000024402041d134400007400c10780039161901c1d1800c1e60303180f0003a401c0f0343c000d200050129902c8280281d6600c3c055020740f0005001c0e04140a11001a200142a924041e0300310340d041a036a000d04941c5950091005001e004141c0d01c00910a040182c52541d0b40014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 66724265 1250 66723015 66723017
    0x60f100603020c0a06060e01050f03070f14032407030f021204030806040b041a01080c04062f160f050d0f0609030e03060a020c06060f010c1b0b12061003050610 70
    0x5000f041000042045191242d0040d0042207000d40b15080312856200070f100d0b8900c100b180d481074141600d40070600004440f0703a2034102420a28200302e140c3d0450b88090241d6040c050b28040541003055502112280e40100c50220814030380000c016003102d00c0c040e0080003661050001c90992024810003503003007501828900c20700d5440c040010f02420001140c541c00c581031003400318140e0b48100c1c01d03880c03840090300d4626a59076504d8414070b4602036481f5440000e0407102000317502075600e00d20580801c1d004009001006044400705203013040b1b8829045003010010820060b170401d2074030000151a007180c41d00440c0282d0b4858030440340c1410000b0b030501c0c3d81d81010b007081500a07020b03400806000b45c1540c440d0f140100140700250007182c0701030124012140020704604d0803403590a44902d05031500345895101e600c0d0411480440c00040441d0740b4108404542085a4409040b040a110030921620301e884400e0002d000849220700080c1410a000d2218960318407190351000005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 66725515 1250 66724265 66724267
    0x10309020616080d0b01050705061b0706240609050d030e060403050613030f020c0901060c0507050a1e0b09060403080c07051309120807140c100c0201050702060f10060302 75
    0x206000055540c428040a000000911106641001840030240911030070f14902005005030000c01940c01e4414a5001400c5803c40c000007142c84841200203050700c00c00d01125400c0140e6035540c801100d11603c0c2c03100340c0d42602121040c1c0302e903201d4011000b0702070602d07103000214a044082100c2c1c08000d20020144114442c17100741e40c0d180e40055500458000080710f0060900c6441000210b00c1c2a00c00d800203001c0503014100c0900014580c0d90540002c1d0901106a2030498122808801e520b411a802c1c050060005040e540e2000000e0140c840c07400828070000c03200f07520888000d0725a00140070a1414001c8111b5665150169001c072604844500c1c1c5c8e80d94100499030500d401500041d502000c1d070300000605110a50201c05014407034080c24400f10140001034510307031012506940003030110781d40c0a134405100e8024000304841710080f54142c1040d540004251001e418004c40180e40d240e0402581950420501c1d400101801c40c0030b60a0401404410503200c8501601c001d140d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 66726621 1106 66725515 66725531
    0x9050403050a0c060b12031306030e0606190e01030c0302130203063007080a030f081303031a1201050f07030b030c10050f130816060e0103 61
    0x900364441c1801e102000d4411118511007401c21141c20780c076144152581c1d00d514810140710411400a0358aa05105050640000043d48540c007018286090b03640a500c1c04101c4d180c0012056807810811004400c0244c2c00d40e4a5038031a074034500028000209015618001d402900e100b22001d5121440b81c9003030a042c0e010688009078810340038003013030a10f51039034400503400d0400341c404242500185c002083c1844c1039070744400d015420610720034003010360104000b035143e1160309219040b41080300307500349444144000102815682c01c100b110040103140f40c0212942e0003441c0c00108001c052405001c0d080596002038915211400700d0245030290141000007075024004080c400d032000c04210044007203144070341c280130707041000d00410300307460000f014606c14141c580211035250000240c038004058406903a0740c00a41418041d040d84001e0742040d4107824600400e02c01c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 66546765 66726621 := by
  have h0 := BRFrame.cov_init 66546765
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66546765 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 66546765 ≤ n) (h2 : n < 66726621) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
