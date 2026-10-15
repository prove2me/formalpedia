-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5180
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:00:42.768049+00:00
-- url     : https://prove2.me/submissions/93a2d079-76d3-4b06-a855-0fb09b9b4360

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 931474820 ≤ n < 931654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 931476070 1250 931474820 931474847
    0x160e0901090c0806060a020d03110d140405010509150103060c030f05130c0914190b1309030e01020d05041503090b2d060102102a0e040b0d0209040f03 66
    0x10214000403400c00d845901c0450300300707080d803100c0c0750320703500c1504000390351261010f043c0050b00180401011103010750024a95500310442a40c2000c04010466049801c08062000c4804000c0c041c0002c0c80070a01c10240c002c0310030409080a00500c44142681540c18880100401d960f406022101032082d07000c1c1507240303c60041800141044110084813450140e0180c0b480080c02c040000c1c00308861044820f80c0500e0912000e40d580d4074000c00113810700740e800d850841a11a070420b2404e9443e0005221821103103540002c070004070307040040885000780d004505551208690702101034200064404642621100c11100d092120b000c8020b02034204d0001c01d210029010300031901c0e104040d48403d200100000c600d8020714140c01c1611075025103680b800b43c2c002a00501c0c807810340b40c1009a03d000b020140c2c01c0c544025110039444903002e26008000959140001c0c6858030381402034940c001e1007214040400714483c0c001945542d00a000148075582c811190401c241c090801d000894 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 931477320 1250 931476070 931476079
    0xf080420030a050610091d07050d0f0807080d0f0b030c12070b0412110d03090e150d0327050102060f180d05031b07050d03090813030c0e0c070308160e 66
    0x2420181c8201d5030f60911750295102031400c01c40c140c2c0340300f5104a00204181030314001040e0481c0b1f44020f012280a46c8a0161645800000f030700c000300c0d46840091018603c203280c0c0390ba030f841c28080504129045411000d02d09802d150007021266000550500503180c1100d80c83c1c181248001d0071440c01c00264032241ca9020041000661b01440d1030001400f01d0296030021150b03c031070410088200717000880140420715040040c007071851a4070b403544e8040c6800c1c4522200d0014080004c15000f103d0100700c000039038005100340c4a02d0041150741d0b49014510040088506080000c0c0d00c410004048224054111000030726107014034000c1901020b5900588404200d43d03803008100358011245c6101032160840030f0b8000c1880d0804680806401c80041d01d08001da001085000d00138172034040c0c804003412f00040c0018031481494800852140e10000300e494585210316406000041c81c0714868141480003070701003904009001d80c040c0100380c00c0940e168940700144c1d807040c1c050342d146800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 931478570 1250 931477320 931477333
    0x5041203021e030c06040f02040207021e0f040b0d020607051c050403030e011e0c05070504060f080606150403331a0f030705040f06091404030f080420030a05 69
    0x505402003402040d41070a120b055200e01c8009510a0f901d20803000f83c000302d907001c10009004038807603c1050f01703240d10081c00540f40281c9500000c50000e011041c8681c0450400e01280c6d191518100300e8072144010f503020302403208240006034000304d806c14084d0003900001000420020184800d040710412110b048000c4415144000c1150708a03000031408280000320220040d0300543c010020044085084814000303652002c581014200344119954460840d0118541d42c841c000c001c05450001c90100c0080d1510103c00e1910381c01a040038020403054150a1607000304104039426250000c03105014080d070801503554864200b44282d0114801004d282d50010454201d00101c0311101c401d0106118078100f085904c04190401c9035240e40101c004000d5803c0c2238010081d100110000095002d07a14480b103800d440c01740a1a64100c1080310410041642103080c0690f83c1c5c04914003510903281540c0c0d03d02c22110b6610004c1d400340d000503086a0155400c12001c00c0c0d00ea84107054841e03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 931479820 1250 931478570 931478573
    0x60305062d090618030c010618110f041203020a06050a0b04050c031e06030f070f030506010b0f070602030411060a032703050d050c07050601060f030605151207050412 73
    0x3480018592003103006100d065521141958000c1e0781d0103030740c00801520003078513003200b00c003003001241d20800a02d0000f80032110600d03e00384a400000d1801c14048115601c0005a82d42100c1c502e640745041817034280008144010600240c8084d00c0c0c03050031480b6501c286007801da00c1e00300f02d010300030021414141048540c500f1508071017001c5000751401d0005854031980240a40001c4500111480d5105101c00c00303640c2c0704400c02d800040c084c00352100d003111401c1c840e0078008644c00940101075001d00030420004100304403801042a00c44450030004115680da50306d106140c03020307014540220120b000e100803018119801d03500140307880d54840d4000c4003e80030704205215000846205801c1c2c0b0301c14880d04150b28903030780c0d05583d43c605c1e040e200c4290800034140a880c141c2c50705010b21003030b0001001049000e01820064548840d0041a210028103a0301c82c4d030003490083c0c0b541400c417145800d48001341d880b10030711003805041c0c650790070f0003c0303d060140b41e20413000545416410720 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 931481070 1250 931479820 931479841
    0x21b10060302100c030203030a0504031e051801090303090e060a0b1903060b18190503030304030503090105090a020a0909111903051e0d0f11030316030b030d05030a090606030506 78
    0x308a9200b0740d0591800c1600407010f8035460702100e0068050f800400000b5907500303e5520a41d4098881e0074140320b22607003813008211500c851002070000c61000039100d90107503105205030045003400d1810301d010764115030780200200054807400041840d1800400c085681d40d41a13400641411916217031202c2e10441e00700800201c481d01034012030320303045001c0b85000c0c0480480b5900344821500c040d8200c20403045c00300144440c0c40e81144407040c080c0108050390180003d5004c0c80c0130323a644580b01e0820822980c00c40e80c0c0501201d4255000d03040b61070042c0c8540c00041e08640701d0382000180040c0c0d03030034150b1051000510a03039105141001440703001c4005400701040d64007a808642c50544803507031402d200c00031203480d50310304e50104144a0001c2d1041441d1800820280b03001c8400042c81301405107550400e0301d070300308200c1103403400a002c2c0343d044c8246020107a00314010446155500e13000ba06910010300030310b602a0b12a600d280502142c1c0d006500190340c0030045404520f8030600c0c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 931482320 1250 931481070 931481081
    0xf2e0c0302091e01050f09010909050709060224041205070212031e04030f082206080105151218191208090601030312230907050310060b0d021b10 64
    0x1500c0f903140140c401c00f40d141044800e40e0354030b0b8182c490f14544000c02000c904590000e84055040054a40c40850202c006015180c060000c50f140c130b490107810030070040e042100300c1c2200c4211348424244292003002618180e60480c0e0040d900301003111240108031400e2190306400f9400003a4044042000d400c008020b01d205000c0311889071480c901407021802c076200d1840301901c01c100d00c5500d500817607406e01c000e082d841d44822603071007036602e80380400300d42c1d200f281d0000c00441c800f20700401013070501c051030307804e034000c400c01207072074806501d1140e10042c40140c48003074103902c00b1a95040a0400708840d1100e0761660401000011182c98080d440424811030b400000d6402404181c6801e4000b4200e03069a07410740b510807068031204074840c01000745152a420045803e10b00b0001ca04140c1c20040c005d00700c61000e041d6050414003031625220b07800f59207a428600e0b101040040c040c1c2101510b400740c1000b04050395812801180300030001c4403010149143c0680720343d5140382103095011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 931483570 1250 931482320 931482337
    0xf0f0506161e02030909040f03030609090803041115040905160201020c0a06051003060216061d0a02090406020f0a02031b1216170a020c040e0f2e0c0302 67
    0x211241a95454110703001c14841250100c0400d400c8840642580030768007a100d5140d1040c41203d083c1a0f00000041407550241c900f540c00e602d407042d010741850f60502448000c3e006000e030500860040341d40d81095840014406000c0070009414140550740391003085c1d0300364150409075600d841d00c80e0001002042d06880c0c12000680c0800001c03451401802610b9203000d510001c3c241c0007560740c0760f00c00903242c01010f14070082102c44000c40081c100d072000c3c0400c03054480f50800aa0b00c1c0e8503214084a903080841d01c1c1404541c0340003009120700042e030340a80d80d4145c9003506252601c1c50301d8400f13400f602c2d680300014280403481000c166800070140c003c800c0074512200f589500540300648a00340e0f1080041d0050b0100f21a20029000001d0b407001948070300103103202000c0c40f01002c01700342c10840c80d00c0011f8001d11210000c42c0351034025980c50030007070406000301035026070a00740e446412207500c051189542d601849001c000d0a036076952464420010311800400e0b0800400a6016820 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 931484820 1250 931483570 931483573
    0x25090f0503070602070b0a05160b0105031b131d070e16090e13020d0605070201050105120c091612050403080610210f06050d060902031908250f0f05 65
    0x8001581d290000b1900103c50740c07500039104803401c0c90480b00055019030003580038404100f004810450349101d01c0b400302d40c061058001b465042400301410024604100c000200d0340c80f81c8001155250003240110001c4e8170000141070396540314000b89a0041c0c0c03400301f058014040001800b14030303040d22910030b1030420710b004401000c0c400b090328440a41d00401e50724030720b2500040c20f8426a5840e00c0d44060005001c00c04080c1d0503070718a4180c3ea001c41702000141d459400420183c207011003401c44049a180140a031150a4001b2810408005004070740490300107075000811400f035400d244a50030035410034403180c41d060070043c1601a050310442e02641c1c1191343c5019043c481d4509020070815691100e040604900c0300c500a04a83c441694266a40d4000042c0a688401c402e10b802c5104000106038044240101402c041000b640c4107980d043d032450142c0081c040408688400340b404552640d5103450b45000300c0007084034500100101c40645000041c0300c0ca00c100740303c14522500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 931486070 1250 931484820 931484849
    0x3090c010f0f0206041e02030d0e030d03110f1809010801061a0304030e09071e020f0c0904120305041e0f121b02063702010b040519052509 61
    0x4404448648803a42c0000050f0441800300700003d40e0f181c3d4694040c10140b4401c074030012503400003814020b2045900740070031181e80c85410b01e8101070050740702a405c80d00f0200100a14800060b4252241403851800301000082e00d5681011002c0070300103104026126021039170716824818000d144502401c0c54200e0009140c403d0044900c0403603100703940c16079540c00c2c503034640400c0c0503414001070302d00b00130b00050760394561883d215040703850300c0307074031284c0c014100c07605044813041c01e10300c828602c0c50182c1d42000403c030208401c0030380300140b01145c0c0740006a9503500e040401c00b180d105420a40c00c200340c001010244076407074000c4401076001d1180b00302c10600c10101030702c85c2c140c032813440b0b4401d0755020b00c1a800352401c1e002801090a000241b83c0d100f40b403014401040e40c091200d140d00d000302168640191a509204003106040e00760f0f17003008241045c0301003400701802501084e481c07546990000e811600b41c0000300c0c10351028243d0560b0050321505002d040d021450184281e51156031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 931487320 1250 931486070 931486097
    0x1e171b0a0510050307030e06070c11100f120209060f090f0d023f0a0b090102090319050118061a090c090d0c1e030b15150a090b03090c01 60
    0x44800c1003152801807080c4040225810140c4407600024002c20506503600e0785894400018003906103d103d0a40e6101c103046203614155690300300d0b000300c0d10302581c0c0c0b03030130703c009825003041682480d00480d0510140d00f40039105000080c0c0700c0c1300741d4960004000b040b00000a2a00d0001d000c03841d00880365243d03800507090900c802c05495503006503011b9507000e4581e00889004000b10003a80042c280d0038103144441c01da441c0382ea008440c004505522032510342062200030100150440e001070029894207506071f000998902030514040282c3e064400d03103800b00642540300380c0f4544451400500c2560842c14160020900d03039145a1608801300003000c03e070302c1c1450040f0720a1088501c12820300324844280504074811880860b4040010200811100d03001000c5031242240071402440a034210b1422200312a0003038040020b0680350a507002195441e903400c1c40303490420003045504c0d030320440030450300b6110a601015070031100000380200600c0104591101c240282c1711414107580b513 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 931488570 1250 931487320 931487329
    0x507020307110415090501030b180a05060f07051c05090c040b03100b031204081b04140402040c03290901060905090f090709182a1e171b 60
    0x1060401441c5000d6031003039609903e0f05510064079407000580a50340d09889054002c110746081e00b040e9010301c000070030049100c80800428035000442d4000c4d14030b0036003a85d2010b5603054090041e1400e800117000261945103c0e100b138500200c42501c040700418030f200000c0b002044190f44205003401801004005c03410a400356565a40c4c1c0034000700b605949242014004000b02021076500d8004e00c081100c041a212000d01701502c1c401c006404c54101c1d1803c001002d1010b9458140102e04103425003a0304a428806182c1c0590141c81c00315900650b00300440040417a1441075110b41d81c55040c40c084606202c0507140c040200b40eaa44004c0d0b629000140c44080c0240300f8180c1c0441050001080d061002c42d81c642c000d290b01c0221000d40740c507080404150f8a101240700d1541e050215400309000b001c080d030000c01240310b0018550401c2c51510496030300298080c045c803180c2052000c400600c241c0582c10010f0a4542c0c500111007030780a00c06884544451b001491107500d91001c41083c0351 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 931489820 1250 931488570 931488577
    0x90b0a08010e0709021b0d210908040501030b0d05010606261005150c1203091506010e0d02180703020319060f033206010602070806040b01030b06060c070603050a05070203 75
    0x11002c004120003483d00003408041e60246041c035042e5111000409042d010403ca15008030750162100c5500b4030705c80003000c10b0400103145000390103080580200103d0403400480702640c0d403c6c41c01048018444001c21030304403803103600a01561800300c0010b1420f620551501c0076281121a615041e640325414092070030085d2403074005200100c0c010003075031806000d0080303402003805444c1d0030400b103a0505410010300c41d4264030305900020811620103000e0000d0140381103040500c03c228209400000d02e03464182d00300c0c40c06080c0350540c0700c095555503c1c5404802e0700a1070100910f02d0700da18000c3c040d40050f100c82c0c50b14203c2d202501610780c680c3c024901520441651a04030b02c0c61902c410b9414029072403c00c6911300d107560300c4c014141c0030750342040e03a441d500c100500f140c0d454400000c1c51700c0910f50080100c0c0e0000f405204c0000c0460801c141140e40282c1e40c000c8513206c4100160041c407031070706030220500c40c00000040164254000500c540c01200c82006107940d0070700282c2e101d20 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 931491070 1250 931489820 931489841
    0xd020a03060b011d1503061801090f060b03070f03110c120d0b01020619050a020c10091202070b031f0510020d090f030221100e0a02101407080d020f04090b0a0801 71
    0x210b402c2000c003e00d0485d4040c5034841c0c0001d10b5407580704a80f0f154812000d03000c4c0c1100b01c4207a1290320684111000d07000718030080c40325180146c034500d0040c000409100c80599881e04041d12100300c42c0c8000720510548040116180940b01d0f18a605d840d09103660788502000310000d13050160403074440d8008110f00c1c1c0710b482a440036140f018080503121004040c010a8840300036424414120302240801070300180070720320080020310025900f410350030300c0740c40505130b0b0031540b2080050041c0302c8014181e981166210620300088241d640c5240709405060700010b4211241c03403422090f442d40001c4441c1030b025a51034503100341e40c40e03c11a0301d0707201250001030741008103109007c007a21311441c0c900054020300380554a06042c04882d003011340b04603461052840c0d0000c0f00350000d5140082c5410541102030070220703144202034542180ca4040d0340b00141c00e8890200300309140c0c040c2d903011a08480c0351842c25540d01c03034a41c520680140100780c04140103000c1c1c00c0e00442d14400510803c1f4091 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 931492320 1250 931491070 931491079
    0x3021e04030c12050a03050310090507020c090f0606220b370c0803060a0f06020d020708070621090b040804030605070f0206011406090d110114040b0f090d020a03060b011d 75
    0x5c21180d00c0a480c10340c80a0f05440d40e503080b09600055511035481020b003d01d84540c050484016080104560b150001e80300d00a130303464500c1404600d603280001c803160481615105080b10403c01d200d100c040c0305d683d00c4001030400004a214510142140c00c4520041448014a400e900d0300383c0d14501140805d410000b2070380d10301581c2e011980c924080c3d0b5000e42d0080200221649a00080c0300614099003c1c0d005a44201103079031107503805000c40005400b4040c002c102d0320703160540c0141125001d103079805440c0072a0102e1041c00300c4c2600603017842e6030400e204540600b8545042c2d0613503803043c070040c1c038014a0500402c00c0c0600c00d51418805a8695004019a07428019401d00031402c050580b9030100f01003000301c4240c1c0700d40141e00303e001c2c060b005500e407120358240054030030600600003c075807020400081c0840544030301520400172403100c0035602d5124030408a1800c1c9003445010f07601121540c070010130040180c200c0c1c0f010000a0341e50a500703040c220702041d07002c08c5500109031310 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 931493570 1250 931492320 931492333
    0x181603020609030c0406032003060903031303021203091b03010515090a0e100603051204030f12050c1501050a0b070f080a0509060a0807080610120c03021e04030c1205 73
    0x161906801524407102d00070240c45400c20400c00180841d191035008031944203048111160380d502d10328444200c0001235010b4080d9280001096807244002002c03c521000c80320590010b00d482080310f400d20205001415999051512625564011170001b041411070405060081e5080c1801500d00030800d60780441031181c07a640801458000003000150481e5a031a10020012070400400682d04c3c0040000075aa50840c00d14038117100742102c500d071401004000401c0000c7c9078105000716170340c01000c507104c40d9260210407905885013210011030380c41121038228180020401140c1240c2049079100c1d0340c543d03682104003041c001d417000640101c21302490040401c11080c02442000060310300189080d5010002030302d0340c0c0040e00500f000610b1003003080036680d00080043c0e00060f00702d614062850590900520108000030304400c15a252154140d815000360140d40c4094080c0b2030810050100e45186101c0350400e101c141d4880d60b500d540003400ca00da15121350b580c0f0fa04200507141 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 931494820 1250 931493570 931493573
    0x60e010e0d03030e07120b06010302120c070f0f06020a02010b01020c0303090105030a06050901080d020f1f0e0c0901180506041512211e0e010f1202070506090105181603 74
    0x48041d01101681450380f1a00403c1c42408284215400740002c10680303c0600100c0c20003480114000740480c0c1450f104000c00003848858500242d8050f00407000e4030b0351421140360240020b6090680204401c4151080d5010000c0c01e401034007074118954001c001c441242c00c0120b030b40e241007032000c03030b0076800421608800e075119100840d4040c0103000041007140d541e9000ca558040700f60303c5500d00f40c000c00802900d80d607040c0030f031655a1000000410501812260600c034182d04200d110300c95a9940b000341041e074409000c0d409070f11314000c106002070341e521050b2108000113511081e90b0b00b46440e0000740e00d072034907210741340720004230206d12140343d41050125154005440020b0300d119140b08980d011034890300c00002456103240d92440c5002049488002420090019800c140042010b200103284d80c03290713000210103c075240200b170310b54180000c2d00c020300c9500c2d805050341c000d410421000681c150001d03401010802c0d50071198400e0a40450f4683e04810328880c6465041c000820 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 931496070 1250 931494820 931494829
    0xa18020a120c0f060309051c1205040f020409030203191b0b1f030602070b07053f0411010215010e0106080a0b030a05010504021e010e0d050106120c0906060e010e 71
    0x1c1c44600c5440d455188a03116000e000301d10f6259032102c00000e898440d8401007140c103105440740b0700907040c0718038040000601c015041e2513030703200e181c542d5540e25070000d4188043da190a601941e00503004100c0202c89060081d141da000b0314082a01c08910741800140c5480b0b05040802100c2c1c0d50300604102c01d050b9200b403510000038041100b130300d101c60000d200e140c03640c5121000840c448d000041e80d805031498080310008005103840140442440482c901030f101c41e90032a02c802c49000116821000074883c01e1940c403462800c01700309201c0d20100001c005105d070710006208070980031a00c004c038802414200c103030824015038400004080040040314081d503540c0382c02c1104418040f8845100320007113850261005420340e9186e4407001071000b035080204610507810f10120f0f0354654541030100180510000070200c1d4051a02d140b86441030190a41c0818090194039081c41e10011503424455401480d074018011103030b203403400018105029828011442c5410786a07041809090320400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 931497320 1250 931496070 931496099
    0x503070204181202031e04122411280c0303230405160b0c150604230106020606010504050a0509040302012706060e092a09010308030a18020a 62
    0x51041880150490000764001c4000303a48007000358001c3d1b0702c2d00170364080030134074181200301611280d42c104014000321300c51000104465402ca070340c4580c001c00d14606c030182c128007409840c1d9040d28040008c42005e0b411802022985880178098041e5078046040d203443c54004090207021441b1002c10000080c00b940210030402001100f00d9921968000c401d803001c43e046a044900b500a0303d050080054045800c0000d40925034a403402d001d007000c003882d03494001c0d0511751390028000d00090b585d59221f80007046244020782809031486910040086908070070b000c2e600c00b500582c40000c20301e500c104144e130100d07100106090a06840c1c81c0600c1b070074080250041d01103549441c0650344048404249461090140d00a2000c1d9105400c2000440d85140c0110740000034560a0000307031480043c1c22510010710440e25900e2131855103c4501502c1d100400076000142d060000041c44102c40c05103101d178064802c103012001c41c1d020340052002c84100d000b580188202818403c44000030885c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 931498570 1250 931497320 931497341
    0x1181a010f030f0305071a1e04050304140f0301020c01050403170f160c0f0c081e0303010b0c0a06151805090d08090316120f0819020d06031212050c070503070204 71
    0x20301d141c00900e484002c0c00c00a40c03185403c1c01007582048c8000003100c0241503842c0000102680b0f001d09040d034a89490b80b003148504445a01d242162840d41e40c4c42803061185494000c1c000c65480b03000000d03140c0a0710040b034041d004926001501078503a0103030510300d88691016000382001d03994200705602030340315540e104401c00001086510000c0c0400602c8001a0b02448003c50050326103001149803000c10b06100307284c0d8107000002d03913112000009580c103542250b40846e840b6011402c02c0707440c01c2c10701d11300a0a40760038160300300f60036100040c100b400e540c40c0440f0381003503003101e00c2007400b170701d0342540d0b17298603640b2503851410312607c20404540c0010500c400da0703240034a0305520a02a100b600b405446560381c44100b03417083ea40080819503200305600303000002e0326080340c1c0c2c07141c00340082c181c1e09001900011650307001e01d0142d20020103154800303401c000002c2d040c0401040c1c91040c1c21612035203440c02c808074280610303140039540d08035800001146413039520381c240170150844040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 931499820 1250 931498570 931498577
    0x9150e06030a0f18020603061e06070602131d150a090f0e0f0115140d060204090c0908010204050a06050c102307090f030b041401181a010f030f03 64
    0x486269554040081d8020b124014000c01c554542c01d070f12000300d40d105030100c0920083c66403602c0050b114041170380d0348960708540c0c5d4682c0100641e5007035a1140d060364429070004000412808009480e40540f4a940c02141a0321485844110f60340091a800d605ca01c045600e59000032584c0c0650024425083c0f405403081c40d509660b58200300c2510340c10340d03074201042d0b120420f074100410300304070704000b1049080003404108813808000614401038014041d03070008059812460b900c445c40040c403120780c010030441d981d07552909500010160034296000003101e680e40000c0428050003030310241c820080c07000c3c82c15807070540296240d500080029000d40180740014156504503c40c3d2400480b4078107060003612401030803407504280051070002031004042003804140005e20080e82501e9022103408600c3e212410140380341144000c207140d483d800d00071b9044a1380310201c03007221801d1080c0e030403a015180c504c110f4402082c090090301240c0c8180402000801c07142d566904225001c0e09 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 931501070 1250 931499820 931499837
    0x513090e01090501020c0d020c092a122403060408030121020d1a0109060e010605030705161b09050f1b0f030c040e15030c040f1103090d140a0915 64
    0x41e940f0f030a907080a25885500e4000700060400e594050003121901041201c100c4868609121990032440076400d41e0030340c41ea810120503411a1002007116100c0c1c00c212000300d00c40c9071050300c001100450410203014941880d001030114100020404d010380c0c0e21611030303801d5070f00703000d6100301075500225601c00e1241c0011114001d40c8880b030b02501018020b0102c201800900c2c5800c6d00404410b900070303455286401030070858107018100040c1558501d151003a40c0e9241c80c101100d49004003000700d684d00c6100134103c010802c1880c441141040c2d00c404480c501643c1d400309100f198004c492400368452014002a0364031180c00c95420804401b0303000c1070801600790310252558008896507000e80d240000d09000364411040001d500080c441c1e182035400740e4000120b52940801080e880c0110381303408000702540c81d0380d00b140300c04160000950383c0304d00d800f1080e07650741c42d01c07040554041055044860b0741408801c084900041c02900c075400c103e80f411581103200048034442c18100311198 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 931502320 1250 931501070 931501073
    0xf1c0611130b0c0d090b03040b04020a0b030a0c030e07140603060301150b1e04060509090c04210219051f02010f0e0a210e0904080d0510150513090e0109 67
    0x20140100900003140b007194868019035440e40c50b0081090040003440740340d480030065804624122a48180e2200c000c2e045074680740b000c6084203195070411000d011000c010082d084850b80c1c050005008075035020b005c4040229a81900c0d915a80174448a25801d0a9403004505124009680280d8080d00012342070030b01394011100f450081d08141e102443c0000e94061704a000c0d0310f2410001d98146c0014609441c10364041d00c40d00c5090800c80c020b50b10034000600281e41c038000d46000744400042108d0100495406c04e00d03000ca0064224458664044810b1807440a880e500c0181d80001d4548106a4032000d508480202644016000c541d02d44201c00d0204580c0d015000d01c54000340010f107110318a600d44030f1083d00c261106d0403003900c0b401281143e02d5602820100000c00240c0c1d85240607210741c1000072140c03051700000c451090500f02070000c54440450103d040307850760440f4a09200510604503500d01c1910b10400c03c50f034501c90240701450381a404012400840300001481c90081d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 931503570 1250 931502320 931502347
    0x20108010915230301050f040b010b0a1704062a0305150d030c05030c161d0907120c0816080f0c0607110418031d030118030f14040906050f1c0611 64
    0x111507401c5a090010140809c105071002094054010881d0303103420071070500b000404509a50810088417441d0502050600066610560455005d88540e55802a8108410000d80c50b0680184006898800002e4682e00c00d40d66102c01544020880307594903480342c604a805d220442000d40c1c407800100300d0011818030030019109620741c141400c156141c43c200741c02a8051002c1c0d82c0405044050f030400c1030204000c00c0c40010f075084128070300490708080c1440301d40400c0d19041242640b02d4060001800280740c8014000c5510082c210351071000b4406c0c42c0c40e181c4a4458800344c014505005401c0002c041100500551002a00c00502440c0000c44000c500d200310714180e011640302a00080c6008100108461000081d0000c1c4802240c002d0701c54002185050060104241440314540355441656031002503014640d450f034440340c89010800041c2030360f20840748643d032803c070341c400d040c189000880e103400e021f1049281c5030300700d546414014090001c0c841d561400e0400000142910303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 931504820 1250 931503570 931503581
    0x702070909080703051c02120403030b03010b010e060a0306030501240b04080a0618021809010b0a081e160f1e180b030c060c060a0b19090b01030b04020f07020108010915230301 77
    0x1c100d407032350142071a00b0042c00b11840800d440c0c0c041c0e4180080c0e4881c0741d030044600c01e90044284c1d40d140d40d0f001c41010850080080e0b4100030195403c084c203601c2c08070842441503a046117030000381c0286640d00c0540105500c50f6110300090350300043f40e0080411001e501003c04642c0000c42151000d542c0c1e80061080c3c003482c011a484000c0c082c05125090401b4400d810340c500084d103010030000d04122525030b440b001c0d002100c41d90f402d00048560802420f00000c6a041c194440810a40c2e03140c08014041e81001d008d48144640000c030044003104014804200310340c0c036442c0c084900d601b20309661000d81400c21409401d0300c40e5501254242c4c031144014400412071a001d0300d440c1c00c00345440d4044d1681c586015110300d90b0b00e2403003410b00d0080804101180c0c51010001420a8014016406000366250a80e400340c40031801e00200d2035a203000703028180c801d98482c6540ea80341c403204421600381e103a20000c4d08400c6503050102008541d4000003404400c00c4401c45c6250080001e400e440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 931506070 1250 931504820 931504837
    0x1802031b0f070317070e0d0f1a1e010605090f0301090503030a14130b16030b06030705070501050f0c040915030b040804030302121c23040b0702070909080703051c02 72
    0x10000100c0a043c03540c000d01c0c1440303000e1451510511030070b044000500b000c0d04d007414140b00d41040d1840741e040081c170b4042d85030a19071145007400d0f05050f642c0c1c2c405482c41c08590380550843d901003c1140305e002400c10754182c400030384440342041c04d488207000a44040100300398040d1340e40c90540010038070810103584075000758035001c29455090074178181d41c2440038004804a166801c81d1300001a5500100b503484003010980101e084c14186045001c0d0000d01240e0703810138000000d02c08402e50000040250a0088000703200c030f031702d50741341e6200c0c411030464404c41d0680c0103100500c080b0541c0d0700072400609002401e005407948a4640d000c8001c4199400c4a2110340010100100340e01404103664441d00e000078141801c0e005004415400c1c0c0300c2031000005070703503000021480d5041808601d450302c80400d40c4400e03454546031800c080c2e0700580c0c00c0c2d00507200d25100051140460700445268503400300bc041d061289030358043d1503c0e040442c00c8003440c40030056122484845102074080034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 931507320 1250 931506070 931506097
    0xe0613060e150702120316050c15010801090210020a020d17090a080106060e0607030c1509050d180515040b0a0c0f05060402101403060f13180506010602071802031b 72
    0x1d041c0f920000e4a400e100c40c1c0750210b035440600400912409551907070800c02c04c9810920703a03e0303140d508254102100c4015540500100400111b0488415480503908510a030b0b000022240d09038001d99844042c240300039408021820002c00140c5c0e031280300412000007084040c100103d140018010101503049000c050399070706000c001c0540d12010301d442d0b1400c21b5881e1880c00712582c8000380392048000b400740001c06203000441c1c2902c880e07800107801503045030a0303d00541580310b00408060000c2000d00c0c000c030803400007003034519000c0b00310b821607010201c5062515281401c020540d400041c900d2040c40440314007100400d060100311964607108001034241c92a29104010502c080a2424010400300c40058480d0750280021290016006c4441c1020307107014030000b840101540b0703080c0c0c180900b03008403e1f200c1e400e00503582120a1140060b62001e13a21940c003281c5e036450512035101c0800034640000050f160342c0d801940c0007000e20001b031220b200070071b110360115841a880281c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 931508570 1250 931507320 931507363
    0x3090a0b0c1501080a08160b010b030a0c030204180b0a0302030609030d0e010b060702130621140613021c0804030c380a180806090f010e0613060e 64
    0x1000401c2c04030500c40012900c5070862075040041c41a55a055004010300d200c00003d10303c001c1188030801c0c0300440d540706000c8400e568462545140c0c80e00281c4a24800c40c0c1810080341881c1d00a00a44c0d0030f8482099020113007074001c0382e0708406018150720b402d4104455075404805600c050110070721a42d6407400550340c82891300341c440300700e8100f0f05c00c014490f450703c0c1400c1c4d42a610202111007a940480d1080e19903046004100010101035000503202c6101c060422045400030201146460060060102118108181c240c58441c21509959000482c51601e8010b1507c03245030203000d030b16404802c141f4219a41d900791141c5c000c0e001500e9094610341c00f007244484030000055808100d9030110710160350b200441f0075044005142c8070180300c0106410411174443c0002c000d401200900c644907407a69094000c1c3c60f00740030303100040907009645c0340d0070744003005000d895503001c125002071426580d480003000300100891030441c0c210f61030b00901100150f0400012035035140b000c00c03010342d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 931509820 1250 931508570 931508587
    0xd05090607060f0b21030912010e011d0f06010e0105061315050d0501050d0c0303030f09020402040e01050415380d05060310150b13030b28141803090a0b 67
    0x14179158000c0032241110001580c1105040044259a00b2001c166051001800c0c48040309024200c155560120342d8a490700d4800e01c604040c050343c080300c1c6040d05032144510015034068456801340a2842452100b000400081c21301900a010822840c140c5c107440603125200e90b10003541000c501d41c0003034000700b80e44111181611415006040c101d40c14500780a13296a1a040e0310050705c00035080c075665000060108486810a10762030f0b90042046540e10746450f1043c42a070021f0080b0b900842c6000c40320f0740203580d40c40400050f01c04203030042d442d80395007040c00340d09048100824041c203c0b00e510ba076210f403491700028046626500e01c003c1118070b0314005140c41d00560600c07148009040101c47c541040703402e80341005807500a040190b49102c00b03440340400394582d503c01885034042004010708206054600081d480d041390b9001d0724102e0390200941554059510540340e10360885c04260300c50400341d03a0722090707190041500e060010700400550540c0341644190080c01000580d1070303 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 931511070 1250 931509820 931509829
    0xa05070e0910020c0c040e19060228120509010b041b0807180e04050c03030403200612190615030603230607084210020d05090607060f0b 60
    0xc0d00d040b0685011400c2c0b01d03044a0b02540d40300c1c04040700f8055690750700c0d050030310303042813145803090080161408080300c4189000c0d0025403064402040e458900c4c941175640000305560400810610395401303801d0110417004a00800c0060310b05159076617a6400f1084030b444a004004083d4620344500ca140c150303244001c0d03d070400c0200150304009800d603400380c0c0400d90450450903220071030107009155650340f40181c41d0598841c2c4140e03040c13202040000400400b42000f00c0f150000300340203a40b881d00c50050007894015607141a14008010000030100500034443e0300518901c0300c0c0c045000341c4d44054072510100400c000f03d0009407580d0045c070072300c01a01c900aa480c00191021170625100343ca4041d11203002400c40d104019680740401d824000c40c5000b1006030341118030b10300c50785c0303010a90b00c003e42c64900000e144070131188074030032100e1070420109006601250054000f001240f036040359254000989580d020100b070201d240400c2c55480343d41c0e604c207080c98000940d650461f0810 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 931512320 1250 931511070 931511083
    0x1e0504050c090f0d0201091a040302041d160315110d06091a06090a03030f050f0a170f16030c11030708030601030b1f08150d03230a050315030a05070e09 67
    0x1a4068011540c1c1400147d1340702240904944031081690b240140d4410210010300c2280d001a5015050007142a400004040003000403291079040b924800c042200c640135502151101404809070011002080c1c5000c0c3c2240664000e50305055107081e0b01048100e0840e4100e41105150a40c1d620364640f00300c0d65400d00f5101050b040b1031081c1071048500001d001e400ca0303400000c08102d8004103e02c80035000700103071000c142c3c03604401900c4010781e040060540900c0c4400c480300b00055404141800b80302a0001e0203061004c100e4a100f0b100b02009a001d0464070050408008191901e0b1295000c10b0003e828200d2042014941e24101540010291041c0c2c103d00313031040d45420058200c58094009402c4e060190741040007041c3c2d52001046502040d8601c40c680212001c01c01004069002054103421040c00004034810a012a40d00149000c0c000c20a004141d01f0004242c0c004110b80442805600c01030441d102c2c0c8000d9612541440079036071000421003150030604c9030810091048 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 931513570 1250 931512320 931512349
    0x70c03141321050d03020c031e040308040909050105070f0f0305091f05011401090b0d0513020603070507021e01200f030c060709080622020409120e040509060405071e0504050c09 78
    0x150300b40b000395000e058982c0700752240c80c100c0300c0359110780c62010f251030800d4ad401140c0004245448136641c07803101002c4d0640c1138088840e9440d180010750940d00940d010551250301b41c0d00d6020800700c001d416801014041c26000c810710500c41c540083d4106003149507000105408089500d5140094201444034904080c0381400821641881007603020030503200c110200e44004141030b201e010f891099402c01600280d006040007042041031a0803000804241d44240d5000c01c15038503440c08907480c8000f0001140c001050100c02c180c1045142c128082003001000948000005080c81c2c02d255500540020b03810b0380101081005c1550054844002000107074080c0050b461f000c00c010f51503c01d2100f0200380d15100b280d0f10025922258026111180e01126100800c070000c20064508003845d41ca46104a050500103000400b0100700540920303448030003403101504001e1501d0b4100415074460015581c0313445e0000361661b85000d04c9000328154110650b40c2c0c8642030170b0000a240c1c1310171 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 931514820 1250 931513570 931513577
    0xe13120c050c1005071e1e0317040803060d03050c060a060303090602061009230106030b1912060905100606050904111e0c0f12030609070c03141321050d 67
    0x4814098981202c1100c2800d1b034400c01010000b404403030151100710313500ea0090145820400d034414004521241009600c6c0261102c18520404031144444000c044a000f0070065060020903583d040003004211414480c0c24654140a09c00085034580001191076041c096101c0104005141e044451000600940e2000e0407141ca0702401000e1003000b01c1c800d0003181c0366103400046004400e10390980c1c40180b0761121524659407100014042c3c01c00c56202c03441440480c3c0c0104020035000d141d0340c1158821409010701840d81d8403804014810000103079006d000381744c07100c802030b80944100000307010203032907640d100d08c203420500c01103c0320444840130b0321a0800056483d85034082e0862201c5000c903000ea40e541e4094503c0c10304215a10500550b43e20403a04c0c1d414040065001640c0728440940b0307586100e40d140c410481300344510b06000f8012445103804004d6141034070001300040c2040f0f844101c01c09594211521007180303070300003001d006a02e10801c042044400c0c4031801e24242c00c1d14 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 931516070 1250 931514820 931514839
    0xc16031b1a0a0506030a05030910050c010518010606170c0706060f0e04031d010e10050c030d060911071502130f15021005010b04090911040c050c0c010305040c0e13120c050c 76
    0x203568981e6840f40300815480ad4000481400300d1501c00c900322248025460020301080c01d1440e0006ca60103060303101c00e102c42d400c0020108900e07200d1000c540d0b078513401310603451040c0c450040c1c0320165403000d03409031182034803000c003c039007900d0700806000140a0b0000305291132405003401040d04d041003244800d007541c0a50154500d80c1c0c0b100424400010484800b0700348a0340d01e100751440e03c01c5403107100e1180000305006101605642c040400c4610040051003100c6091a032a00c4030310582c0d10040c540c1d89541000e02c0405102d50140034900b0321225904c4c0392320384543d6020100c4400350312503455416040b04481d095981031000388000030220f0001c1c03001d0350511030240c4882c051b5000d1000495074035440b03803003400a10700b100c00c2c2c800c01c083c00c00c2105480c0e0001c01400c1d0743c4400050b041e540704228150409511030705c0707160300c55900040100003850801e040380d0312540c1d0241c2025041280446004c000c11342509481e2900c5c03010392698a80c40d04546030150405010007407a5105880b80d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 931517320 1250 931516070 931516073
    0xf031c03050c1b03040e06300c0a09060518011a0c10090b1504090c09020906070f080903070609080a0807051c0e18160e180a02040e0c16031b1a0a0506030a 68
    0x2385102050280c0007000720380c030340f0340501003140f404d2041d2050035070000d404100016000040d40c85038094403010303102c000042da8540040100c0b84828428980c4044c20440f4400d0b682059102400c8001e080c81c0a9600400c82e100d0b940003619280e45060740e01c10041810302111204445c034036006008181c3d010300c14a00d0325103810355690344c644103001c011900014071090b2941ea02d0101e82c2840e5101204681790002800c10001981211f50404e0080c031502402141d42070041e044801281d24141c000d10880d8800e9440d281d1070780083d00d00b01d0b120302c6400303580140c04080035004402d0242d50743d12016445010010800c421310112041c2600021034002d01440c0140c20f66a40580c0820b410520b0203020040007040c1d4200301c04070714540d8145007a00744800464942c00500840c0c18440c92405a51200e08c440c43c201d20801d4200c07462601504110000607009508050082440c007104080d419130035142e0200442e51340c40713410000c0911b03900708650301d05180705042d00000c3c240d00500401d0404d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 931518570 1250 931517320 931517359
    0xa080f0705010f051b0c01080c0325050705060f0702010c030908070f020f0603011d180c010807090b0a02070801060602060105010c080325030b0f031c03050c1b03040e06 74
    0x24060307141007200d500c0441018038010b40031a1804102c010440c10045580c13425151101000d4190900081070113020801c6c0307162481c15a070040e803100c688281c210b40f16541200d0b200100d41001e2081c8403007801081c0c0424070510540e4070842c003414000015240c8050001e00b140c081110341d9003030601d8a00303000049842502600c200c07e61103c05007640015030b00018122240907100030354050400400450114403c1e20031003e0f001590314041015140c612000f4900300341c1c1003c00307c16a00c18102c6281543c400e075a03080d04299241010405241c80d6007483c50a540040f9a400240e40b0070071040080e2002442520014152031000d40102c0d41880c1c0000c00407154600d01402180000c400306860030010070805242c44034810f40320410088400019000c1c1c81000001880381400d15006922410003241000402804034260b80700360602100a078001d01000d006020042c0c001c0c0716082c1440800d084800c1508202e00040d17440d545080b003030309003010380206001e00a142c0c0c1d00141d0000c810 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 931519820 1250 931518570 931518583
    0xd030e1c2102030709180609020309031c2304061401080304180204060f1d0307120605060108041203091a01031b06050702100c1a1611011a09071704060b0a080f 70
    0x150440c06d07480702c1640760048005440d054100d101c0c2c0d41d10000600030803940000040a0500101520075410700258607107600700e600d0024000c4266411030190a0312420708041075500610507040021803040582c03241c080d0040036000345040da1310000d014821608408565858400c460304150301e050f082110040c107184c0903610070414040c01000d94510758007145500d046000003d0222030f10965108001201c800d04d181050310060320b48004524594858042c0728403d41d0015040701c0d41403224034040700103050001c01611400708004403c107151695010350b50085018007445003121600320304030b02111805034405814800d003002803500580300e0031079802c0c10003000d0030300d8260350200381490a0450f03031800100c40840f030070800700882d446034282130701c54000301741d51840d2900048960907400c07129072100210b800e00b120410005030f4a0080700850340a02103240201105004100385010031100b0766084600940b0381c1c1c29000d19050040d00c0318000c00c1c68200a04880890504650b21100c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 931521070 1250 931519820 931519829
    0x60423010515060c071508060a05011704080f13030f1a010311040519020c1b10080411011e030c0806010e010f03050711070e10050f030d030e1c2102030709 68
    0x1001050384000d4500500c00d80c002400c401e460762143c60346e00003005213071210440b2079520685000001203281c2d4402d4112003001031030b8500316802d544507a00d4015142c0c00c801148803500a0400c200000710b07030a003041c04000c40c8100c0310303480341c2661071a010b41d004400465840198620b080100041040c1d07900c0100000e00c195000070b6140c0f03484610081c0310f00e00c0d06100e40454000548440c0000001038610740c01802e0b500741c8002070743c8400400c0703c00d5182c42003400015851401060205000701e602c20801041410400c80f00100c100360000101041e0f1921000b107a0f032154252019508092605c2d0702510907e0801c0602230840c0002c2c02c0030188503041420150755a000402141c0110003180d0115904822140101d80d1000728080c8000700301d480e40700ea01c541c0440000c1a040c9120300006200004020780013080c10110120010140a506080d00d80300345401605d601004644411012a41ea529100100c11120407100c14032005804190703024410810001425404509501540c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 931522320 1250 931521070 931521079
    0xc0e1012020609100f030f0e0c0114070b040c090b030d0516030314190b04051003021c0c140916020d0c03050c060106020304080d0e03070504020a0c05060423010515 72
    0x680890011842d94022121480c1e0000940040c0c2100681c02c4511703103281100d01d50f400e0001c11100403510b000d8801c2100e2400c8a6484580c5050706503014050401400c00c01c112058200074007610307014402d00e000d490070380f02d03440b4800c801d1040101c1c07805401e241c00c8054000b0124005010f80080c1140b24244d846030303031852404802420180319030407800c5d59030100d070b01c0000103061030b281207901454080e01070403803149084115403c0c2c3c180341c01020301c1403640944c10341150b0b10319024006c032000e1008448422104516126001a4007a14200040c12410519041007601d040a204c0c40d402d000d00540c610141c2d10384e41c400e080b07030700140000104c0f96038a001444000540390a64480c0141c141e820006d000d20130000c25203a80c000050812158000b0444000710300000c0b040d2494500041d0741034041e00921010321040c105500140162081403400a181e82000c1d11083c0c00c00b4001d50301116400c1c010352003007041002010184038080c0468000b0080c2d820004000b0008030200412640035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 931523570 1250 931522320 931522349
    0x90d12260907090f09151e060302060a050a111002070605070302090d080d2a14070c060305180f0c090a1112060f060403060506010f080c031306060503030c03070c0e10 73
    0x111141600301e1001345c0c1c2d0219191054124412558000e014401510392001c040d114040c2032444540c081c0c04122500a8201c51601c07170310703c07030859041e1f104044031428060030318412140c0c1c15040040401c5912900001a240e500c103141c80340503039030041c10240805005100041059132088414010280d10440040d9514044802080900885840c11140c490740c40021500030b0700116217502d000e05241c0d5014030b0300c6030b04401a0321502031000b01402900c2c80760b00c02c2c005107000303502c02c50f023000d81030146c41c01980342111058038106204801c41102e4109901c04089820940116504818070b01d2040c007003c0540c1101c030046000c1d496040031402e00c0c070b002182d125202d2080403418600007500c010752b125140d08001001d040c05880840c000ac9200d00c955510300d00c5406444d001c3c0c0e50301241035182d0317117500e000595018003480060301c0303107591680000f40b565001c000800b0700000e00d02c080c40d180c1d0491b082600c03050026034882102c10144108101d00038041c42c2d803a009071016802c0760041d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 931524820 1250 931523570 931523591
    0x108180607030c111509010e0109200d0c23040c0e0405060a0f0308040303120b100e031501080f07090b0916090b120f06120c0105090d1226090709 64
    0x40d08120013200710f401d800303424100303182c0c45c4074100c00070b103c3c000400013800703d4100e4618042c2200c1da015405440e100c135101141c2c0b600340301e00a003610840c00090144e02c0002203621442c909183c00d5100d4076601a151603005051056880048a0003600710744c204481c0c1600c81e005800700010074403061117140e59400250080c2d94180303144014150740c8011303114454481c0f038400c00310703800790009401044482d5040c86000b452400b5040c6001c60250a080303800c800f040742680d10b074012152455260050601408108681d00d154074020100c100042400c446100e100a0070803803240c22a101c3d05041030b401504a44403143c0581c2c0012060010324a684100c05085032014515000300c960050700180c111010141d41403558001d030025045c01807036440b0a000c2089070458603040300300d03030f40054070540003540c020000b400301100d028045880082d090390301d09948030000d405000c0810513000102c4e8030030b907900e403000c190340002d039611a1361414032004881c2e4480c0140314402d8805d46503032900340c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 931526070 1250 931524820 931524827
    0x706050a033605070b0f041401050d050a1d19170c07030f0b0c091e0402370f0806040207021210050402041b090b0c1507020c0108180607030c 62
    0xa0104441103454940d50788001d40c0c80224414501c1c003900c040c4112807001c01c0070750b550403c1b80c9080d940310040f145414940700c505030280201c01001c3d418070209110710300c000c40c03050184134400c0402c0400020240b050740c5041e50419040102c5499680c8049002c4020340004040d02210a800002076406088500c2000301c152007400c0c01000c550041034000010800c0040c401c3c3e0740d03244100c000d01e10310b9407580050b848901070040c5003035110001448200c220b01381c0d0f041b50501c40c0c00c00307400545002d5034400142c03195003030004200300c1e8904401000115601c040240e582842c030610b040050450795040092420f00054610751143d680020140110b60704e550002e01e030540c440040d208580300e000010001002d00310b8007a40140c1c14104202c2d031800254284821440103602e425640c5800c100c0f0301003003900311000750709051003560f20215202c100032a05034442c0d01250300a040b0b090385100010041d40024010300c61004100803032a445000104031a944006136150003d104076030008c00301d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 931527320 1250 931526070 931526111
    0x607110d0302060a0c0507020d06050703060f080f2521020d0302030c0607090803121e0906070f0207030c06180320030c030309092403010612060b030706050a03 70
    0x961080312416040101500030034481d1141042480410000366400e02c240d078180b14451000307511074079400b00b4400007a801c2e8480c0390009020f1400041203500ea2580320200002c54114481c0e960000c1c024131b00c04002001080941c0030b803024840c1c181141800c5540b0880782074004d0400c043d01001841c007950294101560509070002c2440808201c2402d0194a80c0e1001141c844640140c900054185000d0410442160849d5000358581548045561047d0170040c10f00361650703407400520441c416502c4403d6000e0b80038000582038a0800c0800075104600c82da084509540020000b0000302d031180c0f904c08121503140c10034205503401240416500d004641005296a026440d00003018a0200504841c218254200d404850303a050805560313002d804c020039400025000054031002409a0181e00400e45404480b01049802c000900b076507401c3d00310905516800c500f260a00c41e06020b5041d01c2c21050340900f803a01c0c10300a0040091040340d82000178136480705d0702050740b501c624100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 931528570 1250 931527320 931527353
    0x9070f0312020f030703080f090a03020607050a0c0215030108060109060e0103030c140d02010c0905030303100b0c100615080a02070203151306050108031201081906110d050a1d0a020f0607 82
    0x140d031798407015441c01510100041e10034100807007201c400550052000100d9200c40c54050300201003594518000311002d5200b58107200c2000f21030240e034401a100c00803c0c0744c022120300740c055103a6040007606468060141e1011034500d007061800c1140801c0300d805607041d69003620386284055a58207004016035940200710b0b003140300d08402e42c82059410b43c000345802c203003561076005890346e420030155280800e0320b080c004455074202c208443c04500004194000511041d44e0020003000007020454425a00121803c07210030308500e4065406080c05501c051107030001c42c1412420303008281e1300c0364040000201e030454000403920384c08100d1100055241e0220040c000356844130f081540ba40c01c54607080520503240d0b0004540c0303840c00300d0150f05841c0e03203070020f8132803400544841c000b40540550342020b20008000031152141c0724041d840c8a1040f01002207002e02c10f00007c4c954441000da41d01c000c43e041240d043d001662403030408803480c2001c407880c6446003540e041204030340c8600d952 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 931529820 1250 931528570 931528573
    0x51c06120b0a050c18100918050114150306010e04020c01020c0102190806031b4b0a030605150d030c03030c0c0c09050a0608011a0909070f0312020f 65
    0x190801c064411030600c11031260b02c081c0601d403280c20041e00103000d05c50b400c140181e0340e0030394103480d420840c100d00040821484c181444680daa1280704025140c0340c515072080351034000501c003180001c2001403070800c056038030320114054049045698040900114104489111209000d54564041d241840e1805008654030280c40318014002d40c01254100440135200126007a41030151828a201d0348016000e0900c400d044002043c1c205581c0d5440c83d030101d040b016081410900d0004108403a40013041503d05085c000d160b0380e0410941c1c0502014101d48194406250f21a150304c2c604076036019402080b1a102c0760f41c2140203c0300d90b03003001d804c0410280390109065000262106103070103624104100400284110703003483da020b41c083d08411200b01d00b04645d0311340d9031290758807071400340300010308a031600119030940d00801d0700030030010003003c2551000d14040c2c985a0708100a08004d0103040d19000c0c04002080c154400034100d85180c6e610180750600a20910049208640 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 931531070 1250 931529820 931529849
    0x807050109091d030c0a02031005010b160f0813082a010f0c061407090801020405010c08070f020a08060901142a19180503150a1a12030a110a03051c06 66
    0x502d9554950340d003092348240b01d01d1440390645405441014141c03542400c42601d0a14070540d00c0d86050340c1e400341204c60303000395050030010404403000b502d101450414110120f6141071b04191501e51104042e001851401000d10320f01045200e00e07030941e08082c00d0003050104007800c280e030014195503016056034281421040170a1000340342234400d0410717890349031061352508820f900b01c0c01203010f068041f80c40120346802040d1f8001c041c20b24030744240c620030100c510a1340440c01440043d44131010700d07401081804880d242c2805403580c0706213013841d920a10300c1d0407400c1c2605154071401d100a812281885000540c040c031007101c510b88100300c5c0700e2204174402130000345951120240140b20001c170a0f004245898040355680c250011084c0350b407010385034a0080740040007000020b020107004510840415103980e00d18171502912a0081c41c0ca42c004903001512100c401424034200c0e4000781d808500013900401581e02c01149000c107941c0c4000c03050b01c1280140908d4002102140100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 931532320 1250 931531070 931531087
    0x70e0c0c10050a060614040603091118040b0c0903071a0c0607090306140c09041d19020306090d050d09051f0c020c150412110d08030a060807050109091d03 68
    0x80e001030780103404803c02040815542c0804680f00301310322590340b0f80c3c840200000c2003a03e210b600000c1d003042c0142550103035105210005030103419119100926990030504100a01680c2c11455502c03003c7c40c4501850210750304000398454501c1e02446a4030a08042c110b8001014401074860003c2c142040f103c007030030714070b002a042070824071044a450f801c00e040d10380d04020510b03c250081c0110000c5a040041080421003c0c05400d0200110201d190038010700845040010001c601c41c1c0e503031000d1296105005150910a00501d944150791145640d440f0b910303440001c036144506201030003c0c00d410245045410104c244440080c07220418410f145c03420582e03800081148140d4007165400700c400e40903c4002250340d4812814180c051008001c40610241c511004520401c68400c007107290000044110700c60207000e465580c008020411413182500c00c0d500641540801040a07a04e8a00000c040020300c0c05121400381c0c5070700300c481200c0c441d540b2030003e004d0340100341d80c0c880291 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 931533570 1250 931532320 931532353
    0x51902130b1b072601020f030c0306030a06050c130b090109030f051615180807060c2108040b010608010312050706090f15111e160c03110103050c0a02070e0c0c 70
    0x801c4e03204074034604107041c140703600d0005100f240c0d550b8450340710b41411580d40103101c80031a000205001c0e01406102c0902c8009041072280d40c2c814010762000c0c1c4e440c2e03240400504800c00d40303900580d102a108003d0240e00c0ea811481d1241183e0f4060881d440d4400d117490240c0c2414855044413180e410b0200e004107005405c116075a0341341c9129920340e10b02c8010102d5507450043c062050031016003001c1c20600c2518440c0e05020b1516005a168aa011081d00c404482210510000500165014043c0401c002d0b03c10600c03401495980ba00c2c803501d50468a40202d10180d42c0b007070400340000004c1140030007a19400001d00b40e07808c01c070705210924403424240c0c0707d141071340c05c900c008928100c0d003003104200c030005941c10f0701501c0d062a000c8408920b1000e0056000c0480802d80c00003542d29080050b0310781400030f02440c451804424540210000501907aa01408442103154140226486186e00060300701c01c503000c0c03150b500381c0c81e1503441d001c00b034030322400c0400da1050142001d61081080d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 931534820 1250 931533570 931533599
    0x9020403150b0607020f0111030c150103110108011a2a0c03060a060305061815010602030406120501031a0406201213050a08030601050d0f051902130b1b07 68
    0x804940921041006104201c10fa11804500139489080e0b40d100c0078031540318440307071034000e40e4000440380340c400c0c2c817040c2e546490240b044001074211100018410002001141c0590b82d200b800c20806550528400610a14010070f00f82812070b03010803c4415000010000040700708859004003042e240c00300c41b96150414510317018001e20446c0081207114041b8031440b000c89802c032000e01050b490300b09084107886801007406c0002d1080604040c0c29205d0b0410650007082643c00555803a460141d01410021600307001030041460040100302080180c1410f00000940701c404410a03030f1113140240c000c102201d480030703400c1240c2d810800441c01307040c0109006503003101000101e80d512011581c40705894000101950001e04a0303800180c02c900280d50440c505041032800c0c03a003050018000c440604070b02800c590f071031b1000e200719603c160171041a2000c5040c4107615021400c1d40030340c0301038094801d103441d4110004150105415404059807009148003c1d9090030b0360310702c40810a0003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 931536070 1250 931534820 931534853
    0x901080a0b0c0f070201030209040f14010e0a110a0c150510030516050d030804050c06030a021b010b0a061103090a27090b07030c020307050106170c030109050c0402090a09020403 78
    0x1c4204010030640100c0d042607590f4461504662858007550b9801100a074000102003034200d502c0361000310101e10f85000e80c0e00340180c000c0c9804525890b2007041944a4030184c04004020320f010007040324601204111814205c10341001384500045281115044040141e461250341c60030003440702d020030b40407100b01124000c90403516180c8121114a41d20f400e6403003000c2c0d024580440010019020b100220380c0b150140301582d0001c0c80110105d201d99004882020b403140d03000a003140c20184070035420080611030740c02003107105044000303e201c80215000f82010f00c000710082c00e0406400304102da1400e81c0c080c0c448020780d50b40b015441c10b07400d000c1207210503070780076980e040c680c0300c82c94424840c50307a800286000058440580550003000c40680c01c0c02140010414800461001d0044a000b40901403c00660040c42d00c0c9803414141100c004520990400f9000300201e680082c500c07060030000c440042e0303107074480c0f4000381c4894516407225107068000324002060012450011081c030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 931537320 1250 931536070 931536083
    0x1506060c10050115080114151b0309040f1b11070b18150f07080a03060e100816031a06012606090709150e0102010b030109060912080c040618050901080a 67
    0xb1001200c01703032000c510900500e00d40c640c2510340710030a842c0c181186074040440b10f04070f51414003444002c100d030040314100c0d00c000e81c2c03001a00e251070f410706100d640e00008400c80108200341e014a01ca00040d60001254410040034000d0958030302400c0c041880102525916650342d030702c40c0314152002080b20350784184640c41c035426610301d136018031003166600320148030744502e401490354544946420075100c2d141010782e11540030803c81d0160f44007a008485001c5030100c09440e0169040c80c10600c0c8000d00c0c044024a1010000100e6400c4848a06407140c50901031903600c3c030004039003d0818000c0001c1840300c3c0c1d400f08041c00582e00080340201025a40345500780e40d001021340700c08106210b103840e02c50b41c4503113041030980300d0740b100211444140300202e2080c200400103400e4906ca0042540c295139150b0845042188030841035010800d01c1c100030b503c0d07250800414506004d580f0a120520071400c44d1019200c605001c4400070f400000c1c1041060358542030070b10b90340d40c0301c4001104c90 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 931538570 1250 931537320 931537349
    0x41a100207060807030f02120a0e06090106180203090a0b18060901051e190e150a0e03121b07080417070b090f010e1003140a0501081506060c100501 65
    0x4861000c54481c09032051a1507010254888150840081100c10000d0102c16402d00500c3c4400414400b00e0303018038200c3d000400c0708492500500d04111000d0701401d5143e1508000f005902100341d49124107a0b00d43d440140c807030741d0719005c082c00c200307691300014055810a410001e0244094103081543c40c200c1045030000d6580c0070035507088a03420b891702080800300701d9082d06101c48140382c055104000000d000501d11849106806035102c0d005544a65000a110000f540d54107410041e4001c03401c8a080c0030182d440354102e44caa20030340d81401010150000010764410340003200c214445205080e96580780b0450900c8070180d0130a014894031500b0041042e903c0ac04000b44205c143c0d80e04020840c90a904903080101e8403000a43e80350500001c40d0640740700c2c0c0d940781400c3ea0345011680307000c2194900c1c007080200260000305950881490100188451f2400182c0000c8010950510068a0b1288800542c460041c68118407441c411007020744400159070b0411030481b803000395841d40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 931539820 1250 931538570 931538599
    0x9090106021509061b03041406044202030402121504060c11100510091d01050c120105060d02092809021e0f0403050d0302070308010902070f030c030e041a 68
    0x3258070094900e42c0251a10f070855000d0800500001c60b049031050230500b10f40500204107600b850b2084030240c414030540c681c4850314103c01e5500801e00b126030901090005440c84020030000303420410306e81c0055010000804540b510103c1040180854007125904000c3c66041e45441008071000c654640c20281001c011600640c1c1001d50714040401604098260400c032100504000740140d52040d651740c00051050309511919a1490131940c85600c1034030030a0029007990405808407404403c01c2050304591280001924195942254010398034002c0d00c901801900038068881d50041c01300c42011080040d10a4104240111403339454403d5956004c4034102d004074103e00c0503804041d5001200c40306a44002c10003000d461951604060b16030f15414500007801040c071010aa0002e03040d01410b4101030040c0c018001000107501d40f56180d502c00200c0c854801e402820300501c52061001c160180c1403220b1b01020141c4200b001d602490015075810880081990062200c0380560303c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 931541070 1250 931539820 931539823
    0xa0f08070614060112331e050105040e0a06030b1305060c0a0c110a030516240c0201030c030b191e06090e040503040305010c030504031107032609090106021509 70
    0x1880703900305031151110003074a1005d25014120301d01c540b1680700d02e0b12034140400c08a81d0322110450740403040b114030460901c0f8404050002290500017480c021355010019a80e0000481d070a0310b050919020440d1519590030740a00358030f400060075101c10303e0070031040500a10421510303d014800700e40705504d170700504500318820140e6000c00140c1813015180410001542c1c0c144200016280404960340c0e501c5660030724241e24000c14142682c03a8080111030340141000c0703102080d4040c001c504142c02400030f031060545950090600d038603058080400c0c1c1c0a50300c000185500940a84080400000c086150202e54003403500e080d406103c144036440d001c0107010341980c41c43c0d100e00d060320b818200a0954100300501c215a20300c400c0201000241c004e01558207039000d036850108140c1010702e00642400c508861401c0e142c0d1003958200081500180701d0244542580c48582100d8540b05014049120350318049402161a8000260070f640c0012051030800244140e13421507203803840107a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 931542320 1250 931541070 931541111
    0x2360108010b0301211523060d0b090307060c0f2d2703031d010f1e0504090203040c0e0f0c0904020f0405120708061f030f02030a0f080706 61
    0xb401081c14401030205959074001905903809031a02c030500c0a03c0c60340c8184001035203084141070b4a4446240c2410f08844041c6802c10380038001d480350b0246041c1c008507401e111802406130800d03c0c40b0300414002d6000b4811141130303503049581400140b03e8000040d00b55402c14400000133280500c074103203050b03e200280d0402030420b060350f44c0200028982103a200040190031341c402c403000c050380c2c8081704810914074001c6120791035640c154840c2c000044a000c004484060601c1000c1c007441c4029540071001d4122003142c4140452100d42c5820112403a002c2d41c0c014000070392000080c4802d004001c09448101d031008404d480c80c69851503d160400401902c20103180c0c04107000140e000d1506401421501c0c03092410b03641000d80c0c82001807004001c040f0341030030726080060700b40001e040920100d0f6100c2219611080182c0c50301c2882441c6e03000500c8003a003500a0302c0090380855400348100707c0301c030f500160740000032929801c4c00c149680c030144084a0301c510300704105100b041d4100e0700 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 931543570 1250 931542320 931542329
    0xf190e0304050d1e050706201e031c0506030c0102010b010816030b0901061106061c0809060f0a05040807080604020108010e041a0106020a1104050f0612010236010801 73
    0xa1414185480309101402c0c403c03034012a80ea070385014225150b851602071964010b8041e40c02440014a4408060440d849a4004096203a140044034403410b80004030522150401415a002110402521401c2d40508244840c088248480700d0400300015044640248411000e40d0448400100164203c0e11084142030104d840300300050707848030b10310405c1802d298180c05c0100d81d01c40f12500041c4401400d800600204218941c095101355040280c19400f480a454829604810303410407511800c6030000241240000903201e103640c0ca9a000391500807141741c410b640c45280c070142c05441d07500b02e8005c20040303100ea114001045d0400082981c059901a12140616420490f4031b2810000041c002d9407034600025011a84103100c400c0c0600030140e40d0f028080585061070501c2080711101000391182d4180001d101607a58070300103542e00b00038200e42070203000e2400c0c080540a8001c1c0380480d9a90000502818504001c9030704541045203560040180480c050f401581e91000a018 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 931544820 1250 931543570 931543573
    0x905011403121605030406050d0c03090b0c0a0e060c21040e0a0c110d050306010e150d0e0a0c15090e0f0610020c150d181e11090f190e 59
    0x3030b01c10300006400001c1040b40084245440240c0090b101e152655000b41d02c80000603000082d507804085040c8600607648a1924080c81280c495407208800e905000c0c180d084814000100340301c000b401030307500700400e03070001d40810748603404100d034070b03480b48014203074070038030500f44c00031b0340da40a400d0403c031030503640c1c100c80303a40c0151158480341d0010301c00003401d081401400004541844010404035404100e590b070794990343d00d000000101030038420a0101c6c080c00c010b07042c0006008902c82a80e061740388007400000c03d0103401038214504881074202404c84016941c01268902208089000402c215181c0100e2596544000c00c02d0b6141141c2603602c0c0034130700000c542d4615240c40c000c450040544121901182c443c4c00040d040d0811110039030400800141032400544503000740e10048410044a403900c03540303034072003000b800340002c80c01000740444000d0344108103c91170700d200019805800c403906440d001c0712020b5101c1043e104126460440b0204147c0319007140140b003802c0046a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 931546070 1250 931544820 931544833
    0x1020705071a16020a0308120702010e01060f1202010513080c03120c1b0a1502011e020702090114060409050901151a0702010c05012d1a0607080a020a02030607090905011403 76
    0xf010808410380b180d4100e17803041e00004004086540c5c403000d0150341482e007036001c4640c188a4400381c04c440c4d510ba045141a414084100b10b103a000145140482d1081800c0c84410b24440c40100e44c1d03071080d41c1c811981070503001c0c00030030b030b5207000601200c1c4642d0940c00c56000b1343d180402031800703028a4188070815481401180802c0700c183e140340d17003d050050700740d050590b00d070340c801d200402c0b00c941443d0050f0f55031000b41101d40c01d040701444000d41d03403507011860000c29070049852140d05008400c04119080300c0c3c054291102d00840d401401102c2040081d82801c80065020f00b8881043e200b05481000c8040b03420011a010782c1543c06107110f9132450000d466005440d10000081c0a81d01550b0720090031684560380d070340c10100320f074410b1340e21032703200500e00024400c89554044041d6100b002159607451501d41d0390485031200d070040c00b442d44801031000c0880c40c104030801d00035018046d10042c084495048240c03030b020b50b010724200380b10aa0700d42550030702d032890341e040455141e44046c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 931547320 1250 931546070 931546087
    0xc0307031814040e01091e15050c250f060605120c03030d0e0a050a2108131410060609090c02120d02071406040c0e070206090a0b090a02090901020705071a 68
    0x1d07404003002c402108004909400c094544207100e01c1000d00109810307000351340751008c001084038041b822209006042001c0e040694003200e860290700c0100510981c034181c000041c008039451000300c0359000068103078800c09440c024001d40400d1103001d0203002035500c044009032001c01e5401c01c0090280055050440e044508400b5004030310540c00d882c00b48500440101d00144408204e1500903402d41424074031100c82540035501c4081c0860400c03158500340481d2560440704007032525000201c42540080800c003103410820704c41c3c18950b0040c940b00c000907681e600508048111078a42c80c2c1000f940304001c10582c0c4078109942c820600300c0080000010f1152188e001e880744e180140480522020081a0280b6003042520b06480c80740e0341140130450b16410840142d400b4604d8400782800e810101641c41d40c60807444402004518150006401a4000c12165500e141c0041003417001d07044c0000810b000f03502c0b4400030380e4540104000401c100b1014401c1006c400c81d494099850042038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 931548570 1250 931547320 931547329
    0x31a0906010306030c09061a030702070e060112050a0c09050a0302091b04030506010902070c14091b0c0106060c1106030c0d0c0e1503060103060f0f0b1e0c0307031814 73
    0x1403290341810b6503140040b0114044800c402c01501d00034030001007140c1402d0313110b00004c1e1001304004100c4403c00401c5060341d808a02102110001071b0224a0b0b9160100140d403144a0302804c002ea140c075140421003038800c03941182c821541c56880d03101146071036205200c05846c1c40c0c04080d40003810000480e108412205040100c00d80107a00e56041540b40d0380c0f0710303003040004e0f440070310400c1e00850101d041c0126070b00d102c402410304003081c2140e175591102045805200504c44403554411000108048100004845000052070001c200c15500e41001400448072850709403a042c081c41d00303040c00b42c1032402c01ca0340034080780740c02c0ca4101640789e010200a040401d54501c01c10180103010601d503180c4046035003500d0f100c43c40c1c071a101d14080d4001001c4810550040e858a104000b0400c100445a403101080d1b6003480c480564032a03010380507503084c0180c404004480480024465015040800a0507005100740d4441041110188502e445142c2c0b9004003a2140c007072004000d0036261 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 931549820 1250 931548570 931548589
    0x501090209162a020907201609022208070603050c0a02120f04030f08030103200105090d0516080d09060518010e031032040b060d031103030403021c031a 67
    0x3c400d180051070165400320300b030a030301503030780c04003041a4261078100385c4103806501d400b03225848020084020382c0c840800c001800c610505141c1a40000c2007901c290500700f0785400c0e07182815042c0ca0042c0d85884142d81c82c0d030b040c031821000a02c0c1501040b03084d035102044800303442180e4020544203274070202496090740840c0c10800c4801e02003000000007280010510f07140c03406000701c50380f02e40c51418000350306080502c0034401103000300002c0005e40e1300b2900f40d4024400940748070b00501001c0c5809851f0841c03c00c49021004885000042d0105002400f00b0000d840765645d500d005aa4840503945401034220b9000d60b490b5559500f070796944070b0800744103240c60040c00c8459062021804804881c500d4451a000841c4507201a0001d0450f0512104055111801043c2490203480704641010302a1019120380c006001074014144507200401c0d01c08111401e5130795905207480c02039503900610000001052000107008007250182c40f603564005500010b41c40e08c6801d48007007080034034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 931551070 1250 931549820 931549877
    0x140d030e2e1a101b171e030103030e0d05070303031d060a0c02071a120403120e071e05011e2f0d0804260c010c08060301050105120a0303020307020316050109020916 72
    0xd424006c40002040004140840030441c400080ea0f0f035041d0f040c01041d20302e10403003203405060719588401c0040c40001341a421290103180004203101d90321360140101c0c003000150003144c45101b003030101d0030826511120303038000707140c0031502c1c5035542c0c01d8002c0101030b1010552821031070a01c20318035036400030203081d9400392007031414112680121040700110344501c40700c800594407941090000200744124500200c22402451b4010b516200000300007505205000300040b100c02d204002d1280141c40c2d000540a24260502e90340d90310031b1485060840e29058001e2038860702102030440b80c001c6228074010b681107001c030707600115645031002c00c41c0251b9540d0200d1110800c041c1c050359800784541a1001d4641c0d44200480c24003608040c01d654068005a10a4040b03a000b82910368000804103949503240c1409a1207a4841000b81e095001344035070070f000030540800d07201c2001019400108414821515602141c8a40d0401c42446254900c24004115a60800b40700b643c00f0401c29100308 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 931552320 1250 931551070 931551113
    0x315090106120b060a0f290405040903050c190803070e0a320301020315091e040606060f080402090a1109030a140d030e2e1a101b 57
    0x20741d503540c02014a22004102030303031421295402d0050b00c2c0340c2646440002c151205070140a45e0402503040c40f00c601d0007240207030110341044142081040079003904d00a0a000f0401c008100490a000e06294041c10b1400800c0c09900c4040403034450340c010b5403064a401c81c00b180d055a4801e001961000c0041c0c440550042180b440007d00c17400c1c20340c00d12a4001003842e110915000100f14001078030718880a64030990061040049000e54055071066070801102c107054270307031a0346c24407106035040c005501c00c924000c001080244030b00c6401450454007142c0c0c9040c006030021804413a0240140c40080d400a041000324007002020b8001144080d2003800710f03813410720034200007460241c42281c100c07480c7e20000807400a11005000c92000d54115090910049000d4007c181e120002110b1403016050381103081e180c4d030f2004c55064000012440700c104004103240c84401070210840340d0091140d803503601c108400c14800c241c1a441c81040c2c80025901c018582e44140007410041d6240120 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 931553570 1250 931552320 931552331
    0x2060c030903072607030f0f1401022205061e03100b16020312030106020307061d1b0906010c050a0b041b0f06080c0f1209030f04140a050d0203150901 66
    0x954043c040e80300100902012003a401c4200d1000c619141d40c40c04284160740c00c00001000071820421104103200e501c5400c103440880146441c00d040320701200da1000030b40c40410062090030541003d60848400100c105001550f902c4c2003211074030600b07500844606400d00e00c03c00b01510301020716040b40e101800c140c403007511a5030402d0541c0002c00400e07a0501c180c1304020550405000203520400700501103440c40d814017001179031324070806c80c0041001d0f40d11884104204813200000c080001c40400b66070044002d010415045519198403d00c540a4034011400300e60041c0b000c46400703a071050240c00d4004243d250020208401803003520f003c901319034000080400c04d071042c00503103a06d0058030101c07410000000c00c0404004c2400c0d890000800031401542d049006480107035440c40c0c0c1d00307a82a9682c4c544103013035001e003200000401ca00460301044011010b0010341000c101525550b041c1980d820400c0102c80a164020790181c0081c40007200c103840b030a5085510a4803103002059 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 931554820 1250 931553570 931553587
    0x2090115020d0c08161a010905040302030a0f2016060806010903020118051206091b130b010c02040507051b070605340f030806010c2d08030a09021801080a02060c03 72
    0x40035489904210798590b80390501014041140c086d0700d0250a016101308164501942c0284d500e12030554410203010768585000340725881a4a4200c1c0705e000e011503107444801c4244201d5556500ca07040441c0a105801c000c9846c0d40b044c4d40a41c1715000503501e845980c1c0c61500152040702d000b50015021084c1007a001ca03490b121400076020000b1080c00038034a0b0300d048501e040c100b801c1070031804c413090f00421040c86603a90700000c0b18610f0003081e0002030030507880401a140407040b0b0800a4005040004100c1c1c440c0d0054003400743c2454103c0c491032030900a81180d0340b5101e05001c0c01e0089602888804625105001c1d00204031810001c2a00c00700014150380c0d028840703004040310503650001d4040201540020303110b412140c00c3c01c201c01410003d51710307000c021070401c5180b90724210b20461000201134820980300d0a980000c0d01c50350b0303424468801c2c000707022014400e90084121402c048a1844c5441040e4104c2d4900c102510a240c802d030300700459584956208189444140300022 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 931556070 1250 931554820 931554847
    0x10b0a0207080f03071a13150b090f010906050d0203211308010606031103041109060f06070b04022706060d020405120a140d08220b040305040302090115020d0c08 71
    0xe0f4100060046807a80304074a8555044140034141448095500080c03214040724a034400e00710952000f0001d0b04690155000d81c020075400c0d1800b903100001e040bc2c0b00e5685c00000086059800c0244c0501c651070b160b80502140c0c009644009402d07034400381508081001c2c0d02480400c10001c1c855961415000c0700801381d0080568100540c180d6583c4010044035806219403c0141c21040d04a4258034207925507200561006c8040742c0a140c1d01c000040321640c64400071030b8891700c014826034440c41c560405804041c0221003c030300230040020310140410381c60181c2d8072003211038580c401042d0768100034003a0715008260700241549d024007000c980ca95820403183c0f80c00c070310701c0004d040d4040d407414007464018a56444051076001440c001124580c064040c551015119001901580c01d000c1e50301d10141d41000d000e8903030f0301d40b0800c0c4010940e0003401002224001c071618600c60b600d5009620040000f84004809a4401c0100c3c140f003e001c1c5140e02c04040c050740380e150500d40541000c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 931557320 1250 931556070 931556083
    0x207030b040c06020d140912030409141005182802070323041d06061303150c0201060e010e0601020a230111040e06060f0d020d0905060601030e0303010b0a020708 71
    0x715080c610b0701e1401e0140d0340d0304110480c240d0301980780200d050a0940d003518020320504110074003030b2038030280c000c55154042040718028403080c10308100040384520301c2000c403801030f80c00b981001035403407001030107141c002d6840c02c528400300c0000da070300d0f1280440c0035011403141a03421804604e1240039807040a2510103842c0c028001d0716542400316202d0f90b08501c0c2019020300041d409004e2005104070305503911040c0b510408840ca0320640d445202c0040c0c0c42c1e010382082c800003902c424001000308401d1610b14040d04090f140244a0101110000c0c0d0a84102d8021001d504c01d0f070000400c03074035500038841a003280060054440302d01c0152100c1000419411100600d82402404950081024030600d401401d40e031040c0c508042c104a500154008041c1001c1e1090102080e0441480300000c221036403100120341c2107546220411401004c0d21010b80d00752402e005800c001a0107500034011199070f440c1c0703a000b8500c1d40e800e08581c05120740041c10040c0862041d8000842c40f041c0402c542e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 931558570 1250 931557320 931557323
    0x13031413060e01080c0a0f0c02030a0c0f09020301081903050d06230a230307120b190504170c011404080705070f15050d0243080313030207030b04 64
    0x5060086007441c40180c00400301107442d504010009081200d8a1038100030388540b0903da1500200b010409281103544d0070940760043e5150140603c0d05080040c0744450710110f4440c0c01b40e20b01d034241d94404030310807808244200b00b625045507010b044201c0006a00300c1450b4442c0c14801d080402d00080f5034120788031500802d8a0114414000f540884602d0740d400701e90204544540d078450038001c481c842d01418540c1400b803c610f20754038041c1c0740c0d802d00100e03018000c0c8003d525a01c41440c109111144000e60361500d10740102d415250340c4c52550701403c0e2041d50007141c0e030203503035031021480c49840c1d001d4425807403c0d5603119043d100da0075403045c0850040b8011040d1507201c50302414400c2c1440c0d016400180e10607102c8000304800064042c031504c4e03d066a04001d503c581e00740c0c02020192041e07248460441d15070004402e040414200c901c0c41c1180c248010014500d1550f0460804020086000d07008000900008915000107006a5a614400e1058a41c4959255904459039006480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 931559820 1250 931558570 931558597
    0x303041e080f1c090b0108011a060919120302031c0b010203090f0109081e06060a03021503041a16031a0d0803040507080a050604050c01090f0b031b030c04050a120b130314 75
    0x4009540d002d0044d4a40ca0742075030340c80591400c040300012012f120b0050070074010050f00d1440d01046544030910b200a107020719185e81c051f0414070b0000d40701d90142121840c80d1a035240c902c140201d440c410f4140140c1c06070001c503e00740120040080e420b0007416070a0401c032000c50086504c09043c8002c2003000d0001d4454000e041940e500d060402400a0150f40a0f03550607000300050f0342d501c21540c401d001062460355494070341741070204160b240344084000744031800003400b503d40c01d074081c0c4503124007195800300a038a547c01d43c01c40820b403500910035071044036011404007103808a0025a000340c445e8081324070b040c1d0b4503c841810f010041206440e1070304603030100400c1c40070500c40c1c3c0050072824600b180350503061a009800c1d44825001d410140080400000c0e415410100c9070000e00c240311000645a2031b0200400c0c1141d807040c00340714010280150001520b0130b10705031140d40c16a12540700c03d0070383d440c210090f842c46103c0c0801d40c204104058482d4481c41a9001040113551949 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 931561070 1250 931559820 931559843
    0x90c1e0a030e07090221070e040c0f0816020d26010b0318430b03011e050f0f0102030d0f020403120c150b1207080303041e080f1c09 58
    0x503003845081d40c400c3c50042e004114405648060500042061031106c1e9800001c2e121400700f110504403900140e41c11620300000c02e030719560004080c2c61041c0d22641d034aa41a9280c4035620038009803d04c49a0140c3e005608481c9101d02441881c400a0030a09000034042d080da09001e041c02c41c281c1c0f04480c0c0e140004180115140324032002030000c1602d0f001080c0303611407004602280314140c4c40b203010b441c404065503d1b5036040318010803404160003011111150f00e41c0000507082e403080c410350441e605e2103004c0781407201005804004403400100b008200d10311040500c42c203005100f04070b50440c00104511039035a1b0b482d20494903100208080142c03038904500d03100b44490307020a100c0082c004081c1526001500070801d5a000e1402d030403010460b0414078000c181da8400b100d031f05240354041c900c0d02081c0a84000090b43c4901e0003840d6060fa449108036401550451001c00646020000c011482e441c403101d80080c20b101c030511003d00e0000c841668001c0c226440d00c901140c4c4070f001c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 931562320 1250 931561070 931561091
    0x901022d1c0f170106080406020f0309060603012f1e120a2304140123040b10120b1b0309010902030d02030306130509010b06130303020714090c1e0a03 66
    0x71802d6002c00e9603042915511003907003d40801040144200c0040040140c001002c004864065030744900501607841e80f24107144134126142d61048582d14000d61814560b03010050984d24039600103070102006401840071691316681c1c0b03502480d00300482c03040c1d40803811442d0000c400100210040700e07602240030b082001740c0501343c0c1c0f15280c000c040444a400668107024080c0b000c941c2040d4040101a090808402418054642060000b80c0d0106490a0180f100301c1140030f85d01c40c80c4285041c0c2d20503a6503403d4282007001e00d01a041c01010300154080008640701012500812007024031118020807c8000c400c503441110352681c242d464607040300441c141003100400780941400603508628001001c50700410b4601b0503142050740351f601107049070b80290b11105030f400700503000da40ea4040c0010b550700a1070041c80b007180184156000028035220582d006907042e04010031800c40c6071100000072500e5008480c0d003403008011880400300c406031100090000038a5603c1c0803d01d141d91 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 931563570 1250 931562320 931562327
    0x60f08070306031e02041d0a1e170a03020d05070f0210200706060504060e190c080a050402030c090106020d0f0e06160f1a0f06060901022d1c 62
    0xd4036140905003041e205100160043d800d00c070031040b54280d106080e51050000034041c1940e0071219040d9402200c8403072401002161400700e02d07004400c003585202c1184541e050302c21403600054034800144800200d507189a03001082d60500c280703805418580c440518600b2214144c41400205c0e8580c0010805e4039014802d00f50f01074080d10b01004407981c400c01c00ea0b42c4085812010074014000508a0100242d40e40103102504000d04100081a01e03003080505582c800e6821401110340d0b02c001d54103540903405140398aa51680d10b111090b21124080381c00b0b4040600100da0600900e9146100354941d00040c50082036a41d00030004810440c6c4050405071405203028100604c50f00449074030f4540c0c90841d200408151104440800d00d818080a0146160700080040c6002140103c00f010b0b082c0c00d107800384900422420041d22003108221b0340b4880d490a0780d0142c0c005031400b4030700007010b2200707a1901c00c86513414051018444a510308050300d00c41c14181c400005801f2100380c03a070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 931564820 1250 931563570 931563587
    0x30f070c12030f050a0e0d1b08180312210c0d0c120f061a0706060506041502011a090a1a0312031f0e01141c06020306010e0415090b060c07060f 63
    0x2c0a1400300a151020f010301507c41044100ba1401d2000b1000d446088800c04070440240940081d621a118400d100203187c11140145186200e441005905e43c20506104203c0f0003405d0303143c040c103004441e040b100d400510700041006920000038056a074810b0f000b07025400070150917075210101010114104000c4595080c001c440d4185403000a224403910311102503075440c070900c2c0712601c1e440140b0b400c101408440e04049e82000c070100b00047e40d41e140d03401840ea03142c040d800034014165a0411910f90341c4c01e001c0d400d503000c0c50202c0402c1224a19601030041540d1440844c540080158042450040880c1c3e00340401080081000034003a44005542c003166041b21000c03404620b4903902d00e12034001801101c400500b1000c4580c40f665414545d611401d54014400543c0240c6041550003504200d03840c5000c2459080d00c245a407801d0701c0350300c0328580c100140701c984030b040c100c0080040400c1610603030012020842135901200400c5244000c0a860341d500c40300d84000d0300700801040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 931566070 1250 931564820 931564831
    0x1515040602150a06061d0a0504060e18030a050301230411040e0115050901110a0f0605010618050102100207051014010303020715020c040506030a062a14030f070c12030f05 75
    0xd10300075040c022070b03511211100007a030440c0c10030142008103070002401d00d80260301c200c9d40140b0b0100001540624452800c1c400c0042040d41e030250361810703440c03d840f03104040c2480000340c020001440414600c0410804429007a500c1c1810040800041821500c500d403c460759000c01180c20462007600e4136909002d0010140110404240b01202419600030f00c0099818080e40011242c0407039030400c04c61840c00e0300016145520203550074100001c00d070a0040500040702c2640010300000c10f40c1020302200c0c01a4010044402101c62030b10013500848030803039441c066905090200019401014195000b0f0030000045500d50700e000f030b203482800c0e40091410f252052403e8401c1e500801c0289050400380c1c0c0120b482d0307582da40003906101890500800342c61903d524081c2540b90032038504840c00d2148c019070072040c246903082d03a0b00f407803181d00224500c60420000d607521200d54400d41e007191460070241c0240e04203988400e9030380324a5040c90f002a03941c04034001040f0700c5001e03483e00030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 931567320 1250 931566070 931566091
    0xd0e014b0203070b1308120106050d0f090c170c04020f0a0e0d030e090a0204080307060c08090a050703060b060c0d05030a140c03040201030903050903150f0f010e151504060215 77
    0x3e9a03a681e2003160380d10092610b1903480c0902a600700f8407260308201d40d82540c0740c418030b55003036854110103016a0403550f4401d150342d08d0b044140104c0c066510481408a40220041c03804901c0c1041d010701c00c2d0380031618100740c1d00410a00f052241c2759030000d4049101c101c44279a13216a030b81703207000b004c845600301c8251040180110b142c0100b45c11296608894a040c0c404584a136030b1449080040d1103150301c008018400050b80f117090240c00d41c88100021110b640d602000d849020209a56088200e401707001c0350001d200c1000080c0aa0b0302a544640020300314a0a00040c4d800c030782d0400c60b9401084020400000c100b000005051250800da115448030307004a504082964980c030340001440241415075824103181403600540071340f050054020110798140e54110b03080c094044054036001c15481600001c9004a031501460324165500000d025070f0f143d991210180e8400301c56480c1b01e4004640e10b000e4144841080020300103403409400519404c065800d94101007000148403240c0b4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 931568570 1250 931567320 931567327
    0xf06060d150306150b071b1a120a0522020d020307030b04031428020a08030a02070501060806071b0309050306040809100e0927061e090d0e014b0203 65
    0x21411070011b491009403c030010003e03061000b2484404204e680d0444039001d1038925034203070b02001300001000d015030710745506040d0761181c0c0c01410548000b6940442e500704100300d29401c103c480e900d0b440328580000c0100d00c005210f40c020034186a4160000d4607071003242003c03c01410740000d92240c000c2c102d006014501200d140c1c4091070b0810701116940d070483e0301050799445602c20090302400710742103036000790349087c107a80a0009600800b030403502da500f030440c0000c0c25034002c50030074805c0003107488002150054081c240031020f24031604506000205502148948007088031610681c842c800495551240c1c80422602426911411003040100c500b0240e047c0c64003004207030070401d40d9203103030744030035480305411500e807001c107141003c900c84d0300c00b00101c0d0010b41d00500c01003200040301076441e8035030f8201da94568900c040c201e0041020603003d0300741544241c0c01801420302c240304261080c0401c06840004503003040c0d1103a14910b072000041920341841152400c61800c0b40011484e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 931569820 1250 931568570 931568579
    0x30213051e07170a0b04050109290d170f070c140919021c140114060313030f030e0f0a03120e1905011b170a05060303030f06060d15030615 61
    0x40104900c003c10705409400400c21a01d1103401481c264030f0300034818001d40d81c40f480f001000f80b40c00f14601e01d5030494020700c10040ba800ca10b2217078071a50060a025002c2c10603455804094110280d0400e10200802254050018640103454047c2c4074a0035905041d141030b007aaa4160989126903210b100c4a409108500ca0341c818024226245613601603210301200e00d408060301c0c0b000407006c0c07100341401c100c0342c0316410414145069900b0700050b06000e44801060015901045039188030089545040c600424050111076030b0340c07610ba14000c5103d0150203149130600201c8041c400c510392250302850101030700000b1101d4916210802002607481e4001900d07524044202c1c2195020304a006c00400e100c0290400e0056035050803042001c0c0032000302c0182140304d500381088454040d8000b00b00c0c029401d0041a0003994010003c505507240c0041c040c40800c1d0280c0346a51058040081496200c05030003a1780d0b08402c80050308401c1869414001c0170340d00600342d004030841d003041c414003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 931571070 1250 931569820 931569827
    0x10e07080f0603010e0712050f190f0503250528060b0f10050d0c020a15020d060e0a02070203190c0b0a020f01021305030c01090303050d09050106030213051e07 70
    0x36403129128101d8001500c80300c0119004100c108080d1119004078030307001c5035907040b070003907111124817440403224100d0031910120307100c2d0000c045881d010808141c9100c08a000a9101061035010b06c1c00c2e20b14000c0440107803480d4040107800f00360b40c0140f00386401c050000c2030148a040600c03240792000f04448007480e9000c0d041c403051006015640e0b5442444c0d032903d81001c41d098106001c2d007a20a55032103050301a145402c024001741501e0f00340f41522400c0c51008c40c4080000768030180c00d0341d501e4200f000355406500080c10403050b190ba0b403100021050000494580a0741c0078600042e61920a401450700300036941d8100c0000d0550a50848001aa442c1443c0100e481c24040c03591566800034049007040c4410041c3d00c00b80d0300128282d0390707200c0c0300080101119000c404a500703001d01c0e4401525600d00c24030014011174411b005040f5001400c0c1c024204c1d25100fa80000703034080e1a82e0008050f1504400d0750600c0d540c0d20740030450140000300310f403210801c4001540860b03150120303004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 931572320 1250 931571070 931571087
    0x190206060102011a0d050307060207260906040e0601270f0e0105030613020102030c0a0302060105010f031a0907051e040911040b0a120f050f040303060b0429160f0506010e07 76
    0x8501a0f80b0741d00d080d170140101882601c0d1002d5000c1415541c44000e1b05242c03400c00051030620403050480804044600041c0040320501c01c8050f112a060a24202d1110700b11000248440e051160700110b601d001880305c210800c85000d100040c00c030541c28540005d9010007160403810001700d01c03000600c2035a50008000b50300038528620340200f0641840100e065000380d0410b116284500ba081c0d808041d0003080b40345c140c8500ba6540c00219140b208101c0c192248820340600f00708810a0b000f8150074174204050b40403c032400c281d07240c80a01105204007a015010f030004200d408031f010700c60381402d401105950081c100c4030b18105810314040c124540304001c0c0310400d01424031442484143c1e1500b00c108071428103072080003181340c400e5900488200441c2e045001a00c1d020020580c07242001c16182030355200b0481c4000d4405683e080c44c002118026066103002040c8801c007100c403500780d11991014411100300c583c040103841c01601e08401070708121000303030005007084811a8440c200 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 931573570 1250 931572320 931572371
    0x309090b0402070b010e0f2412122d0702031203040303140405060619080c060c0a0602031f050a18051b0414090603012a120219020606010201 62
    0x50000ea0a00000d402841680d10083c41c0c540d80d00300015161010040d8184a550091042c035100d642c4d14054120301103168071240400e44580c01d01c0c5083d4181450f1101504e40303a4011503203800c4040302008031030b411046a070804415447c8804002d41441010000105030510f81942059095400603403222401820702820300e4000c40041c05040c4647c1102000301080408081d00d42882e0401381d8850600b00d42c900d020f4403510046561a0f80c0720001d00007201c000700007901904140d4420010b95901007500c031140c5201ea1036551010414601c019401501e401807008042c08104008040c1041c0d07980c045840b4142c220010400860a5001c0c2c601c0700d1603c5900184a54400b000d1030201c00ca1406421114100880c0c0401c3c4445403864909000f6011500a0125901c5030101400d0320700209100c4004143d1202c0c08040c40c03082003030108003101a04001d0500a84001000100c0e00841551559500b10f00c000e50842d80c4c060140f140c21241c2840280000c90b0001054800b00303000686 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 931574820 1250 931573570 931573589
    0x111809030c1c17150a150e0a031509050f010c0c14030307020303011203020a050d080601200307020f0a0e07020a0b090c090c0f040f1d01061d090402150703021006120309 74
    0x41c070004c04150907440d900302c001d02d060000e1b52155000c2d000904000f50640100705041417580140c684610300c001241d511a200074540f60081d0044005042c0d012800c540750311410350300c8801c1e50828060b032003186040d591840166492820150308003012034181c000c09800400a1011141d80801140d0540325030f031140e0142600e903860224508850314401410714011544484280303940402d0060280c84240e0303600b11141075910700803100e0305400780c07490001c1c2c4c420084c003c010300300100d8010f403070400100b0300480541d40d040030120900040302e4080041c0c005920410802103401348003070b00104400b0040c12011040e8011400e0307100041d010540050000c00e08c071881005940484020301003c0c0364040e9040c5d55460721591f40100f00e0302d100003c1e1230500c00441d0152280707101c10300449420040460441142041c40480240034100340d81042d0704450b191303240c00c0d1800041082911a40c010000c0308003441c0d00d8801c0342c005400c01120030000c004a003011a6006c5030480a6404104 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 931576070 1250 931574820 931574867
    0xa0b151f080403140d0c02100b0303120a0c030b10030b10030b0d02131d01020702100503060a0611032118010b102a0f120f0507111809030c1c 62
    0x920b1307600c0600410700401a1079061449141d0040c2e0f001c50850004e41d05d1100900000c00651304141d00c034003840340c1c8203d1030060180060100201c0381c001c503a1407000707070800080c542081c0010944150300020400d01180d101e2042c0c00720b5083c08894822504154503042040c8810080010b441d01101e000280c4200071840020208003402c0d0301c000100f20212082c11951300750f04040b00d0113500144000e074801c4010203400800d850050b42203a01c6007030010039025402c2c1c1040300c16601c8807001c0303406148521081c003814044001c9040c880480d96106004188030749803070b03101c1080c0940145028090399040c40c01d21525030715000d61580003002d160410165081240c000c00e20640d80b101c103064029801a02d150041c0062a5071003400b0ad8024a07008007940f0084209a82c20140c0103010000030300108444400b040c2c144a22a2081800030942078070030340d010090b01044c2c074042e00c10301d0701d5410008480c032520b8002c2020b00e00d031116000b01414142414080030b440000c900700c050070308103642e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 931577320 1250 931576070 931576097
    0x403080d0e01061e0b070b0105190b1206041b0203031311150a2303010306110c1605030d0e03030f070c03140706090803190e030a0b151f080403 63
    0x1e8001e4049408210300801120741e90350340403188400d5541004048480304d2001041c5a0301000c00c94440c0c83d00601c4e800c240c2d03440d0106002108100541154100000c03d102082c03592004d0020036181e01a60b405a03401d00b401d03070030041120f080c0c03405070907403d060b10543c606154010050700c0d0710000d1320944019003078003402c007210784040300c0b010180d00c000f4011075030b500703810100d002d40004051580e404141000100d011006a0b85051140d803074a40280300400014000e50003100713500c00c40c003440e54100340d0286130051800e4500c2c0050954a0304a10040c88a400e0401041321040751503d07110482e0108680072948034814044a00c4c8035100001d015070902010003808d4008503442046000b40d41d2800e201d194440602e03015910000366000000100c00038008252010742e49425141303450901c036100305503a16a242150560180908840c9402180300c029003603100d052007010500800d41201d0420000980280b20344891070712610b00d4120356170380304401c0c7d90300030747c1818504001c1010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 931578570 1250 931577320 931577347
    0x71d040f0b09010914090a030c0b1b0d1a0a050a0e0901091a0403030c0f020607030c021908190207030b041407050d060b030d050a050d0b120706020609061308040308 72
    0x16070346207a4001c20034000000b4449000c1d408101007138400290200300d91074005102c0c1e247c0e103044801030000352003128030a0200342c524000ca5004251148600107041d04010896920707040002350002d442c1c1e445054044100410080c5410712404580c10a5502c0c10800000c41c0151f0b41e02891001c12008000145080c0d02503100d081d040340c002c2d2185240c00c6c0404100e880751801102d0440c0003074203181810090a02940c008420000716030060410383c1d6480700214010032110b600401103110303c1124528117800f090040341c0e094003441001d580d03859481d100c0d0b00300c40740d04601c0310304541c0490b50400c00718400121150708260322400300040d214005003400d150050725008180d01421011f200002c01a043d1711501180f0800c0e801d840e0100c101083c140c2d00c90042e1002400801c1e0100035403084194168007205c1000e2000300400d0b9900e014590061602d0840d40045016a000034103100c0c00060420800d50701050348298440780810540e04c0001502482c4001054280082801e5001104 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 931579820 1250 931578570 931578581
    0xa1b03020d06080a050304031e020603010b0a09050a06051b150118140a05090628020d150b0c060c190c1e0c140103181b03080d0c08071d040f 62
    0x3e50300444607080c0ba20700304240c50354030900c01200c5100c201620300709c1e060b10307134000408a1500140450300b5030b07192961800745036004c42c45810802c594220b02103840e5446400c21409400d841d52040c0c1c40d01102d0b001c030320107803147c2d0314404116880795075041209140c07011030354150b03150000881c0b40d19154907450009031407814140000c0c0d51041042144441c06944914442c2400c00c0884115440e2082301b1031403042d18002c1110610702a00001140c214140c00070111000e40d00340004038000c0220901d03440c02e1240d0400314410400144a003076440d01080541e07000807441a0080c07401e54080d00c180d402c1c3c0c03180486082402142d4680006001511081d48422074002000c0c50801c161450b0501a0f09024017801442c41c1c0062040f80c910751003031252400c1c59007a40028110301c491900c412013120032510b031000c10314000003008800903400001a0103082c8213890080707401900081c0160611400600c40c5082003694000092075010902e500c3e45200d1080d1030015107024103000e035402030607 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 931581070 1250 931579820 931579829
    0xf020307050d02010b1305130b090705150909010e09071e2c10061407020a0503031b0d081311060c010c09030606050a0b0d0203090a0f12080a1b03020d06 67
    0x10381440c144001d42c040d00310394102c070002c99400441b010f56036010001c541c0103540e00c501001c1580440c50020b0040c00071b007500210800202ca46a0342d403000042c50740e2102809102000c01c1c0030994414504101e0406809009000710780100383c505011a1641c0c0d00340342c411007450301260302104c03002101c0400a0030240492020704000c10034203101e10410607030b0594052144040b4440000c000991620b620000d0782c078241c4d5800050f00610750750f881d05401c208020b83e4400030104000401c0d54003000249040a2541c0f03010f0301c0928240f958a081c0142c05400000303024550b4100100b40e00f80941c0e208404d5804610141100b50078000700d25207000d0344075000c0b004c0d0b00c0e140d2804800e0384c000e440003044a02c5180180401a254002e00c0803000003442420358050041c0300380300c03504009402641c3d0010900c4100e0390241d080e5140c50700c3c0301202d400142c4015444014544803181d102c8442d5500659500c0140000c421100007403040751104401001055404211003a140e10341d03030041030092 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 931582320 1250 931581070 931581073
    0x30c120106050310060302130603020c120a120605010804110d060b1309060609020403030f050304030e0d0b0105040506031209041d01050a05060102060a090f0b06180403110115050d030f02030705 85
    0x3980c40700006412940141d800380a450030303c8000080ba070b442030084800b02100740711182003261905d40140e000c0c0d001841ca00145020340600c02102d00001805040802110740d00d06600a4485200c4030071a29240c00050420042c0c0042001203409103100c59540d000651320403c1c60505820a1030050021601c82540203c405407141d0ba8105176400202c10b06010320020070240790790364031010480c800c40c44000c0100300030709040940f85016001443d4094000e04141c6035580320b02c00041c81c031201482c03040702c110a000d001400542090300c1404d60213081030b070051546507041001303d00315000c0c010b0b20720320032900c6424800749140784004401034890b01000920960030180e100d075000c0c05003200c1c198010300c18800052503248071802004e003225088811041102403548801044a01c02030040b030304140d040003651b11503c20900c10034400e90080e9211840d03181184c0d41c00f803e59158002c42d19804000c0101441250303911070403804d12039414107110318154540c0c901079003903029a08019029 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 931583570 1250 931582320 931582357
    0x5060621120c010e070e0426070501060314010c2a0204050a050a0c08010f060806060c030703020a0210031a120f07030c0302090c030106051608090d0309030c080a02060a05030c 77
    0x480d16200501040079100b00207200c03c3c2d2503070b54055901d20380745c4a1b80050f000c4000c00f1a004c44d00d07140903080e9603d400c0c140310081034160000c0c00519804200304480581d91810204180300b40900a04260410400280421030080300010040d000c203011420000111401500c2800000e40310386007074035400b03842404103190001540009103c01c0740c04078040c43c01d2424020b034062040c0c2d505410780c3c51556241c030301542442012100510020b102d95001300c0c0401602400201c100302408245200364001c0649411510601607804024540c030001d05041200d000130711100c4a0f15000303074003410303110082080302e481c591916142074580510301034045c1d0180802400320b500960000d5074029180703891240c8503407c01c560148002d03c140c030000b070014800d0148040c02e0800c40305106024000e01e40c18001803100044058a1100045001ca145002c0c1002080050f0154000400544000e092024016004500c0b148207c1c1a440100103000000031136480100b4140e80001300b00c40541c500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 931584820 1250 931583570 931583593
    0x12020307020a020f03010f091a0703020f03040b0702070f0b0304050f061e04020409060e07150513140a050316060315050303041203120903110c0405071b080f1602010f02030705060621 80
    0x3021a0b01c0f1054650440707827000154203a402030003184c1e980c548000f800c07461595580c407200b1148034050060390450081c22800a01c1c031000b080c2620260501d40c10869890916140091074540c2c08903940c3c58a1304500704001d0004000e01401310405034000d0a07540c00e0f90340d8800100100828440100791a24041e15080c0b0f19400283d94030a2740c0400b840b040005102c603005480501811030030740d040c1c400402042c886034003002051145c1c4240600701c11f1031552074600280c01c22240c01744142188180d000200037407a414000c1c001d280c01420000c481d1681488082600d0344142d000b0700c807007544170510352010580700b085551500c0724115410400d80f18180350003000d0801d940c0040780c2903c5041d0804096250601c1054080e95041d140c4200c161008140d02d42501c0040c0c400303650203101808600545440d0341c0003040c600301e2501042201d0000ea00c0050103825621b24a0003c6500900a070400180000751403504040c003103580000d000c09120f01c0600c0288c5502c075140d40ca006e003c042c180d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 931586070 1250 931584820 931584833
    0x510030b010831020414070809150123012105161b20030106080705031603120525050d082406070804050a06020601030312020307020a020f03010f09 65
    0x62003036a00766034294990725032140c45420143c403a007141e0000c0c0e80300f00c01d180010314a6004403514078406400441c03461180b450503048800d0072034400010401030820040d1508090041c110040c0d5900305051603941001e940450f500380680c50548040054100d810685e805a0b484603003160010000075100303080111040090007040e55000c00600840250002207400344400c4450b09002c10f581c8200702d2829118a0702d9900001007042c2c242802140c100c1c0d59480a0152030701522241c0014461146001c007898502a02c8040c92401041e109201b030000440446806417032064074900940c943c8a0b07922865a2a4000100e81c160241d40006980c2084408280e210015919843e1901d583c2c0d2102c07001d400911040404082103241040720441c3e502e0030002601070305004a8499007415110004540c160619401550159101500410416520a03100c2c040341241c050250300310304044002039591103030088006c0c803400000c2c180040f00c2e102580200030b00c0316030250500c00c007446401c00e413 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 931587320 1250 931586070 931586081
    0x403060c0912081606060f0816060c0b04030c0c0b12100503070501090504110705010c1d0103060609050108060111010f1e060302030a030503180307230601050604091104051003 77
    0x3000401e240300c40c0080c62501c540c490400c00740d002403070107180c00d07a10502c0142d10700c64002c0807500070703a403100003150b0900c5001464018106410040140c0803580c049031030020384680c000d41c1080340d42881c190000784044180394101d80d01d810300c1c0041400c207240481d024081c503000480b0000001ca2109035001e00d050901c0d000b07441d90842510881e0b01c40090588807003030360080c82d001c100380c08410030090800e5805040c0c07580c00c0404150601c5200c1d0f54143c03c2d01c01ca0b1081400181d2500011108040104907003d004036090070200101443d100b4090031480c07541c400d4905001303110000031816402000c1c0100621231800007000304a0319000744900505c0400040c40e103100c1000600c5004400ca80700700d40540c0e070014000d240445203590101c803540c1c0010000d60f40700b0058544803034401170401c00b51114601c100241c2d280c1c9400910b081c01d104d000c020007000e0580c0900010051501c600341100c0540700f140c031000c00e024a0b10b614a6029104507803001390002c5150011003411030341588407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 931588570 1250 931587320 931587341
    0x4030c0f03081e071d0a030f0503030609101503020a02010f05040c0f1205100209120106030303090209061e300d090b0c0705100903020918060a020a0806130e03040306 73
    0x2000c000b18034002ca07040f1401e20444040c000300e2810302190b01160480f2210a4201301300909203c90305890399030f141040000703180105c030f00740c0c00402404494a0480c4c106507004107802c0803a20300d02d1070200340c120b040d018441c03020b0600d6800285032461038401e40001c0308680c0c03660401c1c8803d0400d40380000501d05203101c0c000308860030040225007280f240c240c2414a54000001307290119038900950001d501c100c106543c0020303075844045c0840400e000b54402540291800115100d56005100540100804176440b441c885016950032000c10308000800c040203a40121106020b0100044000842c03040c810140e80450380c01070342c5480004004031064580e81c0c42080a50b92441078561a00841d96101402c0d00603803070a00241c02e00c405810b0760850039103040d01001d0740d01e402140c024807080d24030440c100100400398041c40d0301085680d80050040300214601040c0c0c5100a01034000034010501c0761b240210241c107148044e4000c0d8546104000540341c0e580d5907403600f0002011031101 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 931589820 1250 931588570 931588591
    0x911030c010f051b161707271505061204060b01020a050a0b071e0c03021c09050103021c02030720061005010f1e0507020913031704030c0f0308 63
    0x22400e01035205203488484241c06456141c1000044c08a0050b0003200c034108a083e0302c185c4c1441d4401d014960208002405a1000c11804164900f0366600301107903a003040c03240c1450000002005542c03d00385007117200c0000000139901c244800c0402c850151507004ca80c2c0030301c01283d000b401c50f009519142c00340340308010401c040c14044d001603031546000e080203003240e0480054800440c8101d68401e07448a00e07854030341d40041d492100c070340700304c050203100c0800242a0410807080540402000b50900301d81e0000c4030000805a00c020324000c014050035041540200b1420030401b4000c4100d8216841b9400030340d20392402c0301009041801070715456045048141149040c40300c0821810f0041c42003101c00716203039042400542d40e29004801e01020419401c1004010800500040d2848502c82d5505561841d16004018007000d01030718414035449948058000242c00505036108071003008a0103480e5602d034281640c0d055103903103018054051343c0e2000c0041585c04030202d446810202e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 931591070 1250 931589820 931589833
    0x7061101050f060f091e070c050f0a0b060112020c0102160b010b03040b07030b18010806061503252604060e03070f060f0e032106030a08120415091103 66
    0xc802c5034500140c038a9500700140e50210600c908214001507400140d05c08002402c101ca080c103000c040104903a1600000c4007007030003101b0408144410072011100b02e00a0030060500c1c0ca400b40191030140956040c00a5900c0280d030100051b01500c202440a0f0000c5488040380b142100c0c034a125035804032041043d940004c190041c80d0400c1e21301036500b0a00c210303c00d40d00d90b4801c0d0010b0500e095000d0303000c28040000c00c40d214404034024042c05015010702003e050900912014218110715030340401800d00030482e005c0c180126440c04000c81c03d44050701d10307076418001d4801400d083c0500c0610244da8868000d82c1046505803800f55106440403c210520090aa07840e030241060041130b040d00c009104003c01c615821080014600c140001450306101d001300b4a15030052400c1064512100600407407103403d03040090b031000060b0083d14421001d640d4a00c028880d015503244144070b070b480400c0911140e182000d039202001e07141041079072240e0522020078040f9404103480391007202d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 931592320 1250 931591070 931591081
    0x160905090a0302100c111b0108090d080c03100b0a02012405010e12070b120603100902011e031d0c040c0f0c060203040206070f1439040e0706110105 65
    0xd40754004603050f07409403064010995080000c2d09825401208100d03401744580350f4100140000044904118200c0c001605504005461880e0050078824141c00005401084e542c1041800c0c2e441400015201e98aa803045000045164960010914810007142080c031480d015808040b24040c8600c034010000110510294103083d1fa0269034006894241500c07600c5c10610900c01c00704e10f4030301c251500c0c10744500244019802a407008020422010184000f42c2418098810000041a014840c2a04540002e001010752403200d08052100701210501d030b81c070a50140d0100c054096506400705554800640c2d074075020f40c03545100e04c1c41e204400541c280074510704001c1c40e140c2d0321104650b020b65201e8000a400003041039800c20000c10940c4005100c50251b1000c1c2c9200350150240d60a01c80e00d05407628401c80da50141d00051103581030848000d2034040c07840e010180c09500d1140410501280c09414990103206081c82781550119509411201d03007020900d21100030400c690340d8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 931593570 1250 931592320 931592323
    0x506010305210d0b0d02030316030806041103071b0b130303051f0501030e0a0204090308090d030b030a06022104060c2c0d081e04060e0d020f040e0c0316090509 70
    0x9a0801d92075482c4200070784003000015400c030705140b0000800305500310320141c01080c00c5034004801c104400f04200c1800f000c240c1c110448541024007541c3c108450903e511040c00d1701d2202070466001d020384800415800034003c51036010803503100c3d0001d280e0f03003819080d80c000c4a150507421404a42800300040712290a220008030b40410ba0300081501032410300198010155441070040c03c6c0a205070361005a2590300074200d24500c684c0d00d0f500c2070300c0c201258905010218040c04d00b0035080c201034071040d07a4005a0808a41e400a100681d41c0d01e03040c0061646d0700e01c4078250782c03181c1e01075010803040c003c603513009c0341820b0101e8840c5140200c00748004026228041d80e44588600091440c00039410843c22580a0500c85c0480a140880000405c024501803002607800f507900080d080c42710580c00455442d40b80d40541e464038a83c0300960015154103124040c030b40c0070f142e4030100200141c0040080106003080541905e158010041d400c4815944038002c4000160404000c92406c950 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 931594820 1250 931593570 931593613
    0x3060907080f010e1e0c070c080712060b0f0d0b070917120304080f0708070203071d0402370504060611031b07180c030507030e032a0a0506010305 64
    0x86420042c2c2070703080a07008403941c00007a09542e80b040d250440c03640c00c0c40084d0195030040004a282589895651911042078041c5800c5040c00c4d0304402c0302040341c12001c1e113280c00415809070002c1006040500030640090011500582c07150007070440c10309000d401c0040714041c40d400d0b6036020031aa152800c1410300290301c04800c42c1c50f03006a9000888814400246421a1045100300d2400581c4a000d003c203401005060b82c076408001501000c514003085090024003024040d001c40480e5003440ba841c4050007403000e07001d5501040c2118008240c201d0404494038101b2406203d40003010014808040d6030080a020f60718007400031840e00d01036190f89a00100070002546000c80303016503500341b051240e060031505d00c80c019001c61a401e50103040c6100b101c8222000580100c0d0580080a58602800080c117041c82c0582d080b50304c190101c110b643d00c14911030f242086091b180560b540d4a02c56071250820b500070b5907a02c5040080108403541241c4c06901100d0000c501c80302d1840c1d0190 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 931596070 1250 931594820 931594831
    0x12031e0c0513050916052d0c010623010507030e030706030b03060c16021306120b0901150602070b0c120408010902121b0103090311010c05090307060c080403032a06020306090708 78
    0x103405c0700c07407100528421070060221100c01c00c0b42c0482d000181d07030030030b4829000c11b000c50400800419141800542481440003c0290150074680f08a400040754601200c441e180707410804d000a440050500484000d00c8041016041320b0810741c1d18000180101a54140140300b07010700d00c040780c00038940606603102034040c020600c288062590800410050091001280303613141c803030010b410384041c807002d068940580c0c0401100d04d4141aa1307401c403416001009040700d1503420901c107255000030044c00341c421200d0400c0d6520b810425580c80d101d01c8029021944500140c08101c2d5001900000c004610940d40750090a200301d0126407510348002041c0d01e15503c0000e4489150310075041120f0980c02400d09041100d22080c0072400c0d240441a0000032034170001d03a00e1118103007086200c00401592401051a501a03940c09080e8411440302504100e82082e40a91100d00d040107003010059034039500700d0500300c0f4501440650412144140b081e1040320000d00114040e0540c1071040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 931597320 1250 931596070 931596091
    0xe120d21020306210a0501050f070306060c0b0402220f0902040606090b030a0504020406050904030c020a1706180f070e01050a060504051305040312060807170a12031e0c05130509 78
    0x1c50003402c0b84c10030f500c840c54080301900c503000d10070006c00c400780300701030090000d84075000042c6406400641a16040da104000f0041c51030700f640046460f40084cd80c0007641140d0125034000c01489100d507124080c071003868500d140c034900503068662079020000841c400c0d00c2c240441d0740e450303000f941c04140c584281c1074141020400680203403625406140e01034402080041c545840d01c020445d001e404031022404107101d42e5900d17055241080110000780001c41c000d00c06600c00d500c1d000e849500161006030030412807861044150300038032510400407420b40c02c543e40c052307032070f4034195550030203205090045a0400300891220300c034901301d8003690b402070141d00000241401e18802480f00800c26810003201148072100d812443c00303268010f0201310300400800c3e00303120300c002c28001d04180c60b4486500100400700001c4080d000d03d40076050604000426101c0240315040c01980440100c103f54039000325041240d4220001e0085148080302d60110036448000384a46039601ba00e008000d0f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 931598570 1250 931597320 931597339
    0x20a02041424030a060c030506090a0c0c0b13020913030e03070b0412060b06030a02070c0806150108090304030f240c02061306022215020a11010e120d21020306 70
    0x902ca644549403039000d0103001c60703003001c0f6551220340448140a452400080e2910244220340c41c0804055811480003c001c02004038129006007040c0840c3c1c400801494403800081c200c00b1800502c0d03010507401030407451507071811000000ca59840e040d011400b0401c132011084080c1000200f0304103450303580c14024a441c0c149403c0d1108150f0440301210500d407210030808043d201e48020b103000d0a918a00036031201c00c10300e000070072140b0720b070042c11840e40300b5420000140703501c6408801000003802c019280f5140c2c3c3e281c1c141103106a81010b04151800c0065000300181c0c1200303203114844064188000d1345685040200783ca0000d446d20005900c04004668812590b02c840e1008a205881c018506518405035183c040070088604a83c80b80500c070400041d00010100c012084852000c0c0107044810b60781c0c44166105241c480c0c0c10000703c660112559201d090380130321800300817401c42d640c0c4001c1200041c00d070500c8641034846510128604841d042090003524015500201100c06 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 931599820 1250 931598570 931598611
    0x7020c0a0e1030060c090e1003060216060905060a06080f060103080a05071e031818020f090d0b041b061d1c0f021906020a11030c0a06020a020414 64
    0xc0a40b58881d400d0410141c2441400214400c3c944085414800d80c004140c0300e61488025140802c0340d80038080a100650411200d1301403915800c003680e601080041e00c840340704010401d080c1462100600706131614014405001000031076510130242e0107002d01c034050712484450340714094480004d0041e40220010b01c00901044060a5604194a40075003000b10fa0744492070082000c408140c240c81d2b540301d5007820b15a1181002d50720244621140d00041e150041d2078401e807818201c8040e1040c0e0210301141d6140918045a005590040002500e20700604101c269114144c3e000c56800392940c0242d50b400351250300136012140c00341c1710605203800142140e011090038244160340204513050810551000314034205805e8000e08034000c60742c45030300c14044642594000841c1c2c0c941d940604008881d4002801c48031503611180103400581d403403022038038100355100c6450740300d070b0b9500c00801c40b103a000a000b5031050080f81d0a1003010181a43c450b4058001d44501802c2c40c2d4121a904 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 931601070 1250 931599820 931599839
    0x91302070b012123100204140105040807060804031704050d09091104091d0f0714010314040807020103112d070302060414070312091e0f060c0c0e07020c0a0e10 70
    0x1080c83c11030000038092006411380e050070015104642070026a002c94140038201c2d020b10030180c0800e083c2041131410f4184003005a40d02818803030704040159010008003003502c01d1500301401072034171280e0009030400b0703e803c540f0351420009000c0000d40030840002c05100d00c2c01402c5041542c40f1030380d4039090800400f80081d05040700080030310b0390500c1c1505c10009003000394150380c11030200500403c17820199541c4d10781d80c4074007100d41010304252003401e40081e050703000c039006a032168011369640c40500c0142d000c1e0590561602c40e000c00030400909580401141c44521020490704185150381200082081c0c0219600600140c0c84100000c00040b00c1d20140d445038504030080300ca00ca0f503641c0d106025600b14091100014412400800c198403c02c020642a000d0700d035101100c06052034070100205030140b1a203010400c1d0a00a2801d2041518225016050000c0100c4140c41e040f24040d6032031860640321030207040e551a0006124046401050142c28103264151449103001c0150 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 931602320 1250 931601070 931601093
    0xb060d1104081006080607170106030b01030e1204080114090a121803050d0e01050a2c0901080109110909120d14090607030509031c090503091302070b0121 68
    0xc90480200300808a12204104500c61003d042c004000c240d10f800e007400203003010381c042c03d02000d2041209403108040c01d0b954160341903070010301c1c0c001003140501c40101c01400409103091024001c5503105100b58264800400c00e942c0204020700400141130266115680d007142c00b1807054011400e640b000a00c80c141800c2d81e800309140c400705005640c50010110581d59100700d0f241e6000032007040c02660441c000c1039041509090179030404a80c41c00241c5a145003480801860750f005a8525800e00c0610b101144c03c2c501802e5040383c0d40e120b200300ea00070002484140c8081d501c40b2015502460400c80240c800c80c031a801a28850854082c100c559410181c0840e0362a074071051545254842c80716042c3c820244140149401c0c105400098200c0f02e0103011105642c004002c00822003802d00d2104490000000c0002681600b0741003903400c40c000c43d10302d194800d10000940e4154641c030340140042a0081c06000044d1740d80f41d01c0e0003c5081d07201302d2048030103140d407901c3d804100c14840c0d5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 931603570 1250 931602320 931602341
    0x92806260f0325020f12030d140402090f0912041d090c10030c05071a1602010501150e0a080601170d0215070e220e06011a1c0e0a0f14010b060d 63
    0x6000040750300d07200080e00c4034111350003082164402306d150b50465145e07000e90038860003d908081228140b64000c9a24990000c01c0c48d20081200700108070488000c20154424407002c03501292a41d071101c0f00c198640400c444203042600c10720010075a014400708603507601140040c100480700c000040140c000d07004483c09882804005d02000b0b02051550860503003030304410005158510305600b6045c0d01e000b211080c1004c580c9400010b208168000505c20306006040c14180d00c9404180d002441c421580c0d00500018092900002000f8000014a0226000c1c0d0b1064400101022800b00e0b9159100c09256a14141520105180600401890707480c0b01e80078108000c129480240c1c000720007041c041020070030381d60f12600d0b2207212060280f01e0140c041e81125441d65401d4a000a05d9402089102374842c0b0440074a188114216800860100404000e48210700106d007401c00d19001c92840a440070460401f0b080c12064040c401c000079098001d00d058200414481c00b0f00c01829950003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 931604820 1250 931603570 931603579
    0x10e1005030f07122a110304050f030a051510231302190504061206050d0201031e09030e0108010905060307140f090420092806260f032502 61
    0x1d400b030740b90140e40a04200c4042100001620743c1c1003c50000d080700d245d004003010040807492100c000d94000c4101d800f00c41d01200c5840744200e4400001e4107103800c50f9002801445904014020703050100510b52090b0a00b2018103042c2d80c5d80c0c01c411080b0b0b480c03030501c08403071200060f01c91540e14041560010b24041d040006003040034071441000c4031511021481d004c9180031038204900b50b4080c89000c0c1702c0202d6642406810f18000c040390385242c0e042d030005e05254803400c9014058601c1f926a40c0c114074030305004e00400d001d41c1000b40440300c040300013074000740c060400400c0c1e065160003128090840540281400f51601c881c004000c8600681c2030790014000c42e51a165a5440c194039001d98041c4202e103418800300804000d9801042d99000d001e1818981001100400d0300031103000c4881035174031102c6850344543ea45000740f402d60001c210f0040300504d820b005524103129110101320b54011034031850801d90706642d4030b000380c0c4001c10005c06c800ca4802500e0504658036240c0318800f40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 931606070 1250 931604820 931604837
    0x60907054806010512070b030c03151507061104121202030c010204090522030f120f05010e0610080903040302150c03280807080105091008030f0405010e1005030f07 72
    0x100d1024040180055a8042d90008005200300d2a20180216030004000001c120080c5000c0c5001202e0100404004001d50301000085554240800c0300c011450300800340c11124082882003810780c3c02c003100980e0103a11b0030070854035050aaa044805a5841810209542c00c90f90f8a68000d055000006021400103100007038415409001a0028060200f000b040034544490300d00500300d0184100e0020055a040c62004039402c01001c800089403031030300c600001102c45680e0054441d080003a034806242034000505801c0c51110365000382c80031030340300b1200000e02004903908281960300352419041008108014508032015941c0c81c0744030b0508030708115910b01440e0550700580d2028014152003490b41582505907100748106c00b0380c1c0e04080300f450038030010080030032105014060040030008042040039401170140b40c000c2c8840000c6a03a5103d034001150826086071046c1d6002c04c1070304205251900c0d1040d03480300c0448c01540c5444c04c0d035440a5441e040d81d80d020386140700b0f120084 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 931607320 1250 931606070 931606177
    0x50a020f1b0f01020d142413140109090201080609040209060f13180c08150406020f130f17010603050d0f1709030304031106070f030f0204050904060506090705 70
    0x80c005000c080007008400905041007116038000301d48001c000318190447c500321444045540c1000b15105802929005031102d02d0070b400350001c1c0308014a002d591040b400c000500000550090b1451030304c00e80c3c6114464450704144812001c1c1510001d50142c0b881c000104117050038110403081910060001600d004484a1035089407501c103101d0820030203101c8860140b00341e003010807009140d460010701102210081e20161540003a20040c10305400107441d640e00303507022040c0e8400550405d18000c105175030310901c0723174904000d1150114a28400d140d00313a0585061060804803900a00640b000341443e0508450348401d02e41c0c41018088007001c80c6907800c018580d128403940a000c000c560700c0c00d103420040c001c520808045111a800f50040140440d84443c10b0b40ca242c2d402d040c0032404601611000000c0d004c0c1c3e40105e5080312864081005100103600b1141c055030b405d07a105500c9880d0444100c5071449040100101c41240c040c07041d04c44800314440c4100000024169255100c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 931608570 1250 931607320 931607323
    0x1050a090b030f010e0f09060c130b0c21090a05040b03160b070303050a0501150f14070312050609061507020a1206020909010e09120904060b040609030501050a020f1b0f 74
    0x40c1d0781c44003d210b05100601c00c5401d007806071a0000c409800064440c90310421066070380a000306107914004010846010071030080e0030503409001842406502c4040802030300b9512502140c24030080c1c4481042c101c0d40000d104100c400305540034202442c01800d2100b8031016212140f001601403140c520800d6548a00c601e80102400c200d41d4015503403e060309000342a5a0050b211141c07940c034180c010030081c400900078400380006810305024520800c24140e540002c0d0759860301100384000350781d0003096030182030003120b200d401008019941f5007000f0710180c00811120641c214000e41e20903011804448050034402c2d1000b40750440c8103031502110402031081100480381642c0129484076a45803401b641d40c050401911603042c94648140700e01da58400340c880484030040000384519080d2115000300d00134081201280340d0311a65944c1c02043c0040c2e5200c00c0d11254a040003069803064103008a90320014415110ba007001d0340481842c21805008100081900c120000e40ba40c02d0f90 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 931609820 1250 931608570 931608577
    0x9030206061012090c030c060807081012021315080c2b230d0903061a06090418020303030f160207030f082505010203070210140a0c120509030306280501050a090b 71
    0x843d40e503509c00d402d00c100098040000940030034003000d8250070502645c0c003980280d1440c20b80450b0340030b12664038030842c0070082c101c0c4613640c0d903031071003451010803440d2000456540783c403801c0d10010107540c80b860700b0aa07022225100068124030b01c07041704c004070b00030b0416808200c0c1030201d1308075404160703d2028900402005403901054a01c4010002e0040c14810540200380d50400304900381038900015500384a0222800d03c115a10301e104142c203003810200140303241c0d0180469a40b4148861401c50a540031610380390070b0000ba110f514840e51000c50343c28100d80d0f2107000700d40300501039520038616403c54610200094082e80404805041014070b00800500503000181c3d01d081012009003071018034050000340740e041c030740c0d42030010400c8448541e10021300300d00080c100384c01c2c0360100c070340095030b04801201d1030402080c0308050340080021070050200716442d80b20381d140d15900311412400e052400c11606620107081049500a81c010300c0740c0d80b0f042c90081941a290b00e240703e190f40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 931611070 1250 931609820 931609829
    0xc120702011508011803080a02070605010e04230d05031e13020405060a031112010e0f01140609190f02040503030a030506150708030a1e0c020109030206061012090c030c 74
    0xe45400000d03528048542e0031802400c814030081c081d8182070340340140d60011081e0001c2c00c001c000000940444003e81c188c0e030300030342c1c040400d0180d9651070b40d841000020565094540114201028030320500300846500400004000b90980c503e190005540070780004042c84020080208807000d201a01400f9601c10f10210f02001c5620000e40107000486000920442c041d08c0c8552060000c25800d40c60210300c40030840d8254a6105d5490b1228050080c494488040d841040c200d07100c0d0302d1064000140000080d200036906a880c8001c11a0510043c4c0700c07038040030901904500d49030300c0f40c2c1000751404a101ca0141c40d0507074803c0407034503603803012401d50002aa0307501804601e1410740000e042010f41840464100501922130345c03402e21020340011f01086e51150300070180b00100a0000042089030b40810a902c4c94880c060701a0090300320880050164500148140c034144c0c906a6183c10030f40d9494001d000c070b01d85000c00500b80700b5000d555001c0e002000000141d00d00804d40040e1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 931612320 1250 931611070 931611073
    0x302040914091627023a0908160f05061f0b0a05041e050a0b0c0c120303070e0a03050a03090806010801020f030c1602040f0c0212130e0c120702 63
    0xd280841409003001980c010351880080120010016081c0100b0001031122204c120a00e032000030010890003445034900c03190100000c0c5001c1c1e506a0081041d130050a02c01040c03600d80c0c40301c0081c00000b00d4440080040c0050024001401702d403014808082c0740c140305045040701c0701100d8842a15088003120350400720010040140c110301d114200c0403000300301c404810b030b04110061401605501076800b032401c410710003100240702200098440002884040e000e60102074440360031181f01d6000d815280c09512a10fa060800350501d41c411520500d1030310051421a222a1800c5580c0f80c2e4040c0340c5a84010500c0e004004503c0074042004064403d484010045241c04070003400c20105070301c0700d0300a910500801100c82001011658071806d0155202e039a11a84000150b00d03100352200a03411a00c0c21154005101c0c07294031460380540990229010801c012040c0102c9200d03400c1c0d0550050341002c02000601b004149494125044200302410511228030aa40b4a6800c03103814005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 931613570 1250 931612320 931612361
    0x12030806031006081c030e0a02062104061a030a0c090b060705060906040c060c03020a030f031d0a150b0307090506031207051c110c0d061b0c020a051212030703020409 73
    0x12101c001403100d0805c8030350a06102d03c0b0850002185c803004100c0000c0c1c065003000a0078030a8503100c0192411030700451103c5000b80c1000c1c02c0080043c5843d03103803062090a425802c203030740d03d000100d80002d29404a241100107090802d40740180a84c0d104d01a0042d0307003840a000041e105020351761003a01c7c4040248801e250070b0521500344900b40c1c2c030860512841701d0800c0c3c003181d404249062800d80504215030050b46402d0114000c1940380568590b003500c020b000440d00790301080011460b0b00804100140da20340c420074104803010341034100d615078010300b0304001c07100c2d19420165012200605991904415554a4003660300510741141c1b0750308205400314501030203aa40f102095000d1400d04c1040707a40c0b010f16655102c0042070a4406c0000720780d144104800ca4009510017902101d080b0300c2c00a00c80c60151061152000413442114400004249801c0100d00c200720456a01c0081a002e02d82d40c91001e01580050300060400da020040070607460228001c0d03005032200301850200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 931614820 1250 931613570 931613593
    0x3030e010204320103020901120203040528060f0b030c0411221503021801200706020d0305180d2001020a090302010e090105010f050a120e160608011203080603100608 73
    0x802c0c6200300c0310f98141031042c4a00c0500e03036400008100004200800180d9a4840381482858085100e1f03035084646030200c1c01041516582d4600300003140300390070a1148a9035000501d003590820084e264059025101c0c0404500d025005591900c0303c00488031700c0c1c0240d04080006030405043c07a0b441c244025981000380e000004070320515802c1d14038003182824003180c6040c0080740074036640d81c104114044492040d0011020307030420308a01104980c0007503a01d1102039112210840010007092a160000342694221580303c006040d145024001280303a8000a0701c4d0040300e040c001d880c12030080e2411400328402d1009041c144240e0f156840058078500c001004584405011800303401d00c0d80c0100b01a1741c000807040c940040a0a00302d40b50081204100c41c4032810481d0024441e00300800b0359204240800c18070b401c06406820600d01c151514000e4584510a01c2a441080220710500020900c030b40d54081c1c0190004003510005100300c1c612200ba954140c02a150640200d42c1200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 931616070 1250 931614820 931614899
    0x30316080702060f01090b01210501090b0901030c060f050d0e03070606050d050a201f14040308030c0a0c021216050f0906040506010c05240a061203030e010204 70
    0x240d0188151006022628018003603501c442c8061080020303e40e110404100c03140c1c010844007a107040180740d800329071354110391275401070f00003841429042031500110480030b040031103515043c2d981008449114170303e0044112a08900e4605030710401c4002d209071000444170307000f17058080c900d40d0000c503101d03502c40c2001710840340140d011901c00c40580c0d0110f000950f000c50b100d2851038104469000501d1010303c5500300f000e41c519055804a00c04549289004076450f06803816811a524406403070000e01d501c190b1441540005010410280000386403442260020400c60380070340380205100d60198007007032080f2120007600d01140c101c4494805504c00001400004003005c03100400302c4140c030404030718540800b1701300c40c0c0030b40e450300d0002e420340e401480c64440c0c041d81301040750710603500610940f10240c07507188101c8401c8281c401141a042c2580100c60a4a1000041854101a55030103030000c24513885c40502a5400303010004109042c034081c1000307000322841c40034449041c0314050 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 931617320 1250 931616070 931616087
    0x302060a06060e101b05010207050105090d020318030c100503071814191a03040308070c0209220b070507020f040903140711030a0809010219030f120608030316 70
    0x544a00749840000c20a9981c000420040342a098540b0468014003590444618006808a0341011119110791040000550090002c0e600903402000b0b0b0b42c0f1071264140d19080001c4800c0700503402402011481d12030040540c48040d402001c81d864a5032000114031042c0c03c2c4280100070560100030480000c1e000806850741a14107040041d05030306140c440e80301c02d8001160580118918584462266a00040c00c0301518071f06411611292165a00303e400ea1701c2101c007240080c3c011404208980d00600301c02c01400d500401c071800caa40c2c0e003040b040c0c000080245595a500c00144880041448414003a010748925580c02e030f51440c480c01807020000002008a004a00d800342110200780e00060b11902d4184044006603180e8903401e22601024103218020341c140100700c0f13070000700001c240041042d030f64281c0984000040451185d0740c1c80210301c2c00600401c000380982001584200c24140c2d84007218000010001d496410503441c0da0811560380d0500300800c201c950381650000f128 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 931618570 1250 931617320 931617331
    0x91905070e18060310270507290a1101021308072d0b1b06010906170a030e2701080307020a0f060f051b0d030f0b030106120b060a0b0d050103030206 65
    0x14542c85080c094046561741083c130562100c40383d038400c1510760044034004009048031542012141ca10f605003400d503100e110901c102071500d40c0e18014145442030110544040c502c0e4000890704259140078146c640c84010941d041d6507543c01c00c081480350329844c8060300909448401012603605100389003107001002c283e0310581480441c80000850003005036401528502070210303440b8051902003110148809600070307039074041d500c000b01b0301812a40c8002c08841040445103074943c00459110340360800755a000d00002d802c00318201041c281804802042041c0300b41c0d580c112030003801c062920301000e82049269800c000f4000e01549030014900c00034004840c960b41110345000c00240c0341441a0300404240070002c5088020441c07203810741c0d140e40116509803640c01c00f20500003001455814240c842d65482e0048810036810144140000e0b6058031306464180050f6031901035405c10300510482d4801035250f1301040300d01c02d0310060b1050419030600401c4a50643c5806414000020030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 931619820 1250 931618570 931618609
    0x90510080f12180109080708031911061302010e1903020312030106090e04051005010b0a02010e0102181c0618140c0a0b0a090801020309030c060114010806091905070e 73
    0x1c0d01071010042c90481c0c05040401161511140c0d0010040e40c13070418a43c081416030143c18000a81001c02000030960718031f000e2100e01a02150300005e4980c46515003501201d584444005055400b61140c0c803201c482c0141042c840c242c8000700012080610f548200340c44c5920500100110701342000141c000b080e600d031440e411903060240c0140b0118191041891449120340490140030040c094400c186645c160207000079070315000701158592000d03840200645c60700b154003040f99018170a4a00b5900510104100c94544030708119009000c025980064006110080c00003070140c4214111100b000d504003142c10124141031411004007640c00000780c000108040160780c03100340d00015500c92400c0942c030340703c00100450345200c1c550000c1c03c6035840041400410400000a860000c980301e08840e52682c8484551300743c0100c0103140b6020804007004609030789802d8080b00c2c2c2c891054200262141c00071501e1500f6074a041e13400380d000c40d031690740b00c01c0c050a18001c040081e400320034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 931621070 1250 931619820 931619833
    0xc010e0f0d08150607230d0c020117070e01031a030f06041b0602030909040813030c0f060e061e0c010222081506040b0a0f03060e1c02030d0b0a090510080f 68
    0x40c0440c540e849403120046c4515440d080b00080040782c050003e41c0114924221141c1906202c40a000210760a000781e02103039181180d8110710710014950b500c00c00349075071000c0e00c020034000150041e0001070103070b03682649100010aa02d8030104035101000001c400200b00a04040c05d280c0414000e640141e00308660054052102640010490700020010784648080f5603850070024500e0082a1481c203010350400320000501401c0e1650205840404d295121000e5441c8415211110301c0c0014070b41000781406824844900880c1400781c1c101000801842c00302c5011a00d0708991261400820021605c1028010420b6200d03040380548401d500030700145820407071070050480d00038800c5214686030294a011501c41812200c0204519119520403c2c0c4a14044014209140c015050ba2280544529051141130010005070459070080c515280344443c0520142c100b103090160003403220440001d1519161140380d108034040c5441142050400d210076090099a0800322020360101 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 931622320 1250 931621070 931621111
    0x2701090e0a030e150408060a0b010813020312160b070306180b012309061204060b090c030408070302070e07210b06120603010f09030c0b060907140c010e0f0d08 70
    0x1c0c4003010550b03040f100d4200c5251603d4a2500c13030700c1280c2010340b140c00b8000c24405801456085115a544262200442c944d901c01040300516000c00e006949a40b0410508910312a004c0c001c000c2c040d174902d4001080010b684401b0b4030100d0544414000039502c820402020030650400480d581040c10300740f00006483d4002010313002290030301040d0502e920440c01c1600c8200089580d400c001414440d181c0c8180000c050030010211402c1e650242804940c0b2803a1400c9911544a805c0005010341180c031940c6441c4806c0c5c0001008134198400e1a0000c10070740c0e0720a2606124081d184da51010400f00d14050305e4841080c0440410403d0500c0c0d410480c40e030b2004140d8040d81030034030700c19501341d403841c0020780034000520105808618100d089028903a102840c00e84032030040486e1101d80d02c8035824007101c054103c40d40c0c2e0004502c4a0b0f01c0000080d84801800880c510748000b00d48e0403c03006e8818100980c044903c086540140340d1060040c2e081201d03280c3c01003500d24410a0100310 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 931623570 1250 931622320 931622327
    0x4200d030503070503070c02190e0a050405030712021006030f03180608011512090605040212030301060e121c051801080103170306060403080301090b1e130b2701090e0a03 75
    0xf620010500c00f022000450840c40740711013a00340d0b900205210040d00c05000c800da0307443d010780549043c111202000595503440342c05260701980e400001503182a00e90388803268811819541d038411401180803040d650a0b40d0300915004e14007a03400c0034849007240c0742c040c1c050801858104440022a1001c0140039005003107641110b640140e031200080740342d0030403910fa1800200001c5020300d040b41030400d001c03c9902c410300c210f00c240c8007a240809600107203552400700f4072801c40000d90039050781a0310b0034080404241ea00401c03080b6010008459051340d60a000111032030009000840d80c01e841003441000070710340c0d02085c00d240c5071550654580c1c240c0d140050008000c204000401b240e005e440e00c80460300190b03046245c0c10b0326035849411550281003682c035014860040f041c808241c907400041d00c2d0400c1400100802c9035011840040e8010307119140003594045412500d42c075a00d1002c1c60603e00c0034a0351141c03000198142810001240d030300000510113680200800d0000030f81 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 931624820 1250 931623570 931623577
    0x27050105160824011101020f0c12030118110f120601020601060c0b04020d0305090d1101021203221e06020309070609060f03020c1002180a050f0f151204200d0305 71
    0x1c0150810f0703101000040141c40d40356000050f10035562000a10010402c5000d010f408031000c0d810a0b03401d210f4101256032030501082c05000d0113862210209400d8840c41d034006121580d1200303060303041508800190000e600700c0750310b003041843c104080010079030b41801518094400780c20498010540e98480388088500204000d00501707814a00310180340c082d605a038001c2000600101010700705203000a4030900c00c2ca403482c00b41c400c0d4440003511000c0807040c4e0b031041440c68a0700f10002c01c500c0c84040d10007021b200959010070282501d00000c0c8200b01501d0140740145d201681e28204501c403145805065840403041120801c02801900d03401000c5410200582c500903031243c0041958504115890700100a0103100084c400706a8440c252509460041190001020380c0c0d5202804000502852090350003242604607141c24130340502000b0340042203036404d80c1004002c0102154644040e034060301d41108034a6444002500e00700c1021814a040d40e8100010020365409080b601 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 931626070 1250 931624820 931624861
    0x2151512070b0a1202040e010621060e130309090203070504080601090e0a080c0c090112060b030607120c02150f041707030804020409030e040c03150b09030d03270501051608 76
    0x94440d180e04130b041281c050718081e005100742c22419507520a800303040d100204001818009444059150300d03580ba2042a003110804c3c07809814596414140c4489118603c0c01102402051040801e84c8840c5101440c443c100703a8036100d40e034904062f84c541ca0301e48143d0100301c60340c2c00c0503203004450f00042618018542d200b0b0500d40c030786002c216a5410141e4280c095500324808074000503800341c0c9400b12207400c60055208108000c2107000b40358517440c0803603400c00410422211041255915407000b40100e41c98819110103003080741281d0403120041e6640c0207200f2880c0700384000e000713503a203440c03c00c09800da40e500e00d40a056a40034140050082c000780c07249584d040c0c26420315000e041d969807041c400070302c100224030011101a008081e0b41d21010807200e00b9003c08540e21422134112048000010020621070740f502100300c001d040ea202900200c2c0044500c041c1c0010b01038045120700314400d000120b2540b0380910404107000d14440300404025492003407240306182d1040300c02d41740 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 931627320 1250 931626070 931626077
    0x190204050603071a07020a15080601110304090603142a060d0612140d02070e011a1b100f0b1c05120403050601030c05090705120702151512070b0a 64
    0x70380d100000a418600d00340e10101c00b40381142c0800c2d02d1440d0354401040498400c03100d500032517072a00c0000c070042090b0390522020520410220340c1b5580240781680140f00a074081342e1500351500603480a80362035a00441e50b042001001d0151800d0a100e00c56005c100d81c9a40401e22100e0410000100050440300380a0b4a000030090b01101c469006603010301400150380b240020240341a47c1d48058216442e00207000300007d8000803440032500307204484144240c1c54040c5d0030075000b441a04442c4034000e804110410800a00000c04c0c1c504011340300b007100c013800306900307048221002d4581d04940c15254a241c44c200908680d10040342c08061110510b03225408140d501c4d045107003614480c005074018030003040000411500160717041c1601d00c91400200c1140d51030b014400c00c90000c0d04c103c004100284540c0094806503d480c55200040348111000f0b0303100d8400a604025080d507542d50000c0c030341c3ca086101c9052030010280318064010003000800c1c0b0784030541d50140140050403080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 931628570 1250 931627320 931627331
    0x12250c02040609050f0915090c040f091b09060b030601090902090109090f09050f0102070317040507030b013314341401020702030705010e06120c1b190204 68
    0x5649407940542c1c06405034031410840d80c04c080d80340c00e400c0001100d242d0103038452500080f02c0c0c0c66024810358003a0328a036008065081170f010810019003100c034400c450440c0d03610302e64000700f007000440040c03400302c0102081030f071810420718405540260300a21802181041801400d9078004010707811103928403c010380b034118283c012540340d04158494940d150070302400e20b840c2c88056004407542d03489201207500c40340601d8585820b0b4041c0040c0503002c075541840f54424881946007050344184144180d508058072640c48880d6041c1c01c5e00070b0301c14030203c070001d044080d5502c200300c03200c9042c3c92114400680000d03c010b20118420030500460940410440080109503050080c1a1100034021990507480f03085d24410a06083d4113407100d030290100026032450600c01c50b101d054018005c1c3c00f055003003400646541a9815045400880401004400b100303c5c01030240031700c201c030407041e41d81c0185210500c1c0880b1001075030815038211108038844051903851510320254155004a074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 931629820 1250 931628570 931628573
    0x703020f0409030e09010312030e061003240f0912020a020a3b0610050f07020409020d080d140711150702010204030b0a0b13050c073512250c 62
    0x2840013483c0710b16600203030898008820000d80400d00c04407810a079404000c8108400322295854006459000d941400ca2000788040351301c2c90702c82c014140c0c50011110591440400031403c480025004000083c1c0e103031919010001d80d00d6a6141a042c90720042c10030814540005000b4412880740284810b0a40c2c941985218002c680c101e48080802400c110110700c0041350b4110f0740112204c07403003903c0300300000b85c6850091007602c12a05000102c142400995400d10006000e19202682c0c02000c0d41d07503000014104d6001010340040c5e0800c046440c3c04003424415103900041e15010520039510b0200f00c08060008101803403440500d00c1c21480d407125041a80280701c0c0e40c0000e0305c100303840810050b051310303144c10079901c1c90070030350320038400900110f03400d01110b03c1076820b030401745810000c02c80032819100001d10444c2c2007001c910500c0740d01c880005c8100c0c1c030421440140020204820b20503042854003654031020031001d91500800ca6886c4e02000d400d4120703440700707102036882002c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 931631070 1250 931629820 931629827
    0x201020d121d010219080403140a0504090e0c030c0619031503050304062a021f14031608060303070218041403030f0405010c020f06011211060a08090f0703020f040903 73
    0x303002014605000303202501c642e0311035020b0f50002c403460060a03812080001c0b642c0c8030301301251041d900360b0f48140d40d5090f40e11410340d85510608454080020502000c00c42c840d540c80303490140606c640c010070341d001c03554052508141000028911600060000059042c48826041e200002c14500040c400c910034a003582e66160541000d030040c40302080c0416907a82004a242004840300801200c08a45c00000c51716503c1042000b034200f259104038800307281901e0809903500750305081101c0c41d0b5410640d8144c89800072100d1120112081c0700b05407204d6001a02550080401d502940c40d1101c9500814500d188600001d120b02003404005002d2007200400314803e048400c00740c80d500e0500100cbd00040200540d82a82c1c81d518010021500da8000515014840400006400e00d42e00c0c01308a0002054000002c0d140da0060f12407100742992454014548100b0f551200e003201d0074464001450045030011010781684811000d001603601c101940521800c111004240c0032070b6454202e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 931632320 1250 931631070 931631081
    0x311210714031303020f0114060a0e0403090b03070201200d0c09080706051b010f060509011d0105060f09040204030c03170a05070206070c09090506090105070f050708070f1505091204030201020d12 86
    0x15140c2d5223402e1030051450141c411050049008888508101e42ca43c0c6c1a00641d020903500200071650340241042115511005103a0244150000041c0d102800e80c001000344010f800a414002d8005411a880c04451148031000d49480c90b02149640c28038610782e696070514003c0704180320004c2a5040500028030214040c01c042c07000034001071800c4a13250000e0550b07405484d20802d22140046010790711030441800300e401001c00c06241c0d07481c000902c10305030712440310068035440030041c13089262201e00040c0700a42c42840c1c0005464514100003039400c1d941011030303c0c000c20801c5003041a40d484001d484a040d01181c80703503038803500c619066030070700d429038803042941d0304004021090050101c1e0320f80c841e005e4000240040d640d0000c0448800d00310b00e01c0ea00104030b0512258010401c1c1a01800d0070b544120050070072880075850f42800b100c0300c900060840c41e100e000f00120710505000c0245020079250300241860f055a0002c2c0d15003030099201820480507520440c6103c11030b8000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 931633570 1250 931632320 931632343
    0x6060e06031012051c0c0f020108100519150c080a0e0402070c060203190e0a0612111318060506091201060e070e040501050f030307080307031121071403130302 70
    0x2002c10b903e0030303884e1294944180481741c911440c0c0149600340150300801a01e00000d600107404400004103500542d49014058481e0512100d441c0001c105611400007480c0e1038001e00700d8149500d441c01520b5111001c4d400d00d05007c0120701003144000072401c1e030649014034010306040801c89443c1000c90020f010300013000e04400442d4030009042d980110083c07600041e03591a100700052035178020340c0c5550a00d2031503500100a0710080220030b03c655042da50305805020041261900104c034010903030020075000320612042c1c10f00b04840c110b80c82400c084031340410414001c2da850140007900902a407410680038404099241421240079480800030f410f0500e02c0200a003040c1000401002c100e10300b4600031032602c0008515807500f0503001290040040045251841c56078075140c89e50400380c000014542c0b0707422144401c10344034014104040f080a10703200440011403500d40f4091029100500344910742c0d41280001b04600f00300c0381d002c110900b0207080707403d103850128074250b0001034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 931634820 1250 931633570 931633589
    0x2090a0b040e210c1f0504121718010207150c0801080708060f04051005041b090506031207050f0d05091005030609010620010231140f0f0d1401060906060e060310 71
    0x36004217801c0c0c1780d03106c0350180d8000c4289601e200c9903200240c8118203401c4800100300c003080e0018540000422203000711045c100000b60800341c20341d07555031500005840e40c0f079400b500d03503401c941501d40c0590100d00414080c0000e00c00c2030700c0c0c40c10054131444c000e070042d294405482c0003c0c0c28440104011800c204159804001c0ca20b8a070402110b801580c1500c16130b0205200d000003030304038050194a000d20801800f600407813540d415080b5995201801c02c550900805510003181d807014050304243d0b0145854066940800c0401c010b00b0020410004050100600c28000152a101c101d0b6044d503255007007003810490300c4140750b5661043c4903002c0c03075070798000a60780100c290319000700c41600d800f070700100000314444114141c0d980354600801410002a032084c0f403862a000302c00105c0c400d0044c1040f47c610700d120380403804000b003c180030354441c0045006031615840074494100181200c4004010540c20924020401840c60060a20407040807011174210054100602c0051402c0c14 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 931636070 1250 931634820 931634863
    0xd09063c0e0105280e0310050601020c06030426041a04080106050102060601080a0906020d060303051b07060504030f050c121005131104020c070302090a0b040e210c 72
    0x810850591421032a1400012482803006045500400a0300c050501c400440d01c1a0380850b2540c4511149a0064600300000c8030b944000c552014400f503440032038255030100d01480c08000192402d5040d01c4580c1c002d050030010080401d1805000c000401c101c0510f28002c1742110034106c0d654000c1d40c001c00c005e4031203410051054410000100203e560560080c0510381e42c650040e6203c0804407945c502281c4040b00041034071405038400504c491241e07000500b04481700b40b1400c214ad589800c01ca01213100015000b1502d4541c00f4840d000701000c400070310034a0b00384880203240b80220320000340701e018814544030401405000c00c3e450001c010340284180e074013040c1107507940d55000c15203000851414010401e40420480783c602802c0e040780d02800b0301e914500622009600c080b401d4130720cd000c2d5100c04001607444200090003042401e0001c10f030046150200000c40c6c540503a403084c10b40c0100e0790040224080d81c540c0c004803031210207131501c90b103000c080507040032141c1d40e01c45983d041d100d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 931637320 1250 931636070 931636157
    0x6020a031e09050f0334170a1b030e041d16260714010c1203050a060501081e0403021c05030403080c1c0e1006090b0f01020d0906 57
    0x260301c40c00441e03019000300e40c1340c1144490030b25264172481c0c4a00c141084951440c506000ca080344041040031700b003074210261300380c9440f0340c0440700c42c0c4034010b15451000181d0040c56036100303003440c41010294000300540c4006950181c260a118045540034a44600100300c030024401c0303a1501c1c000302c010589180c004600400c030204140e90103009503902c4202808100c0488000e4041101c1d04003c000300016800d2030358400c0d22030070040145040094807000900001e4000c54110301c4035134642c50105030350420700095001d0343e2050300002d04002d0300404102c25410450b100140c442140700150143c2e48413400e0403810440c1900030362019a44a2150402035a404001544224041d0f40c64121320307140e40394071051921075460014051002031101e11034504407903201c4035154002000f1961010801148142034400542c00842036640c1d80b031041499081c500340ca0481c0000c2480644079544031020040d080202030f018602c200800b81c4125903015a07604000c41100003d80b81c181103100b0b40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 931638570 1250 931637320 931637381
    0x81f0e060f0d0501061502030408060708190c02060a0c050a121536141603060f1701180312050a09210f1b03050310030210020624060706020a03 63
    0x186c816000f4071030042103841c0b88244080300307030343c1900c0e00030019040c50b461f85481202c0716540a0030340889054901501e2a03500664403441c0200301d10340d00a40b40c43d24186428800319240c1c040f06200f4410b00700003084826602003103802801440703001c0010b118000c002e0994003800c0300c0d0000d0040b0b060b0340d0b80365550005060b641c018075803c141c409040e54a1080706c00019240080d84030700e0160102004101c110904100c2c900b84a01e040c640022155a65100110041119800b0260817151405006007000c0280119004030381c040400c0e03010441a0396004007000800700c00225056615070100d04200c84a40001e551107400c1280d6041c1c2e00c510409010448900c0607240021461070b058444140340610212120b105500c0f419000d401a40d88050f41d10398802455010f40c2c04248c10040700603a10350300d0084070300070700ba4010440d5250002c0c015112001c0001d44030000c1d41000315508165a400088802107503100d80003584a8205c1e05060700580f100650b15080354803800b0b84030b0040c181 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 931639820 1250 931638570 931638581
    0x524030915040317090c0607060e0c100e010917031c09150219090311040906060b13080d0513210c152307061e0903020706081f0e060f0d0501 62
    0x3615031002d001354440c9030005175a0341d52a600140c00c00e005010940100c0c0056124002071445070080c2c0d0b8192800000160074005599004004140789121041945d44e201c01d00c680070303251007030380c2881065120060300d603a030040205401e1486030703001044207809040e4010f580c038503a000401c501106d14107520a400b1f500400b204850420242c044404200d01c510006d4084a030840c0c004440d40c441c04040c000a031905c0081600c1054442c0000140d107210000100841c00880d00310031501418003089078240040c115032001080001d00850b01358032440120a4103c414420090b12400d6868000c03900440700c014000d08140ca9041e000159800003405078103035107a942ea27400501c040c60000001d83d0b240d41c0340308042e80c4001400001c0010308554080258500346e64200382d0705150400304c0a050b9141d10908034010307002800300300400341d001034500d5004844038200000030040a0b840b91207105240c0701e0075204043c010086003440d190484003940746240605a4801d0300075038141b0501038103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 931641070 1250 931639820 931639847
    0x8120313050706022404030c1104290a081501050d1707050f011503080f0706090b090c01030b06032404060504020c160b040305060721021605060105240309150403 71
    0x41c0107901c411a481074040610701c031b554140c0302c8400c030498507100c0a0b00d0340940780700903401c56a00c1b404484e030503042180126240140025948051080005202d0b11020950000300c40b035100600440f1041c0c410310555040d2101a00c80740243c26103800c06c1050b1142480e8055070416001892209100002c80c00801ca003403541c0081c410b200f0303681080d1984040503c0b001c1c015043c00d1020441490241d0020702c0e0307541c0101008602038401ea100d20300c4240f0140c914281d540d01c0802410003558050017520612902140d0700d40c210300c0e00340d4034284030b00d0840c8814505070b001030480c901e0030b80d100d81c0a00084c0c40050011901c0e44405081c0340e135110a044511180034a0700707440001c1088030182201c00740c1e60300101034820f07a15801001d54030460141d421300c02c02100049140080c0c6894400741c401070003101d00e140c14281c4241452400d1000680046000b1001d690032a0342043c1022881c100d1421018052652036031006911070038980b1a2195102560b103c805020625510401403450030b07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 931642320 1250 931641070 931641103
    0xb040f0f151118040e0f12030f280203060d0b0c040f0f1a0c0304030813030212010e0615031c1e090522090609030909150812031305070602 61
    0x1c4801040c40000c40c0508541c405000f005038143c2d21041c18103400c4074007a205264212010003e0711000d2600340600072845140c05040441081258004200c1c480c0e0001e11942081e080072003101c0c40840c09542500304644460b8001000c20002d840300d407400c40a107600315401d0782e0305050600c940c813442d610130701c0382103411409441d010a00d4020f0140c4001201c0c40d019003a100c0485030080c0c00e403540c0101c0800081070205100000214080c81c00034054000f111401d046100d0075403040001e00d082038820006a40c1c03502003902c54045000907001d4001c28903560001c0102c802c540003d280c801c0b0550410b584580c0c4414180c11150007100225081e407510822929403ea0301d4002c0790468858071034140e000d5038501d844000090f800741481840010032030046160340c0c0c2515500142e480c0442e0890004048010412041600744282c0c0c5d02402c8404c0314a01861034170545550710000b2200070b007a000340000101e0005140140304c0b150003170b44001541d16407a030300c80c000b03034643c1e032001000702c40d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 931643570 1250 931642320 931642331
    0x7030914100b180613051008010513152c0307080d0e2b030b130912030b06040f090c020102091305040308010e09062415040f080a020901030b040f0f15 66
    0x80c3c00320802c12803041e034000c0c050148222a842044000d003802038030f052110321a41c54046003006083c02010b1241102c240007801c6038140740b400d2821441c40c0c906a03060f003072038000e402100d0b800c0030070360001f10340502910030802e40542403e0303030540c854060020448d68001602c0c41d003000301500302400c00d07290340c8161080c8100c0c2c2c14400c0080346031a60760615032000008507414140c000d81c096868194080c0c00380800c00f4444986030216902e504055039080b200e03141400d0080d034035024000071244240d550500f01840c051030058003000c40e008250850343c440b1100500103100758141ca01501c001010480503c9900c1c885000404054406400041060b03002003124646411403034001c000007401001d0b07999030046507022180e808010340d011503031144802c02155842440d07030110360344c0142d04c2980d1240340c00c10400ca042c03024ae011000300c1d0001e10075080542e451291580c1101c0c0c2008409081d5075640c54846540414a080245201d0b5842c4040e41401100c170b240e41f00c1c089260004100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 931644820 1250 931643570 931643599
    0x60f060902040e0c070f0f050102030a11090d020d150212010311180a15080f0312090114070c0f080310150c020a2c01081f021207030914100b 62
    0x142d200341c3c001c400e0302d190b480b004605101000c6000304800e6005041210068030b41d80c0da980040542c030502607030141e401000303120f00d1304540d128070300b504040360b80c2c075514110300200460075001002002900c1210704904000502000c14040d00c400c5000c04d4045680700000e0002d0b13010068280015260b0000302040005c02c1e0801c0145032070040c01c0960805020741e07440001e540540400100c1c4800017090a03030000b44800100048002c059030040516111518a003000c1020100188501860b0f070504c2000d4642a800e0404070780c0104061600c01c1042c18a403e08114204070360b407008100207000000c00660303000740e031105030641d40d228001c191882c207217203800c8614414003000a0340c08031760000100300d2040340c0d861f641c007072141d15020b4100c03114400320020b02c0c01809901900b815004881062550303034154101c00c441c107145440031400c0c500d41d40f50040031001d00400070341c20b040e500ca1100c014050746c00340b00c0c030018607140202c83c0002c1e8440342c2400503040304075955002d40518225000c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 931646070 1250 931644820 931644839
    0xa060c05060f1005060703110115150813170412030509100c051506130501121403130501080711010f09020f0f0105070809010e150408160b09010f050c010603060f06 72
    0x80c0500ca034900f558420b2400c042c2004400d611940c002c609010b400d00c403900d85800c0a0140c019080a07210140321260302d891400840301f501c5841ca41c0400860100f0000101e4031809140015504895501c0e100501c81101c04854803407034100081141c4420074000405502c2002010480425a40d2281c1c5006424007511001440f00000700035400404071413007200980d1045540c00040100844032030f20b80c0c840b40204880b02a08210111181c0c030065200784088030000c0340f901c5403048000c52402003000c41c40c550195541c001d1a040010502c04075001d58801c2d040030201240ca50b0080050b2320301800000014010100124000d1310070f40341d041c490303250003d25000c000300103171103041c5000b445645030708659000044490601c485441440071b19140d2000c044006508500110341e5107080c094030030300d004040c16900a80c610305100030b021028070070064600c0f41a003130800805085140340103035074502454440301c00640c03a0000000c01d010141d0032401e2020003100b420400c180d2600d4048 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 931647320 1250 931646070 931646101
    0xf3115200a02040b0310020c01090b01080f19020d2012190308100b07140c040522020d0803130309140f0d05010b03010501140108100806070311090a060c0506 69
    0xc11500100314203009420702e50803e4420440c018259480d101c07602210000300d8006034614080fa039034031784441d000c00c4050380020b40500b041500401141c10740d0031301340340e6035540c80b0025841d540e83c00303c2c6007045458140c500c0e0110344e40445a8404620b520600541d12600308151a02c542c0d0150400da81545c00410900190500a42d5414003071055440c103440319040900480e0403000480c8000400b0b862002c0604801d61080e1100b64008940c500101d250420a400481c815458502032000042d01e800312208500c0701d0f4003c0030b500302428000600d031040c600304080c0c0514000400c100034900c660f00c070740405901c2511001e0440b1b03100c042c5c40c905020b00901c100d80182c0311083c040303090301e48080e044100c103120b4270010602d00b10840c08242510001c3c0c2c1700406001450f142c81407a581c0004501d613108031248540c1c8105450301c1c000030303900e01020707040000b419038420006485003540302c01c6401c1208080c0a90043d04d40d5240300801c003040c44c203130541c0d29010b280d01240380c0d9031020400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 931648570 1250 931647320 931647377
    0xa0b090405060c0a1101020712170618180d021c0c110405040c0b0d050a0f090201301e06080d020c150c0a0b04060605060f3115 56
    0x300003d646419510f0a9a440310604605014145011020001c4240001d203001d07480382d604a0003d210100340601414100c10703c15403000c100070308000b840d07228880680c403d001c03c9009422280c4070701c1e004003403280082d80e821000b4010100820140c58000446400d081004076a5a90140c1726100440300c0106018004010341400301010a01c0d1400c0c3d00510b0704180142448440c466440705080a41e40c070030380241d5402e5484004000283c41c443c86041202c2d038290809001c030f0f014035800200015010103000d41030809084c101d4503403800c50001c80300e01002c0001c0400070b0000c5102e02d08650302c04020080b641c41d051030408181c074000444c440060840c143c0051610080010811441d0210150300c1680140d06101030500c41d03070100700444003580100d94540041c102400d00205079900c03a04118000d810801201c1980082002210b004d00300380d64415038013114004a480d81c803207c03203020705c07200d4514000204080c050070180c1d42d914540c1c2d842d00782c5d01c40000d8004640031174000b0603 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 931649820 1250 931648570 931648573
    0x6030c0510021506011b0c050103060b0a05120406060b0a050c0f160b0a0c120809010c09050303121302090408030702070812030106050c0111030a0e15011a07061b080a0b090405 77
    0x48042c3c0b4030b00034210068201005041c8680d070007400c00c5003061145071802081c0c4204505010070042941c0500c10140600340c1d180c0f0b801c2c0350040f03805014101e8821270710241484418000050705020003640054040c2a28000047d541c410010380180280c009255501807406800001c042112001441c01020b106071a000040c1c03501d000c90103921508840005024001550000400207a441000701410b4065440750f1030581080745540c1d00316001c242246003401200a13051003107903000020f450000c1000aa41c146e5662400104c0200c0f184401009400038000010b0108011803107010354401c000580c2102ca060b6540c92025949601000003454107400400050082511540041c61010744460020480b5101d120403d0510740c01141c800c000340d43d9030a50071240100512a10101c800c094800d0101d55040c0051500001038206c101d10328080300184c00300800880d600840200d030f1851401c41c085018100026010034400c0700e6091405292010401d06171038107006c514002c44d009030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 931651070 1250 931649820 931649833
    0x11e0b03071511010c1e091404090c050d03021e0105100e04141c0908060105031009030c0f0f02040609020c0607030203092d0f0318060a03020904020d06030c051002 72
    0x820385020b00250b000002e0810440440303141c241e4809010341000c141c5603075284c2c0d800030b02a0141d206803c00510034842001603116041002d44440080410016021540008c001040740303040c2391031100c664042c2d60085a4102d4480c241500881c81008503081c3c8d00e4000c0d01d800e1604a2a400c0300c3c012900d00d5104804108148840400310710b541d03500c18821100400007440310901103140c40002540701c00c6c11111461008140c40e480540031300107100c01401000c00354146000241c030703411070103120400c05640d01340c0c5409051252014180f440c0d001402d22081f03400c1400c000c01c1041101101783e000f14208140090320301458402c9480c030b0060f0744045d10160300c90301e000701d003e50310103080903131766208000f400c90320025120408446002000340925200804007202401c2600c50300c0116000c1d003082c411000090088821003119890882c0c0c0190f40c1c03403051005070000d000e1902810b40007071022504140105080e40880180c9010f03101d22802c2c1a5103108100384040c0007025000143c1001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 931652320 1250 931651070 931651079
    0x16031a070c2a0801090b06100c020d0f061506050a021c020a1b050a0e0f061012021e030106020c131a040f0e06040506100b0306090c030907030204020c011e0b0307 71
    0x5844410301c10394121101c5210a0792550143d00f91161845c084d0703602680d04040c03007007510784139035803050350345c1d95040514801500e6000182c402e40401c4014200560901c0045c0801000350700000c0b41a440210304101c0c1925480000e140307070010a0340d6030141c459408400c080c900317994080113055040c2e500600c1c40b40025501c50f81c3c0b50007041000b0383c02c009400c3d07011501d983ca44816002500d5001c02007c4649850603400c11070b15000341005018098440c41e0003c000d600404504035840304200145c0d4854524072603040c1403440016420400d4804400860b44642c0885d041640394002c07902d203105084c0e6051280e0407207400b0141c80f0040943c05900d02d0b5903040c04e80080c40442c040078800034154040000c00ca05140d41140c048910ba00428100001d600851040b80c0241410380c000500310701c1c1c01d6000ca89080c06c0603090181c81d000200c006040001c0c00c1111602865005d0001d5454907a6144564060601c1c1030040321a202900e09215160103a03114152540300000c0040000320b150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 931653570 1250 931652320 931652363
    0x60f090c060e01141b071a090f0d11100e03061801140c03060f040b060409022d0f0c0c10030e0d020f1905120309030406080c1303030e0316031a070c 65
    0x14000f004909001b40d42d000a18098103011466401258444407680e40440b503007004182561620420f101700d052400b81d10100b4040c00c6841002c2c032003a00c05110018400c042525449401c04010b90305200b02001c0081d00d10000500303000114249000340645000542c002d440304104407141210310b541440001c49610304254a0361000700c001d00002500500c107400b044507a48141c1120507110340020700850103070404d1852604c003920414000c04078108556066015110740415150f224a010880904c0810144100898035000810852294084c403001a0252046041c26403250240010140e01680081007441d10144030401500c4d007040080342c2682c0307100140105840503c10702c0065006d004107140110f005441ca00d00554503a0300d0810018482d0f01e0040070100815010f1180b8006446040c131890709036030f490b0424400e01c0780350b240464901100010383c60f51292685d0b200005000814030380380c5801755600c1c005415583d51b50000d866074413000c08000c01000c0b8045450700440c68 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 931654676 1106 931653570 931653607
    0x1051e0702120610060c080903190311010b0f0405091c05070b0a02120613022502040e1207030e06090604090e0c040e0a020d060f090c060e0114 63
    0x3c04d40500d49a02e00140b180c5801d005c002451101007108180c180c418110380902103c280381d81ea10007592429241c12000e8000c034801c521480034011040c010500315000c083d084a4050f51210300f80700041c00002c0c0402541d010f1803010310840540d10034200c450074543e80d140703511051181807580180c00043d1000404a01c1000304000da144442041c650143c0d00311511000da552107200038002c1d10440402c0da60030300139050651200d1800d02c1e240081c560003035500700700c48610b5414081d900c0312002403880c580c2c101804444002407040112800741500502114107100d916030100b990740e04150841c10b0340d6500d0700c22642d10038034100400403544004560611488054000c41906d94810b90343c0a80642003d41d210340620003250005180150040300400c00c0c0704050400b86500c0b440c80c024140014005800f4107071941c80341540042919000c20490f2a010758082c43c90381003003 = true := by decide +kernel

theorem cover : BRFrame.Cov 931474820 931654676 := by
  have h0 := BRFrame.cov_init 931474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 931474820 ≤ n) (h2 : n < 931654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
