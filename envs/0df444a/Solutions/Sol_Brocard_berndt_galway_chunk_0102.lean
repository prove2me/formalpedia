-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0102
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:51:23.999824+00:00
-- url     : https://prove2.me/submissions/53ddc2f3-4180-4629-aaf4-bd89f42630d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 18165474 ≤ n < 18345330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 18166724 1250 18165474 18165491
    0xd0807020a06020d0c0e03010209030a02040b0f0301020f0304050706020a02100309210c2d02091b07030e040506010908060c090111070e1614030606070602090d121704151e 75
    0xb900e074003280701440310362250041d00315044205409c0f4002c034035115130075401084071500180b03041d43c02146264801094241c4000208000c60f00326000303204070b414071180010078002441000c0011000400040c40240f9503103145a0124450b01d02ca003841c28285030700ca103969400c100b021042202030490181d0706040613111014010500c1008080990304134800380d01b48442110041d09000394140c0f5081c1140b110b4200b41c4c2402443c000c0148115038564100c005a1a98189600180a158000c0d0b4407680280e46910400045410103032550381440180b05080091500110341150f102d000a07a1286d00e440403400140c1d6640c0c1076400462040c01051030108400b0056900f07203000301340d11100c40360380603550701d410745440307845215010180d4001d10000340e072131501c0c9004090551140c80f000d42400f64110200c0d02402d00881d049072507450760520440781c25807051800c01b000b003031080e07005074a041035119900188014094184525201e049086268100103008200034101d0441000b2201c1c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 18167974 1250 18166724 18166747
    0x607050a030207050a060e09060d020613030606030221060a020c07030c030501020c0111041d060f060d0b010e01020a0213090305040302061210050a06080f1012030203070605090105090d0807020a0602 87
    0x3c003140580c03480783c0c05031940456118400c509101580601904d5003030191134510810011a22071003007282d00140c108684840d80c200743c1035000017140f141c0000700e40e0781c0c29441001004462403c2da22141c040784505000b10210004241d60484086400140d48480c0100c0c014203081c4681c002030725141a0010000c00c0000540c0140140e4503104020041010701e00051112440743d40b040c440c1c0b400e002424a44420324110809420001c02403000e0001c001001c04502c85801c41c40070200700c255203c10319101d03540c1040000a80e94424405000c13000000e0b40052a4000100d0041c42060307683c2070300b1820180501c044034040d42e0000c042c1c0361104042c0c100440071050032580e81e222600d2500d400281030902803508000c3d540c8944235403600d552102c140d1400e20000600c03c503840004e2a1000a018900c03010281040c0d0080c1c1c05560390301054180303003003030b29005002a5250307803401c2e04010b91880302003850f62a0040c903141c484801e85912078100d2030f001c4c5000014001c507100064140101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 18169224 1250 18167974 18167983
    0x15060f0406030305120f01050607080c1006090b0307060513030b06130e030309010e0d0804060507020106180f05010f03051203070e031e0606031609020d11030408120112020d020405060607050a0302 86
    0x50070401c2c0a444590b0318401d0a64441b1000c0c0b2485070041003e0000c840001c0705040903026074903803c0116000c00e803012001c0000d0b42c0103980034203502642c800041650703040070300c2514050310750350400a1401c40103c010145144591202500f0b8809100114550780d0b146204065940428681448074494105190703490350300038ac480c00f850358646481c1c1980c1c5c5c50081062000c4500940b19691a41c0d070f02d444840140c2001004041195a140304c04115404401d429107007500c42c03800c0000300c858400c01c030541100c0781a0000c0602c41d0540100700002540054004c402d41d2103005860b8481d10b40da50255290300d403074080c41703505000d9107588030741030340c0081e841e41d01c071203100400c03155980c859000381503e0f04c0780305400402d0050202c1b000d00c03000c5100d400424400641c150300280800c5621420340c1150000c0c0d504441d030714000101c0c000410f08200105000d072102d070a0340a0101407960004a5208925070300a01464442c000107240c0c0d6100010f5031156a0400d01342c4520103aa0b141c000e486 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 18170474 1250 18169224 18169237
    0x60e010f0806010e010303020a03050903240a0e03030c04030201050a09170a030305071e14070b040503031005060c0c0d0303020403061b0206090c010801120609080d0b0114070515060f0406030305 85
    0x540b04039000000c0c80404d07404024101d81e0103401a0400503e141c0b4101c5040d13210503851500b5104400320700f6894043d070f01d03914840101c010784105141c10f2002c1c000050760b44959449034180d0042c41407014604629048030106c0b42d09090140c1d813107002c0300069880030142c0d84603890841e10401d50520f03c1a021907003280c5c00c1d1180d84c041240380d035599000d8500540d502080c400301308581000a02450103101d078509006203c01d00c0b06c0c103005041c0d031014071030305040700c041b21140c0022091044540089101c10090031007151113608011450a949076a6a410403034180715480c5018560240b50080d8111005107070450014080d0b03661401070581a0610200c10302c005100d503c0000e920700d8008074508801500c16034a81489034640b89040c03c42600c0e0400945503103554044403000103060000501107400c0422020402d20f07000400501038030740714408140090010032415000130004261070011a4488140c801e56455590108004020a2101c0c1d90051703e40740002c070500d604400034098 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 18171724 1250 18170474 18170489
    0x201060306050c07030512090304080d020307050d020609060412090b0406031a0f060f03041104060e010e01080706090506030403110304060c0b0a02070203071a1201030f12020105060f0103020d060e010f 88
    0x41c0741c40d08001c001051141c0440900010410300221070a40c21f0040e4440e0404190800c881c1416200c801c0c0e1428601d0719100d40b800351b40300141d2102007050a100c26007040095001800b0b262420800c201c4e1102e42c000d000900c07049921140a50381406009031801428003020440c0c0c5403622010054014000d00d04000f641c2c0383c0032020803205260140014800701800b50015042110f8811041e409810240044803e070b0b0f2001601407031034450703200354402850000352004055140c40c80c44800c454040c3c210f4140d542080300203000361600030340500120341098400a03520f41e80e606080f00c0c04448445071701c525003c009400558940e006440f040c08500480d015006621200b0109040384102e0387e0094140c1c204580412036040700029000309003180000e9035107080e120490340794000c84240c00403030b244007191a190085c003141900380c0040580500007000710342040800a000c401117040441d04050b00010020448410b94004100500719200b0269507561075910000b907910950182d1030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 18172974 1250 18171724 18171731
    0x20408033001060306082e020a0302040506071a0a02030402030d0c0201050d0501030b090c030304050f0d021210090605090c0d0b060102160e070e09070c1b0e0702010b031605060d1a060301060201060306 88
    0x2403024103844100c0501f0181ca0003a800c1d107c2070500c504c4044d404c1500c800040c541e0034040040c49440d900010401580719190a99001c94000c0480741200400b90021031031610500820005840c001080e10110605042c0440030404520040311584212100d07050502d04060000082000c5044250b001b08070310025200c2680c0341c0320a256490066208044d0b05c101e00b004104131508160740407560740c60000d0180348a443c4a21134152404c06a4001d00405650303400446013402003038410726811400000c0a8501c45c18282d0006014124000c005440b2002d0000400c4030380e0300030000c403440d0640440451802035035690046c400440115503140108503003103642c1c10a407030649035648c0700b0109a2143e400b000c41c1621313540410500301c2c8040c2009030074640e02082908205c06234a00c0340c0040d5001140d0304200b68145810042031215003080c7c03031180c903014410f50751160706440b0041d105a40009d54018108104035001c44082e0031580c01000010011860b10350640181c0243c0303000707060a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 18174224 1250 18172974 18172993
    0xa090204020703030c0e1008010e07020a051501030308060906030d1215032003010608070b07030509040e010c0306090203070c0b09010204030f12020d090e010b130306020318060a02040803300106030608 88
    0x48400c00810106e002234003120040c042404806d420360342008462049510b035030640d41c0e0390351410540644514404410400410230182c0c009112640007100340e17403011403800c021010a03a14804003078104141702c602c3e2002213502096500414501000240e2801016602e00342900c4070102c50040002a15007403aa00e0700314201401032104494250000745005841c00003004e04070780108800300c4c20001c4c1040740c1c04003540c0c1c3d0b00820014080001c0000f40072006904043e0898080e030340182c1203113005000304a4401d4000c402e91140503000f0301144183c1da00c05903298024455a0070083c4a054540140010301555003451003051109030219032042d80170030310940d40d0f000f6610804260000800c014070855400901030240d07009196403c00d40c3c507440340c1d10784060b40c204452031210040103502420421500300400760b00310405a80c1185000d04180d00c180e1640b00f8184071004d000c0d020003440070800207501914050388a10009000300e96181d0031b0050103802039100300c00e0307141702e5240032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 18175474 1250 18174224 18174229
    0xb0c04051804020303040302010c080f040f050102100b03060a0b0d080414090703060f060c050a0c0608150607020303070305030c04030803010305010b040e010e1e120c01090303060e0c0d050a090204020703030c0e 92
    0x420b014070b8004005500340b80c42c0d6401110040594541180c01d81010300003050384d0710195025202800300308840111070303030405d000246050403816000c0740c414200004021a0340380840d0300c58214211680c040b60700d55a00700800c07000d0000d8a401401d81000040000300c5c803040e1001c0c0d400241044440765404e03229008101d060300e900717014141c0d600300d00003020010240903050ba86d001c00d1082c01610001f29032034039080e00031007166000f48081016081000065070182c2c801160301042110100e0030000580c0102e0b580713001d4150001c1c00d004002012a0100710340005580040da88249055500c1da10b034503000380a04114103420340958241512000c62400600646461400f035500421181908501b6000a40819200c10310140100402e4100350f506c500c00400c2070341500400843c00451624004007180d54550240a1010800c01070100c4c039889003044503280c16005901084540326251010000c21003107074020340c0a84005415010181c2581002040e0341d499181c580a25030500203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 18176724 1250 18175474 18175519
    0xe010609080d03050a0b03030705151e0604020c010204080a080d0609020301030210080c04051005040e010f051c0206160f0213020a0507020405041103030a0206010f0902040f060f020a0b0c0405 84
    0x15888680c1200b020590b032144a60b00c0b4550041030740001082c81625a07011a00310f92183d03e0954507a0042c00390420b210010b03241a542003a8aa030100501110124026203001c030003912440c4580d07000690f40030007000c2501902c5c050407081c4c060311046503692601c1c0d940d40c1e1100980c11041c0f400c00380005081c2040e842a64102d079009802113010030007a0208641046000700901141c40d400c5c040814a5110400e0b480310007420b80d111180d80d18101205511079200c142c3c040c101d44503c01c1c505002e541c40d000c0015006030b41d01903060350010103070310010b4480d000b008804060000d030001080240000c00e04440445030094442c0723180413090b0801003040e842110070090100d03008001c003600500703040d440298031130f018090300d00d6214143e400003810355101c150301f403005078440c10040c0b00645a01002900501c040e0508528241c40c00c3c0c5115080801c521a11050041401d008040310380244480303d04982c2c0450408014030b0080400c0aa681013802a0f9008800a080f040080310480e407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 18177974 1250 18176724 18176729
    0x105010515180a0306050709080f0309030c0907050415120c0e09060d020f060d090c09050108060c0f0909010906081002040b041511030d050f1f0b0d09050a06060e010609 74
    0x6050b07241c0345004480c01c480a4618404035080714194030008042150361044034016011541d42c810003030728004120345441c022070300050480e0001c00c203243c82e6640014100b0205081a1060002582c5241003641c0ca40a168030501082052914481c1310071307400102c80350140081ca03810400c03050051421582008030300865900a0040c00100703007140b628480700500385100508418201c1410f2000c150f41c1d80104039500881a2184802c0040181e005403190242c103210401700443e40c5051a140c0c0d803107802034029407560348001441604500d5031812a10040c0c400b40c02c443c2e195945940240c0103000b24400c000c4c01d4040e50b0503100000109000b101c00700c908014102d4105401c00b030002c1c011300312141100007480040c80c020075154100b88040e1043c40e1038000f001500d45800d100c12018910001c000940c1c21400d081028071480f0310ba02c20034140c940c903100103070703c0e200210b000c00001e0150354030107043da2241c02e102d4010410260854020340f180c40c01d4000c83d903680d41d03809a802c0441030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 18179224 1250 18177974 18178009
    0x312051501050f16060207020103111201060507060902090f060901060207050102070504020c031201060806130b0303030412030e070906030c051012020309030418020a0207060f09050d14030a050a0201050105 90
    0x408062400e90702c240081c040340580001c42d5031416031903940508052901e10811601180c021a0b08000c2d917030980310742c0c0801d082c2d240b45240f80070400507441036046014000c103010300601051840902045601c000d80055000c1c1c000d00c1a41070011215800c01012a00c240c441d0010800200361180701141c6401200c1c41a002022003e00303040801c07000c1d40010b11188000e210901c0b007030b4002581e64888038000c0c000f90302d55500078206a000e102c0d400d066448030700c034000d00380908200e003a01c0010071217074403a40109028400c901d60742011070181c00c9401030b601d080d20842030040f0311420540c0c40441101c4c400e000354012281e0b24420701005e009041801804a06482c0801c00801c01c1a001940c0c03108007030302581e14050f00c40c6000490520034541c1203000340d070701056140c00982c04000d210f02030055800d00c80000307280000010a96150f03400355a0080d006401c01c801001030840d01c0041414500b82a0782d03c80f6240320b8000e020350440140f8400540c02c11000082c5402c14008680000701d4a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 18180474 1250 18179224 18179251
    0x70207050a050f030a0b01060f110c0a170c03102a020726070303030609050f04150c03020c0604030203090a120201020d110309030f030306031002030c1806130f03031205 74
    0x282000c112100b01849040f036054000c031004140010700390110709028082586421a0054068900a00c40011502c079070b10745034070903001c480f015503401c90024100da0411544580e01d1182d201d07840c0c02c040c200020039130540b11315040f507114003c0a40010394805000050301d440b00c80e41458145414a6603907410740940c02c065030074020b503215416030100c4002000c1000e60a80401c201c058a00071580d8410307400250740b41418000c2c00003602840d504a134910042d8049401d0070f4035000c0c01c10350555035641c0b503290313906040c0e42036030b0083e010f6412111294080d25103515050038003035207a50144101c02d01c80c003010720000c50311401d492110401c40349c060780200842005400c080d00c404185034880301c941d00c021710000da541c2da41041580200032419001d5074582c1800c2d42410710700354030b00e03103591650b9005001700980042c0348003c0d2459100d03400c40d8604155a8040400c4c4144140095003101009001022981034082048035003180d100c0d40da8020a040242c000348125841030350700d030703001090 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 18181724 1250 18180474 18180479
    0x50f010611070f05190f0305030d05071d0402220902030a0c0903151503050f0709110f072009040b04021503090c0409170406080f09010603050304060807030b120a0b070207050a 77
    0x1004040c1e8420107000c01d900001d17190300c40e142080718000f5039104035502e40c00083c105003c4860390103100d81203445800c01100310b51600b17580415002460802c540196030105418107850721484801d03240c51720102d91040000d0b00e85c142000a58011100140102d0510103c1c1151621407002e80c1c084030303000160070014108035449100a059440031645070103440e240c010001c51010302c2844030b0000386c0001481068074094504c000d5940c440c48030041054107000c04c500f1000c4860899090075401010354511203072900280c5445106040c0b401c1d000680d1400300020003811440e0341c1d000d01c0c000c680400d4003103005005d0201c5488120b03416107054000c1d20128119080980020720b18620400c12541e80400140800703c480d001a80b00310002a801018030010400c4402d01c0c5402242c004000e11815041d40c80d0140e4a01c114400c2d0401c100c1c109001800340c921a5100206110000781401c2c0340c10000403107595690365115040d64580014004110310300c2c00001c10304112480a8603800e40c0c9403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 18182974 1250 18181724 18181729
    0x10e0d0c030507060603060606030e0106050108070e0909030d06080f160506041701110a030c0e030c0105041e0305011103191a04020702030a050607080f010b030709090506011101050f010611070f05 86
    0x800803c2d08841c0b5544450b004000500540074910107416a56400140000a000c1d11420b40e4080d0b80301a051003685424448803551180900400e000141e03401d480688410403050720b18461240c06000041c039001002c04c3d0a20302092038211f03101040c0031100c52003c2c140304409074400d41d10805511000c1080700b0049a080c0300c1d010000161031100010340c00c40c1940c040b1071300340d21824250000030f86c0d8900c0300350242c1d08000000040002039000384010b00f07103400085c0c402d10a6004003000c0d00c4d114261040c808000703034000e502440e4014001e100c8001024900030b80c0c1d40041e9501c0c1448461102c04e010020500d1007800c032001000034070b402c03001c0b02d0102400001d5000c4030003a40c150144034019030205608000b098080c107003a81d60720b4110720b02881078842c02030041e000610006030820602881a44c0003816000343d5100d050002000d40300c140c01694851604081900b05500701010004051991200c19040701c9141d100c2c000e42c80d088452168031040d042c06004042a180c140c1840b050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 18184224 1250 18182974 18182977
    0xc07090225081603031b0905030a030503040203070b0c01230907060e031203040b0103121701060807090522050702030c030711042301051008041a0403030219020708010e0d0c0305 78
    0x380156049803510b8250344a00340310400000f0281e0101c0d4940301c4c100c182410b001a4501d113003031945080c0c0501c0d814400001d03100c030811007000d0100714002c40410f00f0340d90709001880081646e40301c842d60352001d0761450ba000e040980036101c6060080c03441003202c8904c000c0200c0c8201000009024250300307084003a43c400344003841c01c580503c10350380503010802c0d5150083d4000c90013418264019803452404040f44044100440c0400048140001200e24641120750540740c2e2820130444031303580c401044880d10025032180c1d50110641c00c0346100f40c00b00540d00c0000e007040c6941030100d50b48890b0241e0b503a2041e0501c0c0b020320b40c0100034a030b020407074074031003410b04100081000c15036a00b038190428422000d0030882ca00e030644180104040d10344140c0039801004241800e20f920300d466190303950118096120000940b042600181c101482503044a4044880f8000c084002c044060000d5075940c99020b070401070b40ca0407881280031000003a00f10340414290b502c01132000c0071070f582180c49 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 18185474 1250 18184224 18184297
    0x1409070c11040921030207020603131a0f0601030e071a1804061502011a0907050a0c05030c0a17070b07140c03040e1906051507020604080607050c070902 67
    0xd01c51100d640d99a076039030044041881c011484881d1050b00401e030041c8215400c8015070601d407040000300d0040c0c031548140c3c0d500201c00c20001c4103249a5003054020805220b401110003154901044180915500c09a00039542030b0f90030459200c45043d0a07a90750b100d801743c004c403070191881e1a6940c001c0980103001c1c0c01c0641410580c0b040c17480c000314040d105c990308641024003130403400042250742480344081101c0e141d08581e144c4403030140420714880001e0010000c000c8001460818a40a441140b0115900a04580c1c0e504000c45460fa10b6001e04542100c0540c0440000c2c0310882405041e1130290b80c0026010721a9158100d068400c002c01c48200d07055113a0900601c1d9010760148068001490b80c00003072400c502c3c3c114281d0800b20429666440b84c1c07450f0640c10300440c0c9803a5006a503566000c0001ca94803406400050601c0c040c035440030146120304402c0254459000000d008070701169801c44000075100c050381c20583c090450556900c00071447e013485406c0d5200b0482e4034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 18186724 1250 18185474 18185483
    0x6090c04020a020123010315090309090906020715020d0e0a0c090509100920040c02060705031009090f03140a02060c030604230108070909080702040906020c030706151409070c 77
    0x201d40c803058046400a01d810403485110030070745c40040041c0b00c442e4262003850031380d01c4402c01203011282c1d4003402d42803a90150b5481c444d0743d40c2d5000d00300902d40e411980740b2500300d0117280240302d01942c0c2d83d000e03620024900c04544d0030244890103010000682409039540904070074039507403d02002d2001008010081c80b0f00784210581072891001c14420360905a010b900002c117000c28010082a40220002d111400341d4a803030b901c0700d03185a002c6001a00001d10349030072640c80d2510007428140522a42010b00c41c10300c0d26030240c041001d0300101e1013078a4429200e0700c07001c0d25070502d42c061500030304802c140540c10020000d10035840b0400219406800200002510700c441c0b40280745401c100071561034a05200801446101c0040220800a1030703854420700480307a85903079551040c001c06c0402030046851340d040404001094060710620004842141c0d1103030031900301034003d4550041044218440b030080800c00303000c44107401107030400192074800b554544003400c071004195101d080c0d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 18187974 1250 18186724 18186731
    0x50d1707120302070c0e010605180102010b0411120f010b16061d0109020108090102031e060402040b0c0604060605030a020d02010e01020a061d12250c05090a0509010e06090c04020a0201 81
    0x200080c00041c1c8201c0150981c0d8005898090310310341035001c024603410641c0e0710200b00004020541d409011240090401c0c483d01006c8444040142d002d809050b4030580c2c80f90419003a0000340d94500041d05403051241107100403500c1c1c4210445d41c5e40c40a006101d0101d104110045500706510440d40c0c049104500000c1c404040b050079a5070f0322080d40ca01d40031341c2d44402c144130941d81c0c4544a2500101c034040210302e103013072054461045d50003600030109c55821850000b082076032070303605460051000c180790316581c41c0481105512424100c400f100d40518203600441c0c24107000580512240e405070200580031901c2e001918204a1301e07402c2e504510425103050300080d143c4c017802c444082492001180c12a10450207030414030400411144401e060100030400300c002e1f1460300c9207682e20b82907510044200d04007075020005d43e412440c0c1005441c1d00f07202e602240c80e40211312684800d0003c0080e14040030869464074015924a0501c2d0311140c1004d50b6490181c0c01031044408600001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 18189224 1250 18187974 18187987
    0x41505040905040c090f0b0102030a200105010902190c0302070b0702040e010c0509040c030b03070e0402010c06020c2b0f05160f050303060415060c030f0504080316120207050d17 78
    0x54182d0380c088a0844103060401c1c020803901c1c4050142c0310000e4213420040c0040b0f03590000003543d0f4025814183e0030400c50b0318442542034140122490300d01840310083c0519a180e44544020f507000c1d00030a01c1c0c4402503140b55040600c52046482190b42c554003030500c94bc6000c06995854204000907070740543d861032103004c0d2150900c01c00600b580580c40b01070b240d568050030030044480320020396043c10304050905e1070694011458904ad504403101e020407645450004030340c450f5201c440103000c1032000078030845148001546070541c0540400203001d00c4160f0300d1131500b00603961844c50108004c10300007030b003103801071000d0540390624000e801d1089000d0b0b19282004095509c0a407226000001482035908142c01040c0b0790006000c0c0802031640381100060644104e0340d0302804005610182001e6030784204204c400070880c007800c42ea250f0314210308080500a0055044805e04034100c0041005070000c90303440215040140580100c01c40ea0700c8105121080841c0c0c10006001041074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 18190474 1250 18189224 18189239
    0x31504020d0e070b04030b04080a03090c0909300309050f0d050904050609070903030e031005090f060f0c070609080f0703090905010603061a090a0803030c0a020709050403020304150504 81
    0x140400e080303a400c011948071201d4902d80d0030519513070403400c040d100800c4140302050700c959540741c01a80c444002d99886800c0c610890082c4a00341c070080c48041220000980f61626421800196015003d0045021280c21503e4000880c10078180d078480c1704004600106030003130388200d1103540541c05485200ca54440302e1401c2030014850280402c5010035000320302e080c540725481e03026000b41e40b20300c0c103400c29060140c050b000d544001010403150071510360560718240950426011140c00c240303c1403c00c1c00081e82c03980380b00b0041c2c01d618418600011850401142c11074002e00b144080585031160039100c2d180030309003000043d14030907410401e031041c0e001d0b848010120280aa9554480d00341402c252001761401a4042c604040c208ac0b8140104118034024040b0340026907211036584061001048400407558803810350b42c0404010001c44104040007001d08540a500340c40b0140c0c1c540d4801c101711503050741e010340103901c244428000c0a2800354090140080b80c10312508142e40c880c031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 18191724 1250 18190474 18190477
    0x9030e03030c01020a030e0d090b070f050d030f0b0301050f01060c03090b030705030402010215010311040915050a0213050316030318080a150f0903120506040b04020d0b030f030a0906030203150402 86
    0x60140300c0d69400580440d681341d052003221264407e03200600642980722000070710210303550092044d82c101c009081000c10010000c9503d00d01d40c4402603442c1c0803030894014004008840a042c04d69003003a80c01c90562a062040904c20580c0e0004d15800c0e9091070802c45902080100c1201480816440850a40f2400010314031809540c5d55069580c030382440020704040c0c0039030b844a0448800c01c010301c0055152600c180d0301c84010760b000540c102c068200201e0441c4c0d0310402044082c501800c0c8507000032140c004103101c80792455848019607445090681d900d499403c0c00202210011090000910402c00c181e0203010081d05092440c1d10b840e00141426186001160501e810b41d6151300004010300032000601d00800e07007008040c00d9610081c0c0240030b1000003d0300740d550760000800650f5554820b02641708041d20442d110030142c071880f4020503074070308090700ca4420403500c134a01400020880e006080700b81e0b1000c424518080d000e5010b0b41001d800507441c50011500044540c44034070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 18192974 1250 18191724 18191737
    0x11403040b040507060c0c090f090605070207030b010b0906070210020c0306090d020601060e0906010c0c0914100503030403170d06030f030305040311030a091208130305030406020c100c020409030e0303 88
    0x1811807200e4246840c140b8a0401316070700c0355090080e040c0c02d03107020801c0c0340500c400302c2c0c4503407a003c50356882c1003d2500080540c450300400d00da14280c18411541e0340080c56805491282c00080810b07602c80e10311034194090f104103030b9802181080042c0c014100686010300c00001c9004590451417085d0020b8101030003112a0a0b080d030001d1146c00070f480c3c1c1000322500410080c1418240f0002103800300e1801a8010704060620400c0e0450380c003084a80c03691074008145850f000c20109400c00005540c841080d500703840c0e0030211860100e403070f140c08400c550449078841d5084003800c003c0700703400c52660070502c10420016941d400010104030710000d40c1d52228840e590000d01c40c175051a02420301c2d443c005c2c0480c6294814400c102a19070060780e4001075901180044c2c540b1b20151500450b6441980c21400f80707182d480000004020001000d0000d0303030455025070712494104000e12a2076140b01c103c0f02e00007458101c1c40c20141c2440d900c43c0c9001806468012418940703040420300d50b52008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 18194224 1250 18192974 18192983
    0xb040e0102040e04030f0503010f120507080607031a0616020d06020c06190e0a030806040e010e0a0309050306090a0b010302090702101506110303040203030706050910090c0f05061c020901140304 85
    0x150802040591101c00c40880c2e001b03600340503086504142804c02214098010003584d01c00c000302d150103001c01003040000409a20085900a20307000e04004c1c050405202403802e6200b50500c4000c0a1030000c0950b4007000505c4954100213540b5000c211080b800040252203160707007002805407402c0d060100d03600c56088606050750200d00044011304032400e0f034100d290390f60041c03041c002c00682c0c452a25500000f0494000c80d11403d4901c15034010180c00c00c2c4d4958030700c40c2101c01c5040603080b03030300078089440440036900c41c2c0d42c0703009110b520342c00c1d640b000500c1c61090100500062420384a103a8100c08284100c40380c0ca509001c10108407600e51904c0503590000904c00c0040540c007080354180c0313a140034090360442c28254040f079038a000d5620001c050a49641c0000c140d040308000d00c1021409000040c0002041c0b41001c0e610412213001c0c080c54a04411030110301401c0440484510080c6000380849508440003990000d4015180c0c0300e0400031801120051021341c2c2010714092800f5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 18195474 1250 18194224 18194249
    0x4080415050a080f0402180a02090405090715110a0204090303020706020307120c0207030f1e0b04030c0b010509010302030a12050409020d0e0c1203120601140d050907081903030b040e010204 83
    0x403000c041d1035010004c2610419007900710030040107845680c040c02c130a8a042035401019120500380d08064000c1f000384903005440d1104014026000040a8044030362040d12505501645503003111a00e0081700110b10720f5100b0190a80182030a40c0f00b007200c580285401402d000050340d407003007680c2c02682c0400000340303211083e40080d02030384500d9207200c0940c001426011f00c1c1d655004900300042d0030190996050041c421101e90b0a0701c0e4400c00c2d1503010030800030354585440c024109002e28482650320032000d20000c40e4074207223010100d058a8008009100e01031040e65210541252034160348100401440005500c000500282521002860000ca82c0c003030702c02c0300315280190034142d0328850402009402c0640401000f10b540000c50031510f0070081d0358800068400e100c2e8000820003030707440011004c0c48103807268051030299a000044c1c030041031362901d0180d0b844480c17203403010700b44840c1d4a104002070f010b13a110381c1070000d000d00302156265426840900320780150b03200349102c016 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 18196724 1250 18195474 18195487
    0x40b0406020a0c0906060c02060310030605010b03040302070f0506030a020705011b0e0301150b0405090702150703060e10030302030429160203060109060e06100513030c170307080a05030408041505 86
    0x303405030000036000d513500c00c100c45450004001c004182070b200181c02801c001001ca4480004000c510015540111091000d965104115041070b442142c00343c005008600c804603a041c8200020411101c00405281c110749418142c1c400075840142c0c21143ea640e50058201035910350101181d1804864031000d5441c7c1150081c94251180075140703a00450191109018003100c4109440a5610689401e1080e943d610300a0380790101e003190304581c018500c405c02640da40c3c1900203030709803568400361001d82d0f10b03580ba03220612509400001d02680051006202519110280c000150708825545d5120440038030454034079032220070050f0090228860328029401c1c10410640100f040c1c007801c0103140d281c0075203800c000c0405000b0030312038884030320740912251040e402d0710118040986940780c1d081c1c0c4c0c0d244c104918035030381c032420f0b51507814104040040c10020040e50300c800d411a001902c0c040d41c6440845e02a407000b071045440590034000411b801d40c10741190103c800c1a40c56590b940c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 18197974 1250 18196724 18196733
    0x90605181312081e060303031503030706021206040e0d0c0b07020c0a090606030630030c02040f0603020a05030111030a09030504080d020c0a0f0b0702010315080f1e010b010c0f08040b0406020a 84
    0x34071311620911032400424008036490000440741c0c0541c2c048580d401c40d16005000034110710170f481026052500108007842120400902c250094504a90401129805124203a01c502c5041100303400304610a200b90017003122044c02a60000362441500c1402052200007044151240c008120440e500c11041c86490f405224a03809070982d4031402616440003034603c071003220701c481c00c1032020f030381c41015074205030084c80c0b035080306034cc002c02c20701440c11307404602402401507100584c403543c90340500040f941010f1203500c0e51140d82229551969447c20b04103800790411b070700c04500704001080300080d10b400501c80d081f007009045d030103060b0142c030240030404090120740060726618541c110410420740100c0440f21882d80c203080103c0c5501060450005910b0160300210310b600800d500d49202203800300304103a4941c2c0603e40d0011000501e601c1500322146140e801e80454021012130300402c40082801718074504c1041e40905d010707141e042100c5640c0050340304001591140750000d0801 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 18199224 1250 18197974 18198001
    0x140a0f060b1206030106082b0203160302101b141303021801031109010b070312090c090c0201050f04050a140c130c0806120c010507030c06020f090a09060518131208 72
    0x3e1082e880101130088c4a0030f6501094200c0b01160b004443d071810070310703405c14024410b6070381241ca0950100c4210aa900300a5140d002034001c800c2c0551410740000740100703400039089086102c55035030034444080300b0140c9020b0352090716055540c4095070400001039607500000310354076903807001800301c13549585002d01400d29400d02061240c68071000510800c464801514440c41d0103181594540605650310340003000b0302c1c6409401440e401c580410145030030f410441540c0e2066008003c02d40d1180419019860103440c004c1c0701ea003005203da80401d804285959080003098295039000c034514000400c0c0d003010980c15440952190070620b03140350807050701d650111090f2041c0c80050508400680c5500c0020080740c180440030624509040c0f00d009182d0715158405400c540d1442039901c1010a80c01c800f603031610880c14414042203d6095004540450340c0142103058240d0307043c0c00402d110000140500c0142c041d0348a084041031085141c0c841b91001a140c441d141e040c07083e20f60102 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 18200474 1250 18199224 18199229
    0x204030b07020102040302010203030606160c031202071e0302090702070f03050d0e0d1112030409060f080105070c0b0f0705090402030a0f0c030204050a030209100b04060503060f04140a0f060b1206030106 89
    0x1c2da48148000c0001d41d801004032507002d442200c0450f0f651017000c402d2500104020400303007e0056400e0f01208200c03090250303c051110f00c0d001c50311020340e2071902455000c1c420384003070b001c0000c1c26810801400e02c0801c1079008109801070300c0100380c440b0b04420100320f66500a452a510505502c01c049401ca0304070740c1351040c01d40301c0e900038045d00d458462111040d04810780c00344804900c4c003004602c06009a801406c4540e0044c407605580c0d82c860b202e106c2c4d80c1d019829080d4a0103010900c3c9c20300502c0d6218880380d01106035000340e0f0358428140c0080000801c801d092000800400701070b90340d80c0c8000c601ca092510380005418046100040c210b840485004c0700307062040001b48001c1e591400c2603022a9411510b0590030390710908604241e11003030380000582c400200303011a08940103805140310b508282d07048429018407038200030654640e44004d445074111140812501003aa4020340440c484103500030035450750382c0c0c0240b141c075484904920420403004d000c5c070005280c28001c5000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 18201724 1250 18200474 18200477
    0x9080d151502030d05101d04020a15090807061e08070309120c050706050903031803030c061e0903031005040e01110309030703140708040b1b01060b0403050607030501060509040b0f130204030b07 85
    0x555508041f0ba01c8000c0d0328006880c018480f840307000030304542c0c840380980083d200800d02401c00740442d40024000c4681030107140e02c07502620202081c80b034441c0c080045e000c800d20540c0100242840c3e01915004030140100e010035480d00040c00125001c1c0300170220703020517a80c3d141c100000908240f0300344525a0000c1081010070440410503980010030380e604450800c50801007d206200000c0c598030940e800c0380c071180119010481114008850f43d1024003150fa404a141d944000c42161244000c44024030480c0c0040004d0107542415406040625142000000e07410489206200281c0085994480360307400051480c040641c05940c8114826081080b14141505070380ca40e40e0b507005031f01a242c680340d0045601074040096618254404614a0007000155258540703415903901c94002a03616100b15808101a64481d00c6228100d400329511381d4140103001e0100409000d0740c00d0341e04e621010048507068140d98888004000c83e10004005907924910301e807129031820010031800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 18202974 1250 18201724 18201751
    0x304050c06070b041e03021f02120c040302100309080a030507020f01050411040c0201020705060a18060204030f1a090a030509030109050f0f011401080d081003050f0c0108010909080d151502030d05 86
    0x7c0e00050113049620302950000b401c40e4a000d6510028040d007811700304000000d000307000c40741e00c3c41c1c0010415a40296411000c40d058180d00f41e040c2c2d415980b0080140d08100f07c0114481d1081c0d11041c0c0000305403058662040003200c0d00b44c00d50f0001c1d00e060702c042100300366501d000d1915101c1c02c0c4922050340003c0d4141500c5480c3d0545440000b0716510a440d150381600b00e04500c6066039085080e4481000c6443c2c0fa1039060888410840c0001200c2d40407c501c01e001c1c82520304912684103008400061040d100143e0703041f41e041c1c00074207078540c0641d26110b102c03000400500c58003082c6074521000301560032a2030b040600350b0b6043c1c100f0841400750400148100380c0c000c1031404000c1800d0902d4000703500d50b880c00c0d5503000344582c0058080d0007240b2503c0d5090030046072441590009032b0340c03085503980b9241d07600700b00c8501c928001c0041000708800f880068650b00030702d090b1981541c203001c07820364401c01c03c40720b02060b85100380140c10024949003440340714400d05810a038500500c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 18204224 1250 18202974 18203033
    0xb030f0a0305030a0c05070507030b0105011829091e0307090204260a0803040b0709080105060105090d0602070f0c090f020315060711060d0204051206040203120304050c06070b04 78
    0x251030b9101c050701282c1159110703016807038414040c50440700360395880f00840b10020759909008003030800031302a890004030650000300780c51700150f0b5904180c40b90340b181c8004c10400504003140d950182c40c444100781c4014416260079a8925001c1407860b44480c0c500704c122404d140402d0f0802c03c60b80c00030203105105120902042034445070112154040c0505180c800d41c43c0050186001701342c010003400d01e00c0002c204403c1092032020b02c0d0017500240c0f1002c00c2103407608003050a8840460391180055400c0c800b40800f4640b80c9402c00a003409030000629041c51921820030040542000741c0c4c0001d4040d00410010032140b18098002c0740366801141507042a906618003160407403000c6119036400304140e402c0c801e64040013040d03803a00a09090f03994801c60b00d040003a4003d885803511070019a044c00071204000724580c3d21542c2e00801410742e004045500c07030515000900165403e1140a0300e81d00940c6a00c00140b00603405560b5603907140c54549400200700f2900b1a40500880013400034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 18205474 1250 18204224 18204227
    0x1080604120c03020c030106030804080618060a021b07030303051e070207030312230603010b03010209060708071403040303020102090a080a020102100c02010e01061401030b0a0b0315010c02030d02010b030f0a03 92
    0x80d0790001200d14055800c0481828102d1a192801d0b400c6a8554a010b9002040110707101c010011100b8050a8179015a034030f150014800e4414803105e0b585401c0600040e070301c407016900910700c11740b80e6501c01c0304070400585100d181c00c5081c2c00440c0840c0d981d000703200e481d60340341d01011400c9102c01c000a0882c541182c009442d00f241d440006c050141c20400e20450b56015081048900c10180c00100102c1d00d01051120a12061b51340c24000d520f41260540c4504060089907016031300601402c2c50f101c43c503522003180303510000f01519010480c100c100c4615505000600046010341d00158980110388204891080160b0100b581540080c0c803000040c0d0700400d10070304c141c1c80300000041a6001c071034241e000d089103081da442154644000403520384034260780c1b402e000a0070380c0c6c200040307010001840001703251401074191032502400042c0083d0b80080082500840c1850490483c1c1407507408240f03015001d1258001503516200002e003d410100802140f05c1005001405200d0705500d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 18206724 1250 18205474 18205493
    0x40804030809010c14010b091803030606030403030b030d02030d0612030f030507020f0708031908060114070201020c060d090b070e1507020a26060a020f2209020f0d0501080604 77
    0x1000708100301c04500840c1680c040c4803a10580c0384c00c050301c0c40720960341080f414000e20142d001c2d64030503402034011840341e882c09110084d55401c80c00c000c51a54680004001c0c0e980c100a10403020182c4452945199031402e010310142d85803190000e5844042d01403810b002d4440c19000040e0390000404243c0c04694090300003c03813842136040010b601c2e241c2c03150483c240420a03c40000501c1420300004600c0b030000004d251644134210a02c00e004400c0c0c0003259030b81015241c180c00aa41c0309a01e14021408800508000d4130500459202807403070000304000b6040444804516a520400c80c001d0046905580341c0c8040c0500d07010030010200e00009a8410355410030103030040c0042040000c5403079019a00015040c603c1490310b6202c250150000b054000c4500c16007680100c0d000f00b4900006070081e102000751403c4001d0030401002042c0408000c08004161481c805402c0055030380010704c0104005000e03040e52590b1600b4203c20b080981e1010b03400003400394002410040402c02c0c102 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 18207974 1250 18206724 18206729
    0x8061302010512040c0503030c0c011806080609130c090903030c0c05070603020d0b0a03210e0a05011419051909030b0a0b0a150206010504060b0c070b0d020c0a0605100b03040804 78
    0x10007810107132a1414880304191864012641500c0002000041843c0000e610314510720242d8803840c6040e445941289014a80c0c82003401055007400030074138524051800c9070b0300080b854443e8002c04490f4035001e00315149540720318400c983d00d206030020705505005a9800190230b00f450103852056555884c0c2c0c904152144c2c008040d800710700490b5415003500181c08036400280031826194403802c02410305107a1569500f5042420610045900c0c001e03501000c40640003131002d51014070b082d0041d100785581c54a0b408095008101c1c60402410344118046070501c00c0e6100750301d40040c500d0b80201964041d550b141403204811b0100b0001c0c100c00c42c15680134200b10400308010f80d0f8440402d216103003540065200c0c01b9550103502141da4005682c82c100c03001114140f1003150344a1000700340340702d41280c00c00143c002c55018403205400304e00a00c80240190340052804103410790913401c150154038200c0c2c0f411340f0380b0140844805400d011401130040141034610f0341c213240e941e0f01054443c92 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 18209224 1250 18207974 18207997
    0x501050f21040c270b03030c060c1201120f0201030b0a0806130507090b0603130f05030a080f0a090b0406050601020f0313030b06041509090302031b150f150f0d0f0b01080613020105 79
    0x45c000e64105403024001d448500300820101c42da5030078003e0480802d50840911001d9400310100006405400261052405500051131200081181e001100900842200d868009807003c0001480d02800c11407544503500d1040308046501e5549402810014240c0c85551042e042482e5407009940e44400c4940022003402541c280e103426241500b9900000b041c0501a4000031604100c1030703401c1400e0b10b1040740c044e403154031903654140d0400304132011128040c0400d600c90000400182d159401140c114405004803042000844002803542d4080140b59520781d415401c100208140d840c652a00580d04580c10f1103041c03500360043d0041101da218800c400d0342c480c100401490300900484440b0f0f00340c0001c1c103469660b4091041c1e07072205058501c070b03c0c86801c0d10010712040a940e044d03e010304080c0f228600800b9281040003940240b840020b940040d455020030001060107039807002941c8500d9000e607007589806030721410b0010043c0f50303103c0814102500c4e070041c2c0e401000c594256044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 18210474 1250 18209224 18209231
    0xf0605030a0e0304060504060908060106050a050304020a0f180b0a120803070e03010c030207050c040606090504090501020d0203040c031e0206030414010902120601090f090c0501050f21040c27 84
    0x40d061500c000e40ba42034002e4410307000004012072155441030041c01910000d4135500a8a40e642c00c403130b80c1d100802d00c40da00000d0b5042c0105402c1612a00041d6003041c00240b40c1c2c025603417105091a10848282d1003591828001020303041c540035a405030346035000044034180c00142c900f0318140c65a45041100829100380040001c08040c007600b400107011034081c0003004860141072002e0001c0d4004142078409102d841030301400e600c0d150041c0c00642d0320303681e035000711140f610081c00060441840111260354081c030002c4502162807018620442c094014030a504c1d02d90f0505840b004286c405010031511203640880268640604032600280e0200c0950b402110402c81940148903c0000a61190f201c030b5046480210002e449410307545d0b041c504000c6084410820021a00d040740b0040041d5000a0100015802000030341104081030140c070707152136400150180f02c412030009198030040e126040c4014071a03d10030106c081d0440c0da45029401520602d070b182e001c04c2030a4034001107500e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 18211724 1250 18210474 18210481
    0x3020f010203131203090806060a030219080a0c0f0b070f0b0402010c140109050606040903020a020904020d080301080601030c06030e030328060305010222030305070b10051309020f0405010f060503 86
    0x1080040b03c500c44600400003600d1500c030388a410071301207610000c0d000a4021403003c540c410001c80d415004580c000c080406003840c50303003400794080040122026404000320005044602880f07910015413284040151481c01d02c0142100f10880d500300c80390680083c41444001800704411048040c3c00002c0d140c442c0c0c0d95480100c50399101c1c68030003864600e4001c22030b585000c054005500c1d09210b081565400d940b800140000c4410020340640141d00105004000d07080201c00e4540081c0007a00105110b4090b4072880e072103500a80c0300c82450340c880030040081c00070300f41d0120301811f92450103102c0081c0308000340c0c0d96400003908c40ba02ca0032400c00341e0134503e5024031019003607140b64241071100c1790307884c20564002e4200c000c64210f24584817120110060051800c44181c0b589500c81e107003020141d0702c6103080240c0003050300c1303004801c20001041030b40d03d1030b80038040051f1a10003c1a003120b40d00c14000e0410361401028081d5007800018032222203101c1c114410340300149010754503a83c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 18212974 1250 18211724 18211727
    0x5070b0706060b1b070503010b03030a1d030105180607050405061c1d07060905100f080903070f060c0e010c02090115020a02040504060501060f020601080309060903010b03010c09140a030203060103020f01 89
    0x96143e0010008800004281800802040c0d01c0b050885040d0155600150780b4000d040c00d0320750201d06541c1c503420402502d5102401140040b003404058042860441e9882004c00d084603000c0d18240f000b10a40c4049000c4440c0c00c200c0704e50300980340d1600c11300349440e05020841c81d0103443c4101a4018407184101401112a40610455901140300f84407034071500c088592100494012000064646000821142000b02a00000b10003a40d02c0c0b8800d611358010880d0b00c044080c4c02d0b101c0e1400200209408107404100b2001c81600400c4002010600d803180608078000221001e03045c02001000000541e4550403ea0304496041c66410603040458004a00b80301902400075840b501d0a000e010500c5040d80c00b01d030580e101c580314a00d198500305410b0366501d03824801e070541c5520800440c40a424181e024200904029001103211012107000900359102c00c840400010a03140c030422520030150168111300000365221100c0e41d0854010a450b0070050002900440c03146c1c4041481380d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 18214224 1250 18212974 18212981
    0x10f02030702090f1e0603030d09021f050a0807030902010e010e030a0b04050607020d0212041509181a011107210203030712030506060a020a0b0402030f01060f0306110705070b0706 79
    0x1990040c0045007a14103507466540c1c12005030340c0070413481c800043c440e2602054124103802500010008e609106056040070050150100101d070014082490940d442201c0c1c2e60285518425407901a198459000d0003003458034000d00980806040490207401f50342c0101107460b4202080c40c10700514500c4402181c90881c2e0114001c00f42c0e000c5500b00018044041070380380c0690a0381c1d0030f4414000040c1d20490f030b2106a40b80c1a18010300400c020488002000540d144038011414061481991803a910101c40700056084055a4071a0200d800031450014980d4a0600c03d0070700b9801d01106207921130751800c071070007002c2c8503644013000203c150710508802c06020ba40101125540c071010300e04401d25581103c005004a800c0ca80407038218640340c01901c244103c554000c0c101583c16444044500e44090070683e01070103201050002c00c0e1080c01002d01500444c610140b20b02e10f146042d4045415664040303400b00340503c0420001030700403804004130307015040b13855281c03099401c106008 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 18215474 1250 18214224 18214237
    0x702010c06020c030705010219050324030111030705030403090f26010b040e03070b06010302070b060f010c0213060e0606070330050403030605130605010807030f0617060108210702010f0203 83
    0x111301c400302d1140200314054005011407500000301000407441c40d40d0695440c0819103403a119481e104040c5813500080e004081c074070000050010620540180300c0102c5a401030314000e000800001c00c201c14507421109a200811949940d003d450740380115260f032461500c08200075040c01c4803042c80112409400040c1d22030350041c000c00150101030ba8446d80c1e40c0c00b502d011600d03040394100141d104d40c00703442a9003020341c002190110b00c0c0d84400812031800d103491405030501004c00c2d01ca10140e1a0b07008080b00d18040e01e000010003900b020310508035240001d180e54400c00081065000282c0e00c091001e031012031510b1644058818001d90031250780d080c0310601d40c0b4615001c00c000c181540758102500b1038100356110041403584840c0070003a200c1c10300586001c1031049011500c5540311740e20600713080d81c8100300008c03400d444030380300040300907041544c41e030580c0450f00600c100c0c0002c0c00510b4400380c2c000507a03455001d144810b9000d40c050200c019062203511070080c00340e14024803c8602 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 18216724 1250 18215474 18215497
    0xd02010908070801140a021303060c17011707080a020303040e04050a060f021206030114010b0306010c0204020d02040302030d110a03050702150a0c150b01020c090a11040306050610090b0702010c0602 87
    0x7442503c03105128028082c1e00d0003404400b41d6000801c254103014821604001c02280c03a894400382107440b441c014200c02114141046500141c408449c81614a401d0103000722000c4124842116803031640b41000c5900004015041040107100594000080743c00300c6103155194002c035940ea0408604090004002405603400e0109403034145440c3e80c01003d41860181c100e540a40f00c1d0700c1403500301c03100501c03640c1d2410350010051165106a0001d076501c558145401c00301d107111540441c0581e00008400d550113030700410144218502805a03042d043c00c10300e48080303103e07001000203664a52005000d402e00c00002260000c2d900e030300c84031030b802c4040c0d001d1203aa00c03e510b10b4000d042e94041c50040da800002c80d0403c2014128074000c80180c000140d008003c0f0714030b000300f0001c0080c00501016010ba6851070b40e044501018809080114080e800000d04e038600601030000c402004114503040007602c04c802d003c00703008101512215502803826183c00c00613450100c00034800c5603401403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 18217974 1250 18216724 18216733
    0x9060405060111120a0f090602030d0e24090705040b0303030a020c120a0f11030a020d0503060a03050105010b131d0a09020f090903070311060106080117010f0c0c05010b030f0303060d02010908 84
    0x100c00c84241e00051448032041d540b4440f080001b000102d0b6200100c3c0580001038108003d100e80002c000e80060001c3c10348002942ca001000c05582502940d5880c150203424806c0d0040215140e001c0c40140000d11060b80c2c00c1c44441039200029480c2e01c0000c000c6840240e0110304016000420403a901d0107074030350785042d44e40794201d140c05885204461180b800040051f2055010454040f041c3c900030040c40d001055044010081a52140c02c000c15241c1c000c0c2c40f4017000804242c090103400e000301101c005070303540e070703000c10828541c0070130140c0200d10b000d0501d034042024a816105010f610000d1684001000282440003070b00c4a1445004564850820002e00018200200090403178503c29183c00e400d0300407807071505032114402d00c41d18010a40340001000101070459440c59806100800050314144613100e12048403410481d040009440840340f0381004024401c4903114a02240103281c01080701e0026aa01e00c0300030841409140c007840c03a032085902900c0c41030060101041501d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 18219224 1250 18217974 18217993
    0xc01050c0304091805010b040b010f0c03140a08090f03160209070509030601060504050415030f1103070b0a021011070b0105010e0d050105010905070e01080c0a030218091602070b0909060405060111 86
    0x2003c62039030640c1300341c80e2075107090050070041ca45840382000e10201a190201141c2003080f080d908260412400e805004594040b00c0c5031181b030000400e0245041c1d1903501c4030341031160500e440d00c1c0e090391001c0b1055108200300c080382d5400d1070407030016070f9046842140d0343d564004210740c64010000c101d501840750a002007012900030f4050010380d04140c0d01000900e45441e40c13000d02404520001e0005580c141c5c4140c00b03e0f02c84a61100c2072480038084a00343da94030500c60099904c58100038006820101d482034403461a40116820b4111011690b8105189074440000458041c0705440c14008031080e900b4090f280d00c00702545d10341e04240200803960391050b50601070075080381c885001800006004809601031041c3d82d006505655100d4200206001301740d009611645245290482d69940c40c10b16964040410348201d51404800d10044007180d0041e2034120300e504003401000d0107000d03240311a11085001540004100c402050940301c1d003006070f41c1e031039a8501922440c040d03000d51 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 18220474 1250 18219224 18219251
    0x6120203180102070c03060b01030207080d0203070c0b04060c1b0b06100201060503030f03011e030c030609020a090513030306060201020c0c0d02060702030109030c12020d0f050a090e0106020d0210020c0c01050c030409 95
    0xc01781207078003c0005100c49400400114128851214001d00040040c880c2d0546080b243c2d000e9a803002c018141005020341c1a00d580c084a54201c404555440d1628100e00526034090080d20b00d07564495060340300c90303000d6074940d00421230007482c0c0d0b409050441040b240c000d200b50001e5000301005030940f540d8001110310340c002c0c3d501c24000d030b8107080d125031100b40d00d00d00e00300480021070f6000010310344072500f150758420290540000590348015030041c0403075008840d01c00d41c3e004508000d5403010521701441c000c0d003070713600941c0080190b91050045440d46000800d6050000404480b11100e258403032001032454082c03c140a50503600c2c2850701002c243e0031074038007100c542c0503294904603d040c0803030491780c4026410070039001400741d00c038940c41c543c010005030000d90b52030708002582075251a054500d00a09a04c9800142d1107004a403d003542c041c8000c0703004401c0791205500d050000b40741c49030f45050005400741006070024010160040c24000d0768043c000043c001c0c800130348036160 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 18221724 1250 18220474 18220493
    0xb0907060305010506090d02091801060b04050f03010e060705070218012907050a1403070f15140903070206070314040b0a0305060103090c05040b04020714070609060206010612020318010207 83
    0x18030004240740c0390000c42c180c5420070944160703c90017051440a00242d600b4801140d10191000900068001c04030840d00c40038001c80c0d0161204038083d03a00c46103450100906441e90040d554001c0e4908000400f4004001c00d00d280d1007042814900e5841040f4404078201d444040c2030401303500f40c1d80d030001c01d0040c40b14038203034003401074180a400218101c0040003007c1c841c014ac001c01c0d5501c008010000200c0700320340c0001d101b006e442968102a580d4039041c42884240d0030454032032100d4078012414101d940710307010401c81401c28410081c41c08032015940d0f84903042020303111b00320200f4000101071003080010420859aa81580c94075030b104c8a6042d29084113401e000480d060000040895110740300d000661900a036490050928101c00e20000300401512150095000c00000d80030402040d90a02d05c895104020603130303603103001d000501100d45500018110b40200c4010400c9992023500021002055400142c1c0c1b61600900311502d152401c007500c0031540003003540c0051010441 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 18222974 1250 18221724 18221729
    0x13080c090105030f15060f0904030306050901090c0207030204021b0d0806010206220609030201021e0c060c040501050307111906020307090506130303050304050c121b010509090708130b0907 83
    0x44040d0034a03620760b4209921044e40c2e282070003840c0c1c0218151043e100100380b01c650012000303858a58211100c4000c105221001c980c1500400c1d00c921040005007411071a041c014403055008204100f148070000351a00c0780f92002034800c03a000701d00406541400d42040d6105004c1c04102c40e040d20302d500014048040455036a4090300600f40011400e441d03106200040304e503c1140541d5000c071030340e01c41000340b103201d40540c110366080c441c00c0120445404100070301c24400c10303016264030492030480d2070b0080080c6413080340c2405010070031140c0d03002425039810003514204041002211020135241881d41600218001c084040b10f505100013540214058003c95031095503103a164002d0161601c1413a402e840c844012000401c0482d1086014582061154003560300205003400058081c10441000c08803580000d60802060b4900001c000a107880130708110782800b101c000040d4803450000c0080003449400700c001036005829152030a1040d83c8400c500b80142030010990342d5458050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 18224224 1250 18222974 18222979
    0x11d130e07121a010e061002010f02030702030702030c0609090c070519060c1205010302011b14030307020102040618062a02090405010203011e0e0403050c0304090f09060b01081605030c13080c 84
    0xb49240428010f040081034181d031410740b44a94a621024141710055a50711000c0d021556501403042c0b8942050009502455050313008507160b6400c0e0040605190050b01c1180c42a41304012051003919117101040d80045444003031502c41d006414102d0401c0a29a4a000540303101203104041000e940e0001110034443d996003c50008401c03000c008941080c00041e000c10010468600c03d561040a104000e500c90303084503000c42c00d4003400070324541003070700c0381009070750041014462150301113200e14580c0324400c40e243c1543d2420368090580302c09000040000f504c0b0250180510780a0711980300c0040d405450040e051030241006c1e4001e400030701681c1c00340e00d210f21a0051450040d0007410030b681820f91020015103c96505070380d1640055088020f9004c02e00001800400390711494008154000000c00c05964a290910407940c180580a0522071130005015a00c154100c94050601e11030030034555030740f50848c004142e40145100d03242691b41120000c0f07034440300411407030341c1c05805 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 18225474 1250 18224224 18224243
    0xb061308100b0f010e040f020d0603080304020306070906090b09060c15010f080a051b01020705100908070605160204050a0605040906020903070b0a0206040308060a050915030c011d130e0712 83
    0x50b80810440e01d1000e021240010018601e966035450543d104100d003c900480c0180340c240300f007200c50141c03217140d8425940107001000700000e504090011545c0940d030b910706603103002d0070100702500d0102c1078014000e03090008140b00005464041c101c4541100010440300710008100003010114401d0280c0305040501500004800000003020150140e0000207000714140d542da40d860348280d0366005904511800c034001602d038071510742c030810140f516a0340309141400e0a01403441c2c902d00340d0101c0104401041072514507110805002c0e10650b046401240d61340300c502612029201903007080394001c0c5031801312401c001d045d5009060710442a001d452586556450303520090050506800158002500080c00280310b00c000036400b040092203040103944038800300d40410404c690307038204104486418460b925040200c040c181c03500340307010500401075590070303000c00303820f40d043c0c6001740d44881c1c040c0c030403028541140002d00c4450045444041d6070f82001d4000c00480382d81070f120104e4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 18226724 1250 18225474 18225491
    0x1204141e0604090b0616051c0206040804030803040c0803030a0c0306050f01090515041a0301090e07060f030f0b060a0e0118050603010e0a020d0e1e010504150b06130810 74
    0x140000032211850010441414180340044203c050180c550180364010750400c4208844821000c0044960f030244000301440002a0320850504a940342040300703540c850800c02000400510031107054990000000e030712601c680c94035451640040d00071201501010003041081c10841d4055064210f6a940038001c0039552010300c6004400e5400c850300140384110140300714201034464002100c0c41d2200c2c14a000d42d9200341c0401c014980d41800716141e000401004100300f0350041000404181000d0000f19241041c09007480c0d8480725001c6c05c0c5a1194030744120101568401410440090621541d940b10120014803001c140c15100f400f18180441c42c580e0303000e1949190707068070000b030311552031030342040f11031034880c40b00500407404540c00b0080d0041048040c084c02d09280030340002012030080102880140070940307540c004c101c0e85031008003c00300300313002d10320740c081030448038005881000301005c5540c902c680c1419800c44400343d00c0015050b003001600f020701c0b2481ca03404000e41e40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 18227974 1250 18226724 18226759
    0x25050601150909020f0304171201090b1503190507020f030304050625050702040203041106210612030301090c0203040807080313060c020d03032708120c2802120414 72
    0x25441740c50014600038400240064202c1030b101d075a405010461034181a02c1d21700d42c0f94115826041a40f20b81c0d2034402c0c141040c20402130341e0350704032440404241140740c40142d1045000e80306a0012200b602d8802203194139000780840116114041e080e03a81d2480c0506010b551044151141e200f03040c44600c004186482c500792a0700280c0d03070750380c42c10b14005040d020407029400203001a14071034450b030040c2c1126580c10005200b071462280c00d02e0082c0514034042a00144010001e60280c0d00c20354065240c4a07000c03045030b042d101c84101c0043c600866a000f00c0c990b0180c0d0f00000e411344245403000c90b0201000018192000b1508501c0e6801d546600381216440050200290862003c1504100007800390f00a00e4500402448090605603804040c19039810940303010344260400040058040d80903000180d40300340c05442c01442d2801d140f040086c007080419131040200703108880c58818a04c240402d40c0002040d038041c980721911441c1c480c040340c3c01854401c0c0b26407c1c01041c1c04500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 18229224 1250 18227974 18227977
    0x8010606080c0a0e040603030c03020c04020301050a0306020d02160f11102f010c030603021804080703080406090203030d0b09100b09010f05040306090b1009112505060115090902 78
    0x360210795811000761204049041c4640000380380600340142608444034548492080d107005502039514026174900301e0a010b800d081e01c42c2109030060703004000600c00c82d100c0001e20021a41e00810041e0b540e40040000e0000f4016959070700b10840c54111240248400000c640d12094050107180e4941443d24040140070803103220000040ba10100c509030048000300107a40806c80c040741c03895540351208140c50708681c003403003100021035504c58051055045c0004090b00402e016a074944180c10540c541060600901c500101042403181c000f07800c10103583c100307410543c0d003e000c032512001c03070041c50406450039401c00c82c001c254900000d00110703000895a41102e0b80400240e2500f0ba4510045448440440003441880f508000c0000040d515204800c41c680c00307403000e200d0341c2c100880316540e280d2450344103280060070003207011350b54560a000c80d00030400007150300d0403128050780c0343c01c0e0b00c14a0784030107003040c0980000060f80340100800a40301084a40d2090403558032601c1c01c900700d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 18230474 1250 18229224 18229229
    0x503010302100804020301090203120d060602030906040b070201170f01090b01030c08060f0d02060706020301090c090303050901030c09090c0207090509070608010506070302120a020102090a0509010e0a0506040f022101080106 98
    0x152218404a1283c0c019034a071030300203001400100b1580a59004030340307001d210101e1500c060344002610440c01c1100d10070741300076120720300c0914544250400041c500740154044c0c1604040001034504c110782c05501d4184940e40400d40e05509031418108a80811600344152000181080000c0c003040d8464032411800403003c0e200c441564645500740915000e41c14403954020441040e01e601580d54407000d460b0240c412080944c0e6907040c10f05040556550804c0c4000380849140309000290b085025150754450030b113030001c0c04070180e000441d666003050b03100c004003a140a04074085581d010911b0b41c2030703507039030b01c02440262a034060141c0c2d511031314810070000030400d0005011510b40200180b0546000f4411540490400181c0b211907512050704900981e6001403680c4181c2004510300700142000c461781102580750503001404100c000301243c41150760303080001c816554580c802064912072540443d1a00e440d03041c40380d00000c2d0220b0000004400500004400105025100c203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 18231724 1250 18230474 18230479
    0x30b0301050109092301230a06080304050a0e070302070c08030c010b09091005150402030f010e0709030b0601030b0a1e05010908030304050a0f0302030403120816030c09050111010f0f050103120503010302 89
    0x3510300070b0b40540d4820414154144055520f98003060b244440708a8082c1f1048605e094800580c07d00e4015102250881c0d0700c419280d0f0410310082085607a246150001c881d41410002090b558001e07044009103c2c5c0070f0700400c011409c143c0800d8401e0000007030401c07000060003c125003c030081c20045420403c44091940340d05c40200d2480140d000d41000ea0800c5034107089a06006070000010160b070000ca900e07650034803400700108100680c0e20543c0d0340090b014203241c80764a0460300c60540c0c62000074251030606031165803141c41c94490502d07440050950300e802400c2c0301d28041d5103e44405413885914000b0b4018503011039003030b10210480380207540c00401004001410ba80e245031840310000d05405500060100202241d0f8031401c3d518800125681c02c2041e00d0250b10f4400113142c1c03040c42400301494030003031100e05038010400d181a181e0074204031080c80034130000b80c0d000d00b10b44251580014242100041021061303000541170702d21940006030003070700041c0100c596000922000c4d5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 18232974 1250 18231724 18231743
    0x109020a1202010318050604020102060f070206060d031e030203010602010c09080c04050402060d050103080301060f02010b01090b130f0b07020a080a0b07050310030203150f010611060c0309010b030d030b030105010909 95
    0x4101c0d4109001d4a2600c1810003060000c2200d10100b92405212815070341a04010300300011581e051080ca5031215070705c02c580c002030822060096460000504090248404401c40310505002d413501f11150003005903441d0b01402140001000382d0400c0c4104005903091064101080e40218032800603602c0d184d0060800c6002c420070803001d064098803c0c1c0e0000d200304905468101180100c0340a1070207403620f15079139490048018005c0d80a80032a01c02c40e4906a03000e685603070b001c1c810804584085a0700e6888011980c1000300e29451540800910519480001404010034001d002824005c584864449558070760103510340c4082d0400500c6141d503640000d020038062000b850300034401d040000c1d1160385a60200346048030007a101d080b40140b010400c00503292908003503000d00681d1420740441d03101031060030313a540c2010f00100c011060110000342007410940c000035103080010300310f402c040001d11b030150041407200240d5000b035007000000f040c55521406510ba800b54482d000e81d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 18234224 1250 18232974 18232979
    0xd0507020d0605060a120609050706030e030304030819020a0207030213050c030a091a07080f0603120405150702030a0b090105091b01050d060513020904060e0403021c1704030c030806030109020a 85
    0x100020140240341e03540c45181c0783d0340411400c03000c01c10344e001103105007c0050300300c81a0410a15040b15a48810101340c1407000b44242404048203a0350000c0c1d00d82081e000988501d0000400040c0c0f101170031805031b101160000d00280c0c006414002c4a000342c0380170507194885110441942d004a8107044040c80c1000480e21110059024405590160306c824402201911040b074498805460b8480001e011030144000894401c00707150304001d04038028280c0301c10b08620100d2500440c890180710f1484505202603040d8018120b54001d031f401020f0b01c03002804c07031402c1c40e84603406491100c010340c03800340010b84103100002c95140c00c10715600d000180d003181a0044070668000002d580030140c6825002450b62901244044045141100982c1b5000300c4410f01c8200d031400e61041103117040348028440440d401040d00146200380340c1c801c00302c18220f0202591815020f03030700c150f0f8140d2000200010316030321205247d6140c0c03003559951880c5d00c4007000c140c00d841407540d01951008841a04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 18235474 1250 18234224 18234233
    0x7050313050703051209030d0e09012d0b070b090706020a08090619030c14070803010b0f0c060108060f0f1e09010b09090c04050601020a03050706021602090a0e0d0507020d 75
    0x10806101d22580444054540340c1e40c0b110300380039412900a5042d0800b003444036a03454103001c208120303506450500c1e04900c03008000b910b504410310130600e10000000048104503840b01c06008200381c40041803003a240c1d141c0901405901100e02640d0b500003280104621103004150301c0c0885445a005040b07414403600c0b00c045640c041040d60f6400407041010500409084041022504954800040e540700310640500305024036008006038032010441480004d440200350703030540c3e850000361a10781d07190081c1d0314154460003000b4840c910079100000f030078082c0000d120b8828015110f590300d0036180d0b01320458103183c00b90303500848204004001c03050702c16110841a4081c21003800400c2030f51048000c41c08003003054078900010f4120000c4030700c6a04080c00b0740da030800d000f88020544441c90740c400502c24022070b040100000d8001441c45210010902100a040d03002030a01e9490300b4680c02e15801407002c015003003418010f4081c014070f101d01603130544011507000303031440008055503581d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 18236724 1250 18235474 18235501
    0xf0402040b1f030603030207080106030b010b090301020702030a050309040f090302030a031a0d0b0406050903040501080114060717120105030d050a0e1503010807030308010503070302010c0609030c140703020406090203070503 98
    0x5406400400342000e00103404070a20300c501c2e031402551400601103045042c001e0801080c1e4000881c2c0b0303810f203003003040001e42000115044402101d403503034440c0c1c441d50000e4007a1044c03040182d4144070f141001c006100d0040018651010100c40030032242e4051405a03055a22010380540941c10500c12507440c28000d811407981c0c02c0c500b527400060180604002a141c150580e0140c60102102d000c00c020000e00d40b06194124201e4402941014034000c002416090140201588000c000740300d04035584442c0f0646400d190300a07440c40b0b105000c121944102c0c1c0001665041491030000000750a00300850340d000a4401d540d601131030103020074010388403040c14800c420342112081541c5403240c400030010f0f6020b06160300240032190318604000700001010b0304124130a404c003500800050b0b070095800c107207803940401d01083c0003920b0300341954044001700000d0020300b80e10005c2451248045202400d0782e00c201c1d003c000301500c401140d000c0303000489001001c0340c1c00b000410280300d000c10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 18237974 1250 18236724 18236741
    0xf0103020d060306020c070303200c010f0201020c0102030c030402010f080411190807080f070e01120b070e0d061b030519020903030403051c11030c10020a030609140603060601080f040204 82
    0x3001103002e907a660b480301c0803a4030698a0f0005508499814002c15030321142d02c0078120816200300010000d2001d007151201804d92030f00b4140000c5502900030300707000790155011010f588008544038a00406060344562007103c0481c0002c19581c146030841c1d004815030f07402141c0004030240a1040001070020409181d514650302540310b130030006004104015801c02fa06441d00500140914030500700c0c1713400340d10741104103c2c00300d160052161024442034607205c1030700003160007600c0d100c005003a622080046089601b00201a104c002030001c02d810070042c003158210304100107580742d50200c0488a0a980030b00301c24000341c000003c01d40d840d40241038548401030a1340d1600396250b803014a040e6510101003805a5402103c0b0440c0390803480c907240d554681c60142d481c04c91042d07100d548848241303a100500c141d0208005809600c0b07540140050480c15038200800d040010380302c0141303441118094407070f1003440d002130380e503500c584841801410101040f44060b140c0d942000060b1069a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 18239224 1250 18237974 18237997
    0x405070b0309030705030d06030614010b070b0705070b1602060106020304060c02130b03061e060103020c030d270f140a0203070605030c0906030118050105120a030c020a03020d0b01060905010e0f010302 88
    0x61143c0c5005c41c00500041450159660000940c2455450107000f03448410440320b003100ea60380010001881c0080884e50140c0e40141e104d000303540c0d040301c19140c60051480107400c540f10a410807000e20000346002e91180f4250b0212030ba01d0ba80c1d0802240d40e80304501410f80000d0900906500608040d04043d20380035030000040f5200f1b510b0310200b0b00d0280300701c40c10b0005003050301c108204010301d05103198101000380380941c070700b070380086040d95248907240034415802da80e1050240384030708100ea00c1d20300795104008901d1301c12039424401201800c0c4801070300c001800508000c0b14030400121241129800703005440124944101a907854000401350384851204000c0c41c00f0030745d111001140a80303071500036080c2c030800b41103e0404903081608482e00030461a002051222000100865803da051808080020791840883c44050250303100079000020802c5080401c800d000c802816209255100e98000382d03614011282d060050309041d400035900c07601c0c502e2030b5100b60000c00c004000c0703 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 18240474 1250 18239224 18239227
    0x2180105031008160303030c09030b0f0414010606030f0501090504020109060503070302090a03080703020c030604080d110403050a06020c0607050406081503031b0606011407050303060405070c050303010609030308010801050405070b030903 104
    0x482c18258100010305813828100d41003035a003401059054842c09a5800306403514401403402c550700d403030038011b01410182c103024407040000d0410a4244080da0310300075440083c1700d415503a80024001c3c21a100100700014103000c00400d1095252003143d2150b034059540c1c0400c0c2d450300c041640d0980c409004d4008243d001c0014280d5074503403422880c0103501c19050b180e540d100d80e080007400c1c01e2641c0c0d1a54170036006942400003245842040c0ca051b0041c080002034a4007000b011440d40e480381d03a10003007040c010240303a40d05100d1150f0203451100023000a461007580e500390100c0d194400c6c0d01400000c26000800f09218550241140001640c0607048a207060702c184140483c010362105240e801e0750164041108550780051902c0f000d110046045040640e280d45503030302e07400000c11640c0560740c0d400029640a200307411b064012078001054075074a503104c0d480241701c411503020580c08110f094000151040c0148a1a44500d8000028103510f03810100c003070620360300140100100b80300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 18241724 1250 18240474 18240479
    0x30402012f0c1003020a0815030102090301140a06060f0f0c02120604060f06090b0d11010c0b130611090105031506040b040609051201020703020303040f0201090f09050613021801050310 81
    0x1c0c09000d0410202454024842d98800c201006000d201e0380e210b02e002c02d4010b01070404200c0c0c1052031950080f25400400d0440c9865034042030090060440766503040d0f0030081d80020040d0344070401c50041240c3c0c0802c2c446d41d5240d12007a0b4500c00130080c0d03900024608004421701030304c01c401500071988010540050b071600d800c84145400300a0301d05a031072a42e1500c0900c0101c042c2e1103244010940f898090080301183c81c001107441c41d8580b0050003c80107a00841030b26131082145422803903001e50f404a090800030240c0a800446050032902035182100d0003440040341026110aa80305940b421328595541912443c0c0e0907104000d190402c00038400801e10b401400003800107070a155441c0700b040c915180801c403009a480020800c664410018400465404811a50b00c2a081022002054030f07520040b103004200e58410130400f0040240411104225000a40201d108a40c0c880341001c184411030100c1c495080a082c42c298003038111042940a032020710360144c520160400843d5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 18242974 1250 18241724 18241787
    0x3030403060603061a0102010509030a11070504090302030c0601050405060d02060c0c0402031602210304200d140610140d020f0a0f0303020d02060f01060309050c1e0f09090303040201 80
    0x2d42a0304112500f0703840d21203200c00000e8240b101010700d0802d00c000e06c443d0030b19020040d120b20404000104200203c0321240303500a04018030360082c48081c01c200304550144c24029202e82003035030190018000e0200024030f80c030306801800e0062000404c4420325215680c2000183e07400715881c07003c2c50042289058043d40c9520281d4401c807860490725841000e00c3e82c00a041c061101008081d0706068075803503d442d81100b00384da07845580901f040c9100d000310020511800481003607540e00040d840429000c1190b8070102d40840c09003031040782c0e19500c400b41001c403150b60a0144014602c603e2045040f503140407070700f0704459030015107a03046228900340490300b441d199400100001c9640c620400426170b0401ca4044e40c280b0505c040c0c007450424600000002c0410301c50300313040688400c600420b008052000c044c400000510348104200305c4201c0046050b1910b054510404002d072820402d814000e140303034460350140001d185543d55660040d10511a1085c0c44401c0c607011100c0c100b03144 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 18244224 1250 18242974 18242981
    0x1b0d0606090e150c19090f030606030c05100210020d0902120a0201080108060f0103061a120c09010605041a030403050408070603050405191a280605030f01090807030302090303040306 80
    0x1800c0014010a040103420610740c079004001c0c1c040c0d0503051072401000303078200644090324841170022070417482c90807440108072003d0f025900194030120925500008001c202c0d4004021a0320a5014119050faa8420096104201103159001da0001c2d2003000d906030080c1c0c0240104054150001134111042c1c011a804100341c0d442d8199540c409110300c400d56030400031a80c010314001004098603d09031315481803008061000a1629884140a80d5100c501201d45141c50102070040e84070188220003607680c48d1100c1c7c403441c3c01542e0920001c13a02a1080049505880b04210341c640130790301410030054141e00040c401d9080090511001c1001c040501c070640040860303560110352801d060070a2400e013a01e0b44100003103210700300380903000504406948000c0b2034042d18078610a555400b96a80000e20100440842200c480c000d80086030b07042e400750095410075070807600c0c0d4130f00300d600b06401c030b0b940780c400500314040038041030b00000e02c00e400912440700050306503402c0940d02d507200b03410b8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 18245474 1250 18244224 18244229
    0x5010206270106031406060301020403020d0b0411090406090303050601020706020307081e0a02030c0705040209090a0b0310050a06030b0c18091005100e0108100e1f080a0b0103030809010e1b0d0606 86
    0x1244032017030107030303540d08008071038025100700c00840c81d00d895a4000794000f0407805004000400c40d9000a0138007882400302252024090315240d400e20301890a00002c207043e42089002c6807901c00455042d510002c0c04a0544059800841c90a512620380c1195034000c17817001d410070030b40001c01011041a00028000301035454008640b40c0006080690402c44203810090040e8418400800346940700d140b110b070020798101e030000c0d244240a003c28100403281460642c224280801d00c00b18001a51008081720b00400c44110035032110541e48006110b8815800b80c6880e00c1c01c0000c115107880b80d09250400c00740e000400c0000c1e51000030560221145000b10042082610070600c95600541c065034050b81c01c042400e52941007140c1800302c01006002d90150381c40c100440090074034103004010282000b482120000942e41c0780c9084912000d00040300018902804100101814054100d4603980c000c00f40000001080104800074000c000d11940540301c9039101000c03612034800c0102 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 18246724 1250 18245474 18245483
    0x9050d2d091701090507030303050901090f11030d03050405031b0708010509070f0b0a08010e060103060b03090601051503010f03030f03140703050702250b070204110a02030702030c01090501020627010603 89
    0x54180c5842e030669003490040701084020b90628460000050001c55200c0030380e540740c00c0004050712002d2019005007032054005000e40320410100043c800c44d03511011019100318110307204048110404c8061300d00641d0300405560084c8134400000051000c00074031012998111070341345649602c12400c2d201c1c02d9440041c26000b9880030f02400f4000c10180d0082d00a20703a00d54500810804000c01030201442281d444076641004aa00c0e60f102e41c200000030400f0014403604da01703104030003585850b02031160500c18100d54074403135a10a64181a80d040b034100d1203544558501d5918282d403c2e408902002080603a52306000190b01c0005d070701d0760b004001665000546103004400a4600743c1010041c080c00c10100386403000d07a128a01c015400e407005401455121403203480071401912a404c56030b03020350404910309110650000c05064418003c404499400614000540c1d1019980c0203180c0140c0100d40001c1d160002821a0502103d0f8a602030110145080c061400c4914a03081100c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 18247974 1250 18246724 18246737
    0x50607030501050312030603210904020f041503060f090903200d0809030c101a09011d010509010b040e0601090317070507150c020d08160809031009050d2d 68
    0xf00c01d06003000107010000409000503e18141540020b5842691000307204014290115664200012400382c5880481c09401951101d1013074a961000e41c1140c024a413054002d018082540d51207402180c0c00c0f0f03030f5050003088660b8241414a00546003e12040c0c003071000d00900030a81c94096504036502c100864081c00a410a040c80200448006003000803250300520451907001d8002c1a14114418bc0d543c002540031207a4074880807141103401c3d9540c1c080043c0000294040192600009104a911000b15580c0c1c0740c604011084000307003d00304043c0c505000a02c049034110700f003030780c1100c414106000c825559588400626a0b20b80d1220038142c80416804100641001144080c141c41909182078120a0100800016208001a10038110521080c051281c06022071b550407664500ca00700c4da61040c1404034090b808a11020300070f115001d8944003d640d60302c01c03458095440000380c550742000c50422a181c2049100006041c44940c506029540c81c2c80240000103a840d16101c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 18249224 1250 18247974 18247979
    0xb0f030a0b0405070f03180f050607120608030304030c0615080c12010207020f1009030501020c01020301030311030306030c010e030c0301090605040605071404050904060e01180605060102030412060203040f050607030501 96
    0x80c4191200560814001da00b040103205010390000074041103042c003441d0004441d40c101c40f44806408080c04003500c414100a521000e201c008070340c0d2486003802e5111100f050154000b01c104544003840b81000a070001e101150000e44200321a000c5c40d802140003240c4040f0845100ca090205980002840d500240c0d5400c858100144191040f01d4001d000310309103541500441d20201418039107910070100b25031914840381c02503c4900c0510f400c00300071034603a0710141c031182c000e500038003064010600e4078070700d0015220004100d034810030025004d44012044c610042d00c05240780d81d1000e81c14011058582c030b09440034411005940e010365800306080c1818140784044440141001f000c008864021300b000304000001c80d012100300341e4401580d541c2e1401d00000400b480c4140600c20750a10000d2012720b07001c05245030150b402941e0821a40d21541c0040ea9644924801c420521038410018004260903501859105015a00d000d41c1c0520b1b643c0e44505141040781e150001c00c2c0e07260010b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 18250474 1250 18249224 18249241
    0xd05060109031b0306050601030603050a020904080f030a1a060a0f0806010210020c0601050f0301050c19030917120c0310140a0905010b0415031811040605060c0f0f010605010c08130b0f03 82
    0x1b480d41000007801c04011050840e11602e440302e03415a0040c0c05190404045803c110781c00d800ca80d008100300300070b5500c034100341c861a0094030391a682c3c51910302060350403c0c0c840c60600c04984040a25454000d0189080036040d6040c0350300514050550142e020003400d001c03100c0c0014500c040381580502081e6040c03404100b98030228410b9075010368505420404950710400031200651300b184441c9010001264045016012070740c0020400d074680c50782c0310088400d60010340550b5100381da41c1a1141e665214000840c0402c503140038010300046001c000e124002ca00c0e5000450001d001c5400c9180c0b102124004c3c3c610a0384000d0101700e0010781004012a0000d081c00d80d59003900d018010410000e000c41c140704599400a4081050001050f95a66035623020300010240900f6144e29903c400c0c49203502c8004075024a0b40e1801750383c40001216406208080075a5016196001c1140d04e50b00d500305150490203061107a0501403e000c2204441e0202030490551150340744e03952494503078030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 18251724 1250 18250474 18250481
    0x8010c02010510050121090f0c03020f010c0b070f02070e0c0912070b0f0c0319022d10200f0406032702190504020d09060501060c080d05060109031b0306 67
    0x118102c44030034240c00380306070fa1b4016120b01156008007100b4540b816091a010000c0c5a044001460010803444080c10496406044030841c0d001b110b180c07440d080c14100650b806441000010000504800026000c50160300364a203584024030444030b02e42d0325440201d1900006a90f903c92a0002040159a6140454500070000c154a010b80780c09807402134000c4560140d805409003864000c14064200141041035865146c2c0311003100c5c882d603100042c06521002950900e41c40410003410b89a140b52801c070400b000b00c24160001c00b02668240b0300c440041001d0141084200c0e10610803410280c2c104014221044010002581e00da1500302e01408840c502d078504010b40c0110404507011040110003460304a4050b58801c0c410b4442600341d02c0350700b00f5904804ea00078800301e0025400d0301144e005940b01c0e48510410070460b622120305580050000c4030080069500704201030080318030350031a40e00183c043c100040459100d0b40c0d00400b1040c441041e0301231602445080050009501 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 18252974 1250 18251724 18251731
    0xd05160b04050c0906030703051c030b03010903080711010b010503010506030a060812031006080105031009060b04090605061005040b03070528050c0c040b0d0b10030b0c0a0f0305150405040c0803030108010c020105 93
    0x1401402d459140d270f5922500c490b0301002030b80e60054004100d515490090700250303682e0000800800400c0907c0c50302610b00c00003525070394001a030154000c07040c207005119030707100b9803030503112241142e2800701040502d500080c0b00c00c000984a080c002020340c403c02040280f0701c2c030413000c035480349042d04800c041180130794030850402c1100401006140c80115100e002d40d852000041242001800c0c468082c0c1311a00d84079401519001c5010244049a4800d80c0141c10031510382d15034083c040300449050040b40a000161101000032596960188009149810b80b10b1010140c110100902d8860f80005510303103404248000399400c1406005d05c54596100c90440301003140d1203032100851484104210f000309000c0041020440140f103942c00000199032044c01007110b4507144034200c0440d0068001c0bc4040f9120a070a012440c0c0a4024148213000300031a440484440b0b00400c0040c0002400c01d940340e020f043e89c0800c0b2072001380001e40c0a01300060000c01c0c50307203152000a08445006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 18254224 1250 18252974 18252979
    0xc01050705041202010c1b06050a020114091207060b09070302030603160303080105150c030a0c0b100b071101030207020409141501050a090e070801060e0a050f090d05160b04050c0906 80
    0x80100348180b100c41d0b106a82080c1c4c0a02e84060707425220314211100380001e003c0194000244040046d019034005c0081840ca80d40e94024803458641008030583c81340c007a110960713945c0145185803000c500d03035030103404c4090082da0081070020003c1c000c101003c41c20b0762403000003500002005050b0a00300b084001901c1407180044880340b460310001c21401060040317900c21041d032502040a440d48070140c034001481c000940c3d42e90700d0300d4100034000d010000c000f02e0721280383c1070000382c0018072644582c00315400301904a20705001c0307540301910481a92042418568207000f0600561035078420300031a50b00c5290446d04880074218144c6c5002002e1005200860380c0b040180841d0315014003003001c98514840108035035800d118541d042c81c0c8107030480748403586000000182c2c0a80001da01c2c0c0209244201040280c0b02d4a204504807442100c5001c0d4030ba1000d010038025030702c10f1b0020074140c07600b8a140030f13220f40e03140da0ba9002d06006480648030365000800150301c3d403030540401078004204 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 18255474 1250 18254224 18254227
    0x307030e030a02030a03030203090102070c0803120108030c030d02070201031103100906090b010e12071203091a040b0702010c05070512010204030501050106080403121a04090302060f060a06051e0c0a03050c01050705 94
    0x243c1d0300190761480400c000404041d00030010541e050000d4065a400660008180703140c96101c0c0708032035581d00040f0f00c1c2c50701200084000a1100c002100300c4150058843c01303180b03002d0000c1e591720040d502600003281019a195120116401000c0c042d50217092401c12041e8134914000c03004068039103039000903141d986030850140950780c018000c500f000e030042d544030541002c030305115401c141c51603000254944240c0c40c0c9604060b0310007030b03410944904030300f241c990505030307407841c0d003140128014400c4d40304040203c035015602903020845520710840464203000d8a41022480d000d00030449111540e4011800b401002001c0c001c0c01e025000c980f800002c07a2802d614000c105119040d421880789590b400e00600060200000c22048d43d0041c1051112040500c2c00070365400c0d085850a4a621525000c610700345000144172013107482aaa8240c01d0500102003101e21802004d0101000a0200700903005000203101038150640a80c8030103442c4e009001409007540c200418000c100f100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 18256724 1250 18255474 18255493
    0xc020610081204060804020a2c010905010f0b07060e120703020c040902150c0304050301110c1c05030c0f07050708030304020a0e060d030c020402090405160906180905040f060207050307030e03 84
    0x1800d0781610111380203483d000c005600ca5001258030441c09410070801071020481d00803070409005404a0030408400c6c1d030341d4079a030307079080c60000319482800b41c810f05100c46202005100149406090070034054038002804040b100d039400d282c02580742c04824614800b0409a05042d0188104144924103403001c2c031450843e94006034460920280045412001080c1e80e01c002800f00140c0f0050300c8d01400801c0740c0700ca2080500c095400004840c020b92081da129100d10881e0506c02154103621620746a0454854106c40c0915400c9603521501c101800c0c03000c0c50110340c00300120300003003644802540c1e40742083e005001c0005c9054001050b503402d0402840419110a0f40d039020b2117800d890640c988a015100040180c4680e0030742e550b019042c07000b0f010382081003504054154500d0f4584403140b03a40c80314181c03801c080a4420713100d03006901c101004150700680006034800d2080303807540240d0b901ca581300300c2240c0090384103460a40c07001c90a00d04150b017120781420304010481c010810000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 18257974 1250 18256724 18256753
    0x4111906090b0405130e0f0102180f010507030c03030b0126010602011409030d0506061c05010e01050409050a0b0903040b03011502160e0a0914010606050c010b0a03020a060f09090c02061008 83
    0x148410100190141e03184100803100c0414041147d07200a07050095590724851814950034413107040e0214481da807094101152907000d0b40c01c580c4055455110300d0361003801c03500c00754024004000a1410300000035148000c40ba45584401707041c07a60300c54031426950414400a01b1034102c0300f507000c002e1040005102da004000002c3c0c2e00384441318040403a080e9034400c041001c60203008480f0020705c9550301c40712060398260300200e059410360800d0f019a0b0b0b90b079800b080b040d10001500036000d904232030640000304c2c2100d000c1c9944011003000b00e901e0180e540d039081c0c0c0b1940c42640303d8601042c07002e9011703440c1541400300e0300e50090149141040c040c10020450060b20011b090055119600d46e4680200804881008900c0b400034008000a80d9140c4c0d003d041d42e070040ba8411100e51230f00c1420211480d140c1219000c3e00d4018009070121810720708296900c91803040c6440c00c2c0448140c00103010501c070300540b81d401e14241e006d4078003401d0440d9003028403141600f00040640041c0090342a00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 18259224 1250 18257974 18257989
    0x90f0f031606060b0c03070b0a0501050d0b0c040b03041209050a0e0c030703090206130317130b0a050f0406090509070804050d180b030901060e010b12040b04111906090b0405 76
    0x101d441d4400005038a050b807501000801c00707a402055100d5000c05c020045040100c00b401d00706001d686516016a218442c9104035582401515444002100e00d100402d000503900e41c4c0c8890062241c2c0d1909803121404403031038000310340c100e40e00a0a42022002070754002c1c001d40081c4020b4500000c05e070b003410718201500000820a060b00034003c0f000400e00b503ca0340002582540103005561b44e643c0046150704420660301050740d01e641e00403108510320404104441e0007403641e0044080940c2418445031240d8814945042045000d1011503c100c0c2c100000703000402040d1200001a4a81030910001a00090801003070040035010440450004030394041d004042e45003000e80d4600c0b01b10a000c0c0c120464000c0300015001104110102005500660982c0d078244089001a03988071007031a514800d00d10005134800311b4801040018682c2268550414464011154844e03604d0300401c030b4620450462641a01c4098001c102c1c5503003000f6140c001e004650f8800386040d0030007000c901300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 18260474 1250 18259224 18259237
    0x60402070201230301062309010c020d06060e0a0b0f090103060c0c06020705031308030f040e0a020d020a020d030b0402070201020c0f120601080106140f0f01030e0309030d08090f0f03 80
    0x15a0006105011688664094032507a00c500030148402d42c51800110569002402100c010031500116903200940411554441200e40c001c618a00a503007801168401c11108007240c001c42d10152480001f2520b00a20026001500d208080d601c1d0084e01c1005442203051514041e8141c5890480c0d945c131101c0e40107064a42103003000c988407800d580212224008060054003991021452108002000c001485c0c5181d5a00418481e6511040099103e2203080040444039400300410000b65040344202c56015188000050074003100c81d1180069a00c240c0390b54006130000c02c020440940c151091554011085d03404508003e00ea0740003039911791130340d01000d00c00c0c65481d8841c600d50f650b6120519108250030107903001965208941c0340600081e00401130740c003031031100b00e50305424205110f500c00503004014021001c2d01c0c400541c01800c1100415405010801c428212078500f0024014818403e5481d404c60b0328081092a09281c0450b41060250704460750000a41d08000180c501c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 18261724 1250 18260474 18260479
    0x9041101090b030403121d01020a05070606140a1701061502010b01090b0c100203151008010e07020d200705040204080c0f040207030f050d020408010504080301170d021902040b060304060213091406 86
    0x55412140d40e0300031f0501c3c0c0c013402c0f0440030340c00011001070072030b0300030301a0a10900c5050144401a111848011100e030705404090300034914240c01c005800d03040401c075944a401400002e07a0a4844880c000402c07041ea46c00c0300580e45402c211049941d201c0a43e130014906160b20b541010240340c0c6103600d07900c2032085141e840d500440414401c68640d0221525064024a2108284490751380584050002d10580030701c00b0328440019501d0340049080818042c1d15540c01141c0c1100f005400041a00810300305010b2068000201e801e80301c6200520160030400010f141b1322181404104e000501c5400f0749024900601c40140000e0f0800807a403507076415401c202c1c0d241ea1410b07808500038091984840c000d5070034107042c4400d010114008605840406031840300c2c500984041640d0751115a404c000141c1c00480e40307074100e42e0030900c44110148002c0003c100c0402e54030000d5402c1c1c00a4406551403580041c078001208800203030803000700b0541c88188810061a1900701d00c43d03c00030603e170b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 18262974 1250 18261724 18261731
    0x11010608030d15051206070801080a08040501080c07050a03020606040b03010e030a08130b040c0302100512190207080301090c020d020f06060607020f060304060b01020705120a02060a020c09041101090b03040312 92
    0x484107591200074001130035003d0070150200c0c0369401210340d2100b003a500c10000c200810b0001c00d0140d0085030104006400815882c0341a207490300458455000500345e00104000744115000078400f8004a0030b424040d07401044c180c180389003000100e0f00c06c0044140700b40e240400700d0a4014012066449500f040d081040080e501e10694070310b50010108002e0900401204200802c0004121201035030300039114031001c41c2c180c41c82035555124060700e90740582c499100207041141c40c0d00d1f000d41d44036a83d10300035082031030907911101203070020b0300180d50701500c49101500481e030400c079524000400b8030042410311003010110f51030328000b4240700d010780340000740c020075516204d60515580740041c1c8101d81d0ba26241c10540000c1c0701051480d40140940007002946140c40701c1140303c0504a44043d080d207805682c20003c680e40403104607425401100e1159140e503640103019880b6600401c01e65a10b413800c140010a05c410507000a0705454048c030038000843da22041e40c4c10039030764900001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 18264224 1250 18262974 18262991
    0x1091d090106030c12060606031e0506010e0d061407020102040f060e0301110304060b040506060a0504050d0212060f190212060d030201060305060c07050105090601080c0105070303060503031201030311010608030d 93
    0x39025002a0700050240d0811082c0007400a200c00d030301c0c04c1c589004c0c040030007020391240d034101c003603070304180b500398007141350003c841140304442d8801d0340c214005051490032810850b020a0f07100c008444240c648a60f0b03020b454000c4100d9003007055010005200840c5082e0070101c0010569000340228010000b4031403c02c01d098900750b10101540c0540d01109460785010f1400310080e082500e039040c0114104800320342c43e400d094081d608443c04640301d07142010300b00300c18402141c100c2d04c826640029180e042c00007001c0144141030043c64011a2009149000100d040042141c6810341228910410255555400400005402040c04c8501152682850400b00d000d423085801c0a041800746005008800302d08000030b00e4a54400e90007880103554140b100d9484103002d10610440e500110445843d962085000749591132203400c001a10030303241c0c4003286c41d5400c242c408501c824003440041c02895001003401003aa100c0354004d001f00c0341030401203512405844106194940c840e041c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 18265474 1250 18264224 18264241
    0x150403050c010f0e0d020a150903031e05040203150403090e18010f0204050a0503070308030103060e0f150402011e0c03080a110304051501080703030801050906060f1206030c01091d 79
    0x8440030325100324000d01c03149101c0f0740360100601003c106450988aaa01d1826206001007040109290890103081e5000e6030002d402014084043c021410142d0b01c1c14070300340070000069229800c9240543c001014030f403a10506d0300e007480c00c41c2c2d58042501743c0c89c01c02c800640d10100103c02c2c1c45038084104000d407503541111040322140d448140c455401c042440d800090aa4050030480d0800c844905025550b00180b64035440c0d5400081c1c501c60342040188007203202c0e0303003002d91103495480444904400c42450b0382d04240c8a0a454020844000180b0095688c800310002c03204200d9003200d41107040d0004c000e01550400c280040500c14120001444520f1650080e0b082d01450500703c1d40d00d24041c50010348a110050082d190903a041001095030400003c1c2070051f268551509806a400c0108015440800410302c2d540032104100d040980030b0341d000584000030251810f1106428807030105418159000310042c1001b941000400000045001c00141e00214007950581500d03418074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 18266724 1250 18265474 18265477
    0xf0a050f0c03070b22050304050418080406020d0314010608041202010605120303010305010c08010807090b060d060306021801021c0315030203060708040303050a090305090402090310150905010902070515040305 92
    0x615032400040b8141d42800106410507228002078100b0035100340407a003917074580b1120307a00702400c04d03881440b0900041c1455440308032801415107003000007803100d9036443c0059000d0342110300180c03ca00d1326526003079050300800f400c04113919021000b035814010001c1c04407600034405400743c500940010100c50003036129034050540902005034a82035406603941d01d5000313110403600303580b8040e6005004d0384030380a51410b0303c00c08800b070141d10386401805400b0b0190b04040c240c0c0a0070800c0441640311007445050b000f1445080c0242c2c40b84812200d03a8111000265554195001010f207a5841c00d01140700120034011410001038498031164140d804c1d11250308025018030400090100c5d150300508007a100c1d03842568280304c6542d40d079030948284e03450804020017080041c00341421900e4a07401400d070044c0c029040304d000340e24212a110640c0c0382084d644000d1024800e0034031901040c2e002d210302501c90f2050a6281c082142e540d180d4414602c551040080e100c1c030301103001c1510800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 18267974 1250 18266724 18266737
    0x5010c1118090a0308060901030f030809010608010612060b0d23010f050103050c090a0b010c020904050f0a060b04060503150103020d080408030f091002060402090a0c091a0306010906050f0a050f 85
    0x1074440c0036900c1c2040105a80d00704603c81039001c0742000000540d58035200840f581a65030001400c01c081c801d17580c003900c0000c400361040c0402e54a6902c0407807410024880d801c0140851020044c1c003030724600b008800c4461801c90a805200c181c0c543c0f0001c00c2c1c011400310852003102701125554405010154010081440c6074214035040000000500c0030024680492408c121403104a54503982031a00443e0110b4142d5404038000440031000351400d01001580b00740224259041c58415011460800034020402c803005940c49042c0740d203505045c071885018040a500030201d00c400d14281048601d03052100a12a9061a80e0300c010004800207407030040002d4811a92250f100c00c01088858000000584c0942d90035606038102e10300c0001d10b2401a07401030050009a12354885807809000516440707010321855400008403020091300c1c071086903105080b66038480c00d01000052101c24168000410000c00b4025212080007403030071601220103905005a481035441d040208901401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 18269224 1250 18267974 18268009
    0x609010617011401110303010b0901080f090a110112090c0602241515040306020d0f050601050a03090c0503070b0705061614030603100906050601020607020d05040909050a02040507110c0a05010c11 86
    0x1f1000060b10150000074105010302600e86141c2980d80b184100c8220b04200c07805002d5034001c02c3d0392004950351008070344041e8018945000300b40c2d600310b01c041c25107a42c40c3d001c6980b403080000c200440ca505016901d60001e800c042c00940503118600f046900b540644541010401e41d4118002c036501d0380c507055010000e41d040c654a8950300d040102c000d4100d44c0039600d00724280305280648505910526119102c16181d040c200350301000c00701d0060810000844a81c804400f001c1342c6581d00b00000c00040501c00001541c40dc0c144c0b0341541440400f42c80813100d0350140382000d8070b450b081101091384103140300c0c041d5100e94036100003c0c9003d0905d10043c030020324140010040c020540c1003584500d1082e021140c0d41c1e201c5d50b20890f614007003004141c0000c0e00c140300170701c01322a6580000141e580500d0440b01c8444a075000201150001c0e9036000c045101c0c0407411203c078409100200c00481d0407500c41e45180c2c0781c01c00103401e4440a040040156008000b07c2c00c9a171303143e4103800c4074061384 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 18270474 1250 18269224 18269227
    0x7051203120106020d1722060b0301020301121e0b06060706020909010909051c05031302030709050702030702010212040e010b0906070c0b040911040f03140f1506090106170114011103 80
    0x40c2d01003c1d4603070701c80d0780303101e00080e20200d5184d8040300b945602c1b0f40640350540300c0c048032050014820603000d4008008884a40d12410421030580d8240055806080c064228184964203440c1840005000403d4040340000105200000c0350600303d005d5030150701551a1646c0b16107600c0c086000384070320143d00382e0009142001144250080c7c0c0134811040c403c0c41260321000564454240b0b030018030340c0c01c07400140f080002030306c070016440d54541da261001c0c3c100c80e241600e0b40e81d58030607140200c4010b801031380301280410642d0790412103190584103a520191600e07050001c000f41c1740505008003807071400001104202c81d00d0b9a82141c1c40700d034100c010000203e4941d081800c0d59030052040c54500360400340c8807500404038000700c8040300c0c0011100ba0140c0e10f103a41c0d281e0010358000c2c40d80784a0280c005c0d070303c038006002e102ca1b000845002c00500c2d1a441c00c8001c00450aa060708817108114490300000303881a02e150205054444564405000e296528012034001142040c40b0440307000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 18271724 1250 18270474 18270479
    0x30c1b030910020316060c03021c0203060901050a0b0708070c0b03130b06040209060d05040507171507030b1822031101110703020a080a050403080307020604060c030608070512031201 80
    0x2004000340155880454540d10740401d445000c0760343e4050b0342d04201c01603c0702c400000015415070300c502140348041c2409410b0031102622001d00d000c1000c40219110380010400c803a43c40d1030b05880c0c1c05840e02303d8055258504050b05640e690007200d0f0014a42c450005108081c0401c1e00c42c0480186415030342c1c41d40d2460305034202510043e80d140201c51008210010407094035107802524511040580740504140125403c017001d880007130401d480303a0180003800b04422140c0d409205285104100501c4213041070251040801c1005140e4000c1628007803030030f0903541e602180526000760350003424240b0380b0303903003026403109202c0300705000382e09d41320b501c28001c040d040032041d01141c90320300081002e14010301d1203058504c91040001c1c0140c201e00b91103400030380140090031342c041c483d02d4110f0030187c89550f0004194400c0d01d242002d40e2003901000200991802402c850301414601446440c3c50000ca80e41c1d903030b891380641407055031442550007200c90204191201c00c80011602c088559 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 18272974 1250 18271724 18271777
    0xc040302060301080c040621031d03060c0703080f040309050f2b02011106090703030813050106090f1505090105100e0a031b080102030f060103021b07080127020f06030c 74
    0x17001c916450089040c0348000642030b000d0303468a5000d0b69404189295262a568202c60380d050310005000115200c0c1c01180468030104007051040244004c041d60301d4005003000351003100000c02400e0100f42420030800000e40c41144441191000da602c01c4000a46a00003090204854964200d44024210380041c0d4601416809035040c006e8840484034100c20804907218041140e490036183d00507401000000c0c0f203801096400714075460181000407842c1e990509541032a031200707400c2e9031640e0700c50f2001d0b405485110002e620b0031038450715592410010440c1c4010500c5554841d000030f241104000d409034000c019082c0000300f82c2a00c0e10b460b842c14495070301c0340b00c50207111001015400724502c41c0510803280100100c42c450040c41c0c0e03e500045010394001070403240c1d20389034090100f15208013084440c020b032100f0300000c0380d85000c3c0c140388055004400c100329900600c040303083e000358861103042c1c40c0201c020303030b01e0543d00d03966504015a03034401c40705001c8004a00450804282 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 18274224 1250 18272974 18272983
    0xb1503010f0609150813050d1d090601020c06030601020a0b040c0303032414150307090e06040c0813020105071202030406020c0105091c06060f09020403050f010618050c04030206030108 81
    0xe820045800d8011525003008035400f0110f03020b0b4000921210302004070302c50050200f254080c1e000e2a00041e01c056a036503050070301041d841440c1c0400d000c0c90b44041c00150240034041005000c1c5d90500c56441d104000070740d5000546505070240d84c0010100304183d00c24030010106139002840000340341024030700f01030951aa0710059000910b01060200c5a0880b0b40d804078000201c10a01070b0103500300304080c0203c62401004a500400850401d4000100600a10301c41c0082e912940c00b80c81c50140d0109084500408051090340f811030411410740c0c000507030540003018046001041a600e200607240d5205250f03000c1d04041c20207500c40c0003107500100800941d0b45640c00d5602a800b0b0100540d0740703010703d01400ba4040d030090b8088428082c2c00c03100c400898010400811100d50300d800010440f05213400c90180540c00140520601174100092411902c041d80200905403400440d640c0c0340d42d9448000c45101d440307201054003081840280e8000d503400901c91a03480d45d46000141e0b030b8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 18275474 1250 18274224 18274229
    0x41e150c050403150506090f0901230603010506030c060703051b030c071404051501080402030109021207050a050a03030203040501080a0608070905011707060e060903190f170a05040504020d0b150301 87
    0xa034400c0d684100b9494a501400e1b002c0c00010f0040d2a5646495034400504075008043c41c4403907680c0c400d000c00604000c207041d40c50200e002d5103050700d03041800505094520081015000b035119003410315264413404104c520700d5815181903a1241c0c025070500b004080c031044104000e1002041082001102140010886441581c0300081020510520003920801c035051700c0c1071004c001c0d01c8141540609480d603130061000300001010305c81c03030b4001002282000c0c4250203650006005004a05200d2600009803808075540215149990b07402541c0348110700503a0b040181c140045034105020350401c5000d820103100760750950307481d1514400102024402c50740840080b5009040007100407170040c091320019501e0f03420001d090300602607203500180e4600c0d01846405150000d507026200c01d20b401c035204440c201c4032030b401410b14042880035007c214018800810955241c2901f04048134219a0300b40d5001d41c4440c0704a89020081802d200c11640002940072041410550100154117 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 18276724 1250 18275474 18275483
    0x904060510031407020f0a110d0212010608070902030402030309040c02070b0d020d0501050607030f030b01090e0a02030601030c02031303120302070501020c0601170d0504090b15040617060405041e150c050403 91
    0x340c4c1d614440101d94400c118045a80e01e40c020001280200740300c420f450180841c0544840b10641c45980400c288801032069032100d659111010700c01d92006004940c0140304100056040d030400e03800213500ca200340900c06d88642e03070f500c07900e140c041d0003070000c8401071010f44a80c80c0c80350b4010318a100694801c4945101c11b81c500000071481d45481020344000c15055903600140a2480d2303400e038001c05011741d0031411720466281c00200c0c0080340c0e4200303100300348821000d86c07681081d0002600380c078000d2001e1006e5400a100424001c0004a05030301126085040402d0030440c024058009104202028040354000030f0360b12441c03000001c455040f0744007002041d8101c82060340541e291a8001911400208100001c00511200750840240389400a1110004055031002c0b444a035000d540710401040325807407040c1c9031080040069a201e00c081d101444a403070580d8440500c00840000b80d0340c0062020082c80901a49115403848185081010009004950b13401341064205220445 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 18277974 1250 18276724 18276761
    0xb0a020a1404060203030a051803070f12030b030d0c0602070b0106020c01020c01020706270f030c06080603010204050a03060905010f0c090905090106050306161e0c060e06010e0c090406051003 84
    0x40707550030114201d40c00c43d101c5501450031178550000c420007814005c0c040e401c0c03910031464200c456010070300c0140035051103000744c04542c40d0903280c03106450034041c01c1d1344181450182c4001d140e45000c50a00b0b020140c40c6402c0501c0241c13482d0601c002e000d07248002d0842d0400100115142d0b4000621070100b883c00d0f0203e5079011a11801203945145602401001605038600302e800c0551011020240e00001984c00e0003650300d071070f090b440394805903009403a2084281c50070454650000718960304050300740c2c02035182a0030070010031022010b6120040a07079540d4818070741408020f602c500c0850301e1090042c4641005200010000b00a50140080031460f040100303503c0da1051080d5000c80b100940500415515004070003512095803800c1028032002801c201c3c0c64400e5440703c25565803880e00ea04d04014018180f0400300c0300600d1810f5410303400b14006105080036051420ba00940100007165940d050601082c00380c040d9a200681100005841e45182509a08040c0c1c21065091040303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 18279224 1250 18277974 18277997
    0x304020906090c0406030902030a02031203010510020d1418090702030910020102040806041202030d06081c080907050909010b090f06090f0106120914030c010f05090a030819090b0a020a 81
    0x140c030200f528844540c0e6001c00c000c01006010f500300007a400e0000b000c4c1d51512080e41c010a0a11140c1217000090640000043c4100d26000610301c54080c417a01c02801c200f0030f28031000e0244201e150858541c04000319010aa041d40c2c619805110714001d02908030070708001c40e01075900d0304154602c901c0782d01c0e001d601c110031501c14401c1e10121005440285165180ca4070b811003401010350b819000c40c00100b040c03940000680c0992401041d03000c00a1840d000001d203035440540503040c0b400d04100203d030074408901e000191000503104200c602c07181c1512790512190052030f4007a1826008036031002009a00400050355610410b0705842c0240640d40c1c2c101d242d61409024010b80e008501c8a5244e60754180d60380c0c0c441e440e850b00c40e200c40501d0740801280d280c0745402002c0310340604d030345808940e1520820f174012182c202c400030000349602e0001d590058100c8000402041010580070350080c900c1480340c00c24010143c04c0900c001003810240d1820010354401d0700b20001051409290 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 18280474 1250 18279224 18279229
    0x212070f050708090607030e0d0c030203060c0a08070e010e1e0f06030c0703050f04030c03080309160b07060b041407110f0307020d0303050a0b0907050409060902070309030201080a020715020304020906 88
    0x1c6404060707001689900e02031139202040030507001010240c0c20003005404003100e0340c480d844040d80700c500960301e40750441d140d40304261915100401c0302c0306070003003031114922031034104000540080300348c205003281039001c000407503907840d441c5400c0394400d10400e88283c9454000182c86075101058440050b4961503134280000c1f4032081c2c6040345000700c0ac0060101180c403a001074071031008404140ba03c0c0c6980c175160010007500d00e030016141d04100005201c030120081040500c070f964847e80c41040185014020499800b4019002d4140f40d260102e440e001d54461344040420003401d5204116800c11041c010840c1004078000455885003002071881004004292510594020044500010360340c7d030460180c007000d0552900f4585518450300c5656a101c0042e100b80600d588940d15585498000416a0040d61100403020710421541d130210754800201c070196a020b00700800243c0b80c1e000f420009209030b41c4064080312103050201341c00b02c0e103900210b000e503008490306086600d0b50400c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 18281724 1250 18280474 18280477
    0x106090606020c060d090609120314010f150c060c02030c160f060c06090605160905040b060f07050f06090106030308060301020a082d09060106020106080303040b0a050c0405040212070f05 82
    0x1e20005a031000c10b40412524009000781112081e00101250321034050346c403001901d0645104540702904216842d411940c90b10580c145980e080140000e40d500d00000030660200d07901a04000502c000703141c14071107000b00803541c0e200e54040c070100011014407400a48a0300181c41110305401010180da803a00300388280e44042e40c05040f070102d2042c0c80c0c9001501d009100a40031035926854400035030201d01c00d0f1007024031800c0201d40c04504404940710041400d00e0b1608400d214a1a0400c007503020303103a82d400e40d00c1105d0221440345d17507460607081c6249441409044942144249400c02c0310505c0b040d000300c0f003141e01c2512030495640f10749003090f09038050b0031403040000f090400010102000300f90b400b0812040081072608014040140419030201114000601d80c4202c00410805a0900c103410080440d40040c40c1541000c0c1d8a60241c04000f074107842e04140c4074004104c40740b0766101250b00601c00100110354504098147c2801801c0c00c4403100040b9201c50200d240d10740c003600 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 18282974 1250 18281724 18281729
    0x40c050a0608060103050703060b0703020604150e0601051c0b1302210307030311040b070308040b060109060503040308060328030e0a0501020705120703020a0b0c010614010804120c02040f0e01060906 87
    0x1101c002c41075440200440081c41d000341000101034540c480021a45220001003400344c0c000d5021f01064034180c1030000c00d45038040d94103c05146050080b003c100ca001c030f01141910f500300c8100301903e407054000042d1200c00c84004d0165060b280030300c0301005425040c006030a20075951000f00200c803104460b1400c00600300c0031001d03002004540b00007480b0b6800300e0b0146040800c0782d800c0607107603840c10140350044082100803403210006e0000740032094044543c0290246001020981491700051450001920003400c1c8503407c170100d80240d40911000c138270102032090442c504010907e5140b10b0340c400c03400c1900440c1d4550801c101d40c0c18410f514406844d070680041110500e4001807005980d12010100c0c81c0c0c0c000c6050110050303640c440c082000741000c4020940303c24145030900e00711100d40d44842c20b082c0b8103410810440c0d0304081c2d21b1b0ba0041e040002e5003042d25603203c0a5480031003000d00203511510307000359100034580d20381c401c140040300e00000b041201c0d214054041143c13086e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 18284224 1250 18282974 18282977
    0xf03050f010213181b0507110a0f030f0f05010207080901080702070602030a0c080c0601030507030201080f0403120f140a020a180b1207140f0a1704020d0602090621040c050a06 77
    0x424060030b4801144014869107190000070b0242e800c083c4001c00c82c54034403032440006d600013a0076080c04107030000e081009004580007020745180410b020314549441c03100810500e07240c0c4e0494103021a074000c070845240c0101c000d55882600d850318a409620410000e030100d10302c1408160b0580c03001a0090a5640743d4004518102c20400c0c280d50071855540f0072030301960b0411001021800900449008511900c001c003140c509510016004410081820f200c0c2d46d404410040404c0d80700100f0310040e0314020340003c0715801e200c41d01002d0300e0404605407258101105100a503407480c0d0040000d807480d0390714024200440000414440220b01c19683c0c011002c5c0500300c140130500d2182c642002450030a001054080d5207001c20781d4010a2203001d020001260401109410008491080754000c1d403503000f40c40c140c0e002460a0046040c0074050544c00302d00713950a0f45498080b507000c00114407030408044001184c0c03074181c100896040790103540390440042c840c1880b00743c0100b036038001d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 18285474 1250 18284224 18284257
    0x90209010c0204050a09050109080405010908030307080408090d0503030f040b0a02070b0f1510020f010f020301080d0320070506040203010e0309010c110a09020c0102090109080309030309040207110301060f03050f0102 95
    0x141d000c03c000381074085c0019000c565506c121800241d13092145070130b95441000e1850f05c0794a48800500801102d9000c4e51094100f00304104c030460340002141c3d8041c0c6d10014083e01c0f2060040400c0000c1c0700ed160040442c44008203002d06000c445403190f114620035035011641d507654001c3c0d00b06900a00e60010590700d00d182c0030850010090003290346c0314004070180b14580e421800091000782d03120b0254400b603000700015240080007809100c40c410104031080d49194540a10260b458145c60381900400d942e4050105910f5000070083c01d031120740000f402c2e111040e500700103840d400180c50032403007503181440340003840ca000b005031241c030300050f1070ba40b40c41d84950303e84204c4640703030000c556840400c605002c030300d8081034406410221040400140c48090440001d00840c140d40c024000c00c0d0700c1401114950f50b070000c1240c001d24401c4d140940c442c000d034940660209081c07a44a03030305500b04000403c0c040000446013040b28020030803514a071618882d05401c038414000c415040304072 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 18286724 1250 18285474 18285497
    0xd110c010804020301020c0601120c0e060d080c2d012f130306140915010b0a03020d02040302120604200f100c0510050105031e100504051006030f0b0109020901 70
    0x90301c41e0960150020700054581941a1819418120309070000351002c441c10855905106194410030702804041030130140d242030041c00a04465882c450050180328000b031a80b1b0a024244128881045107640036802c0c514070390311014034084410320a0300a5881c001d9100f1014a10450086007400c81c0c03002c0031408a01c05465901d1039210003501800c00c50701d0100000090040d01c0342c7c44a450031080c0030140c41c1015001d05081035905003041076509440c1d0014020354206d1401c591042850b07040043c0d1b01c200c00785201c4041e003d191b1001e0b620a040d80700308140c0c2c10020410512552103018200d0100340c0b0740784402c0c1002a0007584030f40003001e00c0c1c80104035040c80808409683e0290815400c07107011179840c64030304100700d40c07502d140d5a1188010811803c0409c43d41d000400341c0c030110080400e070441e5466843e050040101c82d60340e00c407804102130060030312070b2540313000300c0c100d0900503a40c6a0a0800ca03450742d0500c100c54a4039000e00004440381c0900c00d54598420503540d51a00e0007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 18287974 1250 18286724 18286727
    0x90105100c12081005010503150f0d052409120403030c0201030f1b03050c091c030504050306040303060e0105150702190b0a0305040614060102151f0b07050d110c01 72
    0x4182031a01003406003032607024001c00c1c8888202880d25050340c0d5040f20b43e00e42541c008a0307500071036102d01d0502500b4030a100c40303000341000340c0ba500070041d200042045d001800080c901c0180c0300001c0c150f405821075080705401070220307946012100c404400c000d512048405503030b41502400c1180c9801c418401440040e01c500504680c81c0d00502d0045140c141c5030844d81c00f250039440354015440c1c030f4442c01030105905401000d600c0444240c070a4280790801e40440c010b901030981784400400700c110100f04160140c02550007604004d012030b0841d241a140180040202d409410011000b0360000550f9240c0047c2e94000740340d01e140c28034140b420550a1080f581e401104a45906150304c00202c1c100052801800b5581004d40d400304042c1024207150003100d11111007612140755000801003036903000122404441e413194100c0b40541d840300e00c241102010803500104952007154000f59a4a05078041c1c049203010b0b0064038003c605070141a11000740e1002001c80d1504100c00d00c42680d0b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 18289224 1250 18287974 18287989
    0x305070203040b030a0e0705040b15030402030a0501090c060206130201090303050a020c1201020d0614060f030a0e0703030801080d09031e0804030606080a0b010b1206041805060c0901030e0606090105 87
    0x484a004407414603490710465107a60704119a0800459507038001e940702004100500001407609940401c0040318480105d06d849120356400c00004d90008003040454508001e034020040d080b400801c0800103616100001e00c806d4030542c0300500c90780d80422040000d0244241001d03034140c440d55159842e55030300350382580151004500b980200c10407860540c4401c4c2103d248442d00b400010b0766107001140040403035030140c000d94072a0302040000341503512000d04942003075504d039080c41c2c0c803540e0b05042c1d100900607801007001c45010740c501c0007003019009103986059907024030540b14103505034102103a004981c0d1002034111105511080310310541000d0007485071303000d031030320600c0c00b92642c8910003640d07034580c0103074119030100400d0014804064012405031006514041c940385206c840d070305056a01605031481282e80c4c004180148240b60241d403076140e88881607407654900003040d6800e5070021126240800d050116030640d048010416602ca468001d1203068a43d007000b00b8440e46 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 18290474 1250 18289224 18289231
    0x1020a0308070e03070905090d0912020103090206070c08070317030f071110020c0304090c02030c0c040213090906090302011503030207120c0e0f060103150503030304060b1309081908060108070305 86
    0x180150380f00740162988091100300058885000c001c200340c20031072340062900080742c41307020070014401020310060083c040844d422540910b000b14000029000080e03140c4629800285002080b400020b02c000003c83c00f0340440340a5550b03030aa2101c6894a030300e030f03403204403601c440d036203d101c0006040c0307801107040510000028040354a8400c0d588605c1d0f080f40c4c8100c030540c14552000c0303000c02c9010b03c1400751b200c183c96980701940c1400c0404208903555001d010032144169004035500e0048011852408000c000c6040248900c04403410484001d0111031001e038015400c020382c2d440403c00004812013103903407560082201c240750582c0b403c910400070740d003201c030040075403000203259004100441c080c40358079402c0000d604203440050210750301881c50702c1020301103480802042c2c0d00031050b2a4441d13007065000c00c2481680001078042c0f200240102e60842c070781851081488404800f910b105070319500b544a4011030034009607100f07001103500714002400d19001480480c4280c004540 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 18291724 1250 18290474 18290477
    0x9091107060905070503010e011409030c06010303030e12041203090b1303031101090f0b1f030803130203010605040c09050909070e070c03020109021806181b090d020303041d0c0901020a030807 84
    0x80180c64100007407c3d146222300344941c42e91123941500c0c603003603000c0313110b03030440c1040c0000c520700000300242e59114001444080c2c01e02da52003d503503022120910001400208100055903103507143d100070403415010030780960015401450100f900703142c3d10103c8017110000014400810719555003102d0041c00d030b5940503459500c1d8400b40740002d42401c14a601d10f03101d40c12120072803074109484c244840140010824042c00c0d41f10810110f68000708603030b088130700c0c07100f003d050304458000311b4050481c580c80240c106103450590340f2095440310b0328070180c9808460024054a8034403120b50b07190140d00458410340c03030050100d24501d0080c28900a0700e4401e000100300844240c000641a071b0491081018034140c802c20851540381c605800c000c0c01d9503201d8000c1c05814800d11703022407401000340703110000c240010080c1c62030b9034448414044550040440740c1c0e441c1c5981c44036540c189802180c3d40c4245043c000300b010038004200359000716a041c3d00508122455490407503e00c0f802501303850 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 18292974 1250 18291724 18291733
    0x303040306020f030106110a150e031b06190209030309010c03110a0302070e0703050709062105090d0f051e09040902030609010903020c040903050f1305060304110109091107060905 79
    0xa0082c0054070b021250392414507101d41c500207000e00420141c84020f4070540103e0b104100260400b40b9580700194508400101c02c0000f500031407840c442c0f0300581c20303d03040050306440e080c40b0001310740b4866058403104c1e1017009031082ca080264000c080506505800900c0b581009510842c010584140a0301e041b8407a00c10509000c1d040c1082c00d079042d030040c0c0010105000c20000800c1d0150046018034080000d4540000c0c0144200e806006103420444021010140040c82c440310103c0e000f560789040005060004041d84d40e49017110042012929072052212058040d00c00d40e80d05002a0029400450501c0c0d0803215603408509104d502954070313045080561030400111f482400680c00004104101c0e0902914205024603190722a6050100c1d20f40008d5000b025100a030360400c0da040d07102d50030003002401d840705c1b81e004541c00c00c202104110502c101d441d40b0700000c41c02a2504026203494141b2181994000c841403190840c0410181000031510741c4101110b174010381c00d85 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 18294224 1250 18292974 18292979
    0x6010207050a030303050906070503010b1603050c0d081006110712051906140604020301060c02010806030a0f03050d0c050f04030809030a02030714090a060302090402010507050a020d030302040e0601020d120b030304 94
    0x903050b820320340040c0c3c0043d0342e400c2082120f040c200300c0242c028880781000c0d070642d89407104a41c818415903546c0018942c0d80021039042600407019100d0111800040c0c0ba41c0a8014400411681c1c0c2104c80c005c40c2c1640540000f004d500600d2403559003190b0744080d02e49241012400c1c2c0002444100c00c82c0c50340301c0d500005041c41c1201c440b844140c0d10072000407074101c00c8041001e03006400070b051144a0b03441000100141500205c001448590a0800240c20b43d510b100203402c2440042024180342c00c5241c1400406901ca001003c802c01c84010130044544840002c0305c1c0760154402036002c08504000903c080f42e00d00b00541002030707006046079900d20541c0c5c082402c2c074085600002c50507042e01000d00481c680b403035015034400361609003007040501e1a0001401140e0242000c2d052060008614007400024454200125006411040c100c13a5920b4001c0081d8042d1250f41900710450010501640c404102c074650f8844642d20708203211105981d001c01045891000c991520041000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 18295474 1250 18294224 18294229
    0x9120302030c03040f0504151503090c08060903070311060609070c02041b030c02010c02010506100804050a08030c0304110117040b070306050a030804051503130b060d020d050a120e030601030b0601020705 89
    0x803c0540002012908480e1800c1c040c00f041e20305403040540036000923001031241c0b401d5244c1140140282e803401240021441c180813030b000340140c100b0001400350208001c1c1051001000f4449103109580d0040d00300c1101c2c03c03003503c954040d10500c0d0301c5204203000c40d0350244140c4c4420203250004000282003054044c1070800d00d0042013104001c42d440c0d8482c0c00c0b10940a2064040b6250580000d01442c5030080c002900e941c2440d401d0000e00032810082001e128040115502030303980b082c0c00640d01d050081c0b000100360011a8100d6030710f090342341024001d5100d940060720407051400008080d80f1180d036071400c8844010a14820156290310010f46503613101004e40045004081c5141e446080005000e00032584203203541403108200b00703101c00820151066600c90790051051285510f03008001240540d8220010b58008008102c107c28007401203854509103102d1b119803402161203c90694280070320707100309541904148010000303d0303001078020b0f40c004c8052040da040303d501c5100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 18296724 1250 18295474 18295477
    0x201051e030a0b030601050d03050d050c0f0a0206040b010f150f030b03150405071e06030f0b0406140306010e0105060901120b03070303051e03130f020a0306020c030903010f090309120302030c03 85
    0x140b41a201d07895840700015030074144061800b4160660302d405040c8425200a8824400c00118040080d941c90000703c0c41c99407407007a50011082e03207014580e1038040d100003d50316001030b20182d40d0241c038100000b4020404c25003900480c0c100c2112072203820b203022401d848810708200c101d401c2c55195803000d1903654003030003c40c01a0032034100312601410141822071410005400030513410018003200307405202800702c00340440d8118a40891640c5807140148003401b03810f042e10350424105000813901b12901c08080e840c0050940c02c80b02d0a030303030740c3c0803044006000388140780c2c0100d402c0108814a505c40d51100d101c010711004081480f404440200b07140000390790080d0300040300801d40c0c20b850801440640607114407082e0181c118109220001d0107140001c900402c600d5840c800401151201c440300c00055800c035504646070b0140045040d00d80e400039284511951030100304e10425400740c89000c009030b8040d900c901400d1704000f51003c86000c104015001e500c0103010607900b801d001c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 18297974 1250 18296724 18296731
    0x5090a05120a150b010215070908010f020a030f0b010914030312010803030f01060e010912110406170f0a15021312060204030b010e09150c040909060c23070201051e03 73
    0x90003480150103034200361000c1d007001000c08440f28100190310020341c0e80040c0962500c80036040803861503d42210984400155910002d09035080c000201208600c82d809400c015820b600c003440140c60404004080b01c86980c010b50104201c074205005043c100c1d0311b8111702d4000901102e18080c0100703014001503100360f2000c0f0513580000b0801200c484090491401403016042c100d03000c400c0300001800c0c0d25454020041d070411800c44050900c900640c0b00340852102074001c01141e51507501860041038600c60021b0b03184510385c2400510000010650005074110303083c003042e003500d82d581070f010754008a190ba1807106a0140841c1d000301003501041c80611a02c00103070356514500d00401e00350310582c881d081007400d0008101288a011030a03201a407080403145c00b15940300d030781c3c455413400b0b41d41203541d90514000380b207000c00043d540800140205600c0b0f041c480d2040402442c0c8224030f500700002c0820040c801c007401540104080d10043c6110300254100c5141c03140481d655800c201c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 18299224 1250 18297974 18298009
    0xc080105150a03050c040f0f050f01030506161d04020403170403061409030913150801090c05090112060b0103020708030910110906042603041d010803120705090a05 72
    0x2002030011070400140141a5941e095600484a6285464070f60b110311000000342c1c06151200e003004c19402c41c2e60b1160b5003042c58020f0400040c28003001c0c601ca610002d0002f19007038410500800c081d0180c0e04c4210041c181a595088260080140380c081c2c8110f1844141d41c11540034400400052480c4c090314001c40340781c07103225468910314108002038610782e40e040b40f0b6000c0720b40148110800003008488003040140c4645000e485134491100051511020303800e840501c00c0710114503200c06400003407807140124044031590344c071401000000c4600b0310440b48440448100000001d0185c0c125040e03030f0390305050050030115181c541999540c0101c44d8110540c015038000c41540c40144107114510714410181400d0100d280b000c01c00340c0c8a64024050301440c0f03c1a0035942c2d040100100d2680960034040d2500c0f1682d42d484215695800c442c0158048540700000c5000d480000030381e070240c40e03d601310415640782d02c0410390700c56001001141d0006056040440c940d120060b041440040c80c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 18300474 1250 18299224 18299231
    0x150c0807031505060702010c1a0109020703020c030d02060711030d09061b080408090616060e010504020306070810060503150a03080c0124060f020f01090303050601080105120709050a0204030c0801 86
    0x1000c01011994540c41090402541c01028030040d00c0741c10694403401d60a00704004180e08034184068840c00c48400a6130080c41c0000100380002603402410b8114401e40860340c0102d250420961207045540c50100140e11047c0028040761040d800114140c0104098902c0c104c086c0f0660380039640c2d5540151103580d115101c2200162804000e002c41e4022031401c503115042c80e039100c00d039030302c12012614071442c070125603221551054501c80300070b0340c0c2c848010007002809403050342c0641300865059105c2d010f030f400001d540fa4014103c0500c01c0c080703504507900150401d40d0030340701c1e13400180c8400b00120003115103200f980ca0300707500d0300302a6004480c07141d103458860320a0b90a485500c01240c203002082042440505540b54015040e501282442000000131010892a1403140b81c0210f8039036003031045100500d82c0550055000344820b90311034078641e880380c00f88603001c110480900c00a42c0015410042c80041d0307444590003e100640142c5232a0392a2240b40110388940c0000405075034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 18301724 1250 18300474 18300481
    0xb0408040303080a0e060106050901110303100f1a19030603020607061a060c070b030405030f070b01140612241002160503012a090512030a020d020105090712150c08 72
    0x700110300b5940b003401410300744a01c10b01d45c00741c9502c4100c1841501b0074040d01050039103032a070251255000a04101040f20b40300d2600c0742d03030a07410700c141c0d214144840311400c4022610704091500d1400c0442c0e14541c05203070283c0940c0c44102420384803421f50400d0340c0e41c03d000c00143e60352001006850300607200403d4101c4c2d04214021010585240a485040200b00040750723800041516800c517402d926695450742d0302ca0410b1411446000310140070004001820b504209800381000d040e101d42d0340c1910000d41214052140c41c0c030895859407a03112246c00000c196032211500e01100080c4079011410b2a94200c011440a02c0d10040b034a003d40c00609a225991581d02d818600501080b402800402201c0c44010000c1000e6241641c031800344000000440d8050040399005100280510220012545c070a544030b412a003000350042c010030185e4001540b0501680f4000c6421001801c0107034076101c2c0081c0c80040741c08084407119400701441361081401d00c02c0781c0500e0b92740e4a56400038034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 18302974 1250 18301724 18301727
    0x2120703050a0e12071b0b0a03060509010605030606071a070c02040509071a03070c0c0e04030f0c080307030c02010e060a060303021203010b0412050102070209090d03150e04020415030b0408040303 86
    0xd078001c0200e07031880d18009440c11482d80015440761020b06400542d0b60301d6265080414485000e62040303841d4203000b12001600c06008801010302c0d1901d40c0d0f08200240d01d0707000b0031150300800c0c4207000000e2410b00c08225a40340040040c40890b22802c011480401111015941c25100701d820305c02050340c0842100075400c050150b81d03030200031000a46281030030400980340b414128030310342800501c08000100c0070340c06501000a43c64001405000b401d03075400071101c80440880f02100040d01c8489028000c601895100260940c0045968119910f6010817801482d0a0600c0d00071992aa42c46100b1400240300050152890103004246c3d0f90460401a1810412482462280700208010040700c1d0944041d1400e40d9400307141c0c4c070280301c583e042c00f50190107001d00281d8080046000d20583c4000025a001038041a881c00d03c511444ea00701d05d42d01071418425031109403105c00014005140079403000c29a01c44920981100c40d44a844035102000c0440d41105c0890001030144280f6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 18304224 1250 18302974 18302981
    0xf030111041502010905030d023007031a21010906020d05040309050303070c06031104030b1503061005010c11060f040b030415060302010c150e0f0c18010302090f130602120703 77
    0x4000ba0009121a403015130310682d50b48900183d04c120164017084149800542c4003a50b0009040300c2c4a407030003e0300d05900010030030b100703407980d4010a1801d00c1d0303a0385040d0704000c1880c003010001d18601c4101c10301140c0302d641607a09110300070603569841c0d14100041080c80504584030080b90b001074a441c01f4030300589420030f95045103100358020700550001030900904202640c1140c907010800300645031142d521030150f034000031305901d420070402c498100503544502004000310100c41c040c3e1521043c03801811400e00410f40040d500c081e40001248041d20b010b6101c0c0d401600c660324000b00214080f0081d0443d410402d0551400010b00090007401c2001c4080b400f0825401c010061135903001802040050600030090002800510100941d95004483d07030004041920610811588842c1d1142190300c0440d110383c0c03101d003072002c3d016020003107141030b258054134010b580d0b2034400c3c1e10f086640c0010103100038800c1c00d001000004a15002604449452800c2889507007484980601907 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 18305474 1250 18304224 18304259
    0x18010801050d12030603020d050d090b030907060503130c06170f060a06110c030105070908060c0309030906070503040902040b030a0506030a03080705090d0203010e0c15090105070305090f03011104 86
    0x10404814014402035079800c0004401a40c00800502c18403036070001039000e840c0561010754000e03080000342090110101d0320000e1124251317aaa010652940301c411246d00041c1e446200c07903031190b4000c0c44500c1c0641c0065400ca0b03000103200091100a0f07980380c03107880302a04204001280610a600510394503510190084002071004030f07a41350207008514010910f204100800c100180c0c101403402041c0400c20704444007400901c0503141032000541010307020311035058030340301e890700080220f12075000340c03802050b04402540c50a039843d000c001194114000942e0a400100030000b0410316510041004111042410303880749844200c5004840f0005e100c03a001c1c0c2c010f1402400000e07441412a6802512070600a88911080d00410700400040740025019841c040303241c0044000082c0004500200301c0d140031002204400301c0106001e5580c0301c1d400300d0f01c14082600007034050001303400360580c0a00b40780311912200c400642924000705800003070b0540014240030402841281140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 18306724 1250 18305474 18305477
    0xc0806090102041d1f08010b0a0b0c0a0b1008060103111002011505060f0702030102071a22080a03090b10050103060603060501080606070c03080a0302030a1503030c02010807051902031801 82
    0x4240c60060700d00704404c403140c0b18188400d40e88000400b0303000900c91420ba5509207104c80c900c642c1d110b038021030003411404c041d244203141001000640d480c6620440b42606640c1020f0f1201d0002c668805544802c06443e101042d424000d0128450b502001101d00031130186004910002e0003e0520490000c0b01d00300004590509142403200d00084400303100b250700c1503503002c2d07503029006444606400b556000941c5540005070080c20b0028020502d6580301403501d5152072601c179108400d801108100c2107041c0101c20042c41c00125684130094418070ba005d0030080b91082c802e94900089840440d91005d420b0890031045c03140f940c4c503129400162410f41820000030b4141000608511402010700d445007400251640030488203c000340001e5070b0080c00303c4c0d1515480c400c041c0c007a420032540c00d02000d203402403030b03640b00440d8820042140d415460380c020108480d001102e079610002c01000901808201d4092080d080c4a510601c50907154003440e150035007a95025024042a00d00303a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 18307974 1250 18306724 18306727
    0xd050c0f0604150f2604050705040e0604110609040518060603010c12050c07020d030203030106110307020603010501030203130b0106090509090105060307050d050705090a0203010503060a0501080d180f030c0806090102 95
    0x11a01c40401840c01083c00503003015491000342040c1240c05000036110300010032848407a0000c55402e45170a135000700d1040042d03a4129466600b40030403240101c0c03240c0a250f01c1000820042110342d030b1006022007001d0500d900d0865150049000d441040c0c980503509803c00000c0b294403a41400750f0f98000c00202c0080c0f124040f481c400030a10b2100100089441d6510404a07000d640c0020459200d154080c084a1044580d810701039240e4100740705500102d0740d0500304110495011040b989100d0340244000d0550342882d0044009400c000c1680b0460480343c15030308081982490000c2c000c154540d2250107c9041a003808902c0c071f40542400d00c503a040c04c080c0030707a550700407406c00c007aa4003d40316071032540020305115242c451140c0c82550000d81c04000d21904c0480c50f0001e45c113071507050701110354607122070150703030304541091050a082d40c000340014040f0341c0c490652450703184229030086a10903162501d0b00540000d43e0702c100c5401e40310303074400c0103114018010107501c065520b0003107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 18309224 1250 18307974 18307979
    0xa020d0c050c010f0903060908090108010609050604060309020f030106080d020f03040f030305070203030f0c060a060602030309071e0306051815010303090302210102030a060303020c030a020114070f020d050c0f0604 94
    0x582d100342c801c41150500a400100c2c550041c81403210200440d00100c041c0060304d020b080c0042c042c3d020b0a00940000c5482c0c00100340fa50003118003008542d800b4010a00e45031914008400070440d00711300300d902512022041d04e556400340038440140c0340074005001e15103944c09010340f408070346402c8120184c000b440200803c3d03008180540c112a0581402c03542c1d403210f840001e04510031001350810b040d80120f0300d080400c9000488500c542003d8008000d804d0310343e402a41e41c0e000440d1110001d500100c810f2240d1340c039084810000801c1c4404590915403240c0e540c41c1541c000b150b040140704014040148a041c041210480700641d500512129505584009000d4111804042d0290003000812007036080c0c5240083c1041001c60000c640364144821040c3c00f61031644007c2d0018414600c00e180d46250105010880b01d078140c46000c1183c605091441c115004900280e40c3c6800d080b11080250300d400d8440c09526218002400c544620340c000c001c109100c0e02c41c4039004c0c10b03052106 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 18310474 1250 18309224 18309233
    0x140c03070f080709050702030c0a0b010602160311010e040e030a030f0506060c0a0b04030c021c0204060605090303090d050a02040c08100902040e0601080a0603050f0709060b09150d0f020f0a020d0c 86
    0xc43c0140c1e2103409000c00e040d82c420b0000e038918400c5c0c10502c5c16900c11214241c0030b2200e4440350714180d03140e640c207488000035481001c1528030f0300c60001030140d1407468440034041d030088207901030504020b4008620380c4ca100b1211800c5810400002020985032070a040000031280704140d031028040b11070f64200420401a203554842248000f4041000100031034181800b907801540303000e5000740281c8009485011040000800c820100e019500308000862440c2c010003d0392203810000c0c2c011070070302d151042009440003410b40140da460180814480143e01d543c0282036800016441c0d820749410610010190750f00590711500c4014810700c400d00140c0e1081c15455004007092900510b1500c4200000c0010400340d8401007030762107100d28000403104041582011986001c40070040d203561920095980c2c801c43c6072490f40410741c5d441103c86045000042c08c1c2c082c82d6030a00082d1001d001180208a9006481102d40b0590105060300007079810000c0301201c0310075250064004416944 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 18311724 1250 18310474 18310483
    0x403030c020d1a07050405090a06141302070c260d021002031509010603050601030c0201050402060a030e03040e13060c020a02090c0d020708190f0c030206040b13140c03070f08 77
    0x400034800d500e03040c0300307005100b20390070090f200300c0c201804018582800d640144c21035010b44a078034016014400020440c2d42e01d88200c0c400c4610b26100101c00e6140601000403100301c0104441c4e0f4123509005840214074800441005001022844440141e0903880e03007884a101c0d00e44070907543d0020540c0085185e001c01c0e40543c2d442a5079025846e0348445201460b04081c0024060b08101860000035480d43d25801c610300070704080e20b04100918009904a080c1c0b001141c001e03410031001c128007081184241c1c09901000c0d0303140709481c1410740342c59212044103c00e41e08483c04112105e443c070240082c9100b20085030250740010030003110154082401a50000c0803480341c075001040c2110080040d030111100158415941607840400c1c22004480c4405420507800285a40c40940803440c0074515a804054040d0028580b0766590341d030311060044005c1c902812440d0f02c03041c00c400a5039400c80322040c20b25210140c01d1404405c801d052a0819541c0000c250141b221340820404c2c80204 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 18312974 1250 18311724 18311747
    0x3140f0406050a090513090b0a06030804051002011803020f060705090f0114090301020f0d050705160803061c0f21120f1503080c0d020d051b10020c0304060e06040303 73
    0x900c252034080c005003e4074514000d50043c0c3e00401c030b003103907946d8500e226030084600038482d110324292529515064012689903000050404104210511140c940064124003890130380c40041501c070841411070072a50b5281904a000da40301013100215807405100640e80000c4031714202d0300300907100380003514030b0710b011042c170741449075500c0e0411003040b8000441c0c000d071070043c00039561402c0c542500d04407a07111051031456246854040764156200e00c0031100708041c40d0f0099400503c807900c0d2a07004d980003418041e40a4044080e00c00b003680055290707414070740038030b25000340c00c0ea2600b4000204c1180c124140301000d0b0180d00012010741040010b031800d038003200f00150110020500800511410f0410026119240c00c0001001001d400074400c107800c14003038802e9208100000c1e42e50f8070021a854001c00e4007840340b00044240e001403105006a41c600b201c0c0c0480b120040b0004076480003e01c1030b1b090300300050901c21245c1080407031144070002d40e80b607172403c0c0c503680f0000c22014610 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 18314224 1250 18312974 18312977
    0x50708040b06040603060608030408070f050a05150409050115020f010506030319020705030102030c0c100c12180b04030503060a050303070b0f19020a020706090603050411090901090602070b0403140f0406 89
    0x7100814019151640200d02661b40a00100200e94036103249540d2034002d445490400e00c144000401c80c0c0c40994403420446d400540006803003410042008404048440450b084020621002038140d000c0d02034a03009041c0550f0031b5080b04504603009081420f040d03c00d0800340c1c1040107010b00e036113000045842c4144104010100202c40381230490030000036500c0280e1541c00442401071b449001340037800141440b2046030548014820044103075040c0300c2100c0080351407411642c1c050300e81a005040014101d400c0f083c01c04129543c1c888503002d090f03a042c0c00080006c03040000c1c80c01c00c8072040c0d01070a404c40055081c003201d59955101c0010007040000c1410f01e44006c0344e0260407800410320340300d00403002552644c1001000030341e910b4a5106107c005207143d0340c0003800c14044c0c494103014541004109000310161010700c84080301c01742407141150341e034800b51004103a00c3c1c400b41004510070714803070f44d043c242800c2c028181c282646480b10040340030000c1612030303c1c108003281c0455103c1e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 18315474 1250 18314224 18314243
    0x20a0501030b0418151407081603110a09080f0102070b0a0b0d020307080105150d080a08070216030606050906041506110c09090c120304060509060906070807031106090105070804 78
    0x340b0101e0003900300c02c0003404034154085161020040c103400c40c80c480441480042285001001c036044840314151440408901c0c2c3e0004601a0b00c441824100c5140807800e0114100080c1c04052000d940410307480c40002d071a2800a21081d0000d00a07a0790340c0c410b40c0020740c04c1c151305444401d010b24014004011880d55030601a0540d15000300c02e208d0150002c00390744085603260310300384c0686400c03582c0f044201d5034456283d8082ca0b11200004e0f20f030340c100c640e6500b001c500c01d07819a414100a495101580704400c002d541c00c91480004102441c495000400c0e002d20300003d004404c00c0140585100728106140303610101e134040354603000c4680c0351405981429804510a00705041c45203080d4100c40c45404002404200151a00b455035080d80c0d41c202a5114800c0981c981c00765020b00c0c40054010000c8086038680f24010381081c4000500c410301d40b0449a407210031030790100c24120041550801200c0340d0a1003400700c184e006070004000e000c0e61804401c018a680002440100001c04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 18316724 1250 18315474 18315491
    0x90f060901020d0309021206040f06050a140606130806090706080a060e040210031103040b090607020a0b0703020901020f010f090302070608010b030106030e01021201030b01170307080f03090a06050c0403140109020a050103 97
    0x840303010148012011f0826251707d4103042c1000d0250040c500003d64429081c200441c2100c500da206041101c002c600641440317455000c10807036a503008494002d50380c041c280c8085600708090002d0b42c00340141c400144469403802c840038003001d81c002c1020024a141410401011218034491948940d04a490350040c00c0225010b13401000324107440271800201108120400120300d0301c40b07001d008510100c1e07100e5038401804980e41c500c0c0880081543c132501006c18080c9029401400d50f4000500684c0c0050031a81a21400c4510b480c0d4800b50040c1c890301c2010625070140150005403a030f80c940b524541d0b050520203501ca01c030610842040503620060030369210000e5043e42c00d80c0483d50610407295a59081181e0508020f0195020000c01c03a80d080300f104400101b240c803003c2e4050f10842c1071145503030f10400c098000410007d1503002380711040c0001601c0c2e210b01403294105230350715a00d440c00c50030144100340621070209000c0c1e24201c081c901603901d0105410481e2402d1a001c6070107038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 18317974 1250 18316724 18316729
    0x6020901020709020304030504170f0a0602090d020d080d24030b060105041d0a1a0901030b04020a0503070801020a030b01030c02191401060e06100e0a0b0f130b090f060901020d030902 80
    0x21035503840f110707000384080244020564040010000c442102c400704005140b860699511024040c540c02820703845405020005070183d0054418150000c1604c0c90b10385035074001c10890441c1501c112a11031000071141c008000c0c9124802c484d01c44020318001010440c0c000e817880c64054000504103d0b5030000041041c0e00c504202d402500300385400d59074900541100550b801400d03583c05c100e10b4104040303440040340d504440c1054500080019602d40d1842d11000e001030405441039800c440c00c0d04d0086802e0300c080141030000d0402ca0b00043ea290b00c0e00310001c08491700d0082a0741054141138122040550016107040c0116228840f81110403903803508a00740e980b030400012055003000300014005001c1038056105000076910b010744420200c8044410764400012103034864000d030018003031041c418018080710240f2802d810f1406030055803420710300d44940d01c0440340b800001541c90460030b044000701c02d88035040c0c58003402c02c8240e0300042d44891006009004065460b9121030556 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 18319224 1250 18317974 18317983
    0x30405010b0a030f050105091b04020f04080607050703030e070302010804030f030f06230604030804120303090503040e0105030c12030406180f0603061a030601020a06020d0f05070504090606020c0604030602090102 93
    0x1410040c28158490f94900d80900c1e040b0582400b50b429521342000140c00f08004500c56401c6120000303401c420300e61031020040203400001581d1841c0c24180004680070034204240d600521080e12182d440b1145031070f004040d920310146100307540d0418941000140d8000411a0300036034581080ba0044803000401c60007000c00c2d031201c0c165241810343c00901d805482000c4020264900d4590110140160503c000c42c415844000d01481c0100020003840320260416101603100b4035000c15140c0c0d030b13034454615541103900070142d0040000010010f5150402c00125009419580700c041603132000c40301504e9020340d12400f0309114101c1d02c0400b801074400100c6001d003103001500308403180c1f6144018001d03c0e6602801d0b041400c54401c003140c24200e601681c4c4030700c4059000700b01e0400f2a42d11940a504810020003000f5154445110800441d00455210750001d0761003030f803203e14102c04181610717065441503040d03411512502c0c04a440f520122801d881c0c00c600d0150703483c10260b0040b860b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 18320474 1250 18319224 18319241
    0xd09020a14010806091e10060f080103050a060519050108010203060a2403180b18010605031609200a031b032003060d120507051204080316060b0604090906050f060109030803040501 79
    0x521254100585030720a0601c0744c1c00e54002e62707590004015100e00c1501d641764280400b501c240d101c044c000001030030580000303901603c80070034a401c820f20742d101c3c10144c420030380141c081650003204001c0241010080308008210302811544030b000c1c0440340c1c0403240e4604442000b056182c801c2d00c00c0500d40d05880140540d484024000380e440d01c907100c64518506128401095400c251000545180001d00c01044203690a400007646240003400e00040c6075140c880c00c185420b84080d22a20011000503220012103520045a080220704089042d110054601070503d8500504029000010b0707a64040303070f02e085060240e880e2500d00c00101e1114030004001d0100b50407001103440d095100000c1c003001c0b88074504680c070402c100c001e0403810b40540d0259903620390041c00701c13f2000d4030403400350f41c0860103624002040d984c3c41d00481d2846c0e0280c0c1020540c5526005400108449481401d80c40910303e00070002c1420113000003440c6084a1001828448000c40030600340f00c400e40c0051174 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 18321724 1250 18320474 18320521
    0x18040b180906011a040b090102010609061202030c0103060f090504020d0203030a1d0d110d06090501050106030204170a020303030408070c050a06080a050f07020303060d170d09020a1401080609 84
    0x4100490a00c11001000c003280e641125001d54400003403003801500e00403c03281d0207074035114245814500f101500b034101d00c00b040e0441d902e945000540341c03000d10440e4050020118480c080c0441801031610b031089900341c4a042610704001005a568000051419140c1e00080890380d41c0b40d90000801e1000540707406903040c0070001e540702410f600300d03002800881e105d000041d10030000100b0401440340b641005401d240e0850b100510a01c0c01ca00413044c0d42d442183c0c00500c039071003502c40a0846200b6080900440c1d80002d0a20040e01341056601e142c09011004044612280d030110703480c2d0202600090040c2c0c00481e041d4100300d030000700400584005012050107940d202c000034030003007040c1c9010040c1464000030910032420418110b11402c0a41c0045186840780c1050061042c0c40b2071050700c9841c421801401d50402000c014100000b0b241d202081c413400c2801000280600c40d480300d18280b550030144001c5981150506920007030843d44442256982c042c2c503080b29115407080d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 18322974 1250 18321724 18321739
    0x309060207080d0506010207090c020604030c051504080903010605120304140a09050403050415020307020315060d0813030512070b06010c061d0d02070f0807030b070513030807050d0504050618040b 86
    0x2019500f66030010f440740900b64220b81045071707240814070498000600501c0140c000c0c50005020078020038926461038442d0085801507219011600c0454405581c215929440010480c1d03003454240a10000b5040448200100c0450440090364138442d40c8030303000b03100e000300c1c0101010ba175800c0603c400a203841e44040c0000d14207072078020700c0c56019026042040c00801c0c5450081031001098a1046601400605082e0740007000d03d4035200c0c1c000d10496004205a107180001030141000d021150511402e081200d0304518007982808103902c01000b81107414000d21021885006c1c40d59000f00c001e0900d81307524040d41c10f103100034010b14071440b65a00c1110340e0020440800141510960340c6660175100e074986c4402070710101c000a846a0074480c4d01c00343c400e0010501d000700307850700503103581440380c50081d820041c0010714a480c2c0c01511039280c0810751406101d400d10018203d5100c1703240c801c2c982420400018540d00485e404074503540541645031140340c07500c5d80700c881c40000003009038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 18324224 1250 18322974 18322987
    0x3030a0f021308010c03062709050c040903020c1005072103200a170702030f0903030c0609070609060203040f030311010902130605130203010302090c07030212040f030605090c030706030906020708 86
    0x3806400710400240c00285405400104d118020820842c4048e11000050552400ca5a0b41004d00317483c01003038405014524940c0040c0d03549110720024188260044c0503585000c90803c000c01c00241e03142402d000c0208281000950072181842c211a0280070030b0700082d4454500720001c01d4400b90101000b15003444c90f81d18504800040c2c03210000700c2d52244068076110142c0c40880710700b03803502c0c40940d10a00a142c1c0400360280070b0050010003500710b03420301e000c00700716505d1300c2c1c0141d402d6002074101150038041c0300d501584030805060180010341c9802d190880d100003103443d40c80050100843c00300b00419081e42034000c0855240c0040c044100e00d0076441036030004009500ca100e20035007240c1c0c8070051307241507402501e040706e40061902d0065034401301e03100320550042070304800b140900c09869030b001e40400c020380041c1040204180c001070131890300c2c0c1e04964014050402940c0151034035459035a0019207030054420b540380100e4401c49618040c40a0700032550001d01e5500041003d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 18325474 1250 18324224 18324239
    0xc1504080723010c08030105150d090303051807080703080a1106010611070602010e030301060305090a0609060b040513020f010f120203040501020901080c03040305030f10030803041401050106020d0203030a0f0213 93
    0x41d91003034240c1da405500e01c9030b12800156042c8500001c0140b407a40184010003551a02600c560408080a031005245c059540c407007108035401003d0850100b6511410700c100c010070901c0781503640c5001002004a00c0c14298520ba644082d444010704040000035154400d510400d036140d070f4071602404a400650f10341501500d40703d201000c85540b48900307480001e03107a105003d02c1c030541c0514009949141d00b00720044002d800004d00702d01c1c2501c50008035800143d0944606000f41d401801e00140c2404281c0400040c0c03078018004480b410282122000942d4400c4245051140c09083c94546241910380560345100c3d1a00501c40c4140b002c0204000d200e0190001c240900d03090344c0340000b0b0f0340d640110390b506010941340600040c074248005004610f030040901d41140d2040000d01030f4075501c5e5110800d0780e10482d0b045900c02e103109280c2c084a0400d0181d640500b0090001d400402d188001c025502c0c0001803420090781c2d100c0250003000c0b0450b504840c4406400230b400c03044070b03890325036 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 18326724 1250 18325474 18325499
    0x3030f0509010c11012007050a0f0303090209011a090405060112090b160305011a0d060f030311010516140313020315011409010b07020402030402031f060501020106090207050c15040807 81
    0x224035020903011021160500010312410740405070b840818039000e0011b81c2201c1544d00071030002c40e81e6101702c0c80c2e020301240c25108000c09151003680c1c04920442c02d0302c10f10845a1060707100c00c0107000e4289001d0740080040003503c58011042d02c0018147d80d078540120740e18403004486981039494400729170180000c440c03805116080344a03006188494180e412012070703c0911500c0348218000740d00308441c00700c4500801c150001124049035881d02d40781c3c1041890441d500c11008281744003e031181070607080c054543e01c814039554440240420f00c8000e482031145290540030030100000003800407a002150b160b2544e0083c1c101c4501d403044c0c400c445a021028020740c41c000740d0145150055240c038400e00c034140e420005007a41003249a5080c0006500003400c00c0707034036008070382440d4030045420720031510345c1d118810045992071400001a084070400d81085a00701d00401640011410015140b42045010759070020390940c8840c4440b40c1d4020741c0c01680042c0150b002c0050440c04c1c1c0a07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 18327974 1250 18326724 18326741
    0x109050405090f06150a0509040f050118031106010303020c01050d0609022a010e030a030c020102090d150605010315050d05070305061609050303030f0103031103040b21060d11090403030f050901 85
    0x1085400a4039001d0b1801085a84000d1407507012040506c140f0013410800d048a4005108400340000d010040e40e44500352001604440c0c42800420801418568810110285010003001521441d419510000e40700e2038100b410b0b40c1030010000304040c0600c1c0759031001c0700800c5610811234850840106102c0c1040503000262003810089034440c0020030184a00801c8100030401107103407030b240b4a019006400c07091103c20540d50f09120f24500b54880707c11030613980e8425440740c1da280790740e10548400ca40d52500454101490100403090351506544080143d810031101840d058040b45081440c2943c40e41004103607000e0072041c8040302c400340b00c1109001322640c4a4842c019281e005140d5030740000c84610205803900001000440c2c000c0751708404243c00c080030f4038546a2a604400819842540c1d4141e1010b2840c00da069044040c00035160000d40441e42031414035826107400c150307000c051b10320300d00c140301700400700701014080d0303100303e00e1003091400c14001e52402c9440e45000384540c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 18329224 1250 18327974 18328003
    0x50105010512060f0a0b0a050324070302040509041403040308040b070606050f0f12010e07030503070b0106020c01050706050c0d06120204050106110d0e060702090f0106030c03090804060e010905040509 88
    0x800c610081c2c040119071244140c5100a1414035655080d4007400500130b406801504160194030204082c0c4007401034114148011180316100d04185860000703043c0010500b008042c4180010b121554071015401d4020f50807441c82450b11658030303021802c0d481264001071402c040010002854a275940240c42150b016000401000d55510207008044540541040d0b1003d1800c030748000c0ea240c04521003403000700b9400002503401e0315041031440d0950682042c1c9055001007413042c10030449031000c9016180ca440a49508140d180000c1e129024488000f000141c40f580090626010b850a0307d001c060817000a00140380d683d202d0b40c147e0f00e58240c040e030065040000100b030070b6000d00c01f9041e140015000034034071070101c0322080320802c02c0006616405242000b424015075144102e0038040c8440c403107060519454000060100c443c908510418141009004c101013144142990115103041c10b10780485009034004851040b01604040e602918182c180480c01d072000403e2200744522 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 18330474 1250 18329224 18329239
    0x20f0a090203100f050603100504020310031e02090a0b0916020c06040303030c03140c0904020a050403050a0b0106020f0c01050d050603010b030a0302031809041e021f020c011e08010b090f0d0501050105 88
    0x31041480311ba444101d81d1000340321440282042282000e50045601c00b0060704103480c001d4903a5201244c01010039030b99503c03240c081e8208020751603e80d6810350400301280040021419582c0030808400008145118128464041d0003405000f44001d0329040310040000d035441e9100c0c50090b00138035800c1100e0000a1401c86c40c0245803201e03112003400f40103d00c4201d4140070b804400c2001a52110050070100442848000000360080040c501d050703100300045000c40d0704006c4028070301102085403802c41e0780100240741c0c0c20798000d001c0f13a402e00c003a0303100465299a100c003c01d01502c81c0751003440c0c045c480c2c0e0001c0030905078040702800340d10072400d1120b4040030140c4208949200c081c1c8002e0440021901c00503048042078192100c0e443c0b010705415140d001c181c2c3c42800019050355964007580140300c0e039441540c0d01501264280003444414000480c603520010039003501402a070054082c0010203107003995400303000c01f807a400002d20101840889280450281900380300e80b6004649 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 18331724 1250 18330474 18330479
    0xa08010c0504150305060114090f0a14090f04031b0218070306090e0106050a0e07020a02060c030a09050418060b030c130f0509010b1c0804030b0108060f0901020a0903020f0a090203100f 81
    0x445c0c004c2e98018403059580305801d07064003241400c268440d0380503d90224030407840f003001d500c808003000010a14040400c54445c00039040c00401e41000b03110382d44001c41c02082000094002c0140810008842c4600018081500c0402c03000101c2e1014903d120703200304100804071740d05070083e40c1030391188038040c030518a10099107400d071a050701403244c0c010303400101408000c00f001629940201b441c0304030351002501e80c000c18101e41c40304400c40a50707000050040e0b20190892a40c1d0000c0200391f4080010410307230180c20581c841c2e031541c01001251280d001e24030315981040b81c1600401c008000010b043d1036111210001e00c1c54440c0303940800d0030032000950070b030f0041c03080c0b038180c0d003010700018115913000c807648000b5144030b10100c1e0484d900b0b000210108400790480c0d4042c0652000406681c14840501d000100d03000b8001207860303004100d484035203070344450f60034116030b8141c6081c0310000700d04c0000341c215589500450003039071000c0304000010042d900600125981000e94109071038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 18332974 1250 18331724 18331727
    0x9150509070e13030815060f0a030b180c0702031c0c02040b06030705040b1c06030602030103032d0f050706090c0303110a0506010b070204020c0a030206060f0d200a08010c050415 78
    0x9411074100800c07101c400b03c0500820b00883e03040b5440008600020064002d4034000b0340c1e10380251040050404000c6060081c0d9901b520030805414000c170303100d682c0011100c1c00000d84207130061a141c40140c0c040350700400c5403010026000c40d840c0250101c000e0421041c0d00400f030018811050784101e00302801c0c001141030140840b401403503942d50b540e1405050080714105076100c8080c0c0b00e40215002040c914111040c481c5d100910301c65000580c2d654034504000300703080900c91080b2402c00800441c0910107501c0106d06122000c1810010000340c40c50030190766500403d8009000103013031840002c10814014a16000d0781c1c426198044c80400003094150746450f220801805d641c04034005110340720f2400c0240101c00d00c0200003520f0803800716030761420081e000604a02592002081c000e00e41740003040328401c607205403a03055103e1116101e044284c2810107410710b03540810b0112100c20b1f2a060340910103000b1200c000d00040d0040c81c0014096403082c45101400a100d40d6203c9100f03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 18334224 1250 18332974 18332999
    0xa0b0108010308030403030509070315021e090d140102070f0507030c0b0a0912020f03030a02060106020105011d01030209040303150b0c1209180702010f0606180b07020918010915050907 81
    0xa03500030f12410304503030b0342d5034080c0d00618010b00b40c3c140503c20000004000703019031004d03101c0501406000750301c0b040b00e00256800c080300b0402500c154002804010056101c00440b116150740283d4001003610600a0041c0288203854014042c41503500701d0f031050081c002003a2044074400d4000c203003038a64443c3c0c0d8035540c3c001c0c0008180002c0721103c0030890900c10418031350300c6a000030700c02c2402c03020b2540024615840003450a000da08900010840c1c582c0a204080c010304029005030f4400700c00401c0780034010014040284645103600200701403522070b601100500d8200000c8500b90350710741c91000c1041c0c2206a0910032840391400001c2c444241106640b8083c0e0044c008074900302c0c248241010f800070007030203801107668484c450342110381940100d200401407500c8210050110009c441c040421070b41080c01c0441d010032854005031034100d261503200c9040041130100034480420140581041c080c064006a031806e860401c400c0e003a40114041c43c001011a594690382c1c0380902010b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 18335474 1250 18334224 18334229
    0x309030c0b0310120611120a0e0c061b01090210021501060306121203090b150307090501140d0809090f070305060d05060c09010507060527030f0a140d05010e0a0b010801 74
    0x8014002c6804c000010120000040305841500e0209012081403c140b5094100880250103120b42806100c003803d2140b05035012582c00501401c000561900490310034841d00d112808003155040d6029019042035008030b80481e4020701c00136810043c10002580e90400900101a0600071400040d050340a445800100c4000e01ca460200a0f420f49407040d14009003c40001490348848007400018000f014162040f44407201c540748480301c41d23050519048940d04415081484d040040c03000c01002552408151021903001c080e50300385142011a40c0100300349141c0080740c4000348020180d00d5101c040c418049940d040100d40e80d40d40401c21019030454002d00203412560110759a81c50706001130901541c18182185000410390350340301102c1003114990305025004002d01d480381080090300c034072080701c400118185403100b1007404042c0b181c0707040c5a042c88036460404100510200a0301c00c0fa01700150304106541c2c0d500e0ba1030070060400c0751207440e0546007410343c0c0990b41c000e1018a05 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 18336724 1250 18335474 18335491
    0x30105030a0201030902010512010b0a0e0906060301030209072607030e01020a080105040c18030506071e0f0e040603060509060603010c0212030f060a080307030201020702010807030501030b06010c060b04090309030c0b03 96
    0x1c003a03296030010342c001c0aa402c0107a040007403c115041c00003903281c03080303802008281e0070f0540d192240180201461550b0ba0a40d110315111028021181d4504055a054a4040701c00008a0701d80303006c150743c5001180b1b281c8800b00d07031808114071b00355074454649108501946080c0204181c000c0ca403401c178403030003400c080070a110300d0060056013032a501c9550b5501140c107014288403110701d4090341d05401c56004403415071040e01044540c039800151034514402d24ac4200c454800c8089001d4101503100035000c0410079134400305106a0340e2904074800560b000002049942410004152034210448e0864025820008400d148034400181a00d9540e0500081403e5807519103000d8803104000c1d10050340448000404241c2210a0000b013010610179000107a60388014800500416001090003050500c2e20b4010000310340c0070108154041e80902e4001400c4002d0300e4401c00400c2c9030070b00d1a400c14605550341003010341000412043d24050700ca010902a0344880f42072035440b00b190300e00c6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 18337974 1250 18336724 18336733
    0x240c07060b03030f0c070812030c1801020a060216020910142e02030a030501090b06040306020313120e09090c0a030f0501060801020304030c020909010902010f05130506040801021e03010503 83
    0x11038916403021031101001410340c1c3c034212810021601d00d8001000c1030440390444039042114250030080300030000364556443d0704614013000c144810740151500c001400000e00e14007001a031003401045600c5500030821501e801405000c8601801d100d003080f402021044046030544100140c080103c5034002d54045031520f074102401100c0c3c412500704d066094404146000542c1c504108540e0141141e0095407208009800102546d2060740040c81c004d2402ca04d2010948400003201e040e25046030000da925141d400f02c9074000e417245200a004902112400146c1c00c0d0b100522401c060000c03103105103e034071802c81c565180d1440400e65940321884680400000e0a60390802800074000e00c0001401a5102400c60a981c002c83c0c2c100c0002d5a98030701d083c1103142468551f50040c000a00130405181194006480201900c01010a0100225a03440500c0c00c4000e0380c0c1c05020064001d5481b0741e07460403c140030b5000906219901030fa10502c0017070000c01032003603d048a80050050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 18339224 1250 18337974 18337987
    0x1080702060f0106110c060f13060908030702010c02130f1b110c0d0203100e0109060e01150b030a0f09060b040615050406031d0307050708010b0303040518060604080f240c 75
    0x558580340c0411003d101e50041d602c01c40d01b140d031031a0180061548000c4095034580d448072020740d002c0306540020003130094154041c0094580001075441140d428209151401c01600002d00d602d850b02a9901c0c2850030001142294134558100c0e101c5038041400c1e000381085070030300540300e10042100e0901c10f580300c4400d000c00c03460102104004680003030b090710a00c80080c1e0310b503400d94041d030408550304da441d00a09000c10040d489025902204000204803006038152003000486507846519002c0b0004004500c0644280e8048070310795000210411440905180400c0580088070206200700e207030000000f660ba48031078450541900c19540c80d40740c030b4103043c4250010071b544920201c083c2c090303018452002404000801509015030000d09020703141c2a035260a43d250000590b0007900300f40410002c41d1201305158802d0a41061003080765922070b00440c2c05801243d0101405104003020350004100c00300320001c0c003001110788028000d404100340d080401e016501c01000303c074100000f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 18340474 1250 18339224 18339227
    0x7140d0c1e030e030601060309020a150f0c03030209061303020a2702030405073501061503020912012a050304030c030c06060314010204080601081c0807170c04030201080702060f0106 80
    0x1c8412521a082c600d044165000110b40b420000342c0115010170350b80c1040310194903003c1c00080c001c01482c455a800a042400010119035420102009000150002c44101070003501079440c0d1403800740000741c86102d0074202030111031107071009a01901c854280072840b482c1c03102100100415120b5150040d2044440701e10003584010804d032120300800c4d402040203900c202d00e501c0461800344159080141604500c4074105214103c8103031680b4040d010004c94519140840000640d41001a2101e00035030119450b602e8000398201154685200b07180003c219040701d100c441d21145016095011044003550356101c19500035010170116010030000034403c2c003076000900e22803400070503c1503030707651446111541c0500d070144603500403074203014041040001e9401044d10b04000e001c1c4207001410361a2004607400c044082190050000b00810300a4586071180764010500254520f450031b42801c1d5500300e804102d00207081c04000c00e0406100084490046110320040007544c2d01e4200c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 18341724 1250 18340474 18340523
    0x150b0901050304060608060c0901030b040506010207170312010b0307090806040803060f031032100303140412030513050609180603070512160e0702060123040207140d0c 74
    0x4200c44e5940c40704000b040f8a8018040e030f60040c0100301c2600d455880304c00014003950500030075103010b00e03e02000c2120680e4000303852f8046481401e96141c00041c6400d2140c00c500c141c814000d03d0b1080c0c0000020307508100c42c0250301ca0340543d0782e441c403c55210305d421903c0da0005e440c0a85a08014008507650389001c003280d214641d0010b04a0309607507003600b00c00c01a07500000f03000c0303a0703400c3c2030180c903422903034648103030986401c1801c000c2c40a1400080e0300c21098200e000140410003000704072005104920304aa0140c020800d1086030140789180040c0703158481e1080072161880c01f00e00040c81c3c10584150b44044900070311007a101880e031003100100c03d8000b81842d605101d08200041c40e0f8413080700420840a00801400144001e41c0d0901a412078030751094003c003040d0401c00c03c540d540410700a065400b2000f10701000004005200200880741d590740303510030300c0003403000b0400120380c1e514510303580d00310b058801c0400120426a034910010718050450420510f000e50814407400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 18342974 1250 18341724 18341731
    0xf03050d030c05040915030201080105041107110303071a04050d03050f0615160305030a0606020f1209040b120a060e0313050409060204091409010e16060804050708030a05040603150b09010503 84
    0x507043d030a00740e940703005800341c41744c0c00d1012040c040c60010074010755a0101c6d007a07000d01010b440c1480209032030314522106218041c000b41144260b44514404c9036400d1048800d856007007151640031401448000b00c56060555085400d885449280941c4074001c0c06200d10500f004410003909941e66000e02c024080300d40303c0512441020088070040542c0401c0c0b4540c8907000750b81e8103031031713152081030700d0308a80c010b4200e01c080d5406003043d00300c3e00e2000242c803001d03050901e03540b5440f60407402c00f0030042d002c252490b9600c02400700b0803600c0b01100044c840242ea0155509001114440d01700c03580701e215000c14210001d1303450304140510700b002d40046014902c03842005180c0307640d44071000226150010b410011b4141d2800f0b0019800b13090140103d9002c8000c040c00102480c0c044440810311284a42c40c18840c480e000103050220a002d09001045c210040d00d617103800442d0014800d500500070b45000c00d00e070140d21503074040b2842244064404003a401d074a09803910006465a803c0203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 18344224 1250 18342974 18342977
    0x120504020a0b0a03200c0111070507170102250204140f06120f10090b0907050f0d0213090302010606110304030c06030e030d0603030801030b060402130512011104030506060306010f03050d030c 84
    0x115503a040758032140804001007980030031175607241c4240038205400e65040c00b00d540c1124009201d0316001c0351002c03030b0342d00c2190120203000c008100755480e19406806001540070014030000f0121207480e0031141164015482103804001c0e41c104050000c658400580c1c03041104620b050010b241820b01c100070040e5248a1000c0306e8086400c40a028901140c1e00c6280c044035464946681c200415502410f070003c0170350700501100c2c1e05000c08a4100b002442a0340c1c03252002c039181d50150f49480c00c03507801403520b00d01c050000785031906001e40a84040d00c51000000c8a03c03c00140304c07d030100580d01601c1c0d000f4000000145011401c030013510012036080500d01082103900c000000520a940c000c40c402e80b1042c501c2c2d031450403d01c240304e4000f00410b004600402000f91803920709075444094a070111448840c204800c0c120b0ba00400b0803492101c0c1d8140002004400c0c04000210907200364801c40c102d404607031725030a418401070014031000f030142c1d00544800440301c1c02500b00c0054140c05 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 18345330 1106 18344224 18344231
    0xd02060a0b04091b050a0501050a12020706110307030c020601050406060c030305040302100914010b040902060301060c021c0305090f060f0a0305040f0206070302060106120504020a0b0a03 82
    0x103200c542030316a180d50030401560350381d01540300c0507040000c003000600c094910414044e100e000d651320407080b04000003043d61082c2c0c1103440d940101c0d540c0445007006046288069009203070115452500e0380c5100c1e40d4a28001d0140d44110010340d000300e003403405494041d08004040e003080d8061403c3c12018004280c00c41816000e541c0d05103000180f81d0b0f60f40c1030490400694001088105050200300c9041c403019401d8905000e03003590081195406680c02c200c1154881c00303000b5040201400100b0925010307000060b00c5078000b8114007a9810260f400395410801600100d0100320302140c44402c500b44880056a1b8140c195201442c145008504255600440d0008400c06440b800000c0401c0040e02e9840b0300325174040d180c83c0e2644141d24020f03480719402d014100c0040c0380d440c941c131150a11801527500844c1c01400d034039800780c00c024000d84a07600c66002030b402e0544 = true := by decide +kernel

theorem cover : BRFrame.Cov 18165474 18345330 := by
  have h0 := BRFrame.cov_init 18165474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18165474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 18165474 ≤ n) (h2 : n < 18345330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
